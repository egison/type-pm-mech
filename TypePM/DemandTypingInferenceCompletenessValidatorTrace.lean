import TypePM.DemandTypingInferenceCompletenessValidator

/-!
# Trace-side terminal-validator completeness

The public validator contains five checks whose successful Boolean form is
more specific than the reconstruction propositions obtained by its soundness
theorem.  This module records the exact semantic facts that the completeness
run must establish and proves that those facts are sufficient for the finite
checks.  None of the predicates contains a typing derivation.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-! ## Primitive-hole allocation -/

/-- Exact source-freshness fact retained for each primitive-pattern hole. -/
def TracePrimitiveHoleConditions
    (signature : FrozenSig) (trace : InferTrace) : Prop :=
  ∀ event, event ∈ trace.events ->
    match event with
    | .inferredPPat .hole target holes bindings _path =>
        ∃ varId,
          holes = [⟨.var varId, target⟩] ∧
          bindings = [] ∧
          varId ∉ signature.capVars ∧
          varId ∉ target.fcv
    | _ => True

theorem tracePrimitiveHoleCheck_complete
    {signature : FrozenSig} {trace : InferTrace}
    (conditions : TracePrimitiveHoleConditions signature trace) :
    tracePrimitiveHoleCheck signature trace = true := by
  unfold tracePrimitiveHoleCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | inferredPPat primitivePattern target holes bindings path =>
      cases primitivePattern with
      | hole =>
          rcases accepted with
            ⟨varId, holesEq, bindingsEq, signatureFresh, targetFresh⟩
          subst holes
          subst bindings
          simp [primitiveHoleEventCheck, signatureFresh, targetFresh]
      | wild => rfl
      | pval name => rfl
      | ctor name patterns => rfl
      | tuple patterns => rfl
  | _ => rfl

/-! ## User-pattern leaf allocation -/

/-- Exact ambient-freshness facts retained for user-pattern leaf events. -/
def TracePatternLeafConditions
    (signature : FrozenSig) (trace : InferTrace) : Prop :=
  ∀ event, event ∈ trace.events ->
    match event with
    | .patternVarFresh context parameters bindings capVar tyVar
    | .patternWildFresh context parameters bindings capVar tyVar =>
        capVar ∉ signature.capVars ∧
        capVar ∉ context.fcv ∧
        capVar ∉ parameters.fcv ∧
        capVar ∉ bindings.fcv ∧
        tyVar ∉ signature.tyVars ∧
        tyVar ∉ context.ftv ∧
        tyVar ∉ parameters.ftv ∧
        tyVar ∉ bindings.ftv
    | .patternValueFresh context parameters bindings capVar target =>
        capVar ∉ signature.capVars ∧
        capVar ∉ context.fcv ∧
        capVar ∉ parameters.fcv ∧
        capVar ∉ bindings.fcv ∧
        capVar ∉ target.fcv
    | _ => True

theorem tracePatternLeafCheck_complete
    {signature : FrozenSig} {trace : InferTrace}
    (conditions : TracePatternLeafConditions signature trace) :
    tracePatternLeafCheck signature trace = true := by
  unfold tracePatternLeafCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event <;> simp_all [patternLeafEventCheck]

/-! ## Pattern-constructor compatibility -/

/-- Terminal lookup and semantic compatibility for each constructor event. -/
def TracePatternCtorConditions
    (signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .patternCtorCompatibility solveCount name childCaps resultCap =>
        solveCount ≤ state.trace.solves.length ∧
        ∃ entry,
          signature.findPatternCtor name = some entry ∧
          entry.CapCompatible
            (childCaps.map fun cap => cap.apply state.prevailing.cap)
            (resultCap.apply state.prevailing.cap)
    | _ => True

theorem tracePatternCtorCheck_complete
    {signature : FrozenSig} {state : InferState}
    (conditions : TracePatternCtorConditions signature state) :
    tracePatternCtorCheck signature state = true := by
  unfold tracePatternCtorCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | patternCtorCompatibility solveCount name childCaps resultCap =>
      rcases accepted with ⟨bound, entry, lookup, compatible⟩
      simp only [lookup, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨bound, capCompatibleCheck_complete compatible⟩
  | _ => rfl

/-! ## Complete validator assembly -/

/-- The five terminal checks whose completeness needs facts about the actual
recorded run, separated from the four purely algebraic stable checks. -/
theorem traceSpecificTerminalChecks_complete
    {signature : FrozenSig} {result : ExprResult}
    (primitiveHoles :
      TracePrimitiveHoleConditions signature result.state.trace)
    (patternLeaves :
      TracePatternLeafConditions signature result.state.trace)
    (patternCtors : TracePatternCtorConditions signature result.state)
    (instances : CanonicalTraceInstanceSuffixConditions result.state)
    (slots : CanonicalTraceSlotAlignmentConditions result.state) :
    tracePrimitiveHoleCheck signature result.state.trace = true ∧
      tracePatternLeafCheck signature result.state.trace = true ∧
      tracePatternCtorCheck signature result.state = true ∧
      traceInstanceSuffixCheck result.state = true ∧
      traceSlotAlignmentCheck result.state = true :=
  ⟨tracePrimitiveHoleCheck_complete primitiveHoles,
    tracePatternLeafCheck_complete patternLeaves,
    tracePatternCtorCheck_complete patternCtors,
    traceInstanceSuffixCheck_complete instances,
    traceSlotAlignmentCheck_complete slots⟩

/-- Once traversal completeness supplies the five run-specific conditions,
all nine conjuncts of the public terminal validator follow. -/
theorem wBridgeCheck_complete
    {signature : FrozenSig} {result : ExprResult}
    (primitiveHoles :
      TracePrimitiveHoleConditions signature result.state.trace)
    (patternLeaves :
      TracePatternLeafConditions signature result.state.trace)
    (patternCtors : TracePatternCtorConditions signature result.state)
    (instances : CanonicalTraceInstanceSuffixConditions result.state)
    (slots : CanonicalTraceSlotAlignmentConditions result.state)
    (types : TraceTypeAlignmentConditions result.state)
    (duals : TraceDualAlignmentConditions result.state)
    (finalization :
      TraceFinalizationSuffixConditions signature result.state)
    (generalization : TraceGeneralizationConditions signature result.state) :
    wBridgeCheck signature result = true := by
  simp only [wBridgeCheck, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨
    tracePrimitiveHoleCheck_complete primitiveHoles,
    tracePatternLeafCheck_complete patternLeaves⟩,
    tracePatternCtorCheck_complete patternCtors⟩,
    traceInstanceSuffixCheck_complete instances⟩,
    traceSlotAlignmentCheck_complete slots⟩,
    traceTypeAlignmentCheck_complete types⟩,
    traceDualAlignmentCheck_complete duals⟩,
    traceFinalizationSuffixCheck_complete finalization⟩,
    traceGeneralizationCheck_complete generalization⟩

end Reconstruction
end Inference
end TypePM
