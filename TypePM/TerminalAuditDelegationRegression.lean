import TypePM.RecursiveExamples
import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingInferenceSoundnessMutual
import TypePM.InterpreterAdequacy

/-!
# Delegated capability regression

This regression fixes the public boundary for a matcher which decomposes a
one-field tuple and delegates the field to its argument matcher.  The
argument-slot capability (the capability supplied by the surrounding matcher
parameter) remains structurally flexible at local matcher
finalization and is later specialized to the opaque constructor `K`.

Evidence produced by a non-root primitive-pattern hole now retains an opaque
subtree as a complete delegated leaf.  A hidden child of an observable
constructor is retained in the same way.  The terminal audit consequently
accepts these programs without treating `K` as structure observed by the
enclosing matcher.  Direct structural evidence remains subject to the ordinary
opaque-constructor and hidden-child rules.

The mutually recursive executable inference functions are opaque to kernel
reduction.  The concrete run is therefore fixed with `#guard`, rather than
introducing `native_decide`.  For the primary opaque-capability program,
symbolic theorems below connect every successful raw result to the
demand-directed traversal theorem and every successful public result to the
audit-bearing `SourceTyping` judgment.  The hidden-parameter variant records
the corresponding public connection.
-/

namespace TypePM
namespace TerminalAuditDelegationRegression

open Inference
open Inference.Reconstruction

/-! ## A well-formed signature with one opaque matcher consumer -/

/-- A value constructor that forces its argument matcher capability to `K`.
Its result remains an ordinary data root, as required by `FrozenSigWF`. -/
def consumeKScheme : CtorScheme where
  capBinders := []
  tyBinders := []
  args := [.matcher (.con "K" []) .int]
  result := .data "Witness" []

/-- `K` stays opaque because the inherited observability table recognizes only
`List`. -/
def signature : FrozenSig :=
  { RecursiveExamples.listSignature with
      dataCtors := ("consumeK", consumeKScheme) ::
        RecursiveExamples.listSignature.dataCtors }

theorem signature_checker_accepts :
    frozenSigWFCheck signature = true := by
  decide

theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound signature_checker_accepts rfl

theorem k_is_opaque : signature.observability "K" = none := by
  rfl

def opaqueK : Cap :=
  .con "K" []

def delegatedK : Shape.Evidence :=
  .known (.delegated opaqueK)

def tupleHoleEvidence : Shape.Evidence :=
  .prod [delegatedK]

/-! ## The delegated/direct-observation boundary -/

/-- A hole at the root of a primitive pattern remains `unseen`; only a hole
below a tuple or constructor is a delegation boundary. -/
theorem rootHole_stays_unseen :
    clauseEvidence signature.toMatcherSig .hole [opaqueK] =
      some .unseen := by
  rfl

/-- Only the non-root hole embedding makes the opaque subtree atomic. -/
theorem opaqueK_is_delegated_at_hole :
    Shape.ofDelegatedCap signature.observability opaqueK = delegatedK := by
  simp [opaqueK, delegatedK, signature, RecursiveExamples.listSignature,
    RecursiveExamples.observability, Shape.ofDelegatedCap]

/-- A one-field tuple hole retains the outer product while keeping `K`
delegated to the next matcher. -/
theorem nonRootTupleHole_evidence :
    clauseEvidence signature.toMatcherSig (generalTuplePP 1) [opaqueK] =
      some tupleHoleEvidence := by
  simp [clauseEvidence, generalTuplePP, clauseEvidenceGo,
    clauseEvidenceListGo, finishClauseEvidence, tupleHoleEvidence,
    PPat.coreOrderCheck, PPat.orderState, PPat.orderStates,
    PPat.holeCount, PPat.holeCountList, FrozenSig.toMatcherSig,
    opaqueK, delegatedK, signature, RecursiveExamples.listSignature,
    RecursiveExamples.observability, Shape.ofDelegatedCap]

/-- The structural tuple plus its catch-all clause finalizes to the precise
delegated capability. -/
theorem delegatedTuple_inferShape :
    Shape.inferShape signature.observability
        [tupleHoleEvidence, .unseen] =
      some (.prod [opaqueK]) := by
  rfl

/-- Merely presenting an opaque constructor as structure does not receive the
delegation exemption. -/
theorem directOpaqueEvidence_rejected :
    Shape.finalize signature.observability (.con "K" []) = none := by
  rfl

/-! ## Minimal closed source program -/

/-- The only structural clause decomposes a one-field tuple and delegates the
field to the recursive matcher's argument slot. -/
def tupleClause : Clause :=
  .mk (generalTuplePP 1) (.var "argument")
    [.mk .wild (.ctor "nil" [])]

def clauses : List Clause :=
  [tupleClause, RecursiveExamples.catchClause]

/-- `self` is deliberately unused.  The `fix` form is needed only because its
matcher placeholder allocates the shared argument-slot capability and records
that capability as structurally flexible. -/
def delegatedTupleMatcher : Expr :=
  .fix "self" "argument" (.matcher clauses)

def programBody : Expr :=
  .tuple [
    .ctor "consumeK" [.var "opaqueMatcher"],
    .app delegatedTupleMatcher (.var "opaqueMatcher")]

/-- The first tuple component fixes the lambda parameter at `Matcher K Int`.
The later matcher application consequently specializes this shared slot
capability to `K`, after the matcher literal's local finalization event. -/
def program : Expr :=
  .lam "opaqueMatcher" programBody

def rawResult : Option Inference.ExprResult :=
  Inference.inferRaw signature [] program

def publicResult : Option Inference.ExprResult :=
  Inference.infer signature [] program

/-- The exact inferred result target observed before the terminal audit. -/
def expectedTarget : Ty :=
  .fn (.matcher (.con "K" []) .int)
    (.prod [
      .data "Witness" [],
      .matcher (.prod [.con "K" []]) (.prod [.int])])

/-- The nine public audit components, in `wBridgeCheck` order. -/
def auditProfile : Option (List Bool) :=
  rawResult.map fun result =>
    [tracePrimitiveHoleCheck signature result.state.trace,
     tracePatternLeafCheck signature result.state.trace,
     tracePatternCtorCheck signature result.state,
     traceInstanceSuffixCheck result.state,
     traceSlotAlignmentCheck result.state,
     traceTypeAlignmentCheck result.state,
     traceDualAlignmentCheck result.state,
     traceFinalizationSuffixCheck signature result.state,
     traceGeneralizationCheck signature result.state]

/-! These guards are executable regressions.  They intentionally use neither
`native_decide` nor a handwritten copy of the inferred state. -/

#guard rawResult.isSome
#guard publicResult.isSome
#guard DirectSelf.check "self" (.matcher clauses)
#guard auditProfile == some
  [true, true, true, true, true, true, true, true, true]
#guard match rawResult with
  | none => false
  | some result => decide (result.resolvedTarget = expectedTarget)
#guard match publicResult with
  | none => false
  | some result => decide (result.resolvedTarget = expectedTarget)
#guard match rawResult with
  | none => false
  | some result => result.state.protectedCaps.isEmpty
#guard match rawResult with
  | none => false
  | some result => decide (result.state.prevailing.cap ⟨1⟩ = .con "K" [])
#guard match rawResult with
  | none => false
  | some result =>
      traceFinalizationSuffixCheck signature result.state &&
        wBridgeCheck signature result

/-! ## A delegated child hidden by an observability mask -/

namespace FalseMask

/-- `List` exposes its parameter, whereas `F` hides its sole parameter. -/
def observability : Shape.Observability :=
  fun former =>
    if former = "List" then some [true]
    else if former = "F" then some [false]
    else none

def nilProjection : Projection.ProjectionSignature observability where
  fieldTypes := nilCanonicalScheme.args
  resultType := nilCanonicalScheme.result
  resultRoot := .data (mask := [true]) (by
    simp [observability]) (by simp)

def consProjection : Projection.ProjectionSignature observability where
  fieldTypes := consCanonicalScheme.args
  resultType := consCanonicalScheme.result
  resultRoot := .data (mask := [true]) (by
    simp [observability]) (by simp)

def nilPatternCtor : PatternCtorScheme observability where
  scheme := nilCanonicalScheme
  projection := nilProjection
  projectionFields := rfl
  projectionResult := rfl

def consPatternCtor : PatternCtorScheme observability where
  scheme := consCanonicalScheme
  projection := consProjection
  projectionFields := rfl
  projectionResult := rfl

def falseMaskedCap : Cap :=
  .con "F" [opaqueK]

/-- A value constructor that fixes its argument matcher capability to
`F[K]`. -/
def consumeFScheme : CtorScheme where
  capBinders := []
  tyBinders := []
  args := [.matcher falseMaskedCap .int]
  result := .data "Witness" []

def signature : FrozenSig where
  observability := observability
  dataCtors :=
    [("consumeF", consumeFScheme),
      ("nil", nilCanonicalScheme),
      ("cons", consCanonicalScheme)]
  patternCtors :=
    [("nil", nilPatternCtor),
      ("cons", consPatternCtor)]
  patternFuns := []
  primitives := []
  constructorsByFormer :=
    [("List", [("nil", 0), ("cons", 2)])]
  armExhaustive := basicArmExhaustive

theorem signature_checker_accepts :
    frozenSigWFCheck signature = true := by
  decide

theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound signature_checker_accepts rfl

/-- A delegated embedding preserves `F` for projection, while retaining its
hidden `K` child as one delegated leaf. -/
theorem falseMaskedCap_delegated_embedding :
    Shape.ofDelegatedCap observability falseMaskedCap =
      .con "F" [delegatedK] := by
  simp [Shape.ofDelegatedCap, Shape.ofDelegatedCapsMasked,
    Shape.hiddenDelegatedCap, observability, falseMaskedCap, opaqueK,
    delegatedK]

/-- The delegated hidden child is restored exactly, rather than canonicalized
to `Any`, at terminal finalization. -/
theorem falseMaskedCap_finalizes_exactly :
    Shape.finalize observability (.con "F" [delegatedK]) =
      some falseMaskedCap := by
  rw [← falseMaskedCap_delegated_embedding]
  exact Shape.finalize_ofDelegatedCap observability falseMaskedCap

/-- Ordinary direct evidence in the same hidden position keeps the existing
canonical `Any` behavior. -/
theorem directOrdinaryFalseEvidence_canonicalizes :
    Shape.finalize observability (.con "F" [.con "K" []]) =
      some (.con "F" [.any]) := by
  exact Shape.finalize_unobservable_child rfl rfl

/-- Delegating `Any` keeps its ordinary canonical evidence, so it still
exact-merges with `Any` supplied by another clause. -/
theorem hiddenAny_stays_canonical :
    Shape.hiddenDelegatedCap .any = .known .any := by
  rfl

def malformedFalseMaskedCap : Cap :=
  .con "F" []

/-- An arity-mismatched capability is retained only at a delegation boundary,
where the next matcher consumes it as one atomic capability. -/
theorem malformedDelegatedEmbedding_finalizes_exactly :
    Shape.ofDelegatedCap observability malformedFalseMaskedCap =
        .known (.delegated malformedFalseMaskedCap) ∧
      Shape.finalize observability
          (Shape.ofDelegatedCap observability malformedFalseMaskedCap) =
        some malformedFalseMaskedCap := by
  constructor
  · simp [Shape.ofDelegatedCap, Shape.ofDelegatedCapsMasked,
      observability, malformedFalseMaskedCap]
  · exact Shape.finalize_ofDelegatedCap observability
      malformedFalseMaskedCap

/-- The same malformed constructor presented as directly observed structure
is rejected. -/
theorem directMalformedEvidence_rejected :
    Shape.finalize observability (.con "F" []) = none := by
  rfl

def programBody : Expr :=
  .tuple [
    .ctor "consumeF" [.var "opaqueMatcher"],
    .app delegatedTupleMatcher (.var "opaqueMatcher")]

def program : Expr :=
  .lam "opaqueMatcher" programBody

def rawResult : Option Inference.ExprResult :=
  Inference.inferRaw signature [] program

def publicResult : Option Inference.ExprResult :=
  Inference.infer signature [] program

def expectedTarget : Ty :=
  .fn (.matcher falseMaskedCap .int)
    (.prod [
      .data "Witness" [],
      .matcher (.prod [falseMaskedCap]) (.prod [.int])])

def auditProfile : Option (List Bool) :=
  rawResult.map fun result =>
    [tracePrimitiveHoleCheck signature result.state.trace,
     tracePatternLeafCheck signature result.state.trace,
     tracePatternCtorCheck signature result.state,
     traceInstanceSuffixCheck result.state,
     traceSlotAlignmentCheck result.state,
     traceTypeAlignmentCheck result.state,
     traceDualAlignmentCheck result.state,
     traceFinalizationSuffixCheck signature result.state,
     traceGeneralizationCheck signature result.state]

#guard rawResult.isSome
#guard publicResult.isSome
#guard auditProfile == some
  [true, true, true, true, true, true, true, true, true]
#guard match rawResult with
  | none => false
  | some result => decide (result.resolvedTarget = expectedTarget)
#guard match publicResult with
  | none => false
  | some result => decide (result.resolvedTarget = expectedTarget)
#guard match rawResult with
  | none => false
  | some result => wBridgeCheck signature result

/-- Any successful public result for the hidden-parameter regression carries
the audited source typing at its reported target. -/
theorem public_success_sourceTyping
    {result : Inference.ExprResult}
    (success : publicResult = some result) :
    SourceTyping signature [] program result.resolvedTarget := by
  apply Inference.infer_success_sourceTyping
  simpa [publicResult] using success

end FalseMask

/-! ## Symbolic connections to raw and public typing -/

/-- Producer protection does not change a successful raw result, so a raw
success exposes the exact underlying fuelled traversal. -/
theorem raw_success_inferExprFuel
    {result : Inference.ExprResult}
    (success : rawResult = some result) :
    Inference.inferExprFuel (Inference.inferenceFuel program) signature [] [] []
      program (Inference.initialState signature []) = some result := by
  unfold rawResult Inference.inferRaw at success
  cases core : Inference.inferExprFuel (Inference.inferenceFuel program)
      signature [] [] [] program (Inference.initialState signature []) with
  | none => simp [core] at success
  | some candidate =>
      have guarded : Inference.enforceProtectedResult candidate =
          some result := by
        simpa [core] using success
      have equality := (Inference.enforceProtectedResult_sound guarded).1
      subst candidate
      rfl

/-- Every concrete raw result guarded above carries the existing chronological
demand-directed synthesis derivation.  No terminal audit is used here. -/
theorem raw_success_demand_synth_run
    {result : Inference.ExprResult}
    (success : rawResult = some result) :
    Inference.DemandSynthRun signature [] program
      (Inference.initialState signature []) result :=
  Inference.inferExprFuel_ddSynthRun
    (raw_success_inferExprFuel success)

/-- Every successful public result for the regression reconstructs the
audit-bearing source typing at exactly the reported target. -/
theorem public_success_sourceTyping
    {result : Inference.ExprResult}
    (success : publicResult = some result) :
    SourceTyping signature [] program result.resolvedTarget := by
  apply Inference.infer_success_sourceTyping
  simpa [publicResult] using success

/-! ## Operational witness -/

/-- Evaluation of the closed source term produces a closure immediately.  This
is only an operational non-stuck witness; it is not the global typed no-stuck
theorem, whose premise is the audit-bearing `SourceTyping` judgment. -/
def programClosure : Value :=
  .closure none [] "opaqueMatcher" programBody

theorem program_runs :
    evalFuel [] 1 [] program = .ok programClosure := by
  rfl

theorem program_runs_relationally :
    Eval [] [] program programClosure :=
  evalFuel_ok program_runs

end TerminalAuditDelegationRegression
end TypePM
