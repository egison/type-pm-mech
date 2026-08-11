import TypePM.InferenceLocalFactorization

/-!
# Local factorization throughout executable inference

Executable inference uses only the ledger-aware solver entry point.  This
module records that fact at every chronological solve cut and lifts it through
the complete terminating traversal.  The invariant is deliberately local to
each stored certificate: it does not assert an unconditional factorization
principle for arbitrary competitor substitutions.
-/

namespace TypePM
namespace Inference

/-- A stored step carries local factorization for its exact captured ledger,
resolved constraint, and emitted delta. -/
def SolveStep.LocallyFactorizing (step : SolveStep) : Prop :=
  step.HasLocalFactorization

/-- Every chronological step is locally factorizing at its own captured
ledger and resolved constraint. -/
def LocallyFactorizingSteps (steps : List SolveStep) : Prop :=
  ∀ step, step ∈ steps → step.LocallyFactorizing

/-- Certificate-local factorization for an inference state's whole trace. -/
def InferState.FactorizingTrace (state : InferState) : Prop :=
  LocallyFactorizingSteps state.trace.solves

/-- The empty inference state has no certificates to audit. -/
theorem InferState.factorizingTrace_empty
    (supply : InferenceBase.FreshSupply :=
      InferenceBase.FreshSupply.empty) :
    (InferState.empty supply).FactorizingTrace := by
  intro step membership
  simp [InferState.empty] at membership

/-- Recording a reconstruction event leaves solve certificates unchanged. -/
theorem InferState.FactorizingTrace.recordEvent
    {state : InferState} (factorizing : state.FactorizingTrace)
    (event : TraceEvent) :
    (state.recordEvent event).FactorizingTrace := by
  simpa [InferState.FactorizingTrace, LocallyFactorizingSteps,
    InferState.recordEvent] using factorizing

/-- Recording provenance leaves solve certificates unchanged. -/
theorem InferState.FactorizingTrace.recordSource
    {state : InferState} (factorizing : state.FactorizingTrace)
    (source : ProducerSource) :
    (state.recordSource source).FactorizingTrace := by
  simpa [InferState.FactorizingTrace, LocallyFactorizingSteps,
    InferState.recordSource] using factorizing

/-- Protecting a matcher capability does not alter stored certificates. -/
theorem InferState.FactorizingTrace.protectMatcherCapability
    {state : InferState} (factorizing : state.FactorizingTrace)
    (capability : Cap) :
    (state.protectMatcherCapability capability).FactorizingTrace := by
  simpa [InferState.FactorizingTrace, LocallyFactorizingSteps] using factorizing

/-- Export freezing changes current ledgers and events, not prior solve
certificates or their captured snapshots. -/
theorem InferState.FactorizingTrace.freezeCapabilityExport
    {state : InferState} (factorizing : state.FactorizingTrace)
    (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).FactorizingTrace := by
  simpa [InferState.FactorizingTrace, LocallyFactorizingSteps,
    InferState.freezeCapabilityExport, InferState.recordEvent] using factorizing

/-- Appending one locally factorizing step preserves the trace invariant. -/
theorem InferState.FactorizingTrace.recordSolve
    {state : InferState} (factorizing : state.FactorizingTrace)
    (step : SolveStep) (stepFactorizing : step.LocallyFactorizing) :
    (state.recordSolve step).FactorizingTrace := by
  intro candidate membership
  simp only [InferState.recordSolve, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with previous | latest
  · exact factorizing candidate previous
  · subst candidate
    exact stepFactorizing

/-- Every result of the executable ledger-aware solver supplies the local
factorization property used by the trace invariant. -/
theorem solveResolvedWithLedger_stepLocallyFactorizing
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    step.LocallyFactorizing :=
  solveResolvedWithLedger_hasLocalFactorization success

/-- Running one resolved constraint appends exactly one certificate satisfying
the local invariant on every successful path. -/
theorem runResolvedConstraint_factorizingTrace
    {state result : InferState} (factorizing : state.FactorizingTrace)
    {origin : ConstraintOrigin} {constraint : Constraint}
    (success : runResolvedConstraint state origin constraint = some result) :
    result.FactorizingTrace := by
  unfold runResolvedConstraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      have stepFactorizing :=
        solveResolvedWithLedger_stepLocallyFactorizing stepEquation
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          have resultEquation := Option.some.inj success
          subst result
          exact factorizing.recordSolve step stepFactorizing
      | producerToSlot _ _ _ _ =>
          change (if capSubstFixesVarsCheck step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have resultEquation := Option.some.inj success
          subst result
          exact factorizing.recordSolve step stepFactorizing

/-- Resolving a raw constraint before the local solve preserves the same
certificate-local trace invariant. -/
theorem runConstraint_factorizingTrace
    {state result : InferState} (factorizing : state.FactorizingTrace)
    {origin : ConstraintOrigin} {raw : Constraint}
    (success : runConstraint state origin raw = some result) :
    result.FactorizingTrace := by
  unfold runConstraint at success
  generalize constraintEquation : raw.resolve state.prevailing = constraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      have stepFactorizing :=
        solveResolvedWithLedger_stepLocallyFactorizing stepEquation
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          have resultEquation := Option.some.inj success
          subst result
          exact factorizing.recordSolve step stepFactorizing
      | producerToSlot _ _ _ _ =>
          change (if capSubstFixesVarsCheck step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have resultEquation := Option.some.inj success
          subst result
          exact factorizing.recordSolve step stepFactorizing

end Inference
end TypePM

/-!
# Local factorization through executable traversal

This module lifts the per-solve certificate invariant through the terminating
inference traversal.  The preservation relation below mirrors the compositional
shape used by the history and state-extension proofs while tracking only the
property relevant here: every stored certificate factors admissible solutions
of its own resolved constraint through its exact emitted delta.
-/

namespace TypePM
namespace Inference

/-- A state transformation preserves per-solve local factorization. -/
def InferState.FactorizingTraceExtension
    (earlier later : InferState) : Prop :=
  earlier.FactorizingTrace → later.FactorizingTrace

namespace InferState.FactorizingTraceExtension

theorem refl (state : InferState) : state.FactorizingTraceExtension state :=
  fun admissible => admissible

theorem trans
    {first middle last : InferState}
    (front : first.FactorizingTraceExtension middle)
    (back : middle.FactorizingTraceExtension last) :
    first.FactorizingTraceExtension last :=
  fun admissible => back (front admissible)

theorem right_congr
    {initial first second : InferState}
    (extension : initial.FactorizingTraceExtension first)
    (equality : first = second) :
    initial.FactorizingTraceExtension second := by
  subst second
  exact extension

theorem snd_of_eq
    {alpha : Type} {initial final : InferState} {pair : alpha × InferState}
    {value : alpha}
    (extension : initial.FactorizingTraceExtension pair.2)
    (equality : pair = (value, final)) :
    initial.FactorizingTraceExtension final := by
  exact extension.right_congr (congrArg Prod.snd equality)

/-- Any transformation that leaves the chronological solve list unchanged
preserves the invariant. -/
theorem of_solves_eq
    {earlier later : InferState}
    (equation : later.trace.solves = earlier.trace.solves) :
    earlier.FactorizingTraceExtension later := by
  intro admissible
  unfold InferState.FactorizingTrace at admissible ⊢
  rw [equation]
  exact admissible

end InferState.FactorizingTraceExtension

/-! ## Atomic and allocation-only updates -/

theorem InferState.factorizingTraceExtension_recordEvent
    (state : InferState) (event : TraceEvent) :
    state.FactorizingTraceExtension (state.recordEvent event) :=
  fun admissible => admissible.recordEvent event

theorem InferState.factorizingTraceExtension_recordSource
    (state : InferState) (source : ProducerSource) :
    state.FactorizingTraceExtension (state.recordSource source) :=
  fun admissible => admissible.recordSource source

theorem InferState.factorizingTraceExtension_protectMatcherCapability
    (state : InferState) (capability : Cap) :
    state.FactorizingTraceExtension
      (state.protectMatcherCapability capability) :=
  fun admissible => admissible.protectMatcherCapability capability

theorem InferState.factorizingTraceExtension_freezeCapabilityExport
    (state : InferState) (capImages : List CapVar)
    (exportedPayload : Ty) :
    state.FactorizingTraceExtension
      (state.freezeCapabilityExport capImages exportedPayload) :=
  fun admissible => admissible.freezeCapabilityExport capImages exportedPayload

theorem InferState.factorizingTraceExtension_freshTy
    (state : InferState) (origin : ConstraintOrigin) :
    state.FactorizingTraceExtension (state.freshTy origin).2 := by
  apply InferState.FactorizingTraceExtension.of_solves_eq
  rfl

theorem InferState.factorizingTraceExtension_freshCap
    (state : InferState) (origin : ConstraintOrigin) :
    state.FactorizingTraceExtension (state.freshCap origin).2 := by
  apply InferState.FactorizingTraceExtension.of_solves_eq
  rfl

theorem instantiateSchemeInState_factorizingTraceExtension
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : NamedScheme) :
    state.FactorizingTraceExtension
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  apply InferState.FactorizingTraceExtension.of_solves_eq
  rfl

theorem instantiateCtorInState_factorizingTraceExtension
    (state : InferState) (scheme : CtorScheme) :
    state.FactorizingTraceExtension (instantiateCtorInState state scheme).2 := by
  apply InferState.FactorizingTraceExtension.of_solves_eq
  rfl

theorem instantiateDualInState_factorizingTraceExtension
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (state : InferState) (scheme : DualScheme) :
    state.FactorizingTraceExtension
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  apply InferState.FactorizingTraceExtension.of_solves_eq
  rfl

theorem instantiateSchemeInState_factorizingTraceExtension_of_eq
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state final : InferState} {scheme : NamedScheme} {target : Ty}
    (success : instantiateSchemeInState signature rawContext normalizedContext
      name state scheme = (target, final)) :
    state.FactorizingTraceExtension final := by
  exact InferState.FactorizingTraceExtension.snd_of_eq
    (instantiateSchemeInState_factorizingTraceExtension signature rawContext
      normalizedContext name state scheme) success

theorem instantiateCtorInState_factorizingTraceExtension_of_eq
    {state final : InferState} {scheme : CtorScheme}
    {arguments : List Ty} {target : Ty}
    (success : instantiateCtorInState state scheme =
      ((arguments, target), final)) :
    state.FactorizingTraceExtension final := by
  exact InferState.FactorizingTraceExtension.snd_of_eq
    (instantiateCtorInState_factorizingTraceExtension state scheme) success

theorem instantiateDualInState_factorizingTraceExtension_of_eq
    {signature : FrozenSig} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {state final : InferState} {scheme : DualScheme}
    {arguments : List Dual} {target : Dual}
    (success : instantiateDualInState signature rawContext rawParameters
      rawBindings context parameters bindings state scheme =
      ((arguments, target), final)) :
    state.FactorizingTraceExtension final := by
  exact InferState.FactorizingTraceExtension.snd_of_eq
    (instantiateDualInState_factorizingTraceExtension signature rawContext
      rawParameters rawBindings context parameters bindings state scheme)
    success

theorem runResolvedConstraint_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {constraint : Constraint}
    (success : runResolvedConstraint state origin constraint = some result) :
    state.FactorizingTraceExtension result :=
  fun admissible => runResolvedConstraint_factorizingTrace admissible success

theorem runConstraint_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin} {raw : Constraint}
    (success : runConstraint state origin raw = some result) :
    state.FactorizingTraceExtension result :=
  fun admissible => runConstraint_factorizingTrace admissible success

/-! ## Non-recursive traversal boundaries -/

theorem visit_factorizingTraceExtension
    (state : InferState) (kind : NodeKind) (path : SyntaxPath) :
    state.FactorizingTraceExtension (visit state kind path) :=
  state.factorizingTraceExtension_recordEvent _

theorem finishExpr_factorizingTraceExtension
    (expression : Expr) (path : SyntaxPath) (target : Ty)
    (state : InferState) :
    state.FactorizingTraceExtension
      (finishExpr expression path target state).state :=
  state.factorizingTraceExtension_recordEvent _

theorem recordSelfReference_factorizingTraceExtension
    (state : InferState) (binder : String) (placeholder : Ty)
    (path : SyntaxPath) :
    state.FactorizingTraceExtension
      (recordSelfReference state binder placeholder path) :=
  (state.factorizingTraceExtension_recordEvent _).trans
    (InferState.factorizingTraceExtension_recordSource _ _)

/-! ## Alignment helpers -/

theorem alignTypesCore_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypesCore state origin left right = some result) :
    state.FactorizingTraceExtension result := by
  unfold alignTypesCore at success
  simp only at success
  split at success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_factorizingTraceExtension firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      exact first.trans
        (runResolvedConstraint_factorizingTraceExtension restSuccess)
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_factorizingTraceExtension firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      exact first.trans
        (runResolvedConstraint_factorizingTraceExtension restSuccess)
  · exact runResolvedConstraint_factorizingTraceExtension success

theorem alignTypes_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some result) :
    state.FactorizingTraceExtension result := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, coreSuccess, finished⟩
  have resultEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (state.prevailing.apply left)
      (state.prevailing.apply right)) = result :=
    Option.some.inj finished
  exact ((alignTypesCore_factorizingTraceExtension coreSuccess).trans
    (aligned.factorizingTraceExtension_recordEvent _)).right_congr resultEq

theorem alignAtSlot_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {inferred expected : Ty}
    (success : alignAtSlot state origin inferred expected = some result) :
    state.FactorizingTraceExtension result := by
  unfold alignAtSlot at success
  simp only at success
  split at success
  · exact runResolvedConstraint_factorizingTraceExtension success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_factorizingTraceExtension firstSuccess
    split at restSuccess <;> try contradiction
    exact first.trans
      (runResolvedConstraint_factorizingTraceExtension restSuccess)
  · exact alignTypes_factorizingTraceExtension success

theorem alignExprResultAtExpected_factorizingTraceExtension
    {path : SyntaxPath} {expressionResult : ExprResult}
    {expected : Ty} {result : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some result) :
    expressionResult.state.FactorizingTraceExtension result := by
  unfold alignExprResultAtExpected at success
  cases alignmentEq : alignAtSlot expressionResult.state
      (freshOrigin .expression path "expected-type")
      (expectedCoercionSource expressionResult.state expressionResult.target
        expected) expected with
  | none => simp [alignmentEq] at success
  | some aligned =>
      simp only [alignmentEq, Option.some.injEq] at success
      subst result
      exact (alignAtSlot_factorizingTraceExtension alignmentEq).trans
        (aligned.factorizingTraceExtension_recordEvent _)

theorem alignDuals_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some result) :
    state.FactorizingTraceExtension result := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, firstSuccess, secondSuccess⟩
  rcases Option.bind_eq_some_iff.mp secondSuccess with
    ⟨aligned, alignSuccess, finished⟩
  have resultEq : aligned.recordEvent (.dualAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (left.applySubst state.prevailing)
      (right.applySubst state.prevailing)) = result :=
    Option.some.inj finished
  exact ((runResolvedConstraint_factorizingTraceExtension firstSuccess).trans
      ((alignTypes_factorizingTraceExtension alignSuccess).trans
        (aligned.factorizingTraceExtension_recordEvent _))).right_congr resultEq

theorem alignDualLists_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : List Dual}
    (success : alignDualLists state origin left right = some result) :
    state.FactorizingTraceExtension result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignDualLists] at success
      subst result
      exact InferState.FactorizingTraceExtension.refl state
  | cons head tail induction =>
      cases right with
      | nil => simp [alignDualLists] at success
      | cons expected expecteds =>
          simp only [alignDualLists] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignDuals_factorizingTraceExtension firstSuccess).trans
            (induction restSuccess)

theorem alignPatternTargets_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some result) :
    state.FactorizingTraceExtension result := by
  induction duals generalizing state targets with
  | nil =>
      cases targets <;> simp [alignPatternTargets] at success
      subst result
      exact InferState.FactorizingTraceExtension.refl state
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignTypes_factorizingTraceExtension firstSuccess).trans
            (induction restSuccess)

theorem alignBindings_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : MonoCtx}
    (success : alignBindings state origin left right = some result) :
    state.FactorizingTraceExtension result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignBindings] at success
      subst result
      exact InferState.FactorizingTraceExtension.refl state
  | cons entry entries induction =>
      cases right with
      | nil => simp [alignBindings] at success
      | cons expected expecteds =>
          simp only [alignBindings] at success
          split at success
          · rcases Option.bind_eq_some_iff.mp success with
              ⟨middle, firstSuccess, restSuccess⟩
            exact (alignTypes_factorizingTraceExtension firstSuccess).trans
              (induction restSuccess)
          · exact absurd success (by simp)

/-! ## Fresh structural evidence and recursive placeholders -/

theorem freshenSkeleton_factorizingTraceExtension
    {observable origin evidence state capability result}
    (success : freshenSkeleton observable origin evidence state =
      some (capability, result)) :
    state.FactorizingTraceExtension result := by
  apply freshenSkeleton.induct
    (motive_1 := fun evidence state => ∀ capability result,
      freshenSkeleton observable origin evidence state =
          some (capability, result) →
        state.FactorizingTraceExtension result)
    (motive_2 := fun evidence state => ∀ capabilities result,
      freshenSkeletonList observable origin evidence state =
          some (capabilities, result) →
        state.FactorizingTraceExtension result)
    (motive_3 := fun mask evidence state => ∀ capabilities result,
      freshenSkeletonMasked observable origin mask evidence state =
          some (capabilities, result) →
        state.FactorizingTraceExtension result)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true })
  case case10 t x state mismatchNil mismatchCons capabilities result success =>
    cases x <;> cases t <;> simp_all [freshenSkeletonMasked]
  all_goals first
    | assumption
    | exact InferState.FactorizingTraceExtension.refl _
    | grind [InferState.factorizingTraceExtension_freshCap,
        InferState.FactorizingTraceExtension.refl,
        InferState.FactorizingTraceExtension.trans,
        Option.bind_eq_some_iff, freshenSkeleton,
        freshenSkeletonList, freshenSkeletonMasked]

theorem recursiveMatcherTemplate_factorizingTraceExtension
    {signature path clauses state capability result}
    (success : recursiveMatcherTemplate signature path clauses state =
      some (capability, result)) :
    state.FactorizingTraceExtension result := by
  unfold recursiveMatcherTemplate at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨evidence, skeleton, finished⟩
  cases evidence with
  | unseen =>
      cases finished
      exact InferState.FactorizingTraceExtension.refl state
  | known leaf => exact freshenSkeleton_factorizingTraceExtension finished
  | con name children => exact freshenSkeleton_factorizingTraceExtension finished
  | prod components => exact freshenSkeleton_factorizingTraceExtension finished

theorem buildFixPlaceholder_factorizingTraceExtension
    {signature path body state domain codomain result}
    (success : buildFixPlaceholder signature path body state =
      some (domain, codomain, result)) :
    state.FactorizingTraceExtension result := by
  cases body <;> simp_all [buildFixPlaceholder]
  case matcher clauses =>
    rcases Option.bind_eq_some_iff.mp success with
      ⟨pair, recursiveSuccess, rest⟩
    rcases pair with ⟨capability, middle⟩
    have recursiveExtension :=
      recursiveMatcherTemplate_factorizingTraceExtension recursiveSuccess
    simp only [Option.some.injEq, Prod.mk.injEq] at rest
    split at rest
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveExtension.trans
        ((InferState.factorizingTraceExtension_freshTy _ _).trans
          (InferState.factorizingTraceExtension_freshTy _ _))
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveExtension.trans
        ((InferState.factorizingTraceExtension_freshCap _ _).trans
          ((InferState.factorizingTraceExtension_freshTy _ _).trans
            (InferState.factorizingTraceExtension_freshTy _ _)))
  all_goals
    rcases success with ⟨_, _, rfl⟩
    exact (InferState.factorizingTraceExtension_freshTy _ _).trans
      (InferState.factorizingTraceExtension_freshTy _ _)

/-! ## Pattern-constructor and finite fresh-list helpers -/

theorem freshPatternCtorAssignments_factorizingTraceExtension
    {origin : ConstraintOrigin} {variables : List TypePM.TyVar}
    {state result : InferState} {assignments : Projection.Assignments}
    (success : freshPatternCtorAssignments origin variables state =
      (assignments, result)) :
    state.FactorizingTraceExtension result := by
  induction variables generalizing state assignments result with
  | nil =>
      simp only [freshPatternCtorAssignments, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact InferState.FactorizingTraceExtension.refl state
  | cons varId variables induction =>
      simp only [freshPatternCtorAssignments] at success
      let fresh := state.freshCap origin
      cases restEq : freshPatternCtorAssignments origin variables fresh.2 with
      | mk restAssignments restState =>
          simp only [fresh, restEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact (InferState.factorizingTraceExtension_freshCap state origin).trans
            (induction restEq)

theorem alignPatternCtorCapabilities_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {children : List Cap} {demands : List (Option Cap)}
    (success : alignPatternCtorCapabilities state origin children demands =
      some result) :
    state.FactorizingTraceExtension result := by
  induction children generalizing state demands with
  | nil =>
      cases demands <;> simp [alignPatternCtorCapabilities] at success
      subst result
      exact InferState.FactorizingTraceExtension.refl state
  | cons child children induction =>
      cases demands with
      | nil => simp [alignPatternCtorCapabilities] at success
      | cons demand demands =>
          cases demand with
          | none =>
              simpa only [alignPatternCtorCapabilities] using induction success
          | some expected =>
              simp only [alignPatternCtorCapabilities] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨middle, firstSuccess, restSuccess⟩
              exact
                (runResolvedConstraint_factorizingTraceExtension
                  firstSuccess).trans (induction restSuccess)

theorem solvePatternCtorCapability_factorizingTraceExtension
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {childCaps : List Cap}
    {state result : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin childCaps
      state = some (capability, result)) :
    state.FactorizingTraceExtension result := by
  unfold solvePatternCtorCapability at success
  simp only at success
  split at success
  · exact freshenSkeleton_factorizingTraceExtension success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨resultVariables, _resultVariablesEq, rest⟩
    let uniqueVariables := resultVariables.eraseDups
    let allocated := freshPatternCtorAssignments origin uniqueVariables state
    rcases allocatedEq : allocated with ⟨assignments, allocatedState⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨demands, _demandsEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨alignedState, alignmentEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨projected, _projectionEq, skeletonEq⟩
    have allocationEq :
        freshPatternCtorAssignments origin uniqueVariables state =
          (assignments, allocatedState) := by
      simpa [allocated] using allocatedEq
    rw [allocationEq] at alignmentEq
    exact
      (freshPatternCtorAssignments_factorizingTraceExtension allocationEq).trans
        ((alignPatternCtorCapabilities_factorizingTraceExtension
          alignmentEq).trans
          (freshenSkeleton_factorizingTraceExtension skeletonEq))

theorem freshTargets_factorizingTraceExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {count : Nat} {targets : List Ty}
    (success : freshTargets state origin count = (targets, result)) :
    state.FactorizingTraceExtension result := by
  induction count generalizing state targets result with
  | zero =>
      simp only [freshTargets, Prod.mk.injEq] at success
      rcases success with ⟨_, equality⟩
      subst result
      exact InferState.FactorizingTraceExtension.refl state
  | succ count induction =>
      simp only [freshTargets] at success
      let fresh := state.freshTy origin
      let rest := freshTargets fresh.2 origin count
      have first : state.FactorizingTraceExtension fresh.2 :=
        InferState.factorizingTraceExtension_freshTy state origin
      have restExtension : fresh.2.FactorizingTraceExtension rest.2 :=
        induction (state := fresh.2) (targets := rest.1)
          (result := rest.2) rfl
      have finalEq : rest.2 = result := congrArg Prod.snd success
      subst result
      exact first.trans restExtension

/-! ## Primitive-pattern traversals -/

set_option maxHeartbeats 1000000 in
theorem inferPPatFuel_factorizingTraceExtension
    {fuel signature path pattern target state result}
    (success : inferPPatFuel fuel signature path pattern target state =
      some result) :
    state.FactorizingTraceExtension result.state := by
  apply inferPPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferPPatFuel fuel signature path pattern target state = some result →
        state.FactorizingTraceExtension result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferPPatsFuel fuel signature path index patterns targets state =
            some result →
          state.FactorizingTraceExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferPPatFuel, inferPPatsFuel, Option.some.injEq]
  all_goals try
    have ctorExtension := instantiateCtorInState_factorizingTraceExtension_of_eq
      (by assumption)
  all_goals try
    have alignmentExtension :=
      alignTypes_factorizingTraceExtension (by assumption)
  all_goals try
    have freshExtension := freshTargets_factorizingTraceExtension (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.FactorizingTraceExtension.refl _
    | grind [InferState.FactorizingTraceExtension.refl,
        InferState.FactorizingTraceExtension.trans,
        InferState.FactorizingTraceExtension.snd_of_eq,
        InferState.FactorizingTraceExtension.right_congr,
        InferState.factorizingTraceExtension_freshCap,
        instantiateCtorInState_factorizingTraceExtension,
        instantiateCtorInState_factorizingTraceExtension_of_eq,
        InferState.factorizingTraceExtension_freezeCapabilityExport,
        alignTypes_factorizingTraceExtension,
        freshTargets_factorizingTraceExtension,
        visit_factorizingTraceExtension,
        InferState.factorizingTraceExtension_recordEvent,
        Option.bind_eq_some_iff, inferPPatFuel, inferPPatsFuel]

theorem inferPPatsFuel_factorizingTraceExtension
    {fuel signature path index patterns targets state result}
    (success : inferPPatsFuel fuel signature path index patterns targets state =
      some result) :
    state.FactorizingTraceExtension result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferPPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferPPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.FactorizingTraceExtension.refl state
          | cons target targets => simp [inferPPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferPPatsFuel] at success
          | cons target targets =>
              simp only [inferPPatsFuel] at success
              cases headEq : inferPPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferPPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact
                          (inferPPatFuel_factorizingTraceExtension headEq).trans
                            (induction (index := index + 1)
                              (patterns := patterns) (targets := targets)
                              (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

set_option maxHeartbeats 1000000 in
theorem inferDPatFuel_factorizingTraceExtension
    {fuel signature path pattern target state result}
    (success : inferDPatFuel fuel signature path pattern target state =
      some result) :
    state.FactorizingTraceExtension result.state := by
  apply inferDPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferDPatFuel fuel signature path pattern target state = some result →
        state.FactorizingTraceExtension result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferDPatsFuel fuel signature path index patterns targets state =
            some result →
          state.FactorizingTraceExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferDPatFuel, inferDPatsFuel, Option.some.injEq]
  all_goals try
    have ctorExtension := instantiateCtorInState_factorizingTraceExtension_of_eq
      (by assumption)
  all_goals try
    have alignmentExtension :=
      alignTypes_factorizingTraceExtension (by assumption)
  all_goals try
    have freshExtension := freshTargets_factorizingTraceExtension (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.FactorizingTraceExtension.refl _
    | grind [InferState.FactorizingTraceExtension.refl,
        InferState.FactorizingTraceExtension.trans,
        InferState.FactorizingTraceExtension.snd_of_eq,
        InferState.FactorizingTraceExtension.right_congr,
        instantiateCtorInState_factorizingTraceExtension,
        instantiateCtorInState_factorizingTraceExtension_of_eq,
        InferState.factorizingTraceExtension_freezeCapabilityExport,
        alignTypes_factorizingTraceExtension,
        freshTargets_factorizingTraceExtension,
        visit_factorizingTraceExtension,
        InferState.factorizingTraceExtension_recordEvent,
        Option.bind_eq_some_iff, inferDPatFuel, inferDPatsFuel]

theorem inferDPatsFuel_factorizingTraceExtension
    {fuel signature path index patterns targets state result}
    (success : inferDPatsFuel fuel signature path index patterns targets state =
      some result) :
    state.FactorizingTraceExtension result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferDPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferDPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.FactorizingTraceExtension.refl state
          | cons target targets => simp [inferDPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferDPatsFuel] at success
          | cons target targets =>
              simp only [inferDPatsFuel] at success
              cases headEq : inferDPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferDPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact
                          (inferDPatFuel_factorizingTraceExtension headEq).trans
                            (induction (index := index + 1)
                              (patterns := patterns) (targets := targets)
                              (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

/-! ## The mutually recursive expression traversal -/

set_option maxHeartbeats 1000000 in
private theorem inferExprFuel_factorizingTraceExtensionCore
    {fuel signature context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result) :
    state.FactorizingTraceExtension result.state := by
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression state =>
      ∀ result,
        inferExprFuel fuel signature context selfEnv path expression state =
            some result →
          state.FactorizingTraceExtension result.state)
    (motive2 := fun fuel signature context selfEnv path expression expected
        state =>
      ∀ result,
        checkExprFuel fuel signature context selfEnv path expression expected
            state = some result →
          state.FactorizingTraceExtension result)
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern state =>
      ∀ result,
        inferPatternFuel fuel signature context parameters bindings selfEnv path
            pattern state = some result →
          state.FactorizingTraceExtension result.state)
    (motive4 := fun fuel signature context parameters bindings selfEnv path
        index patterns state =>
      ∀ result,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            path index patterns state = some result →
          state.FactorizingTraceExtension result.state)
    (motive5 := fun fuel signature context selfEnv path clauses state =>
      ∀ result,
        inferMatcherFuel fuel signature context selfEnv path clauses state =
            some result →
          state.FactorizingTraceExtension result.state)
    (motive6 := fun fuel signature context selfEnv path index clauses target
        state =>
      ∀ result,
        inferClausesFuel fuel signature context selfEnv path index clauses target
            state = some result →
          state.FactorizingTraceExtension result.state)
    (motive7 := fun fuel signature context selfEnv path clause target state =>
      ∀ result,
        inferClauseFuel fuel signature context selfEnv path clause target state =
            some result →
          state.FactorizingTraceExtension result.state)
    (motive8 := fun fuel signature context selfEnv bindings path index arms
        target bodyTarget state =>
      ∀ result,
        checkArmsFuel fuel signature context selfEnv bindings path index arms
            target bodyTarget state = some result →
          state.FactorizingTraceExtension result)
    (motive9 := fun fuel signature context selfEnv path index expressions
        expecteds state =>
      ∀ result,
        checkExprsFuel fuel signature context selfEnv path index expressions
            expecteds state = some result →
          state.FactorizingTraceExtension result)
    (motive10 := fun fuel signature context selfEnv path index expressions
        state =>
      ∀ result,
        inferExprsFuel fuel signature context selfEnv path index expressions
            state = some result →
          state.FactorizingTraceExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [Option.some.injEq, inferExprFuel, checkExprFuel, inferPatternFuel,
      inferPatternsFuel, inferMatcherFuel, inferClausesFuel, inferClauseFuel,
      checkArmsFuel, checkExprsFuel, inferExprsFuel]
  all_goals try
    have placeholderExtension :=
      buildFixPlaceholder_factorizingTraceExtension (by assumption)
  all_goals try
    have dpatExtension := inferDPatFuel_factorizingTraceExtension (by assumption)
  all_goals try
    have ppatExtension := inferPPatFuel_factorizingTraceExtension (by assumption)
  all_goals try
    have alignmentExtension :=
      alignTypes_factorizingTraceExtension (by assumption)
  all_goals try
    have slotAlignmentExtension :=
      alignAtSlot_factorizingTraceExtension (by assumption)
  all_goals try
    have expectedAlignmentExtension :=
      alignExprResultAtExpected_factorizingTraceExtension (by assumption)
  all_goals try
    have dualAlignmentExtension :=
      alignDuals_factorizingTraceExtension (by assumption)
  all_goals try
    have dualListExtension :=
      alignDualLists_factorizingTraceExtension (by assumption)
  all_goals try
    have patternTargetsExtension :=
      alignPatternTargets_factorizingTraceExtension (by assumption)
  all_goals try
    have bindingAlignmentExtension :=
      alignBindings_factorizingTraceExtension (by assumption)
  all_goals try
    have patternCtorCapabilityExtension :=
      solvePatternCtorCapability_factorizingTraceExtension (by assumption)
  all_goals try
    have skeletonExtension :=
      freshenSkeleton_factorizingTraceExtension (by assumption)
  all_goals try
    have recursiveMatcherExtension :=
      recursiveMatcherTemplate_factorizingTraceExtension (by assumption)
  all_goals try
    have schemeExtension :=
      instantiateSchemeInState_factorizingTraceExtension_of_eq (by assumption)
  all_goals try
    have ctorExtension :=
      instantiateCtorInState_factorizingTraceExtension_of_eq (by assumption)
  all_goals try
    have dualInstanceExtension :=
      instantiateDualInState_factorizingTraceExtension_of_eq (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.FactorizingTraceExtension.refl _
    | grind [visit_factorizingTraceExtension,
        finishExpr_factorizingTraceExtension,
        recordSelfReference_factorizingTraceExtension,
        instantiateSchemeInState_factorizingTraceExtension,
        instantiateCtorInState_factorizingTraceExtension,
        instantiateDualInState_factorizingTraceExtension,
        InferState.factorizingTraceExtension_freshTy,
        InferState.factorizingTraceExtension_freshCap,
        InferState.factorizingTraceExtension_protectMatcherCapability,
        InferState.factorizingTraceExtension_freezeCapabilityExport,
        InferState.factorizingTraceExtension_recordEvent,
        InferState.factorizingTraceExtension_recordSource,
        alignTypes_factorizingTraceExtension,
        alignAtSlot_factorizingTraceExtension,
        alignExprResultAtExpected_factorizingTraceExtension,
        alignDuals_factorizingTraceExtension,
        alignDualLists_factorizingTraceExtension,
        alignBindings_factorizingTraceExtension,
        alignPatternTargets_factorizingTraceExtension,
        solvePatternCtorCapability_factorizingTraceExtension,
        runResolvedConstraint_factorizingTraceExtension,
        freshenSkeleton_factorizingTraceExtension,
        recursiveMatcherTemplate_factorizingTraceExtension,
        buildFixPlaceholder_factorizingTraceExtension,
        inferPPatFuel_factorizingTraceExtension,
        inferDPatFuel_factorizingTraceExtension,
        freshTargets_factorizingTraceExtension,
        InferState.FactorizingTraceExtension.snd_of_eq,
        InferState.FactorizingTraceExtension.right_congr,
        InferState.FactorizingTraceExtension.refl,
        InferState.FactorizingTraceExtension.trans]

theorem inferExprFuel_factorizingTraceExtension
    {fuel signature context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result) :
    state.FactorizingTraceExtension result.state :=
  inferExprFuel_factorizingTraceExtensionCore success

theorem checkExprFuel_factorizingTraceExtension
    {fuel signature context selfEnv path expression expected state result}
    (success : checkExprFuel fuel signature context selfEnv path expression
      expected state = some result) :
    state.FactorizingTraceExtension result := by
  cases fuel with
  | zero => simp [checkExprFuel] at success
  | succ fuel =>
      simp only [checkExprFuel] at success
      cases inferredEq : inferExprFuel fuel signature context selfEnv path
          expression state with
      | none => simp [inferredEq] at success
      | some inferred =>
          simp only [inferredEq] at success
          exact (inferExprFuel_factorizingTraceExtension inferredEq).trans
            (alignExprResultAtExpected_factorizingTraceExtension success)

theorem checkExprsFuel_factorizingTraceExtension
    {fuel signature context selfEnv path index expressions expecteds state result}
    (success : checkExprsFuel fuel signature context selfEnv path index
      expressions expecteds state = some result) :
    state.FactorizingTraceExtension result := by
  induction fuel generalizing index expressions expecteds state result with
  | zero => simp [checkExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          cases expecteds with
          | nil =>
              simp only [checkExprsFuel, Option.some.injEq] at success
              subst result
              exact InferState.FactorizingTraceExtension.refl state
          | cons expected expecteds => simp [checkExprsFuel] at success
      | cons expression expressions =>
          cases expecteds with
          | nil => simp [checkExprsFuel] at success
          | cons expected expecteds =>
              simp only [checkExprsFuel] at success
              cases headEq : checkExprFuel fuel signature context selfEnv
                  (index :: path) expression expected state with
              | none => simp [headEq] at success
              | some middle =>
                  simp only [headEq] at success
                  exact
                    (checkExprFuel_factorizingTraceExtension headEq).trans
                      (induction (index := index + 1)
                        (expressions := expressions) (expecteds := expecteds)
                        (state := middle) (result := result) success)

theorem inferExprsFuel_factorizingTraceExtension
    {fuel signature context selfEnv path index expressions state result}
    (success : inferExprsFuel fuel signature context selfEnv path index
      expressions state = some result) :
    state.FactorizingTraceExtension result.state := by
  induction fuel generalizing index expressions state result with
  | zero => simp [inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [inferExprsFuel, Option.some.injEq] at success
          subst result
          exact InferState.FactorizingTraceExtension.refl state
      | cons expression expressions =>
          simp only [inferExprsFuel] at success
          cases headEq : inferExprFuel fuel signature context selfEnv
              (index :: path) expression state with
          | none => simp [headEq] at success
          | some head =>
              cases tailEq : inferExprsFuel fuel signature context selfEnv path
                  (index + 1) expressions head.state with
              | none => simp [headEq, tailEq] at success
              | some tail =>
                  simp [headEq, tailEq] at success
                  subst result
                  exact
                    (inferExprFuel_factorizingTraceExtension headEq).trans
                      (induction (index := index + 1)
                        (expressions := expressions) (state := head.state)
                        (result := tail) tailEq)

/-! ## Pattern traversal companions -/

private structure PatternFactorizingTraceExtensionAtFuel
    (fuel : Nat) : Prop where
  one : ∀ {signature context parameters bindings selfEnv path pattern state
      result},
    inferPatternFuel fuel signature context parameters bindings selfEnv path
      pattern state = some result →
    state.FactorizingTraceExtension result.state
  many : ∀ {signature context parameters bindings selfEnv path index patterns
      state result},
    inferPatternsFuel fuel signature context parameters bindings selfEnv path
      index patterns state = some result →
    state.FactorizingTraceExtension result.state

set_option maxHeartbeats 1000000 in
private theorem patternFactorizingTraceExtensionAtFuel
    (fuel : Nat) : PatternFactorizingTraceExtensionAtFuel fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp_all [inferPatternFuel, inferPatternsFuel]
  | succ fuel ih =>
      refine { one := ?_, many := ?_ }
      · intro signature context parameters bindings selfEnv path pattern state
          result success
        cases pattern with
        | pvar name =>
            simp only [inferPatternFuel] at success
            split at success <;> try contradiction
            simp only [Option.some.injEq] at success
            subst result
            exact
              ((InferState.factorizingTraceExtension_freshCap _ _).trans
                ((InferState.factorizingTraceExtension_freshTy _ _).trans
                  ((InferState.factorizingTraceExtension_recordEvent _ _).trans
                    ((visit_factorizingTraceExtension _ _ _).trans
                      (InferState.factorizingTraceExtension_recordEvent _ _)))))
        | wild =>
            simp only [inferPatternFuel, Option.some.injEq] at success
            subst result
            exact
              ((InferState.factorizingTraceExtension_freshCap _ _).trans
                ((InferState.factorizingTraceExtension_freshTy _ _).trans
                  ((InferState.factorizingTraceExtension_recordEvent _ _).trans
                    ((visit_factorizingTraceExtension _ _ _).trans
                      (InferState.factorizingTraceExtension_recordEvent _ _)))))
        | pval expression =>
            simp only [inferPatternFuel] at success
            cases bodyEq : inferExprFuel fuel signature
                (bindings.toContext ++ context) selfEnv (0 :: path) expression
                (visit state .patternValue path) with
            | none => simp [bodyEq] at success
            | some bodyResult =>
                simp [bodyEq] at success
                subst result
                exact (visit_factorizingTraceExtension state .patternValue
                    path).trans
                  ((inferExprFuel_factorizingTraceExtension bodyEq).trans
                    ((InferState.factorizingTraceExtension_freshCap _ _).trans
                      ((InferState.factorizingTraceExtension_recordEvent
                        _ _).trans
                        (InferState.factorizingTraceExtension_recordEvent _ _))))
        | embed name =>
            simp only [inferPatternFuel] at success
            cases lookup : parameters.find? name with
            | none => simp [lookup] at success
            | some dual =>
                simp [lookup] at success
                subst result
                exact (visit_factorizingTraceExtension state .patternEmbed
                    path).trans
                  (InferState.factorizingTraceExtension_recordEvent _ _)
        | ptuple patterns =>
            simp only [inferPatternFuel] at success
            cases childrenEq : inferPatternsFuel fuel signature context
                parameters bindings selfEnv path 0 patterns
                (visit state .patternTuple path) with
            | none => simp [childrenEq] at success
            | some children =>
                simp [childrenEq] at success
                subst result
                exact (visit_factorizingTraceExtension state .patternTuple
                    path).trans
                  ((ih.many childrenEq).trans
                    (InferState.factorizingTraceExtension_recordEvent _ _))
        | pctor name patterns =>
            simp only [inferPatternFuel] at success
            cases lookup : signature.findPatternCtor name with
            | none => simp [lookup] at success
            | some entry =>
                simp only [lookup] at success
                generalize instEq : instantiateCtorInState state entry.scheme =
                  instantiation at success
                rcases instantiation with ⟨⟨expectedTargets, resultTarget⟩,
                  instState⟩
                dsimp only at success
                cases childrenEq : inferPatternsFuel fuel signature context
                    parameters bindings selfEnv path 0 patterns
                    (visit instState .patternCtor path) with
                | none => simp [childrenEq] at success
                | some children =>
                    simp only [childrenEq] at success
                    cases alignmentEq : alignPatternTargets children.state
                        (freshOrigin .pattern path
                          "pattern-constructor-fields") children.duals
                        expectedTargets with
                    | none => simp [alignmentEq] at success
                    | some aligned =>
                        simp only [alignmentEq] at success
                        cases capabilityEq : solvePatternCtorCapability
                            signature entry
                            (freshOrigin .pattern path
                              "pattern-constructor-capability")
                            (children.duals.map Dual.cap) aligned with
                        | none =>
                            rw [capabilityEq] at success <;> contradiction
                        | some solved =>
                            rcases solved with ⟨capability, solvedState⟩
                            rw [capabilityEq] at success
                            try simp only at success
                            split at success
                            · simp only [Option.some.injEq] at success
                              subst result
                              let exportPayload := capabilityExportPayload
                                [capability]
                                (resultTarget ::
                                  children.bindings.map fun entry => entry.2)
                              let frozenState :=
                                solvedState.freezeCapabilityExport
                                  (freshCapImages state.supply
                                    entry.scheme.capBinders)
                                  exportPayload
                              have frozenExtension :
                                  solvedState.FactorizingTraceExtension
                                    frozenState := by
                                exact
                                  InferState.factorizingTraceExtension_freezeCapabilityExport
                                    solvedState
                                    (freshCapImages state.supply
                                      entry.scheme.capBinders)
                                    exportPayload
                              have finishedExtension :
                                  solvedState.FactorizingTraceExtension
                                    ((frozenState.recordEvent
                                      (.patternCtorCompatibility
                                        frozenState.trace.solves.length name
                                        (children.duals.map Dual.cap)
                                        capability)).recordEvent
                                      (.inferredPattern (.pctor name patterns)
                                        ⟨capability, resultTarget⟩
                                        children.bindings path)) := by
                                exact frozenExtension.trans
                                  ((InferState.factorizingTraceExtension_recordEvent
                                    _ _).trans
                                    (InferState.factorizingTraceExtension_recordEvent
                                      _ _))
                              exact
                                (instantiateCtorInState_factorizingTraceExtension_of_eq
                                  instEq).trans
                                ((visit_factorizingTraceExtension instState
                                  .patternCtor path).trans
                                  ((ih.many childrenEq).trans
                                    ((alignPatternTargets_factorizingTraceExtension
                                      alignmentEq).trans
                                      ((solvePatternCtorCapability_factorizingTraceExtension
                                        capabilityEq).trans
                                        finishedExtension))))
                            · contradiction
        | pand left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternAnd path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context
                    parameters leftResult.bindings selfEnv (1 :: path) right
                    leftResult.state with
                | none => simp [leftEq, rightEq] at success
                | some rightResult =>
                    cases alignmentEq : alignDuals rightResult.state
                        (freshOrigin .pattern path "pattern-and")
                        leftResult.dual rightResult.dual with
                    | none => simp [leftEq, rightEq, alignmentEq] at success
                    | some aligned =>
                        simp [leftEq, rightEq, alignmentEq] at success
                        subst result
                        exact (visit_factorizingTraceExtension state .patternAnd
                            path).trans
                          ((ih.one leftEq).trans
                            ((ih.one rightEq).trans
                              ((alignDuals_factorizingTraceExtension
                                alignmentEq).trans
                                (InferState.factorizingTraceExtension_recordEvent
                                  _ _))))
        | por left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternOr path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context
                    parameters bindings selfEnv (1 :: path) right
                    leftResult.state with
                | none => simp [leftEq, rightEq] at success
                | some rightResult =>
                    cases alignmentEq : alignDuals rightResult.state
                        (freshOrigin .pattern path "pattern-or")
                        leftResult.dual rightResult.dual with
                    | none => simp [leftEq, rightEq, alignmentEq] at success
                    | some aligned =>
                        cases bindingsEq : alignBindings aligned
                            (freshOrigin .pattern path "pattern-or-bindings")
                            leftResult.bindings rightResult.bindings with
                        | none =>
                            simp [leftEq, rightEq, alignmentEq, bindingsEq]
                              at success
                        | some alignedBindings =>
                            simp [leftEq, rightEq, alignmentEq, bindingsEq]
                              at success
                            subst result
                            exact (visit_factorizingTraceExtension state
                                .patternOr path).trans
                              ((ih.one leftEq).trans
                                ((ih.one rightEq).trans
                                  ((alignDuals_factorizingTraceExtension
                                    alignmentEq).trans
                                    ((alignBindings_factorizingTraceExtension
                                      bindingsEq).trans
                                      (InferState.factorizingTraceExtension_recordEvent
                                        _ _)))))
        | papp name patterns =>
            simp only [inferPatternFuel] at success
            cases lookup : signature.findPatternFun name with
            | none => simp [lookup] at success
            | some scheme =>
                simp only [lookup] at success
                let normalizedContext := context.applySubst state.prevailing
                let normalizedParameters :=
                  parameters.applySubst state.prevailing
                let normalizedBindings :=
                  bindings.applySubst state.prevailing
                generalize instEq : instantiateDualInState signature context
                    parameters bindings normalizedContext normalizedParameters
                    normalizedBindings state scheme = instantiation at success
                rcases instantiation with ⟨⟨expectedArgs, resultDual⟩,
                  instState⟩
                dsimp [normalizedContext, normalizedParameters,
                  normalizedBindings] at instEq
                dsimp only at success
                cases childrenEq : inferPatternsFuel fuel signature context
                    parameters bindings selfEnv path 0 patterns
                    (visit instState .patternApp path) with
                | none => simp [childrenEq] at success
                | some children =>
                    simp only [childrenEq] at success
                    cases alignmentEq : alignDualLists children.state
                        (freshOrigin .pattern path
                          "pattern-function-arguments")
                        children.duals expectedArgs with
                    | none => simp [alignmentEq] at success
                    | some aligned =>
                        simp only [alignmentEq] at success
                        simp only [Option.some.injEq] at success
                        subst result
                        exact
                          (instantiateDualInState_factorizingTraceExtension_of_eq
                            instEq).trans
                          ((visit_factorizingTraceExtension instState .patternApp
                            path).trans
                            ((ih.many childrenEq).trans
                              ((alignDualLists_factorizingTraceExtension
                                alignmentEq).trans
                                (InferState.factorizingTraceExtension_recordEvent
                                  _ _))))
      · intro signature context parameters bindings selfEnv path index patterns
          state result success
        cases patterns with
        | nil =>
            simp only [inferPatternsFuel, Option.some.injEq] at success
            subst result
            exact InferState.FactorizingTraceExtension.refl state
        | cons pattern patterns =>
            simp only [inferPatternsFuel] at success
            cases headEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (index :: path) pattern state with
            | none => simp [headEq] at success
            | some head =>
                cases tailEq : inferPatternsFuel fuel signature context
                    parameters head.bindings selfEnv path (index + 1) patterns
                    head.state with
                | none => simp [headEq, tailEq] at success
                | some tail =>
                    simp [headEq, tailEq] at success
                    subst result
                    exact (ih.one headEq).trans
                      (ih.many (result := tail) tailEq)

theorem inferPatternFuel_factorizingTraceExtension
    {fuel signature context parameters bindings selfEnv path pattern state result}
    (success : inferPatternFuel fuel signature context parameters bindings
      selfEnv path pattern state = some result) :
    state.FactorizingTraceExtension result.state :=
  (patternFactorizingTraceExtensionAtFuel fuel).one success

theorem inferPatternsFuel_factorizingTraceExtension
    {fuel signature context parameters bindings selfEnv path index patterns state
      result}
    (success : inferPatternsFuel fuel signature context parameters bindings
      selfEnv path index patterns state = some result) :
    state.FactorizingTraceExtension result.state :=
  (patternFactorizingTraceExtensionAtFuel fuel).many success

/-! ## Arms, clauses, and matchers -/

theorem checkArmsFuel_factorizingTraceExtension
    {fuel signature context selfEnv bindings path index arms target bodyTarget
      state result}
    (success : checkArmsFuel fuel signature context selfEnv bindings path index
      arms target bodyTarget state = some result) :
    state.FactorizingTraceExtension result := by
  induction fuel generalizing index arms state result with
  | zero => simp [checkArmsFuel] at success
  | succ fuel induction =>
      cases arms with
      | nil =>
          simp only [checkArmsFuel, Option.some.injEq] at success
          subst result
          exact InferState.FactorizingTraceExtension.refl state
      | cons arm arms =>
          rcases arm with ⟨dataPattern, body⟩
          simp only [checkArmsFuel] at success
          cases dataEq : inferDPatFuel fuel signature (0 :: index :: path)
              dataPattern target state with
          | none => simp [dataEq] at success
          | some dataResult =>
              simp only [dataEq] at success
              by_cases distinct : namesDisjoint dataResult.bindings.names
                  bindings.names = true
              · rw [if_pos distinct] at success
                cases bodyEq : checkExprFuel fuel signature
                    (dataResult.bindings.toContext ++
                      (bindings.toContext ++ context))
                    (selfEnv.eraseMany
                      (bindings.names ++ dataResult.bindings.names))
                    (1 :: index :: path) body bodyTarget dataResult.state with
                | none => simp_all
                | some middle =>
                    have tailSuccess : checkArmsFuel fuel signature context
                        selfEnv bindings path (index + 1) arms target bodyTarget
                        middle = some result := by
                      simpa only [bodyEq, List.append_assoc] using success
                    exact
                      (inferDPatFuel_factorizingTraceExtension dataEq).trans
                        ((checkExprFuel_factorizingTraceExtension bodyEq).trans
                          (induction (index := index + 1) (arms := arms)
                            (state := middle) (result := result) tailSuccess))
              · rw [if_neg distinct] at success
                contradiction

theorem inferClauseFuel_factorizingTraceExtension
    {fuel signature context selfEnv path clause target state result}
    (success : inferClauseFuel fuel signature context selfEnv path clause target
      state = some result) :
    state.FactorizingTraceExtension result.state := by
  cases fuel with
  | zero => simp [inferClauseFuel] at success
  | succ fuel =>
      rcases clause with ⟨primitivePattern, next, arms⟩
      simp only [inferClauseFuel] at success
      cases ppEq : inferPPatFuel fuel signature (0 :: path) primitivePattern
          target (visit state .clause path) with
      | none => simp [ppEq] at success
      | some ppResult =>
          simp only [ppEq] at success
          cases nextEq : decomposeME next ppResult.holes.length with
          | none => simp [nextEq] at success
          | some nextMatchers =>
              simp only [nextEq] at success
              cases nextMatchersEq : checkExprsFuel fuel signature context
                  selfEnv (1 :: path) 0 nextMatchers
                  (ppResult.holes.map fun hole =>
                    Ty.slot hole.cap hole.target)
                  ppResult.state with
              | none => simp [nextMatchersEq] at success
              | some middle =>
                  simp [nextMatchersEq] at success
                  cases armsEq : checkArmsFuel fuel signature context selfEnv
                      ppResult.bindings (2 :: path) 0 arms target
                      (Ty.listT (prodTy (ppResult.holes.map Dual.target)))
                      middle with
                  | none => simp [armsEq] at success
                  | some final =>
                      simp only [armsEq] at success
                      have resultStateEq : final = result.state :=
                        congrArg ClauseResult.state (Option.some.inj success)
                      exact ((visit_factorizingTraceExtension state .clause
                          path).trans
                        ((inferPPatFuel_factorizingTraceExtension ppEq).trans
                          ((checkExprsFuel_factorizingTraceExtension
                            nextMatchersEq).trans
                            (checkArmsFuel_factorizingTraceExtension
                              armsEq)))).right_congr resultStateEq

theorem inferClausesFuel_factorizingTraceExtension
    {fuel signature context selfEnv path index clauses target state result}
    (success : inferClausesFuel fuel signature context selfEnv path index clauses
      target state = some result) :
    state.FactorizingTraceExtension result.state := by
  induction fuel generalizing index clauses state result with
  | zero => simp [inferClausesFuel] at success
  | succ fuel induction =>
      cases clauses with
      | nil =>
          simp only [inferClausesFuel, Option.some.injEq] at success
          subst result
          exact InferState.FactorizingTraceExtension.refl state
      | cons clause clauses =>
          simp only [inferClausesFuel] at success
          cases headEq : inferClauseFuel fuel signature context selfEnv
              (index :: path) clause target state with
          | none => simp [headEq] at success
          | some head =>
              cases tailEq : inferClausesFuel fuel signature context selfEnv path
                  (index + 1) clauses target head.state with
              | none => simp [headEq, tailEq] at success
              | some tail =>
                  simp [headEq, tailEq] at success
                  subst result
                  exact
                    (inferClauseFuel_factorizingTraceExtension headEq).trans
                      (induction (index := index + 1) (clauses := clauses)
                        (state := head.state) (result := tail) tailEq)

theorem inferMatcherFuel_factorizingTraceExtension
    {fuel signature context selfEnv path clauses state result}
    (success : inferMatcherFuel fuel signature context selfEnv path clauses
      state = some result) :
    state.FactorizingTraceExtension result.state := by
  cases fuel with
  | zero => simp [inferMatcherFuel] at success
  | succ fuel =>
      simp only [inferMatcherFuel] at success
      generalize freshEq : state.freshTy
          (freshOrigin .matcherClause path "matcher-target") = fresh at success
      rcases fresh with ⟨target, freshState⟩
      cases clausesEq : inferClausesFuel fuel signature context selfEnv path 0
          clauses target freshState with
      | none => simp [clausesEq] at success
      | some clausesResult =>
          simp only [clausesEq] at success
          cases evidenceEq : collectClauseEvidence signature.toMatcherSig
              clauses
              (clausesResult.rawHoleLists.map fun holes =>
                (holes.map
                  (Dual.applySubst clausesResult.state.prevailing)).map
                    Dual.cap) with
          | none =>
              rw [evidenceEq] at success
              contradiction
          | some evidence =>
              rw [evidenceEq] at success
              cases shapeEq : Shape.inferShape signature.observability evidence
                  with
              | none => simp [shapeEq] at success
              | some capability =>
                  try simp only [shapeEq] at success
                  split at success
                  · simp only [Option.some.injEq] at success
                    subst result
                    have freshExtension :
                        state.FactorizingTraceExtension freshState :=
                      InferState.FactorizingTraceExtension.snd_of_eq
                        (InferState.factorizingTraceExtension_freshTy state
                          (freshOrigin .matcherClause path "matcher-target"))
                        freshEq
                    exact freshExtension.trans
                      ((inferClausesFuel_factorizingTraceExtension
                        clausesEq).trans
                        ((InferState.factorizingTraceExtension_recordEvent
                          _ _).trans
                          ((InferState.factorizingTraceExtension_recordEvent
                            _ _).trans
                            (InferState.factorizingTraceExtension_protectMatcherCapability
                              _ _))))
                  · contradiction

/-! ## Complete raw inference -/

theorem enforceProtectedResult_factorizingTraceExtension
    {input output : ExprResult}
    (success : enforceProtectedResult input = some output) :
    input.state.FactorizingTraceExtension output.state := by
  have equality : input = output := (enforceProtectedResult_sound success).1
  exact (InferState.FactorizingTraceExtension.refl input.state).right_congr
    (congrArg ExprResult.state equality)

theorem inferRaw_factorizingTraceExtension
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : inferRaw signature context expression = some result) :
    (initialState signature context).FactorizingTraceExtension result.state := by
  unfold inferRaw at success
  cases core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) with
  | none => simp [core] at success
  | some raw =>
      have guarded : enforceProtectedResult raw = some result := by
        simpa [core] using success
      exact (inferExprFuel_factorizingTraceExtension core).trans
        (enforceProtectedResult_factorizingTraceExtension guarded)

/-- Every complete successful raw inference run has local factorization at
each solve cut. -/
theorem inferRaw_factorizingTrace
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : inferRaw signature context expression = some result) :
    result.state.FactorizingTrace := by
  apply inferRaw_factorizingTraceExtension success
  unfold initialState
  exact InferState.factorizingTrace_empty (initialSupply signature context)

end Inference
end TypePM
