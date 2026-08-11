import TypePM.Inference

/-!
# Monotone inference-state extension

`InferState.HistoryPrefix` deliberately records only append-only solver and
event history.  This module packages that property with the two additional
monotonicity facts needed when a later inference cut is compared with an
earlier one: neither fresh counter decreases, and every already protected
capability remains protected.

The capability-origin ledger is intentionally absent.  Origin changes include
policy transitions (for example, freezing a structural capability at an
export boundary), so they do not form one useful global componentwise order.
-/

namespace TypePM
namespace Inference

/-- `later` is a monotone extension of every persistent component of
`earlier`: chronological history, fresh lower bounds, and protected
capabilities. -/
structure InferState.StateExtension (earlier later : InferState) : Prop where
  history : earlier.HistoryPrefix later
  supplyCap : earlier.supply.nextCap ≤ later.supply.nextCap
  supplyTy : earlier.supply.nextTy ≤ later.supply.nextTy
  protectedCaps : ∀ varId, varId ∈ earlier.protectedCaps →
    varId ∈ later.protectedCaps

namespace InferState.StateExtension

/-- State extension is reflexive. -/
theorem refl (state : InferState) : state.StateExtension state where
  history := InferState.HistoryPrefix.refl state
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := fun _ membership => membership

/-- State extensions compose. -/
theorem trans
    {first middle last : InferState}
    (front : first.StateExtension middle)
    (back : middle.StateExtension last) :
    first.StateExtension last where
  history := front.history.trans back.history
  supplyCap := Nat.le_trans front.supplyCap back.supplyCap
  supplyTy := Nat.le_trans front.supplyTy back.supplyTy
  protectedCaps := fun varId membership =>
    back.protectedCaps varId (front.protectedCaps varId membership)

/-- Rewrite the terminal state of a state extension. -/
theorem right_congr
    {initial first second : InferState}
    (extension : initial.StateExtension first) (equality : first = second) :
    initial.StateExtension second := by
  subst second
  exact extension

/-- Eliminate the state component of a successful pair-returning helper. -/
theorem snd_of_eq
    {α : Type} {initial final : InferState} {pair : α × InferState}
    {value : α} (extension : initial.StateExtension pair.2)
    (equality : pair = (value, final)) : initial.StateExtension final := by
  have stateEquality : pair.2 = final := congrArg Prod.snd equality
  exact extension.right_congr stateEquality

end InferState.StateExtension

/-! ## Atomic state updates -/

theorem InferState.stateExtension_recordEvent
    (state : InferState) (event : TraceEvent) :
    state.StateExtension (state.recordEvent event) where
  history := state.historyPrefix_recordEvent event
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := fun _ membership => membership

theorem InferState.stateExtension_recordSolve
    (state : InferState) (step : SolveStep) :
    state.StateExtension (state.recordSolve step) where
  history := state.historyPrefix_recordSolve step
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := fun _ membership => membership

theorem InferState.stateExtension_recordSource
    (state : InferState) (source : ProducerSource) :
    state.StateExtension (state.recordSource source) where
  history := state.historyPrefix_recordSource source
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := fun _ membership => membership

theorem InferState.stateExtension_protectMatcherCapability
    (state : InferState) (capability : Cap) :
    state.StateExtension (state.protectMatcherCapability capability) where
  history := state.historyPrefix_protectMatcherCapability capability
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := by
    intro varId membership
    exact List.mem_append_left _ membership

theorem InferState.stateExtension_freshTy
    (state : InferState) (origin : ConstraintOrigin) :
    state.StateExtension (state.freshTy origin).2 where
  history := state.historyPrefix_freshTy origin
  supplyCap := by
    simp [InferState.freshTy, InferenceBase.freshTyMeta,
      InferState.recordEvent]
  supplyTy := by
    simp only [InferState.freshTy_advances]
    exact Nat.le_add_right _ _
  protectedCaps := by
    intro varId membership
    simpa [InferState.freshTy, InferenceBase.freshTyMeta,
      InferState.recordEvent] using membership

theorem InferState.stateExtension_freshCap
    (state : InferState) (origin : ConstraintOrigin) :
    state.StateExtension (state.freshCap origin).2 where
  history := state.historyPrefix_freshCap origin
  supplyCap := by
    simp only [InferState.freshCap_advances]
    exact Nat.le_add_right _ _
  supplyTy := by
    simp [InferState.freshCap, InferenceBase.freshCapMeta,
      InferState.recordEvent]
  protectedCaps := by
    intro varId membership
    simpa [InferState.freshCap, InferenceBase.freshCapMeta,
      InferState.recordEvent] using membership

theorem InferState.stateExtension_freezeCapabilityExport
    (state : InferState) (capImages : List CapVar)
    (exportedPayload : Ty) :
    state.StateExtension
      (state.freezeCapabilityExport capImages exportedPayload) where
  history := state.historyPrefix_freezeCapabilityExport capImages exportedPayload
  supplyCap := Nat.le_refl _
  supplyTy := Nat.le_refl _
  protectedCaps := by
    intro varId membership
    rw [InferState.freezeCapabilityExport_protectedCaps]
    exact List.mem_append_left _ membership

/-! ## Batch instantiation -/

theorem instantiateSchemeInState_stateExtension
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    state.StateExtension
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 where
  history := instantiateSchemeInState_historyPrefix signature rawContext
    normalizedContext name state scheme
  supplyCap := by
    simp [instantiateSchemeInState, InferenceBase.instantiateScheme,
      Scheme.freshInstantiate, Scheme.advanceSupply, InferState.recordEvent]
  supplyTy := by
    simp [instantiateSchemeInState, InferenceBase.instantiateScheme,
      Scheme.freshInstantiate, Scheme.advanceSupply, InferState.recordEvent]
  protectedCaps := by
    intro varId membership
    simp only [instantiateSchemeInState, InferState.recordEvent]
    exact List.mem_append_left _ membership

theorem instantiateCtorInState_stateExtension
    (state : InferState) (scheme : CtorScheme) :
    state.StateExtension (instantiateCtorInState state scheme).2 where
  history := instantiateCtorInState_historyPrefix state scheme
  supplyCap := by
    simp [instantiateCtorInState, InferenceBase.instantiateCtorScheme,
      InferenceBase.instantiateBinders, InferState.recordEvent]
  supplyTy := by
    simp [instantiateCtorInState, InferenceBase.instantiateCtorScheme,
      InferenceBase.instantiateBinders, InferState.recordEvent]
  protectedCaps := by
    intro varId membership
    simpa [instantiateCtorInState, InferState.recordEvent] using membership

theorem instantiateDualInState_stateExtension
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (state : InferState) (scheme : DualScheme) :
    state.StateExtension
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 where
  history := instantiateDualInState_historyPrefix signature rawContext
    rawParameters rawBindings context parameters bindings state scheme
  supplyCap := by
    simp [instantiateDualInState, InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders, InferState.recordEvent]
  supplyTy := by
    simp [instantiateDualInState, InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders, InferState.recordEvent]
  protectedCaps := by
    intro varId membership
    simp only [instantiateDualInState, InferState.recordEvent]
    exact List.mem_append_left _ membership

theorem instantiateSchemeInState_stateExtension_of_eq
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state final : InferState} {scheme : Scheme} {target : Ty}
    (success : instantiateSchemeInState signature rawContext normalizedContext
      name state scheme = (target, final)) :
    state.StateExtension final := by
  exact InferState.StateExtension.snd_of_eq
    (instantiateSchemeInState_stateExtension signature rawContext
      normalizedContext name state scheme) success

theorem instantiateCtorInState_stateExtension_of_eq
    {state final : InferState} {scheme : CtorScheme}
    {arguments : List Ty} {target : Ty}
    (success : instantiateCtorInState state scheme =
      ((arguments, target), final)) :
    state.StateExtension final := by
  exact InferState.StateExtension.snd_of_eq
    (instantiateCtorInState_stateExtension state scheme) success

theorem instantiateDualInState_stateExtension_of_eq
    {signature : FrozenSig} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {state final : InferState} {scheme : DualScheme}
    {arguments : List Dual} {target : Dual}
    (success : instantiateDualInState signature rawContext rawParameters
      rawBindings context parameters bindings state scheme =
      ((arguments, target), final)) :
    state.StateExtension final := by
  exact InferState.StateExtension.snd_of_eq
    (instantiateDualInState_stateExtension signature rawContext rawParameters
      rawBindings context parameters bindings state scheme) success

/-! ## Single-constraint execution -/

theorem runResolvedConstraint_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {constraint : Constraint}
    (success : runResolvedConstraint state origin constraint = some result) :
    state.StateExtension result := by
  unfold runResolvedConstraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          exact (state.stateExtension_recordSolve step).right_congr
            (Option.some.inj success)
      | producerToSlot _ _ _ _ =>
          change (if capSubstFixesVarsCheck step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          exact (state.stateExtension_recordSolve step).right_congr
            (Option.some.inj success)

theorem runConstraint_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {raw : Constraint}
    (success : runConstraint state origin raw = some result) :
    state.StateExtension result := by
  unfold runConstraint at success
  generalize constraintEquation : raw.resolve state.prevailing = constraint
    at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          exact (state.stateExtension_recordSolve step).right_congr
            (Option.some.inj success)
      | producerToSlot _ _ _ _ =>
          change (if capSubstFixesVarsCheck step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          exact (state.stateExtension_recordSolve step).right_congr
            (Option.some.inj success)

end Inference
end TypePM
