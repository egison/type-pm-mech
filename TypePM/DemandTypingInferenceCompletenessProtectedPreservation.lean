import TypePM.DemandTypingInferenceCompletenessProtectedTrace
import TypePM.Bounds

/-!
# Protected-producer preservation through allocation helpers

The chronological solver cases are handled in
`DemandTypingInferenceCompletenessProtectedTrace`.  This module supplies the
remaining state-only boundaries used by the completeness traversal: fresh
allocation and the three scheme-instantiation helpers.

The two structural-allocation cases need the ordinary traversal bounds.  A
protected variable lies below the current supply, so boundedness of the
prevailing substitution puts its variable image below that supply as well;
fresh structural entries therefore cannot overwrite that image.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessProtectedPreservation

open Inference
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessProtectedTrace

/-- A protected producer image lies below the current capability cut whenever
both its source variable and the prevailing substitution are bounded there. -/
private theorem protectedImage_below
    {state : InferState}
    (bounded : state.prevailing.BoundedBy state.supply)
    (below : ProtectedCapsBelowSupply state)
    {varId image : CapVar}
    (membership : varId ∈ state.protectedCaps)
    (equation : state.prevailing.cap varId = .var image) :
    image.id < state.supply.nextCap := by
  have imageMembership : image ∈ (state.prevailing.cap varId).fcv := by
    rw [equation]
    exact List.mem_singleton_self image
  exact bounded.capImagesBounded varId (below varId membership) image
    imageMembership

/-- Allocating a target metavariable changes neither the current producer
images nor their origin policy. -/
theorem CurrentProtectedProducerSafe.freshTy
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (origin : ConstraintOrigin) :
    CurrentProtectedProducerSafe (state.freshTy origin).2 := by
  change SafeCapVars state.capabilityOrigins state.prevailing.cap
    state.protectedCaps
  exact safe

/-- A fresh structural capability cannot overwrite an old protected image.
The explicit boundedness premises are already fields of every traversal-state
correspondence used by inference completeness. -/
theorem CurrentProtectedProducerSafe.freshCap
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (bounded : state.prevailing.BoundedBy state.supply)
    (below : ProtectedCapsBelowSupply state)
    (origin : ConstraintOrigin) :
    CurrentProtectedProducerSafe (state.freshCap origin).2 := by
  change SafeCapVars
    (state.capabilityOrigins.setOrigin ⟨state.supply.nextCap⟩
      .structuralFlexible)
    state.prevailing.cap state.protectedCaps
  intro varId membership
  rcases safe varId membership with ⟨image, equation, imageSafe⟩
  refine ⟨image, ?_, ?_⟩
  · exact equation
  · have imageBelow := protectedImage_below bounded below membership
      equation
    have different : ⟨state.supply.nextCap⟩ ≠ image := by
      intro equal
      subst image
      exact Nat.lt_irrefl _ imageBelow
    simpa [InferState.freshCap, InferState.recordEvent,
      CapabilityOriginLedger.originOf_setOrigin_of_ne _ _ _ different] using
      imageSafe

/-- Context-scheme instantiation freezes all newly exported capability
images.  Old producer images remain safe under a rename-only ledger update;
new images are fixed by boundedness at the incoming supply. -/
theorem CurrentProtectedProducerSafe.instantiateSchemeInState
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (bounded : state.prevailing.BoundedBy state.supply)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (scheme : Scheme) :
    CurrentProtectedProducerSafe
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  let freshIds := Scheme.canonicalCapImages state.supply scheme
  have oldSafe : SafeCapVars
      (state.capabilityOrigins.setOrigins freshIds .renameOnly)
      state.prevailing.cap state.protectedCaps :=
    SafeCapVars.setOrigins_renameOnly safe
  change SafeCapVars
    (state.capabilityOrigins.setOrigins freshIds .renameOnly)
    state.prevailing.cap (state.protectedCaps ++ freshIds)
  intro varId membership
  rcases List.mem_append.mp membership with old | fresh
  · exact oldSafe varId old
  · refine ⟨varId, ?_, ?_⟩
    · have above := (Scheme.mem_canonicalCapImages_bounds fresh).1
      exact bounded.capFixedAbove varId above
    · have frozen := CapabilityOriginLedger.originOf_setOrigins_of_mem
        state.capabilityOrigins freshIds varId .renameOnly fresh
      rw [frozen]
      simp

/-- Constructor instantiation allocates structural variables without exporting
them yet.  Existing protected images lie below the allocation cut and hence
are disjoint from the fresh constructor range. -/
theorem CurrentProtectedProducerSafe.instantiateCtorInState
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (bounded : state.prevailing.BoundedBy state.supply)
    (below : ProtectedCapsBelowSupply state)
    (scheme : CtorScheme) :
    CurrentProtectedProducerSafe
      (Inference.instantiateCtorInState state scheme).2 := by
  change SafeCapVars
    (state.capabilityOrigins.setOrigins
      (freshCapImages state.supply scheme.capBinders) .structuralFlexible)
    state.prevailing.cap state.protectedCaps
  intro varId membership
  rcases safe varId membership with ⟨image, equation, imageSafe⟩
  refine ⟨image, ?_, ?_⟩
  · exact equation
  · have imageBelow := protectedImage_below bounded below membership
      equation
    have notFresh : image ∉ freshCapImages state.supply scheme.capBinders := by
      intro fresh
      have above : state.supply.nextCap ≤ image.id := by
        simp only [freshCapImages] at fresh
        rcases List.mem_map.mp fresh with ⟨binder, _, rfl⟩
        exact Nat.le_add_right _ _
      exact Nat.not_le_of_lt imageBelow above
    rw [CapabilityOriginLedger.originOf_setOrigins_eq, if_neg notFresh]
    exact imageSafe

/-- Dual-scheme instantiation exports and freezes all of its fresh capability
images, just like ordinary context-scheme instantiation. -/
theorem CurrentProtectedProducerSafe.instantiateDualInState
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (bounded : state.prevailing.BoundedBy state.supply)
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (scheme : DualScheme) :
    CurrentProtectedProducerSafe
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  let freshIds := freshCapImages state.supply scheme.capBinders
  have oldSafe : SafeCapVars
      (state.capabilityOrigins.setOrigins freshIds .renameOnly)
      state.prevailing.cap state.protectedCaps :=
    SafeCapVars.setOrigins_renameOnly safe
  change SafeCapVars
    (state.capabilityOrigins.setOrigins freshIds .renameOnly)
    state.prevailing.cap (state.protectedCaps ++ freshIds)
  intro varId membership
  rcases List.mem_append.mp membership with old | fresh
  · exact oldSafe varId old
  · refine ⟨varId, ?_, ?_⟩
    · have above : state.supply.nextCap ≤ varId.id := by
        simp only [freshIds, freshCapImages] at fresh
        rcases List.mem_map.mp fresh with ⟨binder, _, rfl⟩
        exact Nat.le_add_right _ _
      exact bounded.capFixedAbove varId above
    · have frozen := CapabilityOriginLedger.originOf_setOrigins_of_mem
        state.capabilityOrigins freshIds varId .renameOnly fresh
      rw [frozen]
      simp

end DemandTypingInferenceCompletenessProtectedPreservation
end TypePM
