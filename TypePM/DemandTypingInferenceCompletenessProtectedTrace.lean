import TypePM.DemandTypingInferenceCompletenessProtected
import TypePM.InferenceAdmissibleTrace

/-!
# Protected-producer trace composition

The public raw-inference filter inspects the complete replay, rather than one
local solver delta.  These lemmas compose the local origin policy through the
chronological replay without assuming that the DD and executable MGUs choose
the same representatives.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessProtectedTrace

open Inference
open DemandTypingInferenceCompletenessProtected

/-- A non-structural variable remains a non-structural variable under an
origin-admissible capability post. -/
theorem admissible_image_of_nonStructural
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (nonStructural : ledger.originOf varId ≠ .structuralFlexible) :
    ∃ image, post varId = .var image ∧
      ledger.originOf image ≠ .structuralFlexible := by
  cases origin : ledger.originOf varId with
  | rigid =>
      refine ⟨varId, admissible.rigid origin, ?_⟩
      rw [origin]
      simp
  | renameOnly => exact admissible.renameOnly origin
  | structuralFlexible => simp [origin] at nonStructural

/-- Safe producer images compose with a later admissible delta. -/
theorem SafeCapVars.seq_admissible
    {ledger : CapabilityOriginLedger} {earlier later : CapSubst}
    {varIds : List CapVar}
    (safe : SafeCapVars ledger earlier varIds)
    (admissible : AdmissibleCapPost ledger later) :
    SafeCapVars ledger (CapSubst.comp later earlier) varIds := by
  intro varId membership
  rcases safe varId membership with ⟨middle, earlierEq, middleSafe⟩
  rcases admissible_image_of_nonStructural admissible middleSafe with
    ⟨image, laterEq, imageSafe⟩
  refine ⟨image, ?_, imageSafe⟩
  rw [CapSubst.comp, earlierEq]
  exact laterEq

/-- Freezing an arbitrary batch as rename-only cannot invalidate an existing
safe image: selected images become rename-only and all others retain their
old origin. -/
theorem SafeCapVars.setOrigins_renameOnly
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {varIds selected : List CapVar}
    (safe : SafeCapVars ledger post varIds) :
    SafeCapVars (ledger.setOrigins selected .renameOnly) post varIds := by
  intro varId membership
  rcases safe varId membership with ⟨image, equation, imageSafe⟩
  refine ⟨image, equation, ?_⟩
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  split
  · simp
  · exact imageSafe

/-- The executable terminal predicate stated using `prevailing`; this is
definitionally the same replay inspected by `ProtectedProducerTrace`. -/
def CurrentProtectedProducerSafe (state : InferState) : Prop :=
  SafeCapVars state.capabilityOrigins state.prevailing.cap state.protectedCaps

theorem currentProtectedProducerSafe_iff
    (state : InferState) :
    CurrentProtectedProducerSafe state ↔ ProtectedProducerTrace state := by
  rfl

theorem CurrentProtectedProducerSafe.empty
    (supply : InferenceBase.FreshSupply) :
    CurrentProtectedProducerSafe (InferState.empty supply) := by
  intro varId membership
  simp [InferState.empty] at membership

theorem CurrentProtectedProducerSafe.recordEvent
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (event : TraceEvent) :
    CurrentProtectedProducerSafe (state.recordEvent event) := by
  change SafeCapVars state.capabilityOrigins state.prevailing.cap
    state.protectedCaps
  exact safe

theorem CurrentProtectedProducerSafe.recordSource
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (source : ProducerSource) :
    CurrentProtectedProducerSafe (state.recordSource source) := by
  change SafeCapVars state.capabilityOrigins state.prevailing.cap
    state.protectedCaps
  exact safe

/-- Appending one ledger-admissible solve composes its delta after the safe
prefix replay. -/
theorem CurrentProtectedProducerSafe.recordSolve
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (step : SolveStep)
    (snapshot : step.ledgerSnapshot = state.capabilityOrigins)
    (admissible : step.LedgerAdmissible) :
    CurrentProtectedProducerSafe (state.recordSolve step) := by
  have admissibleAtState : AdmissiblePost state.capabilityOrigins
      step.delta := by
    simpa [SolveStep.LedgerAdmissible, snapshot] using admissible
  unfold CurrentProtectedProducerSafe
  rw [InferState.prevailing_recordSolve]
  change SafeCapVars state.capabilityOrigins
    (CapSubst.comp step.delta.cap state.prevailing.cap) state.protectedCaps
  exact SafeCapVars.seq_admissible safe admissibleAtState.cap

/-- Constructor export freezing preserves the complete replay invariant.
New protected leaves occur in a prevailing image and are therefore fixed by
solved form; their origin is changed to rename-only by the freeze itself. -/
theorem CurrentProtectedProducerSafe.freezeCapabilityExport
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (idempotent : state.prevailing.Idempotent)
    (capImages : List CapVar) (payload : Ty) :
    CurrentProtectedProducerSafe
      (state.freezeCapabilityExport capImages payload) := by
  let leaves := capabilityExportLeaves state capImages payload
  have oldSafe : SafeCapVars
      (state.capabilityOrigins.setOrigins leaves .renameOnly)
      state.prevailing.cap state.protectedCaps :=
    SafeCapVars.setOrigins_renameOnly safe
  intro varId membership
  rw [InferState.freezeCapabilityExport_protectedCaps] at membership
  rcases List.mem_append.mp membership with old | fresh
  · exact oldSafe varId old
  · refine ⟨varId, ?_, ?_⟩
    · simp only [capabilityExportLeaves, List.mem_filter,
        List.mem_eraseDups] at fresh
      have imageLeavesMem : varId ∈ capImages.flatMap fun binder =>
          (state.prevailing.cap binder).fcv := fresh.1.1
      rcases List.mem_flatMap.mp imageLeavesMem with
        ⟨binder, binderMem, imageMem⟩
      have inApplied : varId ∈
          (state.prevailing.apply (.matcher (.var binder) .unit)).fcv := by
        simpa [Subst.apply_matcher, Subst.apply_unit, Cap.apply, Ty.fcv] using
          imageMem
      exact idempotent.image_cap_fixed
        (.matcher (.var binder) .unit) varId inApplied
    · rw [InferState.freezeCapabilityExport_origin_of_mem state capImages
        payload varId fresh]
      simp

/-- Final matcher protection is safe once the capability being exported is
already normalized by the prevailing substitution. -/
theorem CurrentProtectedProducerSafe.protectMatcherCapability
    {state : InferState} (safe : CurrentProtectedProducerSafe state)
    (frozen : ProtectedCapOrigins state) (capability : Cap)
    (fixed : capability.apply state.prevailing.cap = capability) :
    CurrentProtectedProducerSafe
      (state.protectMatcherCapability capability) := by
  let selected := matcherProducerLedgerLeaves state.capabilityOrigins capability
  have oldSafe : SafeCapVars
      (state.capabilityOrigins.setOrigins selected .renameOnly)
      state.prevailing.cap state.protectedCaps :=
    SafeCapVars.setOrigins_renameOnly safe
  have afterFrozen := frozen.protectMatcherCapability capability
  intro varId membership
  rw [InferState.mem_protectMatcherCapability_protectedCaps] at membership
  rcases membership with old | fresh
  · exact oldSafe varId old
  · refine ⟨varId, Cap.fixed_of_apply_self capability fixed varId fresh.1,
        afterFrozen varId ?_⟩
    exact (InferState.mem_protectMatcherCapability_protectedCaps state
      capability varId).2 (Or.inr fresh)

end DemandTypingInferenceCompletenessProtectedTrace
end TypePM
