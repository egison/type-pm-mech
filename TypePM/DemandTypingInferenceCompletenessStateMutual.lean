import TypePM.DemandTypingInferenceCompletenessState

/-!
# Mutual prevailing-state correspondence

One-sided factorization is enough to show that every declarative solve is a
competitor of the executable solver.  Coercion selection also needs the
converse direction: substitutions cannot erase an already visible outer type
constructor, so mutually-instantiating states expose the same matcher/slot
skeleton.  This module packages that stronger invariant and proves that an
ordinary paired cut preserves it without choosing a canonical MGU
orientation.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessStateMutual

open Inference
open DemandTypingInferenceCompletenessState

/-- The DD and executable prevailing substitutions mutually factor through
one another.  The forward residual remains origin-admissible because it is
the direction subsequently used as an executable solver competitor. -/
def MutualStateCorrespondence (ledger : CapabilityOriginLedger)
    (declarative : Subst) (executable : InferState) : Prop :=
  StateCorrespondence ledger declarative executable ∧
    ∃ reverseResidual,
      executable.prevailing = Subst.seq reverseResidual declarative

/-- Initially the two prevailing states coincide. -/
theorem MutualStateCorrespondence.refl
    (ledger : CapabilityOriginLedger) (state : InferState) :
    MutualStateCorrespondence ledger state.prevailing state := by
  refine ⟨StateCorrespondence.refl ledger state, Subst.id, ?_⟩
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (state.prevailing.cap varId)).symm
  · funext varId
    change state.prevailing.target varId =
      Subst.id.apply (state.prevailing.target varId)
    rw [Subst.apply_id]

/-- Reconstruction events do not affect either direction. -/
theorem MutualStateCorrespondence.recordEvent
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (event : TraceEvent) :
    MutualStateCorrespondence ledger declarative
      (state.recordEvent event) := by
  rcases relation with ⟨forward, reverseResidual, reverseEquation⟩
  exact ⟨forward.recordEvent event, reverseResidual,
    by simpa using reverseEquation⟩

/-- The executable paired result, transported through the incoming reverse
residual, is a solution of the DD-side constraint. -/
theorem pairedReverseCompetitorSound
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {left right : Ty} {reverseResidual : Subst}
    (reverseEquation :
      state.prevailing = Subst.seq reverseResidual declarative)
    (result : PairedUnification.PairedResult ledger
      (state.prevailing.apply left) (state.prevailing.apply right)) :
    (Subst.seq result.subst reverseResidual).apply
        (declarative.apply left) =
      (Subst.seq result.subst reverseResidual).apply
        (declarative.apply right) := by
  rw [Subst.seq_apply, Subst.seq_apply]
  have leftTransport := congrArg (fun S : Subst => S.apply left)
    reverseEquation
  have rightTransport := congrArg (fun S : Subst => S.apply right)
    reverseEquation
  simp only [Subst.seq_apply] at leftTransport rightTransport
  rw [← leftTransport, ← rightTransport]
  exact result.sound

/-- An ordinary paired DD cut and the corresponding executable solver cut
preserve mutual factorization. -/
theorem MutualStateCorrespondence.pairedCut_recordSolve
    {ledger : CapabilityOriginLedger} {declarative delta : Subst}
    {state : InferState} {left right : Ty} {step : SolveStep}
    (relation : MutualStateCorrespondence ledger declarative state)
    (dd : OriginSafeExactPairedMGU ledger
      (declarative.apply left) (declarative.apply right) delta)
    (result : PairedUnification.PairedResult ledger
      (state.prevailing.apply left) (state.prevailing.apply right))
    (stepDelta : step.delta = result.subst) :
    MutualStateCorrespondence ledger (Subst.seq delta declarative)
      (state.recordSolve step) := by
  rcases relation with ⟨forwardBefore, reverseBefore, reverseEquation⟩
  have forward :=
    DemandTypingInferenceCompletenessState.pairedCut_recordSolve
      forwardBefore dd result stepDelta
  let competitor := Subst.seq result.subst reverseBefore
  have competitorSound :
      competitor.apply (declarative.apply left) =
        competitor.apply (declarative.apply right) :=
    pairedReverseCompetitorSound reverseEquation result
  rcases dd.exact.1.2 competitor competitorSound with
    ⟨reverseAfter, competitorFactors⟩
  refine ⟨forward, reverseAfter, ?_⟩
  rw [InferState.prevailing_recordSolve, stepDelta]
  calc
    Subst.seq result.subst state.prevailing =
        Subst.seq result.subst
          (Subst.seq reverseBefore declarative) := by
      exact congrArg (Subst.seq result.subst) reverseEquation
    _ = Subst.seq competitor declarative :=
      PhasedPost.seq_assoc result.subst reverseBefore declarative
    _ = Subst.seq (Subst.seq reverseAfter delta) declarative := by
      rw [← competitorFactors]
    _ = Subst.seq reverseAfter (Subst.seq delta declarative) :=
      (PhasedPost.seq_assoc reverseAfter delta declarative).symm

end DemandTypingInferenceCompletenessStateMutual
end TypePM
