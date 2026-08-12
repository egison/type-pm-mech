import TypePM.DemandTypingInferenceCompletenessOneWay
import TypePM.DemandTypingInferenceCompletenessLedgerBisimulation

/-!
# Prevailing-state correspondence for inference completeness

Completeness cannot require the declarative and executable MGUs to be
literally equal: either solver may choose the opposite orientation for a
variable equality.  The invariant used here therefore keeps the DD state as
an admissible instance of the executable prevailing state.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessState

open Inference
open DemandTypingInferenceCompletenessLedgerBisimulation

/-- A DD prevailing substitution is obtained by applying one admissible
residual after the executable prevailing substitution. -/
def StateCorrespondence (ledger : CapabilityOriginLedger)
    (declarative : Subst) (executable : InferState) : Prop :=
  ∃ residual,
    declarative = Subst.seq residual executable.prevailing ∧
      AdmissiblePostBetween executable.capabilityOrigins ledger residual

/-- The initial exact-state case. -/
theorem StateCorrespondence.refl
    (ledger : CapabilityOriginLedger) (state : InferState)
    (ledgerEq : state.capabilityOrigins = ledger) :
    StateCorrespondence ledger state.prevailing state := by
  subst ledger
  refine ⟨Subst.id, ?_, AdmissiblePostBetween.id _⟩
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (state.prevailing.cap varId)).symm
  · funext varId
    change state.prevailing.target varId =
      Subst.id.apply (state.prevailing.target varId)
    rw [Subst.apply_id]

/-- Recording a reconstruction event does not change the state relation. -/
theorem StateCorrespondence.recordEvent
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} (relation : StateCorrespondence ledger declarative state)
    (event : TraceEvent) :
    StateCorrespondence ledger declarative (state.recordEvent event) := by
  rcases relation with ⟨residual, equation, admissible⟩
  exact ⟨residual, by simpa using equation, admissible⟩

/-- Algebraic core of one solver cut.  If an admissible outgoing residual
maps the executable successor to the DD successor, recording the step
preserves state correspondence. -/
theorem stateAfterRecordSolve
    {ledger : CapabilityOriginLedger} {declarativeOutput residual : Subst}
    {state : InferState} {step : SolveStep}
    (equation : declarativeOutput =
      Subst.seq residual (Subst.seq step.delta state.prevailing))
    (admissible : AdmissiblePostBetween state.capabilityOrigins ledger residual) :
    StateCorrespondence ledger declarativeOutput
      (state.recordSolve step) := by
  refine ⟨residual, ?_, admissible⟩
  simpa only [InferState.prevailing_recordSolve] using equation

/-- A paired executable result absorbs the DD delta together with the
incoming state residual.  The conclusion is already phrased as the outgoing
state equation, avoiding any choice of canonical MGU orientation. -/
theorem pairedCut
    {ledger : CapabilityOriginLedger} {declarative delta : Subst}
    {state : InferState} {left right : Ty}
    (relation : StateCorrespondence ledger declarative state)
    (dd : OriginSafeExactPairedMGU ledger
      (declarative.apply left) (declarative.apply right) delta)
    (result : PairedUnification.PairedResult state.capabilityOrigins
      (state.prevailing.apply left) (state.prevailing.apply right)) :
    ∃ residual,
      Subst.seq delta declarative =
        Subst.seq residual (Subst.seq result.subst state.prevailing) ∧
      AdmissiblePostBetween state.capabilityOrigins ledger residual := by
  rcases relation with ⟨incoming, stateEquation, incomingAdmissible⟩
  let combined := Subst.seq delta incoming
  have combinedAdmissible :
      AdmissiblePostBetween state.capabilityOrigins ledger combined :=
    (AdmissiblePostBetween.ofAdmissible dd.admissible).seq
      incomingAdmissible
  have stateApply (target : Ty) :
      incoming.apply (state.prevailing.apply target) =
        declarative.apply target := by
    calc
      incoming.apply (state.prevailing.apply target) =
          (Subst.seq incoming state.prevailing).apply target :=
        (Subst.seq_apply incoming state.prevailing target).symm
      _ = declarative.apply target := by rw [← stateEquation]
  have combinedSound :
      combined.apply (state.prevailing.apply left) =
        combined.apply (state.prevailing.apply right) := by
    simp only [combined, Subst.seq_apply, stateApply]
    exact dd.exact.1.1
  have absorbs : combined = Subst.seq combined result.subst :=
    result.exactPairedMGU.absorbs combinedSound
  refine ⟨combined, ?_, combinedAdmissible⟩
  calc
    Subst.seq delta declarative =
        Subst.seq delta (Subst.seq incoming state.prevailing) := by
      rw [stateEquation]
    _ = Subst.seq combined state.prevailing :=
      PhasedPost.seq_assoc delta incoming state.prevailing
    _ = Subst.seq (Subst.seq combined result.subst) state.prevailing := by
      rw [← absorbs]
    _ = Subst.seq combined
        (Subst.seq result.subst state.prevailing) :=
      (PhasedPost.seq_assoc combined result.subst state.prevailing).symm

/-- State-level paired transition, separated from the executable wrapper so
it remains usable while the wrapper's complete-fuel theorem is established. -/
theorem pairedCut_recordSolve
    {ledger : CapabilityOriginLedger} {declarative delta : Subst}
    {state : InferState} {left right : Ty} {step : SolveStep}
    (relation : StateCorrespondence ledger declarative state)
    (dd : OriginSafeExactPairedMGU ledger
      (declarative.apply left) (declarative.apply right) delta)
    (result : PairedUnification.PairedResult state.capabilityOrigins
      (state.prevailing.apply left) (state.prevailing.apply right))
    (stepDelta : step.delta = result.subst) :
    StateCorrespondence ledger (Subst.seq delta declarative)
      (state.recordSolve step) := by
  rcases pairedCut relation dd result with
    ⟨residual, equation, admissible⟩
  apply stateAfterRecordSolve (residual := residual)
      (admissible := admissible)
  simpa only [stepDelta] using equation

/-- Capability-only counterpart of `pairedCut`.  The incoming residual is
kept paired because it may already contain target-variable information; only
its capability projection participates in this primitive constraint. -/
theorem capabilityCut
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {left right : Cap} {delta : CapSubst}
    (relation : StateCorrespondence ledger declarative state)
    (dd : OriginSafeExactCapMGU ledger
      (left.apply declarative.cap) (right.apply declarative.cap) delta)
    (result : PairedUnification.OrientedCapResult state.capabilityOrigins
      (left.apply state.prevailing.cap) (right.apply state.prevailing.cap)) :
    ∃ residual,
      Subst.seq ⟨delta, TySubst.id⟩ declarative =
        Subst.seq residual
          (Subst.seq ⟨result.subst, TySubst.id⟩ state.prevailing) ∧
      AdmissiblePostBetween state.capabilityOrigins ledger residual := by
  rcases relation with ⟨incoming, stateEquation, incomingAdmissible⟩
  let localDelta : Subst := ⟨delta, TySubst.id⟩
  let combined := Subst.seq localDelta incoming
  have combinedAdmissible :
      AdmissiblePostBetween state.capabilityOrigins ledger combined :=
    (AdmissiblePostBetween.ofAdmissible { cap := dd.admissible }).seq
      incomingAdmissible
  have stateCapApply (capability : Cap) :
      (capability.apply state.prevailing.cap).apply incoming.cap =
        capability.apply declarative.cap := by
    calc
      (capability.apply state.prevailing.cap).apply incoming.cap =
          capability.apply (Subst.seq incoming state.prevailing).cap := by
        exact (Cap.apply_comp incoming.cap state.prevailing.cap capability).symm
      _ = capability.apply declarative.cap := by rw [← stateEquation]
  have sound :
      (left.apply state.prevailing.cap).apply combined.cap =
        (right.apply state.prevailing.cap).apply combined.cap := by
    calc
      (left.apply state.prevailing.cap).apply combined.cap =
          ((left.apply state.prevailing.cap).apply incoming.cap).apply delta := by
        exact Cap.apply_comp delta incoming.cap
          (left.apply state.prevailing.cap)
      _ = (left.apply declarative.cap).apply delta := by rw [stateCapApply]
      _ = (right.apply declarative.cap).apply delta := dd.exact.1.1
      _ = ((right.apply state.prevailing.cap).apply incoming.cap).apply delta := by
        rw [stateCapApply]
      _ = (right.apply state.prevailing.cap).apply combined.cap := by
        exact (Cap.apply_comp delta incoming.cap
          (right.apply state.prevailing.cap)).symm
  have capAbsorbs :
      combined.cap = CapSubst.comp combined.cap result.subst :=
    result.exactCapMGU.absorbs sound
  have absorbs : combined =
      Subst.seq combined ⟨result.subst, TySubst.id⟩ := by
    apply PhasedPost.subst_ext
    · exact capAbsorbs
    · funext varId
      change combined.target varId =
        combined.apply (TySubst.id varId)
      rfl
  refine ⟨combined, ?_, combinedAdmissible⟩
  calc
    Subst.seq ⟨delta, TySubst.id⟩ declarative =
        Subst.seq localDelta (Subst.seq incoming state.prevailing) := by
      rw [stateEquation]
    _ = Subst.seq combined state.prevailing :=
      PhasedPost.seq_assoc localDelta incoming state.prevailing
    _ = Subst.seq (Subst.seq combined
        ⟨result.subst, TySubst.id⟩) state.prevailing := by rw [← absorbs]
    _ = Subst.seq combined
        (Subst.seq ⟨result.subst, TySubst.id⟩ state.prevailing) :=
      (PhasedPost.seq_assoc combined ⟨result.subst, TySubst.id⟩
        state.prevailing).symm

end DemandTypingInferenceCompletenessState
end TypePM
