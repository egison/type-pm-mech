import TypePM.DemandTyping

/-!
# Terminal protected-producer completeness boundary

The public raw inference filter asks whether the final prevailing capability
substitution maps every protected producer leaf to a non-structural variable.
This module separates that Boolean obligation into the two semantic facts a
traversal-completeness proof must retain: final-ledger admissibility of the
prevailing post and non-structural origin of every protected leaf.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessProtected

open Inference

/-- Every producer leaf retained by the executable state is frozen in the
current ledger (either rigid or rename-only). -/
def ProtectedCapOrigins (state : InferState) : Prop :=
  ∀ varId, varId ∈ state.protectedCaps →
    state.capabilityOrigins.originOf varId ≠ .structuralFlexible

/-- Ledger admissibility sends every non-structural input variable to a
non-structural variable image. -/
theorem safeCapVars_of_admissible
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {varIds : List CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (frozen : ∀ varId, varId ∈ varIds →
      ledger.originOf varId ≠ .structuralFlexible) :
    SafeCapVars ledger post varIds := by
  intro varId membership
  have nonStructural := frozen varId membership
  cases origin : ledger.originOf varId with
  | rigid =>
      refine ⟨varId, admissible.rigid origin, ?_⟩
      simp [origin]
  | renameOnly =>
      exact admissible.renameOnly origin
  | structuralFlexible =>
      exact (nonStructural origin).elim

/-- The semantic facts sufficient for the terminal producer filter. -/
theorem protectedProducerTrace_of_admissible
    (state : InferState)
    (admissible : AdmissiblePost state.capabilityOrigins state.prevailing)
    (frozen : ProtectedCapOrigins state) :
    ProtectedProducerTrace state := by
  exact safeCapVars_of_admissible admissible.cap frozen

/-- Executable form consumed directly by `enforceProtectedResult`. -/
theorem protectedProducerTraceCheck_complete
    (state : InferState)
    (admissible : AdmissiblePost state.capabilityOrigins state.prevailing)
    (frozen : ProtectedCapOrigins state) :
    protectedProducerTraceCheck state = true := by
  exact (protectedProducerTraceCheck_eq_true state).2
    (protectedProducerTrace_of_admissible state admissible frozen)

end DemandTypingInferenceCompletenessProtected
end TypePM
