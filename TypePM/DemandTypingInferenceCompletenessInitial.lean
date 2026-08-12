import TypePM.DemandTypingInferenceCompletenessTraversal

/-!
# Initial state for inference completeness

The public completeness theorem starts the DD derivation and executable
traversal at the same canonical supply, identity substitution, and empty
origin ledger.  This module packages that diagonal once, including every
boundedness and producer-protection invariant required by the traversal
recursion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessInitial

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessIdempotence
open DemandTypingInferenceCompletenessProtectedTrace

/-- Canonical DD/executable correspondence at the public inference entry. -/
def initialTraversalState
    (signature : FrozenSig) (context : Context) :
    TraversalStateCorrespondence
      (initialSupply signature context) Subst.id []
      (initialState signature context) := by
  let state := initialState signature context
  have relation := TraversalStateCorrespondence.refl state
    (initialState_prevailingIdempotent signature context)
    (by simpa [state, initialState, InferState.empty, InferState.prevailing,
        replay, replayFrom] using
      Subst.boundedBy_id (initialSupply signature context))
    (by simpa [state, initialState, InferState.empty] using
      DDLedger.LedgerBelow.empty (initialSupply signature context))
    (initialState_protectedCapOrigins signature context)
    (initialState_protectedCapsBelowSupply signature context)
    (initialState_allocatedCapsRecorded signature context)
    (by
      change CurrentProtectedProducerSafe
        (InferState.empty (initialSupply signature context))
      exact CurrentProtectedProducerSafe.empty
        (initialSupply signature context))
  simpa [state, initialState, InferState.empty, InferState.prevailing,
    replay, replayFrom] using relation

/-- The public initial state has no protected producer to reject. -/
theorem initial_protectedProducerTrace
    (signature : FrozenSig) (context : Context) :
    ProtectedProducerTrace (initialState signature context) := by
  intro varId membership
  simp [initialState, InferState.empty] at membership

end DemandTypingInferenceCompletenessInitial
end TypePM
