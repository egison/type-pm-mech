import TypePM.DemandTypingInferenceCompletenessGlobalCertified
import TypePM.DemandTypingInferenceCompletenessPairedRoot
import TypePM.DemandTypingInferenceCompletenessInitial

/-!
# Public-root construction from the global paired traversal

The global recursion returns a bounded paired run at an arbitrary traversal
cut.  This module isolates the index normalization needed at the canonical
public entry point and forgets only the raw-target boundedness proof, which is
not consumed by the terminal validator.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessRootBuilder

open Inference
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessPairedRoot

/-- Package a completed global run at the canonical initial state as the
proof-relevant root certificate consumed by the public facade. -/
def pairedRoot_of_initial
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {finalSupply : InferenceBase.FreshSupply} {terminal : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty}
    (certified : BoundedPairedCertifiedSynthRunCompletion terminal signature
      (initialTraversalState signature context)
      (inferExprFuel (inferenceFuel expression) signature context [] []
        expression (initialState signature context))
      finalSupply terminal ledger target) :
    PairedRootCertifiedSynthesis signature context expression where
  finalSupply := finalSupply
  terminal := terminal
  ledger := ledger
  target := target
  run := certified.raw.run
  history := certified.history
  validation := certified.validation

/-- The proposition-valued output of structural recursion can be packaged
without choosing or exposing a concrete executable result. -/
theorem pairedRoot_nonempty_of_initial
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {finalSupply : InferenceBase.FreshSupply} {terminal : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty}
    (certified : Nonempty
      (BoundedPairedCertifiedSynthRunCompletion terminal signature
        (initialTraversalState signature context)
        (inferExprFuel (inferenceFuel expression) signature context [] []
          expression (initialState signature context))
        finalSupply terminal ledger target)) :
    Nonempty (PairedRootCertifiedSynthesis signature context expression) := by
  rcases certified with ⟨certified⟩
  exact ⟨pairedRoot_of_initial certified⟩

end DemandTypingInferenceCompletenessRootBuilder
end TypePM
