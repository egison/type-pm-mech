import TypePM.DemandTypingInferenceCompletenessRootBuilder
import TypePM.DemandTypingInferenceCompletenessContextBisimulation

/-!
# Initial specialization of global paired completeness

This module discharges every invariant at the canonical public entry point.
It deliberately takes the global fuel-indexed motive as an internal argument,
so the structural strong-induction theorem can be added without changing the
root packaging or the public boundary.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessGlobalRoot

open Inference
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessPairedRoot
open DemandTypingInferenceCompletenessRootBuilder

/-- Specialize a global paired synthesis motive to a DD derivation beginning
at the canonical supply, identity substitution, empty ledger, empty self
environment, and root syntax path. -/
theorem pairedRoot_of_global
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {rawTarget : Ty} {finalSupply : InferenceBase.FreshSupply}
    {terminal : Subst}
    {derived : DDSynth signature (initialSupply signature context) Subst.id
      context expression rawTarget finalSupply terminal}
    {ledger : CapabilityOriginLedger}
    {origin : DDSynthOrigin signature derived [] ledger}
    (complete : PairedAuditedSynthCompletenessAt terminal signature
      (inferenceFuel expression))
    (audit : DDSynthTerminalAudit terminal signature origin) :
    Nonempty (PairedRootCertifiedSynthesis signature context expression) := by
  let before := initialTraversalState signature context
  have contexts : ContextBisimulation before.prevailing context context :=
    ContextBisimulation.same before.prevailing context
  have contextBounded : Context.BoundedBy (initialSupply signature context)
      context := initialSupply_context_boundedBy signature context
  have adequate : SynthBudgetAdequate (inferenceFuel expression)
      expression := by
    change 8 * (exprTraversalFuel expression + 1) ≤
      8 * (exprTraversalFuel expression + 1)
    exact Nat.le_refl _
  have certified := complete (selfEnv := []) (path := []) before contexts
    contextBounded contextBounded audit adequate
  exact pairedRoot_nonempty_of_initial certified

end DemandTypingInferenceCompletenessGlobalRoot
end TypePM
