import TypePM.DemandTypingInferenceCompletenessAcceptance
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation
import TypePM.DemandTypingInferenceCompletenessInitial
import TypePM.DemandTypingInferenceCompletenessCertifiedRun

/-!
# Public acceptance-completeness facade

This module fixes the final shape of milestone 5 independently of the still
evolving structural dispatcher.  The dispatcher has one remaining job: build
`RootCertifiedSynthesis` from a public `DDTyping` derivation.  Everything after
that point—producer protection, terminal event coverage, the finite validator,
`inferRaw`, and public `infer`—is composed here without a caller-supplied bridge
or an inference-success premise.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPublic

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessAcceptance
open DemandTypingInferenceCompletenessValidatorBisimulation
open DemandTypingInferenceCompletenessProtectedTrace

/-- The sole implementation-facing output expected from the final root
dispatcher.  It contains one concrete successful executable run, its final
DD/executable state relation, and compositional validator coverage.  The
existential indices are internal implementation data and disappear from both
public consequences below. -/
structure RootCertifiedSynthesis
    (signature : FrozenSig) (context : Context) (expression : Expr) : Type where
  finalSupply : InferenceBase.FreshSupply
  terminal : Subst
  ledger : CapabilityOriginLedger
  target : Ty
  certified : CertifiedSynthRunCompletion terminal signature
    (initialTraversalState signature context)
    (inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context))
    finalSupply terminal ledger target

/-- The concrete executable result selected by the certified root run. -/
def RootCertifiedSynthesis.result
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (root : RootCertifiedSynthesis signature context expression) : ExprResult :=
  root.certified.run.result

/-- A root certified synthesis run supplies the four event-coverage packages
consumed by the bisimulation-aware validator theorem. -/
theorem RootCertifiedSynthesis.rootConditions
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (root : RootCertifiedSynthesis signature context expression) :
    TraversalValidatorEventCoverage signature root.result.state ∧
      TerminalAuditEventCoverage root.terminal signature root.result.state ∧
      TraceTypeAlignmentConditions root.result.state ∧
      TraceDualAlignmentConditions root.result.state := by
  have initialOrdinary : OpenOrdinaryValidatorEventCoverage signature
      (initialState signature context) := by
    simpa [initialState] using
      OpenOrdinaryValidatorEventCoverage.empty signature
        (initialSupply signature context)
  have initialSensitive : TerminalAuditEventCoverage root.terminal signature
      (initialState signature context) := by
    simpa [initialState] using
      TerminalAuditEventCoverage.empty root.terminal signature
        (initialSupply signature context)
  let coverage := root.certified.validation.applyCoverage initialOrdinary
    initialSensitive
  have safe : ProtectedProducerTrace root.result.state :=
    (currentProtectedProducerSafe_iff root.result.state).mp
      root.certified.run.protected_safe
  exact coverage.atTerminal safe

/-- Final acceptance completeness after the root dispatcher has constructed
its certificate.  There is no Boolean-check, bridge, solver-success, or raw
inference-success premise. -/
theorem infer_eq_some_of_rootCertified
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : RootCertifiedSynthesis signature context expression) :
    infer signature context expression = some root.result := by
  have producerSafe : ProtectedProducerTrace root.result.state :=
    (currentProtectedProducerSafe_iff root.result.state).mp
      root.certified.run.protected_safe
  obtain ⟨traversal, audit, types, duals⟩ := root.rootConditions
  have raw : inferRaw signature context expression = some root.result :=
    inferRaw_complete_of_core_and_protected root.certified.run.success
      producerSafe
  have checked : wBridgeCheck signature root.result = true :=
    wBridgeCheck_complete_of_rootCoverage
      root.certified.run.transition.after signatureWF traversal audit types duals
  exact infer_complete_of_raw_and_checked raw checked

/-- Boolean acceptance is the direct projection of the concrete result
theorem, not a separate completeness proof. -/
theorem infer_isSome_of_rootCertified
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : RootCertifiedSynthesis signature context expression) :
    (infer signature context expression).isSome = true := by
  rw [infer_eq_some_of_rootCertified signatureWF root]
  rfl

/-- The structural dispatcher recurses over proposition-valued origin and
audit trees, so its natural public output is only nonemptiness of a concrete
root run.  Boolean acceptance is itself a proposition and may eliminate that
proof-erased package without selecting or exposing an executable result. -/
theorem infer_isSome_of_nonempty_rootCertified
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : Nonempty (RootCertifiedSynthesis signature context expression)) :
    (infer signature context expression).isSome = true := by
  rcases root with ⟨root⟩
  exact infer_isSome_of_rootCertified signatureWF root

end DemandTypingInferenceCompletenessPublic
end TypePM
