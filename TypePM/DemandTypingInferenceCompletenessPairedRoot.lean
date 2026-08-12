import TypePM.DemandTypingInferenceCompletenessAcceptance
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessInitial

/-!
# Root projection for paired completeness certificates

Pattern-constructor audit facts mention the operands of the demand-directed derivation,
while the executable trace contains their bisimilar representatives.  This
module closes that intentionally paired chronology at the public root and
projects it directly to the nine finite validator conditions.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPairedRoot

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessValidatorBisimulation
open DemandTypingInferenceCompletenessAcceptance
open DemandTypingInferenceCompletenessProtectedTrace

/-- Empty executable history has vacuous paired sensitive coverage. -/
theorem PairedTerminalAuditEventCoverage.empty
    (terminal : Subst) (signature : FrozenSig)
    (supply : InferenceBase.FreshSupply)
    (relation : StateBisimulation [] Subst.id (InferState.empty supply)) :
    PairedTerminalAuditEventCoverage terminal signature relation := by
  intro event membership
  simp [InferState.empty] at membership

/-- Advance absolute paired coverage through one chronological extension. -/
theorem PairedTerminalAuditHistoryExtension.applyCoverage
    {terminal : Subst} {signature : FrozenSig}
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    {transition : BisimulationExtension before ledger' declarative' final}
    {history : initial.StateExtension final}
    (extension : PairedTerminalAuditHistoryExtension terminal signature
      transition history)
    (coverage : PairedTerminalAuditEventCoverage terminal signature before) :
    PairedTerminalAuditEventCoverage terminal signature transition.after := by
  intro event membership
  by_cases previous : event ∈ initial.trace.events
  · have covered := coverage event previous
    cases event <;> try trivial
    all_goals exact
      (PairedTerminalAuditEventWitness.transport transition history covered)
  · exact extension.newEvents event membership previous

/-- Apply both halves of a paired certified run to the empty public prefix. -/
theorem PairedValidatorRunExtension.applyEmpty
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {final : InferState}
    {before : StateBisimulation [] Subst.id (InferState.empty supply)}
    {transition : BisimulationExtension before ledger declarative final}
    {history : (InferState.empty supply).StateExtension final}
    (extension : PairedValidatorRunExtension terminal signature transition
      history) :
    OpenOrdinaryValidatorEventCoverage signature final ∧
      PairedTerminalAuditEventCoverage terminal signature transition.after := by
  constructor
  · exact extension.ordinary.applyCoverage
      (OpenOrdinaryValidatorEventCoverage.empty signature supply)
  · exact PairedTerminalAuditHistoryExtension.applyCoverage
      extension.sensitive
      (by
        simpa only using
          PairedTerminalAuditEventCoverage.empty terminal signature supply
            before)

/-- Matcher-finalization witnesses are projected either from an exact audit
event or directly from paired demand-directed/executable operands. -/
theorem PairedTerminalAuditEventCoverage.finalizations
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    (coverage : PairedTerminalAuditEventCoverage terminal signature relation) :
    TraceFinalizationSuffixConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | matcherFinalization _ _ _ _ _ _ localEvidence _ =>
      cases covered with
      | exact witness =>
          exact TerminalAuditEventWitness.matcher_condition_bisimulation
            relation armBasic witness
      | matcher solveBound localTargetEq localHolesEq target holes capability
          catchAll binders facts =>
          exact PairedTerminalAuditEventWitness.matcherCondition armBasic
            (.matcher (localEvidence := localEvidence) solveBound localTargetEq
              localHolesEq target
              holes capability catchAll binders facts)
  | _ => trivial

/-- Let-generalization witnesses project from either exact or paired demand-directed /
executable operands. -/
theorem PairedTerminalAuditEventCoverage.generalizations
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    (closed : signature.SchemesClosed)
    (coverage : PairedTerminalAuditEventCoverage terminal signature relation) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | letGeneralization _ _ _ _ _ _ _ =>
      exact PairedTerminalAuditEventWitness.letCondition closed covered
  | _ => trivial

/-- A root synthesis run carrying paired validator chronology. -/
structure PairedRootCertifiedSynthesis
    (signature : FrozenSig) (context : Context) (expression : Expr) : Type where
  finalSupply : InferenceBase.FreshSupply
  terminal : Subst
  ledger : CapabilityOriginLedger
  target : Ty
  run : SynthRunCompletion (initialTraversalState signature context)
    (inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context))
    finalSupply terminal ledger target
  history : (initialState signature context).StateExtension run.result.state
  validation : PairedValidatorRunExtension terminal signature run.transition
    history

def PairedRootCertifiedSynthesis.result
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (root : PairedRootCertifiedSynthesis signature context expression) :
    ExprResult := root.run.result

/-- A paired root certificate discharges public inference acceptance without
an exact-operand fiction at pattern-constructor events. -/
theorem infer_eq_some_of_pairedRoot
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : PairedRootCertifiedSynthesis signature context expression) :
    infer signature context expression = some root.result := by
  have covered := PairedValidatorRunExtension.applyEmpty root.validation
  obtain ⟨ordinary, sensitive⟩ := covered
  have producerSafe : ProtectedProducerTrace root.result.state :=
    (currentProtectedProducerSafe_iff root.result.state).mp
      root.run.protected_safe
  obtain ⟨traversal, types, duals⟩ := ordinary.atTerminal producerSafe
  let ordinaryConditions := TraversalValidatorConditions.ofEventCoverage
    traversal
  apply infer_complete_of_core_and_conditions root.run.success producerSafe
  · exact ordinaryConditions.primitiveHoles
  · exact ordinaryConditions.patternLeaves
  · exact sensitive.patternCtors
  · exact ordinaryConditions.instances
  · exact ordinaryConditions.slots
  · exact types
  · exact duals
  · exact PairedTerminalAuditEventCoverage.finalizations
      signatureWF.armExhaustiveBasic sensitive
  · exact PairedTerminalAuditEventCoverage.generalizations
      signatureWF.schemesClosed sensitive

theorem infer_isSome_of_pairedRoot
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : PairedRootCertifiedSynthesis signature context expression) :
    (infer signature context expression).isSome = true := by
  rw [infer_eq_some_of_pairedRoot signatureWF root]
  rfl

theorem infer_isSome_of_nonempty_pairedRoot
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : Nonempty
      (PairedRootCertifiedSynthesis signature context expression)) :
    (infer signature context expression).isSome = true := by
  rcases root with ⟨root⟩
  exact infer_isSome_of_pairedRoot signatureWF root

end DemandTypingInferenceCompletenessPairedRoot
end TypePM
