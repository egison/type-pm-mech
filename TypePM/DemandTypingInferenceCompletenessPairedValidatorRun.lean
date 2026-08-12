import TypePM.DemandTypingInferenceCompletenessCertifiedRun
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation

/-!
# Paired terminal-audit coverage for completeness

The ordinary validator proof is local to the executable trace.  A sensitive
pattern-constructor event is different: its audit fact stores DD operands,
whereas the executable event stores the paired raw operands reconstructed by
the inference run.  This module delays that comparison while carrying the
same `BisimulationExtension` as raw completeness.  At the root terminal cut,
the paired witness projects to the existing exact terminal-audit witness.

This is a completeness-only layer.  It does not change the validator, its
trace conditions, or the public terminal-audit tree.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPairedValidatorRun

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessValidatorBisimulation

/-- A sensitive event justified either exactly, as before, or by paired DD
and executable constructor operands under the current traversal relation. -/
inductive PairedTerminalAuditEventWitness
    (terminal : Subst) (signature : FrozenSig)
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    TraceEvent → Prop where
  | exact
      (witness : TerminalAuditEventWitness terminal signature state event) :
      PairedTerminalAuditEventWitness terminal signature relation event
  | patternCtor
      {solveCount : Nat} {name : String}
      {entry : PatternCtorScheme signature.observability}
      {declarativeDuals executableDuals : List Dual}
      {declarativeCapability executableCapability : Cap}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (lookup : signature.findPatternCtor name = some entry)
      (duals : DualListBisimulation relation declarativeDuals executableDuals)
      (capability : CapBisimulation relation declarativeCapability
        executableCapability)
      (facts : DDTerminalAudit.PatternCtorFacts terminal entry
        declarativeDuals declarativeCapability) :
      PairedTerminalAuditEventWitness terminal signature relation
        (.patternCtorCompatibility solveCount name
          (executableDuals.map Dual.cap) executableCapability)

/-- Paired witnesses transport with the same chronological bisimulation
extension used by the raw completeness package. -/
theorem PairedTerminalAuditEventWitness.transport
    {terminal : Subst} {signature : FrozenSig}
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    (stateExtension : state.StateExtension state')
    {event : TraceEvent}
    (witness : PairedTerminalAuditEventWitness terminal signature before
      event) :
    PairedTerminalAuditEventWitness terminal signature extension.after
      event := by
  cases witness with
  | exact witness =>
      exact .exact (TerminalAuditEventWitness.transport witness
        stateExtension.history)
  | patternCtor solveBound lookup duals capability facts =>
      exact .patternCtor
        (Nat.le_trans solveBound stateExtension.history.solve_length_le)
        lookup
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          extension duals)
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          extension capability)
        facts

/-- At the root cut, paired constructor operands directly satisfy the
executable validator condition.  We deliberately do not manufacture an
`exact` audit witness: its indices require syntactically identical operands,
whereas completeness promises only bisimulation. -/
theorem PairedTerminalAuditEventWitness.patternCtorCondition
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {solveCount : Nat} {name : String} {childCaps : List Cap}
    {resultCap : Cap}
    (witness : PairedTerminalAuditEventWitness terminal signature relation
      (.patternCtorCompatibility solveCount name childCaps resultCap)) :
    solveCount ≤ state.trace.solves.length ∧
      ∃ entry,
        signature.findPatternCtor name = some entry ∧
        entry.CapCompatible
          (childCaps.map fun cap => cap.apply state.prevailing.cap)
          (resultCap.apply state.prevailing.cap) := by
  cases witness with
  | exact witness =>
      exact TerminalAuditEventWitness.patternCtor_condition_bisimulation
        relation witness
  | @patternCtor solveCount name entry declarativeDuals executableDuals
      declarativeCapability executableCapability solveBound lookup duals
      capability facts =>
      have compatible :=
        DDTerminalAudit.PatternCtorFacts.compatible_bisimulation relation
          duals capability facts
      exact ⟨solveBound, entry, lookup, compatible⟩

/-- Pointwise paired coverage of every sensitive event in one trace. -/
def PairedTerminalAuditEventCoverage
    (terminal : Subst) (signature : FrozenSig)
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) : Prop :=
  ∀ event, event ∈ state.trace.events →
    match event with
    | .patternCtorCompatibility _ _ _ _
    | .matcherFinalization _ _ _ _ _ _ _ _
    | .letGeneralization _ _ _ _ _ _ _ =>
        PairedTerminalAuditEventWitness terminal signature relation event
    | _ => True

/-- Root projection of the constructor fragment to the existing validator
condition.  Exact matcher/let witnesses remain available in the other paired
witness branch and are projected by the final whole-trace connector. -/
theorem PairedTerminalAuditEventCoverage.patternCtors
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    (coverage : PairedTerminalAuditEventCoverage terminal signature relation) :
    TracePatternCtorConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | patternCtorCompatibility _ _ _ _ =>
      exact PairedTerminalAuditEventWitness.patternCtorCondition covered
  | _ => trivial

/-- Incremental paired sensitive coverage synchronized with a raw
`BisimulationExtension`.  The relation index makes transport through later
solver suffixes explicit rather than relying on history extension alone. -/
structure PairedTerminalAuditHistoryExtension
    (terminal : Subst) (signature : FrozenSig)
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    (transition : BisimulationExtension before ledger' declarative' final)
    (stateExtension : initial.StateExtension final) :
    Prop where
  newEvents : ∀ event,
    event ∈ final.trace.events → event ∉ initial.trace.events →
      match event with
      | .patternCtorCompatibility _ _ _ _
      | .matcherFinalization _ _ _ _ _ _ _ _
      | .letGeneralization _ _ _ _ _ _ _ =>
          PairedTerminalAuditEventWitness terminal signature transition.after
            event
      | _ => True

/-- Validator chronology used by final completeness: ordinary conditions stay
executable-local, while sensitive conditions use the paired layer above. -/
structure PairedValidatorRunExtension
    (terminal : Subst) (signature : FrozenSig)
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    (transition : BisimulationExtension before ledger' declarative' final)
    (stateExtension : initial.StateExtension final) :
    Prop where
  ordinary : OrdinaryValidatorHistoryExtension signature initial final
  sensitive : PairedTerminalAuditHistoryExtension terminal signature transition
    stateExtension

end DemandTypingInferenceCompletenessPairedValidatorRun
end TypePM
