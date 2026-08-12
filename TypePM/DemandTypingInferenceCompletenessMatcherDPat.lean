import TypePM.DemandTypingInferenceCompletenessMain

/-!
# Heterogeneous data-pattern completeness for matcher arms

Matcher arms may reach their data pattern after earlier solver steps have
changed the executable representation of the shared clause target.  This
module generalizes the primitive data-pattern recursion so the DD target and
the executable target need only be bisimilar.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherDPat

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherMain

def dpatVar_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeTarget executableTarget : Ty}
    (related : TyBisimulation before.prevailing declarativeTarget
      executableTarget) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.var name) executableTarget state)
      q S ledger declarativeTarget [(name, declarativeTarget)] := by
  let event := TraceEvent.inferredDPat (.var name) executableTarget
    [(name, executableTarget)] path
  let final :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord
      before .dpatVar path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .dpatVar path event
  refine
    { result := ⟨executableTarget, [(name, executableTarget)],
        (visit state .dpatVar path).recordEvent event⟩
      success := by simp [inferDPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      protected_safe := final.protected_safe
      target := transition.transportTy related
      bindings := .cons (transition.transportTy related) .nil }

def dpatWild_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeTarget executableTarget : Ty}
    (related : TyBisimulation before.prevailing declarativeTarget
      executableTarget) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path .wild executableTarget state)
      q S ledger declarativeTarget [] := by
  let event := TraceEvent.inferredDPat .wild executableTarget [] path
  let final :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord
      before .dpatWild path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .dpatWild path event
  refine
    { result := ⟨executableTarget, [],
        (visit state .dpatWild path).recordEvent event⟩
      success := by simp [inferDPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      protected_safe := final.protected_safe
      target := transition.transportTy related
      bindings := .nil }

theorem MonoCtxBisimulation.exportPayloadRelated
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarativeContext executableContext : MonoCtx}
    {declarativeTarget executableTarget : Ty}
    (target : TyBisimulation relation declarativeTarget executableTarget)
    (context : MonoCtxBisimulation relation declarativeContext executableContext) :
    TyBisimulation relation
      (capabilityExportPayload []
        (declarativeTarget :: declarativeContext.map fun entry => entry.2))
      (capabilityExportPayload []
        (executableTarget :: executableContext.map fun entry => entry.2)) := by
  unfold capabilityExportPayload
  simp only [List.map_nil, List.nil_append]
  apply tyListBisimulation_prod
  exact .cons target
    (DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.targets
      context)

noncomputable def dpatCtor_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    (patterns : List DPat) {scheme : CtorScheme}
    (lookup : signature.findDataCtor name = some scheme)
    (closed : signature.SchemesClosed)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeTarget executableTarget : Ty}
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (declarativeBounded : declarativeTarget.BoundedBy q)
    (executableBounded : executableTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q scheme) S
      (InferenceBase.instantiateCtorScheme q scheme).value.2
      declarativeTarget S₁)
    {q' : InferenceBase.FreshSupply} {bindings : MonoCtx}
    (children :
      let instantiation := instantiateCtorInState_complete before scheme
      ∀ alignment : StateRunCompletion instantiation.correspondence
          (alignTypes (instantiateCtorInState state scheme).2
            (freshOrigin .dataPattern path "dp-constructor-result")
            (instantiateCtorInState state scheme).1.2 executableTarget)
          (InferenceBase.instantiateCtorScheme q scheme).supply S₁
          (DDLedger.markCtorInstance ledger q scheme),
        DPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (instantiateCtorInState state scheme).1.1 alignment.result)
          q' S' ledger₂
          (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.ctor name patterns)
        executableTarget state)
      q' S' (DDLedger.freezeExport ledger₂ S'
        (freshCapImages q scheme.capBinders)
        (capabilityExportPayload []
          (declarativeTarget :: bindings.map fun entry => entry.2)))
      declarativeTarget bindings := by
  let instantiation := instantiateCtorInState_complete before scheme
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.dataCtors lookup).boundedBy)
  let supplyExtension := SupplyExtends.instantiateCtorScheme q scheme
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .dataPattern path "dp-constructor-result")
    instantiation.correspondence instantiation.target
    (instantiation.transition.transportTy targetRelated)
    instBounded.2 (declarativeBounded.mono supplyExtension)
    (by simpa [Inference.instantiateCtorInState, before.supply_eq] using
      instBounded.2)
    (executableBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let capImages := freshCapImages q scheme.capBinders
  let declarativePayload := capabilityExportPayload []
    (declarativeTarget :: bindings.map fun entry => entry.2)
  let executableBindings := childrenRun.result.bindings
  let executablePayload := capabilityExportPayload []
    (executableTarget :: executableBindings.map fun entry => entry.2)
  let targetAtChildren := childrenRun.transition.transportTy
    (alignment.transition.transportTy
      (instantiation.transition.transportTy targetRelated))
  let payloadRelated := MonoCtxBisimulation.exportPayloadRelated
    targetAtChildren childrenRun.bindings
  let frozen := TraversalStateCorrespondence.freezeCapabilityExportRelated
    childrenRun.completion capImages payloadRelated
  let freezeExtension :=
    TraversalStateCorrespondence.freezeCapabilityExportRelatedExtension
      childrenRun.completion capImages payloadRelated
  let event := TraceEvent.inferredDPat (.ctor name patterns) executableTarget
    executableBindings path
  let visited := frozen.visit .dpatCtor path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let finishExtension := freezeExtension.seq
    (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      frozen .dpatCtor path event)
  let transition := ((instantiation.transition.seq alignment.transition).seq
    childrenRun.transition).seq finishExtension
  refine
    { result := ⟨executableTarget, executableBindings,
        (visit (childrenRun.result.state.freezeCapabilityExport capImages
          executablePayload) .dpatCtor path).recordEvent event⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      protected_safe := final.protected_safe
      target := transition.transportTy targetRelated
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          finishExtension childrenRun.bindings }
  simp only [inferDPatFuel]
  rw [lookup]
  simp only [alignment.success, childrenRun.success]
  simp [capImages, executablePayload, executableBindings, before.supply_eq,
    event]

end DemandTypingInferenceCompletenessMatcherDPat
end TypePM
