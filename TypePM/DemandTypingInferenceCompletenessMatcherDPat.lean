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

noncomputable def dpatTuple_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    (patterns : List DPat)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeTarget executableTarget : Ty}
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (declarativeBounded : declarativeTarget.BoundedBy q)
    (executableBounded : executableTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) declarativeTarget S₁)
    {q' : InferenceBase.FreshSupply} {bindings : MonoCtx}
    (children :
      let fresh := freshTargets_complete before
        (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
      ∀ alignment : StateRunCompletion fresh.state
          (alignTypes (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).2
            (freshOrigin .dataPattern path "dp-tuple-result")
            (.prod (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1)
            executableTarget)
          (freshTargetsSupply patterns.length q).2 S₁ ledger,
        DPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1 alignment.result)
          q' S' ledger₂ (freshTargetsSupply patterns.length q).1 bindings) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.tuple patterns)
        executableTarget state)
      q' S' ledger₂ declarativeTarget bindings := by
  let fieldOrigin := freshOrigin .dataPattern path "dp-tuple-field"
  let resultOrigin := freshOrigin .dataPattern path "dp-tuple-result"
  let fresh := freshTargets_complete before fieldOrigin patterns.length
  let supplyExtension := SupplyExtends.freshTargets patterns.length q
  have declarativeProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargetsSupply patterns.length q).1) :=
    Ty.BoundedBy.prodOfForall
      (freshTargetsSupply_boundedBy patterns.length q)
  have executableProductRelated : TyBisimulation fresh.state.prevailing
      (.prod (freshTargetsSupply patterns.length q).1)
      (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact fresh.state.prevailing.sameTarget _
  have executableProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact declarativeProductBounded
  have targetAtFresh : TyBisimulation fresh.state.prevailing
      declarativeTarget executableTarget := by
    rw [fresh.prevailing_eq]
    exact fresh.transition.transportTy targetRelated
  let alignment := ddAlignTypesWithLedger_complete
    (origin := resultOrigin) fresh.state executableProductRelated
    targetAtFresh
    declarativeProductBounded (declarativeBounded.mono supplyExtension)
    executableProductBounded (executableBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let executableBindings := childrenRun.result.bindings
  let event := TraceEvent.inferredDPat (.tuple patterns) executableTarget
    executableBindings path
  let visited := childrenRun.completion.visit .dpatTuple path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let finishExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      childrenRun.completion .dpatTuple path event
  let transition := ((fresh.extension.seq alignment.transition).seq
    childrenRun.transition).seq finishExtension
  refine
    { result := ⟨executableTarget, executableBindings,
        (visit childrenRun.result.state .dpatTuple path).recordEvent event⟩
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
  have alignmentSuccess := alignment.success
  dsimp [fieldOrigin, resultOrigin] at alignmentSuccess
  simp only [alignmentSuccess, childrenRun.success]
  rfl

theorem StateBisimulation.sameTargets
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    (relation : StateBisimulation ledger S state) : ∀ targets,
    TyListBisimulation relation targets targets
  | [] => .nil
  | target :: targets => .cons (relation.sameTarget target)
      (StateBisimulation.sameTargets relation targets)

theorem StateBisimulation.sameTargetsOfEq
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    (relation : StateBisimulation ledger S state) {left right : List Ty}
    (equal : left = right) : TyListBisimulation relation left right := by
  subst right
  exact StateBisimulation.sameTargets relation left

structure BoundedDPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatsResult) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger' : CapabilityOriginLedger)
    (targets : List Ty) (bindings : MonoCtx) : Type where
  run : DPatsRunCompletion before operation q' S' ledger' targets bindings
  rawTargetsBounded : ∀ target ∈ run.result.targets, target.BoundedBy q'
  rawBindingsBounded : run.result.bindings.BoundedBy q'

noncomputable def dpatCtor_complete_related_bounded
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
    (targetFinalBounded : executableTarget.BoundedBy q')
    (children :
      let instantiation := instantiateCtorInState_complete before scheme
      ∀ alignment : StateRunCompletion instantiation.correspondence
          (alignTypes (instantiateCtorInState state scheme).2
            (freshOrigin .dataPattern path "dp-constructor-result")
            (instantiateCtorInState state scheme).1.2 executableTarget)
          (InferenceBase.instantiateCtorScheme q scheme).supply S₁
          (DDLedger.markCtorInstance ledger q scheme),
        BoundedDPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (instantiateCtorInState state scheme).1.1 alignment.result)
          q' S' ledger₂
          (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings) :
    BoundedDPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.ctor name patterns)
        executableTarget state)
      q' S' (DDLedger.freezeExport ledger₂ S'
        (freshCapImages q scheme.capBinders)
        (capabilityExportPayload []
          (declarativeTarget :: bindings.map fun entry => entry.2)))
      declarativeTarget bindings := by
  let raw := dpatCtor_complete_related fuel signature path name patterns lookup
    closed before targetRelated declarativeBounded executableBounded aligned
    (children := fun alignment => (children alignment).run)
  let instantiation := instantiateCtorInState_complete before scheme
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.dataCtors lookup).boundedBy)
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .dataPattern path "dp-constructor-result")
    instantiation.correspondence instantiation.target
    (instantiation.transition.transportTy targetRelated)
    instBounded.2
    (declarativeBounded.mono (SupplyExtends.instantiateCtorScheme q scheme))
    (by simpa [Inference.instantiateCtorInState, before.supply_eq] using
      instBounded.2)
    (executableBounded.mono (SupplyExtends.instantiateCtorScheme q scheme))
    aligned
  exact ⟨raw, targetFinalBounded, (children alignment).rawBindingsBounded⟩

noncomputable def dpatTuple_complete_related_bounded
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    (patterns : List DPat)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeTarget executableTarget : Ty}
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (declarativeBounded : declarativeTarget.BoundedBy q)
    (executableBounded : executableTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) declarativeTarget S₁)
    {q' : InferenceBase.FreshSupply} {bindings : MonoCtx}
    (targetFinalBounded : executableTarget.BoundedBy q')
    (children :
      let fresh := freshTargets_complete before
        (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
      ∀ alignment : StateRunCompletion fresh.state
          (alignTypes (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).2
            (freshOrigin .dataPattern path "dp-tuple-result")
            (.prod (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1)
            executableTarget)
          (freshTargetsSupply patterns.length q).2 S₁ ledger,
        BoundedDPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1 alignment.result)
          q' S' ledger₂ (freshTargetsSupply patterns.length q).1 bindings) :
    BoundedDPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.tuple patterns)
        executableTarget state)
      q' S' ledger₂ declarativeTarget bindings := by
  let raw := dpatTuple_complete_related fuel signature path patterns before
    targetRelated declarativeBounded executableBounded aligned
    (children := fun alignment => (children alignment).run)
  let fresh := freshTargets_complete before
    (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
  let targetsBounded := freshTargetsSupply_boundedBy patterns.length q
  have productRelated : TyBisimulation fresh.state.prevailing
      (.prod (freshTargetsSupply patterns.length q).1)
      (.prod (freshTargets state
        (freshOrigin .dataPattern path "dp-tuple-field") patterns.length).1) := by
    rw [fresh.targets_eq]
    exact fresh.state.prevailing.sameTarget _
  have productBounded : Ty.BoundedBy
      (freshTargetsSupply patterns.length q).2
      (.prod (freshTargets state
        (freshOrigin .dataPattern path "dp-tuple-field") patterns.length).1) := by
    rw [fresh.targets_eq]
    exact Ty.BoundedBy.prodOfForall targetsBounded
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .dataPattern path "dp-tuple-result") fresh.state
    productRelated
    (by rw [fresh.prevailing_eq]; exact fresh.transition.transportTy targetRelated)
    (Ty.BoundedBy.prodOfForall targetsBounded)
    (declarativeBounded.mono (SupplyExtends.freshTargets patterns.length q))
    productBounded
    (executableBounded.mono (SupplyExtends.freshTargets patterns.length q))
    aligned
  exact ⟨raw, targetFinalBounded, (children alignment).rawBindingsBounded⟩

mutual

theorem dpatOrigin_complete_related_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : DPat}
    {declarativeTarget executableTarget : Ty} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPat signature q S pattern declarativeTarget bindings q' S'}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (declarativeBounded : declarativeTarget.BoundedBy q)
    (executableBounded : executableTarget.BoundedBy q)
    (adequate : DPatAdequate fuel pattern) :
    Nonempty (BoundedDPatRunCompletion before
      (inferDPatFuel fuel signature path pattern executableTarget state)
      q' S' ledger' declarativeTarget bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | var =>
      rename_i name
      let run := dpatVar_complete_related fuel signature path name before
        targetRelated
      exact ⟨⟨run, executableBounded,
        fun entry membership => by
          change entry ∈ [(name, executableTarget)] at membership
          simp only [List.mem_singleton] at membership
          subst entry
          exact executableBounded⟩⟩
  | wild =>
      let run := dpatWild_complete_related fuel signature path before
        targetRelated
      exact ⟨⟨run, executableBounded,
        fun _ membership => by
          change _ ∈ ([] : MonoCtx) at membership
          contradiction⟩⟩
  | @ctor q S name patterns expectedTarget scheme S₁ bindings q' S'
      ledger ledger₂ lookup aligned childrenRaw childrenOrigin =>
      have childAdequate := dpat_ctor (fuel := fuel) adequate
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      let run := dpatCtor_complete_related_bounded fuel signature path name patterns
        lookup closed before targetRelated declarativeBounded executableBounded
        aligned (executableBounded.mono
          ((SupplyExtends.instantiateCtorScheme q scheme).trans
            childrenOrigin.erase.supplyExtends))
        (children := by
          dsimp
          intro alignedRun
          have targetsEq :
              (InferenceBase.instantiateCtorScheme state.supply scheme).value.1 =
                (InferenceBase.instantiateCtorScheme q scheme).value.1 := by
            rw [before.supply_eq]
          have targetsRelated : TyListBisimulation
              alignedRun.completion.prevailing
              (InferenceBase.instantiateCtorScheme q scheme).value.1
              (InferenceBase.instantiateCtorScheme state.supply scheme).value.1 := by
            exact StateBisimulation.sameTargetsOfEq
              alignedRun.completion.prevailing targetsEq.symm
          exact Classical.choice
            (dpatsOrigin_complete_related_nonempty (parent := path) (index := 0)
              closed fuel alignedRun.completion childrenOrigin targetsRelated
              instBounded.1 (fun item membership => by
                rw [targetsEq] at membership
                exact instBounded.1 item membership) childAdequate))
      exact ⟨run⟩
  | @tuple q S patterns expectedTarget S₁ bindings q' S' ledger ledger'
      aligned childrenRaw childrenOrigin =>
      have childAdequate := dpat_tuple (fuel := fuel) adequate
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      let run := dpatTuple_complete_related_bounded fuel signature path patterns before
        targetRelated declarativeBounded executableBounded aligned
        (executableBounded.mono
          ((SupplyExtends.freshTargets patterns.length q).trans
            childrenOrigin.erase.supplyExtends))
        (children := by
          dsimp
          intro alignedRun
          let fresh := freshTargets_complete before
            (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
          have targetsRelated : TyListBisimulation
              alignedRun.completion.prevailing
              (freshTargetsSupply patterns.length q).1
              (freshTargets state
                (freshOrigin .dataPattern path "dp-tuple-field")
                patterns.length).1 := by
            exact StateBisimulation.sameTargetsOfEq
              alignedRun.completion.prevailing fresh.targets_eq.symm
          exact Classical.choice
            (dpatsOrigin_complete_related_nonempty (parent := path) (index := 0)
              closed fuel alignedRun.completion childrenOrigin targetsRelated
              targetsBounded (fun item membership => by
                rw [fresh.targets_eq] at membership
                exact targetsBounded item membership) childAdequate))
      exact ⟨run⟩
termination_by fuel

theorem dpatsOrigin_complete_related_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat} {patterns : List DPat}
    {declarativeTargets executableTargets : List Ty} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPats signature q S patterns declarativeTargets bindings q' S'}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (targetsRelated : TyListBisimulation before.prevailing declarativeTargets
      executableTargets)
    (declarativeBounded : ∀ target ∈ declarativeTargets, target.BoundedBy q)
    (executableBounded : ∀ target ∈ executableTargets, target.BoundedBy q)
    (adequate : DPatListAdequate fuel patterns) :
    Nonempty (BoundedDPatsRunCompletion before
      (inferDPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' declarativeTargets bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | nil =>
      cases targetsRelated
      refine ⟨{
        run := dpatsNil_complete fuel signature parent index before
        rawTargetsBounded := ?_
        rawBindingsBounded := ?_ }⟩
      · intro _ membership
        change _ ∈ ([] : List Ty) at membership
        contradiction
      · intro _ membership
        change _ ∈ ([] : MonoCtx) at membership
        contradiction
  | @cons q S pattern patterns target targets headBindings tailBindings q₁ S₁
      q' S' ledger ledger₁ ledger' headRaw tailRaw headOrigin tailOrigin
      disjoint =>
      cases targetsRelated with
      | cons headRelated tailRelated =>
          rename_i executableTarget executableTail
          have childAdequate := dpatList_cons (fuel := fuel) adequate
          let headRun := Classical.choice
            (dpatOrigin_complete_related_nonempty
              (path := index :: parent) closed fuel before headOrigin
              headRelated (declarativeBounded target (by simp))
              (executableBounded executableTarget (by simp)) childAdequate.1)
          have tailDeclarativeBounded : ∀ item ∈ targets,
              item.BoundedBy q₁ := by
            intro item membership
            exact (declarativeBounded item (by simp [membership])).mono
              headOrigin.erase.supplyExtends
          have tailExecutableBounded : ∀ item ∈ executableTail,
              item.BoundedBy q₁ := by
            intro item membership
            exact (executableBounded item (by simp [membership])).mono
              headOrigin.erase.supplyExtends
          let tailRun := Classical.choice
            (dpatsOrigin_complete_related_nonempty (parent := parent)
              (index := index + 1) closed fuel headRun.run.completion tailOrigin
              (headRun.run.transition.transportTyList tailRelated)
              tailDeclarativeBounded tailExecutableBounded childAdequate.2)
          let run := dpatsCons_complete fuel signature parent index pattern
            patterns before headRun.run tailRun.run disjoint
          exact ⟨⟨run,
            fun item membership => by
              change item ∈ headRun.run.result.target ::
                tailRun.run.result.targets at membership
              simp only [List.mem_cons] at membership
              rcases membership with rfl | membership
              · exact headRun.rawTargetBounded.mono
                  tailOrigin.erase.supplyExtends
              · exact tailRun.rawTargetsBounded item membership,
            by
              apply MonoCtx.BoundedBy.append
              · exact headRun.rawBindingsBounded.mono
                  tailOrigin.erase.supplyExtends
              · exact tailRun.rawBindingsBounded⟩⟩
termination_by fuel

end

/-- The generalized data-pattern reconstruction closes the callback consumed by
matcher-arm completeness.  In particular, the executable target need only be
bisimilar to the target recorded by the DD derivation. -/
theorem matcherDPatCompletenessMotive
    {signature : FrozenSig} (closed : signature.SchemesClosed) :
    MatcherDPatCompletenessMotive signature := by
  intro fuel path pattern target executableTarget bindings q q' S S' ledger
    ledger' state raw origin before targetRelated declarativeBounded
    executableBounded adequate
  exact dpatOrigin_complete_related_nonempty closed fuel before origin
    targetRelated declarativeBounded executableBounded adequate

end DemandTypingInferenceCompletenessMatcherDPat
end TypePM
