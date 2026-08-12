import TypePM.DemandTypingInferenceCompletenessTraversal
import TypePM.DemandTypingInferenceCompletenessDataBisimulation

/-!
# Pattern traversal completeness packages

Pattern traversal returns more data than expression synthesis: a dual, a
monomorphic binding context, and, for primitive patterns, a list of holes.
This module packages those outputs under the same DD/executable state
bisimulation used by raw expression completeness.  It also supplies the
solver-independent constructors used by the mutual traversal proof.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternTraversal

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessDataBisimulation

/-! ## Compositional output relations -/

theorem DualListBisimulation.append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : List Dual}
    (leftRelated : DualListBisimulation relation left left')
    (rightRelated : DualListBisimulation relation right right') :
    DualListBisimulation relation (left ++ right) (left' ++ right') := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons head tail induction => exact .cons head induction

theorem MonoCtxBisimulation.append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : MonoCtx}
    (leftRelated : MonoCtxBisimulation relation left left')
    (rightRelated : MonoCtxBisimulation relation right right') :
    MonoCtxBisimulation relation (left ++ right) (left' ++ right') := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons target tail induction => exact .cons target induction

theorem namesDisjoint_of_bisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : MonoCtx}
    (leftRelated : MonoCtxBisimulation relation left left')
    (rightRelated : MonoCtxBisimulation relation right right')
    (disjoint : ∀ name, name ∈ left.names → name ∉ right.names) :
    namesDisjoint left'.names right'.names = true := by
  rw [← leftRelated.names_eq, ← rightRelated.names_eq]
  exact (namesDisjoint_eq_true _ _).mpr disjoint

/-! ## One structural capability allocation -/

def TraversalStateCorrespondence.freshCapExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before.prevailing (DDLedger.markFreshCap ledger q)
      declarative (state.freshCap origin).2 := by
  let q' : InferenceBase.FreshSupply :=
    { q with nextCap := q.nextCap + 1 }
  let afterState := (state.freshCap origin).2
  let afterLedger := DDLedger.markFreshCap ledger q
  have forwardBetween : AdmissiblePostBetween
      afterState.capabilityOrigins afterLedger before.prevailing.forward := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.forwardBetween
      before.forward_bounded before.executable_ledger_below
      (fresh := [⟨q.nextCap⟩]) (fun varId membership => by
        simp only [List.mem_singleton] at membership
        subst varId
        exact Nat.le_refl _)
    simpa [afterState, afterLedger, DDLedger.markFreshCap,
      CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins, InferState.freshCap,
      InferState.recordEvent, before.supply_eq] using extended
  have reverseBetween : AdmissiblePostBetween
      afterLedger afterState.capabilityOrigins before.prevailing.reverse := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.reverseBetween
      before.reverse_bounded before.ledger_below
      (fresh := [⟨q.nextCap⟩]) (fun varId membership => by
        simp only [List.mem_singleton] at membership
        subst varId
        exact Nat.le_refl _)
    simpa [afterState, afterLedger, DDLedger.markFreshCap,
      CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins, InferState.freshCap,
      InferState.recordEvent, before.supply_eq] using extended
  refine
    { after :=
        { forward := before.prevailing.forward
          forwardEquation := before.prevailing.forwardEquation
          declarativeIdempotent := before.prevailing.declarativeIdempotent
          reverse := before.prevailing.reverse
          reverseEquation := by
            change state.prevailing =
              Subst.seq before.prevailing.reverse declarative
            exact before.prevailing.reverseEquation
          ledgerBisimulation := ⟨forwardBetween, reverseBetween⟩
          executableIdempotent := by
            change state.prevailing.Idempotent
            exact before.prevailing.executableIdempotent }
      transportTy := ?_ }
  intro declarativeTarget executableTarget related
  exact ⟨by
      change declarative.apply declarativeTarget =
        before.prevailing.forward.apply
          (state.prevailing.apply executableTarget)
      exact related.forward,
    by
      change state.prevailing.apply executableTarget =
        before.prevailing.reverse.apply
          (declarative.apply declarativeTarget)
      exact related.reverse⟩

def TraversalStateCorrespondence.freshCap
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    TraversalStateCorrespondence
      { q with nextCap := q.nextCap + 1 } declarative
      (DDLedger.markFreshCap ledger q) (state.freshCap origin).2 := by
  let extension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      before origin
  let supplyExtension := SupplyExtends.bumpCap q 1
  refine
    { supply_eq := ?_
      prevailing := extension.after
      declarative_bounded := before.declarative_bounded.mono supplyExtension
      executable_bounded := before.executable_bounded.mono supplyExtension
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := DDLedger.LedgerBelow.markFreshCap before.ledger_below
      executable_ledger_below := ?_
      protected_origins := before.protected_origins.freshCap
        before.protected_below origin
      protected_below := before.protected_below.freshCap origin
      allocated_recorded := before.allocated_recorded.freshCap origin }
  · change { state.supply with nextCap := state.supply.nextCap + 1 } =
      { q with nextCap := q.nextCap + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextCap := supply.nextCap + 1 }) before.supply_eq
  · simpa [InferState.freshCap, InferState.recordEvent,
      DDLedger.markFreshCap, CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins,
      before.supply_eq] using
        DDLedger.LedgerBelow.markFreshCap before.executable_ledger_below

/-! ## Result packages -/

structure PatternRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  result : PatternResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  dual : DualBisimulation transition.after dual result.dual
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PatternsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  result : PatternsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  duals : DualListBisimulation transition.after duals result.duals
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  result : PPatResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target
  holes : DualListBisimulation transition.after holes result.holes
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  result : PPatsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets
  holes : DualListBisimulation transition.after holes result.holes
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure DPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  result : DPatResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure DPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) (bindings : MonoCtx) : Type where
  result : DPatsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

def PatternRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {dual : Dual} {bindings : MonoCtx}
    (run : PatternRunCompletion before operation q' declarative ledger dual
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PatternsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {duals : List Dual} {bindings : MonoCtx}
    (run : PatternsRunCompletion before operation q' declarative ledger duals
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PPatRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PPatResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {holes : List Dual} {bindings : MonoCtx}
    (run : PPatRunCompletion before operation q' declarative ledger target
      holes bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PPatsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PPatsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty} {holes : List Dual} {bindings : MonoCtx}
    (run : PPatsRunCompletion before operation q' declarative ledger targets
      holes bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def DPatRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option DPatResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {bindings : MonoCtx}
    (run : DPatRunCompletion before operation q' declarative ledger target
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def DPatsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option DPatsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty} {bindings : MonoCtx}
    (run : DPatsRunCompletion before operation q' declarative ledger targets
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

/-! ## Trace-only suffixes -/

def TraversalStateCorrespondence.visitThenRecord
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (event : TraceEvent)
    (eventRecorded : ∀ varId, varId ∈ event.allocatedCapVars →
      varId ∈ state.capabilityOrigins.map Prod.fst) :
    TraversalStateCorrespondence q declarative ledger
      ((visit state kind path).recordEvent event) := by
  let entered := before.visit kind path
  exact entered.recordEvent event (by
    intro varId membership
    simpa [visit, InferState.recordEvent] using eventRecorded varId membership)

def TraversalStateCorrespondence.visitThenRecordExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (event : TraceEvent) :
    BisimulationExtension before.prevailing ledger declarative
      ((visit state kind path).recordEvent event) :=
  (before.visitExtension kind path).seq
    ((before.visit kind path).prevailing.recordEventExtension event)

/-! ## Primitive leaf completions -/

def dpatVar_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.var name) target state)
      q S ledger target [(name, target)] := by
  let event := TraceEvent.inferredDPat (.var name) target [(name, target)] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .dpatVar path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .dpatVar path event
  refine
    { result := ⟨target, [(name, target)],
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
      target := transition.after.sameTarget target
      bindings := .cons (transition.after.sameTarget target) .nil }

def dpatWild_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path .wild target state)
      q S ledger target [] := by
  let event := TraceEvent.inferredDPat .wild target [] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .dpatWild path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .dpatWild path event
  refine
    { result := ⟨target, [], (visit state .dpatWild path).recordEvent event⟩
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
      target := transition.after.sameTarget target
      bindings := .nil }

def ppatWild_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .wild target state)
      q S ledger target [] [] := by
  let event := TraceEvent.inferredPPat .wild target [] [] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .ppatWild path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .ppatWild path event
  refine
    { result := ⟨target, [], [],
        (visit state .ppatWild path).recordEvent event⟩
      success := by simp [inferPPatFuel, event]
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
      target := transition.after.sameTarget target
      holes := .nil
      bindings := .nil }

def ppatValue_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.pval name) target state)
      q S ledger target [] [(name, target)] := by
  let event := TraceEvent.inferredPPat (.pval name) target []
    [(name, target)] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .ppatValue path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .ppatValue path event
  refine
    { result := ⟨target, [], [(name, target)],
        (visit state .ppatValue path).recordEvent event⟩
      success := by simp [inferPPatFuel, event]
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
      target := transition.after.sameTarget target
      holes := .nil
      bindings := .cons (transition.after.sameTarget target) .nil }

def ppatHole_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .hole target state)
      { q with nextCap := q.nextCap + 1 } S
      (DDLedger.markFreshCap ledger q) target
      [⟨.var ⟨q.nextCap⟩, target⟩] [] := by
  let origin := freshOrigin .primitivePattern path "primitive-hole"
  let fresh := state.freshCap origin
  have capabilityEq : fresh.1 = .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  let holes := [Dual.mk fresh.1 target]
  let event := TraceEvent.inferredPPat .hole target holes [] path
  let allocated :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCap
      before origin
  let final :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord
      allocated .ppatHole path event (by
        intro _ membership
        simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition :=
    (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      before origin).seq
      (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
        allocated .ppatHole path event)
  refine
    { result := ⟨target, holes, [],
        (visit fresh.2 .ppatHole path).recordEvent event⟩
      success := by simp [inferPPatFuel, origin, fresh, holes, event]
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
      target := transition.after.sameTarget target
      holes := by
        change DualListBisimulation transition.after
          [⟨.var ⟨q.nextCap⟩, target⟩] holes
        have holesEq : holes = [⟨.var ⟨q.nextCap⟩, target⟩] := by
          simp [holes, capabilityEq]
        rw [holesEq]
        exact .cons (DualBisimulation.same transition.after
          ⟨.var ⟨q.nextCap⟩, target⟩) .nil
      bindings := .nil }

/-! ## Empty and cons list packaging -/

def patternsNil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (path : SyntaxPath)
    (index : Nat) {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings) :
    PatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path index [] state)
      q S ledger [] declarativeBindings := by
  refine
    { result := ⟨[], executableBindings, state⟩
      success := by simp [inferPatternsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      duals := .nil
      bindings := bindings }

def ppatsNil_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    PPatsRunCompletion before
      (inferPPatsFuel (fuel + 1) signature path index [] [] state)
      q S ledger [] [] [] := by
  refine
    { result := ⟨[], [], [], state⟩
      success := by simp [inferPPatsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      targets := .nil
      holes := .nil
      bindings := .nil }

def dpatsNil_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    DPatsRunCompletion before
      (inferDPatsFuel (fuel + 1) signature path index [] [] state)
      q S ledger [] [] := by
  refine
    { result := ⟨[], [], state⟩
      success := by simp [inferDPatsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      targets := .nil
      bindings := .nil }

def patternsCons_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (parent : SyntaxPath)
    (index : Nat) (pattern : Pattern) (patterns : List Pattern)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {dual : Dual} {duals : List Dual}
    {bindings₁ bindings' : MonoCtx}
    (head : PatternRunCompletion before
      (inferPatternFuel fuel signature context parameters
        executableBindings selfEnv (index :: parent) pattern state)
      q₁ S₁ ledger₁ dual bindings₁)
    (tail : PatternsRunCompletion head.completion
      (inferPatternsFuel fuel signature context parameters
        head.result.bindings selfEnv parent (index + 1) patterns
        head.result.state)
      q' S' ledger' duals bindings') :
    PatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv parent index (pattern :: patterns) state)
      q' S' ledger' (dual :: duals) bindings' := by
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.dual :: tail.result.duals,
        tail.result.bindings, tail.result.state⟩
      success := by simp [inferPatternsFuel, head.success, tail.success]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      duals := .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          tail.transition head.dual) tail.duals
      bindings := tail.bindings }

def ppatsCons_complete
    (fuel : Nat) (signature : FrozenSig) (parent : SyntaxPath) (index : Nat)
    (pattern : PPat) (patterns : List PPat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {target : Ty} {targets : List Ty} {holes restHoles : List Dual}
    {bindings restBindings : MonoCtx}
    (head : PPatRunCompletion before
      (inferPPatFuel fuel signature (index :: parent) pattern
        executableTarget state)
      q₁ S₁ ledger₁ target holes bindings)
    (tail : PPatsRunCompletion head.completion
      (inferPPatsFuel fuel signature parent (index + 1) patterns
        executableTargets head.result.state)
      q' S' ledger' targets restHoles restBindings)
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names) :
    PPatsRunCompletion before
      (inferPPatsFuel (fuel + 1) signature parent index
        (pattern :: patterns) (executableTarget :: executableTargets) state)
      q' S' ledger' (target :: targets) (holes ++ restHoles)
      (bindings ++ restBindings) := by
  let transportedBindings :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      tail.transition head.bindings
  have checked := namesDisjoint_of_bisimulation transportedBindings
    tail.bindings disjoint
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.target :: tail.result.targets,
        head.result.holes ++ tail.result.holes,
        head.result.bindings ++ tail.result.bindings, tail.result.state⟩
      success := by
        simp [inferPPatsFuel, head.success, tail.success, checked]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      targets := .cons (tail.transition.transportTy head.target) tail.targets
      holes :=
        DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.append
          (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
            tail.transition head.holes) tail.holes
      bindings := DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.append transportedBindings
        tail.bindings }

def dpatsCons_complete
    (fuel : Nat) (signature : FrozenSig) (parent : SyntaxPath) (index : Nat)
    (pattern : DPat) (patterns : List DPat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {target : Ty} {targets : List Ty}
    {bindings restBindings : MonoCtx}
    (head : DPatRunCompletion before
      (inferDPatFuel fuel signature (index :: parent) pattern
        executableTarget state)
      q₁ S₁ ledger₁ target bindings)
    (tail : DPatsRunCompletion head.completion
      (inferDPatsFuel fuel signature parent (index + 1) patterns
        executableTargets head.result.state)
      q' S' ledger' targets restBindings)
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names) :
    DPatsRunCompletion before
      (inferDPatsFuel (fuel + 1) signature parent index
        (pattern :: patterns) (executableTarget :: executableTargets) state)
      q' S' ledger' (target :: targets) (bindings ++ restBindings) := by
  let transportedBindings :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      tail.transition head.bindings
  have checked := namesDisjoint_of_bisimulation transportedBindings
    tail.bindings disjoint
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.target :: tail.result.targets,
        head.result.bindings ++ tail.result.bindings, tail.result.state⟩
      success := by
        simp [inferDPatsFuel, head.success, tail.success, checked]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      targets := .cons (tail.transition.transportTy head.target) tail.targets
      bindings := DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.append transportedBindings
        tail.bindings }

end DemandTypingInferenceCompletenessPatternTraversal
end TypePM
