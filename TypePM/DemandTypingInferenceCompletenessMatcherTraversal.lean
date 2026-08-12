import TypePM.DemandTypingInferenceCompletenessExprTraversal
import TypePM.DemandTypingInferenceCompletenessPatternTraversal

/-!
# Checking and matcher traversal composition

This module contains the syntax-directed glue between completed recursive
subruns.  Solver choices remain owned by the alignment-completeness module;
these constructors only compose successful runs in executable source order.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherTraversal

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation

/-- Checking is synthesis followed by the executable expected-type cut. -/
def checkExprFuel_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected raw : Ty} {q q₁ q' : InferenceBase.FreshSupply}
    {S S₁ S' : Subst} {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (synth : SynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression initial)
      q₁ S₁ ledger₁ raw)
    (aligned : StateRunCompletion synth.completion.state
      (alignExprResultAtExpected path synth.result expected)
      q' S' ledger') :
    StateRunCompletion before
      (checkExprFuel (fuel + 1) signature context selfEnv path expression
        expected initial) q' S' ledger' := by
  refine
    { result := aligned.result
      success := ?_
      supply_eq := aligned.supply_eq
      transition := synth.transition.seq aligned.transition
      declarative_bounded := aligned.declarative_bounded
      executable_bounded := aligned.executable_bounded
      forward_bounded := aligned.forward_bounded
      reverse_bounded := aligned.reverse_bounded
      ledger_below := aligned.ledger_below
      executable_ledger_below := aligned.executable_ledger_below
      protected_origins := aligned.protected_origins
      protected_below := aligned.protected_below
      allocated_recorded := aligned.allocated_recorded }
  simp only [checkExprFuel]
  rw (occs := .pos [1]) [synth.success]
  exact aligned.success

def checkExprsFuel_nil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (selfEnv : SelfEnv) (parent : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    StateRunCompletion before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index [] []
        state) q S ledger := by
  refine
    { result := state
      success := by simp [checkExprsFuel]
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
      allocated_recorded := before.allocated_recorded }

def checkExprsFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (head : StateRunCompletion before
      (checkExprFuel fuel signature context selfEnv (index :: parent)
        expression expected state) q₁ S₁ ledger₁)
    (tail : StateRunCompletion head.completion
      (checkExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions expecteds head.result) q' S' ledger') :
    StateRunCompletion before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) (expected :: expecteds) state)
      q' S' ledger' := by
  refine
    { result := tail.result
      success := ?_
      supply_eq := tail.supply_eq
      transition := head.transition.seq tail.transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded }
  simp only [checkExprsFuel]
  rw (occs := .pos [1]) [head.success]
  exact tail.success

/-- Completed arm traversal has no data result beyond its final state. -/
def checkArmsFuel_nil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (selfEnv : SelfEnv) (bindings : MonoCtx) (parent : SyntaxPath)
    (index : Nat) (clauseTarget bodyTarget : Ty)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    StateRunCompletion before
      (checkArmsFuel (fuel + 1) signature context selfEnv bindings parent index
        [] clauseTarget bodyTarget state) q S ledger := by
  refine
    { result := state
      success := by simp [checkArmsFuel]
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
      allocated_recorded := before.allocated_recorded }

def checkArmsFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {ppBindings executablePPBindings : MonoCtx}
    {parent : SyntaxPath} {index : Nat} {dataPattern : DPat} {body : Expr}
    {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {armBindings : MonoCtx} {q q₁ q₂ q' : InferenceBase.FreshSupply}
    {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (ppRelated : MonoCtxBisimulation before.prevailing ppBindings
      executablePPBindings)
    (data : DPatRunCompletion before
      (inferDPatFuel fuel signature (0 :: index :: parent) dataPattern
        executableClauseTarget state) q₁ S₁ ledger₁ clauseTarget
      armBindings)
    (disjoint : ∀ name, name ∈ armBindings.names →
      name ∉ ppBindings.names)
    (bodyRun : StateRunCompletion data.completion
      (checkExprFuel fuel signature
        (data.result.bindings.toContext ++ executablePPBindings.toContext ++
          context)
        (selfEnv.eraseMany
          (executablePPBindings.names ++ data.result.bindings.names))
        (1 :: index :: parent) body executableBodyTarget data.result.state)
      q₂ S₂ ledger₂)
    (tail : StateRunCompletion bodyRun.completion
      (checkArmsFuel fuel signature context selfEnv executablePPBindings parent
        (index + 1) arms executableClauseTarget executableBodyTarget
        bodyRun.result) q' S' ledger') :
    StateRunCompletion before
      (checkArmsFuel (fuel + 1) signature context selfEnv executablePPBindings
        parent index (.mk dataPattern body :: arms) executableClauseTarget
        executableBodyTarget state) q' S' ledger' := by
  have ppAtData :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      data.transition ppRelated
  have checked := namesDisjoint_of_bisimulation data.bindings ppAtData disjoint
  refine
    { result := tail.result
      success := ?_
      supply_eq := tail.supply_eq
      transition := ((data.transition.seq bodyRun.transition).seq
        tail.transition)
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded }
  simp only [checkArmsFuel]
  rw (occs := .pos [1]) [data.success]
  simp only [checked, if_true]
  rw (occs := .pos [1]) [bodyRun.success]
  exact tail.success

/-- Clause output retains the raw primitive-hole list for matcher
finalization. -/
structure ClauseRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClauseResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) : Type where
  result : ClauseResult
  success : operation = some result
  state : TraversalStateCorrespondence q' declarative ledger result.state
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  target : TyBisimulation transition.after target result.target
  holes : DualListBisimulation transition.after holes result.rawHoles

inductive DualListsBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    List (List Dual) → List (List Dual) → Prop where
  | nil : DualListsBisimulation relation [] []
  | cons (head : DualListBisimulation relation declarativeHoles
      executableHoles)
      (tail : DualListsBisimulation relation declarativeLists
        executableLists) :
      DualListsBisimulation relation (declarativeHoles :: declarativeLists)
        (executableHoles :: executableLists)

structure ClausesRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClausesResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holeLists : List (List Dual)) : Type where
  result : ClausesResult
  success : operation = some result
  state : TraversalStateCorrespondence q' declarative ledger result.state
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  target : TyBisimulation transition.after target result.target
  holes : DualListsBisimulation transition.after holeLists
    result.rawHoleLists

end DemandTypingInferenceCompletenessMatcherTraversal
end TypePM
