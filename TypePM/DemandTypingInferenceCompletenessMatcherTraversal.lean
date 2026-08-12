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
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessProtectedTrace
open DemandTypingInferenceCompletenessProtectedTrace

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
      allocated_recorded := aligned.allocated_recorded
      protected_safe := aligned.protected_safe }
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
      allocated_recorded := before.allocated_recorded
      protected_safe := before.protected_safe }

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
      allocated_recorded := tail.allocated_recorded
      protected_safe := tail.protected_safe }
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
      allocated_recorded := before.allocated_recorded
      protected_safe := before.protected_safe }

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
      allocated_recorded := tail.allocated_recorded
      protected_safe := tail.protected_safe }
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
  protected_safe : CurrentProtectedProducerSafe result.state
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

/-- Pointwise dual correspondence preserves the number of primitive holes.
This is the bridge needed by `decomposeME`, whose arity argument is computed
from the executable primitive-pattern result. -/
theorem DualListBisimulation.length_eq
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeHoles executableHoles : List Dual}
    (related : DualListBisimulation relation declarativeHoles executableHoles) :
    declarativeHoles.length = executableHoles.length := by
  induction related with
  | nil => rfl
  | cons _ _ induction => exact congrArg Nat.succ induction

/-- A chronological state extension transports every clause's primitive-hole
list through the same residual pair. -/
theorem BisimulationExtension.transportDualLists
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeLists executableLists : List (List Dual)}
    (related : DualListsBisimulation before declarativeLists executableLists) :
    DualListsBisimulation extension.after declarativeLists executableLists := by
  induction related with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          extension head)
        induction

structure ClausesRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClausesResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holeLists : List (List Dual)) : Type where
  result : ClausesResult
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
  protected_safe : CurrentProtectedProducerSafe result.state
  target : TyBisimulation transition.after target result.target
  holes : DualListsBisimulation transition.after holeLists
    result.rawHoleLists

def ClauseRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ClauseResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {holes : List Dual}
    (run : ClauseRunCompletion before operation q' declarative ledger target
      holes) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded, run.protected_safe⟩

def ClausesRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ClausesResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {holeLists : List (List Dual)}
    (run : ClausesRunCompletion before operation q' declarative ledger target
      holeLists) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded, run.protected_safe⟩

/-! ## Clause traversal composition -/

/-- Compose primitive-pattern inference, next-matcher checking, and arm
checking in the executable order of one clause.  All solver choices are
contained in the three supplied completed subruns. -/
def inferClauseFuel_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {primitivePattern : PPat}
    {next : Expr} {arms : List Arm}
    {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {nextMatchers : List Expr}
    {q q₁ q₂ q' : InferenceBase.FreshSupply}
    {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (primitive : PPatRunCompletion (before.visit .clause path)
      (inferPPatFuel fuel signature (0 :: path) primitivePattern
        executableTarget (visit state .clause path))
      q₁ S₁ ledger₁ declarativeTarget holes bindings)
    (decomposed : decomposeME next holes.length = some nextMatchers)
    (nextRun : StateRunCompletion primitive.completion
      (checkExprsFuel fuel signature context selfEnv (1 :: path) 0
        nextMatchers
        (primitive.result.holes.map fun hole => .slot hole.cap hole.target)
        primitive.result.state)
      q₂ S₂ ledger₂)
    (armsRun : StateRunCompletion nextRun.completion
      (checkArmsFuel fuel signature context selfEnv primitive.result.bindings
        (2 :: path) 0 arms executableTarget
        (Ty.listT (prodTy (primitive.result.holes.map Dual.target)))
        nextRun.result)
      q' S' ledger') :
    ClauseRunCompletion before
      (inferClauseFuel (fuel + 1) signature context selfEnv path
        (.mk primitivePattern next arms) executableTarget state)
      q' S' ledger' declarativeTarget holes := by
  have holeLength :=
    DemandTypingInferenceCompletenessMatcherTraversal.DualListBisimulation.length_eq
      primitive.holes
  have executableDecomposed :
      decomposeME next primitive.result.holes.length = some nextMatchers := by
    rw [← holeLength]
    exact decomposed
  let visitTransition := before.visitExtension .clause path
  let transition :=
    ((visitTransition.seq primitive.transition).seq nextRun.transition).seq
      armsRun.transition
  refine
    { result := ⟨executableTarget, primitive.result.holes, armsRun.result⟩
      success := ?_
      supply_eq := armsRun.supply_eq
      transition := transition
      declarative_bounded := armsRun.declarative_bounded
      executable_bounded := armsRun.executable_bounded
      forward_bounded := armsRun.forward_bounded
      reverse_bounded := armsRun.reverse_bounded
      ledger_below := armsRun.ledger_below
      executable_ledger_below := armsRun.executable_ledger_below
      protected_origins := armsRun.protected_origins
      protected_below := armsRun.protected_below
      allocated_recorded := armsRun.allocated_recorded
      protected_safe := armsRun.protected_safe
      target := transition.transportTy targetRelated
      holes :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          (nextRun.transition.seq armsRun.transition) primitive.holes }
  simp only [inferClauseFuel]
  simp [primitive.success, executableDecomposed, nextRun.success,
    armsRun.success]

/-- Empty clause traversal preserves the shared matcher target. -/
def inferClausesFuel_nil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (selfEnv : SelfEnv) (parent : SyntaxPath) (index : Nat)
    {declarativeTarget executableTarget : Ty}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget) :
    ClausesRunCompletion before
      (inferClausesFuel (fuel + 1) signature context selfEnv parent index []
        executableTarget state)
      q S ledger declarativeTarget [] := by
  refine
    { result := ⟨executableTarget, [], state⟩
      success := by simp [inferClausesFuel]
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
      protected_safe := before.protected_safe
      target := targetRelated
      holes := .nil }

/-- Compose the completed head clause with the completed suffix traversal. -/
def inferClausesFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {clause : Clause} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {holeLists : List (List Dual)}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (head : ClauseRunCompletion before
      (inferClauseFuel fuel signature context selfEnv (index :: parent)
        clause executableTarget state)
      q₁ S₁ ledger₁ declarativeTarget holes)
    (tail : ClausesRunCompletion head.completion
      (inferClausesFuel fuel signature context selfEnv parent (index + 1)
        clauses executableTarget head.result.state)
      q' S' ledger' declarativeTarget holeLists) :
    ClausesRunCompletion before
      (inferClausesFuel (fuel + 1) signature context selfEnv parent index
        (clause :: clauses) executableTarget state)
      q' S' ledger' declarativeTarget (holes :: holeLists) := by
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨executableTarget,
        head.result.rawHoles :: tail.result.rawHoleLists, tail.result.state⟩
      success := ?_
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
      protected_safe := tail.protected_safe
      target := transition.transportTy targetRelated
      holes := .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          tail.transition head.holes)
        tail.holes }
  simp only [inferClausesFuel]
  simp [head.success, tail.success]

end DemandTypingInferenceCompletenessMatcherTraversal
end TypePM
