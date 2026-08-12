import TypePM.DemandTypingInferenceCompletenessMatcherTraversal
import TypePM.DemandTypingInferenceCompletenessFuel
import TypePM.DemandTypingTerminalAuditTree

/-!
# Matcher-family completeness dispatch

The global expression recursion and matcher-clause recursion are mutually
dependent.  This module keeps the matcher side acyclic by accepting the
expression-checking component as a traversal-stable motive.  The final public
completeness theorem discharges that motive; it is not a premise of the public
API.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherMain

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherTraversal

/-! ## Weighted expression-checking boundary -/

/-- The extra unit is the administrative `checkExprFuel` layer in front of
expression synthesis. -/
abbrev MatcherCheckBudgetAdequate (fuel : Nat) (expression : Expr) : Prop :=
  8 * (exprTraversalFuel expression + 1) + 1 ≤ fuel

/-- Expression-list budget used by `checkExprsFuel`. -/
abbrev MatcherChecksBudgetAdequate
    (fuel : Nat) (expressions : List Expr) : Prop :=
  8 * (exprListTraversalFuel expressions + 1) ≤ fuel

/-- Traversal-stable, terminal-audited checking component at one fixed fuel.
Declarative and executable contexts may differ after pattern binding, but are
related by the current state bisimulation. -/
abbrev MatcherCheckCompletenessAt
    (terminal : Subst) (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {declarativeExpected executableExpected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDCheck signature q S declarativeContext expression
      declarativeExpected q' S'}
    {origin : DDCheckOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext executableContext →
    TyBisimulation before.prevailing declarativeExpected executableExpected →
    declarativeContext.BoundedBy q → executableContext.BoundedBy q →
    declarativeExpected.BoundedBy q →
    executableExpected.BoundedBy q →
    DDCheckTerminalAudit terminal signature origin →
    MatcherCheckBudgetAdequate fuel expression →
    Nonempty (StateRunCompletion before
      (checkExprFuel fuel signature executableContext selfEnv path expression
        executableExpected state) q' S' ledger')

/-- Unrestricted checking motive used by closed global recursions. -/
abbrev MatcherCheckCompletenessMotive
    (terminal : Subst) (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat}, MatcherCheckCompletenessAt terminal signature fuel

/-- Strict fuel ceiling used while the global expression recursion is still
being defined.  Matcher children may use every checking call strictly below
their enclosing expression fuel, but cannot recurse at that outer fuel. -/
abbrev MatcherCheckCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound →
    MatcherCheckCompletenessAt terminal signature fuel

theorem MatcherCheckCompletenessBelow.lower
    {terminal : Subst} {signature : FrozenSig} {bound : Nat}
    (below : MatcherCheckCompletenessBelow terminal signature (bound + 1)) :
    MatcherCheckCompletenessBelow terminal signature bound := by
  intro fuel fuelLt
  exact below (Nat.lt_trans fuelLt (Nat.lt_succ_self bound))

/-- Reconstruct an audited left-to-right checking list from the single
expression checking motive.  Each tail is run at the concrete state returned
by its head. -/
theorem checksOrigin_complete_nonempty_from_below
    {terminal : Subst} {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : MatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ declarativeExpecteds,
      expected.BoundedBy q)
    (executableExpectedsBounded : ∀ expected ∈ executableExpecteds,
      expected.BoundedBy q)
    (expectedsRelated : TyListBisimulation before.prevailing
      declarativeExpecteds executableExpecteds)
    {raw : DDChecks signature q S context expressions declarativeExpecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (StateRunCompletion before
      (checkExprsFuel fuel signature context selfEnv parent index expressions
        executableExpecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          cases expectedsRelated
          exact ⟨checkExprsFuel_nil_complete fuel signature context selfEnv
            parent index before⟩
      | cons headAudit tailAudit =>
              rename_i expression expected q₁ S₁ ledger₁ expressions
                expecteds headRaw tailRaw headOrigin tailOrigin
              cases expectedsRelated with
              | cons expectedRelated tailRelated =>
              rename_i executableExpected executableExpecteds
              have headAdequate :
                  MatcherCheckBudgetAdequate fuel expression := by
                simp only [MatcherChecksBudgetAdequate,
                  MatcherCheckBudgetAdequate, exprListTraversalFuel]
                  at adequate ⊢
                omega
              have tailAdequate :
                  MatcherChecksBudgetAdequate fuel expressions := by
                simp only [MatcherChecksBudgetAdequate,
                  exprListTraversalFuel] at adequate ⊢
                omega
              have expectedBounded := expectedsBounded expected (by simp)
              have executableExpectedBounded :=
                executableExpectedsBounded executableExpected (by simp)
              let headRun := Classical.choice
                (checkBelow (Nat.lt_succ_self fuel)
                  (selfEnv := selfEnv) (path := index :: parent)
                  before
                  (ContextBisimulation.same before.prevailing context)
                  expectedRelated contextBounded contextBounded expectedBounded
                  executableExpectedBounded headAudit headAdequate)
              have tailContextBounded : context.BoundedBy q₁ :=
                contextBounded.mono headOrigin.erase.supplyExtends
              have tailExpectedsBounded :
                  ∀ item ∈ expecteds, item.BoundedBy q₁ := by
                intro item membership
                exact (expectedsBounded item (by simp [membership])).mono
                  headOrigin.erase.supplyExtends
              have tailExecutableExpectedsBounded :
                  ∀ item ∈ executableExpecteds, item.BoundedBy q₁ := by
                intro item membership
                exact (executableExpectedsBounded item (by simp [membership])).mono
                  headOrigin.erase.supplyExtends
              let tailRun := Classical.choice
                (checksOrigin_complete_nonempty_from_below
                  (selfEnv := selfEnv) (parent := parent)
                  (index := index + 1) fuel checkBelow.lower
                  headRun.completion
                  tailContextBounded tailExpectedsBounded
                  tailExecutableExpectedsBounded
                  (headRun.transition.transportTyList tailRelated) tailAudit
                  tailAdequate)
              exact ⟨checkExprsFuel_cons_complete before headRun tailRun⟩
termination_by fuel

/-- Unrestricted wrapper retained for completed global motives. -/
theorem checksOrigin_complete_nonempty_from_check
    {terminal : Subst} {signature : FrozenSig}
    (checkComplete : MatcherCheckCompletenessMotive terminal signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ declarativeExpecteds,
      expected.BoundedBy q)
    (executableExpectedsBounded : ∀ expected ∈ executableExpecteds,
      expected.BoundedBy q)
    (expectedsRelated : TyListBisimulation before.prevailing
      declarativeExpecteds executableExpecteds)
    {raw : DDChecks signature q S context expressions declarativeExpecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (StateRunCompletion before
      (checkExprsFuel fuel signature context selfEnv parent index expressions
        executableExpecteds state) q' S' ledger') :=
  checksOrigin_complete_nonempty_from_below fuel
    (fun _ => checkComplete) before contextBounded expectedsBounded
    executableExpectedsBounded expectedsRelated audit adequate

/-! ## Matcher arms -/

/-- Context correspondence is compositional under source-order append. -/
theorem ContextBisimulation.append
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarativeLeft declarativeRight executableLeft executableRight : Context}
    (left : ContextBisimulation relation declarativeLeft executableLeft)
    (right : ContextBisimulation relation declarativeRight executableRight) :
    ContextBisimulation relation (declarativeLeft ++ declarativeRight)
      (executableLeft ++ executableRight) := by
  constructor
  · rw [Context.applySubst, List.map_append]
    change declarativeLeft.applySubst S ++ declarativeRight.applySubst S = _
    calc
      _ = (executableLeft.applySubst state.prevailing).applySubst
            relation.forward ++ declarativeRight.applySubst S :=
        congrArg (fun first : Context => first ++ declarativeRight.applySubst S)
          left.forward
      _ = (executableLeft.applySubst state.prevailing).applySubst
            relation.forward ++
          (executableRight.applySubst state.prevailing).applySubst
            relation.forward :=
        congrArg (fun second : Context =>
          (executableLeft.applySubst state.prevailing).applySubst
            relation.forward ++ second) right.forward
      _ = _ := by simp [Context.applySubst, List.map_append]
  · rw [Context.applySubst, List.map_append]
    change executableLeft.applySubst state.prevailing ++
      executableRight.applySubst state.prevailing = _
    calc
      _ = (declarativeLeft.applySubst S).applySubst relation.reverse ++
          executableRight.applySubst state.prevailing :=
        congrArg (fun first : Context =>
          first ++ executableRight.applySubst state.prevailing) left.reverse
      _ = (declarativeLeft.applySubst S).applySubst relation.reverse ++
          (declarativeRight.applySubst S).applySubst relation.reverse :=
        congrArg (fun second : Context =>
          (declarativeLeft.applySubst S).applySubst relation.reverse ++ second)
          right.reverse
      _ = _ := by simp [Context.applySubst, List.map_append]

/-- Data-pattern recursion required by an arm. -/
structure BoundedDPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger' : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  run : DPatRunCompletion before operation q' S' ledger' target bindings
  rawTargetBounded : run.result.target.BoundedBy q'
  rawBindingsBounded : run.result.bindings.BoundedBy q'

abbrev MatcherDPatCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {path : SyntaxPath} {pattern : DPat}
    {target executableTarget : Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (raw : DDDPat signature q S pattern target bindings q' S')
    (origin : DDDPatOrigin signature raw ledger ledger'),
    (before : TraversalStateCorrespondence q S ledger state) →
    TyBisimulation before.prevailing target executableTarget →
    target.BoundedBy q → executableTarget.BoundedBy q →
    DPatAdequate fuel pattern →
    Nonempty (BoundedDPatRunCompletion before
      (inferDPatFuel fuel signature path pattern executableTarget state)
      q' S' ledger' target bindings)

abbrev MatcherArmsBudgetAdequate (fuel : Nat) (arms : List Arm) : Prop :=
  8 * (armListTraversalFuel arms + 1) ≤ fuel

/-- Reconstruct an audited arm list.  Pattern output contexts are related,
not identified: the body call receives the exact executable bindings returned
by `inferDPatFuel`. -/
theorem armsOrigin_complete_nonempty_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv}
    {ppBindings executablePPBindings : MonoCtx}
    {parent : SyntaxPath} {index : Nat} {arms : List Arm}
    {declarativeClauseTarget declarativeBodyTarget : Ty}
    {executableClauseTarget executableBodyTarget : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : MatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (ppRelated : MonoCtxBisimulation before.prevailing ppBindings
      executablePPBindings)
    (clauseTargetRelated : TyBisimulation before.prevailing
      declarativeClauseTarget executableClauseTarget)
    (bodyTargetRelated : TyBisimulation before.prevailing
      declarativeBodyTarget executableBodyTarget)
    (contextBounded : context.BoundedBy q)
    (ppBounded : ppBindings.BoundedBy q)
    (executablePPBounded : executablePPBindings.BoundedBy q)
    (clauseTargetBounded : declarativeClauseTarget.BoundedBy q)
    (bodyTargetBounded : declarativeBodyTarget.BoundedBy q)
    (executableClauseTargetBounded : executableClauseTarget.BoundedBy q)
    (executableBodyTargetBounded : executableBodyTarget.BoundedBy q)
    {raw : DDArms signature q S context ppBindings arms
      declarativeClauseTarget declarativeBodyTarget q' S'}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    (adequate : MatcherArmsBudgetAdequate fuel arms) :
    Nonempty (StateRunCompletion before
      (checkArmsFuel fuel signature context selfEnv executablePPBindings
        parent index arms executableClauseTarget executableBodyTarget state)
      q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherArmsBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨checkArmsFuel_nil_complete fuel signature context selfEnv
            executablePPBindings parent index executableClauseTarget
            executableBodyTarget before⟩
      | cons bodyAudit tailAudit =>
          rename_i q₁ S₁ armBindings body q₂ S₂ ledger₁ ledger₂ arms
            dataPattern disjoint patternRaw bodyRaw bodyOrigin tailRaw
            patternOrigin tailOrigin
          have dataAdequate : DPatAdequate fuel dataPattern := by
            simp only [MatcherArmsBudgetAdequate, armListTraversalFuel,
              armTraversalFuel, DPatAdequate] at adequate ⊢
            omega
          have bodyAdequate : MatcherCheckBudgetAdequate fuel body := by
            simp only [MatcherArmsBudgetAdequate, MatcherCheckBudgetAdequate,
              armListTraversalFuel, armTraversalFuel] at adequate ⊢
            omega
          have tailAdequate : MatcherArmsBudgetAdequate fuel arms := by
            simp only [MatcherArmsBudgetAdequate, armListTraversalFuel,
              armTraversalFuel] at adequate ⊢
            omega
          let dataRun := Classical.choice
            (dpatComplete (path := 0 :: index :: parent)
              patternRaw patternOrigin before clauseTargetRelated
              clauseTargetBounded executableClauseTargetBounded dataAdequate)
          have ppAtData : MonoCtxBisimulation dataRun.run.transition.after
              ppBindings executablePPBindings :=
            BisimulationExtension.transportMonoCtx dataRun.run.transition ppRelated
          let bodyContexts := ContextBisimulation.append
            (ContextBisimulation.append dataRun.run.bindings.toContext
              ppAtData.toContext)
            (ContextBisimulation.same dataRun.run.transition.after context)
          obtain ⟨_, armBindingsBounded⟩ :=
            patternOrigin.erase.boundedBy closed before.declarative_bounded
              clauseTargetBounded
          have bodyContextBounded :
              (armBindings.toContext ++ ppBindings.toContext ++ context).BoundedBy
                q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append armBindingsBounded.toContext
                (ppBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (contextBounded.mono patternOrigin.erase.supplyExtends)
          have bodyExecutableContextBounded :
              (dataRun.run.result.bindings.toContext ++
                executablePPBindings.toContext ++ context).BoundedBy q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append dataRun.rawBindingsBounded.toContext
                (executablePPBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (contextBounded.mono patternOrigin.erase.supplyExtends)
          have bodyExpectedBounded : declarativeBodyTarget.BoundedBy q₁ :=
            bodyTargetBounded.mono patternOrigin.erase.supplyExtends
          let bodyRun := Classical.choice
            (checkBelow (Nat.lt_succ_self fuel)
              (selfEnv := selfEnv.eraseMany
                (executablePPBindings.names ++
                  dataRun.run.result.bindings.names))
              (path := 1 :: index :: parent) dataRun.run.completion
              bodyContexts
              (dataRun.run.transition.transportTy bodyTargetRelated)
              bodyContextBounded bodyExecutableContextBounded bodyExpectedBounded
              (executableBodyTargetBounded.mono
                patternOrigin.erase.supplyExtends)
              bodyAudit bodyAdequate)
          let prefixExtension := patternOrigin.erase.supplyExtends.trans
            bodyOrigin.erase.supplyExtends
          have tailContextBounded : context.BoundedBy q₂ :=
            contextBounded.mono prefixExtension
          have tailPPBounded : ppBindings.BoundedBy q₂ :=
            ppBounded.mono prefixExtension
          have tailExecutablePPBounded : executablePPBindings.BoundedBy q₂ :=
            executablePPBounded.mono prefixExtension
          have tailClauseBounded : declarativeClauseTarget.BoundedBy q₂ :=
            clauseTargetBounded.mono prefixExtension
          have tailBodyBounded : declarativeBodyTarget.BoundedBy q₂ :=
            bodyTargetBounded.mono prefixExtension
          have tailExecutableClauseBounded :
              executableClauseTarget.BoundedBy q₂ :=
            executableClauseTargetBounded.mono prefixExtension
          have tailExecutableBodyBounded :
              executableBodyTarget.BoundedBy q₂ :=
            executableBodyTargetBounded.mono prefixExtension
          have ppAtBody : MonoCtxBisimulation bodyRun.transition.after
              ppBindings executablePPBindings :=
            BisimulationExtension.transportMonoCtx
              (dataRun.run.transition.seq bodyRun.transition) ppRelated
          let tailRun := Classical.choice
            (armsOrigin_complete_nonempty_below closed dpatComplete fuel
              checkBelow.lower
              (selfEnv := selfEnv) (parent := parent) (index := index + 1)
              bodyRun.completion ppAtBody
              ((dataRun.run.transition.seq bodyRun.transition).transportTy
                clauseTargetRelated)
              ((dataRun.run.transition.seq bodyRun.transition).transportTy
                bodyTargetRelated)
              tailContextBounded tailPPBounded tailExecutablePPBounded
              tailClauseBounded tailBodyBounded tailExecutableClauseBounded
              tailExecutableBodyBounded (origin := tailOrigin)
              tailAudit tailAdequate)
          exact ⟨checkArmsFuel_cons_complete
            (executableClauseTarget := executableClauseTarget)
            (executableBodyTarget := executableBodyTarget)
            (clauseTarget := declarativeClauseTarget)
            (bodyTarget := declarativeBodyTarget)
            before ppRelated dataRun.run disjoint bodyRun tailRun⟩
termination_by fuel

/-- Unrestricted wrapper retained for completed global motives. -/
theorem armsOrigin_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    (checkComplete : MatcherCheckCompletenessMotive terminal signature)
    {context : Context} {selfEnv : SelfEnv}
    {ppBindings executablePPBindings : MonoCtx}
    {parent : SyntaxPath} {index : Nat} {arms : List Arm}
    {declarativeClauseTarget declarativeBodyTarget : Ty}
    {executableClauseTarget executableBodyTarget : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (ppRelated : MonoCtxBisimulation before.prevailing ppBindings
      executablePPBindings)
    (clauseTargetRelated : TyBisimulation before.prevailing
      declarativeClauseTarget executableClauseTarget)
    (bodyTargetRelated : TyBisimulation before.prevailing
      declarativeBodyTarget executableBodyTarget)
    (contextBounded : context.BoundedBy q)
    (ppBounded : ppBindings.BoundedBy q)
    (executablePPBounded : executablePPBindings.BoundedBy q)
    (clauseTargetBounded : declarativeClauseTarget.BoundedBy q)
    (bodyTargetBounded : declarativeBodyTarget.BoundedBy q)
    (executableClauseTargetBounded : executableClauseTarget.BoundedBy q)
    (executableBodyTargetBounded : executableBodyTarget.BoundedBy q)
    {raw : DDArms signature q S context ppBindings arms
      declarativeClauseTarget declarativeBodyTarget q' S'}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    (adequate : MatcherArmsBudgetAdequate fuel arms) :
    Nonempty (StateRunCompletion before
      (checkArmsFuel fuel signature context selfEnv executablePPBindings
        parent index arms executableClauseTarget executableBodyTarget state)
      q' S' ledger') :=
  armsOrigin_complete_nonempty_below closed dpatComplete fuel
    (fun _ => checkComplete) before ppRelated clauseTargetRelated
    bodyTargetRelated contextBounded ppBounded executablePPBounded clauseTargetBounded
    bodyTargetBounded executableClauseTargetBounded executableBodyTargetBounded
    audit adequate

/-! ## Clause data transport -/

/-- A related primitive-hole list induces the related list of slot demands
used for next-matcher checking. -/
theorem DualListBisimulation.slots
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarative executable : List Dual}
    (related : DualListBisimulation relation declarative executable) :
    TyListBisimulation relation
      (declarative.map fun hole => .slot hole.cap hole.target)
      (executable.map fun hole => .slot hole.cap hole.target) := by
  induction related with
  | nil => exact .nil
  | cons head tail induction =>
      apply TyListBisimulation.cons
      · constructor
        · simp only [Subst.apply_slot]
          rw [(Ty.matcher.inj head.cap.forward).1, head.target.forward]
        · simp only [Subst.apply_slot]
          rw [(Ty.matcher.inj head.cap.reverse).1, head.target.reverse]
      · exact induction

/-- Related primitive holes also induce the related arm-body product target.
`prodTy` has special zero- and one-field cases, hence the short shape split. -/
theorem DualListBisimulation.prodTargets
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarative executable : List Dual}
    (related : DualListBisimulation relation declarative executable) :
    TyBisimulation relation
      (prodTy (declarative.map Dual.target))
      (prodTy (executable.map Dual.target)) := by
  cases related with
  | nil => exact relation.sameTarget (.prod [])
  | cons head tail =>
      cases tail with
      | nil => exact head.target
      | cons second rest =>
          exact tyListBisimulation_prod
            (.cons head.target (.cons second.target
              (by
                induction rest with
                | nil => exact .nil
                | cons item rest induction => exact .cons item.target induction)))

/-- Syntactic decomposition never increases the next-matcher traversal
measure by more than the list-cell overhead. -/
theorem exprListTraversalFuel_decomposeME
    {next : Expr} {arity : Nat} {expressions : List Expr}
    (decomposed : decomposeME next arity = some expressions) :
    exprListTraversalFuel expressions ≤ exprTraversalFuel next + 2 := by
  cases arity with
  | zero =>
      cases next <;> simp [decomposeME] at decomposed
      rename_i children
      cases children with
      | nil =>
          simp only [Option.some.injEq] at decomposed
          subst expressions
          simp [exprListTraversalFuel, exprTraversalFuel]
      | cons => simp at decomposed
  | succ arity =>
      cases arity with
      | zero =>
          simp [decomposeME] at decomposed
          subst expressions
          simp [exprListTraversalFuel]
          omega
      | succ arity =>
          cases next <;> simp [decomposeME] at decomposed
          rename_i children
          rcases decomposed with ⟨_, rfl⟩
          simp [exprTraversalFuel]
          omega

/-- Primitive-pattern recursion required by a clause. -/
structure BoundedPPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger' : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  run : PPatRunCompletion before operation q' S' ledger' target holes bindings
  rawTargetBounded : run.result.target.BoundedBy q'
  rawHolesBounded : ∀ hole ∈ run.result.holes, Dual.BoundedBy q' hole
  rawBindingsBounded : run.result.bindings.BoundedBy q'

abbrev MatcherPPatCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {path : SyntaxPath} {pattern : PPat}
    {target executableTarget : Ty} {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (raw : DDPPat signature q S pattern target holes bindings q' S')
    (origin : DDPPatOrigin signature raw ledger ledger'),
    (before : TraversalStateCorrespondence q S ledger state) →
    TyBisimulation before.prevailing target executableTarget →
    target.BoundedBy q → executableTarget.BoundedBy q →
    PPatAdequate fuel pattern →
    Nonempty (BoundedPPatRunCompletion before
      (inferPPatFuel fuel signature path pattern executableTarget state)
      q' S' ledger' target holes bindings)

abbrev MatcherClauseBudgetAdequate (fuel : Nat) (clause : Clause) : Prop :=
  8 * (clauseTraversalFuel clause + 1) ≤ fuel

/-- Reconstruct one audited matcher clause from primitive-pattern, checking,
and arm motives. -/
theorem clauseOrigin_complete_nonempty_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {clause : Clause} {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : MatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : context.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClause signature q S context clause declarativeTarget holes q' S'}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    (audit : DDClauseTerminalAudit terminal signature origin)
    (adequate : MatcherClauseBudgetAdequate fuel clause) :
    Nonempty (ClauseRunCompletion before
      (inferClauseFuel fuel signature context selfEnv path clause
        executableTarget state)
      q' S' ledger' declarativeTarget holes) := by
  cases fuel with
  | zero => simp [MatcherClauseBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | mk nextAudit armsAudit =>
          rename_i q₁ S₁ nextMatchers q₂ S₂ ledger₁ ledger₂ ppBindings
            arms primitivePattern next decomposed nextRaw nextOrigin ppRaw
            armsRaw ppOrigin armsOrigin
          have primitiveAdequate : PPatAdequate fuel primitivePattern := by
            simp only [MatcherClauseBudgetAdequate, clauseTraversalFuel,
              PPatAdequate] at adequate ⊢
            omega
          have nextAdequate :
              MatcherChecksBudgetAdequate fuel nextMatchers := by
            have measure := exprListTraversalFuel_decomposeME decomposed
            have primitivePositive : 0 < ppatTraversalFuel primitivePattern := by
              cases primitivePattern <;>
                simp only [ppatTraversalFuel] <;> omega
            have armsPositive : 0 < armListTraversalFuel arms := by
              cases arms <;> simp only [armListTraversalFuel] <;> omega
            simp only [MatcherClauseBudgetAdequate, MatcherChecksBudgetAdequate,
              clauseTraversalFuel] at adequate ⊢
            omega
          have armsAdequate : MatcherArmsBudgetAdequate fuel arms := by
            simp only [MatcherClauseBudgetAdequate, MatcherArmsBudgetAdequate,
              clauseTraversalFuel] at adequate ⊢
            omega
          let visited := before.visit .clause path
          let primitiveRun := Classical.choice
            (ppatComplete (path := 0 :: path) ppRaw ppOrigin visited
              ((before.visitExtension .clause path).transportTy targetRelated)
              targetBounded executableTargetBounded primitiveAdequate)
          obtain ⟨_, holesBounded, ppBindingsBounded⟩ :=
            ppOrigin.erase.boundedBy closed before.declarative_bounded
              targetBounded
          have nextContextBounded : context.BoundedBy q₁ :=
            contextBounded.mono ppOrigin.erase.supplyExtends
          have nextExpectedsBounded : ∀ expected : Ty, expected ∈
              (holes.map fun hole => Ty.slot hole.cap hole.target) →
              Ty.BoundedBy q₁ expected := by
            intro expected membership
            obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
            exact Ty.BoundedBy.slotOf (holesBounded hole holeMembership).1
              (holesBounded hole holeMembership).2
          let nextRun := Classical.choice
            (checksOrigin_complete_nonempty_from_below
              (selfEnv := selfEnv) (parent := 1 :: path) (index := 0)
              fuel checkBelow.lower primitiveRun.run.completion nextContextBounded
              nextExpectedsBounded (fun expected membership => by
                obtain ⟨hole, holeMembership, rfl⟩ :=
                  List.mem_map.mp membership
                exact Ty.BoundedBy.slotOf
                  (primitiveRun.rawHolesBounded hole holeMembership).1
                  (primitiveRun.rawHolesBounded hole holeMembership).2)
              (DualListBisimulation.slots primitiveRun.run.holes) nextAudit
              nextAdequate)
          let targetAtNext := (primitiveRun.run.transition.seq nextRun.transition).transportTy
            ((before.visitExtension .clause path).transportTy targetRelated)
          let ppAtNext := BisimulationExtension.transportMonoCtx
            nextRun.transition primitiveRun.run.bindings
          let holesAtNext := BisimulationExtension.transportDualList
            nextRun.transition primitiveRun.run.holes
          have armsContextBounded : context.BoundedBy q₂ :=
            contextBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          have armsPPBounded : ppBindings.BoundedBy q₂ :=
            ppBindingsBounded.mono nextOrigin.erase.supplyExtends
          have armsTargetBounded : declarativeTarget.BoundedBy q₂ :=
            targetBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          let declarativeBodyTarget :=
            Ty.listT (prodTy (holes.map Dual.target))
          let executableBodyTarget :=
            Ty.listT (prodTy (primitiveRun.run.result.holes.map Dual.target))
          have bodyTargetRelated : TyBisimulation nextRun.transition.after
              declarativeBodyTarget executableBodyTarget :=
            DemandTypingInferenceCompletenessExprTraversal.TyBisimulation.listT
              (DualListBisimulation.prodTargets holesAtNext)
          have armsBodyBounded : declarativeBodyTarget.BoundedBy q₂ := by
            exact listT_boundedBy (prodTy_boundedBy (fun target membership => by
              obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
              exact (holesBounded hole holeMembership).2.mono
                nextOrigin.erase.supplyExtends))
          have armsExecutableTargetBounded : executableTarget.BoundedBy q₂ :=
            executableTargetBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          have armsExecutableBodyBounded : executableBodyTarget.BoundedBy q₂ := by
            exact listT_boundedBy (prodTy_boundedBy (fun target membership => by
              obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
              exact (primitiveRun.rawHolesBounded hole holeMembership).2.mono
                nextOrigin.erase.supplyExtends))
          let armsRun := Classical.choice
            (armsOrigin_complete_nonempty_below closed dpatComplete fuel
              checkBelow.lower
              (selfEnv := selfEnv) (parent := 2 :: path) (index := 0)
              nextRun.completion ppAtNext targetAtNext bodyTargetRelated
              armsContextBounded armsPPBounded
              (primitiveRun.rawBindingsBounded.mono
                nextOrigin.erase.supplyExtends) armsTargetBounded
              armsBodyBounded armsExecutableTargetBounded
              armsExecutableBodyBounded armsAudit armsAdequate)
          exact ⟨inferClauseFuel_complete before targetRelated primitiveRun.run
            decomposed nextRun armsRun⟩

/-- Unrestricted wrapper retained for completed global motives. -/
theorem clauseOrigin_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    (checkComplete : MatcherCheckCompletenessMotive terminal signature)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {clause : Clause} {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : context.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClause signature q S context clause declarativeTarget holes q' S'}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    (audit : DDClauseTerminalAudit terminal signature origin)
    (adequate : MatcherClauseBudgetAdequate fuel clause) :
    Nonempty (ClauseRunCompletion before
      (inferClauseFuel fuel signature context selfEnv path clause
        executableTarget state)
      q' S' ledger' declarativeTarget holes) :=
  clauseOrigin_complete_nonempty_below closed ppatComplete dpatComplete fuel
    (fun _ => checkComplete) before targetRelated contextBounded targetBounded
    executableTargetBounded audit adequate

/-! ## Clause lists -/

abbrev MatcherClausesBudgetAdequate
    (fuel : Nat) (clauses : List Clause) : Prop :=
  8 * (clauseListTraversalFuel clauses + 1) ≤ fuel

/-- Full origin-and-audit dispatcher for matcher clause lists.  The shared
matcher target remains paired through every completed head transition. -/
theorem clausesOrigin_complete_nonempty_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holeLists : List (List Dual)}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : MatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : context.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClauses signature q S context clauses declarativeTarget holeLists
      q' S'}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (adequate : MatcherClausesBudgetAdequate fuel clauses) :
    Nonempty (ClausesRunCompletion before
      (inferClausesFuel fuel signature context selfEnv parent index clauses
        executableTarget state)
      q' S' ledger' declarativeTarget holeLists) := by
  cases fuel with
  | zero => simp [MatcherClausesBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨inferClausesFuel_nil_complete fuel signature context selfEnv
            parent index before targetRelated⟩
      | cons headAudit tailAudit =>
          rename_i clause holes q₁ S₁ ledger₁ clauses holeLists headRaw
            tailRaw headOrigin tailOrigin
          have headAdequate : MatcherClauseBudgetAdequate fuel clause := by
            have tailPositive : 0 < clauseListTraversalFuel clauses := by
              cases clauses <;> simp only [clauseListTraversalFuel] <;> omega
            simp only [MatcherClausesBudgetAdequate,
              MatcherClauseBudgetAdequate, clauseListTraversalFuel]
              at adequate ⊢
            omega
          have tailAdequate : MatcherClausesBudgetAdequate fuel clauses := by
            have headPositive : 0 < clauseTraversalFuel clause := by
              cases clause
              simp only [clauseTraversalFuel]
              omega
            simp only [MatcherClausesBudgetAdequate,
              clauseListTraversalFuel] at adequate ⊢
            omega
          let headRun := Classical.choice
            (clauseOrigin_complete_nonempty_below closed ppatComplete
              dpatComplete (selfEnv := selfEnv) (path := index :: parent)
              fuel checkBelow.lower before targetRelated contextBounded
              targetBounded executableTargetBounded headAudit headAdequate)
          have tailContextBounded : context.BoundedBy q₁ :=
            contextBounded.mono headOrigin.erase.supplyExtends
          have tailTargetBounded : declarativeTarget.BoundedBy q₁ :=
            targetBounded.mono headOrigin.erase.supplyExtends
          have tailExecutableTargetBounded : executableTarget.BoundedBy q₁ :=
            executableTargetBounded.mono headOrigin.erase.supplyExtends
          let tailRun := Classical.choice
            (clausesOrigin_complete_nonempty_below closed ppatComplete
              dpatComplete (selfEnv := selfEnv) (parent := parent)
              (index := index + 1) fuel checkBelow.lower headRun.completion
              (headRun.transition.transportTy targetRelated)
              tailContextBounded tailTargetBounded
              tailExecutableTargetBounded tailAudit tailAdequate)
          exact ⟨inferClausesFuel_cons_complete before targetRelated headRun
            tailRun⟩
termination_by fuel

/-- Strict-ceiling matcher dispatcher used by the enclosing expression
recursion.  Every checking call occurs below `bound`; no unrestricted
self-hypothesis is manufactured inside the matcher traversal. -/
theorem clausesOrigin_complete_nonempty_from_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {bound : Nat}
    (checkBelow : MatcherCheckCompletenessBelow terminal signature bound)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holeLists : List (List Dual)}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (fuelLt : fuel < bound)
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : context.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClauses signature q S context clauses declarativeTarget holeLists
      q' S'}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (adequate : MatcherClausesBudgetAdequate fuel clauses) :
    Nonempty (ClausesRunCompletion before
      (inferClausesFuel fuel signature context selfEnv parent index clauses
        executableTarget state)
      q' S' ledger' declarativeTarget holeLists) :=
  clausesOrigin_complete_nonempty_below closed ppatComplete dpatComplete fuel
    (fun {childFuel} childLt =>
      checkBelow (Nat.lt_trans childLt fuelLt)) before
    targetRelated contextBounded targetBounded executableTargetBounded audit
    adequate

/-- Unrestricted wrapper retained for completed global motives. -/
theorem clausesOrigin_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    (checkComplete : MatcherCheckCompletenessMotive terminal signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holeLists : List (List Dual)}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : context.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClauses signature q S context clauses declarativeTarget holeLists
      q' S'}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (adequate : MatcherClausesBudgetAdequate fuel clauses) :
    Nonempty (ClausesRunCompletion before
      (inferClausesFuel fuel signature context selfEnv parent index clauses
        executableTarget state)
      q' S' ledger' declarativeTarget holeLists) :=
  clausesOrigin_complete_nonempty_below closed ppatComplete dpatComplete fuel
    (fun _ => checkComplete) before targetRelated contextBounded targetBounded
    executableTargetBounded audit adequate

end DemandTypingInferenceCompletenessMatcherMain
end TypePM
