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

/-- Traversal-stable, terminal-audited checking component required by matcher
arms.  Declarative and executable contexts may differ after pattern binding,
but are related by the current state bisimulation. -/
abbrev MatcherCheckCompletenessMotive
    (terminal : Subst) (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected : Ty} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDCheck signature q S declarativeContext expression expected q' S'}
    {origin : DDCheckOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext executableContext →
    declarativeContext.BoundedBy q → expected.BoundedBy q →
    DDCheckTerminalAudit terminal signature origin →
    MatcherCheckBudgetAdequate fuel expression →
    Nonempty (StateRunCompletion before
      (checkExprFuel fuel signature executableContext selfEnv path expression
        expected state) q' S' ledger')

/-- Reconstruct an audited left-to-right checking list from the single
expression checking motive.  Each tail is run at the concrete state returned
by its head. -/
theorem checksOrigin_complete_nonempty_from_check
    {terminal : Subst} {signature : FrozenSig}
    (checkComplete : MatcherCheckCompletenessMotive terminal signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {expressions : List Expr} {expecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ expecteds, expected.BoundedBy q)
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (StateRunCompletion before
      (checkExprsFuel fuel signature context selfEnv parent index expressions
        expecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨checkExprsFuel_nil_complete fuel signature context selfEnv
            parent index before⟩
      | cons headAudit tailAudit =>
              rename_i expression expected q₁ S₁ ledger₁ expressions
                expecteds headRaw tailRaw headOrigin tailOrigin
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
              let headRun := Classical.choice
                (checkComplete (selfEnv := selfEnv) (path := index :: parent)
                  before
                  (ContextBisimulation.same before.prevailing context)
                  contextBounded expectedBounded headAudit headAdequate)
              have tailContextBounded : context.BoundedBy q₁ :=
                contextBounded.mono headOrigin.erase.supplyExtends
              have tailExpectedsBounded :
                  ∀ item ∈ expecteds, item.BoundedBy q₁ := by
                intro item membership
                exact (expectedsBounded item (by simp [membership])).mono
                  headOrigin.erase.supplyExtends
              let tailRun := Classical.choice
                (checksOrigin_complete_nonempty_from_check
                  (selfEnv := selfEnv) (parent := parent)
                  (index := index + 1) checkComplete fuel headRun.completion
                  tailContextBounded tailExpectedsBounded tailAudit
                  tailAdequate)
              exact ⟨checkExprsFuel_cons_complete before headRun tailRun⟩
termination_by fuel

end DemandTypingInferenceCompletenessMatcherMain
end TypePM
