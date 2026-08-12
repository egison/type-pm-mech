import TypePM.DemandTypingInferenceCompletenessMatcherGlobal
import TypePM.DemandTypingInferenceCompletenessPatternCtorCapComplete

/-!
# Closed global paired completeness recursion

This module ties the expression, checking, user-pattern, and matcher-clause
components into one strong induction on executable fuel.  Matcher literals
consume two administrative fuel units; `matchAll` consumes one.  Every
recursive callback therefore comes from the strict lower-fuel hypothesis.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessGlobalRecursion

open Inference
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessMatcherGlobal
open DemandTypingInferenceCompletenessPatternCtorCapComplete

/-- Terminal-audited DD synthesis is complete for the executable traversal at
every fuel satisfying the weighted syntax budget. -/
theorem pairedAuditedSynthCompleteness
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (armBasic : signature.armExhaustive = basicArmExhaustive) :
    ∀ fuel, PairedAuditedSynthCompletenessAt terminal signature fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel smaller =>
      intro declarativeContext executableContext selfEnv path expression target
        q q' S S' ledger ledger' state raw origin before signatureBelow
        contexts contextBounded executableContextBounded audit adequate
      have synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
          fuel := by
        intro childFuel childLt
        exact smaller childFuel childLt
      apply auditedSynth_complete_paired_except_matchers closed synthBelow before
        signatureBelow contexts contextBounded executableContextBounded audit
        adequate
      · intro clauses rawHoleLists q'' S'' evidence capability ledger₁
          clausesRaw clausesOrigin collected inferred clauseCaps catchAll
          binders arms coverage clausesAudit facts caseAdequate
        cases fuel with
        | zero => simp [SynthBudgetAdequate] at caseAdequate
        | succ predecessor =>
            cases predecessor with
            | zero =>
                simp [SynthBudgetAdequate, exprTraversalFuel]
                  at caseAdequate
                omega
            | succ inner =>
                exact auditedSynthMatcher_complete_paired closed armBasic
                  inner
                  (pairedMatcherCheckCompletenessBelow_of_paired closed
                    (synthBelow.mono (by omega)))
                  before signatureBelow contexts contextBounded
                  executableContextBounded collected inferred clauseCaps
                  catchAll binders arms coverage clausesAudit facts caseAdequate
      · intro targetExpr matcher pattern body bodyTy q'' S'' ledger'' raw'
          origin' matchAllAudit caseAdequate
        cases matchAllAudit with
        | matchAll targetAudit patternAudit matcherAudit bodyAudit =>
            cases fuel with
            | zero => simp [SynthBudgetAdequate] at caseAdequate
            | succ inner =>
                exact auditedSynthMatchAll_complete_paired closed
                  (patternCtorCapCompletenessPackage signature) inner synthBelow
                  before signatureBelow contexts contextBounded
                  executableContextBounded (by assumption) targetAudit
                  patternAudit matcherAudit bodyAudit caseAdequate

end DemandTypingInferenceCompletenessGlobalRecursion
end TypePM
