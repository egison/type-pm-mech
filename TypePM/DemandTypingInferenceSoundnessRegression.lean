import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.CertifiedInferenceRegression
import TypePM.RecursiveExamples

/-!
# Public executable-to-demand-directed soundness regressions

These examples exercise the public `infer_success_sourceTyping` boundary rather
than a constructor-local reconstruction lemma.  The first fixes terminal
generalization after `let`; the second crosses the recursive-matcher,
matcher-clause, pattern-constructor, and `matchAll` branches in one run.
-/

namespace TypePM
namespace DemandTypingInferenceSoundnessRegression

/-- A successful `let` whose ambient lambda variable is solved later produces
a public demand-directed typing derivation at its reported type. -/
theorem terminalLet_sourceTyping :
    SourceTyping CertifiedInferenceRegression.emptySignature []
      CertifiedInferenceRegression.terminalLetExpression
      CertifiedInferenceRegression.terminalLetResult.resolvedTarget :=
  Inference.infer_success_sourceTyping
    CertifiedInferenceRegression.terminalLetResult_success

/-- The flagship recursive matcher and its nontrivial `matchAll` consumer are
accepted by the public inference soundness theorem. -/
theorem listMatcherMatchAll_sourceTyping :
    SourceTyping RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll
      RecursiveExamples.listMatcherMatchAllTy := by
  have typing := Inference.infer_success_sourceTyping
    RecursiveExamples.listMatcherMatchAllInferenceResult_success
  rw [RecursiveExamples.listMatcherMatchAllInferenceResult_target] at typing
  exact typing

end DemandTypingInferenceSoundnessRegression
end TypePM
