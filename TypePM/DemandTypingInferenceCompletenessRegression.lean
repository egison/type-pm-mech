import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.DemandTypingRegression
import TypePM.RecursiveExamples

/-!
# Acceptance-completeness regressions

These examples pin the premise-free public theorem on the two recursive
matcher signatures used by the end-to-end suite.  Their existing executable
success witnesses are first reflected into `SourceTyping`; completeness must then
recover Boolean acceptance without any caller-supplied paired root.  They
exercise recursive matcher finalization, the larger multiset constructor
family, and a pattern-constructor consumer under `matchAll`.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessRegression

open DemandTypingInferenceCompletenessPublic

/-- A demand-directed derivation assembled independently of executable inference still
reaches public acceptance.  This pins the terminal audit as a genuine
relative-completeness premise rather than a copy of an `infer` result. -/
theorem handwrittenOrProgram_infer_isSome :
    (Inference.infer RecursiveExamples.listSignature []
      AcceptanceGapRegression.orProgram).isSome = true := by
  exact SourceTyping.infer_isSome
    (DemandTypingRegression.orProgram_sourceTyping RecursiveExamples.listSignature
      (by decide))
    RecursiveExamples.listSignature_wf

/-- The recursive list matcher reaches public acceptance from `SourceTyping`
under the executable frozen-signature check. -/
theorem listMatcher_infer_isSome :
    (Inference.infer RecursiveExamples.listSignature []
      RecursiveExamples.listMatcher).isSome = true := by
  have typing := Inference.infer_success_sourceTyping
    RecursiveExamples.listMatcherInferenceResult_success
  exact SourceTyping.infer_isSome typing RecursiveExamples.listSignature_wf

/-- The multiset matcher covers the additional `join` constructor while
crossing the same recursive matcher-finalization boundary. -/
theorem paperCompleteMultisetMatcher_infer_isSome :
    (Inference.infer RecursiveExamples.multisetSignature []
      RecursiveExamples.paperCompleteMultisetMatcher).isSome = true := by
  have typing := Inference.infer_success_sourceTyping
    RecursiveExamples.paperCompleteMultisetInferenceResult_success
  exact SourceTyping.infer_isSome typing RecursiveExamples.multisetSignature_wf

/-- The flagship consumer combines recursive matcher inference with a
user-pattern constructor and `matchAll`. -/
theorem listMatcherMatchAll_infer_isSome :
    (Inference.infer RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll).isSome = true := by
  have typing := Inference.infer_success_sourceTyping
    RecursiveExamples.listMatcherMatchAllInferenceResult_success
  exact SourceTyping.infer_isSome typing RecursiveExamples.listSignature_wf

end DemandTypingInferenceCompletenessRegression
end TypePM
