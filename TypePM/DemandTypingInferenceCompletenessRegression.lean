import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.RecursiveExamples

/-!
# Acceptance-completeness regressions

These examples pin the proof-erasing paired-root facade on the two recursive
matcher signatures used by the end-to-end suite.  They exercise recursive
matcher finalization, the larger multiset constructor family, and a
pattern-constructor consumer under `matchAll`.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessRegression

open DemandTypingInferenceCompletenessPairedRoot
open DemandTypingInferenceCompletenessPublic

/-- The recursive list matcher reaches public acceptance from its internal
paired root certificate under the executable frozen-signature check. -/
theorem listMatcher_infer_isSome
    (root : Nonempty (PairedRootCertifiedSynthesis
      RecursiveExamples.listSignature [] RecursiveExamples.listMatcher)) :
    (Inference.infer RecursiveExamples.listSignature []
      RecursiveExamples.listMatcher).isSome = true :=
  infer_isSome_of_rootCertified RecursiveExamples.listSignature_wf root

/-- The multiset matcher covers the additional `join` constructor while
crossing the same recursive matcher-finalization boundary. -/
theorem paperCompleteMultisetMatcher_infer_isSome
    (root : Nonempty (PairedRootCertifiedSynthesis
      RecursiveExamples.multisetSignature []
        RecursiveExamples.paperCompleteMultisetMatcher)) :
    (Inference.infer RecursiveExamples.multisetSignature []
      RecursiveExamples.paperCompleteMultisetMatcher).isSome = true :=
  infer_isSome_of_rootCertified RecursiveExamples.multisetSignature_wf root

/-- The flagship consumer combines recursive matcher inference with a
user-pattern constructor and `matchAll`. -/
theorem listMatcherMatchAll_infer_isSome
    (root : Nonempty (PairedRootCertifiedSynthesis
      RecursiveExamples.listSignature []
        RecursiveExamples.listMatcherMatchAll)) :
    (Inference.infer RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll).isSome = true :=
  infer_isSome_of_rootCertified RecursiveExamples.listSignature_wf root

end DemandTypingInferenceCompletenessRegression
end TypePM
