import TypePM.DemandTypingInferenceEquivalence
import TypePM.RecursiveExamples

/-!
# Executable acceptance-equivalence regressions

These closed examples specialize the public Milestone 6 interface without
adding a source annotation, a typing premise, or an executable-success
premise.  The first two pin the general-context and closed-program
equivalences.  The flagship `matchAll` example separately checks that the
concrete type reported by `inferType` has a `DDTyping` derivation; it does not
claim that every independently derived DD target is syntactically equal to
that reported type.
-/

namespace TypePM
namespace DemandTypingInferenceEquivalenceRegression

/-- The context-general acceptance equivalence specializes to the complete
recursive list matcher without any caller-supplied typing or run witness. -/
theorem listMatcher_ddTypable_iff_infer_isSome :
    (∃ target, DDTyping RecursiveExamples.listSignature []
      RecursiveExamples.listMatcher target) ↔
      (Inference.infer RecursiveExamples.listSignature []
        RecursiveExamples.listMatcher).isSome = true :=
  Inference.ddTypable_iff_infer_isSome RecursiveExamples.listSignature_wf

/-- The dedicated closed-program statement covers the larger multiset
matcher, including its additional `join` pattern constructor. -/
theorem paperCompleteMultisetMatcher_annotation_free :
    (∃ target, DDTyping RecursiveExamples.multisetSignature []
      RecursiveExamples.paperCompleteMultisetMatcher target) ↔
      (Inference.infer RecursiveExamples.multisetSignature []
        RecursiveExamples.paperCompleteMultisetMatcher).isSome = true :=
  Inference.annotation_freeness
    RecursiveExamples.multisetSignature_wf

/-- The reverse direction of annotation-freeness reflects a concrete public
acceptance bit into existential source typability. -/
theorem listMatcher_typable_of_acceptance :
    ∃ target, DDTyping RecursiveExamples.listSignature []
      RecursiveExamples.listMatcher target := by
  apply (Inference.annotation_freeness
    RecursiveExamples.listSignature_wf).2
  simpa [Inference.inferenceSucceeds] using
    RecursiveExamples.listMatcher_inference_succeeds

/-- The forward direction sends the resulting source-typability witness back
to public executable acceptance without exposing its target. -/
theorem listMatcher_acceptance_of_typability :
    (Inference.infer RecursiveExamples.listSignature []
      RecursiveExamples.listMatcher).isSome = true :=
  (Inference.annotation_freeness RecursiveExamples.listSignature_wf).1
    listMatcher_typable_of_acceptance

/-- The type-only API reports the exact concrete type already pinned for the
recursive-matcher `matchAll` example.  This is a fact about the deterministic
executable result, not a DD target-uniqueness theorem. -/
theorem listMatcherMatchAll_inferType_result :
    Inference.inferType RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll =
        some RecursiveExamples.listMatcherMatchAllTy := by
  simp [Inference.inferType,
    RecursiveExamples.listMatcherMatchAllInferenceResult_success,
    RecursiveExamples.listMatcherMatchAllInferenceResult_target]

/-- Consequently the type returned by `inferType` is a source-facing DD
type for the flagship recursive matcher consumer. -/
theorem listMatcherMatchAll_inferType_ddTyping :
    DDTyping RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll
      RecursiveExamples.listMatcherMatchAllTy :=
  Inference.inferType_success_ddTyping listMatcherMatchAll_inferType_result

/-- Compilation of this definition pins the public decision procedure for
DD typability independently of the concrete positive result above. -/
def listMatcherMatchAll_ddTypableDecidable :
    Decidable (∃ target, DDTyping RecursiveExamples.listSignature []
      RecursiveExamples.listMatcherMatchAll target) :=
  Inference.ddTypableDecidable RecursiveExamples.listSignature []
    RecursiveExamples.listMatcherMatchAll RecursiveExamples.listSignature_wf

end DemandTypingInferenceEquivalenceRegression
end TypePM
