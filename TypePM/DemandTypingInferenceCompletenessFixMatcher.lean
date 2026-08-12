import TypePM.DemandTypingInferenceCompletenessMatcherExprTraversal
import TypePM.DemandTypingInferenceCompletenessPatternCtorCapability

/-! # Recursive-matcher placeholder completeness -/

namespace TypePM
namespace DemandTypingInferenceCompletenessFixMatcher

open Inference
open DemandTypingInferenceCompletenessPatternCtorCapability

/-- The executable recursive-matcher placeholder exists whenever its pure
supply twin succeeds.  The already-proved forward correspondence then pins
the terminal supply exactly. -/
theorem buildFixPlaceholder_complete_of_supply
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {initial : InferState} {domain codomain : Ty}
    {q₀ : InferenceBase.FreshSupply}
    (pure : fixMatcherPlaceholderSupply signature clauses initial.supply =
      some (domain, codomain, q₀)) :
    ∃ final, buildFixPlaceholder signature path (.matcher clauses) initial =
        some (domain, codomain, final) ∧ final.supply = q₀ := by
  unfold fixMatcherPlaceholderSupply at pure
  cases evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses with
  | none => simp [evidenceEq] at pure
  | some evidence =>
      cases evidence with
      | unseen =>
          simp [evidenceEq, Cap.fcv] at pure
          rcases pure with ⟨rfl, rfl, rfl⟩
          let capState := (initial.freshCap
            (freshOrigin .recursiveBinder path
              "fix-argument-capability")).2
          let targetState := (capState.freshTy
            (freshOrigin .recursiveBinder path "fix-argument-target")).2
          let final := (targetState.freshTy
            (freshOrigin .recursiveBinder path "fix-producer-target")).2
          refine ⟨final, ?_, ?_⟩
          · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
              Cap.fcv, capState, targetState, final, InferState.freshCap,
              InferState.freshTy, InferenceBase.freshCapMeta,
              InferenceBase.freshTyMeta]
          · simp [capState, targetState, final, InferState.freshCap,
              InferState.freshTy, InferenceBase.freshCapMeta,
              InferenceBase.freshTyMeta]
      | known leaf =>
          exact completeFresh evidenceEq (by simp) pure
      | con name children =>
          exact completeFresh evidenceEq (by simp) pure
      | prod components =>
          exact completeFresh evidenceEq (by simp) pure
where
  completeFresh
      {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
      {initial : InferState} {evidence : Shape.Evidence}
      {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
      (evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses =
        some evidence)
      (notUnseen : evidence ≠ .unseen)
      (pure : fixMatcherPlaceholderSupply signature clauses initial.supply =
        some (domain, codomain, q₀)) :
      ∃ final, buildFixPlaceholder signature path (.matcher clauses) initial =
          some (domain, codomain, final) ∧ final.supply = q₀ := by
    cases freshEq : freshenSkeletonSupply signature.observability evidence
        initial.supply with
    | none =>
        unfold fixMatcherPlaceholderSupply at pure
        simp [evidenceEq, notUnseen, freshEq] at pure
    | some pair =>
        rcases pair with ⟨capability, q₁⟩
        rcases freshenSkeleton_complete_exact
            (origin := freshOrigin .recursiveBinder path
              "fix-producer-shape") freshEq with
          ⟨middle, executableFresh, supplyEq, _, _⟩
        have pureTail := pure
        unfold fixMatcherPlaceholderSupply at pureTail
        simp [evidenceEq, notUnseen, freshEq] at pureTail
        generalize fcvEq : capability.fcv = variables at pureTail
        cases variables with
        | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq] at pureTail
            rcases pureTail with ⟨rfl, rfl, rfl⟩
            let capState := (middle.freshCap
              (freshOrigin .recursiveBinder path
                "fix-argument-capability")).2
            let targetState := (capState.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
            let final := (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
            refine ⟨final, ?_, ?_⟩
            · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
                executableFresh, fcvEq, capState, targetState, final,
                InferState.freshCap, InferState.freshTy,
                InferenceBase.freshCapMeta, InferenceBase.freshTyMeta,
                supplyEq]
            · rw [← supplyEq]
              simp [capState, targetState, final, InferState.freshCap,
                InferState.freshTy, InferenceBase.freshCapMeta,
                InferenceBase.freshTyMeta]
        | cons first rest =>
            simp only [Option.some.injEq, Prod.mk.injEq] at pureTail
            rcases pureTail with ⟨rfl, rfl, rfl⟩
            let targetState := (middle.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
            let final := (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
            refine ⟨final, ?_, ?_⟩
            · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
                executableFresh, fcvEq, targetState, final,
                InferState.freshTy, InferenceBase.freshTyMeta, supplyEq]
            · rw [← supplyEq]
              simp [targetState, final, InferState.freshTy,
                InferenceBase.freshTyMeta]

end DemandTypingInferenceCompletenessFixMatcher
end TypePM
