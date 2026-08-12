import TypePM.CertifiedInference
import TypePM.CoherentTyping
import TypePM.SignatureChecker

/-!
# End-to-end recursive matcher regressions

This file deliberately keeps only the executable examples.  Their source
typing derivations are reconstructed from successful Algorithm W runs and
algorithmic trace certificates; no parallel handwritten typing proof is
maintained.
-/

namespace TypePM
namespace RecursiveExamples

/-! ## Frozen generic List signature -/

def observability : Shape.Observability :=
  fun former => if former = "List" then some [true] else none

def a : Ty := .var 0
def listA : Ty := .data "List" [a]

def nilScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := []
  result := listA

def consScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [a, listA]
  result := listA

def joinScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [listA, listA]
  result := listA

def nilProjection : Projection.ProjectionSignature observability where
  fieldTypes := nilScheme.args
  resultType := nilScheme.result
  resultRoot := .data (mask := [true]) (by
    simp [observability]) (by simp)

def consProjection : Projection.ProjectionSignature observability where
  fieldTypes := consScheme.args
  resultType := consScheme.result
  resultRoot := .data (mask := [true]) (by
    simp [observability]) (by simp)

def joinProjection : Projection.ProjectionSignature observability where
  fieldTypes := joinScheme.args
  resultType := joinScheme.result
  resultRoot := .data (mask := [true]) (by
    simp [observability]) (by simp)

def nilPatternCtor : PatternCtorScheme observability where
  scheme := nilScheme
  projection := nilProjection
  projectionFields := rfl
  projectionResult := rfl

def consPatternCtor : PatternCtorScheme observability where
  scheme := consScheme
  projection := consProjection
  projectionFields := rfl
  projectionResult := rfl

def joinPatternCtor : PatternCtorScheme observability where
  scheme := joinScheme
  projection := joinProjection
  projectionFields := rfl
  projectionResult := rfl

def listSignature : FrozenSig where
  observability := observability
  dataCtors := [("nil", nilScheme), ("cons", consScheme)]
  patternCtors :=
    [("nil", nilPatternCtor),
      ("cons", consPatternCtor)]
  patternFuns := []
  primitives := []
  constructorsByFormer :=
    [("List", [("nil", 0), ("cons", 2)])]
  armExhaustive := basicArmExhaustive

def multisetSignature : FrozenSig where
  observability := observability
  dataCtors := [("nil", nilScheme), ("cons", consScheme)]
  patternCtors :=
    [("nil", nilPatternCtor),
      ("cons", consPatternCtor),
      ("join", joinPatternCtor)]
  patternFuns := []
  primitives := []
  constructorsByFormer :=
    [("List", [("nil", 0), ("cons", 2), ("join", 2)])]
  armExhaustive := basicArmExhaustive

/--
The generic list signature—with its non-empty pattern-constructor table and
coverage index—satisfies every dynamic frozen-signature obligation.  Unlike
the earlier empty-table regressions, the pattern-constructor uniqueness and
index-coherence fields of `FrozenSigWF` are discharged non-vacuously here,
by one run of the executable signature checker.
-/
theorem listSignature_wf : FrozenSigWF listSignature :=
  frozenSigWFCheck_sound (by decide) rfl

/-- The multiset signature, including `join`, passes the same checker. -/
theorem multisetSignature_wf : FrozenSigWF multisetSignature :=
  frozenSigWFCheck_sound (by decide) rfl

/-- A declared pattern-constructor family without its coverage-index row is
rejected instead of satisfying index coherence vacuously. -/
def listSignatureWithoutCoverageIndex : FrozenSig :=
  { listSignature with constructorsByFormer := [] }

theorem listSignatureWithoutCoverageIndex_checker_rejects :
    frozenSigWFCheck listSignatureWithoutCoverageIndex = false := by
  decide

/-! ## Complete recursive List and paper multiset terms -/

def selfName := "self"
def argumentName := "m"

def nilClause : Clause :=
  .mk (generalPP "nil" 0) (.tuple [])
    [.mk .wild (.ctor "nil" [])]

def selfCall : Expr := .app (.var selfName) (.var argumentName)

def consClause : Clause :=
  .mk (generalPP "cons" 2)
    (.tuple [.var argumentName, selfCall])
    [.mk .wild (.ctor "nil" [])]

def catchClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole") (.ctor "nil" [])]

def listClauses : List Clause :=
  [nilClause, consClause, catchClause]

def listMatcher : Expr :=
  .fix selfName argumentName (.matcher listClauses)

def multisetSelfName := "multisetSelf"
def multisetArgumentName := "multisetArgument"

def multisetSelfCall : Expr :=
  .app (.var multisetSelfName) (.var multisetArgumentName)

def multisetConsClause : Clause :=
  .mk (generalPP "cons" 2)
    (.tuple [.var multisetArgumentName, multisetSelfCall])
    [.mk .wild (.ctor "nil" [])]

def multisetJoinClause : Clause :=
  .mk (generalPP "join" 2)
    (.tuple [multisetSelfCall, multisetSelfCall])
    [.mk .wild (.ctor "nil" [])]

def multisetClauses : List Clause :=
  [nilClause, multisetConsClause, multisetJoinClause, catchClause]

def paperCompleteMultisetMatcher : Expr :=
  .fix multisetSelfName multisetArgumentName (.matcher multisetClauses)

/-- The deterministic fresh variables left in both closed W results. -/
def resultP : Cap := .var 1
def resultA : Ty := .var 4

def matcherTy : Ty :=
  .fn (.slot resultP resultA)
    (.matcher (.con "List" [resultP]) (.data "List" [resultA]))

/-! ## Executable W results -/

theorem listMatcher_inference_succeeds :
    Inference.inferenceSucceeds listSignature [] listMatcher = true := by
  native_decide

def listMatcherInferenceResult : Inference.ExprResult :=
  (Inference.infer listSignature [] listMatcher).get (by native_decide)

theorem listMatcherInferenceResult_success :
    Inference.infer listSignature [] listMatcher =
      some listMatcherInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem paperCompleteMultisetMatcher_inference_succeeds :
    Inference.inferenceSucceeds multisetSignature []
      paperCompleteMultisetMatcher = true := by
  native_decide

def paperCompleteMultisetInferenceResult : Inference.ExprResult :=
  (Inference.infer multisetSignature [] paperCompleteMultisetMatcher).get
    (by native_decide)

theorem paperCompleteMultisetInferenceResult_success :
    Inference.infer multisetSignature [] paperCompleteMultisetMatcher =
      some paperCompleteMultisetInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- Matcher finalization exports the structural producer variable into the
protected ledger in both recursive end-to-end examples. -/
theorem recursiveMatcher_final_producers_protected :
    ⟨1⟩ ∈ listMatcherInferenceResult.state.protectedCaps ∧
      ⟨1⟩ ∈ paperCompleteMultisetInferenceResult.state.protectedCaps := by
  native_decide

/-! ## Reconstructed typing from public inference success -/

theorem listMatcherInferenceResult_target :
    listMatcherInferenceResult.resolvedTarget = matcherTy := by
  native_decide

theorem paperCompleteMultisetInferenceResult_target :
    paperCompleteMultisetInferenceResult.resolvedTarget = matcherTy := by
  native_decide

theorem listMatcher_reconstructed :
    Inference.Reconstruction.ExprDeriv listSignature [] listMatcher
      matcherTy := by
  have derivation := Inference.infer_success_reconstruct
    listMatcherInferenceResult_success
  rw [listMatcherInferenceResult_target] at derivation
  simpa [Inference.ResolvedContext, Context.applySubst] using derivation

theorem paperCompleteMultisetMatcher_reconstructed :
    Inference.Reconstruction.ExprDeriv multisetSignature []
      paperCompleteMultisetMatcher matcherTy := by
  have derivation := Inference.infer_success_reconstruct
    paperCompleteMultisetInferenceResult_success
  rw [paperCompleteMultisetInferenceResult_target] at derivation
  simpa [Inference.ResolvedContext, Context.applySubst] using derivation

theorem listMatcher_typed :
    TypingInvariant listSignature [] listMatcher matcherTy :=
  listMatcher_reconstructed.toTypingInvariant

theorem paperCompleteMultisetMatcher_typed :
    TypingInvariant multisetSignature [] paperCompleteMultisetMatcher matcherTy :=
  paperCompleteMultisetMatcher_reconstructed.toTypingInvariant

/-! ## Flagship recursive-matcher use through an element slot -/

/--
The complete recursive `listMatcher` is applied to an inferred element slot,
then consumed by a nontrivial `matchAll`.  The constructor pattern binds both
the head and tail, and the body observes both bindings.
-/
def listMatcherMatchAll : Expr :=
  .lam "element"
    (.matchAll
      (.ctor "cons" [.lit 1, .ctor "nil" []])
      (.app listMatcher (.var "element"))
      (.pctor "cons" [.pvar "x", .pvar "rest"])
      (.tuple [.var "x", .var "rest"]))

/-- Exact terminal type, including the inferred element-slot capability. -/
def listMatcherMatchAllTy : Ty :=
  .fn (.slot (.var 4) .int)
    (.listT (.prod [.int, .data "List" [.int]]))

theorem listMatcherMatchAll_inference_succeeds :
    Inference.inferenceSucceeds listSignature [] listMatcherMatchAll = true := by
  native_decide

def listMatcherMatchAllInferenceResult : Inference.ExprResult :=
  (Inference.infer listSignature [] listMatcherMatchAll).get (by native_decide)

theorem listMatcherMatchAllInferenceResult_success :
    Inference.infer listSignature [] listMatcherMatchAll =
      some listMatcherMatchAllInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem listMatcherMatchAllInferenceResult_target :
    listMatcherMatchAllInferenceResult.resolvedTarget =
      listMatcherMatchAllTy := by
  native_decide

/-- Public certified inference reconstructs the complete typing invariant. -/
theorem listMatcherMatchAll_typed :
    TypingInvariant listSignature [] listMatcherMatchAll listMatcherMatchAllTy := by
  have typing := Inference.infer_success_typingInvariant
    listMatcherMatchAllInferenceResult_success
  rw [listMatcherMatchAllInferenceResult_target] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

/-- The same flagship success lands in the mutual coherent judgment, so the
coherent fragment is non-vacuous on a recursive-matcher program. -/
theorem listMatcherMatchAll_coherent :
    Coherent.CoherentExpr listSignature [] listMatcherMatchAll
      listMatcherMatchAllTy := by
  have typing := Coherent.infer_success_coherent
    listMatcherMatchAllInferenceResult_success
  rw [listMatcherMatchAllInferenceResult_target] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

/-! ## Deliberately incomplete multiset regression -/

def simplifiedMultisetClauses : List Clause :=
  [nilClause, consClause, catchClause]

def simplifiedMultisetMatcher : Expr :=
  .fix selfName argumentName (.matcher simplifiedMultisetClauses)

theorem simplifiedMultiset_directSelf :
    DirectSelf.Holds selfName (.matcher simplifiedMultisetClauses) := by
  native_decide

/-- The omitted general `join` clause fails the exact coverage obligation for
the expected List-family matcher capability. -/
theorem simplifiedMultiset_coverageCheck_fails :
    Inference.coverageCheck multisetSignature.toMatcherSig
      simplifiedMultisetClauses (.con "List" [resultP]) = false := by
  decide

theorem simplifiedMultiset_not_coverageOK :
    ¬ CoverageOK multisetSignature.toMatcherSig simplifiedMultisetClauses
      (.con "List" [resultP]) := by
  intro coverage
  have checked := Inference.coverageCheck_complete coverage
  rw [simplifiedMultiset_coverageCheck_fails] at checked
  contradiction

/-- The protected raw W traversal rejects the coverage-incomplete matcher. -/
theorem simplifiedMultisetMatcher_raw_inference_rejected :
    Inference.inferRaw multisetSignature [] simplifiedMultisetMatcher = none := by
  native_decide

/-- The public reconstruction-audited entry point rejects it as well. -/
theorem simplifiedMultisetMatcher_public_inference_rejected :
    Inference.infer multisetSignature [] simplifiedMultisetMatcher = none := by
  simp [Inference.infer,
    simplifiedMultisetMatcher_raw_inference_rejected]

theorem simplifiedMultisetMatcher_inference_fails :
    Inference.inferenceSucceeds multisetSignature [] simplifiedMultisetMatcher =
      false := by
  simp [Inference.inferenceSucceeds,
    simplifiedMultisetMatcher_public_inference_rejected]

end RecursiveExamples
end TypePM
