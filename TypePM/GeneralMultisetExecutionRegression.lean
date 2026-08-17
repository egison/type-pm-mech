import TypePM.InterpreterAdequacy
import TypePM.InterpreterDispatchBridge
import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.RecursiveExamples

/-!
# General recursive multiset-matcher execution regression

This fixture gives `nil`, `cons`, and `join` an executable meaning over the
ordinary `List` representation.  The matcher definition is recursive and is
not specialized to an input length.  Concrete runs fix the current
depth-first, left-to-right result order and show that equal values at distinct
occurrences remain distinct branches.

The generic matcher function is checked at the expected
`MatcherSlot κ α -> Matcher [κ] [α]` type.  Its closed applications use
`.something` as the executable element matcher.
-/

namespace TypePM
namespace GeneralMultisetExecutionRegression

/-- The recursive multiset signature adds the two primitives used by the
operational clauses.  `submultisetSplits` enumerates all bipartitions by
occurrence; unlike `splits`, it is not restricted to consecutive prefixes. -/
def signature : FrozenSig :=
  { RecursiveExamples.multisetSignature with
    primitives :=
      [(.append, appendCanonicalScheme),
        (.submultisetSplits, splitsCanonicalScheme)] }

theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound (by decide) rfl

def nilE : Expr := .ctor "nil" []
def consE (head tail : Expr) : Expr := .ctor "cons" [head, tail]
def singletonE (value : Expr) : Expr := consE value nilE
def appendE (left right : Expr) : Expr := .prim .append [left, right]

def selfName := "multisetSelf"
def argumentName := "elementMatcher"
def headName := "head"
def tailName := "tail"
def selectedName := "selected"
def residueName := "residue"
def leftName := "left"
def rightName := "right"

def selfCall : Expr := .app (.var selfName) (.var argumentName)

def nilClause : Clause :=
  .mk (generalPP "nil" 0) (.tuple [])
    [.mk (.ctor "nil" []) (singletonE (.tuple [])),
      .mk .wild nilE]

def recursiveConsChoices : Expr :=
  .matchAll (.var tailName) selfCall
    (.pctor "cons" [.pvar selectedName, .pvar residueName])
    (.tuple
      [.var selectedName,
        consE (.var headName) (.var residueName)])

def directConsChoice : Expr :=
  singletonE (.tuple [.var headName, .var tailName])

def consChoices : Expr :=
  appendE directConsChoice recursiveConsChoices

def consClause : Clause :=
  .mk (generalPP "cons" 2)
    (.tuple [.var argumentName, selfCall])
    [.mk (.ctor "nil" []) nilE,
      .mk (.ctor "cons" [.var headName, .var tailName]) consChoices,
      .mk .wild nilE]

def joinPattern : Pattern :=
  .pctor "join" [.pvar leftName, .pvar rightName]

def joinClause : Clause :=
  .mk (generalPP "join" 2)
    (.tuple [selfCall, selfCall])
    [.mk (.var "joinTarget")
      (.prim .submultisetSplits [.var "joinTarget"])]

def catchClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole") (singletonE (.var "whole"))]

def clauses : List Clause :=
  [nilClause, consClause, joinClause, catchClause]

def matcherFunction : Expr :=
  .fix selfName argumentName (.matcher clauses)

def matcher : Expr := .app matcherFunction .something

def listE : List Int → Expr
  | [] => nilE
  | head :: tail => consE (.lit head) (listE tail)

def listV : List Int → Value
  | [] => .ctor "nil" []
  | head :: tail => .ctor "cons" [.lit head, listV tail]

def nilProgram (elements : List Int) : Expr :=
  .matchAll (listE elements) matcher (.pctor "nil" []) (.lit 0)

def consPattern : Pattern :=
  .pctor "cons" [.pvar selectedName, .pvar residueName]

def consProgram (elements : List Int) : Expr :=
  .matchAll (listE elements) matcher consPattern
    (.tuple [.var selectedName, .var residueName])

def nestedConsProgram (elements : List Int) : Expr :=
  .matchAll (listE elements) matcher
    (.pctor "cons"
      [.pvar "first",
        .pctor "cons" [.pvar "second", .pvar "rest"]])
    (.tuple [.var "first", .var "second", .var "rest"])

def joinProgram (elements : List Int) : Expr :=
  .matchAll (listE elements) matcher joinPattern
    (.tuple [.var leftName, .var rightName])

def consExpected (choices : List (Int × List Int)) : Value :=
  mkListV (choices.map fun choice =>
    .tuple [.lit choice.1, listV choice.2])

def nestedConsExpected (choices : List (Int × Int × List Int)) : Value :=
  mkListV (choices.map fun choice =>
    .tuple [.lit choice.1, .lit choice.2.1, listV choice.2.2])

def joinExpected (choices : List (List Int × List Int)) : Value :=
  mkListV (choices.map fun choice =>
    .tuple [listV choice.1, listV choice.2])

/-! ## Public typing and safety of the length-independent definition -/

def matcherInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] matcherFunction).get (by native_decide)

theorem matcher_inference_success :
    Inference.infer signature [] matcherFunction =
      some matcherInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- Deterministic fresh identifiers aside, this is
`MatcherSlot κ α -> Matcher [κ] [α]`. -/
def matcherFunctionTy : Ty :=
  .fn (.slot (.var 1) (.var 30))
    (.matcher (.con "List" [.var 1]) (.data "List" [.var 30]))

theorem matcher_inference_result_type :
    matcherInferenceResult.resolvedTarget = matcherFunctionTy := by
  native_decide

theorem matcher_source_typed :
    SourceTyping signature [] matcherFunction matcherFunctionTy := by
  have typing := Inference.infer_success_sourceTyping matcher_inference_success
  rw [matcher_inference_result_type] at typing
  exact typing

theorem matcher_function_runs :
    evalFuel [] 1 [] matcherFunction =
      .ok (selfClosure selfName [] argumentName (.matcher clauses)) := by
  rfl

theorem matcher_function_runs_relationally :
    Eval [] [] matcherFunction
      (selfClosure selfName [] argumentName (.matcher clauses)) :=
  evalFuel_ok matcher_function_runs

theorem matcher_function_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] matcherFunction ≠ .stuck :=
  SourceTyping.never_stuck_paper1 signature_wf rfl matcher_source_typed
    (by decide) fuel

def ownershipProbeState : Inference.InferState :=
  let first := (Inference.InferState.empty.freshCap
    (Inference.freshOrigin .matcherClause [] "borrowed-probe")).2
  (first.freshCap
    (Inference.freshOrigin .matcherClause [] "owned-result-probe")).2

def ownershipProbeFinal : Inference.InferState :=
  ownershipProbeState.protectMatcherCapabilityExcept
    (.prod [.var 0, .var 1]) [0]

/-- Selective finalization leaves the slot-demand representative flexible but
still freezes a distinct matcher-owned result leaf. -/
theorem matcher_owned_result_leaf_remains_frozen :
    ⟨0⟩ ∉ ownershipProbeFinal.protectedCaps ∧
      ⟨1⟩ ∈ ownershipProbeFinal.protectedCaps ∧
      ownershipProbeFinal.capabilityOrigins.originOf ⟨0⟩ =
        .structuralFlexible ∧
      ownershipProbeFinal.capabilityOrigins.originOf ⟨1⟩ = .renameOnly := by
  decide

/-- Public inference accepts a closed use of the recursive `cons` clause. -/
def consThreeInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] (consProgram [1, 2, 3])).get
    (by native_decide)

theorem cons_three_inference_success :
    Inference.infer signature [] (consProgram [1, 2, 3]) =
      some consThreeInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def consThreeResultTy : Ty :=
  .listT (.prod [.int, .listT .int])

theorem cons_three_inference_result_type :
    consThreeInferenceResult.resolvedTarget = consThreeResultTy := by
  native_decide

theorem cons_three_source_typed :
    SourceTyping signature [] (consProgram [1, 2, 3]) consThreeResultTy := by
  have typing :=
    Inference.infer_success_sourceTyping cons_three_inference_success
  rw [cons_three_inference_result_type] at typing
  exact typing

theorem cons_three_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] (consProgram [1, 2, 3]) ≠ .stuck :=
  SourceTyping.never_stuck_paper1 signature_wf rfl cons_three_source_typed
    (by decide) fuel

/-- Nested recursive `cons` use crosses the same public typing boundary. -/
def nestedConsThreeInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] (nestedConsProgram [1, 2, 3])).get
    (by native_decide)

theorem nested_cons_three_inference_success :
    Inference.infer signature [] (nestedConsProgram [1, 2, 3]) =
      some nestedConsThreeInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def nestedConsThreeResultTy : Ty :=
  .listT (.prod [.int, .int, .listT .int])

theorem nested_cons_three_inference_result_type :
    nestedConsThreeInferenceResult.resolvedTarget =
      nestedConsThreeResultTy := by
  native_decide

theorem nested_cons_three_source_typed :
    SourceTyping signature [] (nestedConsProgram [1, 2, 3])
      nestedConsThreeResultTy := by
  have typing :=
    Inference.infer_success_sourceTyping nested_cons_three_inference_success
  rw [nested_cons_three_inference_result_type] at typing
  exact typing

theorem nested_cons_three_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] (nestedConsProgram [1, 2, 3]) ≠ .stuck :=
  SourceTyping.never_stuck_paper1 signature_wf rfl
    nested_cons_three_source_typed (by decide) fuel

/-- The public boundary also accepts the recursive `join` clause. -/
def joinThreeInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] (joinProgram [1, 2, 3])).get
    (by native_decide)

theorem join_three_inference_success :
    Inference.infer signature [] (joinProgram [1, 2, 3]) =
      some joinThreeInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def joinThreeResultTy : Ty :=
  .listT (.prod [.listT .int, .listT .int])

theorem join_three_inference_result_type :
    joinThreeInferenceResult.resolvedTarget = joinThreeResultTy := by
  native_decide

theorem join_three_source_typed :
    SourceTyping signature [] (joinProgram [1, 2, 3]) joinThreeResultTy := by
  have typing :=
    Inference.infer_success_sourceTyping join_three_inference_success
  rw [join_three_inference_result_type] at typing
  exact typing

theorem join_three_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] (joinProgram [1, 2, 3]) ≠ .stuck :=
  SourceTyping.never_stuck_paper1 signature_wf rfl join_three_source_typed
    (by decide) fuel

/-! ## Exact operational matrix -/

theorem nil_empty_runs :
    evalFuel [] 160 [] (nilProgram []) = .ok (mkListV [.lit 0]) := by
  rfl

theorem nil_nonempty_fails_normally :
    evalFuel [] 180 [] (nilProgram [1]) = .ok (mkListV []) := by
  rfl

theorem cons_empty_fails_normally :
    evalFuel [] 180 [] (consProgram []) = .ok (consExpected []) := by
  rfl

theorem cons_singleton_runs :
    evalFuel [] 200 [] (consProgram [7]) =
      .ok (consExpected [(7, [])]) := by
  rfl

theorem cons_three_runs_in_search_order :
    evalFuel [] 320 [] (consProgram [1, 2, 3]) =
      .ok (consExpected [(1, [2, 3]), (2, [1, 3]), (3, [1, 2])]) := by
  rfl

theorem cons_duplicates_preserve_occurrence_branches :
    evalFuel [] 300 [] (consProgram [1, 1, 2]) =
      .ok (consExpected
        [(1, [1, 2]), (1, [1, 2]), (2, [1, 1])]) := by
  rfl

theorem nested_cons_runs_in_depth_first_order :
    evalFuel [] 420 [] (nestedConsProgram [1, 2, 3]) =
      .ok (nestedConsExpected
        [(1, 2, [3]), (1, 3, [2]),
          (2, 1, [3]), (2, 3, [1]),
          (3, 1, [2]), (3, 2, [1])]) := by
  rfl

theorem join_empty_runs :
    evalFuel [] 180 [] (joinProgram []) =
      .ok (joinExpected [([], [])]) := by
  rfl

theorem join_singleton_runs :
    evalFuel [] 220 [] (joinProgram [7]) =
      .ok (joinExpected [([], [7]), ([7], [])]) := by
  rfl

theorem join_three_runs_in_submultiset_order :
    evalFuel [] 420 [] (joinProgram [1, 2, 3]) =
      .ok (joinExpected
        [([], [1, 2, 3]),
          ([1], [2, 3]), ([2], [1, 3]), ([3], [1, 2]),
          ([1, 2], [3]), ([1, 3], [2]), ([2, 3], [1]),
          ([1, 2, 3], [])]) := by
  rfl

theorem join_duplicates_preserve_occurrence_branches :
    evalFuel [] 300 [] (joinProgram [1, 1]) =
      .ok (joinExpected
        [([], [1, 1]), ([1], [1]), ([1], [1]), ([1, 1], [])]) := by
  rfl

/-! Exact interpreter results imply the corresponding relational evaluations. -/

theorem cons_three_runs_relationally :
    Eval [] [] (consProgram [1, 2, 3])
      (consExpected [(1, [2, 3]), (2, [1, 3]), (3, [1, 2])]) :=
  evalFuel_ok cons_three_runs_in_search_order

theorem nested_cons_runs_relationally :
    Eval [] [] (nestedConsProgram [1, 2, 3])
      (nestedConsExpected
        [(1, 2, [3]), (1, 3, [2]),
          (2, 1, [3]), (2, 3, [1]),
          (3, 1, [2]), (3, 2, [1])]) :=
  evalFuel_ok nested_cons_runs_in_depth_first_order

theorem join_three_runs_relationally :
    Eval [] [] (joinProgram [1, 2, 3])
      (joinExpected
        [([], [1, 2, 3]),
          ([1], [2, 3]), ([2], [1, 3]), ([3], [1, 2]),
          ([1, 2], [3]), ([1, 3], [2]), ([2, 3], [1]),
          ([1, 2, 3], [])]) :=
  evalFuel_ok join_three_runs_in_submultiset_order

end GeneralMultisetExecutionRegression
end TypePM
