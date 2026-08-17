import TypePM.DynamicDispatchRegression
import TypePM.InterpreterAdequacy
import TypePM.InterpreterDispatchBridge
import TypePM.DemandTypingInferenceSoundnessPublic

/-!
# Executable Egison-feature regressions

The metatheory proves safety for every expression accepted by `SourceTyping`.
These concrete regressions check a different obligation: that the executable
model gives the intended Egison behavior to representative programs.  The
primary fixtures cross public inference, reconstruction of `SourceTyping`,
exact fuel-indexed evaluation, adequacy, and the all-fuel no-stuck theorem.
An auxiliary singleton fixture also checks the actual recursive `List`
representation at the operational boundary.

The multiset fixture is deliberately finite: its matcher enumerates both
choices from a two-element collection.  It validates nondeterministic search
and result collection without claiming that this one clause implements the
general recursive multiset matcher.
-/

namespace TypePM
namespace FeatureExecutionRegression

namespace NonLinear

abbrev signature : FrozenSig :=
  DynamicDispatchRegression.TypedFixture.signature

abbrev matcherExpression : Expr :=
  DynamicDispatchRegression.TypedFixture.matcherExpression

def equalTarget : Expr := .ctor "pair" [.lit 1, .lit 1]
def unequalTarget : Expr := .ctor "pair" [.lit 1, .lit 2]

/-- `$x` binds the first field; `#x` compares the second field with it. -/
def pattern : Pattern :=
  .pctor "pair" [.pvar "x", .pval (.var "x")]

def equalProgram : Expr :=
  .matchAll equalTarget matcherExpression pattern (.var "x")

def unequalProgram : Expr :=
  .matchAll unequalTarget matcherExpression pattern (.var "x")

def equalExpected : Value := mkListV [.lit 1]
def unequalExpected : Value := mkListV []

/-- Equal repeated occurrences produce one result. -/
theorem equal_program_runs :
    evalFuel [] 30 [] equalProgram = .ok equalExpected := by
  rfl

/-- A different second occurrence is a normal match failure, not `stuck`. -/
theorem unequal_program_runs :
    evalFuel [] 30 [] unequalProgram = .ok unequalExpected := by
  rfl

def equalInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] equalProgram).get (by native_decide)

def unequalInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] unequalProgram).get (by native_decide)

theorem equal_inference_success :
    Inference.infer signature [] equalProgram = some equalInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem unequal_inference_success :
    Inference.infer signature [] unequalProgram = some unequalInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def resultTy : Ty := .listT .int

theorem equal_inference_result_type :
    equalInferenceResult.resolvedTarget = resultTy := by
  native_decide

theorem unequal_inference_result_type :
    unequalInferenceResult.resolvedTarget = resultTy := by
  native_decide

theorem equal_source_typed :
    SourceTyping signature [] equalProgram resultTy := by
  have typing := Inference.infer_success_sourceTyping equal_inference_success
  rw [equal_inference_result_type] at typing
  exact typing

theorem unequal_source_typed :
    SourceTyping signature [] unequalProgram resultTy := by
  have typing := Inference.infer_success_sourceTyping unequal_inference_success
  rw [unequal_inference_result_type] at typing
  exact typing

theorem equal_program_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] equalProgram ≠ .stuck :=
  SourceTyping.never_stuck_paper1
    DynamicDispatchRegression.TypedFixture.signature_wf rfl
    equal_source_typed (by native_decide) fuel

theorem unequal_program_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] unequalProgram ≠ .stuck :=
  SourceTyping.never_stuck_paper1
    DynamicDispatchRegression.TypedFixture.signature_wf rfl
    unequal_source_typed (by native_decide) fuel

/-- Adequacy turns the successful executable run into relational evaluation. -/
theorem equal_program_runs_relationally :
    Eval [] [] equalProgram equalExpected :=
  evalFuel_ok equal_program_runs

theorem unequal_program_runs_relationally :
    Eval [] [] unequalProgram unequalExpected :=
  evalFuel_ok unequal_program_runs

end NonLinear

namespace Multiset

/-! ## Actual `List` representation: the singleton boundary -/

/-- The existing `cons` matcher extracts the only element and the empty
residue from a singleton `List`. -/
theorem singleton_program_runs :
    evalFuel [] 30 [] DynamicDispatchRegression.program =
      .ok DynamicDispatchRegression.decompositionValue := by
  rfl

theorem singleton_program_runs_relationally :
    Eval [] [] DynamicDispatchRegression.program
      DynamicDispatchRegression.decompositionValue :=
  evalFuel_ok singleton_program_runs

/-! ## Two choices from a finite two-element carrier -/

abbrev signature : FrozenSig :=
  DynamicDispatchRegression.TypedFixture.signature

def nilExpression : Expr := .ctor "nil" []
def target : Expr := .ctor "pair" [.lit 1, .lit 2]

def emptyClause : Clause :=
  DynamicDispatchRegression.TypedFixture.emptyClause

def twoElementDataPattern : DPat :=
  .ctor "pair" [.var "first", .var "second"]

/-- Both possible selected-element/residue decompositions. -/
def twoChoices : Expr :=
  .ctor "cons"
    [.tuple [.var "first", .var "second"],
      .ctor "cons"
        [.tuple [.var "second", .var "first"], nilExpression]]

def choiceClause : Clause :=
  .mk (generalPP "pair" 2) (.tuple [.something, .something])
    [.mk twoElementDataPattern twoChoices,
      .mk .wild nilExpression]

def catchClause : Clause :=
  DynamicDispatchRegression.TypedFixture.catchAllClause

/-- A two-element `Pair` is the finite carrier.  The matcher, rather than the
carrier constructor, supplies multiset behavior by returning both choices. -/
def matcherExpression : Expr :=
  .matcher [emptyClause, choiceClause, catchClause]

def pattern : Pattern :=
  .pctor "pair" [.pvar "selected", .pvar "residue"]

def program : Expr :=
  .matchAll target matcherExpression pattern
    (.tuple [.var "selected", .var "residue"])

def expected : Value :=
  mkListV
    [.tuple [.lit 1, .lit 2],
      .tuple [.lit 2, .lit 1]]

/-- Matching the two-element carrier enumerates both multiset choices. -/
theorem program_runs :
    evalFuel [] 40 [] program = .ok expected := by
  rfl

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] program).get (by native_decide)

theorem inference_success :
    Inference.infer signature [] program = some inferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def resultTy : Ty :=
  .listT (.prod [.int, .int])

theorem inference_result_type :
    inferenceResult.resolvedTarget = resultTy := by
  native_decide

theorem source_typed :
    SourceTyping signature [] program resultTy := by
  have typing := Inference.infer_success_sourceTyping inference_success
  rw [inference_result_type] at typing
  exact typing

theorem program_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] program ≠ .stuck :=
  SourceTyping.never_stuck_paper1
    DynamicDispatchRegression.TypedFixture.signature_wf rfl
    source_typed (by native_decide) fuel

/-- Adequacy independently replays the concrete interpreter result. -/
theorem program_runs_relationally :
    Eval [] [] program expected :=
  evalFuel_ok program_runs

end Multiset

end FeatureExecutionRegression
end TypePM
