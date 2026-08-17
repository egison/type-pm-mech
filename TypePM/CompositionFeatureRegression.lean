import TypePM.GeneralMultisetExecutionRegression
import TypePM.PatternFunctionSafetyRegression

/-!
# Composed Egison-feature execution regression

This fixture exercises the general recursive multiset matcher, a nonlinear
value pattern, and a pattern-function expansion in one `matchAll`.  `join`
selects a singleton left part and `cons` selects an element from the remaining
right part.  `$x` binds the left integer and `#x` requires the right integer to
be equal.  Both selected tuple elements invoke the closed nullary `unit`
pattern function.  Equal values at distinct source positions therefore
produce two equal result values as two distinct search branches.

The public end-to-end positive uses the nullary definition because the
parameterized `pass` fixture intentionally lies outside public inference:
its shared value-flow capability binder cannot later be structurally
strengthened to `Any` under the variable-only rule.
-/

namespace TypePM
namespace CompositionFeatureRegression

/-- The general multiset signature extended with the closed `unit` pattern
function used inside each selected tuple element. -/
def signature : FrozenSig :=
  { GeneralMultisetExecutionRegression.signature with
    patternFuns := [("unit", PatternFunctionSafetyRegression.unitScheme)] }

@[simp] theorem find_unit :
    signature.findPatternFun "unit" =
      some PatternFunctionSafetyRegression.unitScheme := by
  rfl

/-- The nullary definition remains well typed after adding it to the general
multiset signature; its body and scheme have no ambient variables. -/
theorem unit_definition_typed (context : Context) :
    PatternDefTy signature context PatternFunctionSafetyRegression.unitDefinition
      PatternFunctionSafetyRegression.unitScheme := by
  refine @PatternDefTy.mk signature context
    PatternFunctionSafetyRegression.unitDefinition []
    PatternFunctionSafetyRegression.unitResult []
    PatternFunctionSafetyRegression.unitScheme Subst.id find_unit
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · rfl
  · simp [PatternDef.parameterNames,
      PatternFunctionSafetyRegression.unitDefinition]
  · intro capability member
    simp at member
  · simp
  · exact (PatternTy.tuple PatternTys.nil).resolve_id
  · rfl
  · exact DualScheme.ValueFlowEquivalent.refl
      PatternFunctionSafetyRegression.unitScheme

/-- All frozen-signature obligations, including closed schemes and the
multiset data/matcher interface, are discharged by the executable checker. -/
theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound (by decide) rfl

def runtimeSignature : RuntimeSigF :=
  [("unit", PatternFunctionSafetyRegression.unitDefinition.runtime)]

/-- The nonempty runtime table agrees with the source declaration in every
expression context, not only in the empty context used by the program. -/
theorem runtime_agrees (context : Context) :
    RuntimeSigAgrees signature context runtimeSignature where
  runtimeTyped := by
    intro entry member
    simp only [runtimeSignature, List.mem_singleton] at member
    subst entry
    exact ⟨PatternFunctionSafetyRegression.unitDefinition,
      PatternFunctionSafetyRegression.unitScheme, rfl,
      unit_definition_typed context⟩
  sourceLookup := by
    intro name scheme found
    by_cases unitName : name = "unit"
    · subst name
      have schemeEquality : scheme =
          PatternFunctionSafetyRegression.unitScheme :=
        (Option.some.inj (find_unit.symm.trans found)).symm
      subst scheme
      exact ⟨PatternFunctionSafetyRegression.unitDefinition, rfl, rfl,
        unit_definition_typed context⟩
    · have reverseName : "unit" ≠ name :=
        fun equality => unitName equality.symm
      simp [signature, FrozenSig.findPatternFun, reverseName] at found

theorem global_runtime_agreement :
    ∀ context, RuntimeSigAgrees signature context runtimeSignature :=
  runtime_agrees

/-- The erased nullary pattern-function body contains no free expression
variables. -/
theorem runtime_signature_scoped : RuntimeSigScoped runtimeSignature := by
  intro entry membership
  simp only [runtimeSignature, List.mem_singleton] at membership
  subst entry
  rfl

def nilE : Expr := .ctor "nil" []
def consE (head tail : Expr) : Expr := .ctor "cons" [head, tail]
def singletonE (value : Expr) : Expr := consE value nilE

def nilV : Value := .ctor "nil" []
def consV (head tail : Value) : Value := .ctor "cons" [head, tail]

def listE : List Expr → Expr
  | [] => nilE
  | head :: tail => consE head (listE tail)

def listV : List Value → Value
  | [] => nilV
  | head :: tail => consV head (listV tail)

def tupleElementE (number : Int) : Expr :=
  .tuple [.lit number, .tuple []]

def tupleElementV (number : Int) : Value :=
  .tuple [.lit number, .tuple []]

/-- The element matcher exposes both fields of `(Int, ())`.  Its second field
is matched by the tuple matcher needed by the `unit` pattern function. -/
def elementTupleClause : Clause :=
  .mk (.tuple [.hole, .hole]) (.tuple [.something, .tuple []])
    [.mk (.tuple [.var "number", .var "unitValue"])
      (singletonE (.tuple [.var "number", .var "unitValue"])),
      .mk .wild nilE]

def elementCatchClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole") (singletonE (.var "whole"))]

def elementMatcher : Expr :=
  .matcher [elementTupleClause, elementCatchClause]

/-- The general multiset function is instantiated with the tuple element
matcher, rather than with `something`. -/
def matcher : Expr :=
  .app GeneralMultisetExecutionRegression.matcherFunction elementMatcher

def firstElement : Pattern :=
  .ptuple [.pvar "x", .papp "unit" []]

def equalElement : Pattern :=
  .ptuple [.pval (.var "x"), .papp "unit" []]

/-- `join` first selects a singleton left part.  Recursive `cons` matching
binds its integer as `x`; a second recursive `cons` on the right part must
select an equal integer through `#x`.  Both selected elements invoke `unit`. -/
def pattern : Pattern :=
  .pctor "join"
    [.pctor "cons" [firstElement, .pctor "nil" []],
      .pctor "cons" [equalElement, .pvar "rest"]]

def target : Expr :=
  listE [tupleElementE 1, tupleElementE 1, tupleElementE 2]

def unequalTarget : Expr :=
  listE [tupleElementE 1, tupleElementE 2, tupleElementE 3]

def programFor (subject : Expr) : Expr :=
  .matchAll subject matcher pattern (.tuple [.var "x", .var "rest"])

def program : Expr := programFor target
def unequalProgram : Expr := programFor unequalTarget

/-- The two `1` occurrences create distinct branches even though their result
values are equal.  The unmatched `2` remains on the right in both branches. -/
def expected : Value :=
  mkListV
    [.tuple [.lit 1, listV [tupleElementV 2]],
      .tuple [.lit 1, listV [tupleElementV 2]]]

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] program).get (by native_decide)

theorem inference_success :
    Inference.infer signature [] program = some inferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def resultTy : Ty :=
  .listT (.prod [.int, .listT (.prod [.int, .prod []])])

theorem inference_result_type :
    inferenceResult.resolvedTarget = resultTy := by
  native_decide

theorem source_typed : SourceTyping signature [] program resultTy := by
  have typing := Inference.infer_success_sourceTyping inference_success
  rw [inference_result_type] at typing
  exact typing

/-- A single exact run covers `join`, recursive `cons`, nonlinear equality,
two pattern-function expansions per successful branch, and result collection. -/
theorem program_runs :
    evalFuel runtimeSignature 100 [] program = .ok expected := by
  rfl

theorem program_runs_relationally :
    Eval runtimeSignature [] program expected :=
  evalFuel_ok program_runs

@[simp] theorem program_freeVars : program.freeVars = [] := by
  native_decide

/-- Public source typing and nonempty runtime agreement rule out `stuck` for
every fuel, including fuels too small to finish the search. -/
theorem program_never_stuck (fuel : Nat) :
    evalFuel runtimeSignature fuel [] program ≠ .stuck := by
  exact typed_never_stuck_runtime signature_wf global_runtime_agreement
    runtime_signature_scoped
    (source_typed.typingInvariant signature_wf.schemesClosed)
    program_freeVars fuel

/-! ## Nonlinear mismatch under the same composition -/

def unequalInferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] unequalProgram).get (by native_decide)

theorem unequal_inference_success :
    Inference.infer signature [] unequalProgram =
      some unequalInferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem unequal_inference_result_type :
    unequalInferenceResult.resolvedTarget = resultTy := by
  native_decide

theorem unequal_source_typed :
    SourceTyping signature [] unequalProgram resultTy := by
  have typing :=
    Inference.infer_success_sourceTyping unequal_inference_success
  rw [unequal_inference_result_type] at typing
  exact typing

/-- With no duplicate integer, every branch fails normally at `#x`; this is
an empty result rather than evaluator `stuck`. -/
theorem unequal_program_runs :
    evalFuel runtimeSignature 100 [] unequalProgram = .ok (mkListV []) := by
  rfl

theorem unequal_program_runs_relationally :
    Eval runtimeSignature [] unequalProgram (mkListV []) :=
  evalFuel_ok unequal_program_runs

@[simp] theorem unequal_program_freeVars :
    unequalProgram.freeVars = [] := by
  native_decide

theorem unequal_program_never_stuck (fuel : Nat) :
    evalFuel runtimeSignature fuel [] unequalProgram ≠ .stuck := by
  exact typed_never_stuck_runtime signature_wf global_runtime_agreement
    runtime_signature_scoped
    (unequal_source_typed.typingInvariant signature_wf.schemesClosed)
    unequal_program_freeVars fuel

end CompositionFeatureRegression
end TypePM
