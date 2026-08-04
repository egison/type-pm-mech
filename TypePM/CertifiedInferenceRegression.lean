import TypePM.CertifiedInference

/-!
# Certified executable-inference regressions

These examples exercise the public, terminally certified inference entry
point at the boundaries that require more than local unification: terminal
specialization after `let`, quantified expression and pattern-function
instantiation, slot-to-slot checking, and specialization of a finalized
matcher literal by an enclosing `matchAll`.
-/

namespace TypePM
namespace CertifiedInferenceRegression

def emptySignature : FrozenSig where
  observability := fun _ => none
  dataCtors := []
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

theorem option_eq_some_get_of_isSome {α : Type} (value : Option α)
    (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => simp at present
  | some result => rfl

/-! ## A generalized `let` whose ambient lambda variable is solved later -/

def terminalLetExpression : Expr :=
  .lam "x" (.letE "y" (.var "x") (.app (.var "y") (.lit 1)))

theorem terminalLet_inference_succeeds :
    Inference.inferenceSucceeds emptySignature [] terminalLetExpression = true := by
  native_decide

def terminalLetResult : Inference.ExprResult :=
  (Inference.infer emptySignature [] terminalLetExpression).get (by
    native_decide)

theorem terminalLetResult_success :
    Inference.infer emptySignature [] terminalLetExpression =
      some terminalLetResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

theorem terminalLet_typed :
    HasTy emptySignature
      (Inference.ResolvedContext terminalLetResult.state.prevailing [])
      terminalLetExpression terminalLetResult.resolvedTarget :=
  Inference.infer_success_sound terminalLetResult_success

/-! ## Expression-scheme instantiation in both variable sorts -/

def quantifiedProducerScheme : Scheme where
  capBinders := [0]
  tyBinders := [0]
  body := .matcher (.var 0) (.var 0)

def quantifiedContext : Context :=
  [("producer", quantifiedProducerScheme)]

def quantifiedExpression : Expr :=
  .var "producer"

theorem quantifiedScheme_inference_succeeds :
    Inference.inferenceSucceeds emptySignature quantifiedContext
      quantifiedExpression = true := by
  native_decide

def quantifiedSchemeResult : Inference.ExprResult :=
  (Inference.infer emptySignature quantifiedContext quantifiedExpression).get
    (by native_decide)

theorem quantifiedSchemeResult_success :
    Inference.infer emptySignature quantifiedContext quantifiedExpression =
      some quantifiedSchemeResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

theorem quantifiedScheme_typed :
    HasTy emptySignature
      (Inference.ResolvedContext quantifiedSchemeResult.state.prevailing
        quantifiedContext)
      quantifiedExpression quantifiedSchemeResult.resolvedTarget :=
  Inference.infer_success_sound quantifiedSchemeResult_success

/-! ## Pattern-function instantiation in both variable sorts -/

def quantifiedPatternFunction : DualScheme where
  capBinders := [0]
  tyBinders := [0]
  args := [⟨.var 0, .var 0⟩]
  result := ⟨.none, .var 0⟩

def patternFunctionSignature : FrozenSig :=
  { emptySignature with
    patternFuns := [("quantified", quantifiedPatternFunction)] }

def quantifiedPAppExpression : Expr :=
  .matchAll (.lit 0) .something (.papp "quantified" [.wild]) (.lit 1)

theorem quantifiedPApp_inference_succeeds :
    Inference.inferenceSucceeds patternFunctionSignature []
      quantifiedPAppExpression = true := by
  native_decide

def quantifiedPAppResult : Inference.ExprResult :=
  (Inference.infer patternFunctionSignature [] quantifiedPAppExpression).get
    (by native_decide)

theorem quantifiedPAppResult_success :
    Inference.infer patternFunctionSignature [] quantifiedPAppExpression =
      some quantifiedPAppResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

theorem quantifiedPApp_typed :
    HasTy patternFunctionSignature
      (Inference.ResolvedContext quantifiedPAppResult.state.prevailing [])
      quantifiedPAppExpression quantifiedPAppResult.resolvedTarget :=
  Inference.infer_success_sound quantifiedPAppResult_success

/-! ## Slot-to-slot expected-type alignment -/

def slotContext : Context :=
  [("slot", Scheme.mono (.slot .none .int))]

def slotToSlotExpression : Expr :=
  .matchAll (.lit 0) (.var "slot") .wild (.lit 1)

theorem slotToSlot_inference_succeeds :
    Inference.inferenceSucceeds emptySignature slotContext
      slotToSlotExpression = true := by
  native_decide

def slotToSlotResult : Inference.ExprResult :=
  (Inference.infer emptySignature slotContext slotToSlotExpression).get
    (by native_decide)

theorem slotToSlotResult_success :
    Inference.infer emptySignature slotContext slotToSlotExpression =
      some slotToSlotResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

def isSlotToSlotEvent : Inference.TraceEvent → Bool
  | .slotAlignment _ _ (.slot _ _) (.slot _ _) => true
  | _ => false

/-- The expected-type boundary really took the slot-to-slot branch. -/
theorem slotToSlot_alignment_recorded :
    slotToSlotResult.state.trace.events.any isSlotToSlotEvent = true := by
  native_decide

theorem slotToSlot_typed :
    HasTy emptySignature
      (Inference.ResolvedContext slotToSlotResult.state.prevailing slotContext)
      slotToSlotExpression slotToSlotResult.resolvedTarget :=
  Inference.infer_success_sound slotToSlotResult_success

/-! ## Finalized matcher target specialized by an enclosing use -/

def nilScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := []
  result := .data "List" [.var 0]

def matcherSignature : FrozenSig :=
  { emptySignature with dataCtors := [("nil", nilScheme)] }

def catchAllClause : Clause :=
  .mk .hole .something [.mk (.var "whole") (.ctor "nil" [])]

def specializedMatcherExpression : Expr :=
  .matchAll (.lit 0) (.matcher [catchAllClause]) .wild (.lit 1)

theorem specializedMatcher_inference_succeeds :
    Inference.inferenceSucceeds matcherSignature []
      specializedMatcherExpression = true := by
  native_decide

def specializedMatcherResult : Inference.ExprResult :=
  (Inference.infer matcherSignature [] specializedMatcherExpression).get
    (by native_decide)

theorem specializedMatcherResult_success :
    Inference.infer matcherSignature [] specializedMatcherExpression =
      some specializedMatcherResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

def isMatcherTargetSpecializedToInt
    (state : Inference.InferState) : Inference.TraceEvent → Bool
  | .matcherFinalization _ _ rawTarget _ localTarget _ _ _ =>
      match localTarget with
      | .var _ => decide (state.prevailing.apply rawTarget = .int)
      | _ => false
  | _ => false

/-- At matcher finalization the target is still a meta-variable, whereas the
terminal substitution maps that same raw target to `Int` after `matchAll`
checks the enclosing target expression. -/
theorem matcherTarget_specialized_after_finalization :
    specializedMatcherResult.state.trace.events.any
      (isMatcherTargetSpecializedToInt specializedMatcherResult.state) = true := by
  native_decide

theorem specializedMatcher_typed :
    HasTy matcherSignature
      (Inference.ResolvedContext specializedMatcherResult.state.prevailing [])
      specializedMatcherExpression specializedMatcherResult.resolvedTarget :=
  Inference.infer_success_sound specializedMatcherResult_success

end CertifiedInferenceRegression
end TypePM
