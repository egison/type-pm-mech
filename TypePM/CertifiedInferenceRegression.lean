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

/-! ## Unary product-matcher selection at a use site -/

def concretePairProductType : Ty :=
  .prod [.matcher .any .int, .matcher .any .int]

def concretePairMatcherType : Ty :=
  .matcher (.prod [.any, .any]) (.prod [.int, .int])

def concretePairSlotType : Ty :=
  .slot (.prod [.any, .any]) (.prod [.int, .int])

/-- A matcher expectation is not a coercion demand: the selector leaves the
raw product untouched, so only the ordinary alignment of a raw matcher can
succeed at a matcher-headed use site. -/
theorem productMatcher_expected_source
    (state : Inference.InferState) :
    Inference.expectedCoercionSource state concretePairProductType
      concretePairMatcherType = concretePairProductType := by
  simp [Inference.expectedCoercionSource, Inference.productMatcherDuals?,
    Inference.productSlotDuals?, Inference.matcherDual?, Inference.slotDual?,
    concretePairProductType, concretePairMatcherType]

/-- A slot expectation presents the lifted matcher to the existing
matcher-to-slot alignment path. -/
theorem productMatcher_slot_source
    (state : Inference.InferState) :
    Inference.expectedCoercionSource state concretePairProductType
      concretePairSlotType = concretePairMatcherType := by
  simp [Inference.expectedCoercionSource, Inference.productMatcherDuals?,
    Inference.productSlotDuals?, Inference.matcherDual?,
    Inference.productMatcherTarget,
    concretePairProductType, concretePairMatcherType, concretePairSlotType]

def concretePairOfSlotsType : Ty :=
  .prod [.slot .any .int, .slot .any .int]

/-- A product whose components are already slots selects the unary slot-tuple
lift when the aggregate slot is expected. -/
theorem productSlot_slot_source
    (state : Inference.InferState) :
    Inference.expectedCoercionSource state concretePairOfSlotsType
      concretePairSlotType = concretePairSlotType := by
  simp [Inference.expectedCoercionSource, Inference.productMatcherDuals?,
    Inference.productSlotDuals?, Inference.matcherDual?, Inference.slotDual?,
    Inference.slotTupleTarget, concretePairOfSlotsType, concretePairSlotType]

/-- Both component recognizers accept the empty product.  The executable
selector resolves that overlap by choosing the matcher-product branch. -/
theorem emptyProduct_prefers_productMatcher
    (state : Inference.InferState) :
    Inference.expectedCoercionSource state (.prod [])
      (.slot (.prod []) (.prod [])) =
        .matcher (.prod []) (.prod []) := by
  simp [Inference.expectedCoercionSource, Inference.productMatcherDuals?,
    Inference.productSlotDuals?, Inference.productMatcherTarget]

/-! ## Domain-directed application checking -/

/-- Check both the terminal type and the exact expected-type alignment
observed in a successful public run. -/
def inferenceHasAlignment
    (context : Context) (expression : Expr)
    (inferred requested resultTarget : Ty) : Bool :=
  match Inference.infer emptySignature context expression with
  | none => false
  | some result =>
      decide (result.resolvedTarget = resultTarget) &&
        result.state.trace.events.any fun
          | .slotAlignment _ _ actualInferred actualRequested =>
              decide (result.state.prevailing.apply actualInferred = inferred) &&
                decide (result.state.prevailing.apply actualRequested = requested)
          | _ => false

def productMatcherConsumerContext : Context :=
  [("consume", Scheme.mono (.fn concretePairMatcherType .int))]

def productMatcherArgumentApplication : Expr :=
  .app (.var "consume") (.tuple [.something, .something])

/-- A matcher-headed domain is not a coercion demand: the raw product of
matchers is not lifted there, so the application is rejected.  A downstream
`RuntimeTyping` certificate exists, but does not define source acceptance. -/
def productMatcherArgumentApplicationSucceeds : Bool :=
  Inference.inferenceSucceeds emptySignature productMatcherConsumerContext
    productMatcherArgumentApplication

#guard !productMatcherArgumentApplicationSucceeds

def productSlotConsumerContext : Context :=
  [("consume", Scheme.mono (.fn concretePairSlotType .int))]

def productSlotArgumentApplication : Expr :=
  .app (.var "consume") (.tuple [.something, .something])

/-- The same domain-directed path composes the product-matcher lift with the
producer-stable matcher-to-slot conversion. -/
def productSlotArgumentApplicationSucceeds : Bool :=
  Inference.inferenceSucceeds emptySignature productSlotConsumerContext
    productSlotArgumentApplication

#guard productSlotArgumentApplicationSucceeds

#guard inferenceHasAlignment productSlotConsumerContext
  productSlotArgumentApplication concretePairMatcherType
  concretePairSlotType .int

def slotTupleConsumerContext : Context :=
  [("consume", Scheme.mono (.fn concretePairSlotType .int)),
   ("left", Scheme.mono (.slot .any .int)),
   ("right", Scheme.mono (.slot .any .int))]

def slotTupleArgumentApplication : Expr :=
  .app (.var "consume") (.tuple [.var "left", .var "right"])

/-- A product of already-slot-valued expressions uses `coerceSlotTuple` at an
ordinary application argument. -/
def slotTupleArgumentApplicationSucceeds : Bool :=
  Inference.inferenceSucceeds emptySignature slotTupleConsumerContext
    slotTupleArgumentApplication

#guard slotTupleArgumentApplicationSucceeds

#guard inferenceHasAlignment slotTupleConsumerContext
  slotTupleArgumentApplication concretePairSlotType concretePairSlotType .int

/-! A product expectation does not trigger componentwise matcher-to-slot
coercions.  Only the explicit whole-product routes above are accepted. -/

def componentSlotConsumerContext : Context :=
  [("consume", Scheme.mono
    (.fn (.prod [.slot .any .int, .slot .any .int]) .int))]

def componentSlotArgumentApplication : Expr :=
  .app (.var "consume") (.tuple [.something, .something])

#guard !Inference.inferenceSucceeds emptySignature componentSlotConsumerContext
  componentSlotArgumentApplication

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
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem terminalLet_typed :
    RuntimeTyping emptySignature
      (Inference.ResolvedContext terminalLetResult.state.prevailing [])
      terminalLetExpression terminalLetResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping terminalLetResult_success

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
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem quantifiedScheme_typed :
    RuntimeTyping emptySignature
      (Inference.ResolvedContext quantifiedSchemeResult.state.prevailing
        quantifiedContext)
      quantifiedExpression quantifiedSchemeResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping quantifiedSchemeResult_success

/-! ## Pattern-function instantiation in both variable sorts -/

def quantifiedPatternFunction : DualScheme where
  capBinders := [0]
  tyBinders := [0]
  args := [⟨.var 0, .var 0⟩]
  result := ⟨.any, .var 0⟩

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
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem quantifiedPApp_typed :
    RuntimeTyping patternFunctionSignature
      (Inference.ResolvedContext quantifiedPAppResult.state.prevailing [])
      quantifiedPAppExpression quantifiedPAppResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping quantifiedPAppResult_success

/-! ## Slot-to-slot expected-type alignment -/

def slotContext : Context :=
  [("slot", Scheme.mono (.slot .any .int))]

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
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def isSlotToSlotEvent : Inference.TraceEvent → Bool
  | .slotAlignment _ _ (.slot _ _) (.slot _ _) => true
  | _ => false

/-- The expected-type boundary really took the slot-to-slot branch. -/
theorem slotToSlot_alignment_recorded :
    slotToSlotResult.state.trace.events.any isSlotToSlotEvent = true := by
  native_decide

theorem slotToSlot_typed :
    RuntimeTyping emptySignature
      (Inference.ResolvedContext slotToSlotResult.state.prevailing slotContext)
      slotToSlotExpression slotToSlotResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping slotToSlotResult_success

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
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

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
    RuntimeTyping matcherSignature
      (Inference.ResolvedContext specializedMatcherResult.state.prevailing [])
      specializedMatcherExpression specializedMatcherResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping specializedMatcherResult_success

/-! ## Public enforcement of the hole/value-pattern-pattern order -/

/-- A general tuple clause keeps coverage independent of the malformed
refinement clause tested below. -/
def generalTupleClause : Clause :=
  .mk (.tuple [.hole, .hole]) (.tuple [.something, .something])
    [.mk .wild (.ctor "nil" [])]

/-- This clause has one PP hole to the left of `#$same`. -/
def outOfOrderTupleClause : Clause :=
  .mk (.tuple [.hole, .pval "same"]) .something
    [.mk .wild (.ctor "nil" [])]

def outOfOrderMatcherExpression : Expr :=
  .matcher [generalTupleClause, outOfOrderTupleClause, catchAllClause]

/-- Raw W already rejects the malformed clause when matcher finalization asks
for actual clause evidence; the terminal validator is a second fail-closed
boundary, not the first order check. -/
theorem outOfOrderMatcher_raw_inference_fails :
    Inference.inferRaw matcherSignature [] outOfOrderMatcherExpression =
      none := by
  native_decide

/-- The public terminally certified entry point rejects the out-of-order PP,
not merely the standalone clause-evidence helper. -/
theorem outOfOrderMatcher_inference_fails :
    Inference.infer matcherSignature [] outOfOrderMatcherExpression = none := by
  native_decide

/-- Reversing only the relevant children puts `#$same` before the PP hole. -/
def inOrderTupleClause : Clause :=
  .mk (.tuple [.pval "same", .hole]) .something
    [.mk .wild (.ctor "nil" [])]

def inOrderMatcherExpression : Expr :=
  .matcher [generalTupleClause, inOrderTupleClause, catchAllClause]

def inOrderRawMatcherResult : Inference.ExprResult :=
  (Inference.inferRaw matcherSignature [] inOrderMatcherExpression).get
    (by native_decide)

/-- Reversing the two relevant children succeeds before terminal
certification as well as at the public entry point. -/
theorem inOrderMatcher_raw_inference_succeeds :
    Inference.inferRaw matcherSignature [] inOrderMatcherExpression =
      some inOrderRawMatcherResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def inOrderMatcherResult : Inference.ExprResult :=
  (Inference.infer matcherSignature [] inOrderMatcherExpression).get
    (by native_decide)

/-- The public entry point accepts the reverse order, fixing the boundary as
an order restriction rather than a blanket rejection of the two forms. -/
theorem inOrderMatcher_inference_succeeds :
    Inference.infer matcherSignature [] inOrderMatcherExpression =
      some inOrderMatcherResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

end CertifiedInferenceRegression
end TypePM
