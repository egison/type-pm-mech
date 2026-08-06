import TypePM.CanonicalCoercion
import TypePM.CertifiedInferenceRegression

/-!
# Surface witnesses for domain-directed application coercions

These declarations complement the executable guards in
`CertifiedInferenceRegression` with explicit declarative derivations.  Each
application has result type `Int`; only the coercion spine used to check its
argument differs.
-/

namespace TypePM
namespace ApplicationCoercionRegression

open CertifiedInferenceRegression

private theorem productMatcherConsumer_typed :
    HasTy emptySignature productMatcherConsumerContext (.var "consume")
      (.fn concretePairMatcherType .int) := by
  apply HasTy.var
      (scheme := Scheme.mono (.fn concretePairMatcherType .int))
  · simp [productMatcherConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem productSlotConsumer_typed :
    HasTy emptySignature productSlotConsumerContext (.var "consume")
      (.fn concretePairSlotType .int) := by
  apply HasTy.var
      (scheme := Scheme.mono (.fn concretePairSlotType .int))
  · simp [productSlotConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem slotTupleConsumer_typed :
    HasTy emptySignature slotTupleConsumerContext (.var "consume")
      (.fn concretePairSlotType .int) := by
  apply HasTy.var
      (scheme := Scheme.mono (.fn concretePairSlotType .int))
  · simp [slotTupleConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem pairOfMatchers_product_typed
    (context : Context) :
    HasTy emptySignature context (.tuple [.something, .something])
      concretePairProductType := by
  simpa [concretePairProductType] using
    (HasTy.tuple
      (ExprsTy.cons (HasTy.something (target := .int))
        (ExprsTy.cons (HasTy.something (target := .int)) ExprsTy.nil)) :
      HasTy emptySignature context (.tuple [.something, .something])
        (.prod [.matcher .any .int, .matcher .any .int]))

private theorem pairOfMatchers_matcher_typed
    (context : Context) :
    HasTy emptySignature context (.tuple [.something, .something])
      concretePairMatcherType := by
  simpa [concretePairProductType, concretePairMatcherType] using
    (HasTy.coerceProductMatcher
      (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
      (pairOfMatchers_product_typed context))

/-- A product of matcher-valued components is lifted to a product matcher at
the ordinary function-argument boundary. -/
theorem productMatcherArgumentApplication_surface_typed :
    HasTy emptySignature productMatcherConsumerContext
      productMatcherArgumentApplication .int := by
  exact HasTy.app productMatcherConsumer_typed
    (pairOfMatchers_matcher_typed productMatcherConsumerContext)

private theorem concretePairMatcher_toSlot_raw :
    MatcherToSlotRawCert
      (.prod [.any, .any]) (.prod [.any, .any])
      (.prod [.int, .int]) (.prod [.int, .int])
      [] CapSubst.id TySubst.id := by
  refine
    { matched := ?_
      capSubstitution := ?_
      targetUnified := ?_
      rangeFixed := ?_ }
  · rfl
  · rfl
  · rfl
  · exact Subst.id_rangeFixed

/-- Observable canonical evidence chooses the whole-product lift before the
single direct matcher-to-slot alignment. -/
def pairProductToSlotNormalPlan
    (context : Context) :
    CanonicalCoercion.NormalPlan emptySignature context
      (.tuple [.something, .something]) concretePairProductType
      concretePairSlotType := by
  apply CanonicalCoercion.NormalPlan.coerce
  apply CanonicalCoercion.Spine.productMatcherToSlot
    (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
  simpa [concretePairMatcherType, concretePairSlotType, Cap.apply_id] using
    (CanonicalCoercion.Step.matcherToSlot
      (signature := emptySignature) (context := context)
      (expression := .tuple [.something, .something])
      concretePairMatcher_toSlot_raw VariablePost.id)

@[simp] theorem pairProductToSlotNormalPlan_kinds
    (context : Context) :
    (pairProductToSlotNormalPlan context).kinds =
      [.productMatcher, .matcherToSlot] := by
  unfold pairProductToSlotNormalPlan CanonicalCoercion.NormalPlan.kinds
  apply CanonicalCoercion.Spine.productMatcherToSlot_kinds

private theorem emptyProductMatcher_toSlot_raw :
    MatcherToSlotRawCert (.prod []) (.prod []) (.prod []) (.prod [])
      [] CapSubst.id TySubst.id := by
  refine
    { matched := rfl
      capSubstitution := rfl
      targetUnified := rfl
      rangeFixed := Subst.id_rangeFixed }

/-- The empty product overlap is resolved by the same matcher-first policy as
the executable selector; an empty `slotTuple` step is not available. -/
def emptyProductToSlotNormalPlan
    (context : Context) :
    CanonicalCoercion.NormalPlan emptySignature context (.tuple [])
      (.prod []) (.slot (.prod []) (.prod [])) := by
  apply CanonicalCoercion.NormalPlan.coerce
  apply CanonicalCoercion.Spine.productMatcherToSlot (duals := [])
  simpa [Cap.apply_id] using
    (CanonicalCoercion.Step.matcherToSlot
      (signature := emptySignature) (context := context)
      (expression := .tuple []) emptyProductMatcher_toSlot_raw VariablePost.id)

@[simp] theorem emptyProductToSlotNormalPlan_kinds
    (context : Context) :
    (emptyProductToSlotNormalPlan context).kinds =
      [.productMatcher, .matcherToSlot] := by
  unfold emptyProductToSlotNormalPlan CanonicalCoercion.NormalPlan.kinds
  apply CanonicalCoercion.Spine.productMatcherToSlot_kinds

private theorem pairOfMatchers_slot_typed
    (context : Context) :
    HasTy emptySignature context (.tuple [.something, .something])
      concretePairSlotType := by
  exact (pairProductToSlotNormalPlan context).toHasTy
    (pairOfMatchers_product_typed context)

/-- A product matcher is subsequently converted to the aggregate slot required
by the function domain. -/
theorem productSlotArgumentApplication_surface_typed :
    HasTy emptySignature productSlotConsumerContext
      productSlotArgumentApplication .int := by
  exact HasTy.app productSlotConsumer_typed
    (pairOfMatchers_slot_typed productSlotConsumerContext)

private theorem slotVariable_typed
    (name : String)
    (lookup : slotTupleConsumerContext.find? name =
      some (Scheme.mono (.slot .any .int))) :
    HasTy emptySignature slotTupleConsumerContext (.var name)
      (.slot .any .int) :=
  HasTy.var lookup (Scheme.mono_valueFlowInst _)

private theorem pairOfSlots_product_typed :
    HasTy emptySignature slotTupleConsumerContext
      (.tuple [.var "left", .var "right"]) concretePairOfSlotsType := by
  have leftTyping := slotVariable_typed "left" (by
    simp [slotTupleConsumerContext, Context.find?])
  have rightTyping := slotVariable_typed "right" (by
    simp [slotTupleConsumerContext, Context.find?])
  simpa [concretePairOfSlotsType] using
    (HasTy.tuple (ExprsTy.cons leftTyping
      (ExprsTy.cons rightTyping ExprsTy.nil)))

private theorem pairOfSlots_slot_typed :
    HasTy emptySignature slotTupleConsumerContext
      (.tuple [.var "left", .var "right"]) concretePairSlotType := by
  simpa [concretePairOfSlotsType, concretePairSlotType] using
    (HasTy.coerceSlotTuple
      (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
      pairOfSlots_product_typed)

/-- When the children already synthesize slots, the canonical plan is the
single aggregate slot-tuple step. -/
def pairSlotsNormalPlan :
    CanonicalCoercion.NormalPlan emptySignature slotTupleConsumerContext
      (.tuple [.var "left", .var "right"])
      concretePairOfSlotsType concretePairSlotType := by
  apply CanonicalCoercion.NormalPlan.coerce
  exact CanonicalCoercion.Spine.one
    (CanonicalCoercion.Step.slotTuple
      (signature := emptySignature) (context := slotTupleConsumerContext)
      (expression := .tuple [.var "left", .var "right"])
      (duals := [⟨.any, .int⟩, ⟨.any, .int⟩]) (by simp))

@[simp] theorem pairSlotsNormalPlan_kinds :
    pairSlotsNormalPlan.kinds = [.slotTuple] := by
  rfl

/-- A product of slot-valued components uses the aggregate slot-tuple
coercion before application. -/
theorem slotTupleArgumentApplication_surface_typed :
    HasTy emptySignature slotTupleConsumerContext
      slotTupleArgumentApplication .int := by
  exact HasTy.app slotTupleConsumer_typed pairOfSlots_slot_typed

end ApplicationCoercionRegression
end TypePM
