import TypePM.CanonicalCoercion
import TypePM.CertifiedInferenceRegression

/-!
# Runtime-certificate witnesses for application coercions

These declarations complement the executable guards in
`CertifiedInferenceRegression` with explicit state-free certificates.  Each
application has result type `Int`; only the coercion spine used to check its
argument differs.  The matcher-headed variant is certificate-only: a matcher
expectation is not a slot demand, so the public inferencer rejects that
application and its guard is negative.
-/

namespace TypePM
namespace ApplicationCoercionRegression

open CertifiedInferenceRegression

private theorem productMatcherConsumer_typed :
    RuntimeTyping emptySignature productMatcherConsumerContext (.var "consume")
      (.fn concretePairMatcherType .int) := by
  apply RuntimeTyping.var
      (scheme := Scheme.mono (.fn concretePairMatcherType .int))
  · simp [productMatcherConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem productSlotConsumer_typed :
    RuntimeTyping emptySignature productSlotConsumerContext (.var "consume")
      (.fn concretePairSlotType .int) := by
  apply RuntimeTyping.var
      (scheme := Scheme.mono (.fn concretePairSlotType .int))
  · simp [productSlotConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem slotTupleConsumer_typed :
    RuntimeTyping emptySignature slotTupleConsumerContext (.var "consume")
      (.fn concretePairSlotType .int) := by
  apply RuntimeTyping.var
      (scheme := Scheme.mono (.fn concretePairSlotType .int))
  · simp [slotTupleConsumerContext, Context.find?]
  · exact Scheme.mono_valueFlowInst _

private theorem pairOfMatchers_product_typed
    (context : Context) :
    RuntimeTyping emptySignature context (.tuple [.something, .something])
      concretePairProductType := by
  simpa [concretePairProductType] using
    (RuntimeTyping.tuple
      (ExprsTy.cons (RuntimeTyping.something (target := .int))
        (ExprsTy.cons (RuntimeTyping.something (target := .int)) ExprsTy.nil)) :
      RuntimeTyping emptySignature context (.tuple [.something, .something])
        (.prod [.matcher .any .int, .matcher .any .int]))

private theorem pairOfMatchers_matcher_typed
    (context : Context) :
    RuntimeTyping emptySignature context (.tuple [.something, .something])
      concretePairMatcherType := by
  simpa [concretePairProductType, concretePairMatcherType] using
    (RuntimeTyping.coerceProductMatcher
      (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
      (pairOfMatchers_product_typed context))

/-- A state-free certificate can lift a product of matchers at a matcher-headed
argument boundary.  This does not imply source acceptance: under slot-demand
the boundary is not a coercion demand, so both `DDTyping` and public inference
reject the application. -/
theorem productMatcherArgumentApplication_runtimeCertified :
    RuntimeTyping emptySignature productMatcherConsumerContext
      productMatcherArgumentApplication .int := by
  exact RuntimeTyping.app productMatcherConsumer_typed
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
  · simp
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

/-- The empty product overlap is resolved by the same matcher-first policy as
the executable selector; an empty `slotTuple` step is not available. -/
def emptyProductToSlotNormalPlan
    (context : Context) :
    CanonicalCoercion.NormalPlan emptySignature context (.tuple [])
      (.prod []) (.slot (.prod []) (.prod [])) := by
  exact CanonicalCoercion.NormalPlan.emptySlotTuple

@[simp] theorem emptyProductToSlotNormalPlan_kinds
    (context : Context) :
    (emptyProductToSlotNormalPlan context).kinds =
      [.productMatcher, .matcherToSlot] := by
  unfold emptyProductToSlotNormalPlan CanonicalCoercion.NormalPlan.kinds
  apply CanonicalCoercion.Spine.productMatcherToSlot_kinds

private theorem pairOfMatchers_slot_typed
    (context : Context) :
    RuntimeTyping emptySignature context (.tuple [.something, .something])
      concretePairSlotType := by
  exact (pairProductToSlotNormalPlan context).toRuntimeTyping
    (pairOfMatchers_product_typed context)

/-- A product matcher is subsequently converted to the aggregate slot required
by the function domain. -/
theorem productSlotArgumentApplication_runtimeCertified :
    RuntimeTyping emptySignature productSlotConsumerContext
      productSlotArgumentApplication .int := by
  exact RuntimeTyping.app productSlotConsumer_typed
    (pairOfMatchers_slot_typed productSlotConsumerContext)

private theorem slotVariable_typed
    (name : String)
    (lookup : slotTupleConsumerContext.find? name =
      some (Scheme.mono (.slot .any .int))) :
    RuntimeTyping emptySignature slotTupleConsumerContext (.var name)
      (.slot .any .int) :=
  RuntimeTyping.var lookup (Scheme.mono_valueFlowInst _)

private theorem pairOfSlots_product_typed :
    RuntimeTyping emptySignature slotTupleConsumerContext
      (.tuple [.var "left", .var "right"]) concretePairOfSlotsType := by
  have leftTyping := slotVariable_typed "left" (by
    simp [slotTupleConsumerContext, Context.find?])
  have rightTyping := slotVariable_typed "right" (by
    simp [slotTupleConsumerContext, Context.find?])
  simpa [concretePairOfSlotsType] using
    (RuntimeTyping.tuple (ExprsTy.cons leftTyping
      (ExprsTy.cons rightTyping ExprsTy.nil)))

private theorem pairOfSlots_slot_typed :
    RuntimeTyping emptySignature slotTupleConsumerContext
      (.tuple [.var "left", .var "right"]) concretePairSlotType := by
  simpa [concretePairOfSlotsType, concretePairSlotType] using
    (RuntimeTyping.coerceSlotTuple
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
theorem slotTupleArgumentApplication_runtimeCertified :
    RuntimeTyping emptySignature slotTupleConsumerContext
      slotTupleArgumentApplication .int := by
  exact RuntimeTyping.app slotTupleConsumer_typed pairOfSlots_slot_typed

end ApplicationCoercionRegression
end TypePM
