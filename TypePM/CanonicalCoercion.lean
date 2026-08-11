import TypePM.Elaboration

/-!
# Observable coercion-plan spines

`Elaboration.CoercionPlan` is a `Prop`-valued reachability relation.  Its
`refl` and `trans` constructors are convenient for surface factorization, but
they do not expose an observable normal form: identity steps can be inserted
freely and the same spine can be parenthesized in many ways.

This module gives the three observable, non-identity primitive coercions an
indexed `Type`-valued candidate normal-plan syntax.  `Spine` is deliberately
nonempty and has no general composition constructor.  Besides one primitive
step, it admits only the aggregate slot shape needed after a whole-product
matcher lift:

* product of matchers, then matcher-to-slot.

Thus a product-of-matchers used as a slot is represented with the whole-product
step first, rather than by coercing tuple components independently.  A
nonempty product of slots becomes its aggregate slot in the single observable
`slotTuple` step.  A raw slot-to-slot check is not observable here: its
certificate proves that its fully substituted endpoints are equal, so it is
represented by `NormalPlan.refl`.

The forgetful interpretation below proves that every observable spine is sound
for the existing `Elaboration.CoercionPlan` relation.  Conversely, every
surface plan logically has a normal plan: composition closes on the sole
whole-product-first two-step path, and the empty slot product uses that same
matcher-first path.  Because `CoercionPlan` is a proposition, this completeness
result is wrapped in `Nonempty` and does not compute observable plan data.
The observable `kinds` sequence is unique at fixed endpoints; full plan
inhabitant uniqueness remains a separate question because raw certificates can
differ.
-/

namespace TypePM
namespace CanonicalCoercion

/-- Observable names of the three non-identity primitive coercion rules. -/
inductive Kind where
  | productMatcher
  | slotTuple
  | matcherToSlot
deriving Repr, DecidableEq

/--
A successful raw slot-to-slot check has equal source and requested slot types
after applying its capability MGU, target MGU, and any later post-substitution.
-/
theorem slotToSlotRawCert_appliedSlot_eq
    {sourceCap requestedCap : Cap}
    {sourceTarget requestedTarget : Ty}
    {C : CapSubst} {T : TySubst}
    (raw : SlotToSlotRawCert sourceCap requestedCap sourceTarget
      requestedTarget C T)
    (post : Subst) :
    Ty.slot ((sourceCap.apply C).apply post.cap)
        (post.apply ((Subst.mk C T).apply sourceTarget)) =
      Ty.slot ((requestedCap.apply C).apply post.cap)
        (post.apply ((Subst.mk C T).apply requestedTarget)) := by
  have capabilityEq :
      (sourceCap.apply C).apply post.cap =
        (requestedCap.apply C).apply post.cap := by
    exact congrArg (fun capability => capability.apply post.cap)
      (Unification.mguCap_sound raw.capabilityUnified)
  have targetEq :
      post.apply ((Subst.mk C T).apply sourceTarget) =
        post.apply ((Subst.mk C T).apply requestedTarget) := by
    apply congrArg post.apply
    simpa only [Subst.apply] using
      Unification.mguTy_sound raw.targetUnified
  rw [capabilityEq, targetEq]

/--
One primitive, non-identity coercion step.  The source and target indices are
exactly those of the corresponding `Elaboration.CoercionPlan` constructor.

The certificates remain propositions, while the constructor choice is data in
`Type` and can therefore be inspected by an elaborator or a normalization
proof.
-/
inductive Step (signature : FrozenSig) (context : NamedContext) (expression : Expr) :
    Ty -> Ty -> Type where
  | matcherToSlot
      {producerCap producerTarget consumerCap consumerTarget bindings C T post} :
      MatcherToSlotRawCert producerCap consumerCap producerTarget
        consumerTarget bindings C T ->
      VariablePost post ->
      Step signature context expression
        (.matcher ((producerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply producerTarget)))
        (.slot ((consumerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply consumerTarget)))
  | productMatcher {duals : List Dual} :
      Step signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target))
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  | slotTuple {duals : List Dual} :
      duals ≠ [] ->
      Step signature context expression
        (.prod (duals.map fun dual => .slot dual.cap dual.target))
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- The observable rule name of one primitive step. -/
def Step.kind
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) : Kind :=
  match step with
  | .matcherToSlot _ _ => .matcherToSlot
  | .productMatcher => .productMatcher
  | .slotTuple _ => .slotTuple

/-- Observable rule classification determined by endpoint heads. -/
private def endpointKind? : Ty -> Ty -> Option Kind
  | .matcher _ _, .slot _ _ => some .matcherToSlot
  | .prod _, .matcher _ _ => some .productMatcher
  | .prod _, .slot _ _ => some .slotTuple
  | _, _ => none

private theorem Step.endpointKind?_eq
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) :
    endpointKind? source target = some step.kind := by
  cases step <;> rfl

/-- Primitive steps with the same indexed endpoints have the same observable
rule name, even when their hidden raw certificates differ. -/
theorem Step.kind_unique
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (first second : Step signature context expression source target) :
    first.kind = second.kind := by
  have equality : some first.kind = some second.kind :=
    first.endpointKind?_eq.symm.trans second.endpointKind?_eq
  exact Option.some.inj equality

/-- Forget one observable step into the existing surface coercion relation. -/
def Step.toCoercionPlan
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match step with
  | .matcherToSlot raw post => .matcherToSlot raw post
  | .productMatcher => .productMatcher
  | .slotTuple _ => .slotTuple

/-- Every observable primitive step changes its indexed type. -/
theorem Step.source_ne_target
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) :
    source ≠ target := by
  cases step <;> simp

/--
A nonempty coercion-plan spine.

There is no constructor for identity and no general `cons`/`trans`.  The only
two-step form is the canonical aggregate matcher-to-slot path.  Its indices
force the second step to be matcher-to-slot.
-/
inductive Spine (signature : FrozenSig) (context : NamedContext) (expression : Expr) :
    Ty -> Ty -> Type where
  | one {source target} :
      Step signature context expression source target ->
      Spine signature context expression source target
  | productMatcherToSlot
      {duals : List Dual} {target : Ty} :
      Step signature context expression
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
        target ->
      Spine signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target))
        target

/-- The observable primitive-rule sequence of a canonical spine. -/
def Spine.kinds
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) : List Kind :=
  match spine with
  | .one step => [step.kind]
  | .productMatcherToSlot alignment =>
      [.productMatcher, alignment.kind]

/-- Canonical observable sequence selected solely from the endpoint heads and
the first product component.  Empty products follow matcher-first precedence. -/
private def endpointSpineKinds : Ty -> Ty -> List Kind
  | .matcher _ _, .slot _ _ => [.matcherToSlot]
  | .prod [], .matcher _ _ => [.productMatcher]
  | .prod [], .slot _ _ => [.productMatcher, .matcherToSlot]
  | .prod (.matcher _ _ :: _), .matcher _ _ => [.productMatcher]
  | .prod (.matcher _ _ :: _), .slot _ _ =>
      [.productMatcher, .matcherToSlot]
  | .prod (.slot _ _ :: _), .slot _ _ => [.slotTuple]
  | _, _ => []

private def MatcherHead : Ty -> Prop
  | .matcher _ _ => True
  | _ => False

private def SlotHead : Ty -> Prop
  | .slot _ _ => True
  | _ => False

/-- A primitive step whose source is a matcher must be matcher-to-slot. -/
private theorem Step.kind_eq_matcherToSlot_of_source
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target)
    (sourceMatcher : MatcherHead source) :
    step.kind = .matcherToSlot := by
  cases step <;> simp_all [MatcherHead, Step.kind]

/-- Observable primitive steps never start at a slot. -/
private theorem Step.source_not_slot
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) :
    ¬ SlotHead source := by
  cases step <;> simp [SlotHead]

/-- A primitive step starting at a matcher necessarily ends at a slot. -/
private theorem Step.target_slot_of_source_matcher
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target)
    (sourceMatcher : MatcherHead source) :
    SlotHead target := by
  cases step <;> simp_all [MatcherHead, SlotHead]

/-- A whole product-matcher lift followed by slot alignment has exactly the
two intended primitive rules.  The endpoints of `alignment` rule out every
`Step` constructor except matcher-to-slot. -/
@[simp] theorem Spine.productMatcherToSlot_kinds
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {duals : List Dual} {target : Ty}
    (alignment : Step signature context expression
      (.matcher (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)))
      target) :
    (Spine.productMatcherToSlot alignment).kinds =
      [.productMatcher, .matcherToSlot] := by
  change [.productMatcher, alignment.kind] =
    [.productMatcher, .matcherToSlot]
  rw [Step.kind_eq_matcherToSlot_of_source alignment (by trivial)]

private theorem Spine.kinds_eq_endpointSpineKinds
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    spine.kinds = endpointSpineKinds source target := by
  cases spine with
  | one step =>
      cases step with
      | matcherToSlot _ _ => rfl
      | @productMatcher duals => cases duals <;> rfl
      | @slotTuple duals nonempty =>
          cases duals with
          | nil => exact False.elim (nonempty rfl)
          | cons _ _ => rfl
  | @productMatcherToSlot duals target alignment =>
      rw [Spine.productMatcherToSlot_kinds]
      have targetSlot := alignment.target_slot_of_source_matcher (by trivial)
      cases duals <;> cases target <;>
        simp_all [SlotHead, endpointSpineKinds]

/-- Canonical spines with the same endpoints have the same observable rule
sequence, although their hidden certificates need not be equal. -/
theorem Spine.kinds_unique
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (first second : Spine signature context expression source target) :
    first.kinds = second.kinds := by
  rw [first.kinds_eq_endpointSpineKinds,
    second.kinds_eq_endpointSpineKinds]

/-- Canonical spines contain no zero-step identity representation. -/
theorem Spine.kinds_ne_nil
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    spine.kinds ≠ [] := by
  cases spine <;> simp [Spine.kinds]

/-- Canonical spines contain at most the one required aggregate composition. -/
theorem Spine.kinds_length_le_two
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    spine.kinds.length <= 2 := by
  cases spine <;> simp [Spine.kinds]

/-- Canonical nonempty spines never start at a slot. -/
private theorem Spine.source_not_slot
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    ¬ SlotHead source := by
  cases spine with
  | one step => exact step.source_not_slot
  | productMatcherToSlot _ => simp [SlotHead]

/-- Every observable nonempty spine changes its indexed type. -/
theorem Spine.source_ne_target
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    source ≠ target := by
  cases spine with
  | one step => exact step.source_ne_target
  | productMatcherToSlot alignment =>
      intro equality
      have targetSlot := alignment.target_slot_of_source_matcher (by trivial)
      rw [← equality] at targetSlot
      exact targetSlot

/--
The whole-product-first policy is observable as the first primitive rule.
Because `Spine` is indexed, a spine satisfying this predicate necessarily
starts at a product of matcher types and first constructs their product matcher.
-/
def Spine.WholeProductFirst
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) : Prop :=
  spine.kinds.head? = some .productMatcher

@[simp] theorem Spine.productMatcher_wholeProductFirst
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {duals : List Dual} :
    Spine.WholeProductFirst
      (Spine.one
        (Step.productMatcher (signature := signature) (context := context)
          (expression := expression) (duals := duals))) := by
  rfl

@[simp] theorem Spine.productMatcherToSlot_wholeProductFirst
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {duals : List Dual} {target : Ty}
    (alignment : Step signature context expression
      (.matcher (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)))
      target) :
    Spine.WholeProductFirst (Spine.productMatcherToSlot alignment) := by
  rfl

/-- Interpret a canonical spine in the existing propositional relation. -/
def Spine.toCoercionPlan
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match spine with
  | .one step => step.toCoercionPlan
  | .productMatcherToSlot alignment =>
      .trans .productMatcher alignment.toCoercionPlan

/-- Soundness of the observable spine for surface coercion replay. -/
theorem Spine.sound
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  spine.toCoercionPlan

/--
The outer candidate normal-plan syntax.  The dedicated identity constructor
lives at this layer and every explicit coercion constructor contains one
nonempty `Spine`.  Since every spine changes its indexed type, equal endpoints
force `refl`; this does not yet say that arbitrary inhabitants with distinct
endpoints are unique.  There is deliberately no constructor corresponding to
`CoercionPlan.trans`.
-/
inductive NormalPlan
    (signature : FrozenSig) (context : NamedContext) (expression : Expr) :
    Ty -> Ty -> Type where
  | refl {target} :
      NormalPlan signature context expression target target
  | coerce {source target} :
      Spine signature context expression source target ->
      NormalPlan signature context expression source target

/-- At equal endpoints the dedicated identity constructor is the only
possible candidate normal plan. -/
theorem NormalPlan.eq_refl
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {target : Ty}
    (plan : NormalPlan signature context expression target target) :
    plan = .refl := by
  cases plan with
  | refl => rfl
  | coerce spine => exact False.elim (spine.source_ne_target rfl)

/--
Canonicalize a certified surface slot-to-slot check as identity.  The raw
certificate proves that the two fully substituted endpoints coincide;
`VariablePost` is retained as an argument so this helper consumes exactly the
evidence carried by `Elaboration.CoercionPlan.checkSlotToSlot`.
-/
def NormalPlan.ofSurfaceSlotToSlot
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {sourceCap sourceTarget requestedCap requestedTarget C T post}
    (raw : SlotToSlotRawCert sourceCap requestedCap sourceTarget
      requestedTarget C T)
    (_postVariable : VariablePost post) :
    NormalPlan signature context expression
      (.slot ((sourceCap.apply C).apply post.cap)
        (post.apply ((Subst.mk C T).apply sourceTarget)))
      (.slot ((requestedCap.apply C).apply post.cap)
        (post.apply ((Subst.mk C T).apply requestedTarget))) := by
  rw [slotToSlotRawCert_appliedSlot_eq raw post]
  exact .refl

/-- Compose two candidate normal plans.  Apart from identity, the indexed head
shapes leave exactly one composable pair: a whole-product matcher lift followed
by matcher-to-slot alignment. -/
def NormalPlan.comp
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source middle target : Ty}
    (first : NormalPlan signature context expression source middle)
    (second : NormalPlan signature context expression middle target) :
    NormalPlan signature context expression source target := by
  cases first with
  | refl => exact second
  | coerce firstSpine =>
      cases second with
      | refl => exact .coerce firstSpine
      | coerce secondSpine =>
          cases firstSpine with
          | one firstStep =>
              cases firstStep with
              | matcherToSlot _ _ =>
                  exact False.elim (secondSpine.source_not_slot (by trivial))
              | @productMatcher duals =>
                  cases secondSpine with
                  | one secondStep =>
                      exact .coerce
                        (.productMatcherToSlot (duals := duals) secondStep)
              | slotTuple _ =>
                  exact False.elim (secondSpine.source_not_slot (by trivial))
          | productMatcherToSlot alignment =>
              have middleSlot := alignment.target_slot_of_source_matcher
                (by trivial)
              exact False.elim (secondSpine.source_not_slot middleSlot)

/-- Identity raw certificate used by the canonical empty-product overlap. -/
theorem emptyProductMatcherToSlotRaw :
    MatcherToSlotRawCert (.prod []) (.prod []) (.prod []) (.prod [])
      [] CapSubst.id TySubst.id := by
  refine
    { matched := rfl
      capSubstitution := rfl
      targetUnified := Unification.mguTy_self _
      rangeFixed := Subst.id_rangeFixed }

/-- The empty slot-product surface rule normalizes through the matcher-first
two-step policy, because observable `slotTuple` steps are nonempty. -/
def NormalPlan.emptySlotTuple
    {signature : FrozenSig} {context : NamedContext} {expression : Expr} :
    NormalPlan signature context expression (.prod [])
      (.slot (.prod []) (.prod [])) := by
  apply NormalPlan.coerce
  apply Spine.productMatcherToSlot (duals := [])
  simpa [Cap.apply_id] using
    (Step.matcherToSlot (signature := signature) (context := context)
      (expression := expression) emptyProductMatcherToSlotRaw VariablePost.id)

/-- Observable rule sequence, with identity represented by the empty list. -/
def NormalPlan.kinds
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) : List Kind :=
  match plan with
  | .refl => []
  | .coerce spine => spine.kinds

private def endpointNormalKinds (source target : Ty) : List Kind :=
  if source = target then [] else endpointSpineKinds source target

private theorem NormalPlan.kinds_eq_endpointNormalKinds
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) :
    plan.kinds = endpointNormalKinds source target := by
  cases plan with
  | refl => simp [NormalPlan.kinds, endpointNormalKinds]
  | coerce spine =>
      simp [NormalPlan.kinds, endpointNormalKinds, spine.source_ne_target,
        spine.kinds_eq_endpointSpineKinds]

/-- Normal plans with the same endpoints have one observable rule sequence.
The plans themselves may still differ in hidden raw certificates. -/
theorem NormalPlan.kinds_unique
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (first second : NormalPlan signature context expression source target) :
    first.kinds = second.kinds := by
  rw [first.kinds_eq_endpointNormalKinds,
    second.kinds_eq_endpointNormalKinds]

/-- Forget a normal plan into the existing propositional coercion relation. -/
def NormalPlan.toCoercionPlan
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match plan with
  | .refl => .refl
  | .coerce spine => spine.toCoercionPlan

/-- Soundness of the candidate normal-plan syntax for the existing coercion relation. -/
theorem NormalPlan.sound
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  plan.toCoercionPlan

/-- Replaying a normal plan over a runtime certificate yields the target
runtime certificate. -/
theorem NormalPlan.toRuntimeTyping
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target)
    (typing : RuntimeTyping signature context expression source) :
    RuntimeTyping signature context expression target :=
  plan.toCoercionPlan.toRuntimeTyping typing

end CanonicalCoercion

namespace Elaboration

open CanonicalCoercion

/-- Every propositional outer coercion spine has a candidate normal plan.
`Nonempty` is necessary because a proof in `Prop` cannot computationally return
observable `NormalPlan` data in `Type`. -/
theorem CoercionPlan.normalizable
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty}
    (plan : CoercionPlan signature context expression source target) :
    Nonempty (NormalPlan signature context expression source target) := by
  induction plan with
  | refl => exact ⟨.refl⟩
  | matcherToSlot raw post =>
      exact ⟨.coerce (.one (.matcherToSlot raw post))⟩
  | checkSlotToSlot raw post =>
      exact ⟨.ofSurfaceSlotToSlot raw post⟩
  | productMatcher =>
      exact ⟨.coerce (.one .productMatcher)⟩
  | @slotTuple duals =>
      cases duals with
      | nil => exact ⟨.emptySlotTuple⟩
      | cons head tail =>
          exact ⟨.coerce (.one (.slotTuple (by simp)))⟩
  | trans _ _ firstIH secondIH =>
      rcases firstIH with ⟨first⟩
      rcases secondIH with ⟨second⟩
      exact ⟨first.comp second⟩

/-- The candidate normal syntax is sound and complete for propositional outer
coercion reachability. -/
theorem coercionPlan_iff_nonempty_normalPlan
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {source target : Ty} :
    CoercionPlan signature context expression source target ↔
      Nonempty (NormalPlan signature context expression source target) := by
  constructor
  · exact CoercionPlan.normalizable
  · rintro ⟨normal⟩
    exact normal.sound

end Elaboration
end TypePM
