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
for the existing `Elaboration.CoercionPlan` relation.  Normalization of an
arbitrary surface plan into this syntax and uniqueness of inhabitants are
separate, currently unproved properties.
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
inductive Step (signature : FrozenSig) (context : Context) (expression : Expr) :
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
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) : Kind :=
  match step with
  | .matcherToSlot _ _ => .matcherToSlot
  | .productMatcher => .productMatcher
  | .slotTuple _ => .slotTuple

/-- Forget one observable step into the existing surface coercion relation. -/
def Step.toCoercionPlan
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match step with
  | .matcherToSlot raw post => .matcherToSlot raw post
  | .productMatcher => .productMatcher
  | .slotTuple _ => .slotTuple

/-- Every observable primitive step changes its indexed type. -/
theorem Step.source_ne_target
    {signature : FrozenSig} {context : Context} {expression : Expr}
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
inductive Spine (signature : FrozenSig) (context : Context) (expression : Expr) :
    Ty -> Ty -> Type where
  | one {source target} :
      Step signature context expression source target ->
      Spine signature context expression source target
  | productMatcherToSlot
      {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty} :
      Step signature context expression
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
        (.slot consumerCap consumerTarget) ->
      Spine signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target))
        (.slot consumerCap consumerTarget)

/-- The observable primitive-rule sequence of a canonical spine. -/
def Spine.kinds
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) : List Kind :=
  match spine with
  | .one step => [step.kind]
  | .productMatcherToSlot alignment =>
      [.productMatcher, alignment.kind]

private def MatcherHead : Ty -> Prop
  | .matcher _ _ => True
  | _ => False

private def SlotHead : Ty -> Prop
  | .slot _ _ => True
  | _ => False

private theorem Step.kind_eq_matcherToSlot_of_heads
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (step : Step signature context expression source target)
    (sourceMatcher : MatcherHead source) (targetSlot : SlotHead target) :
    step.kind = .matcherToSlot := by
  cases step <;> simp_all [MatcherHead, SlotHead, Step.kind]

/-- A whole product-matcher lift followed by slot alignment has exactly the
two intended primitive rules.  The endpoints of `alignment` rule out every
`Step` constructor except matcher-to-slot. -/
@[simp] theorem Spine.productMatcherToSlot_kinds
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (alignment : Step signature context expression
      (.matcher (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)))
      (.slot consumerCap consumerTarget)) :
    (Spine.productMatcherToSlot alignment).kinds =
      [.productMatcher, .matcherToSlot] := by
  change [.productMatcher, alignment.kind] =
    [.productMatcher, .matcherToSlot]
  rw [Step.kind_eq_matcherToSlot_of_heads alignment (by trivial) (by trivial)]

/-- Canonical spines contain no zero-step identity representation. -/
theorem Spine.kinds_ne_nil
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    spine.kinds ≠ [] := by
  cases spine <;> simp [Spine.kinds]

/-- Canonical spines contain at most the one required aggregate composition. -/
theorem Spine.kinds_length_le_two
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    spine.kinds.length <= 2 := by
  cases spine <;> simp [Spine.kinds]

/-- Every observable nonempty spine changes its indexed type. -/
theorem Spine.source_ne_target
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    source ≠ target := by
  cases spine with
  | one step => exact step.source_ne_target
  | productMatcherToSlot _ => simp

/--
The whole-product-first policy is observable as the first primitive rule.
Because `Spine` is indexed, a spine satisfying this predicate necessarily
starts at a product of matcher types and first constructs their product matcher.
-/
def Spine.WholeProductFirst
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) : Prop :=
  spine.kinds.head? = some .productMatcher

@[simp] theorem Spine.productMatcher_wholeProductFirst
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {duals : List Dual} :
    Spine.WholeProductFirst
      (Spine.one
        (Step.productMatcher (signature := signature) (context := context)
          (expression := expression) (duals := duals))) := by
  rfl

@[simp] theorem Spine.productMatcherToSlot_wholeProductFirst
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (alignment : Step signature context expression
      (.matcher (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)))
      (.slot consumerCap consumerTarget)) :
    Spine.WholeProductFirst (Spine.productMatcherToSlot alignment) := by
  rfl

/-- Interpret a canonical spine in the existing propositional relation. -/
def Spine.toCoercionPlan
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (spine : Spine signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match spine with
  | .one step => step.toCoercionPlan
  | .productMatcherToSlot alignment =>
      .trans .productMatcher alignment.toCoercionPlan

/-- Soundness of the observable spine for surface coercion replay. -/
theorem Spine.sound
    {signature : FrozenSig} {context : Context} {expression : Expr}
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
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    Ty -> Ty -> Type where
  | refl {target} :
      NormalPlan signature context expression target target
  | coerce {source target} :
      Spine signature context expression source target ->
      NormalPlan signature context expression source target

/-- At equal endpoints the dedicated identity constructor is the only
possible candidate normal plan. -/
theorem NormalPlan.eq_refl
    {signature : FrozenSig} {context : Context} {expression : Expr}
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
    {signature : FrozenSig} {context : Context} {expression : Expr}
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

/-- Observable rule sequence, with identity represented by the empty list. -/
def NormalPlan.kinds
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) : List Kind :=
  match plan with
  | .refl => []
  | .coerce spine => spine.kinds

/-- Forget a normal plan into the existing propositional coercion relation. -/
def NormalPlan.toCoercionPlan
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  match plan with
  | .refl => .refl
  | .coerce spine => spine.toCoercionPlan

/-- Soundness of the candidate normal-plan syntax for the existing coercion relation. -/
theorem NormalPlan.sound
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target) :
    Elaboration.CoercionPlan signature context expression source target :=
  plan.toCoercionPlan

/-- Replaying a normal plan over a source typing yields the target surface
typing. -/
theorem NormalPlan.toHasTy
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : NormalPlan signature context expression source target)
    (typing : HasTy signature context expression source) :
    HasTy signature context expression target :=
  plan.toCoercionPlan.toHasTy typing

end CanonicalCoercion
end TypePM
