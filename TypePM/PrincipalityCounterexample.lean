import TypePM.Source

/-!
# The runtime certificate is not a principal-type specification

This module records why the internal `RuntimeTyping` family must not be used
as a principal-type specification.  The closed expression
`(something, something)` has certificates for

* a product of matchers, by `T-TUPLE`, and
* a product matcher, by `COERCE-PRODUCT-MATCHER`,

and these two certificate types have different head constructors (`prod`
versus `matcher`).  Every certificate type of a tuple expression has a
`prod`, `matcher`, or `slot` head, and paired substitution preserves each
of these heads, so no certificate type of this expression has both forms
among its substitution instances.  Hence this internal family has no
principal certificate type for the expression.

The counterexample is not exotic: usable product matchers require exactly
this coercion overlap, and the failure is independent of capability
evidence.  It says nothing about type uniqueness or principality for the
public `DDTyping` judgment.
-/

namespace TypePM
namespace PrincipalityCounterexample

/-- The two-element tuple of `something` matchers. -/
def pairProgram : Expr :=
  .tuple [.something, .something]

/-- Its product-of-matchers typing, by `T-TUPLE`. -/
theorem pair_prod_typing {signature : FrozenSig} :
    RuntimeTyping signature [] pairProgram
      (.prod [.matcher .any .int, .matcher .any .int]) :=
  RuntimeTyping.tuple (.cons RuntimeTyping.something (.cons RuntimeTyping.something .nil))

/-- Its product-matcher typing, by `COERCE-PRODUCT-MATCHER`. -/
theorem pair_matcher_typing {signature : FrozenSig} :
    RuntimeTyping signature [] pairProgram
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  RuntimeTyping.coerceProductMatcher
    (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
    pair_prod_typing

/-- Every derivable type of a tuple has a `prod`, `matcher`, or `slot` head. -/
theorem tuple_ty_head {signature : FrozenSig} {context : NamedContext}
    {expressions : List Expr} {target : Ty}
    (typing : RuntimeTyping signature context (.tuple expressions) target) :
    (∃ components, target = .prod components) ∨
    (∃ capability targetTy, target = .matcher capability targetTy) ∨
    (∃ capability targetTy, target = .slot capability targetTy) := by
  cases typing with
  | tuple _ => exact .inl ⟨_, rfl⟩
  | coerceProductMatcher _ => exact .inr (.inl ⟨_, _, rfl⟩)
  | coerceMatcherToSlot _ _ => exact .inr (.inr ⟨_, _, rfl⟩)
  | coerceSlotTuple _ => exact .inr (.inr ⟨_, _, rfl⟩)

/-- Paired substitution preserves the `prod` head. -/
theorem apply_prod_head (S : Subst) (components : List Ty) :
    ∃ applied, S.apply (.prod components) = .prod applied :=
  ⟨Ty.applyTargetList S.target (Ty.applyCapabilityList S.cap components),
    rfl⟩

/-- Paired substitution preserves the `matcher` head. -/
theorem apply_matcher_head (S : Subst) (capability : Cap) (target : Ty) :
    ∃ appliedCap appliedTarget,
      S.apply (.matcher capability target) =
        .matcher appliedCap appliedTarget :=
  ⟨capability.apply S.cap,
    (target.applyCapability S.cap).applyTarget S.target, rfl⟩

/-- Paired substitution preserves the `slot` head. -/
theorem apply_slot_head (S : Subst) (capability : Cap) (target : Ty) :
    ∃ appliedCap appliedTarget,
      S.apply (.slot capability target) = .slot appliedCap appliedTarget :=
  ⟨capability.apply S.cap,
    (target.applyCapability S.cap).applyTarget S.target, rfl⟩

/--
No `RuntimeTyping` type of `(something, something)` has both the product and
product-matcher certificates among its paired-substitution instances.
Principality therefore fails for the runtime-certificate family as stated.
-/
theorem no_principal_type {signature : FrozenSig} :
    ¬ ∃ principal : Ty,
        RuntimeTyping signature [] pairProgram principal ∧
        ∀ target : Ty,
          RuntimeTyping signature [] pairProgram target →
          ∃ S : Subst, S.apply principal = target := by
  rintro ⟨principal, principalTyping, instances⟩
  obtain ⟨S₁, prodInstance⟩ := instances _ pair_prod_typing
  obtain ⟨S₂, matcherInstance⟩ := instances _ pair_matcher_typing
  rcases tuple_ty_head principalTyping with
    ⟨components, rfl⟩ | ⟨capability, targetTy, rfl⟩ |
      ⟨capability, targetTy, rfl⟩
  · obtain ⟨applied, appliedEq⟩ := apply_prod_head S₂ components
    rw [appliedEq] at matcherInstance
    cases matcherInstance
  · obtain ⟨appliedCap, appliedTarget, appliedEq⟩ :=
      apply_matcher_head S₁ capability targetTy
    rw [appliedEq] at prodInstance
    cases prodInstance
  · obtain ⟨appliedCap, appliedTarget, appliedEq⟩ :=
      apply_slot_head S₁ capability targetTy
    rw [appliedEq] at prodInstance
    cases prodInstance

end PrincipalityCounterexample
end TypePM
