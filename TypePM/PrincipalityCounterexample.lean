import TypePM.Source

/-!
# Principality fails for the two-sort declarative system

This module settles the negative side of the principality question.  The
closed expression `(something, something)` is derivably

* a product of matchers, by `T-TUPLE`, and
* a product matcher, by `COERCE-TUPLE-MATCHER`,

and these two derivable types have different head constructors (`prod`
versus `matcher`).  Every derivable type of a tuple expression has a
`prod`, `matcher`, or `slot` head, and paired substitution preserves each
of these heads, so no derivable type of this expression has both typings
among its substitution instances.  Hence no principal type exists.

The counterexample is not exotic: usable product matchers require exactly
this coercion overlap, and the failure is independent of capability
evidence.  It delimits what a restricted principality statement must
exclude; the pattern-free fragment of `TypePM.DamasMilner` contains no
coercion rule and is unaffected.
-/

namespace TypePM
namespace PrincipalityCounterexample

/-- The two-element tuple of `something` matchers. -/
def pairProgram : Expr :=
  .tuple [.something, .something]

/-- Its product-of-matchers typing, by `T-TUPLE`. -/
theorem pair_prod_typing {signature : FrozenSig} :
    HasTy signature [] pairProgram
      (.prod [.matcher .none .int, .matcher .none .int]) :=
  HasTy.tuple (.cons HasTy.something (.cons HasTy.something .nil))

/-- Its product-matcher typing, by `COERCE-TUPLE-MATCHER`. -/
theorem pair_matcher_typing {signature : FrozenSig} :
    HasTy signature [] pairProgram
      (.matcher (.prod [.none, .none]) (.prod [.int, .int])) :=
  HasTy.coerceTupleMatcher
    (duals := [⟨.none, .int⟩, ⟨.none, .int⟩])
    (.cons HasTy.something (.cons HasTy.something .nil))

/-- Every derivable type of a tuple has a `prod`, `matcher`, or `slot` head. -/
theorem tuple_ty_head {signature : FrozenSig} {context : Context}
    {expressions : List Expr} {target : Ty}
    (typing : HasTy signature context (.tuple expressions) target) :
    (∃ components, target = .prod components) ∨
    (∃ capability targetTy, target = .matcher capability targetTy) ∨
    (∃ capability targetTy, target = .slot capability targetTy) := by
  cases typing with
  | tuple _ => exact .inl ⟨_, rfl⟩
  | coerceTupleMatcher _ => exact .inr (.inl ⟨_, _, rfl⟩)
  | coerceMatcherToSlot _ _ _ => exact .inr (.inr ⟨_, _, rfl⟩)
  | checkSlotToSlot _ _ _ => exact .inr (.inr ⟨_, _, rfl⟩)
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
No derivable type of `(something, something)` has both the product typing
and the product-matcher typing among its paired-substitution instances.
Principality therefore fails for the declarative system as stated.
-/
theorem no_principal_type {signature : FrozenSig} :
    ¬ ∃ principal : Ty,
        HasTy signature [] pairProgram principal ∧
        ∀ target : Ty,
          HasTy signature [] pairProgram target →
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
