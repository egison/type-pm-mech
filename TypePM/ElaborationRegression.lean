import TypePM.Elaboration
import TypePM.PrincipalityCounterexample

/-!
# Surface/core factorization regressions

The principality counterexample remains a negative result for plain surface
types.  These regressions pin its positive reinterpretation: the product type
is synthesized before coercion, and the product-matcher view is carried by an
explicit plan.
-/

namespace TypePM
namespace ElaborationRegression

open PrincipalityCounterexample
open Elaboration

def pairProductType : Ty :=
  .prod [.matcher .none .int, .matcher .none .int]

def pairMatcherType : Ty :=
  .matcher (.prod [.none, .none]) (.prod [.int, .int])

def letPairProgram : Expr :=
  .letE "pairMatcher" pairProgram (.var "pairMatcher")

theorem pair_synthesizes_product {signature : FrozenSig} :
    SynthHead signature [] pairProgram
      (.prod [.matcher .none .int, .matcher .none .int]) :=
  .tuple (.cons HasTy.something (.cons HasTy.something .nil))

theorem pair_product_matcher_plan {signature : FrozenSig} :
    CoercionPlan signature [] pairProgram
      (.prod [.matcher .none .int, .matcher .none .int])
      (.matcher (.prod [.none, .none]) (.prod [.int, .int])) :=
  .productMatcher
    (duals := [⟨.none, .int⟩, ⟨.none, .int⟩])

theorem pair_product_matcher_replays {signature : FrozenSig} :
    HasTy signature [] pairProgram
      (.matcher (.prod [.none, .none]) (.prod [.int, .int])) :=
  pair_product_matcher_plan.toHasTy pair_synthesizes_product.toHasTy

theorem pair_surface_factor_exists {signature : FrozenSig} :
    ∃ source,
      SynthHead signature [] pairProgram source ∧
      CoercionPlan signature [] pairProgram source
        (.matcher (.prod [.none, .none]) (.prod [.int, .int])) :=
  HasTy.factorHead pair_matcher_typing

/-- The generalized unary product lift can be inserted at a variable use,
after the ordinary product has crossed a `let` boundary.  The former
tuple-literal-only rule could not express this elaboration. -/
theorem let_bound_pair_checks_as_product_matcher {signature : FrozenSig} :
    HasTy signature [] letPairProgram pairMatcherType := by
  have pairScheme :
      signature.generalize [] pairProductType = Scheme.mono pairProductType := by
    have capClosed : pairProductType.fcv = [] := by rfl
    have targetClosed : pairProductType.ftv = [] := by rfl
    simp [FrozenSig.generalize, TypePM.generalize, capClosed, targetClosed,
      uniqueVars, Scheme.mono]
  have variableTyping :
      HasTy signature
        [("pairMatcher", signature.generalize [] pairProductType)]
        (.var "pairMatcher") pairProductType := by
    apply HasTy.var
      (scheme := signature.generalize [] pairProductType)
    · simp [Context.find?, pairScheme]
    · rw [pairScheme]
      exact Scheme.mono_valueFlowInst pairProductType
  simpa [letPairProgram, pairProductType, pairMatcherType] using
    HasTy.letE (pair_prod_typing (signature := signature))
      (HasTy.coerceProductMatcher
        (duals := [⟨.none, .int⟩, ⟨.none, .int⟩]) variableTyping)

end ElaborationRegression
end TypePM
