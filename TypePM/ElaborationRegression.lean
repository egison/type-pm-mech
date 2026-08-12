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
  .prod [.matcher .any .int, .matcher .any .int]

def pairMatcherType : Ty :=
  .matcher (.prod [.any, .any]) (.prod [.int, .int])

def letPairProgram : Expr :=
  .letE "pairMatcher" pairProgram (.var "pairMatcher")

theorem pair_synthesizes_product {signature : FrozenSig} :
    SynthHead signature [] pairProgram
      (.prod [.matcher .any .int, .matcher .any .int]) :=
  .tuple (.cons TypingInvariant.something (.cons TypingInvariant.something .nil))

theorem pair_product_matcher_plan {signature : FrozenSig} :
    CoercionPlan signature [] pairProgram
      (.prod [.matcher .any .int, .matcher .any .int])
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  .productMatcher
    (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])

theorem pair_product_matcher_replays {signature : FrozenSig} :
    TypingInvariant signature [] pairProgram
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  pair_product_matcher_plan.toTypingInvariant pair_synthesizes_product.toTypingInvariant

theorem pair_typingInvariant_factor_exists {signature : FrozenSig} :
    ∃ source,
      SynthHead signature [] pairProgram source ∧
      CoercionPlan signature [] pairProgram source
        (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  ⟨pairProductType, pair_synthesizes_product, pair_product_matcher_plan⟩

/-- The generalized unary product lift can be inserted at a variable use,
after the ordinary product has crossed a `let` boundary.  The former
tuple-literal-only rule could not express this elaboration. -/
theorem let_bound_pair_checks_as_product_matcher {signature : FrozenSig} :
    TypingInvariant signature [] letPairProgram pairMatcherType := by
  have pairScheme :
      signature.generalize [] pairProductType = Scheme.mono pairProductType := by
    have capClosed : pairProductType.fcv = [] := by rfl
    have targetClosed : pairProductType.ftv = [] := by rfl
    unfold FrozenSig.generalize Scheme.generalize
    have capBinders :
        generalizedCapVars (signature.fcv ++ Context.fcv [])
          pairProductType = [] := by
      simp [generalizedCapVars, capClosed, uniqueVars]
    have tyBinders :
        generalizedTyVars (signature.ftv ++ Context.ftv [])
          pairProductType = [] := by
      simp [generalizedTyVars, targetClosed, uniqueVars]
    rw [capBinders, tyBinders]
    simp [Scheme.close, Scheme.mono, pairProductType, PolyTy.abstract,
      PolyTy.lift, PolyCap.abstract, PolyCap.lift]
  have variableTyping :
      TypingInvariant signature
        [("pairMatcher", signature.generalize [] pairProductType)]
        (.var "pairMatcher") pairProductType := by
    apply TypingInvariant.var
      (scheme := signature.generalize [] pairProductType)
    · simp [Context.find?, pairScheme]
    · rw [pairScheme]
      exact Scheme.mono_valueFlowInst pairProductType
  simpa [letPairProgram, pairProductType, pairMatcherType] using
    TypingInvariant.letE (pair_prod_typing (signature := signature))
      (TypingInvariant.coerceProductMatcher
        (duals := [⟨.any, .int⟩, ⟨.any, .int⟩]) variableTyping)

end ElaborationRegression
end TypePM
