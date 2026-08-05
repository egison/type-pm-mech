import TypePM.RecursiveExamples

/-!
# Pattern-constructor consumer-capability fallback regression

This focused fixture isolates the fallback needed by `cons $x $rest`.
Independent fresh child consumers hide the sharing in the generic constructor
signature from exact projection.  The fallback allocates one shared result
leaf, constrains only those consumers, and then succeeds through the same exact
projection and compatibility checks used by reconstruction.
-/

namespace TypePM
namespace PatternCtorCapabilityRegression

open Inference

/-- Two independently inferred pattern-variable capabilities. -/
def childCapabilities : List Cap := [.var 0, .var 1]

/-- The fallback starts above the two child metas and carries an unrelated
protected producer entry whose ledger must not be changed. -/
def initialState : InferState :=
  { InferState.empty { nextCap := 2, nextTy := 1 } with
    protectedCaps := [99] }

def origin : ConstraintOrigin :=
  { phase := .pattern
    path := []
    label := "pattern-constructor-fallback-regression" }

/-- Exact projection cannot see that the second independent leaf must have a
`List` head sharing the first leaf. -/
theorem exact_projection_of_independent_children_fails :
    Projection.projectSignature RecursiveExamples.consProjection
      (childCapabilities.map Shape.ofCap) = none := by
  native_decide

def fallbackResult : Cap × InferState :=
  (solvePatternCtorCapability RecursiveExamples.listSignature
      RecursiveExamples.consPatternCtor origin childCapabilities initialState).get
    (by native_decide)

private theorem option_eq_some_get_of_isSome {alpha : Type}
    (value : Option alpha) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => simp at present
  | some result => rfl

/-- The consumer-side fallback succeeds from precisely the state for which the
old exact path above failed. -/
theorem fallback_succeeds :
    solvePatternCtorCapability RecursiveExamples.listSignature
      RecursiveExamples.consPatternCtor origin childCapabilities initialState =
        some fallbackResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

/-- The allocated shared result leaf is `kappa = ?2`; after replay, the two
child demands are exactly `kappa` and `List kappa`. -/
theorem fallback_zonks_shared_children :
    (childCapabilities.map fun capability =>
        capability.apply fallbackResult.2.prevailing.cap) =
      [.var 2, .con "List" [.var 2]] := by
  native_decide

/-- Exact projection after solving returns the corresponding outer
`List kappa` capability. -/
theorem fallback_zonks_shared_result :
    fallbackResult.1.apply fallbackResult.2.prevailing.cap =
      .con "List" [.var 2] := by
  native_decide

/-- The same locally zonked values pass the exact compatibility check that is
repeated by the terminal validator. -/
theorem fallback_final_compatibility :
    capCompatibleCheck RecursiveExamples.consPatternCtor
      (childCapabilities.map fun capability =>
        capability.apply fallbackResult.2.prevailing.cap)
      (fallbackResult.1.apply fallbackResult.2.prevailing.cap) = true := by
  native_decide

/-- Solving consumer capabilities neither adds nor removes producer-ledger
entries. -/
theorem fallback_preserves_protected_ledger :
    fallbackResult.2.protectedCaps = initialState.protectedCaps := by
  native_decide

/-- Every generated delta also fixes the unrelated protected producer. -/
theorem fallback_trace_preserves_protected_producer :
    protectedProducerTraceCheck fallbackResult.2 = true := by
  native_decide

end PatternCtorCapabilityRegression
end TypePM
