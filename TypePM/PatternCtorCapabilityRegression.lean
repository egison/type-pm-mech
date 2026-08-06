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

/-- The consumer-side fallback succeeds from precisely the state for which the
old exact path above failed. -/
theorem fallback_succeeds :
    solvePatternCtorCapability RecursiveExamples.listSignature
      RecursiveExamples.consPatternCtor origin childCapabilities initialState =
        some fallbackResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

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

/-! ## Public pattern-constructor acceptance boundary -/

/-- A nullary pattern function whose target fits the tail of `cons`, but whose
fixed product capability cannot satisfy the required `List kappa` demand. -/
def incompatibleTailScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := ⟨.prod [], Ty.listT .int⟩

/-- The control twin differs only in exposing the concrete tail capability
required by the surrounding `cons` pattern. -/
def compatibleTailScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := ⟨.con "List" [.any], Ty.listT .int⟩

/-- Instantiation exposes a fresh capability producer which must remain
protected when it appears as the tail child of `cons`. -/
def protectedTailScheme : DualScheme where
  capBinders := [0]
  tyBinders := []
  args := []
  result := ⟨.var 0, Ty.listT .int⟩

def publicSignature : FrozenSig :=
  { RecursiveExamples.listSignature with
    patternFuns :=
      [("incompatible-tail", incompatibleTailScheme),
        ("compatible-tail", compatibleTailScheme),
        ("protected-tail", protectedTailScheme)] }

/-- A concrete matcher slot keeps these regressions independent of recursive
matcher inference. -/
def publicContext : Context :=
  [("list-slot", Scheme.mono
    (.slot (.con "List" [.any]) (Ty.listT .int)))]

/-- All three public programs share their target, matcher, outer constructor,
and body; only the nullary tail pattern function changes. -/
def publicProgram (tailName : String) : Expr :=
  .matchAll
    (.ctor "cons" [.lit 1, .ctor "nil" []])
    (.var "list-slot")
    (.pctor "cons" [.wild, .papp tailName []])
    (.lit 1)

def incompatibleProgram : Expr :=
  publicProgram "incompatible-tail"

def compatibleProgram : Expr :=
  publicProgram "compatible-tail"

def protectedProgram : Expr :=
  publicProgram "protected-tail"

/-- Target alignment succeeds, but the fixed second-child capability
`.prod []` cannot be made equal to the fallback demand `List kappa`. -/
theorem incompatible_direct_solver_rejected :
    solvePatternCtorCapability publicSignature
      RecursiveExamples.consPatternCtor origin [.any, .prod []] initialState =
        none := by
  native_decide

/-- The incompatibility is rejected by raw W itself. -/
theorem incompatible_raw_inference_rejected :
    Inference.inferRaw publicSignature publicContext incompatibleProgram =
      none := by
  native_decide

/-- Consequently the public certified entry point also rejects the same
source-level pattern-constructor application. -/
theorem incompatible_public_inference_rejected :
    Inference.infer publicSignature publicContext incompatibleProgram = none := by
  native_decide

def compatibleResult : Inference.ExprResult :=
  (Inference.infer publicSignature publicContext compatibleProgram).get
    (by native_decide)

/-- The otherwise identical concrete-capability control reaches the public
success boundary. -/
theorem compatible_public_inference_succeeds :
    Inference.infer publicSignature publicContext compatibleProgram =
      some compatibleResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- Pin both the control result and its unchanged concrete context. -/
theorem compatible_result_type :
    compatibleResult.resolvedTarget = Ty.listT .int := by
  native_decide

theorem compatible_resolved_context :
    Inference.ResolvedContext compatibleResult.state.prevailing publicContext =
      publicContext := by
  native_decide

/-- Public success reconstructs the source typing for the control twin. -/
theorem compatible_typed :
    HasTy publicSignature publicContext compatibleProgram (Ty.listT .int) := by
  have typing := Inference.infer_success_sound
    compatible_public_inference_succeeds
  rw [compatible_result_type, compatible_resolved_context] at typing
  exact typing

/-! ## Protected producer as an actual constructor child -/

/-- Use the production dual-scheme instantiator so the child image and ledger
entry arise together, rather than injecting a protected identifier by hand. -/
def protectedTailInstantiation : (List Dual × Dual) × InferState :=
  instantiateDualInState publicSignature [] [] [] [] [] [] initialState
    protectedTailScheme

def protectedTailDual : Dual :=
  protectedTailInstantiation.1.2

def protectedTailState : InferState :=
  protectedTailInstantiation.2

/-- The fresh image is the expected variable and is appended to the existing
producer ledger. -/
theorem protected_tail_image_recorded :
    protectedTailDual.cap = .var 2 ∧
      protectedTailState.protectedCaps = [99, 2] := by
  native_decide

/-- The raw capability unifier can construct the forbidden strengthening
delta; the producer-protection filter is what rejects it. -/
def protectedStrengtheningStep : SolveStep :=
  (solveResolved protectedTailState.trace.solves.length origin
    (.capEq protectedTailDual.cap (.con "List" [.any]))).get
      (by native_decide)

theorem protected_strengthening_fixes_check_fails :
    capSubstFixesVarsCheck protectedStrengtheningStep.delta.cap
      protectedTailState.protectedCaps = false := by
  native_decide

theorem protected_strengthening_constraint_rejected :
    runResolvedConstraint protectedTailState origin
      (.capEq protectedTailDual.cap (.con "List" [.any])) = none := by
  native_decide

/-- Placing that protected image in the second child makes the fallback demand
`List kappa`; satisfying it would structurally strengthen the producer. -/
theorem protected_child_direct_solver_rejected :
    solvePatternCtorCapability publicSignature
      RecursiveExamples.consPatternCtor origin
      [.any, protectedTailDual.cap] protectedTailState = none := by
  native_decide

/-- The same boundary is reached through an actual nullary `papp` child in the
public source program. -/
theorem protected_child_raw_inference_rejected :
    Inference.inferRaw publicSignature publicContext protectedProgram = none := by
  native_decide

theorem protected_child_public_inference_rejected :
    Inference.infer publicSignature publicContext protectedProgram = none := by
  native_decide

end PatternCtorCapabilityRegression
end TypePM
