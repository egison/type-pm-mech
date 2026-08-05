import TypePM.DynamicSafetyRegression

/-!
# Dynamic value-pattern-pattern capture regression

This regression drives the legal `#$captured` path through concrete
primitive-pattern matching and one matcher-state reduction.  Unlike the
standalone order checks, it reaches `CoreSafety.stepPreservation` from an
`AtomTy.mk` state, so the proof of the matcher step consumes the
`captureAdm_of_coreOrder` value-pattern branch.

The first matcher clause has no holes and is followed by the mandatory bare
hole catch-all.  Its decomposition is therefore a singleton list containing
the empty tuple, while its next-matcher expression is the empty tuple.
-/

namespace TypePM
namespace DynamicCaptureRegression

abbrev signature : FrozenSig := DynamicSafetyRegression.signature

abbrev runtimeSignature : RuntimeSigF :=
  DynamicSafetyRegression.runtimeSignature

theorem signature_wf : FrozenSigWF signature :=
  DynamicSafetyRegression.signature_wf

theorem global_runtime_agreement :
    ∀ context, RuntimeSigAgrees signature context runtimeSignature :=
  DynamicSafetyRegression.global_runtime_agreement

def capturedPattern : Pattern :=
  .pval (.lit 5)

def unitDecompositionExpression : Expr :=
  .ctor "cons" [.tuple [], .ctor "nil" []]

def unitDecompositionValue : Value :=
  .ctor "cons" [.tuple [], .ctor "nil" []]

def capturedClause : Clause :=
  .mk (.pval "captured") (.tuple [])
    [.mk (.var "whole") unitDecompositionExpression]

def catchAllClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole")
      (.ctor "cons" [.var "whole", .ctor "nil" []])]

def clauses : List Clause :=
  [capturedClause, catchAllClause]

def program : Expr :=
  .matchAll (.lit 7) (.matcher clauses) capturedPattern (.lit 1)

def matcherValue : Value :=
  .matcherV [] clauses clauses

def initialAtom : Atom :=
  ⟨capturedPattern, matcherValue, .lit 7⟩

def initialState : MState :=
  ⟨[.atom initialAtom], [], []⟩

def terminalState : MState :=
  ⟨[], [], []⟩

/-! ## Concrete operational path -/

theorem captured_expression_evaluation :
    Eval runtimeSignature [] (.lit 5) (.lit 5) :=
  .lit

theorem primitive_pattern_capture :
    PPM runtimeSignature [] (.pval "captured") capturedPattern
      (some ([], [("captured", .lit 5)])) := by
  simpa [capturedPattern] using
    (PPM.pval (name := "captured") captured_expression_evaluation)

theorem unit_decomposition_evaluation :
    Eval runtimeSignature
      [("whole", .lit 7), ("captured", .lit 5)]
      unitDecompositionExpression unitDecompositionValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .tuple rfl (by simp)
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

theorem matcher_reduction :
    MAtom runtimeSignature [] capturedPattern matcherValue (.lit 7)
      [[]] [] := by
  simpa [runtimeSignature, capturedPattern, matcherValue, clauses,
    capturedClause, catchAllClause, unitDecompositionExpression,
    unitDecompositionValue, listOfV, decodeTuple, pdMatch] using
    (MAtom.matcher (SF := runtimeSignature)
      (ρ := []) (ρm := []) (original := clauses)
      (pattern := capturedPattern) (value := Value.lit 7)
      (pp := PPat.pval "captured") (next := Expr.tuple [])
      (dp := DPat.var "whole") (body := unitDecompositionExpression)
      (arms := []) (clauses := [catchAllClause])
      (holes := []) (ρp := [("captured", Value.lit 5)])
      (ρd := [("whole", Value.lit 7)])
      (decomposition := unitDecompositionValue)
      (tuples := [Value.tuple []]) (valueLists := [[]])
      (matcherValue := Value.tuple []) (matchers := [])
      rfl primitive_pattern_capture rfl unit_decomposition_evaluation
      rfl rfl (Eval.tuple rfl (by simp)) rfl)

theorem state_step :
    Step runtimeSignature initialState [terminalState] := by
  simpa [initialState, initialAtom, terminalState, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := []) matcher_reduction)

theorem state_search :
    Search runtimeSignature initialState [[]] := by
  refine Search.step (substitutions := [[[]]]) state_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .done
  · simp at member

theorem state_reaches_terminal :
    Reaches runtimeSignature initialState terminalState :=
  .step state_step (by simp) .refl

/-! ## Public inference and the typed initial state -/

private theorem option_eq_some_get_of_isSome {alpha : Type}
    (value : Option alpha) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => simp at present
  | some result => rfl

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] program).get (by native_decide)

theorem inference_success :
    Inference.infer signature [] program = some inferenceResult :=
  option_eq_some_get_of_isSome _ (by native_decide)

/-- Pin the observable result of the public certified inference run. -/
theorem inference_result_type :
    inferenceResult.resolvedTarget = Ty.listT .int := by
  native_decide

theorem program_typed :
    HasTy signature [] program (Ty.listT .int) := by
  have typing := Inference.infer_success_sound inference_success
  rw [inference_result_type] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

theorem target_evaluation :
    Eval runtimeSignature [] (.lit 7) (.lit 7) :=
  .lit

theorem matcher_evaluation :
    Eval runtimeSignature [] (.matcher clauses) matcherValue := by
  exact .matcher

theorem target_evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature target_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement target_evaluation

theorem matcher_evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature matcher_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement matcher_evaluation

theorem primitive_pattern_capture_mirror :
    PPMRuntimeSigAgrees signature runtimeSignature primitive_pattern_capture :=
  PPMRuntimeSigAgrees.of_global global_runtime_agreement
    primitive_pattern_capture

theorem matcher_reduction_mirror :
    MAtomRuntimeSigAgrees signature runtimeSignature matcher_reduction :=
  MAtomRuntimeSigAgrees.of_global global_runtime_agreement matcher_reduction

theorem state_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature state_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement state_step

theorem state_search_mirror :
    SearchRuntimeSigAgrees signature runtimeSignature state_search :=
  SearchRuntimeSigAgrees.of_global global_runtime_agreement state_search

theorem state_reachability_mirror :
    ReachesRuntimeSigAgrees signature runtimeSignature
      state_reaches_terminal :=
  ReachesRuntimeSigAgrees.of_global global_runtime_agreement
    state_reaches_terminal

def safetyPackage : CoreSafety signature runtimeSignature :=
  core_safety signature_wf

private theorem empty_environment_typed : EnvTyped signature [] [] := by
  intro name value found
  simp [Env.find?] at found

/-- The initial state uses the structural atom rule, not the target-only
`AtomTy.primitive` shortcut. -/
theorem initial_atom_typed :
    AtomTy signature [] [] [] initialAtom [] := by
  cases program_typed with
  | matchAll targetTyping patternTyping matcherTyping bodyTyping =>
      have outputEquality := patternTyping.pval_inversion.1
      rw [outputEquality] at patternTyping
      have targetValueTyping := safetyPackage.evalPreservation
        target_evaluation_mirror EnvPristine.nil empty_environment_typed
        targetTyping
      have matcherValueTyping := safetyPackage.evalPreservation
        matcher_evaluation_mirror EnvPristine.nil empty_environment_typed
        matcherTyping
      exact .mk patternTyping (.inr matcherValueTyping) targetValueTyping

theorem initial_state_typed :
    MStateTyAt signature [] [] initialState [] := by
  simpa [initialState, initialAtom, matcherValue] using
    initial_atom_typed.initialState_typed EnvPristine.nil
      (.matcherLiteral EnvPristine.nil) .lit empty_environment_typed

/-- Applying public step preservation to the concrete `MAtom.matcher` step
forces its proof through the legal `#$captured` admissibility branch. -/
theorem terminal_state_typed :
    MStateTyAt signature [] [] terminalState [] :=
  safetyPackage.stepPreservation state_step_mirror
    (global_runtime_agreement []) initial_state_typed terminalState (by simp)

end DynamicCaptureRegression
end TypePM
