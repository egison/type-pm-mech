import TypePM.DynamicDispatchRegression
import TypePM.Readiness

/-!
# Readiness-construction regression

This file exercises `MStateTy.progress_of_evals` on the typed ordered-dispatch
fixture: the pair pattern `pair $x $rest` against the three-clause matcher
whose first clause shape-fails, whose live clause has a failing data arm
before the successful one, and whose mandatory catch-all is last.

The point of the fixture is what it does *not* provide: no `MAtomReady` or
`StepReady` value, no decode successes, and no identification of the
committed clause or arm are constructed here.  Only the embedded evaluations
are supplied — the value expressions captured by shape-compatible clause
headers (here none), each receivable arm's decomposition body, and each
shape-compatible clause's next-matcher expression — and the readiness
construction derives the step from the typing evidence alone.
-/

namespace TypePM
namespace ReadinessRegression

open DynamicDispatchRegression.TypedFixture

/-- The successful arm's decomposition evaluates under the data bindings for
every capture environment: its variables resolve in the data prefix. -/
theorem decomposition_evaluation_any (ppEnvironment : Env) :
    Eval runtimeSignature (dataEnvironment ++ ppEnvironment ++ [])
      decompositionExpression decompositionValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · refine Eval.tuple rfl ?_
    intro pair member
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact .var (by rfl)
    · rcases member with rfl | member
      · exact .var (by rfl)
      · simp at member
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

/-- The irrefutable arm's constant body evaluates in every environment. -/
theorem exhaustive_body_evaluation (environment : Env) :
    Eval runtimeSignature environment (.ctor "nil" []) nilValue := by
  exact .ctor rfl (by simp)

/-- The catch-all arm's body evaluates under its whole-value binding for
every capture environment. -/
theorem catchAll_body_evaluation (ppEnvironment : Env) :
    Eval runtimeSignature
      ([("whole", targetValue)] ++ ppEnvironment ++ [])
      (.ctor "cons" [.var "whole", .ctor "nil" []])
      (.ctor "cons" [targetValue, .ctor "nil" []]) := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .var (by rfl)
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

/-- The dispatch-site convergence package for the fixture's matcher. -/
theorem dispatch_evals :
    MatcherDispatchEvals signature runtimeSignature [] [] userPattern
      targetValue clauses := by
  refine ⟨?_, ?_, ?_⟩
  · intro clause member shape expression exprMember
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [emptyClause, Clause.pp, generalPP, userPattern, ppShapeOK] at shape
    · simp [livePairClause, Clause.pp, generalPP, userPattern,
        List.replicate, capturedExprs, capturedExprsList] at exprMember
    · simp [catchAllClause, Clause.pp, capturedExprs] at exprMember
  · intro clause member shape captures ppEnvironment ppm arm armMember
      dataEnvironment' dataEq
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [emptyClause, Clause.pp, generalPP, userPattern, ppShapeOK] at shape
    · simp only [livePairClause, Clause.arms, List.mem_cons,
        List.not_mem_nil, or_false] at armMember
      rcases armMember with rfl | rfl | rfl
      · simp [failingDataArm, Arm.pat, pdMatch, targetValue] at dataEq
      · have dataEnvEq : dataEnvironment' = dataEnvironment :=
          (Option.some.inj (second_data_arm_success.symm.trans dataEq)).symm
        subst dataEnvEq
        exact ⟨_, decomposition_evaluation_any ppEnvironment,
          EvalRuntimeSigAgrees.of_global global_runtime_agreement _⟩
      · have dataEnvEq : dataEnvironment' = [] := by
          simpa [exhaustiveDataArm, Arm.pat, pdMatch] using dataEq.symm
        subst dataEnvEq
        exact ⟨_, exhaustive_body_evaluation _,
          EvalRuntimeSigAgrees.of_global global_runtime_agreement _⟩
    · simp only [catchAllClause, Clause.arms, List.mem_cons,
        List.not_mem_nil, or_false] at armMember
      subst armMember
      have dataEnvEq : dataEnvironment' = [("whole", targetValue)] := by
        simpa [Arm.pat, pdMatch] using dataEq.symm
      subst dataEnvEq
      exact ⟨_, catchAll_body_evaluation ppEnvironment,
        EvalRuntimeSigAgrees.of_global global_runtime_agreement _⟩
  · intro clause member shape
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [emptyClause, Clause.pp, generalPP, userPattern, ppShapeOK] at shape
    · exact ⟨_, next_matchers_evaluation,
        EvalRuntimeSigAgrees.of_global global_runtime_agreement _⟩
    · exact ⟨_, Eval.something,
        EvalRuntimeSigAgrees.of_global global_runtime_agreement _⟩

/-- Atom-level convergence for the fixture's initial atom. -/
theorem initial_atom_evals :
    AtomEvals signature runtimeSignature []
      ⟨userPattern, matcherValue, targetValue⟩ := by
  refine ⟨?_, ?_⟩
  · intro expression patternEq _
    simp [userPattern] at patternEq
  · intro matcherEnvironment original current matcherEq
    simp only [matcherValue] at matcherEq
    injection matcherEq with environmentEq originalEq currentEq
    subst environmentEq
    subst originalEq
    subst currentEq
    exact dispatch_evals

/-- State-level convergence for the fixture's initial matching state. -/
theorem initial_evals :
    StateEvals signature runtimeSignature initialState := by
  intro tree rest treeEq
  rcases List.cons.inj treeEq with ⟨rfl, rfl⟩
  exact .atom initial_atom_evals

/--
The readiness construction fires end to end: the typed initial state takes a
concrete step from the convergence package alone, without a hand-built
`StepReady` value, decode success, or committed clause/arm.
-/
theorem initial_progress :
    ∃ states, Step runtimeSignature initialState states := by
  obtain ⟨goal, typed⟩ := initial_state_typed
  exact MStateTy.progress_of_evals signature_wf (runtime_agrees [])
    typed (by simp [initialState]) initial_evals

end ReadinessRegression
end TypePM
