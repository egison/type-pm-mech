import TypePM.InterpreterAdequacy
import TypePM.Safety

/-!
# Completeness of the fuel-indexed interpreter

Every finite relational derivation is reproduced by the interpreter once the
fuel is large enough.  The statement is strengthened to persistence above a
finite threshold so sibling derivations can be combined without a separate
fuel-monotonicity proof.
-/

namespace TypePM

/-- A fuel-indexed computation returns the same result at every fuel above a
finite threshold. -/
def EventuallyOk (run : Nat → RunResult α) (result : α) : Prop :=
  ∃ threshold, ∀ extra, run (threshold + extra) = .ok result

/-- Pointwise eventual evaluation drives the executable list traversal. -/
theorem evalListFuel_eventually_of_pointwise
    {SF : RuntimeSigF} {ρ : Env} :
    ∀ {expressions : List Expr} {values : List Value},
      expressions.length = values.length →
      (∀ pair ∈ expressions.zip values,
        EventuallyOk (fun fuel => evalFuel SF fuel ρ pair.1) pair.2) →
      EventuallyOk (fun fuel => evalListFuel SF fuel ρ expressions) values
  | [], [], _, _ => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | expression :: expressions, value :: values, lengths, pointwise => by
      have headEventually := pointwise (expression, value) (by simp)
      have tailEventually := evalListFuel_eventually_of_pointwise
        (Nat.succ.inj lengths) (fun pair membership =>
          pointwise pair (by simp [membership]))
      obtain ⟨headThreshold, headRun⟩ := headEventually
      obtain ⟨tailThreshold, tailRun⟩ := tailEventually
      refine ⟨headThreshold + tailThreshold + 1, ?_⟩
      intro extra
      have head := headRun (tailThreshold + extra)
      have tail := tailRun (headThreshold + extra)
      rw [show headThreshold + tailThreshold + 1 + extra =
          (headThreshold + tailThreshold + extra) + 1 by omega]
      simp only [evalListFuel, RunResult.monad_bind_eq_bind]
      have head' : evalFuel SF (headThreshold + tailThreshold + extra) ρ
          expression = .ok value := by
        simpa [Nat.add_assoc] using head
      have tail' : evalListFuel SF (headThreshold + tailThreshold + extra) ρ
          expressions = .ok values := by
        rw [show headThreshold + tailThreshold + extra =
          tailThreshold + (headThreshold + extra) by omega]
        simpa only using tail
      rw [head']
      simp only [RunResult.bind_ok]
      rw [tail']
      rfl

/-- Pointwise eventual body evaluation drives substitution-list traversal. -/
theorem evalSubstsFuel_eventually_of_pointwise
    {SF : RuntimeSigF} {ρ : Env} {body : Expr} :
    ∀ {substitutions : List MatchSubst} {values : List Value},
      substitutions.length = values.length →
      (∀ pair ∈ substitutions.zip values,
        EventuallyOk
          (fun fuel => evalFuel SF fuel (pair.1 ++ ρ) body) pair.2) →
      EventuallyOk
        (fun fuel => evalSubstsFuel SF fuel ρ body substitutions) values
  | [], [], _, _ => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | substitution :: substitutions, value :: values, lengths, pointwise => by
      have headEventually := pointwise (substitution, value) (by simp)
      have tailEventually := evalSubstsFuel_eventually_of_pointwise
        (Nat.succ.inj lengths) (fun pair membership =>
          pointwise pair (by simp [membership]))
      obtain ⟨headThreshold, headRun⟩ := headEventually
      obtain ⟨tailThreshold, tailRun⟩ := tailEventually
      refine ⟨headThreshold + tailThreshold + 1, ?_⟩
      intro extra
      rw [show headThreshold + tailThreshold + 1 + extra =
          (headThreshold + tailThreshold + extra) + 1 by omega]
      simp only [evalSubstsFuel, RunResult.monad_bind_eq_bind]
      have head' :
          evalFuel SF (headThreshold + tailThreshold + extra)
            (substitution ++ ρ) body = .ok value := by
        simpa [Nat.add_assoc] using headRun (tailThreshold + extra)
      have tail' :
          evalSubstsFuel SF (headThreshold + tailThreshold + extra) ρ body
            substitutions = .ok values := by
        rw [show headThreshold + tailThreshold + extra =
          tailThreshold + (headThreshold + extra) by omega]
        simpa only using tailRun (headThreshold + extra)
      rw [head']
      simp only [RunResult.bind_ok]
      rw [tail']
      rfl

/-- Pointwise eventual primitive-pattern matching drives its list traversal. -/
theorem ppmListFuel_eventually_of_pointwise
    {SF : RuntimeSigF} {ρ : Env} :
    ∀ {pps : List PPat} {patterns : List Pattern}
      {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        EventuallyOk
          (fun fuel => ppmFuel SF fuel ρ entry.1.1 entry.1.2)
          (some entry.2)) →
      EventuallyOk
        (fun fuel => ppmListFuel SF fuel ρ pps patterns) results
  | [], [], [], _, _, _ => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | [], [], _ :: _, _, resultLengths, _ => by simp at resultLengths
  | [], _ :: _, _, lengths, _, _ => by simp at lengths
  | _ :: _, [], _, lengths, _, _ => by simp at lengths
  | pp :: pps, pattern :: patterns, result :: results,
      lengths, resultLengths, pointwise => by
      have headEventually := pointwise ((pp, pattern), result) (by simp)
      have tailEventually := ppmListFuel_eventually_of_pointwise
        (Nat.succ.inj lengths) (Nat.succ.inj resultLengths)
        (fun entry membership => pointwise entry (by simp [membership]))
      obtain ⟨headThreshold, headRun⟩ := headEventually
      obtain ⟨tailThreshold, tailRun⟩ := tailEventually
      refine ⟨headThreshold + tailThreshold + 1, ?_⟩
      intro extra
      rw [show headThreshold + tailThreshold + 1 + extra =
          (headThreshold + tailThreshold + extra) + 1 by omega]
      simp only [ppmListFuel, RunResult.monad_bind_eq_bind]
      have head' :
          ppmFuel SF (headThreshold + tailThreshold + extra) ρ pp pattern =
            .ok (some result) := by
        simpa [Nat.add_assoc] using headRun (tailThreshold + extra)
      have tail' :
          ppmListFuel SF (headThreshold + tailThreshold + extra) ρ pps
            patterns = .ok results := by
        rw [show headThreshold + tailThreshold + extra =
          tailThreshold + (headThreshold + extra) by omega]
        simpa only using tailRun (headThreshold + extra)
      rw [head']
      simp only [RunResult.bind_ok]
      rw [tail']
      rfl
  | _ :: _, _ :: _, [], _, resultLengths, _ => by simp at resultLengths

/-- Pointwise eventual search drives successor-list traversal. -/
theorem searchListFuel_eventually_of_pointwise
    {SF : RuntimeSigF} :
    ∀ {states : List MState}
      {substitutions : List (List MatchSubst)},
      states.length = substitutions.length →
      (∀ pair ∈ states.zip substitutions,
        EventuallyOk (fun fuel => searchFuel SF fuel pair.1) pair.2) →
      EventuallyOk
        (fun fuel => searchListFuel SF fuel states) substitutions
  | [], [], _, _ => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | state :: states, result :: results, lengths, pointwise => by
      have headEventually := pointwise (state, result) (by simp)
      have tailEventually := searchListFuel_eventually_of_pointwise
        (Nat.succ.inj lengths) (fun pair membership =>
          pointwise pair (by simp [membership]))
      obtain ⟨headThreshold, headRun⟩ := headEventually
      obtain ⟨tailThreshold, tailRun⟩ := tailEventually
      refine ⟨headThreshold + tailThreshold + 1, ?_⟩
      intro extra
      rw [show headThreshold + tailThreshold + 1 + extra =
          (headThreshold + tailThreshold + extra) + 1 by omega]
      simp only [searchListFuel, RunResult.monad_bind_eq_bind]
      have head' :
          searchFuel SF (headThreshold + tailThreshold + extra) state =
            .ok result := by
        simpa [Nat.add_assoc] using headRun (tailThreshold + extra)
      have tail' :
          searchListFuel SF (headThreshold + tailThreshold + extra) states =
            .ok results := by
        rw [show headThreshold + tailThreshold + extra =
          tailThreshold + (headThreshold + extra) by omega]
        simpa only using tailRun (headThreshold + extra)
      rw [head']
      simp only [RunResult.bind_ok]
      rw [tail']
      rfl

/-- For a dispatchable pattern, eventual atom success against a matcher value
is exactly eventual success of the clause cursor, one fuel level below. -/
theorem dispatchFuel_eventually_of_matom
    {SF : RuntimeSigF} {ρ matcherEnv : Env} {original current : List Clause}
    {pattern : Pattern} {value : Value}
    {continuations : List (List Atom)} {new : MatchSubst}
    (dispatchable : pattern.isMatcherDispatchable = true)
    (eventual : EventuallyOk
      (fun fuel => matomFuel SF fuel ρ pattern
        (.matcherV matcherEnv original current) value)
      (continuations, new)) :
    EventuallyOk
      (fun fuel => dispatchFuel SF fuel ρ matcherEnv pattern value current)
      (continuations, new) := by
  obtain ⟨threshold, run⟩ := eventual
  refine ⟨threshold, ?_⟩
  intro extra
  have lifted := run (extra + 1)
  cases pattern <;>
    simp [Pattern.isMatcherDispatchable, matomFuel] at dispatchable lifted ⊢ <;>
    assumption

/-- A positive-fuel atom run against a matcher value enters the dispatch
cursor exactly when the pattern is dispatchable. -/
theorem matomFuel_matcher_eq
    {SF : RuntimeSigF} {fuel : Nat} {ρ matcherEnv : Env}
    {original current : List Clause} {pattern : Pattern} {value : Value}
    (dispatchable : pattern.isMatcherDispatchable = true) :
    matomFuel SF (fuel + 1) ρ pattern
        (.matcherV matcherEnv original current) value =
      dispatchFuel SF fuel ρ matcherEnv pattern value current := by
  cases pattern <;>
    simp [Pattern.isMatcherDispatchable, matomFuel] at dispatchable ⊢

/-- The `mnode` step equation also holds when an embedded head is known to
miss the parameter environment. -/
theorem stepFuel_mnode_guard_eq
    {SF : RuntimeSigF} {fuel : Nat} {stack : List Tree} {ρ : Env}
    {substitution : MatchSubst} {tree : Tree} {innerStack : List Tree}
    {innerEnv : Env} {innerSubst : MatchSubst} {piE : PiEnv}
    (guard : ∀ name matcher value,
      tree = .atom ⟨.embed name, matcher, value⟩ →
      List.find? (fun entry => entry.1 == name) piE = none) :
    stepFuel SF (fuel + 1)
      ⟨.mnode (tree :: innerStack) innerEnv innerSubst piE :: stack,
        ρ, substitution⟩ =
      (do
        let states ← stepFuel SF fuel
          ⟨tree :: innerStack, innerEnv, innerSubst⟩
        pure (states.map fun state =>
          ⟨.mnode state.S innerEnv state.θ piE :: stack,
            ρ, substitution⟩)) := by
  cases tree with
  | mnode trees environment substitution' parameters => rfl
  | atom atom =>
      obtain ⟨pattern, matcher, value⟩ := atom
      cases pattern with
      | embed name => simp [stepFuel, guard name matcher value rfl]
      | pvar name => rfl
      | wild => rfl
      | pval expression => rfl
      | pctor name patterns => rfl
      | pand left right => rfl
      | por left right => rfl
      | papp name arguments => rfl
      | ptuple patterns => rfl

/-- A relational step witnesses that the search state is nonterminal, exposing
the executable search equation without a separate syntactic case split. -/
theorem searchFuel_step_eq
    {SF : RuntimeSigF} {fuel : Nat} {state : MState} {states : List MState}
    (reduction : Step SF state states) :
    searchFuel SF (fuel + 1) state =
      (do
        let next ← stepFuel SF fuel state
        let results ← searchListFuel SF fuel next
        pure results.flatten) := by
  cases reduction <;> rfl

/-- Eventual atom success at a cursor whose first clause has already matched
its header yields eventual success of that clause's arm cursor. -/
theorem armsFuel_eventually_of_matom
    {SF : RuntimeSigF} {ρ matcherEnv : Env} {original clauses : List Clause}
    {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
    {arms : List Arm} {holes : List Pattern} {ppEnv : Env}
    {continuations : List (List Atom)} {new : MatchSubst}
    (dispatchable : pattern.isMatcherDispatchable = true)
    (headerEventually : EventuallyOk
      (fun fuel => ppmFuel SF fuel ρ pp pattern) (some (holes, ppEnv)))
    (atomEventually : EventuallyOk
      (fun fuel => matomFuel SF fuel ρ pattern
        (.matcherV matcherEnv original (.mk pp next arms :: clauses)) value)
      (continuations, new)) :
    EventuallyOk
      (fun fuel => armsFuel SF fuel ρ matcherEnv value next holes ppEnv arms)
      (continuations, new) := by
  obtain ⟨headerThreshold, headerRun⟩ := headerEventually
  obtain ⟨atomThreshold, atomRun⟩ := atomEventually
  refine ⟨headerThreshold + atomThreshold, ?_⟩
  intro extra
  let common := headerThreshold + atomThreshold + extra
  have header : ppmFuel SF common ρ pp pattern = .ok (some (holes, ppEnv)) := by
    dsimp [common]
    simpa [Nat.add_assoc] using headerRun (atomThreshold + extra)
  have atom :
      matomFuel SF (common + 2) ρ pattern
        (.matcherV matcherEnv original (.mk pp next arms :: clauses)) value =
        .ok (continuations, new) := by
    dsimp [common]
    rw [show headerThreshold + atomThreshold + extra + 2 =
      atomThreshold + (headerThreshold + extra + 2) by omega]
    exact atomRun (headerThreshold + extra + 2)
  rw [show common + 2 = (common + 1) + 1 by omega,
    matomFuel_matcher_eq dispatchable] at atom
  simp only [dispatchFuel, RunResult.monad_bind_eq_bind] at atom
  rw [header] at atom
  simpa only [RunResult.bind_ok] using atom

mutual

/-- Every finite expression-evaluation derivation is reproduced persistently
above a finite fuel threshold. -/
theorem evalFuel_eventually_ok
    {SF : RuntimeSigF} {ρ : Env} {expression : Expr} {value : Value} :
    ∀ (_ : Eval SF ρ expression value),
      EventuallyOk (fun fuel => evalFuel SF fuel ρ expression) value
  | .var found => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      simp [evalFuel, found]
  | .lam | .fix | .lit | .something | .matcher => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | .app functionEvaluation argumentEvaluation bodyEvaluation => by
      obtain ⟨fnThreshold, fnRun⟩ :=
        evalFuel_eventually_ok functionEvaluation
      obtain ⟨argThreshold, argRun⟩ :=
        evalFuel_eventually_ok argumentEvaluation
      obtain ⟨bodyThreshold, bodyRun⟩ :=
        evalFuel_eventually_ok bodyEvaluation
      refine ⟨fnThreshold + argThreshold + bodyThreshold + 1, ?_⟩
      intro extra
      let common := fnThreshold + argThreshold + bodyThreshold + extra
      rw [show fnThreshold + argThreshold + bodyThreshold + 1 + extra =
        common + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have fnResult := fnRun (argThreshold + bodyThreshold + extra)
      have argResult := argRun (fnThreshold + bodyThreshold + extra)
      have bodyResult := bodyRun (fnThreshold + argThreshold + extra)
      dsimp [common]
      simp only at fnResult argResult bodyResult
      rw [show fnThreshold + argThreshold + bodyThreshold + extra =
        fnThreshold + (argThreshold + bodyThreshold + extra) by omega,
        fnResult]
      simp only [RunResult.bind_ok]
      rw [show fnThreshold + (argThreshold + bodyThreshold + extra) =
        argThreshold + (fnThreshold + bodyThreshold + extra) by omega,
        argResult]
      simp only [RunResult.bind_ok]
      rw [show argThreshold + (fnThreshold + bodyThreshold + extra) =
        bodyThreshold + (fnThreshold + argThreshold + extra) by omega]
      exact bodyResult
  | @Eval.tuple _ ρ exprs values lengths evaluations => by
      have listEventually := evalListFuel_eventually_of_pointwise lengths
        (fun pair membership =>
          evalFuel_eventually_ok (evaluations pair membership))
      obtain ⟨threshold, run⟩ := listEventually
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have result : evalListFuel SF (threshold + extra) ρ exprs =
          .ok values := by
        simpa only using run extra
      rw [result]
      rfl
  | @Eval.ctor _ ρ name exprs values lengths evaluations => by
      have listEventually := evalListFuel_eventually_of_pointwise lengths
        (fun pair membership =>
          evalFuel_eventually_ok (evaluations pair membership))
      obtain ⟨threshold, run⟩ := listEventually
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have result : evalListFuel SF (threshold + extra) ρ exprs =
          .ok values := by
        simpa only using run extra
      rw [result]
      rfl
  | @Eval.prim _ ρ op exprs values value lengths evaluations primitive => by
      have listEventually := evalListFuel_eventually_of_pointwise lengths
        (fun pair membership =>
          evalFuel_eventually_ok (evaluations pair membership))
      obtain ⟨threshold, run⟩ := listEventually
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have result : evalListFuel SF (threshold + extra) ρ exprs =
          .ok values := by
        simpa only using run extra
      rw [result]
      simp [primitive]
  | .letE boundEvaluation bodyEvaluation => by
      obtain ⟨boundThreshold, boundRun⟩ :=
        evalFuel_eventually_ok boundEvaluation
      obtain ⟨bodyThreshold, bodyRun⟩ :=
        evalFuel_eventually_ok bodyEvaluation
      refine ⟨boundThreshold + bodyThreshold + 1, ?_⟩
      intro extra
      rw [show boundThreshold + bodyThreshold + 1 + extra =
        (boundThreshold + bodyThreshold + extra) + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have boundResult := boundRun (bodyThreshold + extra)
      have bodyResult := bodyRun (boundThreshold + extra)
      simp only at boundResult bodyResult
      rw [show boundThreshold + bodyThreshold + extra =
          boundThreshold + (bodyThreshold + extra) by omega,
        boundResult]
      simp only [RunResult.bind_ok]
      rw [show boundThreshold + (bodyThreshold + extra) =
          bodyThreshold + (boundThreshold + extra) by omega]
      exact bodyResult
  | .matchAll targetEvaluation matcherEvaluation search lengths evaluations => by
      obtain ⟨targetThreshold, targetRun⟩ :=
        evalFuel_eventually_ok targetEvaluation
      obtain ⟨matcherThreshold, matcherRun⟩ :=
        evalFuel_eventually_ok matcherEvaluation
      obtain ⟨searchThreshold, searchRun⟩ :=
        searchFuel_eventually_ok search
      have bodiesEventually := evalSubstsFuel_eventually_of_pointwise lengths
        (fun pair membership =>
          evalFuel_eventually_ok (evaluations pair membership))
      obtain ⟨bodyThreshold, bodyRun⟩ := bodiesEventually
      refine ⟨targetThreshold + matcherThreshold + searchThreshold +
        bodyThreshold + 1, ?_⟩
      intro extra
      let common := targetThreshold + matcherThreshold + searchThreshold +
        bodyThreshold + extra
      rw [show targetThreshold + matcherThreshold + searchThreshold +
        bodyThreshold + 1 + extra = common + 1 by omega]
      simp only [evalFuel, RunResult.monad_bind_eq_bind]
      have targetResult := targetRun
        (matcherThreshold + searchThreshold + bodyThreshold + extra)
      have matcherResult := matcherRun
        (targetThreshold + searchThreshold + bodyThreshold + extra)
      have searchResult := searchRun
        (targetThreshold + matcherThreshold + bodyThreshold + extra)
      have bodyResult := bodyRun
        (targetThreshold + matcherThreshold + searchThreshold + extra)
      dsimp [common]
      simp only at targetResult matcherResult searchResult bodyResult
      rw [show targetThreshold + matcherThreshold + searchThreshold +
          bodyThreshold + extra = targetThreshold +
            (matcherThreshold + searchThreshold + bodyThreshold + extra)
        by omega, targetResult]
      simp only [RunResult.bind_ok]
      rw [show targetThreshold +
            (matcherThreshold + searchThreshold + bodyThreshold + extra) =
          matcherThreshold +
            (targetThreshold + searchThreshold + bodyThreshold + extra)
        by omega, matcherResult]
      simp only [RunResult.bind_ok]
      rw [show matcherThreshold +
            (targetThreshold + searchThreshold + bodyThreshold + extra) =
          searchThreshold +
            (targetThreshold + matcherThreshold + bodyThreshold + extra)
        by omega, searchResult]
      simp only [RunResult.bind_ok]
      rw [show searchThreshold +
            (targetThreshold + matcherThreshold + bodyThreshold + extra) =
          bodyThreshold +
            (targetThreshold + matcherThreshold + searchThreshold + extra)
        by omega, bodyResult]
      rfl

/-- Every finite primitive-pattern matching derivation is reproduced
persistently above a finite fuel threshold. -/
theorem ppmFuel_eventually_ok
    {SF : RuntimeSigF} {ρ : Env} {pp : PPat} {pattern : Pattern}
    {result : Option (List Pattern × Env)} :
    ∀ (_ : PPM SF ρ pp pattern result),
      EventuallyOk (fun fuel => ppmFuel SF fuel ρ pp pattern) result
  | .hole | .wild => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | .pval evaluation => by
      obtain ⟨threshold, run⟩ := evalFuel_eventually_ok evaluation
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [ppmFuel]
      rw [if_pos (PPM.success_shape (.pval evaluation))]
      simp only [RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      rfl
  | @PPM.ctor _ _ name _ _ _ lengths resultLengths matchings => by
      have listEventually := ppmListFuel_eventually_of_pointwise lengths
        resultLengths (fun entry membership =>
          ppmFuel_eventually_ok (matchings entry membership))
      obtain ⟨threshold, run⟩ := listEventually
      have shape := PPM.success_shape
        (.ctor (name := name) lengths resultLengths matchings)
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [ppmFuel]
      rw [if_pos shape]
      simp only [RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      rfl
  | .tuple lengths resultLengths matchings => by
      have listEventually := ppmListFuel_eventually_of_pointwise lengths
        resultLengths (fun entry membership =>
          ppmFuel_eventually_ok (matchings entry membership))
      obtain ⟨threshold, run⟩ := listEventually
      have shape := PPM.success_shape
        (.tuple lengths resultLengths matchings)
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [ppmFuel]
      rw [if_pos shape]
      simp only [RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      rfl
  | .fail shape => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      simp [ppmFuel, shape]

/-- Every finite atom-reduction derivation is reproduced persistently above
a finite fuel threshold. -/
theorem matomFuel_eventually_ok
    {SF : RuntimeSigF} {ρ : Env} {pattern : Pattern} {matcher value : Value}
    {continuations : List (List Atom)} {new : MatchSubst} :
    ∀ (_ : MAtom SF ρ pattern matcher value continuations new),
      EventuallyOk
        (fun fuel => matomFuel SF fuel ρ pattern matcher value)
        (continuations, new)
  | .someWC | .someVar | .and | .or => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | .someValEq evaluation equal => by
      obtain ⟨threshold, run⟩ := evalFuel_eventually_ok evaluation
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [matomFuel, RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      simp [equal]
  | .someValNeq evaluation unequal => by
      obtain ⟨threshold, run⟩ := evalFuel_eventually_ok evaluation
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      simp only [matomFuel, RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      simp [unequal]
  | .tuple firstLength secondLength => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      simp [matomFuel, firstLength, secondLength]
  | .prodSome primitive => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      cases pattern <;> simp [Pattern.isPrimForm, matomFuel] at primitive ⊢
  | @MAtom.matcherPPFail _ ρ ρm original pattern value pp next arms
      clauses continuations new dispatchable failure recursive => by
      obtain ⟨headerThreshold, headerRun⟩ :=
        ppmFuel_eventually_ok failure
      have tailEventually := dispatchFuel_eventually_of_matom dispatchable
        (matomFuel_eventually_ok recursive)
      obtain ⟨tailThreshold, tailRun⟩ := tailEventually
      refine ⟨headerThreshold + tailThreshold + 2, ?_⟩
      intro extra
      let common := headerThreshold + tailThreshold + extra
      have header : ppmFuel SF common ρ pp pattern = .ok none := by
        dsimp [common]
        simpa [Nat.add_assoc] using headerRun (tailThreshold + extra)
      have tail : dispatchFuel SF common ρ ρm pattern value clauses =
          .ok (continuations, new) := by
        dsimp [common]
        rw [show headerThreshold + tailThreshold + extra =
          tailThreshold + (headerThreshold + extra) by omega]
        exact tailRun (headerThreshold + extra)
      change matomFuel SF (headerThreshold + tailThreshold + 2 + extra)
        ρ pattern (.matcherV ρm original (.mk pp next arms :: clauses))
        value = .ok (continuations, new)
      rw [show headerThreshold + tailThreshold + 2 + extra =
        (common + 1) + 1 by omega, matomFuel_matcher_eq dispatchable]
      simp only [dispatchFuel, RunResult.monad_bind_eq_bind]
      rw [header]
      simp only [RunResult.bind_ok]
      exact tail
  | @MAtom.matcherDPFail _ ρ ρm original pattern value pp next dp body
      arms clauses holes ρp continuations new dispatchable header failed
      recursive => by
      have headerEventually := ppmFuel_eventually_ok header
      have tailArmsEventually := armsFuel_eventually_of_matom dispatchable
        headerEventually (matomFuel_eventually_ok recursive)
      obtain ⟨headerThreshold, headerRun⟩ := headerEventually
      obtain ⟨armsThreshold, armsRun⟩ := tailArmsEventually
      refine ⟨headerThreshold + armsThreshold + 3, ?_⟩
      intro extra
      let common := headerThreshold + armsThreshold + extra
      have headerResult : ppmFuel SF (common + 1) ρ pp pattern =
          .ok (some (holes, ρp)) := by
        dsimp [common]
        rw [show headerThreshold + armsThreshold + extra + 1 =
          headerThreshold + (armsThreshold + extra + 1) by omega]
        exact headerRun (armsThreshold + extra + 1)
      have armsResult : armsFuel SF common ρ ρm value next holes ρp arms =
          .ok (continuations, new) := by
        dsimp [common]
        rw [show headerThreshold + armsThreshold + extra =
          armsThreshold + (headerThreshold + extra) by omega]
        exact armsRun (headerThreshold + extra)
      change matomFuel SF (headerThreshold + armsThreshold + 3 + extra)
        ρ pattern
          (.matcherV ρm original
            (.mk pp next (.mk dp body :: arms) :: clauses))
        value = .ok (continuations, new)
      rw [show headerThreshold + armsThreshold + 3 + extra =
        (common + 2) + 1 by omega, matomFuel_matcher_eq dispatchable]
      simp only [dispatchFuel, RunResult.monad_bind_eq_bind]
      rw [headerResult]
      simp only [RunResult.bind_ok, armsFuel, failed]
      exact armsResult
  | @MAtom.matcher _ ρ ρm original pattern value pp next dp body arms
      clauses holes ρp ρd decomposition tuples valueLists matcherValue
      matchers dispatchable header dataMatch bodyEvaluation listDecode
      tupleDecode nextEvaluation matcherDecode => by
      obtain ⟨headerThreshold, headerRun⟩ :=
        ppmFuel_eventually_ok header
      obtain ⟨bodyThreshold, bodyRun⟩ :=
        evalFuel_eventually_ok bodyEvaluation
      obtain ⟨nextThreshold, nextRun⟩ :=
        evalFuel_eventually_ok nextEvaluation
      refine ⟨headerThreshold + bodyThreshold + nextThreshold + 3, ?_⟩
      intro extra
      let common := headerThreshold + bodyThreshold + nextThreshold + extra
      have headerResult : ppmFuel SF (common + 1) ρ pp pattern =
          .ok (some (holes, ρp)) := by
        dsimp [common]
        rw [show headerThreshold + bodyThreshold + nextThreshold + extra + 1 =
          headerThreshold + (bodyThreshold + nextThreshold + extra + 1)
          by omega]
        exact headerRun (bodyThreshold + nextThreshold + extra + 1)
      have bodyResult : evalFuel SF common (ρd ++ ρp ++ ρm) body =
          .ok decomposition := by
        dsimp [common]
        rw [show headerThreshold + bodyThreshold + nextThreshold + extra =
          bodyThreshold + (headerThreshold + nextThreshold + extra) by omega]
        exact bodyRun (headerThreshold + nextThreshold + extra)
      have nextResult : evalFuel SF common ρm next = .ok matcherValue := by
        dsimp [common]
        rw [show headerThreshold + bodyThreshold + nextThreshold + extra =
          nextThreshold + (headerThreshold + bodyThreshold + extra) by omega]
        exact nextRun (headerThreshold + bodyThreshold + extra)
      change matomFuel SF
        (headerThreshold + bodyThreshold + nextThreshold + 3 + extra)
        ρ pattern
          (.matcherV ρm original
            (.mk pp next (.mk dp body :: arms) :: clauses))
        value = .ok
          (valueLists.map fun values =>
            (holes.zip (matchers.zip values)).map fun entry =>
              ⟨entry.1, entry.2.1, entry.2.2⟩,
            [])
      rw [show headerThreshold + bodyThreshold + nextThreshold + 3 + extra =
        (common + 2) + 1 by omega, matomFuel_matcher_eq dispatchable]
      simp only [dispatchFuel, RunResult.monad_bind_eq_bind]
      rw [headerResult]
      simp only [RunResult.bind_ok, armsFuel, dataMatch]
      rw [bodyResult]
      simp [RunResult.bind_ok, listDecode, tupleDecode]
      rw [nextResult]
      simp [matcherDecode]

/-- Every finite matching-state step is reproduced persistently above a
finite fuel threshold. -/
theorem stepFuel_eventually_ok
    {SF : RuntimeSigF} {state : MState} {states : List MState} :
    ∀ (_ : Step SF state states),
      EventuallyOk (fun fuel => stepFuel SF fuel state) states
  | @Step.reduce _ stack ρ substitution pattern matcher value
      continuations new atomReduction => by
      obtain ⟨threshold, run⟩ := matomFuel_eventually_ok atomReduction
      refine ⟨threshold + 1, ?_⟩
      intro extra
      have notPatfun : ∀ name arguments, pattern ≠ .papp name arguments := by
        intro name arguments equality
        subst pattern
        cases atomReduction <;>
          simp [Pattern.isPrimForm, Pattern.isMatcherDispatchable] at *
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      change stepFuel SF (threshold + extra + 1)
        ⟨.atom ⟨pattern, matcher, value⟩ :: stack, ρ, substitution⟩ = .ok _
      rw [stepFuel_atom_eq notPatfun]
      simp only [RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      rfl
  | .patfunEnter found length => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      simp [stepFuel, found, length]
  | @Step.mnodeStep _ stack ρ substitution tree innerStack ρf θf piE
      states guard inner => by
      obtain ⟨threshold, run⟩ := stepFuel_eventually_ok inner
      refine ⟨threshold + 1, ?_⟩
      intro extra
      rw [show threshold + 1 + extra = (threshold + extra) + 1 by omega]
      change stepFuel SF (threshold + extra + 1)
        ⟨.mnode (tree :: innerStack) ρf θf piE :: stack,
          ρ, substitution⟩ = .ok _
      rw [stepFuel_mnode_guard_eq guard]
      simp only [RunResult.monad_bind_eq_bind]
      have result := run extra
      simp only at result
      rw [result]
      rfl
  | .mnodeVarpat found => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      simp [stepFuel, found]
  | .mnodeDone => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl

/-- Every finite exhaustive-search derivation is reproduced persistently
above a finite fuel threshold. -/
theorem searchFuel_eventually_ok
    {SF : RuntimeSigF} {state : MState} {substitutions : List MatchSubst} :
    ∀ (_ : Search SF state substitutions),
      EventuallyOk (fun fuel => searchFuel SF fuel state) substitutions
  | .done => by
      refine ⟨1, ?_⟩
      intro extra
      rw [Nat.one_add]
      rfl
  | .step reduction lengths searches => by
      obtain ⟨stepThreshold, stepRun⟩ :=
        stepFuel_eventually_ok reduction
      have listEventually := searchListFuel_eventually_of_pointwise lengths
        (fun pair membership =>
          searchFuel_eventually_ok (searches pair membership))
      obtain ⟨listThreshold, listRun⟩ := listEventually
      refine ⟨stepThreshold + listThreshold + 1, ?_⟩
      intro extra
      rw [show stepThreshold + listThreshold + 1 + extra =
        (stepThreshold + listThreshold + extra) + 1 by omega]
      change searchFuel SF (stepThreshold + listThreshold + extra + 1)
        state = .ok _
      rw [searchFuel_step_eq reduction]
      simp only [RunResult.monad_bind_eq_bind]
      have stepResult := stepRun (listThreshold + extra)
      have listResult := listRun (stepThreshold + extra)
      simp only at stepResult listResult
      rw [show stepThreshold + listThreshold + extra =
          stepThreshold + (listThreshold + extra) by omega,
        stepResult]
      simp only [RunResult.bind_ok]
      rw [show stepThreshold + (listThreshold + extra) =
          listThreshold + (stepThreshold + extra) by omega,
        listResult]
      rfl

end

/-- Conventional existential completeness corollary for expression
evaluation. -/
theorem evalFuel_complete
    {SF : RuntimeSigF} {ρ : Env} {expression : Expr} {value : Value}
    (evaluation : Eval SF ρ expression value) :
    ∃ fuel, evalFuel SF fuel ρ expression = .ok value := by
  obtain ⟨threshold, run⟩ := evalFuel_eventually_ok evaluation
  exact ⟨threshold, by simpa using run 0⟩

end TypePM
