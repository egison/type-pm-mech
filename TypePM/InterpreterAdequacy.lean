import TypePM.Interpreter

/-!
# Adequacy of the fuel-indexed interpreter

A successful interpreter run reconstructs the corresponding big-step
derivation: `evalFuel = ok` yields `Eval`, `ppmFuel = ok` yields `PPM`
(including explicit shape failure), `matomFuel = ok` yields `MAtom`,
`stepFuel = ok` yields `Step`, and `searchFuel = ok` yields `Search`.
Timeouts and stuck runs claim nothing here; the no-stuck safety theorem is
separate.

Each proof is a structural induction on fuel that mirrors the interpreter's
match structure, so every successful branch maps onto exactly one relational
constructor.  The two reduction equations below expose the shared
non-pattern-function atom case and the shared non-embedded node case of
`stepFuel` once, instead of once per head constructor.
-/

namespace TypePM

/-- On a non-pattern-function atom head, `stepFuel` is the `matomFuel`
reduction. -/
theorem stepFuel_atom_eq {SF : RuntimeSigF} {fuel : Nat}
    {stack : List Tree} {ρ : Env} {substitution : MatchSubst}
    {pattern : Pattern} {matcher value : Value}
    (notPatfun : ∀ name arguments, pattern ≠ .papp name arguments) :
    stepFuel SF (fuel + 1)
      ⟨.atom ⟨pattern, matcher, value⟩ :: stack, ρ, substitution⟩ =
      (do
        let (continuations, new) ←
          matomFuel SF fuel (substitution ++ ρ) pattern matcher value
        pure (continuations.map fun atoms =>
          ⟨atoms.map .atom ++ stack, ρ, new ++ substitution⟩)) := by
  cases pattern with
  | papp name arguments => exact absurd rfl (notPatfun name arguments)
  | pvar name => rfl
  | wild => rfl
  | pval expression => rfl
  | embed name => rfl
  | pctor name patterns => rfl
  | pand left right => rfl
  | por left right => rfl
  | ptuple patterns => rfl

/-- On a non-embedded inner head, `stepFuel` steps inside the isolated
node. -/
theorem stepFuel_mnode_eq {SF : RuntimeSigF} {fuel : Nat}
    {stack : List Tree} {ρ : Env} {substitution : MatchSubst}
    {innerTree : Tree} {innerStack : List Tree} {innerEnv : Env}
    {innerSubst : MatchSubst} {piE : PiEnv}
    (notEmbed : ∀ name matcher value,
      innerTree ≠ .atom ⟨.embed name, matcher, value⟩) :
    stepFuel SF (fuel + 1)
      ⟨.mnode (innerTree :: innerStack) innerEnv innerSubst piE :: stack,
        ρ, substitution⟩ =
      (do
        let states ← stepFuel SF fuel
          ⟨innerTree :: innerStack, innerEnv, innerSubst⟩
        pure (states.map fun state =>
          ⟨.mnode state.S innerEnv state.θ piE :: stack,
            ρ, substitution⟩)) := by
  cases innerTree with
  | mnode innerTrees innerEnv' innerSubst' piE' => rfl
  | atom innerAtom =>
      obtain ⟨innerPattern, innerMatcher, innerValue⟩ := innerAtom
      cases innerPattern with
      | embed name =>
          exact absurd rfl (notEmbed name innerMatcher innerValue)
      | pvar name => rfl
      | wild => rfl
      | pval expression => rfl
      | pctor name patterns => rfl
      | pand left right => rfl
      | por left right => rfl
      | papp name arguments => rfl
      | ptuple patterns => rfl

mutual

/-- A successful expression run is a big-step evaluation. -/
theorem evalFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {expression : Expr} {value : Value},
      evalFuel SF fuel ρ expression = .ok value →
      Eval SF ρ expression value
  | 0, _, _, _, h => by simp [evalFuel] at h
  | fuel + 1, ρ, expression, value, h => by
    cases expression with
    | var name =>
        simp only [evalFuel] at h
        split at h
        · cases h
          exact .var (by assumption)
        · cases h
    | lam param body =>
        cases h
        exact .lam
    | fix name param body =>
        cases h
        exact .fix
    | app fn arg =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hFn : evalFuel SF fuel ρ fn with
        | ok fnValue =>
            rw [hFn] at h
            simp only [RunResult.bind_ok] at h
            cases fnValue with
            | closure self closureEnv param body =>
                cases hArg : evalFuel SF fuel ρ arg with
                | ok argValue =>
                    rw [hArg] at h
                    simp only [RunResult.bind_ok] at h
                    exact .app (evalFuel_ok hFn) (evalFuel_ok hArg)
                      (evalFuel_ok h)
                | timeout => rw [hArg] at h; cases h
                | stuck => rw [hArg] at h; cases h
            | lit n => cases h
            | ctor name values => cases h
            | tuple values => cases h
            | matcherV env original current => cases h
            | something => cases h
        | timeout => rw [hFn] at h; cases h
        | stuck => rw [hFn] at h; cases h
    | lit n =>
        cases h
        exact .lit
    | tuple exprs =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hValues : evalListFuel SF fuel ρ exprs with
        | ok values =>
            rw [hValues] at h
            cases h
            obtain ⟨lengths, pointwise⟩ := evalListFuel_ok hValues
            exact .tuple lengths pointwise
        | timeout => rw [hValues] at h; cases h
        | stuck => rw [hValues] at h; cases h
    | ctor name exprs =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hValues : evalListFuel SF fuel ρ exprs with
        | ok values =>
            rw [hValues] at h
            cases h
            obtain ⟨lengths, pointwise⟩ := evalListFuel_ok hValues
            exact .ctor lengths pointwise
        | timeout => rw [hValues] at h; cases h
        | stuck => rw [hValues] at h; cases h
    | prim op exprs =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hValues : evalListFuel SF fuel ρ exprs with
        | ok values =>
            rw [hValues] at h
            simp only [RunResult.bind_ok] at h
            split at h
            · cases h
              obtain ⟨lengths, pointwise⟩ := evalListFuel_ok hValues
              exact .prim lengths pointwise (by assumption)
            · cases h
        | timeout => rw [hValues] at h; cases h
        | stuck => rw [hValues] at h; cases h
    | letE name bound body =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hBound : evalFuel SF fuel ρ bound with
        | ok boundValue =>
            rw [hBound] at h
            simp only [RunResult.bind_ok] at h
            exact .letE (evalFuel_ok hBound) (evalFuel_ok h)
        | timeout => rw [hBound] at h; cases h
        | stuck => rw [hBound] at h; cases h
    | something =>
        cases h
        exact .something
    | matcher clauses =>
        cases h
        exact .matcher
    | matchAll target matcher pattern body =>
        simp only [evalFuel, RunResult.monad_bind_eq_bind] at h
        cases hTarget : evalFuel SF fuel ρ target with
        | ok targetValue =>
            rw [hTarget] at h
            simp only [RunResult.bind_ok] at h
            cases hMatcher : evalFuel SF fuel ρ matcher with
            | ok matcherValue =>
                rw [hMatcher] at h
                simp only [RunResult.bind_ok] at h
                cases hSearch : searchFuel SF fuel
                    ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], ρ, []⟩
                    with
                | ok substitutions =>
                    rw [hSearch] at h
                    simp only [RunResult.bind_ok] at h
                    cases hValues : evalSubstsFuel SF fuel ρ body
                        substitutions with
                    | ok values =>
                        rw [hValues] at h
                        cases h
                        obtain ⟨lengths, pointwise⟩ :=
                          evalSubstsFuel_ok hValues
                        exact .matchAll (evalFuel_ok hTarget)
                          (evalFuel_ok hMatcher) (searchFuel_ok hSearch)
                          lengths pointwise
                    | timeout => rw [hValues] at h; cases h
                    | stuck => rw [hValues] at h; cases h
                | timeout => rw [hSearch] at h; cases h
                | stuck => rw [hSearch] at h; cases h
            | timeout => rw [hMatcher] at h; cases h
            | stuck => rw [hMatcher] at h; cases h
        | timeout => rw [hTarget] at h; cases h
        | stuck => rw [hTarget] at h; cases h

/-- A successful expression-list run is a pointwise evaluation. -/
theorem evalListFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {exprs : List Expr} {values : List Value},
      evalListFuel SF fuel ρ exprs = .ok values →
      exprs.length = values.length ∧
        ∀ pair ∈ exprs.zip values, Eval SF ρ pair.1 pair.2
  | 0, _, _, _, h => by simp [evalListFuel] at h
  | _ + 1, _, [], _, h => by
      cases h
      exact ⟨rfl, fun pair membership => by cases membership⟩
  | fuel + 1, ρ, expression :: exprs, values, h => by
      simp only [evalListFuel, RunResult.monad_bind_eq_bind] at h
      cases hHead : evalFuel SF fuel ρ expression with
      | ok headValue =>
          rw [hHead] at h
          simp only [RunResult.bind_ok] at h
          cases hTail : evalListFuel SF fuel ρ exprs with
          | ok tailValues =>
              rw [hTail] at h
              cases h
              obtain ⟨lengths, pointwise⟩ := evalListFuel_ok hTail
              refine ⟨by simp [lengths], ?_⟩
              intro pair membership
              rw [List.zip_cons_cons] at membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact evalFuel_ok hHead
              · exact pointwise pair membership
          | timeout => rw [hTail] at h; cases h
          | stuck => rw [hTail] at h; cases h
      | timeout => rw [hHead] at h; cases h
      | stuck => rw [hHead] at h; cases h

/-- A successful per-substitution body run is a pointwise evaluation. -/
theorem evalSubstsFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {body : Expr}
      {substitutions : List MatchSubst} {values : List Value},
      evalSubstsFuel SF fuel ρ body substitutions = .ok values →
      substitutions.length = values.length ∧
        ∀ pair ∈ substitutions.zip values,
          Eval SF (pair.1 ++ ρ) body pair.2
  | 0, _, _, _, _, h => by simp [evalSubstsFuel] at h
  | _ + 1, _, _, [], _, h => by
      cases h
      exact ⟨rfl, fun pair membership => by cases membership⟩
  | fuel + 1, ρ, body, substitution :: substitutions, values, h => by
      simp only [evalSubstsFuel, RunResult.monad_bind_eq_bind] at h
      cases hHead : evalFuel SF fuel (substitution ++ ρ) body with
      | ok headValue =>
          rw [hHead] at h
          simp only [RunResult.bind_ok] at h
          cases hTail : evalSubstsFuel SF fuel ρ body substitutions with
          | ok tailValues =>
              rw [hTail] at h
              cases h
              obtain ⟨lengths, pointwise⟩ := evalSubstsFuel_ok hTail
              refine ⟨by simp [lengths], ?_⟩
              intro pair membership
              rw [List.zip_cons_cons] at membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact evalFuel_ok hHead
              · exact pointwise pair membership
          | timeout => rw [hTail] at h; cases h
          | stuck => rw [hTail] at h; cases h
      | timeout => rw [hHead] at h; cases h
      | stuck => rw [hHead] at h; cases h

/-- A successful primitive-pattern run is a `PPM` derivation, with the
`none` outcome mapping to explicit shape failure. -/
theorem ppmFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {pp : PPat} {pattern : Pattern}
      {outcome : Option (List Pattern × Env)},
      ppmFuel SF fuel ρ pp pattern = .ok outcome →
      PPM SF ρ pp pattern outcome
  | 0, _, _, _, _, h => by simp [ppmFuel] at h
  | fuel + 1, ρ, pp, pattern, outcome, h => by
    simp only [ppmFuel] at h
    split at h
    · rename_i hShape
      cases pp with
      | hole =>
          cases h
          exact .hole
      | wild =>
          cases pattern with
          | wild => cases h; exact .wild
          | pvar _ => simp [ppShapeOK] at hShape
          | pval _ => simp [ppShapeOK] at hShape
          | embed _ => simp [ppShapeOK] at hShape
          | pctor _ _ => simp [ppShapeOK] at hShape
          | pand _ _ => simp [ppShapeOK] at hShape
          | por _ _ => simp [ppShapeOK] at hShape
          | papp _ _ => simp [ppShapeOK] at hShape
          | ptuple _ => simp [ppShapeOK] at hShape
      | pval name =>
          cases pattern with
          | pval expression =>
              have h' : RunResult.bind (evalFuel SF fuel ρ expression)
                  (fun value => pure (some ([], [(name, value)]))) =
                  .ok outcome := h
              cases hEval : evalFuel SF fuel ρ expression with
              | ok value =>
                  rw [hEval] at h'
                  cases h'
                  exact .pval (evalFuel_ok hEval)
              | timeout => rw [hEval] at h'; cases h'
              | stuck => rw [hEval] at h'; cases h'
          | pvar _ => simp [ppShapeOK] at hShape
          | wild => simp [ppShapeOK] at hShape
          | embed _ => simp [ppShapeOK] at hShape
          | pctor _ _ => simp [ppShapeOK] at hShape
          | pand _ _ => simp [ppShapeOK] at hShape
          | por _ _ => simp [ppShapeOK] at hShape
          | papp _ _ => simp [ppShapeOK] at hShape
          | ptuple _ => simp [ppShapeOK] at hShape
      | ctor name pps =>
          cases pattern with
          | pctor name' patterns =>
              simp only [ppShapeOK, Bool.and_eq_true] at hShape
              obtain ⟨hName, _⟩ := hShape
              have nameEq : name = name' := by simpa using hName
              subst nameEq
              have h' : RunResult.bind (ppmListFuel SF fuel ρ pps patterns)
                  (fun results => pure (some ((results.map (·.1)).flatten,
                    (results.map (·.2)).flatten))) = .ok outcome := h
              cases hList : ppmListFuel SF fuel ρ pps patterns with
              | ok results =>
                  rw [hList] at h'
                  simp only [RunResult.bind_ok] at h'
                  cases h'
                  obtain ⟨lengths, zipLengths, pointwise⟩ :=
                    ppmListFuel_ok hList
                  exact .ctor lengths zipLengths pointwise
              | timeout => rw [hList] at h'; cases h'
              | stuck => rw [hList] at h'; cases h'
          | pvar _ => simp [ppShapeOK] at hShape
          | wild => simp [ppShapeOK] at hShape
          | pval _ => simp [ppShapeOK] at hShape
          | embed _ => simp [ppShapeOK] at hShape
          | pand _ _ => simp [ppShapeOK] at hShape
          | por _ _ => simp [ppShapeOK] at hShape
          | papp _ _ => simp [ppShapeOK] at hShape
          | ptuple _ => simp [ppShapeOK] at hShape
      | tuple pps =>
          cases pattern with
          | ptuple patterns =>
              have h' : RunResult.bind (ppmListFuel SF fuel ρ pps patterns)
                  (fun results => pure (some ((results.map (·.1)).flatten,
                    (results.map (·.2)).flatten))) = .ok outcome := h
              cases hList : ppmListFuel SF fuel ρ pps patterns with
              | ok results =>
                  rw [hList] at h'
                  simp only [RunResult.bind_ok] at h'
                  cases h'
                  obtain ⟨lengths, zipLengths, pointwise⟩ :=
                    ppmListFuel_ok hList
                  exact .tuple lengths zipLengths pointwise
              | timeout => rw [hList] at h'; cases h'
              | stuck => rw [hList] at h'; cases h'
          | pvar _ => simp [ppShapeOK] at hShape
          | wild => simp [ppShapeOK] at hShape
          | pval _ => simp [ppShapeOK] at hShape
          | embed _ => simp [ppShapeOK] at hShape
          | pctor _ _ => simp [ppShapeOK] at hShape
          | pand _ _ => simp [ppShapeOK] at hShape
          | por _ _ => simp [ppShapeOK] at hShape
          | papp _ _ => simp [ppShapeOK] at hShape
    · rename_i hShape
      cases h
      exact .fail (by simpa using hShape)

/-- A successful component run is a pointwise `PPM` success of the exact
arity. -/
theorem ppmListFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {pps : List PPat} {patterns : List Pattern}
      {results : List (List Pattern × Env)},
      ppmListFuel SF fuel ρ pps patterns = .ok results →
      pps.length = patterns.length ∧
        (pps.zip patterns).length = results.length ∧
        ∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF ρ entry.1.1 entry.1.2 (some entry.2)
  | 0, _, _, _, _, h => by simp [ppmListFuel] at h
  | _ + 1, _, [], [], _, h => by
      cases h
      exact ⟨rfl, rfl, fun entry membership => by cases membership⟩
  | _ + 1, _, [], _ :: _, _, h => by cases h
  | _ + 1, _, _ :: _, [], _, h => by cases h
  | fuel + 1, ρ, pp :: pps, pattern :: patterns, results, h => by
      simp only [ppmListFuel, RunResult.monad_bind_eq_bind] at h
      cases hHead : ppmFuel SF fuel ρ pp pattern with
      | ok headOutcome =>
          rw [hHead] at h
          simp only [RunResult.bind_ok] at h
          cases headOutcome with
          | none => cases h
          | some result =>
              cases hTail : ppmListFuel SF fuel ρ pps patterns with
              | ok tailResults =>
                  rw [hTail] at h
                  simp only [RunResult.bind_ok] at h
                  cases h
                  obtain ⟨lengths, zipLengths, pointwise⟩ :=
                    ppmListFuel_ok hTail
                  refine ⟨by simp [lengths], ?_, ?_⟩
                  · simp [List.zip_cons_cons, zipLengths]
                  · intro entry membership
                    rw [List.zip_cons_cons, List.zip_cons_cons]
                      at membership
                    rcases List.mem_cons.mp membership with
                      rfl | membership
                    · exact ppmFuel_ok hHead
                    · exact pointwise entry membership
              | timeout => rw [hTail] at h; cases h
              | stuck => rw [hTail] at h; cases h
      | timeout => rw [hHead] at h; cases h
      | stuck => rw [hHead] at h; cases h

/-- A successful atom run is an `MAtom` reduction. -/
theorem matomFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ : Env} {pattern : Pattern} {matcher value : Value}
      {continuations : List (List Atom)} {new : MatchSubst},
      matomFuel SF fuel ρ pattern matcher value = .ok (continuations, new) →
      MAtom SF ρ pattern matcher value continuations new
  | 0, _, _, _, _, _, _, h => by simp [matomFuel] at h
  | fuel + 1, ρ, pattern, matcher, value, continuations, new, h => by
    cases pattern with
    | pand left right =>
        cases h
        exact .and
    | por left right =>
        cases h
        exact .or
    | wild =>
        cases matcher with
        | something => cases h; exact .someWC
        | tuple matchers => cases h; exact .prodSome rfl
        | matcherV matcherEnv original clauses =>
            exact dispatchFuel_ok rfl h
        | lit n => cases h
        | ctor name values => cases h
        | closure self env param body => cases h
    | pvar name =>
        cases matcher with
        | something => cases h; exact .someVar
        | tuple matchers => cases h; exact .prodSome rfl
        | matcherV matcherEnv original clauses =>
            exact dispatchFuel_ok rfl h
        | lit n => cases h
        | ctor name' values => cases h
        | closure self env param body => cases h
    | pval expression =>
        cases matcher with
        | something =>
            simp only [matomFuel, RunResult.monad_bind_eq_bind] at h
            cases hEval : evalFuel SF fuel ρ expression with
            | ok expected =>
                rw [hEval] at h
                simp only [RunResult.bind_ok] at h
                split at h
                · cases h
                  exact .someValEq (evalFuel_ok hEval) (by assumption)
                · rename_i hNeq
                  cases h
                  exact .someValNeq (evalFuel_ok hEval) (by simpa using hNeq)
            | timeout => rw [hEval] at h; cases h
            | stuck => rw [hEval] at h; cases h
        | tuple matchers => cases h; exact .prodSome rfl
        | matcherV matcherEnv original clauses =>
            exact dispatchFuel_ok rfl h
        | lit n => cases h
        | ctor name values => cases h
        | closure self env param body => cases h
    | pctor name patterns =>
        cases matcher with
        | matcherV matcherEnv original clauses =>
            exact dispatchFuel_ok rfl h
        | something => cases h
        | tuple matchers => cases h
        | lit n => cases h
        | ctor name' values => cases h
        | closure self env param body => cases h
    | ptuple patterns =>
        cases matcher with
        | tuple matchers =>
            cases value with
            | tuple values =>
                have h' : (if patterns.length = matchers.length ∧
                      matchers.length = values.length then
                      (.ok ([(patterns.zip (matchers.zip values)).map
                        fun entry => ⟨entry.1, entry.2.1, entry.2.2⟩],
                        ([] : MatchSubst)) : RunResult _)
                    else .stuck) = .ok (continuations, new) := h
                split at h'
                · rename_i lengths
                  cases h'
                  exact .tuple lengths.1 lengths.2
                · cases h'
            | lit n => cases h
            | ctor name values => cases h
            | closure self env param body => cases h
            | matcherV env original current => cases h
            | something => cases h
        | matcherV matcherEnv original clauses =>
            exact dispatchFuel_ok rfl h
        | something => cases h
        | lit n => cases h
        | ctor name values => cases h
        | closure self env param body => cases h
    | papp name arguments =>
        cases matcher <;> cases h
    | embed name =>
        cases matcher <;> cases h

/-- A successful clause dispatch is an `MAtom` reduction against any stored
original clause list. -/
theorem dispatchFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ matcherEnv : Env} {pattern : Pattern} {value : Value}
      {clauses original : List Clause}
      {continuations : List (List Atom)} {new : MatchSubst},
      pattern.isMatcherDispatchable = true →
      dispatchFuel SF fuel ρ matcherEnv pattern value clauses =
        .ok (continuations, new) →
      MAtom SF ρ pattern (.matcherV matcherEnv original clauses) value
        continuations new
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [dispatchFuel] at h
  | _ + 1, _, _, _, _, [], _, _, _, _, h => by simp [dispatchFuel] at h
  | fuel + 1, ρ, matcherEnv, pattern, value, .mk pp next arms :: clauses,
      original, continuations, new, dispatchable, h => by
      simp only [dispatchFuel, RunResult.monad_bind_eq_bind] at h
      cases hPPM : ppmFuel SF fuel ρ pp pattern with
      | ok outcome =>
          rw [hPPM] at h
          simp only [RunResult.bind_ok] at h
          cases outcome with
          | none =>
              exact .matcherPPFail dispatchable (ppmFuel_ok hPPM)
                (dispatchFuel_ok dispatchable h)
          | some result =>
              obtain ⟨holes, ppEnv⟩ := result
              exact armsFuel_ok dispatchable (ppmFuel_ok hPPM) h
      | timeout => rw [hPPM] at h; cases h
      | stuck => rw [hPPM] at h; cases h

/-- A successful arm dispatch inside the committed clause is an `MAtom`
reduction on that clause. -/
theorem armsFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {ρ matcherEnv : Env} {pattern : Pattern} {value : Value}
      {pp : PPat} {next : Expr} {holes : List Pattern} {ppEnv : Env}
      {arms : List Arm} {clauses original : List Clause}
      {continuations : List (List Atom)} {new : MatchSubst},
      pattern.isMatcherDispatchable = true →
      PPM SF ρ pp pattern (some (holes, ppEnv)) →
      armsFuel SF fuel ρ matcherEnv value next holes ppEnv arms =
        .ok (continuations, new) →
      MAtom SF ρ pattern
        (.matcherV matcherEnv original (.mk pp next arms :: clauses)) value
        continuations new
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by
      simp [armsFuel] at h
  | _ + 1, _, _, _, _, _, _, _, _, [], _, _, _, _, _, _, h => by
      simp [armsFuel] at h
  | fuel + 1, ρ, matcherEnv, pattern, value, pp, next, holes, ppEnv,
      .mk dp body :: arms, clauses, original, continuations, new,
      dispatchable, ppm, h => by
      simp only [armsFuel, RunResult.monad_bind_eq_bind] at h
      split at h
      · rename_i hData
        exact .matcherDPFail dispatchable ppm hData
          (armsFuel_ok dispatchable ppm h)
      · rename_i dataEnv hData
        cases hBody : evalFuel SF fuel (dataEnv ++ ppEnv ++ matcherEnv)
            body with
        | ok decomposition =>
            rw [hBody] at h
            simp only [RunResult.bind_ok] at h
            split at h
            · cases h
            · rename_i tuples hList
              split at h
              · cases h
              · rename_i valueLists hDecode
                cases hNext : evalFuel SF fuel matcherEnv next with
                | ok matcherValue =>
                    rw [hNext] at h
                    simp only [RunResult.bind_ok] at h
                    split at h
                    · cases h
                    · rename_i matchers hMatchers
                      cases h
                      exact .matcher dispatchable ppm hData
                        (evalFuel_ok hBody) hList hDecode
                        (evalFuel_ok hNext) hMatchers
                | timeout => rw [hNext] at h; cases h
                | stuck => rw [hNext] at h; cases h
        | timeout => rw [hBody] at h; cases h
        | stuck => rw [hBody] at h; cases h

/-- A successful state step is a `Step` reduction. -/
theorem stepFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {state : MState} {states : List MState},
      stepFuel SF fuel state = .ok states →
      Step SF state states
  | 0, _, _, h => by simp [stepFuel] at h
  | fuel + 1, ⟨stack, ρ, substitution⟩, states, h => by
    cases stack with
    | nil => simp [stepFuel] at h
    | cons tree rest =>
      by_cases hPatfun : ∃ name arguments matcher value,
          tree = .atom ⟨.papp name arguments, matcher, value⟩
      · obtain ⟨name, arguments, matcher, value, rfl⟩ := hPatfun
        simp only [stepFuel] at h
        split at h
        · rename_i entry hFind
          obtain ⟨foundName, signature⟩ := entry
          have nameEq : foundName = name := by
            simpa using List.find?_some hFind
          subst nameEq
          split at h
          · rename_i arity
            cases h
            exact .patfunEnter hFind arity
          · cases h
        · cases h
      · cases tree with
        | atom atom =>
            obtain ⟨pattern, matcher, value⟩ := atom
            have notPatfun : ∀ name arguments,
                pattern ≠ .papp name arguments := by
              intro name arguments contradiction
              subst contradiction
              exact hPatfun ⟨name, arguments, matcher, value, rfl⟩
            rw [stepFuel_atom_eq notPatfun,
              RunResult.monad_bind_eq_bind] at h
            cases hAtom : matomFuel SF fuel (substitution ++ ρ) pattern
                matcher value with
            | ok result =>
                rw [hAtom] at h
                simp only [RunResult.bind_ok] at h
                obtain ⟨continuations, new⟩ := result
                cases h
                exact .reduce (matomFuel_ok hAtom)
            | timeout => rw [hAtom] at h; cases h
            | stuck => rw [hAtom] at h; cases h
        | mnode trees innerEnv innerSubst piE =>
            cases trees with
            | nil =>
                cases h
                exact .mnodeDone
            | cons innerTree innerStack =>
                by_cases hEmbed : ∃ name matcher value,
                    innerTree = .atom ⟨.embed name, matcher, value⟩
                · obtain ⟨name, matcher, value, rfl⟩ := hEmbed
                  simp only [stepFuel] at h
                  split at h
                  · rename_i entry hFind
                    obtain ⟨foundName, actual⟩ := entry
                    have nameEq : foundName = name := by
                      simpa using List.find?_some hFind
                    subst nameEq
                    cases h
                    exact .mnodeVarpat hFind
                  · rename_i hFind
                    simp only [RunResult.monad_bind_eq_bind] at h
                    cases hInner : stepFuel SF fuel
                        ⟨.atom ⟨.embed name, matcher, value⟩ ::
                          innerStack, innerEnv, innerSubst⟩ with
                    | ok innerStates =>
                        rw [hInner] at h
                        cases h
                        refine .mnodeStep ?_ (stepFuel_ok hInner)
                        intro name' matcher' value' treeEq
                        cases treeEq
                        exact hFind
                    | timeout => rw [hInner] at h; cases h
                    | stuck => rw [hInner] at h; cases h
                · have notEmbed : ∀ name matcher value,
                      innerTree ≠ .atom ⟨.embed name, matcher, value⟩ := by
                    intro name matcher value contradiction
                    exact hEmbed ⟨name, matcher, value, contradiction⟩
                  rw [stepFuel_mnode_eq notEmbed,
                    RunResult.monad_bind_eq_bind] at h
                  cases hInner : stepFuel SF fuel
                      ⟨innerTree :: innerStack, innerEnv, innerSubst⟩ with
                  | ok innerStates =>
                      rw [hInner] at h
                      cases h
                      refine .mnodeStep ?_ (stepFuel_ok hInner)
                      intro name matcher value treeEq
                      exact absurd treeEq (notEmbed name matcher value)
                  | timeout => rw [hInner] at h; cases h
                  | stuck => rw [hInner] at h; cases h

/-- A successful search run is a `Search` derivation. -/
theorem searchFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {state : MState} {substitutions : List MatchSubst},
      searchFuel SF fuel state = .ok substitutions →
      Search SF state substitutions
  | 0, _, _, h => by simp [searchFuel] at h
  | fuel + 1, ⟨stack, ρ, substitution⟩, substitutions, h => by
    cases stack with
    | nil =>
        cases h
        exact .done
    | cons tree rest =>
        simp only [searchFuel, RunResult.monad_bind_eq_bind] at h
        cases hStep : stepFuel SF fuel ⟨tree :: rest, ρ, substitution⟩ with
        | ok states =>
            rw [hStep] at h
            simp only [RunResult.bind_ok] at h
            cases hList : searchListFuel SF fuel states with
            | ok results =>
                rw [hList] at h
                cases h
                obtain ⟨lengths, pointwise⟩ := searchListFuel_ok hList
                exact .step (stepFuel_ok hStep) lengths pointwise
            | timeout => rw [hList] at h; cases h
            | stuck => rw [hList] at h; cases h
        | timeout => rw [hStep] at h; cases h
        | stuck => rw [hStep] at h; cases h

/-- A successful search over a state list is pointwise `Search`. -/
theorem searchListFuel_ok {SF : RuntimeSigF} :
    ∀ {fuel : Nat} {states : List MState}
      {results : List (List MatchSubst)},
      searchListFuel SF fuel states = .ok results →
      states.length = results.length ∧
        ∀ pair ∈ states.zip results, Search SF pair.1 pair.2
  | 0, _, _, h => by simp [searchListFuel] at h
  | _ + 1, [], _, h => by
      cases h
      exact ⟨rfl, fun pair membership => by cases membership⟩
  | fuel + 1, state :: states, results, h => by
      simp only [searchListFuel, RunResult.monad_bind_eq_bind] at h
      cases hHead : searchFuel SF fuel state with
      | ok headResults =>
          rw [hHead] at h
          simp only [RunResult.bind_ok] at h
          cases hTail : searchListFuel SF fuel states with
          | ok tailResults =>
              rw [hTail] at h
              cases h
              obtain ⟨lengths, pointwise⟩ := searchListFuel_ok hTail
              refine ⟨by simp [lengths], ?_⟩
              intro pair membership
              rw [List.zip_cons_cons] at membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact searchFuel_ok hHead
              · exact pointwise pair membership
          | timeout => rw [hTail] at h; cases h
          | stuck => rw [hTail] at h; cases h
      | timeout => rw [hHead] at h; cases h
      | stuck => rw [hHead] at h; cases h

end

end TypePM
