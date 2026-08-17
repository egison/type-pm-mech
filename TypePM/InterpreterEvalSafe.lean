import TypePM.InterpreterStepSafe
import TypePM.InterpreterInversions
import TypePM.InterpreterAdequacy

/-!
# Expression-level safety of the fuel-indexed interpreter

`evalSafe` is the expression layer of the no-stuck theorem: a typed
expression evaluated in a typed, pristine, scoped environment that answers
all its free variables never returns `.stuck`, and every successful value
is scoped.  Typing and pristineness of intermediate values are recovered
relationally through adequacy (`evalFuel_ok`) and the existing relational
preservation, never re-proved functionally.

The pattern-matching search is abstracted as a fuel-bounded `SearchKernel`
premise; the final strong induction ties it to `searchSafe`.
-/

namespace TypePM

/-- The search-layer contract a strictly smaller fuel provides to the
expression layer. -/
def SearchKernel (signature : FrozenSig) (SF : RuntimeSigF)
    (fuel : Nat) : Prop :=
  ∀ {fuel' : Nat}, fuel' < fuel →
    ∀ {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state →
      Safe (fun substitutions => ∀ θ' ∈ substitutions,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise state, name ∈ Env.names θ')
        (searchFuel SF fuel' state)

/-- Weaken a search kernel to a smaller fuel bound. -/
theorem SearchKernel.weaken {signature : FrozenSig} {SF : RuntimeSigF}
    {fuel : Nat} (kernel : SearchKernel signature SF (fuel + 1)) :
    SearchKernel signature SF fuel :=
  fun {_fuel'} lt {_context} {_goal} {_state} typing wellScoped =>
    kernel (Nat.lt_succ_of_lt lt) typing wellScoped

/-- The names bound by a closure application. -/
private theorem pushArg_names {self : Option String} {ρ : Env}
    {param : String} {body : Expr} {arg : Value} :
    Env.names (pushArg self ρ param body arg) =
      param :: (selfNames self ++ Env.names ρ) := by
  cases self <;> rfl

/-- Equal zip arity pairs every left member with a right output. -/
private theorem List.exists_snd_mem_zip_of_fst_mem
    {lefts : List α} {rights : List β}
    (lengths : lefts.length = rights.length) {left : α}
    (member : left ∈ lefts) :
    ∃ right, (left, right) ∈ lefts.zip rights := by
  induction lefts generalizing rights with
  | nil => cases member
  | cons head lefts induction =>
      cases rights with
      | nil => simp at lengths
      | cons right rights =>
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨right, by
              rw [List.zip_cons_cons]; exact List.mem_cons_self⟩
          · obtain ⟨found, foundMember⟩ :=
              induction (by simpa using lengths) member
            exact ⟨found, by
              rw [List.zip_cons_cons]
              exact List.mem_cons_of_mem _ foundMember⟩

/-- Element free variables inject into the list free variables. -/
private theorem Expr.freeVarsList_mem_of_mem
    {exprs : List Expr} {expression : Expr} {name : String}
    (exprMember : expression ∈ exprs)
    (nameMember : name ∈ expression.freeVars) :
    name ∈ Expr.freeVarsList exprs := by
  induction exprs with
  | nil => cases exprMember
  | cons head exprs induction =>
      simp only [Expr.freeVarsList, List.mem_append]
      rcases List.mem_cons.mp exprMember with rfl | exprMember
      · exact .inl nameMember
      · exact .inr (induction exprMember)

/-- The primitive delta preserves scoping. -/
private theorem primEval_scoped {op : PrimOp} {values : List Value}
    {value : Value}
    (evaluation : primEval op values = some value)
    (valuesScoped : ∀ v ∈ values, ScopedValue v) :
    ScopedValue value := by
  cases op with
  | append =>
      cases values with
      | nil => exact nomatch evaluation
      | cons v₁ rest =>
          cases rest with
          | nil => exact nomatch evaluation
          | cons v₂ rest₂ =>
              cases rest₂ with
              | cons _ _ => exact nomatch evaluation
              | nil =>
                  cases h₁ : listOfV v₁ with
                  | none => simp [primEval, h₁] at evaluation
                  | some l₁ =>
                      cases h₂ : listOfV v₂ with
                      | none => simp [primEval, h₁, h₂] at evaluation
                      | some l₂ =>
                          simp [primEval, h₁, h₂] at evaluation
                          subst evaluation
                          refine mkListV_scoped ?_
                          intro element membership
                          rcases List.mem_append.mp membership with h | h
                          · exact listOfV_scoped
                              (valuesScoped v₁ (by simp)) h₁ element h
                          · exact listOfV_scoped
                              (valuesScoped v₂ (by simp)) h₂ element h
  | splits =>
      cases values with
      | nil => exact nomatch evaluation
      | cons v rest =>
          cases rest with
          | cons _ _ => exact nomatch evaluation
          | nil =>
              cases hDecode : listOfV v with
              | none => simp [primEval, hDecode] at evaluation
              | some l =>
                  simp [primEval, hDecode] at evaluation
                  subst evaluation
                  refine mkListV_scoped ?_
                  intro element membership
                  obtain ⟨index, _, rfl⟩ := List.mem_map.mp membership
                  refine ScopedValue.tuple
                    (.cons (mkListV_scoped ?_)
                      (.cons (mkListV_scoped ?_) .nil))
                  · intro x hx
                    exact listOfV_scoped (valuesScoped v (by simp)) hDecode
                      x (List.take_subset _ _ hx)
                  · intro x hx
                    exact listOfV_scoped (valuesScoped v (by simp)) hDecode
                      x (List.drop_subset _ _ hx)
  | submultisetSplits =>
      cases values with
      | nil => exact nomatch evaluation
      | cons v rest =>
          cases rest with
          | cons _ _ => exact nomatch evaluation
          | nil =>
              cases hDecode : listOfV v with
              | none => simp [primEval, hDecode] at evaluation
              | some elements =>
                  simp [primEval, hDecode] at evaluation
                  subst evaluation
                  refine mkListV_scoped ?_
                  intro splitValue membership
                  obtain ⟨⟨left, right⟩, splitMembership, rfl⟩ :=
                    List.mem_map.mp membership
                  obtain ⟨leftMembers, rightMembers⟩ :=
                    submultisetSplits_members splitMembership
                  refine ScopedValue.tuple
                    (.cons (mkListV_scoped ?_)
                      (.cons (mkListV_scoped ?_) .nil))
                  · intro x hx
                    exact listOfV_scoped (valuesScoped v (by simp)) hDecode
                      x (leftMembers x hx)
                  · intro x hx
                    exact listOfV_scoped (valuesScoped v (by simp)) hDecode
                      x (rightMembers x hx)
  | removeFirstChoice =>
      cases values with
      | nil => exact nomatch evaluation
      | cons needle rest =>
          cases rest with
          | nil => exact nomatch evaluation
          | cons input tail =>
              cases tail with
              | cons _ _ => exact nomatch evaluation
              | nil =>
                  cases hDecode : listOfV input with
                  | none => simp [primEval, hDecode] at evaluation
                  | some elements =>
                      simp [primEval, hDecode] at evaluation
                      subst evaluation
                      refine mkListV_scoped ?_
                      intro residueValue membership
                      obtain ⟨residue, residueMembership, rfl⟩ :=
                        List.mem_map.mp membership
                      refine mkListV_scoped ?_
                      intro element elementMembership
                      exact listOfV_scoped
                        (valuesScoped input (by simp)) hDecode element
                        (removeFirstChoice_members residueMembership element
                          elementMembership)

/-- Pointwise value typing of a successful list evaluation, recovered
relationally. -/
private theorem valueTys_of_zip
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF)
    {context : Context} {ρ : Env}
    (ρPristine : EnvPristine ρ) (ρTyped : EnvTyped signature context ρ) :
    ∀ {exprs : List Expr} {targets : List Ty} {values : List Value},
      exprs.length = targets.length →
      exprs.length = values.length →
      (∀ pair ∈ exprs.zip targets,
        TypingInvariant signature context pair.1 pair.2) →
      (∀ pair ∈ exprs.zip values, Eval SF ρ pair.1 pair.2) →
      ValueTys signature values targets := by
  intro exprs
  induction exprs with
  | nil =>
      intro targets values l1 l2 _ _
      cases targets with
      | cons _ _ => simp at l1
      | nil =>
          cases values with
          | cons _ _ => simp at l2
          | nil => exact .nil
  | cons e exprs induction =>
      intro targets values l1 l2 typings evals
      cases targets with
      | nil => simp at l1
      | cons τ targets =>
          cases values with
          | nil => simp at l2
          | cons v values =>
              refine .cons ?_ ?_
              · exact (EvalRuntimeSigAgrees.of_global agrees
                    (evals (e, v) (by
                      rw [List.zip_cons_cons]
                      exact List.mem_cons_self))).preservation
                  signatureWF ρPristine ρTyped
                  (typings (e, τ) (by
                    rw [List.zip_cons_cons]
                    exact List.mem_cons_self))
              · refine induction (by simpa using l1) (by simpa using l2)
                  ?_ ?_
                · intro pair membership
                  exact typings pair (by
                    rw [List.zip_cons_cons]
                    exact List.mem_cons_of_mem _ membership)
                · intro pair membership
                  exact evals pair (by
                    rw [List.zip_cons_cons]
                    exact List.mem_cons_of_mem _ membership)

mutual

/--
A typed expression in a typed, pristine, scoped environment that answers
its free variables cannot stick, and its value is scoped.
-/
theorem evalSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF) :
    ∀ {fuel : Nat} {context : Context} {ρ : Env} {expression : Expr}
      {target : Ty},
      TypingInvariant signature context expression target →
      EnvTyped signature context ρ → EnvPristine ρ → ScopedEnv ρ →
      (∀ name ∈ expression.freeVars, name ∈ Env.names ρ) →
      SearchKernel signature SF fuel →
      Safe ScopedValue (evalFuel SF fuel ρ expression)
  | 0, _, _, _, _, _, _, _, _, _, _ => Safe.timeout
  | fuel + 1, context, ρ, expression, target, typing, ρTyped, ρPristine,
      ρScoped, fv, kernel => by
    cases expression with
    | var name =>
        obtain ⟨value, found⟩ := Env.find?_isSome_of_mem_names
          (fv name (by simp [Expr.freeVars]))
        simp only [evalFuel, found]
        exact ρScoped.lookup found
    | lam param body =>
        simp only [evalFuel]
        refine ScopedValue.closure ρScoped ?_
        intro name membership
        by_cases hParam : name = param
        · exact hParam ▸ List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          exact fv name (by
            simp only [Expr.freeVars]
            exact List.mem_removeAll_of_mem membership (by simp [hParam]))
    | fix self param body =>
        simp only [evalFuel, selfClosure]
        refine ScopedValue.closure ρScoped ?_
        intro name membership
        by_cases hParam : name = param
        · exact hParam ▸ List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          by_cases hSelf : name = self
          · subst hSelf
            exact List.mem_append.mpr (.inl (by simp [selfNames]))
          · refine List.mem_append.mpr (.inr ?_)
            exact fv name (by
              simp only [Expr.freeVars]
              exact List.mem_removeAll_of_mem membership
                (by simp [hParam, hSelf]))
    | app fn arg =>
        obtain ⟨domain, codomain, fnTyping, argTyping⟩ := typing.app_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have fnRun := evalSafe signatureWF agrees fnTyping ρTyped
          ρPristine ρScoped
          (fun name h => fv name (by
            simp only [Expr.freeVars]
            exact List.mem_append.mpr (.inl h)))
          kernel.weaken
        cases hFn : evalFuel SF fuel ρ fn with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hFn] at fnRun
            exact fnRun.elim
        | ok fnValue =>
            rw [hFn] at fnRun
            have fnAgree := EvalRuntimeSigAgrees.of_global agrees
              (evalFuel_ok hFn)
            have fnTyped := fnAgree.preservation signatureWF ρPristine
              ρTyped fnTyping
            have fnPristine := fnAgree.pristine signatureWF ρPristine
            obtain ⟨self, closureEnv, param, body, rfl⟩ :=
              ValueTy.fn_inversion signatureWF fnTyped
            simp only [RunResult.bind_ok]
            have argRun := evalSafe signatureWF agrees argTyping ρTyped
              ρPristine ρScoped
              (fun name h => fv name (by
                simp only [Expr.freeVars]
                exact List.mem_append.mpr (.inr h)))
              kernel.weaken
            cases hArg : evalFuel SF fuel ρ arg with
            | timeout => exact Safe.timeout
            | stuck =>
                rw [hArg] at argRun
                exact argRun.elim
            | ok argValue =>
                rw [hArg] at argRun
                have argAgree := EvalRuntimeSigAgrees.of_global agrees
                  (evalFuel_ok hArg)
                have argTyped := argAgree.preservation signatureWF
                  ρPristine ρTyped argTyping
                have argPristine := argAgree.pristine signatureWF
                  ρPristine
                simp only [RunResult.bind_ok]
                obtain ⟨bodyContext, pushTyped, bodyTyping⟩ :=
                  pushArg_typed fnTyped argTyped
                cases fnRun with
                | closure closureEnvScoped bodyFv =>
                cases fnPristine with
                | closure closureEnvPristine =>
                have pushScoped :
                    ScopedEnv (pushArg self closureEnv param body
                      argValue) := by
                  cases self with
                  | none => exact .cons argRun closureEnvScoped
                  | some selfName =>
                      exact .cons argRun
                        (.cons (ScopedValue.closure closureEnvScoped
                          bodyFv) closureEnvScoped)
                refine evalSafe signatureWF agrees bodyTyping pushTyped
                  (pushArg_pristine closureEnvPristine argPristine)
                  pushScoped ?_ kernel.weaken
                intro name membership
                rw [pushArg_names]
                exact bodyFv name membership
    | lit n =>
        simp only [evalFuel]
        exact ScopedValue.lit
    | something =>
        simp only [evalFuel]
        exact ScopedValue.something
    | tuple exprs =>
        obtain ⟨targets, exprsTyping⟩ := typing.tuple_facts
        obtain ⟨lengths, pointwise⟩ := exprsTyping.zip_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have listRun := evalListSafe signatureWF agrees
          (fun e membership =>
            (List.exists_snd_mem_zip_of_fst_mem lengths membership).elim
              (fun τ pairMembership => ⟨τ, pointwise _ pairMembership⟩))
          ρTyped ρPristine ρScoped
          (fun e membership name h =>
            fv name (by
              simp only [Expr.freeVars]
              exact Expr.freeVarsList_mem_of_mem membership h))
          kernel.weaken
        cases hList : evalListFuel SF fuel ρ exprs with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hList] at listRun
            exact listRun.elim
        | ok values =>
            rw [hList] at listRun
            simp only [RunResult.bind_ok]
            exact ScopedValue.tuple listRun
    | ctor name exprs =>
        obtain ⟨scheme, targets, result, _, _, exprsTyping⟩ :=
          typing.ctorE_facts
        obtain ⟨lengths, pointwise⟩ := exprsTyping.zip_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have listRun := evalListSafe signatureWF agrees
          (fun e membership =>
            (List.exists_snd_mem_zip_of_fst_mem lengths membership).elim
              (fun τ pairMembership => ⟨τ, pointwise _ pairMembership⟩))
          ρTyped ρPristine ρScoped
          (fun e membership nm h =>
            fv nm (by
              simp only [Expr.freeVars]
              exact Expr.freeVarsList_mem_of_mem membership h))
          kernel.weaken
        cases hList : evalListFuel SF fuel ρ exprs with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hList] at listRun
            exact listRun.elim
        | ok values =>
            rw [hList] at listRun
            simp only [RunResult.bind_ok]
            exact ScopedValue.ctor listRun
    | prim op exprs =>
        obtain ⟨scheme, targets, result, found, instanceTyping,
          exprsTyping⟩ := typing.prim_facts
        obtain ⟨lengths, pointwise⟩ := exprsTyping.zip_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have listRun := evalListSafe signatureWF agrees
          (fun e membership =>
            (List.exists_snd_mem_zip_of_fst_mem lengths membership).elim
              (fun τ pairMembership => ⟨τ, pointwise _ pairMembership⟩))
          ρTyped ρPristine ρScoped
          (fun e membership nm h =>
            fv nm (by
              simp only [Expr.freeVars]
              exact Expr.freeVarsList_mem_of_mem membership h))
          kernel.weaken
        cases hList : evalListFuel SF fuel ρ exprs with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hList] at listRun
            exact listRun.elim
        | ok values =>
            rw [hList] at listRun
            simp only [RunResult.bind_ok]
            obtain ⟨valueLengths, valuePointwise⟩ := evalListFuel_ok hList
            have valuesTyped := valueTys_of_zip signatureWF agrees
              ρPristine ρTyped lengths valueLengths pointwise
              valuePointwise
            obtain ⟨value, primOk⟩ := primEval_isSome signatureWF found
              instanceTyping valuesTyped
            simp only [primOk]
            exact primEval_scoped primOk (ScopedValues.mem listRun)
    | letE letName bound body =>
        obtain ⟨valueTy, bodyTy, boundTyping, bodyTyping⟩ :=
          typing.letE_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have boundRun := evalSafe signatureWF agrees boundTyping ρTyped
          ρPristine ρScoped
          (fun name h => fv name (by
            simp only [Expr.freeVars]
            exact List.mem_append.mpr (.inl h)))
          kernel.weaken
        cases hBound : evalFuel SF fuel ρ bound with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hBound] at boundRun
            exact boundRun.elim
        | ok boundValue =>
            rw [hBound] at boundRun
            simp only [RunResult.bind_ok]
            have boundAgree := EvalRuntimeSigAgrees.of_global agrees
              (evalFuel_ok hBound)
            have boundPristine := boundAgree.pristine signatureWF
              ρPristine
            have valueInstances :
                ∀ target',
                  (signature.generalize context valueTy).ValueFlowInst
                    target' →
                  ValueTy signature boundValue target' :=
              fun target' instanceTyping =>
                boundAgree.preservation signatureWF ρPristine ρTyped
                  ((boundTyping.generalizedValueFlow
                    signatureWF.armExhaustiveBasic) instanceTyping)
            refine evalSafe signatureWF agrees bodyTyping
              (EnvTyped.consScheme valueInstances ρTyped)
              (.cons boundPristine ρPristine)
              (.cons boundRun ρScoped) ?_ kernel.weaken
            intro name membership
            by_cases hName : name = letName
            · exact hName ▸ List.mem_cons_self
            · refine List.mem_cons_of_mem _ ?_
              exact fv name (by
                simp only [Expr.freeVars]
                exact List.mem_append.mpr (.inr
                  (List.mem_removeAll_of_mem membership
                    (by simp [hName]))))
    | matcher clauses =>
        simp only [evalFuel]
        have clausesScoped : ScopedClauses (Env.names ρ) clauses :=
          fun name h => fv name (by simpa [Expr.freeVars] using h)
        exact ScopedValue.matcherV ρScoped clausesScoped clausesScoped
    | matchAll matchTarget matcher pattern body =>
        obtain ⟨prevailing, targetTy, patternCap, result, bindings,
          targetTyping, patternTyping, matcherTyping, bodyTyping⟩ :=
          typing.matchAll_facts
        simp only [evalFuel, RunResult.monad_bind_eq_bind]
        have targetRun := evalSafe signatureWF agrees targetTyping ρTyped
          ρPristine ρScoped
          (fun name h => fv name (by
            simp only [Expr.freeVars]
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl h)))))))
          kernel.weaken
        cases hTarget : evalFuel SF fuel ρ matchTarget with
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hTarget] at targetRun
            exact targetRun.elim
        | ok targetValue =>
            rw [hTarget] at targetRun
            have targetAgree := EvalRuntimeSigAgrees.of_global agrees
              (evalFuel_ok hTarget)
            have targetTyped := targetAgree.preservation signatureWF
              ρPristine ρTyped targetTyping
            have targetPristine := targetAgree.pristine signatureWF
              ρPristine
            simp only [RunResult.bind_ok]
            have matcherRun := evalSafe signatureWF agrees matcherTyping
              ρTyped ρPristine ρScoped
              (fun name h => fv name (by
                simp only [Expr.freeVars]
                exact List.mem_append.mpr (.inl (List.mem_append.mpr
                  (.inl (List.mem_append.mpr (.inr h)))))))
              kernel.weaken
            cases hMatcher : evalFuel SF fuel ρ matcher with
            | timeout => exact Safe.timeout
            | stuck =>
                rw [hMatcher] at matcherRun
                exact matcherRun.elim
            | ok matcherValue =>
                rw [hMatcher] at matcherRun
                have matcherAgree := EvalRuntimeSigAgrees.of_global
                  agrees (evalFuel_ok hMatcher)
                have matcherTyped := matcherAgree.preservation
                  signatureWF ρPristine ρTyped matcherTyping
                have matcherPristine := matcherAgree.pristine signatureWF
                  ρPristine
                simp only [RunResult.bind_ok]
                have atomTyping :
                    AtomTy signature context [] []
                      ⟨pattern, matcherValue, targetValue⟩ bindings :=
                  .mk patternTyping
                    (matcherTyped.toMatcherUsable signatureWF)
                    targetTyped
                have stateTyping := atomTyping.initialState_typed
                  ρPristine matcherPristine targetPristine ρTyped
                have stateScoped :
                    ScopedState
                      ⟨[.atom ⟨pattern, matcherValue, targetValue⟩],
                        ρ, []⟩ :=
                  ⟨ρScoped, .nil,
                    .cons
                      ⟨fun name h => fv name (by
                        simp only [Expr.freeVars]
                        exact List.mem_append.mpr (.inl
                          (List.mem_append.mpr (.inr h)))),
                        matcherRun, targetRun⟩
                      .nil⟩
                have searchRun := kernel (Nat.lt_succ_self fuel)
                  stateTyping stateScoped
                cases hSearch : searchFuel SF fuel
                    ⟨[.atom ⟨pattern, matcherValue, targetValue⟩],
                      ρ, []⟩ with
                | timeout => exact Safe.timeout
                | stuck =>
                    rw [hSearch] at searchRun
                    exact searchRun.elim
                | ok substitutions =>
                    rw [hSearch] at searchRun
                    simp only [RunResult.bind_ok]
                    have substsRun := evalSubstsSafe signatureWF agrees
                      bodyTyping ρTyped ρPristine ρScoped
                      (fun θ' membership => by
                        obtain ⟨typed, pristine, scopedEnv, promise⟩ :=
                          searchRun θ' membership
                        refine ⟨typed, pristine, scopedEnv, ?_⟩
                        intro name nameMembership
                        rw [Env.names_append]
                        by_cases hIn : name ∈ pattern.scopeVars
                        · exact List.mem_append.mpr (.inl (promise name
                            (by simp [statePromise, stackBinders, hIn])))
                        · exact List.mem_append.mpr (.inr (fv name (by
                            simp only [Expr.freeVars]
                            exact List.mem_append.mpr (.inr
                              (List.mem_removeAll_of_mem nameMembership
                                hIn))))))
                      kernel.weaken
                    cases hSubsts : evalSubstsFuel SF fuel ρ body
                        substitutions with
                    | timeout => exact Safe.timeout
                    | stuck =>
                        rw [hSubsts] at substsRun
                        exact substsRun.elim
                    | ok values =>
                        rw [hSubsts] at substsRun
                        simp only [RunResult.bind_ok]
                        exact mkListV_scoped (ScopedValues.mem substsRun)

/-- Pointwise expression-list evaluation is safe. -/
theorem evalListSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF) :
    ∀ {fuel : Nat} {context : Context} {ρ : Env} {exprs : List Expr},
      (∀ e ∈ exprs, ∃ τ, TypingInvariant signature context e τ) →
      EnvTyped signature context ρ → EnvPristine ρ → ScopedEnv ρ →
      (∀ e ∈ exprs, ∀ name ∈ e.freeVars, name ∈ Env.names ρ) →
      SearchKernel signature SF fuel →
      Safe ScopedValues (evalListFuel SF fuel ρ exprs)
  | 0, _, _, _, _, _, _, _, _, _ => Safe.timeout
  | _ + 1, _, _, [], _, _, _, _, _, _ => ScopedValues.nil
  | fuel + 1, context, ρ, e :: exprs, typings, ρTyped, ρPristine,
      ρScoped, fvs, kernel => by
      simp only [evalListFuel, RunResult.monad_bind_eq_bind]
      obtain ⟨τ, headTyping⟩ := typings e List.mem_cons_self
      have headRun := evalSafe signatureWF agrees headTyping ρTyped
        ρPristine ρScoped (fvs e List.mem_cons_self) kernel.weaken
      cases hHead : evalFuel SF fuel ρ e with
      | timeout => exact Safe.timeout
      | stuck =>
          rw [hHead] at headRun
          exact headRun.elim
      | ok value =>
          rw [hHead] at headRun
          simp only [RunResult.bind_ok]
          have tailRun := evalListSafe signatureWF agrees
            (fun candidate membership =>
              typings candidate (List.mem_cons_of_mem _ membership))
            ρTyped ρPristine ρScoped
            (fun candidate membership =>
              fvs candidate (List.mem_cons_of_mem _ membership))
            kernel.weaken
          cases hTail : evalListFuel SF fuel ρ exprs with
          | timeout => exact Safe.timeout
          | stuck =>
              rw [hTail] at tailRun
              exact tailRun.elim
          | ok values =>
              rw [hTail] at tailRun
              simp only [RunResult.bind_ok]
              exact .cons headRun tailRun

/-- Per-substitution body evaluation is safe. -/
theorem evalSubstsSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF) :
    ∀ {fuel : Nat} {context : Context} {ρ : Env} {body : Expr}
      {substitutions : List MatchSubst} {bindings : MonoCtx}
      {result : Ty},
      TypingInvariant signature (bindings.toContext ++ context) body
        result →
      EnvTyped signature context ρ → EnvPristine ρ → ScopedEnv ρ →
      (∀ θ' ∈ substitutions,
        MatchSubstTyped signature bindings θ' ∧ EnvPristine θ' ∧
        ScopedEnv θ' ∧
        ∀ name ∈ body.freeVars, name ∈ Env.names (θ' ++ ρ)) →
      SearchKernel signature SF fuel →
      Safe ScopedValues (evalSubstsFuel SF fuel ρ body substitutions)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => Safe.timeout
  | _ + 1, _, _, _, [], _, _, _, _, _, _, _, _ => ScopedValues.nil
  | fuel + 1, context, ρ, body, θ' :: substitutions, bindings, result,
      bodyTyping, ρTyped, ρPristine, ρScoped, facts, kernel => by
      simp only [evalSubstsFuel, RunResult.monad_bind_eq_bind]
      obtain ⟨θTyped, θPristine, θScoped, headFv⟩ :=
        facts θ' List.mem_cons_self
      have headRun := evalSafe signatureWF agrees bodyTyping
        (θTyped.envTyped_append ρTyped) (θPristine.append ρPristine)
        (ScopedEnv.append θScoped ρScoped) headFv kernel.weaken
      cases hHead : evalFuel SF fuel (θ' ++ ρ) body with
      | timeout => exact Safe.timeout
      | stuck =>
          rw [hHead] at headRun
          exact headRun.elim
      | ok value =>
          rw [hHead] at headRun
          simp only [RunResult.bind_ok]
          have tailRun := evalSubstsSafe signatureWF agrees bodyTyping
            ρTyped ρPristine ρScoped
            (fun candidate membership =>
              facts candidate (List.mem_cons_of_mem _ membership))
            kernel.weaken
          cases hTail : evalSubstsFuel SF fuel ρ body substitutions with
          | timeout => exact Safe.timeout
          | stuck =>
              rw [hTail] at tailRun
              exact tailRun.elim
          | ok values =>
              rw [hTail] at tailRun
              simp only [RunResult.bind_ok]
              exact .cons headRun tailRun

end

end TypePM
