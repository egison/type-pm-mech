import TypePM.InterpreterEvalSafe

/-!
# The no-stuck strong induction

`NoStuckAt signature fuel` bundles every interpreter layer's safety
statement at exactly one fuel.  `noStuck_master` closes the bundle for all
fuels by strong induction: each layer's standalone kernel-premised theorem
is instantiated with the bundle at strictly smaller fuels.

The clause-dispatch walk (`dispatchFuel`) enters through the explicit
`DispatchKernelAt` hypothesis, discharged separately by the dispatch/ppm
modules.
-/

namespace TypePM

/-- Every interpreter layer's safety statement at one fuel. -/
structure NoStuckAt (signature : FrozenSig) (fuel : Nat) : Prop where
  eval :
    ∀ {context : Context} {ρ : Env} {expression : Expr} {target : Ty},
      TypingInvariant signature context expression target →
      EnvTyped signature context ρ → EnvPristine ρ → ScopedEnv ρ →
      (∀ name ∈ expression.freeVars, name ∈ Env.names ρ) →
      Safe ScopedValue (evalFuel [] fuel ρ expression)
  matom :
    ∀ {context : Context} {input output : MonoCtx} {ρa : Env}
      {pattern : Pattern} {matcher value : Value},
      AtomTy signature context [] input ⟨pattern, matcher, value⟩
        output →
      EnvTyped signature (input.toContext ++ context) ρa →
      EnvPristine ρa → ScopedEnv ρa →
      (∀ name ∈ Pattern.exprVarsUnder [] pattern,
        name ∈ Env.names ρa) →
      ScopedValue matcher → ScopedValue value →
      ValuePristine matcher → ValuePristine value →
      Safe (MatomOutputScoped (Env.names ρa) pattern)
        (matomFuel [] fuel ρa pattern matcher value)
  step :
    ∀ {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state → state.S ≠ [] →
      Safe (fun states => ∀ next ∈ states,
          ScopedState next ∧
          ∀ name ∈ statePromise state, name ∈ statePromise next)
        (stepFuel [] fuel state)
  search :
    ∀ {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state →
      Safe (fun substitutions => ∀ θ' ∈ substitutions,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise state, name ∈ Env.names θ')
        (searchFuel [] fuel state)

/-- The clause-dispatch contract the strong induction owes the atom
layer, at one fuel, given the bundle below it. -/
def DispatchKernelAt (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {context : Context} {input output : MonoCtx} {ρa : Env}
    {pattern : Pattern} {matcher value : Value}
    {matcherEnv : Env} {original current : List Clause},
    AtomTy signature context [] input ⟨pattern, matcher, value⟩ output →
    EnvTyped signature (input.toContext ++ context) ρa →
    EnvPristine ρa → ScopedEnv ρa →
    (∀ name ∈ Pattern.exprVarsUnder [] pattern, name ∈ Env.names ρa) →
    ScopedValue matcher → ScopedValue value →
    ValuePristine matcher → ValuePristine value →
    matcher = .matcherV matcherEnv original current →
    Safe (fun dispatchOutput =>
        dispatchOutput.2 = ([] : MatchSubst) ∧
        ∀ atoms ∈ dispatchOutput.1,
          AtomsScoped (Env.names ρa) [] atoms ∧
          ∀ name ∈ pattern.scopeVars,
            name ∈ Pattern.scopeVarsList (atoms.map Atom.p))
      (dispatchFuel [] fuel ρa matcherEnv pattern value current)

/-- At fuel zero every layer times out. -/
theorem NoStuckAt.zero (signature : FrozenSig) :
    NoStuckAt signature 0 where
  eval := fun _ _ _ _ _ => Safe.timeout
  matom := fun _ _ _ _ _ _ _ _ _ => Safe.timeout
  step := fun _ _ _ => Safe.timeout
  search := fun _ _ => Safe.timeout

/--
The strong induction: given the dispatch contract at every fuel (relative
to the bundle strictly below it), every layer is safe at every fuel.
-/
theorem noStuck_master
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    (dispatchDischarge :
      ∀ fuel, (∀ fuel' < fuel, NoStuckAt signature fuel') →
        DispatchKernelAt signature fuel) :
    ∀ fuel, NoStuckAt signature fuel := by
  have strong : ∀ fuel fuel', fuel' ≤ fuel → NoStuckAt signature fuel' := by
    intro fuel
    induction fuel with
    | zero =>
        intro fuel' le
        rw [Nat.le_zero.mp le]
        exact NoStuckAt.zero signature
    | succ fuel IH =>
        intro fuel' le
        rcases Nat.eq_or_lt_of_le le with rfl | lt
        · -- the bundle strictly below `fuel + 1`
          have below : ∀ fuel'' < fuel + 1, NoStuckAt signature fuel'' :=
            fun fuel'' lt'' => IH fuel'' (Nat.le_of_lt_succ lt'')
          refine ⟨?_, ?_, ?_, ?_⟩
          · -- expression layer
            intro context ρ expression target typing ρTyped ρPristine
              ρScoped fv
            exact evalSafe signatureWF agrees typing ρTyped ρPristine
              ρScoped fv
              (fun {fuel''} lt'' {_context} {_goal} {_state} typing'
                  wellScoped' =>
                (below fuel'' lt'').search typing' wellScoped')
          · -- atom layer
            intro context input output ρa pattern matcher value typing
              envTyped envPristine envScoped ambient matcherScoped
              valueScoped matcherPristine valuePristine
            refine matomSafe signatureWF agrees rfl typing envTyped
              ambient matcherScoped valueScoped matcherPristine
              valuePristine ?_ ?_
            · -- embedded-evaluation kernel
              intro fuel'' lt'' expression target' typing' fv'
              have run := (below fuel'' lt'').eval typing' envTyped
                envPristine envScoped fv'
              refine ⟨run.not_stuck, ?_⟩
              intro v hv
              rw [hv] at run
              exact run
            · -- dispatch kernel
              intro fuel'' lt'' matcherEnv original current matcherEq
              exact dispatchDischarge fuel''
                (fun fuel''' lt''' => below fuel'''
                  (Nat.lt_trans lt''' lt''))
                typing envTyped envPristine envScoped ambient
                matcherScoped valueScoped matcherPristine valuePristine
                matcherEq
          · -- state layer
            intro context goal state typing wellScoped nonterminal
            refine stepSafe signatureWF agrees typing wellScoped
              nonterminal ?_
            intro fuel'' lt'' input output pattern matcher value
              atomTyping combinedTyped ambient matcherScoped valueScoped
              matcherPristine valuePristine
            exact (below fuel'' lt'').matom atomTyping combinedTyped
              (typing.1.2.2.append typing.1.2.1)
              (ScopedEnv.append wellScoped.2.1 wellScoped.1)
              ambient matcherScoped valueScoped matcherPristine
              valuePristine
          · -- search layer
            intro context goal state typing wellScoped
            exact searchSafe signatureWF agrees typing wellScoped
              (fun {fuel''} lt'' {state'} typing' wellScoped'
                  nonterminal' =>
                (below fuel'' lt'').step typing' wellScoped'
                  nonterminal')
        · exact IH fuel' (Nat.lt_succ_iff.mp lt)
  exact fun fuel => strong fuel fuel (Nat.le_refl fuel)

/-- A signature with no pattern functions agrees with the empty runtime
table in every context. -/
theorem runtimeSigAgrees_nil
    {signature : FrozenSig} (noPatternFuns : signature.patternFuns = [])
    (context : Context) :
    RuntimeSigAgrees signature context ([] : RuntimeSigF) where
  runtimeTyped := fun _ membership => nomatch membership
  sourceLookup := by
    intro name scheme found
    rw [FrozenSig.findPatternFun, noPatternFuns] at found
    cases found

/-- The empty environment is typed at the empty context. -/
theorem envTyped_nil (signature : FrozenSig) :
    EnvTyped signature [] ([] : Env) := by
  intro name value found
  simp [Env.find?] at found

/--
Expression-layer progress, relative to the dispatch contract: a typed
closed program never sticks, at any fuel.  Nontermination remains the
only way to fail to produce a value.
-/
theorem typed_never_stuck_of_dispatch
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    (dispatchDischarge :
      ∀ fuel, (∀ fuel' < fuel, NoStuckAt signature fuel') →
        DispatchKernelAt signature fuel)
    {expression : Expr} {target : Ty}
    (typing : TypingInvariant signature [] expression target)
    (closed : expression.freeVars = [])
    (fuel : Nat) :
    evalFuel [] fuel [] expression ≠ .stuck :=
  ((noStuck_master signatureWF agrees dispatchDischarge fuel).eval typing
      (envTyped_nil signature) .nil .nil
      (fun name membership => by
        rw [closed] at membership
        cases membership)).not_stuck

end TypePM
