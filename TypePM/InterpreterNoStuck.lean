import TypePM.InterpreterEvalSafe

/-!
# The no-stuck strong induction

`NoStuckAt signature SF fuel` bundles every interpreter layer's safety
statement at exactly one fuel.  `noStuck_master` closes the bundle for all
fuels by strong induction: each layer's standalone kernel-premised theorem
is instantiated with the bundle at strictly smaller fuels.

The clause-dispatch walk (`dispatchFuel`) enters through the explicit
`DispatchKernelAt` hypothesis, discharged separately by the dispatch/ppm
modules.
-/

namespace TypePM

/-- Every interpreter layer's safety statement at one fuel. -/
structure NoStuckAt (signature : FrozenSig) (SF : RuntimeSigF)
    (fuel : Nat) : Prop where
  eval :
    ∀ {context : Context} {ρ : Env} {expression : Expr} {target : Ty},
      TypingInvariant signature context expression target →
      EnvTyped signature context ρ → EnvPristine ρ → ScopedEnv ρ →
      (∀ name ∈ expression.freeVars, name ∈ Env.names ρ) →
      Safe ScopedValue (evalFuel SF fuel ρ expression)
  matom :
    ∀ {context : Context} {parameters : PatternCtx}
      {input output : MonoCtx} {ρa : Env}
      {pattern : Pattern} {matcher value : Value},
      AtomTy signature context parameters input ⟨pattern, matcher, value⟩
        output →
      (∀ name arguments, pattern ≠ .papp name arguments) →
      (∀ name, pattern ≠ .embed name) →
      EnvTyped signature (input.toContext ++ context) ρa →
      EnvPristine ρa → ScopedEnv ρa →
      (∀ name ∈ Pattern.exprVarsUnder [] pattern,
        name ∈ Env.names ρa) →
      ScopedValue matcher → ScopedValue value →
      ValuePristine matcher → ValuePristine value →
      Safe (MatomOutputScoped (Env.names ρa) pattern)
        (matomFuel SF fuel ρa pattern matcher value)
  step :
    ∀ {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
      {state : MState},
      MStateTyAt signature context parameters state goal →
      ScopedState state → state.S ≠ [] → HeadNotEmbed state →
      Safe (fun states => ∀ next ∈ states,
          ScopedState next ∧
          ∀ name ∈ statePromise state, name ∈ statePromise next)
        (stepFuel SF fuel state)
  search :
    ∀ {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state →
      Safe (fun substitutions => ∀ θ' ∈ substitutions,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise state, name ∈ Env.names θ')
        (searchFuel SF fuel state)

/-- The clause-dispatch contract the strong induction owes the atom
layer, at one fuel, given the bundle below it. -/
def DispatchKernelAt (signature : FrozenSig) (SF : RuntimeSigF)
    (fuel : Nat) : Prop :=
  ∀ {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {ρa : Env}
    {pattern : Pattern} {matcher value : Value}
    {matcherEnv : Env} {original current : List Clause},
    AtomTy signature context parameters input ⟨pattern, matcher, value⟩
      output →
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
      (dispatchFuel SF fuel ρa matcherEnv pattern value current)

/-- At fuel zero every layer times out. -/
theorem NoStuckAt.zero (signature : FrozenSig) (SF : RuntimeSigF) :
    NoStuckAt signature SF 0 where
  eval := by intros; exact Safe.timeout
  matom := by intros; exact Safe.timeout
  step := by intros; exact Safe.timeout
  search := by intros; exact Safe.timeout

/--
The strong induction: given the dispatch contract at every fuel (relative
to the bundle strictly below it), every layer is safe at every fuel.
-/
theorem noStuck_master
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF)
    (runtimeScoped : RuntimeSigScoped SF)
    (dispatchDischarge :
      ∀ fuel, (∀ fuel' < fuel, NoStuckAt signature SF fuel') →
        DispatchKernelAt signature SF fuel) :
    ∀ fuel, NoStuckAt signature SF fuel := by
  have strong : ∀ fuel fuel', fuel' ≤ fuel →
      NoStuckAt signature SF fuel' := by
    intro fuel
    induction fuel with
    | zero =>
        intro fuel' le
        rw [Nat.le_zero.mp le]
        exact NoStuckAt.zero signature SF
    | succ fuel IH =>
        intro fuel' le
        rcases Nat.eq_or_lt_of_le le with rfl | lt
        · -- the bundle strictly below `fuel + 1`
          have below : ∀ fuel'' < fuel + 1,
              NoStuckAt signature SF fuel'' :=
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
            intro context parameters input output ρa pattern matcher value
              typing notPatfun notEmbed envTyped envPristine envScoped
              ambient matcherScoped
              valueScoped matcherPristine valuePristine
            refine matomSafe signatureWF notPatfun notEmbed typing envTyped
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
            intro context parameters goal state typing wellScoped nonterminal
              headNotEmbed
            refine stepSafe signatureWF agrees runtimeScoped typing wellScoped
              nonterminal headNotEmbed ?_ ?_
            · intro fuel'' lt'' input output pattern matcher value
                atomTyping notPatfun notEmbed combinedTyped ambient
                matcherScoped valueScoped matcherPristine valuePristine
              exact (below fuel'' lt'').matom atomTyping notPatfun notEmbed
                combinedTyped
                (typing.1.2.2.append typing.1.2.1)
                (ScopedEnv.append wellScoped.2.1 wellScoped.1)
                ambient matcherScoped valueScoped matcherPristine
                valuePristine
            · intro fuel'' lt'' parameters' goal' state' typing'
                wellScoped' nonterminal' headNotEmbed'
              exact (below fuel'' lt'').step typing' wellScoped'
                nonterminal' headNotEmbed'
          · -- search layer
            intro context goal state typing wellScoped
            exact searchSafe signatureWF agrees typing wellScoped
              (fun {fuel''} lt'' {state'} typing' wellScoped'
                  nonterminal' headNotEmbed' =>
                (below fuel'' lt'').step typing' wellScoped'
                  nonterminal' headNotEmbed')
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
closed program never sticks, at any fuel.  This theorem does not itself
classify an all-fuel timeout as divergence.
-/
theorem typed_never_stuck_of_dispatch
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF)
    (runtimeScoped : RuntimeSigScoped SF)
    (dispatchDischarge :
      ∀ fuel, (∀ fuel' < fuel, NoStuckAt signature SF fuel') →
        DispatchKernelAt signature SF fuel)
    {expression : Expr} {target : Ty}
    (typing : TypingInvariant signature [] expression target)
    (closed : expression.freeVars = [])
    (fuel : Nat) :
    evalFuel SF fuel [] expression ≠ .stuck :=
  ((noStuck_master signatureWF agrees runtimeScoped dispatchDischarge fuel
      ).eval typing
      (envTyped_nil signature) .nil .nil
      (fun name membership => by
        rw [closed] at membership
        cases membership)).not_stuck

end TypePM
