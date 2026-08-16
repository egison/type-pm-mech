import TypePM.InterpreterNoStuck
import TypePM.InterpreterPpmPrimitive
import TypePM.InterpreterPpmSafe
import TypePM.InterpreterDispatchSafe
import TypePM.InterpreterCompleteness
import TypePM.Soundness

/-!
# Extraction lemmas for the dispatch discharge

The strong induction owes the atom layer a clause-dispatch contract
(`DispatchKernelAt`).  Discharging it starts from the matcher literal's
typing, pristineness, and scoping; this module packages the small
inversions that turn those value-level facts into the per-clause facts
the dispatch walk consumes.
-/

namespace TypePM

/-- A pristine matcher literal has its cursor at the start, over a
pristine capturing environment. -/
theorem ValuePristine.matcherV_start
    {ρm : Env} {original current : List Clause}
    (pristine : ValuePristine (.matcherV ρm original current)) :
    current = original ∧ EnvPristine ρm := by
  cases pristine with
  | matcherLiteral envPristine => exact ⟨rfl, envPristine⟩

/-- The three scoping facts a scoped matcher literal carries. -/
theorem ScopedValue.matcherV_fields
    {ρm : Env} {original current : List Clause}
    (wellScoped : ScopedValue (.matcherV ρm original current)) :
    ScopedEnv ρm ∧ ScopedClauses (Env.names ρm) original ∧
    ScopedClauses (Env.names ρm) current := by
  cases wellScoped with
  | matcherV envScoped originalScoped currentScoped =>
      exact ⟨envScoped, originalScoped, currentScoped⟩

/-- Per-clause scoping facts from a scoped clause list: the next-matcher
expression and every arm body (below its binders) see only the capturing
environment's names. -/
theorem ScopedClauses.clause_facts
    {names : List String} {clauses : List Clause}
    (wellScoped : ScopedClauses names clauses)
    {pp : PPat} {next : Expr} {arms : List Arm}
    (membership : Clause.mk pp next arms ∈ clauses) :
    (∀ name ∈ next.freeVars, name ∈ names) ∧
    (∀ dp body, Arm.mk dp body ∈ arms →
      ∀ name ∈ body.freeVars.removeAll (dp.bindVars ++ pp.bindVars),
        name ∈ names) := by
  constructor
  · intro name nameMembership
    refine wellScoped name (Clause.freeVars_mem_of_mem membership name ?_)
    simp only [Clause.freeVars]
    exact List.mem_append.mpr (.inl nameMembership)
  · intro dp body armMembership name nameMembership
    refine wellScoped name (Clause.freeVars_mem_of_mem membership name ?_)
    simp only [Clause.freeVars]
    exact List.mem_append.mpr (.inr
      (Arm.freeVars_mem_of_mem armMembership name nameMembership))

/-- The ordered (capture-admissible) clause-header kernel: below a
core-ordered header, the committed match cannot stick and a successful
capture environment is typed, pristine, and scoped. -/
theorem ppmPair_of_captureAdm
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {input : MonoCtx}
    {ρa : Env} {pp : PPat} {pattern : Pattern} {target : Ty}
    {ppBindings : MonoCtx}
    (admissible : CaptureAdm signature context input pp pattern target
      ppBindings)
    (ppOrder : PPatCoreOrder pp)
    (ambient : ∀ name ∈ Pattern.exprVarsUnder [] pattern,
      name ∈ Env.names ρa)
    {fuel : Nat}
    (evalKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {expression : Expr} {target' : Ty},
          TypingInvariant signature (input.toContext ++ context)
            expression target' →
          (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
          evalFuel SF fuel' ρa expression ≠ .stuck ∧
          ∀ v, evalFuel SF fuel' ρa expression = .ok v →
            ScopedValue v ∧ ValuePristine v ∧
            ValueTy signature v target') :
    ppmFuel SF fuel ρa pp pattern ≠ .stuck ∧
    ∀ captures ppEnv,
      ppmFuel SF fuel ρa pp pattern = .ok (some (captures, ppEnv)) →
      MonoEnvTys signature ppBindings ppEnv ∧
      EnvPristine ppEnv ∧ ScopedEnv ppEnv := by
  obtain ⟨finished, ordered⟩ := ppOrder
  have run := ppmSafe evalKernel admissible ordered (fun _ => rfl) ambient
  refine ⟨run.not_stuck, ?_⟩
  intro captures ppEnv hOk
  rw [hOk] at run
  exact run captures ppEnv rfl

/--
Discharge of the dispatch contract: a typed atom whose matcher is a
matcher literal drives the clause walk safely.  The ordered route
recovers capture admissibility from the clause order; the primitive
route analyzes the shallow header match directly.
-/
theorem dispatchKernelAt_discharge
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF) :
    ∀ fuel, (∀ fuel' < fuel, NoStuckAt signature SF fuel') →
      DispatchKernelAt signature SF fuel := by
  intro fuel below
  intro context parameters input output ρa pattern matcher value matcherEnv
    original current typing envTyped envPristine envScoped ambient matcherScoped
    valueScoped matcherPristine valuePristine matcherEq
  subst matcherEq
  obtain ⟨currentEq, matcherEnvPristine⟩ := matcherPristine.matcherV_start
  subst currentEq
  obtain ⟨matcherEnvScoped, originalScoped, -⟩ :=
    matcherScoped.matcherV_fields
  have evalKernelShared :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {context' : Context} {ρ' : Env} {e : Expr} {τ : Ty},
          TypingInvariant signature context' e τ →
          EnvTyped signature context' ρ' → EnvPristine ρ' →
          ScopedEnv ρ' →
          (∀ name ∈ e.freeVars, name ∈ Env.names ρ') →
          evalFuel SF fuel' ρ' e ≠ .stuck ∧
          ∀ v, evalFuel SF fuel' ρ' e = .ok v → ScopedValue v := by
    intro fuel' lt context' ρ' e τ t envT envP envS fv
    have run := (below fuel' lt).eval t envT envP envS fv
    refine ⟨run.not_stuck, ?_⟩
    intro v hv
    rw [hv] at run
    exact run
  have evalKernelRich :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {expression : Expr} {target' : Ty},
          TypingInvariant signature (input.toContext ++ context)
            expression target' →
          (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
          evalFuel SF fuel' ρa expression ≠ .stuck ∧
          ∀ v, evalFuel SF fuel' ρa expression = .ok v →
            ScopedValue v ∧ ValuePristine v ∧
            ValueTy signature v target' := by
    intro fuel' lt expression target' t fv
    have run := (below fuel' lt).eval t envTyped envPristine envScoped fv
    refine ⟨run.not_stuck, ?_⟩
    intro v hv
    rw [hv] at run
    have agree := EvalRuntimeSigAgrees.of_global agrees (evalFuel_ok hv)
    exact ⟨run, agree.pristine signatureWF envPristine,
      agree.preservation signatureWF envPristine envTyped t⟩
  cases typing with
  | mk patternTyping matcherTyping valueTyping =>
      obtain ⟨producerCapability, mTyping, demand⟩ := matcherTyping
      obtain ⟨matcherContext, matcherEnvTyped, _cursor, sourceTyping⟩ :=
        mTyping.matcherLiteral_inversion
      obtain ⟨evidence, clausesTyped, _shape, catchAll, armsExhaustive,
        _ppNodup, _armNodup, _coverage⟩ := sourceTyping.matcher_inversion
      rcases catchAll with ⟨before, catchNext, catchName, catchBody,
        originalEq, -⟩
      refine dispatchSafe signatureWF agrees clausesTyped armsExhaustive
        matcherEnvTyped matcherEnvPristine matcherEnvScoped
        originalScoped valueTyping valuePristine valueScoped ambient
        ?_ evalKernelShared (fun _ membership => membership) ?_
      · intro clause member shapeTrue prevailing' holes ppBindings
          ppTyping ppCaps ppOrder fuel' lt
        obtain ⟨finished, ordered⟩ := ppOrder
        have admissible := (captureAdm_of_order_at signatureWF
          ppTyping.terminal ordered (fun _ => rfl) ppCaps
          patternTyping.terminal demand shapeTrue).1
        exact ppmPair_of_captureAdm admissible ⟨finished, ordered⟩
          ambient (fun {fuel''} lt' =>
            evalKernelRich (Nat.lt_trans lt' lt))
      · exact ⟨.mk .hole catchNext [.mk (.var catchName) catchBody],
          by rw [originalEq]
             exact List.mem_append_right _ List.mem_cons_self,
          rfl⟩
  | primitive patternTyping primForm matcherAt valueTyping =>
      obtain ⟨consumerCapability, producerCapability, mTyping, demand⟩ :=
        matcherAt
      obtain ⟨matcherContext, matcherEnvTyped, _cursor, sourceTyping⟩ :=
        mTyping.matcherLiteral_inversion
      obtain ⟨evidence, clausesTyped, _shape, catchAll, armsExhaustive,
        _ppNodup, _armNodup, _coverage⟩ := sourceTyping.matcher_inversion
      rcases catchAll with ⟨before, catchNext, catchName, catchBody,
        originalEq, -⟩
      refine dispatchSafe signatureWF agrees clausesTyped armsExhaustive
        matcherEnvTyped matcherEnvPristine matcherEnvScoped
        originalScoped valueTyping valuePristine valueScoped ambient
        ?_ evalKernelShared (fun _ membership => membership) ?_
      · intro clause member shapeTrue prevailing' holes ppBindings
          ppTyping ppCaps ppOrder fuel' lt
        exact ppmSafe_primitive patternTyping primForm ppTyping shapeTrue
          ambient (fun {fuel''} lt' =>
            evalKernelRich (Nat.lt_trans lt' lt))
      · exact ⟨.mk .hole catchNext [.mk (.var catchName) catchBody],
          by rw [originalEq]
             exact List.mem_append_right _ List.mem_cons_self,
          rfl⟩

/--
**Expression-layer progress with a checked runtime table.**  A typed closed
program never sticks: for every fuel, the fuel-indexed reference interpreter
returns a value or times out, never a stuck configuration.
-/
theorem typed_never_stuck_runtime
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF)
    (runtimeScoped : RuntimeSigScoped SF)
    {expression : Expr} {target : Ty}
    (typing : TypingInvariant signature [] expression target)
    (closed : expression.freeVars = [])
    (fuel : Nat) :
    evalFuel SF fuel [] expression ≠ .stuck :=
  typed_never_stuck_of_dispatch signatureWF agrees runtimeScoped
    (dispatchKernelAt_discharge signatureWF agrees) typing closed fuel

/-- For a typed closed program, timing out at every fuel is equivalent to the
absence of a finite relational evaluation.  The right-hand side is deliberately
not called divergence: relating it to a separate coinductive divergence
judgment would require another theorem. -/
theorem typed_all_timeout_iff_no_finite_eval
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context SF)
    (runtimeScoped : RuntimeSigScoped SF)
    {expression : Expr} {target : Ty}
    (typing : TypingInvariant signature [] expression target)
    (closed : expression.freeVars = []) :
    (∀ fuel, evalFuel SF fuel [] expression = .timeout) ↔
      ¬∃ value, Eval SF [] expression value := by
  constructor
  · intro allTimeout finite
    obtain ⟨value, evaluation⟩ := finite
    obtain ⟨threshold, persistent⟩ := evalFuel_eventually_ok evaluation
    have success : evalFuel SF threshold [] expression = .ok value := by
      simpa using persistent 0
    rw [allTimeout threshold] at success
    cases success
  · intro noFinite fuel
    cases run : evalFuel SF fuel [] expression with
    | timeout => rfl
    | stuck =>
        exact absurd run
          (typed_never_stuck_runtime signatureWF agrees runtimeScoped
            typing closed fuel)
    | ok value =>
        exact (noFinite ⟨value, evalFuel_ok run⟩).elim

/-- Empty-runtime specialization retained for the paper-1 fragment. -/
theorem typed_never_stuck
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    {expression : Expr} {target : Ty}
    (typing : TypingInvariant signature [] expression target)
    (closed : expression.freeVars = [])
    (fuel : Nat) :
    evalFuel [] fuel [] expression ≠ .stuck :=
  typed_never_stuck_runtime signatureWF agrees runtimeSigScoped_nil
    typing closed fuel

namespace SourceTyping

/-- Paper-1 source-facing no-stuck theorem.  The fragment explicitly has no
source pattern-function definitions, so the empty runtime table satisfies the
required agreement in every source context. -/
theorem never_stuck_paper1
    {signature : FrozenSig} {expression : Expr} {target : Ty}
    (signatureWF : FrozenSigWF signature)
    (noPatternFuns : signature.patternFuns = [])
    (typing : SourceTyping signature [] expression target)
    (closed : expression.freeVars = [])
    (fuel : Nat) :
    evalFuel [] fuel [] expression ≠ .stuck :=
  typed_never_stuck signatureWF (runtimeSigAgrees_nil noPatternFuns)
    (typing.typingInvariant signatureWF.schemesClosed) closed fuel

/-- Paper-1 specialization of the exact all-fuel-timeout characterization. -/
theorem all_timeout_iff_no_finite_eval_paper1
    {signature : FrozenSig} {expression : Expr} {target : Ty}
    (signatureWF : FrozenSigWF signature)
    (noPatternFuns : signature.patternFuns = [])
    (typing : SourceTyping signature [] expression target)
    (closed : expression.freeVars = []) :
    (∀ fuel, evalFuel [] fuel [] expression = .timeout) ↔
      ¬∃ value, Eval [] [] expression value :=
  typed_all_timeout_iff_no_finite_eval signatureWF
    (runtimeSigAgrees_nil noPatternFuns) runtimeSigScoped_nil
    (typing.typingInvariant signatureWF.schemesClosed) closed

end SourceTyping

end TypePM
