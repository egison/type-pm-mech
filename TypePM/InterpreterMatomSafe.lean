import TypePM.InterpreterSafetyDefs
import TypePM.InterpreterAdequacy
import TypePM.Readiness
import TypePM.InterpreterInversions

/-!
# Atom-level safety of the fuel-indexed interpreter

`matomSafe` is the functional twin of `MAtomReady.of_typed`: a typed atom in
a scoped, pristine, typed environment cannot stick, and its successful
outputs are scoped.  The matcher-dispatch case is received through a
fuel-bounded kernel (discharged by the dispatch-walk module), and the
embedded value-pattern evaluation through a fuel-bounded evaluation kernel
(discharged by the master induction).

The statement is polymorphic in the pattern-parameter context and runtime
table.  Its caller supplies the two local facts that the atom being sent to
`matomFuel` is neither a pattern-function application nor an embedded
parameter; `stepSafe` handles those forms before entering this layer.
-/

namespace TypePM

/-- Scoped outputs of one atom reduction: the new bindings are scoped, each
continuation branch is scoped under the new bindings and the ambient names,
and the pattern's guaranteed binders are covered by the new bindings
together with each branch's remaining binders. -/
def MatomOutputScoped (ambient : List String) (pattern : Pattern)
    (output : List (List Atom) × MatchSubst) : Prop :=
  ScopedEnv output.2 ∧
  ∀ atoms ∈ output.1,
    AtomsScoped (Env.names output.2 ++ ambient) [] atoms ∧
    ∀ name ∈ pattern.scopeVars,
      name ∈ Env.names output.2 ++ Pattern.scopeVarsList (atoms.map Atom.p)

/-- Removal of nothing removes nothing. -/
theorem List.removeAll_nil (l : List String) : l.removeAll [] = l := by
  simp [List.removeAll]

/-- Threaded expression scoping yields capture scoping. -/
theorem CapturedScoped.of_exprVars {scope : List String} :
    ∀ {patterns : List Pattern} {bound : List String},
      (∀ name ∈ Pattern.exprVarsUnderList bound patterns, name ∈ scope) →
      CapturedScoped scope bound patterns
  | [], _, _ => trivial
  | pattern :: patterns, bound, ambient => by
      refine ⟨?_, ?_⟩
      · intro name membership
        rcases Pattern.mem_exprVarsUnder_extend (bs := [])
            (bound := bound) membership with h | h
        · refine .inl (ambient name ?_)
          simp only [Pattern.exprVarsUnderList, List.mem_append]
          exact .inl (by simpa using h)
        · exact .inr h
      · refine CapturedScoped.of_exprVars ?_
        intro name membership
        refine ambient name ?_
        simp only [Pattern.exprVarsUnderList, List.mem_append]
        exact .inr membership

/-- Zipped continuation atoms project back to their patterns. -/
theorem zipAtoms_map_p :
    ∀ {patterns : List Pattern} {matchers values : List Value},
      matchers.length = patterns.length →
      values.length = patterns.length →
      ((patterns.zip (matchers.zip values)).map fun entry =>
        (⟨entry.1, entry.2.1, entry.2.2⟩ : Atom)).map Atom.p = patterns
  | [], _, _, _, _ => rfl
  | pattern :: patterns, matcher :: matchers, value :: values,
      mlen, vlen => by
      simp only [List.zip_cons_cons, List.map_cons]
      exact congrArg (List.cons pattern)
        (zipAtoms_map_p (by simpa using mlen) (by simpa using vlen))
  | _ :: _, [], _, mlen, _ => by simp at mlen
  | _ :: _, _ :: _, [], _, vlen => by simp at vlen

/-- Component count of a product matcher value at an exposed product type. -/
theorem ValueTy.matcherProduct_length
    {signature : FrozenSig} {matchers : List Value} {capability : Cap}
    {targets : List Ty}
    (typing : ValueTy signature (.tuple matchers)
      (.matcher capability (.prod targets))) :
    matchers.length = targets.length := by
  cases typing with
  | matcherProduct fieldsTyped =>
      simpa using ValueTys.length fieldsTyped

/--
A typed atom in a scoped, pristine, typed environment reduces safely: no
stuck configuration, and the outputs are scoped.  The dispatch and
evaluation obligations arrive as fuel-bounded kernels.
-/
theorem matomSafe
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {ρa : Env}
    {pattern : Pattern} {matcher value : Value} {fuel : Nat}
    (notPatfun : ∀ name arguments, pattern ≠ .papp name arguments)
    (notEmbed : ∀ name, pattern ≠ .embed name)
    (typing : AtomTy signature context parameters input
      ⟨pattern, matcher, value⟩ output)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) ρa)
    (ambient : ∀ name ∈ Pattern.exprVarsUnder [] pattern,
      name ∈ Env.names ρa)
    (matcherScoped : ScopedValue matcher)
    (valueScoped : ScopedValue value)
    (matcherPristine : ValuePristine matcher)
    (valuePristine : ValuePristine value)
    (evalKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {expression : Expr} {target : Ty},
          TypingInvariant signature (input.toContext ++ context) expression
            target →
          (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
          evalFuel SF fuel' ρa expression ≠ .stuck ∧
          ∀ v, evalFuel SF fuel' ρa expression = .ok v → ScopedValue v)
    (dispatchKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {matcherEnv : Env} {original current : List Clause},
          matcher = .matcherV matcherEnv original current →
          Safe (fun dispatchOutput =>
            dispatchOutput.2 = ([] : MatchSubst) ∧
            ∀ atoms ∈ dispatchOutput.1,
              AtomsScoped (Env.names ρa) [] atoms ∧
              ∀ name ∈ pattern.scopeVars,
                name ∈ Pattern.scopeVarsList (atoms.map Atom.p))
            (dispatchFuel SF fuel' ρa matcherEnv pattern value current)) :
    Safe (MatomOutputScoped (Env.names ρa) pattern)
      (matomFuel SF fuel ρa pattern matcher value) := by
  cases fuel with
  | zero => exact Safe.timeout
  | succ fuel =>
  cases typing with
  | mk patternTyping matcherTyping valueTyping =>
      obtain ⟨producerCapability, mTyping, demand⟩ := matcherTyping
      cases pattern with
      | pand left right =>
          refine ⟨.nil, ?_⟩
          intro atoms membership
          rcases List.mem_cons.mp membership with rfl | membership
          · refine ⟨⟨?_, matcherScoped, valueScoped, ?_, matcherScoped,
              valueScoped, trivial⟩, ?_⟩
            · intro name nameMembership
              refine .inl (ambient name ?_)
              simp only [Pattern.exprVarsUnder, List.mem_append]
              exact .inl nameMembership
            · intro name nameMembership
              rcases Pattern.mem_exprVarsUnder_extend (bs := [])
                  (bound := [] ++ left.scopeVars) nameMembership with h | h
              · refine .inl (ambient name ?_)
                simp only [Pattern.exprVarsUnder, List.mem_append]
                exact .inr (by simpa using h)
              · exact .inr (by simpa using h)
            · intro name nameMembership
              refine List.mem_append.mpr (.inr ?_)
              simp only [List.map_cons, List.map_nil, Pattern.scopeVarsList]
              rcases List.mem_append.mp
                  (by simpa [Pattern.scopeVars] using nameMembership)
                  with h | h
              · exact List.mem_append.mpr (.inl h)
              · exact List.mem_append.mpr
                  (.inr (List.mem_append.mpr (.inl h)))
          · cases membership
      | por left right =>
          refine ⟨.nil, ?_⟩
          intro atoms membership
          rcases List.mem_cons.mp membership with rfl | membership
          · refine ⟨⟨?_, matcherScoped, valueScoped, trivial⟩, ?_⟩
            · intro name nameMembership
              refine .inl (ambient name ?_)
              simp only [Pattern.exprVarsUnder, List.mem_append]
              exact .inl nameMembership
            · intro name nameMembership
              refine List.mem_append.mpr (.inr ?_)
              simp only [List.map_cons, List.map_nil,
                Pattern.scopeVarsList]
              refine List.mem_append.mpr (.inl ?_)
              have both : name ∈ left.scopeVars ∧
                  name ∈ right.scopeVars := by
                simpa [Pattern.scopeVars] using nameMembership
              exact both.1
          · rcases List.mem_cons.mp membership with rfl | membership
            · refine ⟨⟨?_, matcherScoped, valueScoped, trivial⟩, ?_⟩
              · intro name nameMembership
                refine .inl (ambient name ?_)
                simp only [Pattern.exprVarsUnder, List.mem_append]
                exact .inr nameMembership
              · intro name nameMembership
                refine List.mem_append.mpr (.inr ?_)
                simp only [List.map_cons, List.map_nil,
                  Pattern.scopeVarsList]
                refine List.mem_append.mpr (.inl ?_)
                have both : name ∈ left.scopeVars ∧
                    name ∈ right.scopeVars := by
                  simpa [Pattern.scopeVars] using nameMembership
                exact both.2
            · cases membership
      | papp name arguments =>
          exact absurd rfl (notPatfun name arguments)
      | embed name =>
          exact absurd rfl (notEmbed name)
      | pvar name =>
          cases matcher with
          | lit n => cases mTyping
          | closure self closureEnv param body => cases mTyping
          | ctor ctorName values =>
              cases mTyping with
              | ctor found instanceTyping fieldsTyped =>
                  obtain ⟨former, arguments, resultEq⟩ :=
                    signatureWF.dataResult found instanceTyping
                  exact nomatch resultEq
          | something =>
              refine ⟨.cons valueScoped .nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨trivial, ?_⟩
                intro name nameMembership
                simp only [Pattern.scopeVars, List.mem_singleton]
                  at nameMembership
                subst nameMembership
                exact List.mem_append.mpr (.inl (by simp [Env.names]))
              · cases membership
          | tuple matchers =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro name nameMembership
                  simp [Pattern.exprVarsUnder] at nameMembership
                · intro name nameMembership
                  refine List.mem_append.mpr (.inr ?_)
                  simpa [Pattern.scopeVarsList] using nameMembership
              · cases membership
          | matcherV matcherEnv original current =>
              exact (dispatchKernel (Nat.lt_succ_self fuel) rfl).mono
                (fun dispatchOutput props =>
                  ⟨props.1 ▸ .nil, fun atoms membership =>
                    ⟨((props.2 atoms membership).1).mono_scope
                      (fun name h => by
                        rw [props.1]
                        exact List.mem_append.mpr (.inr h)),
                    fun name h => by
                      rw [props.1]
                      simpa using (props.2 atoms membership).2 name h⟩⟩)
      | wild =>
          cases matcher with
          | lit n => cases mTyping
          | closure self closureEnv param body => cases mTyping
          | ctor ctorName values =>
              cases mTyping with
              | ctor found instanceTyping fieldsTyped =>
                  obtain ⟨former, arguments, resultEq⟩ :=
                    signatureWF.dataResult found instanceTyping
                  exact nomatch resultEq
          | something =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨trivial, fun name nameMembership => by
                  simp [Pattern.scopeVars] at nameMembership⟩
              · cases membership
          | tuple matchers =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro name nameMembership
                  simp [Pattern.exprVarsUnder] at nameMembership
                · intro name nameMembership
                  simp [Pattern.scopeVars] at nameMembership
              · cases membership
          | matcherV matcherEnv original current =>
              exact (dispatchKernel (Nat.lt_succ_self fuel) rfl).mono
                (fun dispatchOutput props =>
                  ⟨props.1 ▸ .nil, fun atoms membership =>
                    ⟨((props.2 atoms membership).1).mono_scope
                      (fun name h => by
                        rw [props.1]
                        exact List.mem_append.mpr (.inr h)),
                    fun name h => by
                      rw [props.1]
                      simpa using (props.2 atoms membership).2 name h⟩⟩)
      | pval expression =>
          cases matcher with
          | lit n => cases mTyping
          | closure self closureEnv param body => cases mTyping
          | ctor ctorName values =>
              cases mTyping with
              | ctor found instanceTyping fieldsTyped =>
                  obtain ⟨former, arguments, resultEq⟩ :=
                    signatureWF.dataResult found instanceTyping
                  exact nomatch resultEq
          | something =>
              have expressionTyping := patternTyping.pval_inversion.2
              have expressionFv :
                  ∀ name ∈ expression.freeVars, name ∈ Env.names ρa := by
                intro name membership
                refine ambient name ?_
                simpa [Pattern.exprVarsUnder, List.removeAll_nil] using
                  membership
              simp only [matomFuel, RunResult.monad_bind_eq_bind]
              cases hEval : evalFuel SF fuel ρa expression with
              | ok expected =>
                  simp only [RunResult.bind_ok]
                  split
                  · refine ⟨.nil, ?_⟩
                    intro atoms membership
                    rcases List.mem_cons.mp membership with rfl | membership
                    · exact ⟨trivial, fun name nameMembership => by
                        simp [Pattern.scopeVars] at nameMembership⟩
                    · cases membership
                  · refine ⟨.nil, ?_⟩
                    intro atoms membership
                    cases membership
              | timeout =>
                  exact Safe.timeout
              | stuck =>
                  exact absurd hEval
                    ((evalKernel (Nat.lt_succ_self fuel) expressionTyping
                      expressionFv).1)
          | tuple matchers =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro name nameMembership
                  refine .inl (ambient name ?_)
                  simpa [Pattern.exprVarsUnder] using nameMembership
                · intro name nameMembership
                  simp [Pattern.scopeVars] at nameMembership
              · cases membership
          | matcherV matcherEnv original current =>
              exact (dispatchKernel (Nat.lt_succ_self fuel) rfl).mono
                (fun dispatchOutput props =>
                  ⟨props.1 ▸ .nil, fun atoms membership =>
                    ⟨((props.2 atoms membership).1).mono_scope
                      (fun name h => by
                        rw [props.1]
                        exact List.mem_append.mpr (.inr h)),
                    fun name h => by
                      rw [props.1]
                      simpa using (props.2 atoms membership).2 name h⟩⟩)
      | pctor ctorName patterns =>
          cases matcher with
          | lit n => cases mTyping
          | closure self closureEnv param body => cases mTyping
          | ctor ctorName' values =>
              cases mTyping with
              | ctor found instanceTyping fieldsTyped =>
                  obtain ⟨former, arguments, resultEq⟩ :=
                    signatureWF.dataResult found instanceTyping
                  exact nomatch resultEq
          | something =>
              exfalso
              have capEq : producerCapability = .any :=
                mTyping.something_capability_unique
              subst capEq
              have consumerEq := demand.any_producer_consumer
              obtain ⟨former, arguments, conEq⟩ :=
                patternTyping.terminal.pctor_capability signatureWF
              exact nomatch consumerEq.symm.trans conEq
          | tuple matchers =>
              exfalso
              cases mTyping with
              | matcherProduct fieldsTyped =>
                  obtain ⟨former, arguments, conEq⟩ :=
                    patternTyping.terminal.pctor_capability signatureWF
                  rw [conEq] at demand
                  exact nomatch demand
          | matcherV matcherEnv original current =>
              exact (dispatchKernel (Nat.lt_succ_self fuel) rfl).mono
                (fun dispatchOutput props =>
                  ⟨props.1 ▸ .nil, fun atoms membership =>
                    ⟨((props.2 atoms membership).1).mono_scope
                      (fun name h => by
                        rw [props.1]
                        exact List.mem_append.mpr (.inr h)),
                    fun name h => by
                      rw [props.1]
                      simpa using (props.2 atoms membership).2 name h⟩⟩)
      | ptuple patterns =>
          cases matcher with
          | lit n => cases mTyping
          | closure self closureEnv param body => cases mTyping
          | ctor ctorName values =>
              cases mTyping with
              | ctor found instanceTyping fieldsTyped =>
                  obtain ⟨former, arguments, resultEq⟩ :=
                    signatureWF.dataResult found instanceTyping
                  exact nomatch resultEq
          | something =>
              exfalso
              have capEq : producerCapability = .any :=
                mTyping.something_capability_unique
              subst capEq
              have consumerEq := demand.any_producer_consumer
              obtain ⟨components, prodEq⟩ :=
                patternTyping.terminal.ptuple_capability
              exact nomatch consumerEq.symm.trans prodEq
          | matcherV matcherEnv original current =>
              exact (dispatchKernel (Nat.lt_succ_self fuel) rfl).mono
                (fun dispatchOutput props =>
                  ⟨props.1 ▸ .nil, fun atoms membership =>
                    ⟨((props.2 atoms membership).1).mono_scope
                      (fun name h => by
                        rw [props.1]
                        exact List.mem_append.mpr (.inr h)),
                    fun name h => by
                      rw [props.1]
                      simpa using (props.2 atoms membership).2 name h⟩⟩)
          | tuple matchers =>
              cases patternTyping.terminal with
              | @tuple _ _ _ _ _ duals _ children =>
                  obtain ⟨values, valueEq, valuesTyped⟩ :=
                    ValueTy.product_inversion signatureWF valueTyping
                  subst valueEq
                  have matcherComponents :
                      matchers.length = duals.length := by
                    simpa using mTyping.matcherProduct_length
                  have valueComponents :
                      values.length = duals.length := by
                    simpa using ValueTys.length valuesTyped
                  have patternLength :
                      patterns.length = duals.length := by
                    simpa using children.length
                  have lengths :
                      patterns.length = matchers.length ∧
                        matchers.length = values.length :=
                    ⟨patternLength.trans matcherComponents.symm,
                      matcherComponents.trans valueComponents.symm⟩
                  simp only [matomFuel]
                  rw [if_pos lengths]
                  refine ⟨.nil, ?_⟩
                  intro atoms membership
                  rcases List.mem_cons.mp membership with
                    rfl | membership
                  · refine ⟨?_, ?_⟩
                    · refine AtomsScoped.of_captured
                        (CapturedScoped.of_exprVars ?_)
                        ?_ ?_
                      · intro name nameMembership
                        exact ambient name
                          (by simpa [Pattern.exprVarsUnder] using
                            nameMembership)
                      · cases matcherScoped with
                        | tuple matchersScoped =>
                            exact matchersScoped.mem
                      · cases valueScoped with
                        | tuple valuesScoped =>
                            exact valuesScoped.mem
                    · intro name nameMembership
                      refine List.mem_append.mpr (.inr ?_)
                      rw [zipAtoms_map_p lengths.1.symm
                        (lengths.1.trans lengths.2).symm]
                      simpa [Pattern.scopeVars] using nameMembership
                  · cases membership
  | primitive patternTyping primForm matcherAt valueTyping =>
      obtain ⟨consumerCapability, producerCapability, mTyping, demand⟩ :=
        matcherAt
      cases matcher with
      | lit n => cases mTyping
      | closure self closureEnv param body => cases mTyping
      | ctor ctorName values =>
          cases mTyping with
          | ctor found instanceTyping fieldsTyped =>
              obtain ⟨former, arguments, resultEq⟩ :=
                signatureWF.dataResult found instanceTyping
              exact nomatch resultEq
      | something =>
          cases pattern with
          | pvar name =>
              refine ⟨.cons valueScoped .nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨trivial, ?_⟩
                intro candidate nameMembership
                simp only [Pattern.scopeVars, List.mem_singleton]
                  at nameMembership
                subst nameMembership
                exact List.mem_append.mpr (.inl (by simp [Env.names]))
              · cases membership
          | wild =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨trivial, fun candidate nameMembership => by
                  simp [Pattern.scopeVars] at nameMembership⟩
              · cases membership
          | pval expression =>
              have expressionTyping := patternTyping.pval_inversion.2
              have expressionFv :
                  ∀ name ∈ expression.freeVars, name ∈ Env.names ρa := by
                intro name membership
                refine ambient name ?_
                simpa [Pattern.exprVarsUnder, List.removeAll_nil] using
                  membership
              simp only [matomFuel, RunResult.monad_bind_eq_bind]
              cases hEval : evalFuel SF fuel ρa expression with
              | ok expected =>
                  simp only [RunResult.bind_ok]
                  split
                  · refine ⟨.nil, ?_⟩
                    intro atoms membership
                    rcases List.mem_cons.mp membership with
                      rfl | membership
                    · exact ⟨trivial, fun candidate nameMembership => by
                        simp [Pattern.scopeVars] at nameMembership⟩
                    · cases membership
                  · refine ⟨.nil, ?_⟩
                    intro atoms membership
                    cases membership
              | timeout =>
                  exact Safe.timeout
              | stuck =>
                  exact absurd hEval
                    ((evalKernel (Nat.lt_succ_self fuel) expressionTyping
                      expressionFv).1)
          | pand left right => simp [Pattern.isPrimForm] at primForm
          | por left right => simp [Pattern.isPrimForm] at primForm
          | papp name arguments => simp [Pattern.isPrimForm] at primForm
          | embed name => simp [Pattern.isPrimForm] at primForm
          | pctor name patterns => simp [Pattern.isPrimForm] at primForm
          | ptuple patterns => simp [Pattern.isPrimForm] at primForm
      | tuple matchers =>
          cases pattern with
          | pvar name =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro candidate nameMembership
                  simp [Pattern.exprVarsUnder] at nameMembership
                · intro candidate nameMembership
                  refine List.mem_append.mpr (.inr ?_)
                  simpa [Pattern.scopeVarsList] using nameMembership
              · cases membership
          | wild =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro candidate nameMembership
                  simp [Pattern.exprVarsUnder] at nameMembership
                · intro candidate nameMembership
                  simp [Pattern.scopeVars] at nameMembership
              · cases membership
          | pval expression =>
              refine ⟨.nil, ?_⟩
              intro atoms membership
              rcases List.mem_cons.mp membership with rfl | membership
              · refine ⟨⟨?_, .something, valueScoped, trivial⟩, ?_⟩
                · intro candidate nameMembership
                  refine .inl (ambient candidate ?_)
                  simpa [Pattern.exprVarsUnder] using nameMembership
                · intro candidate nameMembership
                  simp [Pattern.scopeVars] at nameMembership
              · cases membership
          | pand left right => simp [Pattern.isPrimForm] at primForm
          | por left right => simp [Pattern.isPrimForm] at primForm
          | papp name arguments => simp [Pattern.isPrimForm] at primForm
          | embed name => simp [Pattern.isPrimForm] at primForm
          | pctor name patterns => simp [Pattern.isPrimForm] at primForm
          | ptuple patterns => simp [Pattern.isPrimForm] at primForm
      | matcherV matcherEnv original current =>
          have dispatchable :=
            Pattern.isMatcherDispatchable_of_isPrimForm primForm
          have run := dispatchKernel (Nat.lt_succ_self fuel)
            (matcherEnv := matcherEnv) (original := original)
            (current := current) rfl
          cases pattern with
          | pvar name =>
              exact run.mono (fun dispatchOutput props =>
                ⟨props.1 ▸ .nil, fun atoms membership =>
                  ⟨((props.2 atoms membership).1).mono_scope
                    (fun candidate h => by
                      rw [props.1]
                      exact List.mem_append.mpr (.inr h)),
                  fun candidate h => by
                    rw [props.1]
                    simpa using (props.2 atoms membership).2 candidate h⟩⟩)
          | wild =>
              exact run.mono (fun dispatchOutput props =>
                ⟨props.1 ▸ .nil, fun atoms membership =>
                  ⟨((props.2 atoms membership).1).mono_scope
                    (fun candidate h => by
                      rw [props.1]
                      exact List.mem_append.mpr (.inr h)),
                  fun candidate h => by
                    rw [props.1]
                    simpa using (props.2 atoms membership).2 candidate h⟩⟩)
          | pval expression =>
              exact run.mono (fun dispatchOutput props =>
                ⟨props.1 ▸ .nil, fun atoms membership =>
                  ⟨((props.2 atoms membership).1).mono_scope
                    (fun candidate h => by
                      rw [props.1]
                      exact List.mem_append.mpr (.inr h)),
                  fun candidate h => by
                    rw [props.1]
                    simpa using (props.2 atoms membership).2 candidate h⟩⟩)
          | pand left right => simp [Pattern.isPrimForm] at primForm
          | por left right => simp [Pattern.isPrimForm] at primForm
          | papp name arguments => simp [Pattern.isPrimForm] at primForm
          | embed name => simp [Pattern.isPrimForm] at primForm
          | pctor name patterns => simp [Pattern.isPrimForm] at primForm
          | ptuple patterns => simp [Pattern.isPrimForm] at primForm

end TypePM
