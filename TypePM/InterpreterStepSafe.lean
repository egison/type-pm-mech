import TypePM.InterpreterMatomSafe
import TypePM.RuntimeAgreementBridge

/-!
# State- and search-level safety of the fuel-indexed interpreter

`stepSafe` lifts atom-level safety to one matching-state step.  It covers
ordinary atoms as well as isolated pattern-function nodes.  Successors'
typedness is recovered relationally through adequacy rather than re-proved
functionally.
-/

namespace TypePM

/-- The next state is not an isolated embedded-parameter atom.  Such atoms
are consumed by their enclosing pattern-function node, rather than by the
ordinary atom reducer. -/
def HeadNotEmbed (state : MState) : Prop :=
  ∀ name matcher value rest,
    state.S ≠ .atom ⟨.embed name, matcher, value⟩ :: rest

/-- The names a state promises to have bound by each successful branch's
end: its current substitution and the stack's remaining binders. -/
def statePromise (state : MState) : List String :=
  Env.names state.θ ++ stackBinders state.S

/-- Resolving an aligned suffix through a name-unique actual-pattern table
recovers the suffix's patterns in order. -/
private theorem resolvePiPatterns_aligned :
    ∀ {piE : PiEnv} {parameters : List String}
      {arguments : List Pattern},
      (piE.map Prod.fst).Nodup →
      parameters.length = arguments.length →
      (∀ entry ∈ parameters.zip arguments, entry ∈ piE) →
      resolvePiPatterns piE parameters = arguments
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, length, _ => by simp at length
  | _, _ :: _, [], _, length, _ => by simp at length
  | piE, parameter :: parameters, argument :: arguments, nodup, length,
      contained => by
      have found : List.find? (fun entry => entry.1 == parameter) piE =
          some (parameter, argument) :=
        PiEnv.find?_eq_some_of_mem nodup
          (contained (parameter, argument) (by simp))
      simp only [List.length_cons, Nat.succ.injEq] at length
      simp only [resolvePiPatterns, List.filterMap_cons, found]
      change argument :: resolvePiPatterns piE parameters =
        argument :: arguments
      rw [resolvePiPatterns_aligned nodup length]
      intro entry membership
      exact contained entry (by simp; exact .inr membership)

private theorem resolvePiPatterns_zip
    {parameters : List String} {arguments : List Pattern}
    (nodup : parameters.Nodup)
    (length : parameters.length = arguments.length) :
    resolvePiPatterns (parameters.zip arguments) parameters = arguments := by
  apply resolvePiPatterns_aligned
  · simpa [List.map_fst_zip (Nat.le_of_eq length)] using nodup
  · exact length
  · intro entry membership
    exact membership

/-- A freshly entered pattern-function node promises exactly the binders of
its actual arguments. -/
private theorem nodeBinders_patfun
    {runtime : PatFunRuntimeSig} {arguments : List Pattern}
    (linear : runtime.body.linearEmbeds = some runtime.params)
    (parametersNodup : runtime.params.Nodup)
    (length : runtime.params.length = arguments.length) :
    nodeBinders [.atom ⟨runtime.body, matcher, value⟩]
        (runtime.params.zip arguments) =
      Pattern.scopeVarsList arguments := by
  simp only [nodeBinders, stackEmbedOccs, treeEmbedOccs, List.append_nil,
    Pattern.embedVars_eq_of_linearEmbeds runtime.body linear,
    resolvePiScopeVars, resolvePiPatterns_zip parametersNodup length]

private theorem nodePatterns_patfun
    {runtime : PatFunRuntimeSig} {arguments : List Pattern}
    (linear : runtime.body.linearEmbeds = some runtime.params)
    (parametersNodup : runtime.params.Nodup)
    (length : runtime.params.length = arguments.length) :
    nodePatterns [.atom ⟨runtime.body, matcher, value⟩]
        (runtime.params.zip arguments) = arguments := by
  simp only [nodePatterns, stackEmbedOccs, treeEmbedOccs, List.append_nil,
    Pattern.embedVars_eq_of_linearEmbeds runtime.body linear]
  exact resolvePiPatterns_zip parametersNodup length

/-- Binders promised by a pushed branch cover the branch's own scope
variables and the tail's binders. -/
private theorem stackBinders_atoms_append
    {atoms : List Atom} {rest : List Tree} {name : String} :
    (name ∈ Pattern.scopeVarsList (atoms.map Atom.p) ∨
      name ∈ stackBinders rest) →
    name ∈ stackBinders (atoms.map Tree.atom ++ rest) := by
  induction atoms with
  | nil =>
      intro h
      rcases h with h | h
      · exact absurd h (by simp [Pattern.scopeVarsList])
      · simpa using h
  | cons atom atoms induction =>
      intro h
      simp only [List.map_cons, List.cons_append, stackBinders]
      rcases h with h | h
      · rw [List.map_cons] at h
        simp only [Pattern.scopeVarsList] at h
        rcases List.mem_append.mp h with h | h
        · exact List.mem_append.mpr (.inl h)
        · exact List.mem_append.mpr (.inr (induction (.inl h)))
      · exact List.mem_append.mpr (.inr (induction (.inr h)))

/-- One matching step preserves the state's ordinary environment in every
successor. -/
private theorem Step.environment_eq {SF : RuntimeSigF} {state : MState}
    {states : List MState} (reduction : Step SF state states) :
    ∀ next ∈ states, next.ρ = state.ρ := by
  cases reduction with
  | reduce atomReduction =>
      intro next membership
      obtain ⟨atoms, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | patfunEnter found length =>
      intro next membership
      simp only [List.mem_singleton] at membership
      subst next
      rfl
  | mnodeStep guard inner =>
      intro next membership
      obtain ⟨innerState, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | mnodeVarpat found =>
      intro next membership
      simp only [List.mem_singleton] at membership
      subst next
      rfl
  | mnodeDone =>
      intro next membership
      simp only [List.mem_singleton] at membership
      subst next
      rfl

/--
One typed, scoped, nonterminal matching-state step is safe: no stuck
configuration, every successor state is scoped, and the state's promise
survives into every successor's promise.
-/
theorem stepSafe
    {signature : FrozenSig} (_signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    (agrees : ∀ context, RuntimeSigAgrees signature context
      SF)
    (runtimeScoped : RuntimeSigScoped SF)
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    {state : MState} {fuel : Nat}
    (typing : MStateTyAt signature context parameters state goal)
    (stateScoped : ScopedState state)
    (nonterminal : state.S ≠ [])
    (headNotEmbed : HeadNotEmbed state)
    (matomKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {input output : MonoCtx} {pattern : Pattern}
          {matcher value : Value},
          AtomTy signature context parameters input ⟨pattern, matcher, value⟩
            output →
          (∀ name arguments, pattern ≠ .papp name arguments) →
          (∀ name, pattern ≠ .embed name) →
          EnvTyped signature (input.toContext ++ context)
            (state.θ ++ state.ρ) →
          (∀ name ∈ Pattern.exprVarsUnder [] pattern,
            name ∈ Env.names (state.θ ++ state.ρ)) →
          ScopedValue matcher → ScopedValue value →
          ValuePristine matcher → ValuePristine value →
          Safe (MatomOutputScoped (Env.names (state.θ ++ state.ρ)) pattern)
            (matomFuel SF fuel' (state.θ ++ state.ρ) pattern matcher
              value))
    (stepKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {parameters' : PatternCtx} {goal' : MonoCtx} {state' : MState},
          MStateTyAt signature context parameters' state' goal' →
          ScopedState state' → state'.S ≠ [] → HeadNotEmbed state' →
          Safe (fun states => ∀ next ∈ states,
              ScopedState next ∧
              ∀ name ∈ statePromise state', name ∈ statePromise next)
            (stepFuel SF fuel' state')) :
    Safe (fun states => ∀ next ∈ states,
        ScopedState next ∧
        ∀ name ∈ statePromise state, name ∈ statePromise next)
      (stepFuel SF fuel state) := by
  cases fuel with
  | zero => exact Safe.timeout
  | succ fuel =>
  obtain ⟨stack, ρ, θ⟩ := state
  cases stack with
  | nil => exact absurd rfl nonterminal
  | cons tree rest =>
      obtain ⟨ρScoped, θScoped, stackScoped⟩ := stateScoped
      cases tree with
      | mnode innerTrees innerEnv innerSubst piE =>
          cases stackScoped with
          | mnode innerEnvScoped innerSubstScoped innerTreesScoped
              actualsScoped restScoped =>
          obtain ⟨⟨stackPristine, ρPristine, θPristine⟩, noEmbed,
            ρTyped, input, θTyped, stackTyped⟩ := typing
          cases stackPristine with
          | cons nodePristine restPristine =>
          cases nodePristine with
          | mnode innerPristine capturedPristine innerSubstPristine =>
          cases stackTyped with
          | cons nodeTyped restTyped =>
          obtain ⟨innerParameters, innerBindings, innerGoal, rem, duals,
              suffix, namesNodup, innerNoEmbed, argumentsNoEmbed,
              occurrences, actualTyping, remInParameters,
              innerEnvTyped, innerSubstTyped, innerStackTyped⟩ :=
            nodeTyped.mnode_inversion
          have innerTyping : MStateTyAt signature context innerParameters
              ⟨innerTrees, innerEnv, innerSubst⟩ innerGoal :=
            ⟨⟨innerPristine, capturedPristine, innerSubstPristine⟩,
              innerNoEmbed, innerEnvTyped, innerBindings, innerSubstTyped,
              innerStackTyped⟩
          cases innerTrees with
          | nil =>
              simp only [stepFuel]
              intro next membership
              simp only [List.mem_singleton] at membership
              subst next
              constructor
              · refine ⟨ρScoped, θScoped, ?_⟩
                simpa only [nodeBinders_nil, List.nil_append] using restScoped
              · intro candidate membership
                simpa only [statePromise, stackBinders, nodeBinders_nil,
                  List.nil_append] using membership
          | cons innerTree innerRest =>
              by_cases embedded : ∃ name matcher value,
                  innerTree = .atom ⟨.embed name, matcher, value⟩
              · obtain ⟨name, innerMatcher, innerValue, rfl⟩ := embedded
                have leadingOccurrences :
                    name :: stackEmbedOccs innerRest = rem.map Prod.fst := by
                  simpa [stackEmbedOccs, treeEmbedOccs,
                    Pattern.embedVars] using occurrences
                cases remShape : rem with
                | nil =>
                    rw [remShape] at leadingOccurrences
                    cases leadingOccurrences
                | cons entry remRest =>
                    obtain ⟨entryName, entryPattern⟩ := entry
                    rw [remShape] at leadingOccurrences
                    have entryNameEq : entryName = name := by
                      simpa using (List.cons.inj leadingOccurrences.symm).1
                    subst entryName
                    have entryMember : (name, entryPattern) ∈ piE := by
                      obtain ⟨index, dropEq⟩ := suffix
                      rw [dropEq] at remShape
                      exact List.mem_of_mem_drop
                        (remShape ▸ List.mem_cons_self)
                    have found :
                        List.find? (fun entry => entry.1 == name) piE =
                          some (name, entryPattern) :=
                      PiEnv.find?_eq_some_of_mem namesNodup entryMember
                    have patternSplit :
                        nodePatterns
                            (.atom ⟨.embed name, innerMatcher, innerValue⟩ ::
                              innerRest) piE =
                          entryPattern :: nodePatterns innerRest piE := by
                      simp [nodePatterns, resolvePiPatterns, stackEmbedOccs,
                        treeEmbedOccs, Pattern.embedVars, found]
                    have binderSplit :
                        nodeBinders
                            (.atom ⟨.embed name, innerMatcher, innerValue⟩ ::
                              innerRest) piE =
                          entryPattern.scopeVars ++
                            nodeBinders innerRest piE := by
                      change Pattern.scopeVarsList
                          (nodePatterns
                            (.atom ⟨.embed name, innerMatcher, innerValue⟩ ::
                              innerRest) piE) = _
                      rw [patternSplit]
                      rfl
                    rw [patternSplit] at actualsScoped
                    obtain ⟨actualScoped, remainingActualsScoped⟩ :=
                      actualsScoped
                    cases innerTreesScoped with
                    | cons embeddedScoped residualInnerScoped =>
                    simp only [stepFuel, found]
                    intro next membership
                    simp only [List.mem_singleton] at membership
                    subst next
                    constructor
                    · refine ⟨ρScoped, θScoped, .cons ?_ ?_⟩
                      · refine ⟨?_, embeddedScoped.2.1,
                          embeddedScoped.2.2⟩
                        intro candidate membership
                        rcases actualScoped candidate membership with h | h
                        · exact h
                        · cases h
                      · refine .mnode innerEnvScoped innerSubstScoped ?_ ?_ ?_
                        · simpa [Pattern.scopeVars] using
                            residualInnerScoped
                        · simpa only [List.nil_append] using
                            remainingActualsScoped.bound_to_scope
                        · refine restScoped.mono ?_
                          intro candidate membership
                          have reordered : candidate ∈
                              (entryPattern.scopeVars ++
                                  nodeBinders innerRest piE) ++
                                (Env.names θ ++ Env.names ρ) := by
                            simpa only [binderSplit] using membership
                          simp only [List.mem_append] at reordered ⊢
                          rcases reordered with h | h
                          · rcases h with h | h
                            · exact .inr (.inl h)
                            · exact .inl h
                          · exact .inr (.inr h)
                    · intro candidate membership
                      simpa [statePromise, stackBinders, binderSplit] using
                        membership
              · have notEmbed : ∀ name matcher value,
                    innerTree ≠ .atom ⟨.embed name, matcher, value⟩ := by
                  intro name matcher value equality
                  exact embedded ⟨name, matcher, value, equality⟩
                have innerRun := stepKernel (Nat.lt_succ_self fuel)
                    innerTyping
                    ⟨innerEnvScoped, innerSubstScoped, innerTreesScoped⟩
                    (by simp)
                    (by
                      intro name matcher value rest equality
                      exact notEmbed name matcher value
                        (List.cons.inj equality).1)
                rw [stepFuel_mnode_eq notEmbed,
                  RunResult.monad_bind_eq_bind]
                cases hInner : stepFuel SF fuel
                    ⟨innerTree :: innerRest, innerEnv, innerSubst⟩ with
                | timeout => exact Safe.timeout
                | stuck =>
                    rw [hInner] at innerRun
                    exact innerRun.elim
                | ok states =>
                    rw [hInner] at innerRun
                    simp only [RunResult.bind_ok]
                    have relational := stepFuel_ok hInner
                    have linear : RuntimePatternLinear SF :=
                      (agrees context).runtimePatternLinear
                    intro next membership
                    obtain ⟨innerNext, innerMembership, rfl⟩ :=
                      List.mem_map.mp membership
                    obtain ⟨nextStack, nextEnv, nextSubst⟩ := innerNext
                    have environmentEquality :=
                      relational.environment_eq
                        ⟨nextStack, nextEnv, nextSubst⟩ innerMembership
                    simp only at environmentEquality
                    subst nextEnv
                    obtain ⟨nextScoped, _promise⟩ :=
                      innerRun ⟨nextStack, innerEnv, nextSubst⟩
                        innerMembership
                    obtain ⟨nextEnvScoped, nextSubstScoped,
                      nextStackScoped⟩ := nextScoped
                    have occurrencesEquality :
                        stackEmbedOccs nextStack =
                          stackEmbedOccs (innerTree :: innerRest) :=
                      Step.embedOccs linear relational innerNoEmbed
                        ⟨nextStack, innerEnv, nextSubst⟩ innerMembership
                    have patternsEquality :
                        nodePatterns nextStack piE =
                          nodePatterns (innerTree :: innerRest) piE := by
                      simp [nodePatterns, occurrencesEquality]
                    have bindersEquality :
                        nodeBinders nextStack piE =
                          nodeBinders (innerTree :: innerRest) piE := by
                      unfold nodeBinders resolvePiScopeVars
                      rw [occurrencesEquality]
                    constructor
                    · refine ⟨ρScoped, θScoped,
                        .mnode innerEnvScoped nextSubstScoped
                          nextStackScoped ?_ ?_⟩
                      · simpa [patternsEquality] using actualsScoped
                      · simpa [bindersEquality] using restScoped
                    · intro candidate membership
                      simpa [statePromise, stackBinders, bindersEquality]
                        using membership
      | atom atom =>
      obtain ⟨pattern, matcher, value⟩ := atom
      cases stackScoped with
      | cons atomScoped restScoped =>
      obtain ⟨ambient, matcherScoped, valueScoped⟩ := atomScoped
      obtain ⟨⟨stackPristine, ρPristine, θPristine⟩, _noEmbed, ρTyped,
        input, θTyped, stackTyped⟩ := typing
      cases stackPristine with
      | cons headPristine _restPristine =>
      cases headPristine with
      | atom atomPristine =>
      obtain ⟨matcherPristine, valuePristine⟩ := atomPristine
      cases stackTyped with
      | cons treeTyped restTyped =>
      cases treeTyped with
      | atom atomTyping =>
      by_cases hPatfun : ∃ name arguments,
          pattern = .papp name arguments
      · obtain ⟨name, arguments, rfl⟩ := hPatfun
        cases atomTyping with
        | mk patternTyping matcherUsable valueTyping =>
            cases patternTyping.terminal with
            | @app _ _ _ _ _ scheme _ duals _ result sourceLookup
                children instanceTyping =>
                obtain ⟨definition, _nameEquality, runtimeFound,
                    definitionTyping⟩ :=
                  (agrees context).sourceLookup sourceLookup
                have runtimeArity :
                    definition.runtime.params.length = arguments.length := by
                  exact (definitionTyping.actual_arity instanceTyping).trans
                    children.length.symm
                obtain ⟨bodyLinear, parametersNodup⟩ :=
                  (agrees context).runtimePatternLinear runtimeFound
                have bodyClosed := runtimeScoped.lookup runtimeFound
                have nodeBinderEquality :
                    nodeBinders
                        [.atom ⟨definition.runtime.body, matcher, value⟩]
                        (definition.runtime.params.zip arguments) =
                      Pattern.scopeVarsList arguments :=
                  nodeBinders_patfun bodyLinear parametersNodup runtimeArity
                have argumentsScoped : ScopedPatterns
                    (Env.names θ ++ Env.names ρ) [] arguments := by
                  apply ScopedPatterns.of_ambient
                  intro candidate membership
                  exact ambient candidate (by
                    simpa [Pattern.exprVarsUnder] using membership)
                have nodePatternEquality :
                    nodePatterns
                        [.atom ⟨definition.runtime.body, matcher, value⟩]
                        (definition.runtime.params.zip arguments) =
                      arguments :=
                  nodePatterns_patfun bodyLinear parametersNodup runtimeArity
                have piScoped : ScopedPatterns
                    (Env.names θ ++ Env.names ρ) []
                    (nodePatterns
                      [.atom ⟨definition.runtime.body, matcher, value⟩]
                      (definition.runtime.params.zip arguments)) := by
                  simpa [nodePatternEquality] using argumentsScoped
                have innerScoped : ScopedStack (Env.names ([] : MatchSubst) ++
                    Env.names ρ)
                    [.atom ⟨definition.runtime.body, matcher, value⟩] := by
                  refine .cons ⟨?_, matcherScoped, valueScoped⟩ .nil
                  intro candidate membership
                  rw [bodyClosed] at membership
                  cases membership
                have tailScoped : ScopedStack
                    (nodeBinders
                        [.atom ⟨definition.runtime.body, matcher, value⟩]
                        (definition.runtime.params.zip arguments) ++
                      (Env.names θ ++ Env.names ρ)) rest := by
                  simpa [nodeBinderEquality, Pattern.scopeVars] using
                    restScoped
                simp only [stepFuel, runtimeFound, runtimeArity, if_true]
                intro next membership
                simp only [List.mem_singleton] at membership
                subst next
                constructor
                · exact ⟨ρScoped, θScoped,
                    .mnode ρScoped .nil innerScoped piScoped tailScoped⟩
                · intro candidate membership
                  simpa [statePromise, stackBinders, nodeBinderEquality,
                    Pattern.scopeVars] using membership
        | primitive patternTyping primitive matcherAt valueTyping =>
            simp [Pattern.isPrimForm] at primitive
      · have notPatfun : ∀ name arguments,
            pattern ≠ .papp name arguments := by
          intro name arguments contradiction
          exact hPatfun ⟨name, arguments, contradiction⟩
        have notEmbed : ∀ name, pattern ≠ .embed name := by
          intro name equality
          subst pattern
          exact headNotEmbed name matcher value rest rfl
        rw [stepFuel_atom_eq notPatfun, RunResult.monad_bind_eq_bind]
        have combinedTyped :
            EnvTyped signature (input.toContext ++ context) (θ ++ ρ) :=
          θTyped.envTyped_append ρTyped
        have run := matomKernel (Nat.lt_succ_self fuel) atomTyping
          notPatfun notEmbed combinedTyped
          (fun name membership => by
            simpa [Env.names_append] using ambient name membership)
          matcherScoped valueScoped matcherPristine valuePristine
        cases hAtom : matomFuel SF fuel (θ ++ ρ) pattern matcher value with
        | ok result =>
            rw [hAtom] at run
            simp only [RunResult.bind_ok]
            obtain ⟨continuations, new⟩ := result
            obtain ⟨newScoped, branches⟩ := run
            intro next membership
            obtain ⟨atoms, atomsMembership, rfl⟩ :=
              List.mem_map.mp membership
            obtain ⟨atomsScoped, binderClaim⟩ :=
              branches atoms atomsMembership
            constructor
            · refine ⟨ρScoped, ScopedEnv.append newScoped θScoped, ?_⟩
              refine ScopedStack.of_atomsScoped
                (atomsScoped.mono_scope ?_)
                (fun name membership => by cases membership) ?_
              · intro name membership
                rcases List.mem_append.mp membership with h | h
                · exact List.mem_append.mpr (.inl (by
                    rw [Env.names_append]
                    exact List.mem_append.mpr (.inl h)))
                · rw [Env.names_append] at h
                  rcases List.mem_append.mp h with h | h
                  · exact List.mem_append.mpr (.inl (by
                      rw [Env.names_append]
                      exact List.mem_append.mpr (.inr h)))
                  · exact List.mem_append.mpr (.inr h)
              · refine restScoped.mono ?_
                intro name membership
                rcases List.mem_append.mp membership with h | h
                · rcases List.mem_append.mp (binderClaim name h) with h | h
                  · exact List.mem_append.mpr (.inr (List.mem_append.mpr
                      (.inl (by
                        rw [Env.names_append]
                        exact List.mem_append.mpr (.inl h)))))
                  · exact List.mem_append.mpr (.inl h)
                · rcases List.mem_append.mp h with h | h
                  · exact List.mem_append.mpr (.inr (List.mem_append.mpr
                      (.inl (by
                        rw [Env.names_append]
                        exact List.mem_append.mpr (.inr h)))))
                  · exact List.mem_append.mpr (.inr (List.mem_append.mpr
                      (.inr h)))
            · intro name membership
              simp only [statePromise, stackBinders] at membership ⊢
              rcases List.mem_append.mp membership with h | h
              · exact List.mem_append.mpr (.inl (by
                  rw [Env.names_append]
                  exact List.mem_append.mpr (.inr h)))
              · rcases List.mem_append.mp h with h | h
                · rcases List.mem_append.mp (binderClaim name h) with h | h
                  · exact List.mem_append.mpr (.inl (by
                      rw [Env.names_append]
                      exact List.mem_append.mpr (.inl h)))
                  · exact List.mem_append.mpr
                      (.inr (stackBinders_atoms_append (.inl h)))
                · exact List.mem_append.mpr
                    (.inr (stackBinders_atoms_append (.inr h)))
        | timeout =>
            exact Safe.timeout
        | stuck =>
            rw [hAtom] at run
            exact run.elim

mutual

/-- A top-level typed state cannot expose an embedded parameter directly;
there is no top-level pattern-parameter context in which to type it. -/
private theorem MStateTy.headNotEmbed
    {signature : FrozenSig} {context : Context} {state : MState}
    {goal : MonoCtx} (typing : MStateTy signature context state goal) :
    HeadNotEmbed state := by
  intro name matcher value rest equality
  change MStateTyAt signature context [] state goal at typing
  unfold MStateTyAt at typing
  rw [equality] at typing
  obtain ⟨_, _, _, input, _, stackTyped⟩ := typing
  cases stackTyped with
  | cons treeTyped _ =>
      cases treeTyped with
      | atom atomTyping =>
          cases atomTyping with
          | mk patternTyping _ _ =>
              have found := patternTyping.embed_inversion.1
              simp [PatternCtx.find?] at found
          | primitive patternTyping _ _ _ =>
              have found := patternTyping.embed_inversion.1
              simp [PatternCtx.find?] at found

/--
Exhaustive search from a typed, scoped state is safe: no stuck run, and
every returned substitution is typed at the goal, pristine, scoped, and
covers the state's promise.
-/
theorem searchSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      SF) :
    ∀ {fuel : Nat} {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {state' : MState},
          MStateTy signature context state' goal →
          ScopedState state' → state'.S ≠ [] → HeadNotEmbed state' →
          Safe (fun states => ∀ next ∈ states,
              ScopedState next ∧
              ∀ name ∈ statePromise state', name ∈ statePromise next)
            (stepFuel SF fuel' state')) →
      Safe (fun substitutions => ∀ θ' ∈ substitutions,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise state, name ∈ Env.names θ')
        (searchFuel SF fuel state)
  | 0, _, _, _, _, _, _ => Safe.timeout
  | fuel + 1, context, goal, ⟨stack, ρ, θ⟩, typing, stateScoped,
      stepKernel => by
    cases stack with
    | nil =>
        intro θ' membership
        rcases List.mem_singleton.mp membership with rfl
        refine ⟨typing.terminal_substitution, typing.1.2.2,
          stateScoped.2.1, ?_⟩
        intro name membership
        simpa [statePromise, stackBinders] using membership
    | cons tree rest =>
        simp only [searchFuel, RunResult.monad_bind_eq_bind]
        have stepRun := stepKernel (Nat.lt_succ_self fuel) typing
          stateScoped (by simp) typing.headNotEmbed
        cases hStep : stepFuel SF fuel ⟨tree :: rest, ρ, θ⟩ with
        | ok states =>
            rw [hStep] at stepRun
            simp only [RunResult.bind_ok]
            have stepRelational :=
              stepFuel_ok (SF := SF) hStep
            have successorsTyped :=
              (StepRuntimeSigAgrees.of_global agrees stepRelational
                ).preservation signatureWF (agrees context) typing
            have listRun := searchListSafe signatureWF agrees
              (fuel := fuel) (goal := goal)
              (fun next membership =>
                ⟨successorsTyped next membership,
                  (stepRun next membership).1⟩)
              (fun {fuel'} lt {state'} t s n h =>
                stepKernel (Nat.lt_succ_of_lt lt) t s n h)
            cases hList : searchListFuel SF fuel states with
            | ok results =>
                rw [hList] at listRun
                simp only [RunResult.bind_ok]
                intro θ' membership
                obtain ⟨branch, branchMembership, θMembership⟩ :=
                  List.mem_flatten.mp membership
                obtain ⟨lengths, _⟩ := searchListFuel_ok hList
                obtain ⟨pairState, pairMembership⟩ :=
                  List.exists_fst_mem_zip_of_snd_mem lengths
                    branchMembership
                obtain ⟨typed, pristine, scopedEnv, promise⟩ :=
                  listRun _ pairMembership θ' θMembership
                refine ⟨typed, pristine, scopedEnv, ?_⟩
                intro name nameMembership
                exact promise name
                  ((stepRun pairState
                      (List.fst_mem_of_mem_zip pairMembership)).2
                    name nameMembership)
            | timeout => exact Safe.timeout
            | stuck =>
                rw [hList] at listRun
                exact listRun.elim
        | timeout => exact Safe.timeout
        | stuck =>
            rw [hStep] at stepRun
            exact stepRun.elim

/--
Pointwise search over pending states is safe, pairing each state with its
own substitutions and promise.
-/
theorem searchListSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      SF) :
    ∀ {fuel : Nat} {context : Context} {goal : MonoCtx}
      {pending : List MState},
      (∀ next ∈ pending,
        MStateTy signature context next goal ∧ ScopedState next) →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {state' : MState},
          MStateTy signature context state' goal →
          ScopedState state' → state'.S ≠ [] → HeadNotEmbed state' →
          Safe (fun states => ∀ next ∈ states,
              ScopedState next ∧
              ∀ name ∈ statePromise state', name ∈ statePromise next)
            (stepFuel SF fuel' state')) →
      Safe (fun results => ∀ pair ∈ pending.zip results, ∀ θ' ∈ pair.2,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise pair.1, name ∈ Env.names θ')
        (searchListFuel SF fuel pending)
  | 0, _, _, _, _, _ => Safe.timeout
  | _ + 1, _, _, [], _, _ => by
      intro pair membership
      cases membership
  | fuel + 1, context, goal, next :: pendingRest, facts, stepKernel => by
      simp only [searchListFuel, RunResult.monad_bind_eq_bind]
      obtain ⟨nextTyped, nextScoped⟩ := facts next List.mem_cons_self
      have headRun := searchSafe signatureWF agrees (fuel := fuel)
        nextTyped nextScoped
        (fun {fuel'} lt {state'} t s n h =>
          stepKernel (Nat.lt_succ_of_lt lt) t s n h)
      cases hHead : searchFuel SF fuel next with
      | ok headResults =>
          rw [hHead] at headRun
          simp only [RunResult.bind_ok]
          have tailRun := searchListSafe signatureWF agrees (fuel := fuel)
            (fun candidate membership =>
              facts candidate (List.mem_cons_of_mem _ membership))
            (fun {fuel'} lt {state'} t s n h =>
              stepKernel (Nat.lt_succ_of_lt lt) t s n h)
          cases hTail : searchListFuel SF fuel pendingRest with
          | ok tailResults =>
              rw [hTail] at tailRun
              simp only [RunResult.bind_ok]
              intro pair membership
              rw [List.zip_cons_cons] at membership
              rcases List.mem_cons.mp membership with rfl | membership
              · exact headRun
              · exact tailRun pair membership
          | timeout => exact Safe.timeout
          | stuck =>
              rw [hTail] at tailRun
              exact tailRun.elim
      | timeout => exact Safe.timeout
      | stuck =>
          rw [hHead] at headRun
          exact headRun.elim

end

end TypePM
