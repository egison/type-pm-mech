import TypePM.InterpreterMatomSafe
import TypePM.RuntimeAgreementBridge

/-!
# State- and search-level safety of the fuel-indexed interpreter

`stepSafe` lifts atom-level safety to one matching-state step: a typed,
scoped, nonterminal state cannot stick, every successor is scoped, and the
names promised by the state (its substitution together with the stack's
remaining binders) survive into every successor.  `searchSafe` iterates
this to the terminal substitutions, which are typed at the goal binding
context (through adequacy and the relational preservation), pristine,
scoped, and cover every promised name.

Both statements are for the `SF = []` fragment; successors' typedness is
recovered relationally through adequacy rather than re-proved
functionally.
-/

namespace TypePM

/-- The names a state promises to have bound by each successful branch's
end: its current substitution and the stack's remaining binders. -/
def statePromise (state : MState) : List String :=
  Env.names state.θ ++ stackBinders state.S

/-- With an empty runtime signature a typed pattern-function atom is
impossible: its static lookup would have to resolve in the runtime table. -/
private theorem papp_refuted
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {name : String} {arguments : List Pattern}
    {matcher value : Value}
    (agrees : RuntimeSigAgrees signature context ([] : RuntimeSigF))
    (typing : AtomTy signature context parameters input
      ⟨.papp name arguments, matcher, value⟩ output) : False := by
  cases typing with
  | mk patternTyping matcherUsable valueTyping =>
      cases patternTyping.terminal with
      | app sourceLookup children instanceTyping =>
          obtain ⟨definition, _, runtimeFound, _⟩ :=
            agrees.sourceLookup sourceLookup
          simp at runtimeFound
  | primitive patternTyping primForm matcherAt valueTyping =>
      simp [Pattern.isPrimForm] at primForm

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

/--
One typed, scoped, nonterminal matching-state step is safe: no stuck
configuration, every successor state is scoped, and the state's promise
survives into every successor's promise.
-/
theorem stepSafe
    {signature : FrozenSig} (_signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    {context : Context} {goal : MonoCtx} {state : MState} {fuel : Nat}
    (typing : MStateTy signature context state goal)
    (stateScoped : ScopedState state)
    (nonterminal : state.S ≠ [])
    (matomKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {input output : MonoCtx} {pattern : Pattern}
          {matcher value : Value},
          AtomTy signature context [] input ⟨pattern, matcher, value⟩
            output →
          EnvTyped signature (input.toContext ++ context)
            (state.θ ++ state.ρ) →
          (∀ name ∈ Pattern.exprVarsUnder [] pattern,
            name ∈ Env.names (state.θ ++ state.ρ)) →
          ScopedValue matcher → ScopedValue value →
          ValuePristine matcher → ValuePristine value →
          Safe (MatomOutputScoped (Env.names (state.θ ++ state.ρ)) pattern)
            (matomFuel [] fuel' (state.θ ++ state.ρ) pattern matcher
              value)) :
    Safe (fun states => ∀ next ∈ states,
        ScopedState next ∧
        ∀ name ∈ statePromise state, name ∈ statePromise next)
      (stepFuel [] fuel state) := by
  cases fuel with
  | zero => exact Safe.timeout
  | succ fuel =>
  obtain ⟨stack, ρ, θ⟩ := state
  cases stack with
  | nil => exact absurd rfl nonterminal
  | cons tree rest =>
      obtain ⟨ρScoped, θScoped, stackScoped⟩ := stateScoped
      cases tree with
      | mnode innerTrees innerEnv innerSubst piE => cases stackScoped
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
        exact (papp_refuted (agrees context) atomTyping).elim
      · have notPatfun : ∀ name arguments,
            pattern ≠ .papp name arguments := by
          intro name arguments contradiction
          exact hPatfun ⟨name, arguments, contradiction⟩
        rw [stepFuel_atom_eq notPatfun, RunResult.monad_bind_eq_bind]
        have combinedTyped :
            EnvTyped signature (input.toContext ++ context) (θ ++ ρ) :=
          θTyped.envTyped_append ρTyped
        have run := matomKernel (Nat.lt_succ_self fuel) atomTyping
          combinedTyped
          (fun name membership => by
            simpa [Env.names_append] using ambient name membership)
          matcherScoped valueScoped matcherPristine valuePristine
        cases hAtom : matomFuel [] fuel (θ ++ ρ) pattern matcher value with
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

/--
Exhaustive search from a typed, scoped state is safe: no stuck run, and
every returned substitution is typed at the goal, pristine, scoped, and
covers the state's promise.
-/
theorem searchSafe
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF)) :
    ∀ {fuel : Nat} {context : Context} {goal : MonoCtx} {state : MState},
      MStateTy signature context state goal →
      ScopedState state →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {state' : MState},
          MStateTy signature context state' goal →
          ScopedState state' → state'.S ≠ [] →
          Safe (fun states => ∀ next ∈ states,
              ScopedState next ∧
              ∀ name ∈ statePromise state', name ∈ statePromise next)
            (stepFuel [] fuel' state')) →
      Safe (fun substitutions => ∀ θ' ∈ substitutions,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise state, name ∈ Env.names θ')
        (searchFuel [] fuel state)
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
          stateScoped (by simp)
        cases hStep : stepFuel [] fuel ⟨tree :: rest, ρ, θ⟩ with
        | ok states =>
            rw [hStep] at stepRun
            simp only [RunResult.bind_ok]
            have stepRelational :=
              stepFuel_ok (SF := ([] : RuntimeSigF)) hStep
            have successorsTyped :=
              (StepRuntimeSigAgrees.of_global agrees stepRelational
                ).preservation signatureWF (agrees context) typing
            have listRun := searchListSafe signatureWF agrees
              (fuel := fuel) (goal := goal)
              (fun next membership =>
                ⟨successorsTyped next membership,
                  (stepRun next membership).1⟩)
              (fun {fuel'} lt {state'} t s n =>
                stepKernel (Nat.lt_succ_of_lt lt) t s n)
            cases hList : searchListFuel [] fuel states with
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
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF)) :
    ∀ {fuel : Nat} {context : Context} {goal : MonoCtx}
      {pending : List MState},
      (∀ next ∈ pending,
        MStateTy signature context next goal ∧ ScopedState next) →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {state' : MState},
          MStateTy signature context state' goal →
          ScopedState state' → state'.S ≠ [] →
          Safe (fun states => ∀ next ∈ states,
              ScopedState next ∧
              ∀ name ∈ statePromise state', name ∈ statePromise next)
            (stepFuel [] fuel' state')) →
      Safe (fun results => ∀ pair ∈ pending.zip results, ∀ θ' ∈ pair.2,
          MatchSubstTyped signature goal θ' ∧ EnvPristine θ' ∧
          ScopedEnv θ' ∧
          ∀ name ∈ statePromise pair.1, name ∈ Env.names θ')
        (searchListFuel [] fuel pending)
  | 0, _, _, _, _, _ => Safe.timeout
  | _ + 1, _, _, [], _, _ => by
      intro pair membership
      cases membership
  | fuel + 1, context, goal, next :: pendingRest, facts, stepKernel => by
      simp only [searchListFuel, RunResult.monad_bind_eq_bind]
      obtain ⟨nextTyped, nextScoped⟩ := facts next List.mem_cons_self
      have headRun := searchSafe signatureWF agrees (fuel := fuel)
        nextTyped nextScoped
        (fun {fuel'} lt {state'} t s n =>
          stepKernel (Nat.lt_succ_of_lt lt) t s n)
      cases hHead : searchFuel [] fuel next with
      | ok headResults =>
          rw [hHead] at headRun
          simp only [RunResult.bind_ok]
          have tailRun := searchListSafe signatureWF agrees (fuel := fuel)
            (fun candidate membership =>
              facts candidate (List.mem_cons_of_mem _ membership))
            (fun {fuel'} lt {state'} t s n =>
              stepKernel (Nat.lt_succ_of_lt lt) t s n)
          cases hTail : searchListFuel [] fuel pendingRest with
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
