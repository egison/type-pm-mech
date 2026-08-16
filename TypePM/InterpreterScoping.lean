import TypePM.Interpreter
import TypePM.TermFreeVars

/-!
# Scoping invariants for the no-stuck theorem

The closedness half of the no-stuck theorem: values, environments, and
matching states carry enough name discipline that every variable lookup the
interpreter performs succeeds.  Everything here is purely syntactic; the
type-shaped refutations live in the safety module.

The matching-state invariant covers the `SF = []` fragment: stacks contain
only atoms (pattern-function nodes require a nonempty runtime signature to
arise, and the paper fragment fixes `SF = []`), and the stack threads each
atom's guaranteed binders (`Pattern.scopeVars`) into the scope of the atoms
below it — mirroring, names-only, what the typed threading does with binding
contexts.
-/

namespace TypePM

/-- The recursion names bound by a closure's self reference. -/
def selfNames : Option String → List String
  | none => []
  | some name => [name]

/-- Clause expressions scoped by the capturing environment's names. -/
def ScopedClauses (names : List String) (clauses : List Clause) : Prop :=
  ∀ name ∈ Clause.freeVarsList clauses, name ∈ names

mutual

/-- Every embedded expression inside a value sees only names its stored
environment (extended by the appropriate binders) can answer. -/
inductive ScopedValue : Value → Prop where
  | lit {n : Int} : ScopedValue (.lit n)
  | something : ScopedValue .something
  | ctor {name : String} {values : List Value} :
      ScopedValues values → ScopedValue (.ctor name values)
  | tuple {values : List Value} :
      ScopedValues values → ScopedValue (.tuple values)
  | closure {self : Option String} {ρ : Env} {param : String} {body : Expr} :
      ScopedEnv ρ →
      (∀ name ∈ body.freeVars,
        name ∈ param :: selfNames self ++ ρ.names) →
      ScopedValue (.closure self ρ param body)
  | matcherV {ρ : Env} {original current : List Clause} :
      ScopedEnv ρ →
      ScopedClauses ρ.names original →
      ScopedClauses ρ.names current →
      ScopedValue (.matcherV ρ original current)

/-- Pointwise scoped values. -/
inductive ScopedValues : List Value → Prop where
  | nil : ScopedValues []
  | cons {value : Value} {values : List Value} :
      ScopedValue value → ScopedValues values →
      ScopedValues (value :: values)

/-- Every value stored in an environment is scoped. -/
inductive ScopedEnv : Env → Prop where
  | nil : ScopedEnv []
  | cons {name : String} {value : Value} {ρ : Env} :
      ScopedValue value → ScopedEnv ρ →
      ScopedEnv ((name, value) :: ρ)

end

/-- Scoped values survive list membership. -/
theorem ScopedValues.mem :
    ∀ {values : List Value}, ScopedValues values →
      ∀ value ∈ values, ScopedValue value
  | [], _, _, membership => by cases membership
  | _ :: _, wellScoped, value, membership => by
      cases wellScoped with
      | cons head tail =>
          rcases List.mem_cons.mp membership with rfl | membership
          · exact head
          · exact ScopedValues.mem tail value membership

/-- Build pointwise scoped values from membership. -/
theorem ScopedValues.of_mem :
    ∀ {values : List Value},
      (∀ value ∈ values, ScopedValue value) → ScopedValues values
  | [], _ => .nil
  | value :: _, wellScoped =>
      .cons (wellScoped value List.mem_cons_self)
        (ScopedValues.of_mem fun candidate membership =>
          wellScoped candidate (List.mem_cons_of_mem _ membership))

/-- Environment scoping distributes over append. -/
theorem ScopedEnv.append :
    ∀ {left right : Env}, ScopedEnv left → ScopedEnv right →
      ScopedEnv (left ++ right)
  | [], _, _, rightScoped => rightScoped
  | _ :: _, _, leftScoped, rightScoped => by
      cases leftScoped with
      | cons value rest =>
          exact .cons value (ScopedEnv.append rest rightScoped)

/-- Environment lookup returns scoped values. -/
theorem ScopedEnv.lookup :
    ∀ {ρ : Env}, ScopedEnv ρ →
      ∀ {name : String} {value : Value},
        Env.find? ρ name = some value → ScopedValue value
  | [], _, name, value, found => by simp [Env.find?] at found
  | (entryName, entryValue) :: ρ, wellScoped, name, value, found => by
      cases wellScoped with
      | cons valueScoped rest =>
          by_cases hName : entryName = name
          · subst hName
            simp [Env.find?] at found
            subst found
            exact valueScoped
          · refine ScopedEnv.lookup rest (name := name) (value := value) ?_
            simpa [Env.find?, List.find?_cons, hName] using found

/-- One atom's components scoped under the given ambient names. -/
def ScopedAtom (scope : List String) (atom : Atom) : Prop :=
  (∀ name ∈ Pattern.exprVarsUnder [] atom.p, name ∈ scope) ∧
  ScopedValue atom.m ∧ ScopedValue atom.v

/-- Weakening for atoms. -/
theorem ScopedAtom.mono {scope scope' : List String} {atom : Atom}
    (wellScoped : ScopedAtom scope atom)
    (subset : ∀ name ∈ scope, name ∈ scope') :
    ScopedAtom scope' atom :=
  ⟨fun name membership => subset name (wellScoped.1 name membership),
    wellScoped.2.1, wellScoped.2.2⟩

/-- Atom-only matching stacks threading guaranteed binders downward. -/
inductive ScopedStack : List String → List Tree → Prop where
  | nil {scope : List String} : ScopedStack scope []
  | cons {scope : List String} {atom : Atom} {rest : List Tree} :
      ScopedAtom scope atom →
      ScopedStack (atom.p.scopeVars ++ scope) rest →
      ScopedStack scope (.atom atom :: rest)

/-- Weakening for stacks. -/
theorem ScopedStack.mono {scope scope' : List String} {stack : List Tree}
    (wellScoped : ScopedStack scope stack)
    (subset : ∀ name ∈ scope, name ∈ scope') :
    ScopedStack scope' stack := by
  induction wellScoped generalizing scope' with
  | nil => exact .nil
  | cons atomScoped rest induction =>
      refine .cons (atomScoped.mono subset) (induction ?_)
      intro name membership
      rw [List.mem_append] at membership ⊢
      rcases membership with membership | membership
      · exact .inl membership
      · exact .inr (subset name membership)

/-- Names guaranteed bound once every atom of the stack has reduced. -/
def stackScopeOut : List String → List Tree → List String
  | scope, [] => scope
  | scope, .atom atom :: rest =>
      stackScopeOut (atom.p.scopeVars ++ scope) rest
  | scope, .mnode _ _ _ _ :: rest => stackScopeOut scope rest

/-- A whole matching state is scoped. -/
def ScopedState (state : MState) : Prop :=
  ScopedEnv state.ρ ∧ ScopedEnv state.θ ∧
  ScopedStack (Env.names state.θ ++ Env.names state.ρ) state.S

/-! ## Names of produced match environments -/

mutual

/-- A successful data match binds exactly the data pattern's binders. -/
theorem pdMatch_names :
    ∀ {dp : DPat} {value : Value} {environment : Env},
      pdMatch dp value = some environment →
      environment.names = dp.bindVars
  | .var name, value, environment, h => by
      simp only [pdMatch, Option.some.injEq] at h
      subst h
      rfl
  | .wild, value, environment, h => by
      simp only [pdMatch, Option.some.injEq] at h
      subst h
      rfl
  | .ctor name pats, value, environment, h => by
      cases value with
      | ctor valueName values =>
          simp only [pdMatch] at h
          split at h
          · exact pdMatchList_names h
          · cases h
      | lit n => simp [pdMatch] at h
      | tuple values => simp [pdMatch] at h
      | closure self ρ param body => simp [pdMatch] at h
      | matcherV ρ original current => simp [pdMatch] at h
      | something => simp [pdMatch] at h
  | .tuple pats, value, environment, h => by
      cases value with
      | tuple values =>
          simp only [pdMatch] at h
          exact pdMatchList_names h
      | lit n => simp [pdMatch] at h
      | ctor valueName values => simp [pdMatch] at h
      | closure self ρ param body => simp [pdMatch] at h
      | matcherV ρ original current => simp [pdMatch] at h
      | something => simp [pdMatch] at h

/-- List form of `pdMatch_names`. -/
theorem pdMatchList_names :
    ∀ {pats : List DPat} {values : List Value} {environment : Env},
      pdMatchList pats values = some environment →
      environment.names = DPat.bindVarsList pats
  | [], values, environment, h => by
      cases values with
      | nil =>
          simp only [pdMatchList, Option.some.injEq] at h
          subst h
          rfl
      | cons value values => simp [pdMatchList] at h
  | pat :: pats, values, environment, h => by
      cases values with
      | nil => simp [pdMatchList] at h
      | cons value values =>
          simp only [pdMatchList, Option.bind_eq_bind, Option.bind_eq_some_iff]
            at h
          obtain ⟨headEnv, headMatch, h⟩ := h
          obtain ⟨tailEnv, tailMatch, h⟩ := h
          cases h
          simp [Env.names_append, pdMatch_names headMatch,
            pdMatchList_names tailMatch, DPat.bindVarsList]

end

/-! ## Bound-set reasoning for embedded expressions -/

/-- Three-way disjunction rotation used by bound-list permutations. -/
private theorem or_swap_tail {a b c : Prop} :
    a ∨ b ∨ c ↔ a ∨ c ∨ b := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  · intro h
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inr h)
    · exact .inr (.inl h)

mutual

/-- `exprVarsUnder` depends on the bound list only through membership. -/
theorem Pattern.exprVarsUnder_congr :
    ∀ {pattern : Pattern} {bs bs' : List String},
      (∀ name, name ∈ bs ↔ name ∈ bs') →
      Pattern.exprVarsUnder bs pattern = Pattern.exprVarsUnder bs' pattern
  | .pvar _, _, _, _ => rfl
  | .wild, _, _, _ => rfl
  | .embed _, _, _, _ => rfl
  | .pval expression, bs, bs', equivalent => by
      simp only [Pattern.exprVarsUnder, List.removeAll]
      refine List.filter_congr ?_
      intro name _
      simp [List.elem_eq_contains, List.contains_eq_mem, equivalent name]
  | .pctor _ patterns, bs, bs', equivalent =>
      Pattern.exprVarsUnderList_congr equivalent
  | .pand left right, bs, bs', equivalent => by
      simp only [Pattern.exprVarsUnder]
      rw [Pattern.exprVarsUnder_congr equivalent,
        Pattern.exprVarsUnder_congr (bs := bs ++ left.scopeVars)
          (bs' := bs' ++ left.scopeVars)
          (fun name => by simp [equivalent name])]
  | .por left right, bs, bs', equivalent => by
      simp only [Pattern.exprVarsUnder]
      rw [Pattern.exprVarsUnder_congr equivalent,
        Pattern.exprVarsUnder_congr (pattern := right) equivalent]
  | .papp _ patterns, bs, bs', equivalent =>
      Pattern.exprVarsUnderList_congr equivalent
  | .ptuple patterns, bs, bs', equivalent =>
      Pattern.exprVarsUnderList_congr equivalent

/-- List form of `Pattern.exprVarsUnder_congr`. -/
theorem Pattern.exprVarsUnderList_congr :
    ∀ {patterns : List Pattern} {bs bs' : List String},
      (∀ name, name ∈ bs ↔ name ∈ bs') →
      Pattern.exprVarsUnderList bs patterns =
        Pattern.exprVarsUnderList bs' patterns
  | [], _, _, _ => rfl
  | pattern :: patterns, bs, bs', equivalent => by
      simp only [Pattern.exprVarsUnderList]
      rw [Pattern.exprVarsUnder_congr equivalent,
        Pattern.exprVarsUnderList_congr
          (bs := bs ++ pattern.scopeVars)
          (bs' := bs' ++ pattern.scopeVars)
          (fun name => by simp [equivalent name])]

end

/-- Reassociate a bound-list extension to the outside. -/
theorem Pattern.exprVarsUnder_extend_comm
    {pattern : Pattern} {bs inner bound : List String} :
    Pattern.exprVarsUnder (bs ++ inner ++ bound) pattern =
      Pattern.exprVarsUnder (bs ++ bound ++ inner) pattern :=
  Pattern.exprVarsUnder_congr (fun name => by
    simp only [List.mem_append]
    exact Iff.trans or_assoc
      (Iff.trans (or_congr_right or_comm) or_assoc.symm))

/-- Reassociate a bound-list extension to the outside, list form. -/
theorem Pattern.exprVarsUnderList_extend_comm
    {patterns : List Pattern} {bs inner bound : List String} :
    Pattern.exprVarsUnderList (bs ++ inner ++ bound) patterns =
      Pattern.exprVarsUnderList (bs ++ bound ++ inner) patterns :=
  Pattern.exprVarsUnderList_congr (fun name => by
    simp only [List.mem_append]
    exact Iff.trans or_assoc
      (Iff.trans (or_congr_right or_comm) or_assoc.symm))

mutual

/-- Extending the bound list only moves names into the bound side. -/
theorem Pattern.mem_exprVarsUnder_extend :
    ∀ {pattern : Pattern} {name : String} {bs bound : List String},
      name ∈ Pattern.exprVarsUnder bs pattern →
      name ∈ Pattern.exprVarsUnder (bs ++ bound) pattern ∨ name ∈ bound
  | .pvar _, _, _, _, membership => by
      simp [Pattern.exprVarsUnder] at membership
  | .wild, _, _, _, membership => by
      simp [Pattern.exprVarsUnder] at membership
  | .embed _, _, _, _, membership => by
      simp [Pattern.exprVarsUnder] at membership
  | .pval expression, name, bs, bound, membership => by
      obtain ⟨present, fresh⟩ := List.mem_of_mem_removeAll membership
      by_cases hBound : name ∈ bound
      · exact .inr hBound
      · refine .inl (List.mem_removeAll_of_mem present ?_)
        intro contradiction
        rcases List.mem_append.mp contradiction with h | h
        · exact fresh h
        · exact hBound h
  | .pctor _ patterns, name, bs, bound, membership =>
      Pattern.mem_exprVarsUnderList_extend membership
  | .pand left right, name, bs, bound, membership => by
      simp only [Pattern.exprVarsUnder, List.mem_append] at membership ⊢
      rcases membership with membership | membership
      · rcases Pattern.mem_exprVarsUnder_extend (bound := bound)
          membership with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases Pattern.mem_exprVarsUnder_extend (bound := bound)
          membership with h | h
        · rw [Pattern.exprVarsUnder_extend_comm] at h
          exact .inl (.inr h)
        · exact .inr h
  | .por left right, name, bs, bound, membership => by
      simp only [Pattern.exprVarsUnder, List.mem_append] at membership ⊢
      rcases membership with membership | membership
      · rcases Pattern.mem_exprVarsUnder_extend (bound := bound)
          membership with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases Pattern.mem_exprVarsUnder_extend (bound := bound)
          membership with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | .papp _ patterns, name, bs, bound, membership =>
      Pattern.mem_exprVarsUnderList_extend membership
  | .ptuple patterns, name, bs, bound, membership =>
      Pattern.mem_exprVarsUnderList_extend membership

/-- List form of `Pattern.mem_exprVarsUnder_extend`. -/
theorem Pattern.mem_exprVarsUnderList_extend :
    ∀ {patterns : List Pattern} {name : String} {bs bound : List String},
      name ∈ Pattern.exprVarsUnderList bs patterns →
      name ∈ Pattern.exprVarsUnderList (bs ++ bound) patterns ∨
        name ∈ bound
  | [], _, _, _, membership => by
      simp [Pattern.exprVarsUnderList] at membership
  | pattern :: patterns, name, bs, bound, membership => by
      simp only [Pattern.exprVarsUnderList, List.mem_append]
        at membership ⊢
      rcases membership with membership | membership
      · rcases Pattern.mem_exprVarsUnder_extend (bound := bound)
          membership with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases Pattern.mem_exprVarsUnderList_extend (bound := bound)
          membership with h | h
        · rw [Pattern.exprVarsUnderList_extend_comm] at h
          exact .inl (.inr h)
        · exact .inr h

end

/-! ## Scope facts for successful primitive-pattern matches -/

/-- Guaranteed binders distribute over pattern-list append. -/
theorem Pattern.scopeVarsList_append (left right : List Pattern) :
    Pattern.scopeVarsList (left ++ right) =
      Pattern.scopeVarsList left ++ Pattern.scopeVarsList right := by
  induction left with
  | nil => rfl
  | cons pattern patterns induction =>
      simp [Pattern.scopeVarsList, induction]

mutual

/-- A successful primitive-pattern match binds exactly the clause header's
`#$x` binders. -/
theorem ppm_env_names {SF : RuntimeSigF} {ρ : Env} :
    ∀ (pp : PPat) {pattern : Pattern} {captures : List Pattern}
      {ppEnv : Env},
      PPM SF ρ pp pattern (some (captures, ppEnv)) →
      Env.names ppEnv = pp.bindVars
  | .hole, pattern, captures, ppEnv, h => by
      cases h
      rfl
  | .wild, pattern, captures, ppEnv, h => by
      cases h
      rfl
  | .pval name, pattern, captures, ppEnv, h => by
      cases h with
      | pval evaluation => rfl
  | .ctor name pps, pattern, captures, ppEnv, h => by
      cases h with
      | ctor lengthPP lengthResults all =>
          exact ppm_env_names_list pps lengthPP lengthResults all
  | .tuple pps, pattern, captures, ppEnv, h => by
      cases h with
      | tuple lengthPP lengthResults all =>
          exact ppm_env_names_list pps lengthPP lengthResults all

/-- List form of `ppm_env_names`. -/
theorem ppm_env_names_list {SF : RuntimeSigF} {ρ : Env} :
    ∀ (pps : List PPat) {patterns : List Pattern}
      {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF ρ entry.1.1 entry.1.2 (some entry.2)) →
      Env.names ((results.map Prod.snd).flatten) = PPat.bindVarsList pps
  | [], patterns, results, lengthPP, lengthResults, _ => by
      cases patterns with
      | nil =>
          cases results with
          | nil => rfl
          | cons result results => simp at lengthResults
      | cons pattern patterns => simp at lengthPP
  | pp :: pps, patterns, results, lengthPP, lengthResults, all => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnv⟩ := result
              have headPPM : PPM SF ρ pp pattern (some (captures, ppEnv)) :=
                all ((pp, pattern), (captures, ppEnv))
                  (by simp [List.zip_cons_cons])
              have tail := ppm_env_names_list pps
                (by simpa using lengthPP)
                (by simpa [List.zip_cons_cons] using lengthResults)
                (fun entry membership => all entry
                  (by simp [List.zip_cons_cons]
                      exact .inr membership))
              simp [PPat.bindVarsList, ppm_env_names pp headPPM, tail]

end

mutual

/-- The captured subpatterns preserve the pattern's guaranteed binders. -/
theorem ppm_scopeVars_sub {SF : RuntimeSigF} {ρ : Env} :
    ∀ (pp : PPat) {pattern : Pattern} {captures : List Pattern}
      {ppEnv : Env},
      PPM SF ρ pp pattern (some (captures, ppEnv)) →
      ∀ name ∈ pattern.scopeVars, name ∈ Pattern.scopeVarsList captures
  | .hole, pattern, captures, ppEnv, h => by
      cases h
      intro name membership
      simp [Pattern.scopeVarsList, membership]
  | .wild, pattern, captures, ppEnv, h => by
      cases h
      intro name membership
      simp [Pattern.scopeVars] at membership
  | .pval binder, pattern, captures, ppEnv, h => by
      cases h with
      | pval evaluation =>
          intro name membership
          simp [Pattern.scopeVars] at membership
  | .ctor name pps, pattern, captures, ppEnv, h => by
      cases h with
      | ctor lengthPP lengthResults all =>
          exact ppm_scopeVars_sub_list pps lengthPP lengthResults all
  | .tuple pps, pattern, captures, ppEnv, h => by
      cases h with
      | tuple lengthPP lengthResults all =>
          exact ppm_scopeVars_sub_list pps lengthPP lengthResults all

/-- List form of `ppm_scopeVars_sub`. -/
theorem ppm_scopeVars_sub_list {SF : RuntimeSigF} {ρ : Env} :
    ∀ (pps : List PPat) {patterns : List Pattern}
      {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF ρ entry.1.1 entry.1.2 (some entry.2)) →
      ∀ name ∈ Pattern.scopeVarsList patterns,
        name ∈ Pattern.scopeVarsList ((results.map Prod.fst).flatten)
  | [], patterns, results, lengthPP, lengthResults, _ => by
      cases patterns with
      | nil =>
          intro name membership
          simp [Pattern.scopeVarsList] at membership
      | cons pattern patterns => simp at lengthPP
  | pp :: pps, patterns, results, lengthPP, lengthResults, all => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnv⟩ := result
              have headPPM : PPM SF ρ pp pattern (some (captures, ppEnv)) :=
                all ((pp, pattern), (captures, ppEnv))
                  (by simp [List.zip_cons_cons])
              have tail := ppm_scopeVars_sub_list pps
                (by simpa using lengthPP)
                (by simpa [List.zip_cons_cons] using lengthResults)
                (fun entry membership => all entry
                  (by simp [List.zip_cons_cons]
                      exact .inr membership))
              intro name membership
              simp only [Pattern.scopeVarsList, List.mem_append]
                at membership
              simp only [List.map_cons, List.flatten_cons,
                Pattern.scopeVarsList_append, List.mem_append]
              rcases membership with membership | membership
              · exact .inl (ppm_scopeVars_sub pp headPPM name membership)
              · exact .inr (tail name membership)

end

/-! ## Scoping of captured continuation patterns -/

/-- Left-to-right scoping of hole-captured subpatterns: each capture's
embedded expressions see the ambient scope or the binders of earlier
captures. -/
def CapturedScoped (scope : List String) :
    List String → List Pattern → Prop
  | _, [] => True
  | bound, capture :: captures =>
      (∀ name ∈ Pattern.exprVarsUnder [] capture,
        name ∈ scope ∨ name ∈ bound) ∧
      CapturedScoped scope (bound ++ capture.scopeVars) captures

/-- Bound-side weakening for `CapturedScoped`. -/
theorem CapturedScoped.mono_bound {scope : List String} :
    ∀ {captures : List Pattern} {bound bound' : List String},
      CapturedScoped scope bound captures →
      (∀ name ∈ bound, name ∈ bound') →
      CapturedScoped scope bound' captures
  | [], _, _, _, _ => trivial
  | capture :: captures, bound, bound', wellScoped, subset => by
      obtain ⟨head, rest⟩ := wellScoped
      refine ⟨?_, ?_⟩
      · intro name membership
        rcases head name membership with h | h
        · exact .inl h
        · exact .inr (subset name h)
      · refine CapturedScoped.mono_bound rest ?_
        intro name membership
        rcases List.mem_append.mp membership with h | h
        · exact List.mem_append.mpr (.inl (subset name h))
        · exact List.mem_append.mpr (.inr h)

/-- `CapturedScoped` composes along capture-list append. -/
theorem CapturedScoped.append {scope : List String} :
    ∀ {front rear : List Pattern} {bound : List String},
      CapturedScoped scope bound front →
      CapturedScoped scope (bound ++ Pattern.scopeVarsList front) rear →
      CapturedScoped scope bound (front ++ rear)
  | [], rear, bound, _, rearScoped => by
      refine CapturedScoped.mono_bound (bound := bound ++ Pattern.scopeVarsList []) rearScoped ?_
      intro name membership
      simpa [Pattern.scopeVarsList] using membership
  | capture :: front, rear, bound, frontScoped, rearScoped => by
      obtain ⟨head, rest⟩ := frontScoped
      refine ⟨head, ?_⟩
      refine CapturedScoped.append rest
        (CapturedScoped.mono_bound rearScoped ?_)
      intro name membership
      simp only [Pattern.scopeVarsList, List.mem_append] at membership ⊢
      rcases membership with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

mutual

/-- A successful primitive-pattern match hands its captures to the
continuation with the ambient scoping intact. -/
theorem ppm_captured_scoped {SF : RuntimeSigF} {ρ : Env}
    {scope : List String} :
    ∀ (pp : PPat) {pattern : Pattern} {captures : List Pattern}
      {ppEnv : Env} {bound : List String},
      PPM SF ρ pp pattern (some (captures, ppEnv)) →
      (∀ name ∈ Pattern.exprVarsUnder bound pattern, name ∈ scope) →
      CapturedScoped scope bound captures
  | .hole, pattern, captures, ppEnv, bound, h, ambient => by
      cases h
      refine ⟨?_, trivial⟩
      intro name membership
      rcases Pattern.mem_exprVarsUnder_extend (bs := [])
          (bound := bound) membership with h | h
      · exact .inl (ambient name (by simpa using h))
      · exact .inr h
  | .wild, pattern, captures, ppEnv, bound, h, _ => by
      cases h
      trivial
  | .pval binder, pattern, captures, ppEnv, bound, h, _ => by
      cases h with
      | pval evaluation => trivial
  | .ctor name pps, pattern, captures, ppEnv, bound, h, ambient => by
      cases h with
      | ctor lengthPP lengthResults all =>
          exact ppm_captured_scoped_list pps lengthPP lengthResults all
            (by simpa [Pattern.exprVarsUnder] using ambient)
  | .tuple pps, pattern, captures, ppEnv, bound, h, ambient => by
      cases h with
      | tuple lengthPP lengthResults all =>
          exact ppm_captured_scoped_list pps lengthPP lengthResults all
            (by simpa [Pattern.exprVarsUnder] using ambient)

/-- List form of `ppm_captured_scoped`. -/
theorem ppm_captured_scoped_list {SF : RuntimeSigF} {ρ : Env}
    {scope : List String} :
    ∀ (pps : List PPat) {patterns : List Pattern}
      {results : List (List Pattern × Env)} {bound : List String},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF ρ entry.1.1 entry.1.2 (some entry.2)) →
      (∀ name ∈ Pattern.exprVarsUnderList bound patterns,
        name ∈ scope) →
      CapturedScoped scope bound ((results.map Prod.fst).flatten)
  | [], patterns, results, bound, lengthPP, lengthResults, _, _ => by
      cases patterns with
      | nil =>
          cases results with
          | nil => trivial
          | cons result results => simp at lengthResults
      | cons pattern patterns => simp at lengthPP
  | pp :: pps, patterns, results, bound, lengthPP, lengthResults, all,
      ambient => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnv⟩ := result
              have headPPM : PPM SF ρ pp pattern (some (captures, ppEnv)) :=
                all ((pp, pattern), (captures, ppEnv))
                  (by simp [List.zip_cons_cons])
              have headAmbient :
                  ∀ name ∈ Pattern.exprVarsUnder bound pattern,
                    name ∈ scope := by
                intro name membership
                refine ambient name ?_
                simp [Pattern.exprVarsUnderList, membership]
              have headScoped :=
                ppm_captured_scoped pp headPPM headAmbient
              have tailScoped :=
                ppm_captured_scoped_list pps
                  (by simpa using lengthPP)
                  (by simpa [List.zip_cons_cons] using lengthResults)
                  (fun entry membership => all entry
                    (by simp [List.zip_cons_cons]
                        exact .inr membership))
                  (fun name membership => ambient name
                    (by simp [Pattern.exprVarsUnderList]
                        exact .inr membership))
              simp only [List.map_cons, List.flatten_cons]
              refine CapturedScoped.append headScoped ?_
              refine CapturedScoped.mono_bound tailScoped ?_
              intro name membership
              rcases List.mem_append.mp membership with h | h
              · exact List.mem_append.mpr (.inl h)
              · exact List.mem_append.mpr
                  (.inr (ppm_scopeVars_sub pp headPPM name h))

end

/-! ## Scoping of decoded values -/

/-- Decoded list elements of a scoped value are scoped. -/
theorem listOfV_scoped :
    ∀ {value : Value} {elements : List Value},
      ScopedValue value → listOfV value = some elements →
      ∀ element ∈ elements, ScopedValue element := by
  let P : Value → Prop := fun value =>
    ∀ {elements : List Value},
      ScopedValue value → listOfV value = some elements →
      ∀ element ∈ elements, ScopedValue element
  intro value
  refine Value.rec
    (motive_1 := P)
    (motive_2 := fun fields => ∀ value ∈ fields, P value)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ value
  · intro literal elements _ decode
    simp [listOfV] at decode
  · intro name fields fieldsIH elements wellScoped decode
    by_cases nilName : name = "nil"
    · subst name
      cases fields with
      | nil =>
          simp only [listOfV, Option.some.injEq] at decode
          subst decode
          intro element membership
          cases membership
      | cons head tail => simp [listOfV] at decode
    · by_cases consName : name = "cons"
      · subst name
        cases fields with
        | nil => simp [listOfV] at decode
        | cons head tail =>
            cases tail with
            | nil => simp [listOfV] at decode
            | cons rest tailTail =>
                cases tailTail with
                | cons third more => simp [listOfV] at decode
                | nil =>
                    simp only [listOfV] at decode
                    cases restDecode : listOfV rest with
                    | none => rw [restDecode] at decode; cases decode
                    | some restElements =>
                        rw [restDecode] at decode
                        simp only [Option.map_some,
                          Option.some.injEq] at decode
                        subst decode
                        cases wellScoped with
                        | ctor fieldsScoped =>
                            cases fieldsScoped with
                            | cons headScoped restScoped =>
                                cases restScoped with
                                | cons tailScoped nilScoped =>
                                    intro element membership
                                    rcases List.mem_cons.mp membership
                                      with rfl | membership
                                    · exact headScoped
                                    · exact fieldsIH rest (by simp)
                                        tailScoped restDecode element
                                        membership
      · simp [listOfV, nilName, consName] at decode
  · intro fields _ elements _ decode
    simp [listOfV] at decode
  · intro self environment parameter body _ elements _ decode
    simp [listOfV] at decode
  · intro environment originalClauses currentClauses _ elements _ decode
    simp [listOfV] at decode
  · intro elements _ decode
    simp [listOfV] at decode
  · intro value membership
    contradiction
  · intro head tail headIH tailIH value membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact headIH
    · exact tailIH value membership
  · trivial
  · intros
    trivial
  · intros
    trivial

/-- Decoded tuple components of a scoped value are scoped. -/
theorem decodeTuple_scoped {k : Nat} {value : Value}
    {components : List Value}
    (wellScoped : ScopedValue value)
    (decode : decodeTuple k value = some components) :
    ∀ component ∈ components, ScopedValue component := by
  simp only [decodeTuple] at decode
  split at decode
  · cases decode
    intro component membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact wellScoped
    · cases membership
  · split at decode
    · rename_i values
      split at decode
      · cases decode
        cases wellScoped with
        | tuple valuesScoped =>
            exact valuesScoped.mem
      · cases decode
    · cases decode

/-- Encoding scoped values gives a scoped list value. -/
theorem mkListV_scoped :
    ∀ {values : List Value},
      (∀ value ∈ values, ScopedValue value) →
      ScopedValue (mkListV values)
  | [], _ => .ctor .nil
  | value :: _, wellScoped =>
      .ctor (.cons (wellScoped value List.mem_cons_self)
        (.cons (mkListV_scoped fun candidate membership =>
          wellScoped candidate (List.mem_cons_of_mem _ membership)) .nil))

end TypePM
