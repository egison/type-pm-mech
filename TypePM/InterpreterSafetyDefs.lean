import TypePM.InterpreterScoping

/-!
# Shared statement forms for the no-stuck theorem

`Safe P r` is the per-result safety contract of one fuel-bounded run: a
stuck run is forbidden, a timeout claims nothing, and a successful run
satisfies `P`.  `AtomsScoped` is the left-to-right scoping contract of one
continuation branch produced by an atom reduction, and `stackBinders`
collects the binders a stack still promises to bind.
-/

namespace TypePM

/-- Contract of one fuel-bounded result: never stuck, and `P` on success. -/
def Safe (P : α → Prop) : RunResult α → Prop
  | .ok value => P value
  | .timeout => True
  | .stuck => False

@[simp] theorem Safe.ok_iff {P : α → Prop} {value : α} :
    Safe P (.ok value) ↔ P value := Iff.rfl

@[simp] theorem Safe.timeout {P : α → Prop} :
    Safe P (.timeout : RunResult α) := trivial

theorem Safe.not_stuck {P : α → Prop} {run : RunResult α}
    (safe : Safe P run) : run ≠ .stuck := by
  intro h
  subst h
  exact safe

/-- Contract weakening. -/
theorem Safe.mono {P Q : α → Prop} {run : RunResult α}
    (safe : Safe P run) (weaken : ∀ value, P value → Q value) :
    Safe Q run := by
  cases run with
  | ok value => exact weaken value safe
  | timeout => trivial
  | stuck => exact safe

/-- Left-to-right scoping of one continuation branch: each atom's embedded
expressions see the ambient scope or the binders of the atoms before it,
and each atom's matcher and target values are scoped. -/
def AtomsScoped (scope : List String) :
    List String → List Atom → Prop
  | _, [] => True
  | bound, atom :: atoms =>
      (∀ name ∈ Pattern.exprVarsUnder [] atom.p,
        name ∈ scope ∨ name ∈ bound) ∧
      ScopedValue atom.m ∧ ScopedValue atom.v ∧
      AtomsScoped scope (bound ++ atom.p.scopeVars) atoms

/-- Binders a matching stack still promises to bind, front to back. -/
def stackBinders : List Tree → List String
  | [] => []
  | .atom atom :: rest => atom.p.scopeVars ++ stackBinders rest
  | .mnode trees _ _ piE :: rest =>
      nodeBinders trees piE ++ stackBinders rest

/-- Ambient weakening for branch scoping. -/
theorem AtomsScoped.mono_scope {scope scope' : List String} :
    ∀ {atoms : List Atom} {bound : List String},
      AtomsScoped scope bound atoms →
      (∀ name ∈ scope, name ∈ scope') →
      AtomsScoped scope' bound atoms
  | [], _, _, _ => trivial
  | _ :: atoms, bound, wellScoped, subset => by
      obtain ⟨ambient, matcherScoped, valueScoped, rest⟩ := wellScoped
      refine ⟨?_, matcherScoped, valueScoped,
        AtomsScoped.mono_scope rest subset⟩
      intro name membership
      rcases ambient name membership with h | h
      · exact .inl (subset name h)
      · exact .inr h

/-- Bound-side weakening for branch scoping. -/
theorem AtomsScoped.mono_bound {scope : List String} :
    ∀ {atoms : List Atom} {bound bound' : List String},
      AtomsScoped scope bound atoms →
      (∀ name ∈ bound, name ∈ bound') →
      AtomsScoped scope bound' atoms
  | [], _, _, _, _ => trivial
  | _ :: atoms, bound, bound', wellScoped, subset => by
      obtain ⟨ambient, matcherScoped, valueScoped, rest⟩ := wellScoped
      refine ⟨?_, matcherScoped, valueScoped, ?_⟩
      · intro name membership
        rcases ambient name membership with h | h
        · exact .inl h
        · exact .inr (subset name h)
      · refine AtomsScoped.mono_bound rest ?_
        intro name membership
        rcases List.mem_append.mp membership with h | h
        · exact List.mem_append.mpr (.inl (subset name h))
        · exact List.mem_append.mpr (.inr h)

/-- Branch scoping from capture scoping plus pointwise value scoping. -/
theorem AtomsScoped.of_captured {scope : List String} :
    ∀ {patterns : List Pattern} {matchers values : List Value}
      {bound : List String},
      CapturedScoped scope bound patterns →
      (∀ matcher ∈ matchers, ScopedValue matcher) →
      (∀ value ∈ values, ScopedValue value) →
      AtomsScoped scope bound
        ((patterns.zip (matchers.zip values)).map fun entry =>
          ⟨entry.1, entry.2.1, entry.2.2⟩)
  | [], _, _, _, _, _, _ => trivial
  | pattern :: patterns, matchers, values, bound, capturedScoped,
      matchersScoped, valuesScoped => by
      cases matchers with
      | nil => trivial
      | cons matcher matchers =>
          cases values with
          | nil => trivial
          | cons value values =>
              obtain ⟨head, rest⟩ := capturedScoped
              refine ⟨head,
                matchersScoped matcher List.mem_cons_self,
                valuesScoped value List.mem_cons_self, ?_⟩
              exact AtomsScoped.of_captured rest
                (fun candidate membership => matchersScoped candidate
                  (List.mem_cons_of_mem _ membership))
                (fun candidate membership => valuesScoped candidate
                  (List.mem_cons_of_mem _ membership))

/-- Convert one scoped branch into a scoped stack over a tail. -/
theorem ScopedStack.of_atomsScoped {scope : List String} :
    ∀ {atoms : List Atom} {rest : List Tree} {bound : List String},
      AtomsScoped scope bound atoms →
      (∀ name ∈ bound, name ∈ scope) →
      ScopedStack (Pattern.scopeVarsList (atoms.map Atom.p) ++ scope) rest →
      ScopedStack scope (atoms.map .atom ++ rest)
  | [], rest, bound, _, _, restScoped => by
      refine restScoped.mono ?_
      intro name membership
      simpa [Pattern.scopeVarsList] using membership
  | atom :: atoms, rest, bound, wellScoped, boundSub, restScoped => by
      obtain ⟨ambient, matcherScoped, valueScoped, tail⟩ := wellScoped
      refine .cons ⟨?_, matcherScoped, valueScoped⟩ ?_
      · intro name membership
        rcases ambient name membership with h | h
        · exact h
        · exact boundSub name h
      · refine ScopedStack.of_atomsScoped
          (AtomsScoped.mono_scope tail
            (fun name membership => List.mem_append.mpr (.inr membership)))
          ?_ ?_
        · intro name membership
          rcases List.mem_append.mp membership with h | h
          · exact List.mem_append.mpr (.inr (boundSub name h))
          · exact List.mem_append.mpr (.inl h)
        · refine restScoped.mono ?_
          intro name membership
          rcases List.mem_append.mp membership with h | h
          · rw [List.map_cons] at h
            simp only [Pattern.scopeVarsList] at h
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append.mpr
                (.inr (List.mem_append.mpr (.inl h)))
            · exact List.mem_append.mpr (.inl h)
          · exact List.mem_append.mpr
              (.inr (List.mem_append.mpr (.inr h)))

end TypePM
