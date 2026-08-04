import TypePM.Semantics

/-!
# Branch reachability for matching search

`Search` explores every successor returned by `Step`.  `Reaches` records one
chosen branch.  The bridge below is independent of typing and is later used
to iterate one-step preservation and type every successful substitution.
-/

namespace TypePM

/-- Reflexive transitive closure of `Step`, choosing one successor per step. -/
inductive Reaches (SF : RuntimeSigF) : MState → MState → Prop where
  | refl {state} :
      Reaches SF state state
  | step {state successors next destination} :
      Step SF state successors →
      next ∈ successors →
      Reaches SF next destination →
      Reaches SF state destination

/-- Iterate any invariant preserved by each chosen matching successor. -/
theorem Reaches.preserve
    {SF : RuntimeSigF} {Invariant : MState → Prop}
    (oneStep :
      ∀ {state successors},
        Step SF state successors →
        Invariant state →
        ∀ next ∈ successors, Invariant next)
    {start finish : MState}
    (reachable : Reaches SF start finish)
    (initial : Invariant start) :
    Invariant finish := by
  induction reachable with
  | refl => exact initial
  | step reduction member _ ih =>
      exact ih (oneStep reduction initial _ member)

/-! ## List helpers -/

theorem exists_mem_zip_right {α β : Type} :
    ∀ {left : List α} {right : List β},
      left.length = right.length →
      ∀ {item : β}, item ∈ right →
        ∃ partner, (partner, item) ∈ left.zip right
  | [], [], _, _, member => nomatch member
  | [], _ :: _, equality, _, _ => nomatch equality
  | _ :: _, [], _, _, member => nomatch member
  | head :: left, itemHead :: right, equality, item, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨head, by simp⟩
      · obtain ⟨partner, paired⟩ :=
          exists_mem_zip_right (by simpa using equality) member
        exact ⟨partner, by simp [paired]⟩

theorem mem_left_of_zip {α β : Type} :
    ∀ {left : List α} {right : List β} {a : α} {b : β},
      (a, b) ∈ left.zip right → a ∈ left
  | [], _, _, _, member => nomatch member
  | _ :: _, [], _, _, member => nomatch member
  | head :: left, _ :: right, a, b, member => by
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with equality | member
      · exact List.mem_cons.mpr (.inl (Prod.mk.inj equality).1)
      · exact List.mem_cons.mpr (.inr (mem_left_of_zip member))

/-! ## Exhaustive search exposes branch reachability -/

/-- Every substitution returned by `Search` belongs to a terminal branch. -/
theorem Search.member_reaches
    {SF : RuntimeSigF} {state : MState}
    {substitutions : List MatchSubst}
    (search : Search SF state substitutions) :
    ∀ substitution ∈ substitutions,
      ∃ environment,
        Reaches SF state ⟨[], environment, substitution⟩ := by
  refine Search.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun state substitutions _ =>
      ∀ substitution ∈ substitutions,
        ∃ environment,
          Reaches SF state ⟨[], environment, substitution⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?done ?step search
  case done =>
      intro _environment _initialSubstitution substitution member
      simp only [List.mem_singleton] at member
      subst substitution
      exact ⟨_, .refl⟩
  case step =>
      intro state successors resultLists reduction lengths all
        _reductionIH ih substitution member
      obtain ⟨resultList, resultListMem, substitutionMem⟩ :=
        List.mem_flatten.mp member
      obtain ⟨successor, paired⟩ :=
        exists_mem_zip_right lengths resultListMem
      obtain ⟨environment, reachable⟩ :=
        ih (successor, resultList) paired substitution substitutionMem
      exact
        ⟨environment,
          .step reduction (mem_left_of_zip paired) reachable⟩
  all_goals intros; trivial

end TypePM
