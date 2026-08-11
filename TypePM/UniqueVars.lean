import TypePM.Syntax

/-!
# Duplicate-free variable lists

Generalization uses a deterministic list normalization that retains the last
occurrence of each variable.  It is independent of either scheme
representation.
-/

namespace TypePM

/-- Keep one occurrence of every variable, retaining the last occurrence. -/
def uniqueVars {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | item :: items =>
      if item ∈ items then
        uniqueVars items
      else
        item :: uniqueVars items

@[simp] theorem mem_uniqueVars {α : Type} [DecidableEq α]
    {item : α} {items : List α} :
    item ∈ uniqueVars items ↔ item ∈ items := by
  induction items with
  | nil =>
      simp [uniqueVars]
  | cons head tail ih =>
      simp only [uniqueVars]
      split <;> simp_all

theorem uniqueVars_nodup {α : Type} [DecidableEq α]
    (items : List α) :
    (uniqueVars items).Nodup := by
  induction items with
  | nil =>
      simp [uniqueVars]
  | cons head tail ih =>
      simp only [uniqueVars]
      split <;> rename_i hmem
      · exact ih
      · constructor
        · intro item hitem heq
          subst item
          exact hmem (mem_uniqueVars.mp hitem)
        · exact ih

end TypePM
