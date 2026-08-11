import TypePM.PolyScheme

/-!
# Closing and reopening laws for capture-free schemes

Closing replaces selected solver metavariables by finite local indices.
Reopening those indices with the corresponding entries of the original
binder lists recovers the source syntax exactly.  The result does not require
duplicate-free binder lists: `finIdxOf?` chooses an occurrence whose `get`
value is the queried variable.
-/

namespace TypePM

/-! ## The finite-index lookup fact used by both sorts -/

/-- A successful finite index lookup points to an equal list element. -/
theorem List.get_eq_of_finIdxOf?_eq_some {alpha : Type} [BEq alpha]
    [LawfulBEq alpha] {items : List alpha} {item : alpha}
    {index : Fin items.length} (found : items.finIdxOf? item = some index) :
    items.get index = item := by
  exact (List.finIdxOf?_eq_some_iff.mp found).1

namespace PolyCap

mutual

/-- Abstracting through a capability binder list and reopening with that
list's variables recovers the original capability. -/
theorem instantiate_abstract_get (binders : List CapVar) :
    ∀ capability : Cap,
      PolyCap.instantiate (fun index => Cap.var (binders.get index))
          (PolyCap.abstract (fun varId => binders.finIdxOf? varId)
            capability) =
        capability
  | .any => by simp [PolyCap.abstract, PolyCap.instantiate]
  | .var varId => by
      simp only [PolyCap.abstract]
      split <;> rename_i found
      · simp only [PolyCap.instantiate]
        rw [List.get_eq_of_finIdxOf?_eq_some found]
      · simp [PolyCap.instantiate]
  | .skolem _ => by simp [PolyCap.abstract, PolyCap.instantiate]
  | .con name children => by
      simp only [PolyCap.abstract, PolyCap.instantiate]
      congr 1
      exact PolyCap.instantiate_abstract_get_list binders children
  | .prod components => by
      simp only [PolyCap.abstract, PolyCap.instantiate]
      congr 1
      exact PolyCap.instantiate_abstract_get_list binders components

/-- List form of `PolyCap.instantiate_abstract_get`. -/
theorem instantiate_abstract_get_list (binders : List CapVar) :
    ∀ capabilities : List Cap,
      (capabilities.map
          (PolyCap.abstract (fun varId => binders.finIdxOf? varId))).map
          (PolyCap.instantiate
            (fun index => Cap.var (binders.get index))) =
        capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [PolyCap.instantiate_abstract_get binders capability,
        PolyCap.instantiate_abstract_get_list binders capabilities]

end

end PolyCap

namespace PolyTy

mutual

/-- Abstracting both variable sorts through binder lists and reopening with
the corresponding original variables recovers an ordinary type. -/
theorem instantiate_abstract_get
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar) :
    ∀ target : Ty,
      PolyTy.instantiate
          (fun index => Cap.var (capBinders.get index))
          (fun index => Ty.var (tyBinders.get index))
          (PolyTy.abstract
            (fun varId => capBinders.finIdxOf? varId)
            (fun varId => tyBinders.finIdxOf? varId) target) =
        target
  | .var varId => by
      simp only [PolyTy.abstract]
      split <;> rename_i found
      · simp only [PolyTy.instantiate]
        rw [List.get_eq_of_finIdxOf?_eq_some found]
      · simp [PolyTy.instantiate]
  | .skolem _ => by simp [PolyTy.abstract, PolyTy.instantiate]
  | .unit => by simp [PolyTy.abstract, PolyTy.instantiate]
  | .int => by simp [PolyTy.abstract, PolyTy.instantiate]
  | .bool => by simp [PolyTy.abstract, PolyTy.instantiate]
  | .data name children => by
      simp only [PolyTy.abstract, PolyTy.instantiate]
      congr 1
      exact PolyTy.instantiate_abstract_get_list capBinders tyBinders children
  | .prod components => by
      simp only [PolyTy.abstract, PolyTy.instantiate]
      congr 1
      exact PolyTy.instantiate_abstract_get_list capBinders tyBinders components
  | .fn domain codomain => by
      simp only [PolyTy.abstract, PolyTy.instantiate]
      rw [PolyTy.instantiate_abstract_get capBinders tyBinders domain,
        PolyTy.instantiate_abstract_get capBinders tyBinders codomain]
  | .matcher capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate]
      rw [PolyCap.instantiate_abstract_get capBinders capability,
        PolyTy.instantiate_abstract_get capBinders tyBinders target]
  | .slot capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate]
      rw [PolyCap.instantiate_abstract_get capBinders capability,
        PolyTy.instantiate_abstract_get capBinders tyBinders target]

/-- List form of `PolyTy.instantiate_abstract_get`. -/
theorem instantiate_abstract_get_list
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar) :
    ∀ targets : List Ty,
      (targets.map
          (PolyTy.abstract
            (fun varId => capBinders.finIdxOf? varId)
            (fun varId => tyBinders.finIdxOf? varId))).map
          (PolyTy.instantiate
            (fun index => Cap.var (capBinders.get index))
            (fun index => Ty.var (tyBinders.get index))) =
        targets
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [PolyTy.instantiate_abstract_get capBinders tyBinders target,
        PolyTy.instantiate_abstract_get_list capBinders tyBinders targets]

end

end PolyTy

namespace PolyScheme

/-- Closing an ordinary target and reopening its finite binders with the
original binder-list variables is a left inverse, even when a binder list
contains duplicates. -/
theorem instantiate_close_get
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (target : Ty) :
    (close capBinders tyBinders target).instantiate
        (fun index => Cap.var (capBinders.get index))
        (fun index => Ty.var (tyBinders.get index)) =
      target := by
  exact PolyTy.instantiate_abstract_get capBinders tyBinders target

end PolyScheme
end TypePM
