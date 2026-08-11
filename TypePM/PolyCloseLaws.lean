import TypePM.PolyInstantiation

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

/-! ## Replaying a finite opening as an ordinary substitution -/

/-- Turn a finite capability opening back into an ordinary substitution on
the names that were selected for closing. -/
def openingCapSubst (binders : List CapVar)
    (opening : Fin binders.length → CapVar) : CapSubst :=
  fun varId =>
    match binders.finIdxOf? varId with
    | some index => .var (opening index)
    | none => .var varId

/-- Turn a finite target opening back into an ordinary substitution on the
names that were selected for closing. -/
def openingTySubst (binders : List TypePM.TyVar)
    (opening : Fin binders.length → Ty) : TySubst :=
  fun varId =>
    match binders.finIdxOf? varId with
    | some index => opening index
    | none => .var varId

namespace PolyCap

mutual

/-- Closing and opening with arbitrary finite capability images is exactly
the ordinary substitution induced by those images. -/
theorem instantiate_abstract_open (binders : List CapVar)
    (opening : Fin binders.length → CapVar) :
    ∀ capability : Cap,
      PolyCap.instantiate (fun index => Cap.var (opening index))
          (PolyCap.abstract (fun varId => binders.finIdxOf? varId)
            capability) =
        capability.apply (openingCapSubst binders opening)
  | .any => by simp [PolyCap.abstract, PolyCap.instantiate, Cap.apply]
  | .var varId => by
      simp only [PolyCap.abstract]
      split <;> rename_i found <;>
        simp [PolyCap.instantiate, Cap.apply, openingCapSubst, found]
  | .skolem _ => by simp [PolyCap.abstract, PolyCap.instantiate, Cap.apply]
  | .con name children => by
      simp only [PolyCap.abstract, PolyCap.instantiate, Cap.apply]
      congr 1
      exact instantiate_abstract_open_list binders opening children
  | .prod components => by
      simp only [PolyCap.abstract, PolyCap.instantiate, Cap.apply]
      congr 1
      exact instantiate_abstract_open_list binders opening components

/-- List form of `PolyCap.instantiate_abstract_open`. -/
theorem instantiate_abstract_open_list (binders : List CapVar)
    (opening : Fin binders.length → CapVar) :
    ∀ capabilities : List Cap,
      (capabilities.map
          (PolyCap.abstract (fun varId => binders.finIdxOf? varId))).map
          (PolyCap.instantiate (fun index => Cap.var (opening index))) =
        Cap.applyList (openingCapSubst binders opening) capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [instantiate_abstract_open binders opening capability,
        instantiate_abstract_open_list binders opening capabilities]
      rfl

end

end PolyCap

namespace PolyTy

mutual

/-- Closing and opening both finite binder sorts is exactly their induced
ordinary paired substitution. -/
theorem instantiate_abstract_open
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (capOpening : Fin capBinders.length → CapVar)
    (tyOpening : Fin tyBinders.length → Ty) :
    ∀ target : Ty,
      PolyTy.instantiate (fun index => Cap.var (capOpening index)) tyOpening
          (PolyTy.abstract
            (fun varId => capBinders.finIdxOf? varId)
            (fun varId => tyBinders.finIdxOf? varId) target) =
        (Subst.mk (openingCapSubst capBinders capOpening)
          (openingTySubst tyBinders tyOpening)).apply target
  | .var varId => by
      simp only [PolyTy.abstract]
      split <;> rename_i found <;>
        simp [PolyTy.instantiate, Subst.apply, openingTySubst, found,
          Ty.applyCapability, Ty.applyTarget]
  | .skolem _ => by simp [PolyTy.abstract, PolyTy.instantiate, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .unit => by simp [PolyTy.abstract, PolyTy.instantiate, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .int => by simp [PolyTy.abstract, PolyTy.instantiate, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .bool => by simp [PolyTy.abstract, PolyTy.instantiate, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .data name children => by
      simp only [PolyTy.abstract, PolyTy.instantiate, Subst.apply]
      congr 1
      exact instantiate_abstract_open_list capBinders tyBinders
        capOpening tyOpening children
  | .prod components => by
      simp only [PolyTy.abstract, PolyTy.instantiate, Subst.apply]
      congr 1
      exact instantiate_abstract_open_list capBinders tyBinders
        capOpening tyOpening components
  | .fn domain codomain => by
      simp only [PolyTy.abstract, PolyTy.instantiate, Subst.apply]
      rw [instantiate_abstract_open capBinders tyBinders capOpening tyOpening domain,
        instantiate_abstract_open capBinders tyBinders capOpening tyOpening codomain]
      rfl
  | .matcher capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate, Subst.apply]
      rw [PolyCap.instantiate_abstract_open capBinders capOpening capability,
        instantiate_abstract_open capBinders tyBinders capOpening tyOpening target]
      rfl
  | .slot capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate, Subst.apply]
      rw [PolyCap.instantiate_abstract_open capBinders capOpening capability,
        instantiate_abstract_open capBinders tyBinders capOpening tyOpening target]
      rfl

/-- List form of `PolyTy.instantiate_abstract_open`. -/
theorem instantiate_abstract_open_list
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (capOpening : Fin capBinders.length → CapVar)
    (tyOpening : Fin tyBinders.length → Ty) :
    ∀ targets : List Ty,
      (targets.map
          (PolyTy.abstract
            (fun varId => capBinders.finIdxOf? varId)
            (fun varId => tyBinders.finIdxOf? varId))).map
          (PolyTy.instantiate (fun index => Cap.var (capOpening index))
            tyOpening) =
        Ty.applyTargetList (openingTySubst tyBinders tyOpening)
          (Ty.applyCapabilityList (openingCapSubst capBinders capOpening)
            targets)
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [instantiate_abstract_open capBinders tyBinders capOpening tyOpening target,
        instantiate_abstract_open_list capBinders tyBinders capOpening
          tyOpening targets]
      rfl

end


end PolyTy

namespace PolyCap

mutual

/-- Abstracting with an empty capability binder space is the ordinary lift. -/
theorem abstract_none_eq_lift : ∀ capability : Cap,
    PolyCap.abstract
        (fun varId => ([] : List CapVar).finIdxOf? varId) capability =
      PolyCap.lift capability
  | .any => by simp [PolyCap.abstract, PolyCap.lift]
  | .var _ => by simp [PolyCap.abstract, PolyCap.lift]
  | .skolem _ => by simp [PolyCap.abstract, PolyCap.lift]
  | .con name children => by
      simp only [PolyCap.abstract, PolyCap.lift]
      congr 1
      exact abstractList_none_eq_lift children
  | .prod components => by
      simp only [PolyCap.abstract, PolyCap.lift]
      congr 1
      exact abstractList_none_eq_lift components

/-- List form of `PolyCap.abstract_none_eq_lift`. -/
theorem abstractList_none_eq_lift : ∀ capabilities : List Cap,
    capabilities.map
        (PolyCap.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)) =
      capabilities.map PolyCap.lift
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [abstract_none_eq_lift capability,
        abstractList_none_eq_lift capabilities]

end

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

/-- Abstracting with empty binder spaces is the ordinary polymorphic lift. -/
theorem abstract_none_eq_lift : ∀ target : Ty,
    PolyTy.abstract
        (fun varId => ([] : List CapVar).finIdxOf? varId)
        (fun varId => ([] : List TypePM.TyVar).finIdxOf? varId) target =
      PolyTy.lift target
  | .var _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .skolem _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .unit => by simp [PolyTy.abstract, PolyTy.lift]
  | .int => by simp [PolyTy.abstract, PolyTy.lift]
  | .bool => by simp [PolyTy.abstract, PolyTy.lift]
  | .data name children => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact abstractList_none_eq_lift children
  | .prod components => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact abstractList_none_eq_lift components
  | .fn domain codomain => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [abstract_none_eq_lift domain, abstract_none_eq_lift codomain]
  | .matcher capability target => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_none_eq_lift capability,
        abstract_none_eq_lift target]
  | .slot capability target => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_none_eq_lift capability,
        abstract_none_eq_lift target]

/-- List form of `PolyTy.abstract_none_eq_lift`. -/
theorem abstractList_none_eq_lift : ∀ targets : List Ty,
    targets.map
        (PolyTy.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)
          (fun varId => ([] : List TypePM.TyVar).finIdxOf? varId)) =
      targets.map PolyTy.lift
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [abstract_none_eq_lift target, abstractList_none_eq_lift targets]

end

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

namespace Scheme

/-- A finite opening of a freshly closed scheme is exactly the paired
ordinary substitution induced on the selected source names. -/
theorem openValue_close
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (target : Ty) (opening : (close capBinders tyBinders target).ValueOpening) :
    (close capBinders tyBinders target).openValue opening =
      (Subst.mk (openingCapSubst capBinders opening.capImage)
        (openingTySubst tyBinders opening.tyImage)).apply target := by
  exact PolyTy.instantiate_abstract_open capBinders tyBinders
    opening.capImage opening.tyImage target

/-- Closing no binders is exactly the canonical monomorphic embedding. -/
@[simp] theorem close_nil_nil (target : Ty) :
    close [] [] target = mono target := by
  unfold close mono
  congr 1
  exact PolyTy.abstract_none_eq_lift target

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

end Scheme
end TypePM
