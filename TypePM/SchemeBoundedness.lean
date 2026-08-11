import TypePM.Bounds
import TypePM.PolyFreeVars
import TypePM.PolyGeneralization

/-!
# Boundedness of canonical expression schemes

This module connects the finite-index `Scheme` representation to the fresh
supply bounds used by demand typing.  Bound indices are not solver
metavariables and therefore do not contribute to `Scheme.BoundedBy`.
Opening is expressed only through the dedicated opening functions.
-/

namespace TypePM

namespace PolyCap

mutual

@[simp] theorem fcv_lift {capArity : Nat} :
    ∀ capability : Cap, (lift (capArity := capArity) capability).fcv =
      capability.fcv
  | .any => by simp [lift, fcv, Cap.fcv]
  | .var _ => by simp [lift, fcv, Cap.fcv]
  | .skolem _ => by simp [lift, fcv, Cap.fcv]
  | .con _ children => by
      simp only [lift, fcv]
      exact fcvList_lift children
  | .prod components => by
      simp only [lift, fcv]
      exact fcvList_lift components

@[simp] theorem fcvList_lift {capArity : Nat} :
    ∀ capabilities : List Cap,
      PolyCap.fcvList
          (capabilities.map (lift (capArity := capArity))) =
        Cap.fcvList capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons, fcvList, Cap.fcvList, fcv_lift]
      rw [fcvList_lift capabilities]

end

end PolyCap

namespace PolyTy

mutual

@[simp] theorem fcv_lift {capArity tyArity : Nat} :
    ∀ target : Ty,
      (lift (capArity := capArity) (tyArity := tyArity) target).fcv =
        target.fcv
  | .var _ => by simp [lift, fcv, Ty.fcv]
  | .skolem _ => by simp [lift, fcv, Ty.fcv]
  | .unit => by simp [lift, fcv, Ty.fcv]
  | .int => by simp [lift, fcv, Ty.fcv]
  | .bool => by simp [lift, fcv, Ty.fcv]
  | .data _ children => by
      simp only [lift, fcv]
      exact fcvList_lift children
  | .prod components => by
      simp only [lift, fcv]
      exact fcvList_lift components
  | .fn domain codomain => by
      simp only [lift, fcv, Ty.fcv, fcv_lift domain, fcv_lift codomain]
  | .matcher capability target => by
      simp only [lift, fcv, Ty.fcv, PolyCap.fcv_lift, fcv_lift target]
  | .slot capability target => by
      simp only [lift, fcv, Ty.fcv, PolyCap.fcv_lift, fcv_lift target]

@[simp] theorem fcvList_lift {capArity tyArity : Nat} :
    ∀ targets : List Ty,
      PolyTy.fcvList (targets.map (lift (capArity := capArity)
        (tyArity := tyArity))) = Ty.fcvList targets
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons, fcvList, Ty.fcvList, fcv_lift]
      rw [fcvList_lift targets]

end


mutual

@[simp] theorem ftv_lift {capArity tyArity : Nat} :
    ∀ target : Ty,
      (lift (capArity := capArity) (tyArity := tyArity) target).ftv =
        target.ftv
  | .var _ => by simp [lift, ftv, Ty.ftv]
  | .skolem _ => by simp [lift, ftv, Ty.ftv]
  | .unit => by simp [lift, ftv, Ty.ftv]
  | .int => by simp [lift, ftv, Ty.ftv]
  | .bool => by simp [lift, ftv, Ty.ftv]
  | .data _ children => by
      simp only [lift, ftv]
      exact ftvList_lift children
  | .prod components => by
      simp only [lift, ftv]
      exact ftvList_lift components
  | .fn domain codomain => by
      simp only [lift, ftv, Ty.ftv, ftv_lift domain, ftv_lift codomain]
  | .matcher _ target => by simp [lift, ftv, Ty.ftv, ftv_lift target]
  | .slot _ target => by simp [lift, ftv, Ty.ftv, ftv_lift target]

@[simp] theorem ftvList_lift {capArity tyArity : Nat} :
    ∀ targets : List Ty,
      PolyTy.ftvList (targets.map (lift (capArity := capArity)
        (tyArity := tyArity))) = Ty.ftvList targets
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons, ftvList, Ty.ftvList, ftv_lift]
      rw [ftvList_lift targets]

end


end PolyTy

namespace PolyCap

mutual

/-- Opening a polymorphic capability preserves supply boundedness when both
its free metavariables and its finite opening images are bounded. -/
theorem instantiate_boundedBy {capArity : Nat}
    {supply : InferenceBase.FreshSupply}
    (openCap : Fin capArity → Cap)
    (openingBounded : ∀ index, (openCap index).BoundedBy supply) :
    ∀ capability : PolyCap capArity,
      (∀ varId ∈ capability.fcv, varId.id < supply.nextCap) →
      (capability.instantiate openCap).BoundedBy supply
  | .any, _ => by
      simp only [instantiate]
      intro _ mem
      exact nomatch mem
  | .mvar varId, freeBounded => by
      simpa only [instantiate] using
        Cap.BoundedBy.varOf (freeBounded varId (by simp [fcv]))
  | .bound index, _ => by
      simpa only [instantiate] using openingBounded index
  | .skolem _, _ => by
      simp only [instantiate]
      intro _ mem
      exact nomatch mem
  | .con name children, freeBounded => by
      simp only [instantiate]
      apply Cap.BoundedBy.conOfForall
      intro capability mem
      obtain ⟨raw, rawMem, rfl⟩ := List.mem_map.mp mem
      exact instantiateList_boundedBy openCap openingBounded children
        freeBounded raw rawMem
  | .prod components, freeBounded => by
      simp only [instantiate]
      apply Cap.BoundedBy.prodOfForall
      intro capability mem
      obtain ⟨raw, rawMem, rfl⟩ := List.mem_map.mp mem
      exact instantiateList_boundedBy openCap openingBounded components
        freeBounded raw rawMem

/-- List form of `PolyCap.instantiate_boundedBy`. -/
theorem instantiateList_boundedBy {capArity : Nat}
    {supply : InferenceBase.FreshSupply}
    (openCap : Fin capArity → Cap)
    (openingBounded : ∀ index, (openCap index).BoundedBy supply) :
    ∀ capabilities : List (PolyCap capArity),
      (∀ varId ∈ PolyCap.fcvList capabilities,
        varId.id < supply.nextCap) →
      ∀ capability ∈ capabilities,
        (capability.instantiate openCap).BoundedBy supply
  | [], _, _, mem => nomatch mem
  | head :: tail, freeBounded, capability, mem => by
      rcases List.mem_cons.mp mem with headEq | tailMem
      · subst capability
        apply instantiate_boundedBy openCap openingBounded head
        intro varId varMem
        exact freeBounded varId (List.mem_append.mpr (Or.inl varMem))
      · apply instantiateList_boundedBy openCap openingBounded tail
          (fun varId varMem =>
            freeBounded varId (List.mem_append.mpr (Or.inr varMem)))
          capability tailMem

end

end PolyCap

namespace PolyTy

mutual

/-- Opening a polymorphic type is bounded when its free metavariables and
both opening images are bounded. -/
theorem instantiate_boundedBy {capArity tyArity : Nat}
    {supply : InferenceBase.FreshSupply}
    (openCap : Fin capArity → Cap) (openTy : Fin tyArity → Ty)
    (capsOpeningBounded : ∀ index, (openCap index).BoundedBy supply)
    (tysOpeningBounded : ∀ index, (openTy index).BoundedBy supply) :
    ∀ target : PolyTy capArity tyArity,
      (∀ varId ∈ target.fcv, varId.id < supply.nextCap) →
      (∀ varId ∈ target.ftv, varId < supply.nextTy) →
      (target.instantiate openCap openTy).BoundedBy supply
  | .mvar varId, _, freeTys =>
      by simpa only [instantiate] using
        Ty.BoundedBy.varOf (freeTys varId (by simp [ftv]))
  | .bound index, _, _ => by
      simpa only [instantiate] using tysOpeningBounded index
  | .skolem _, _, _ => by
      simp only [instantiate]
      constructor <;> intro _ mem <;> exact nomatch mem
  | .unit, _, _ => by
      simp only [instantiate]
      constructor <;> intro _ mem <;> exact nomatch mem
  | .int, _, _ => by simpa only [instantiate] using
      (Ty.BoundedBy.int (q := supply))
  | .bool, _, _ => by
      simp only [instantiate]
      constructor <;> intro _ mem <;> exact nomatch mem
  | .data name children, freeCaps, freeTys => by
      have childrenBounded := instantiateList_boundedBy openCap openTy
        capsOpeningBounded tysOpeningBounded children freeCaps freeTys
      simp only [instantiate]
      constructor
      · intro varId mem
        obtain ⟨child, childMem, varMem⟩ := Ty.mem_fcvList_split mem
        obtain ⟨rawChild, rawMem, rfl⟩ := List.mem_map.mp childMem
        exact (childrenBounded rawChild rawMem).caps varId varMem
      · intro varId mem
        obtain ⟨child, childMem, varMem⟩ := Ty.mem_ftvList_split mem
        obtain ⟨rawChild, rawMem, rfl⟩ := List.mem_map.mp childMem
        exact (childrenBounded rawChild rawMem).targets varId varMem
  | .prod components, freeCaps, freeTys => by
      simp only [instantiate]
      apply Ty.BoundedBy.prodOfForall
      intro target mem
      obtain ⟨raw, rawMem, rfl⟩ := List.mem_map.mp mem
      exact instantiateList_boundedBy openCap openTy capsOpeningBounded
        tysOpeningBounded components freeCaps freeTys raw rawMem
  | .fn domain codomain, freeCaps, freeTys => by
      simp only [instantiate]
      apply Ty.BoundedBy.fnOf
      · exact instantiate_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded domain
          (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inl mem)))
          (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inl mem)))
      · exact instantiate_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded codomain
          (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inr mem)))
          (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inr mem)))
  | .matcher capability target, freeCaps, freeTys => by
      simp only [instantiate]
      apply Ty.BoundedBy.matcherOf
      · apply PolyCap.instantiate_boundedBy openCap capsOpeningBounded
          capability
        intro varId mem
        exact freeCaps varId (List.mem_append.mpr (Or.inl mem))
      · apply instantiate_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded target
        · intro varId mem
          exact freeCaps varId (List.mem_append.mpr (Or.inr mem))
        · exact freeTys
  | .slot capability target, freeCaps, freeTys => by
      simp only [instantiate]
      apply Ty.BoundedBy.slotOf
      · apply PolyCap.instantiate_boundedBy openCap capsOpeningBounded
          capability
        intro varId mem
        exact freeCaps varId (List.mem_append.mpr (Or.inl mem))
      · apply instantiate_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded target
        · intro varId mem
          exact freeCaps varId (List.mem_append.mpr (Or.inr mem))
        · exact freeTys

/-- List form of `PolyTy.instantiate_boundedBy`. -/
theorem instantiateList_boundedBy {capArity tyArity : Nat}
    {supply : InferenceBase.FreshSupply}
    (openCap : Fin capArity → Cap) (openTy : Fin tyArity → Ty)
    (capsOpeningBounded : ∀ index, (openCap index).BoundedBy supply)
    (tysOpeningBounded : ∀ index, (openTy index).BoundedBy supply) :
    ∀ targets : List (PolyTy capArity tyArity),
      (∀ varId ∈ PolyTy.fcvList targets, varId.id < supply.nextCap) →
      (∀ varId ∈ PolyTy.ftvList targets, varId < supply.nextTy) →
      ∀ target ∈ targets,
        (target.instantiate openCap openTy).BoundedBy supply
  | [], _, _, _, mem => nomatch mem
  | head :: tail, freeCaps, freeTys, target, mem => by
      rcases List.mem_cons.mp mem with headEq | tailMem
      · subst target
        apply instantiate_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded head
        · intro varId varMem
          exact freeCaps varId (List.mem_append.mpr (Or.inl varMem))
        · intro varId varMem
          exact freeTys varId (List.mem_append.mpr (Or.inl varMem))
      · apply instantiateList_boundedBy openCap openTy capsOpeningBounded
          tysOpeningBounded tail
          (fun varId varMem =>
            freeCaps varId (List.mem_append.mpr (Or.inr varMem)))
          (fun varId varMem =>
            freeTys varId (List.mem_append.mpr (Or.inr varMem)))
          target tailMem

end

end PolyTy

namespace PolyCap

mutual

/-- Ambient capability substitution preserves bounded free metavariables. -/
theorem applyMeta_fcv_bounded {capArity : Nat}
    {supply : InferenceBase.FreshSupply} {substitution : Subst}
    (substBounded : substitution.BoundedBy supply) :
    ∀ capability : PolyCap capArity,
      (∀ varId ∈ capability.fcv, varId.id < supply.nextCap) →
      ∀ varId ∈ (capability.applyMeta substitution.cap).fcv,
        varId.id < supply.nextCap
  | .any, _, _, mem => by
      simp [applyMeta, fcv] at mem
  | .mvar original, freeBounded, varId, mem => by
      simp only [applyMeta, fcv_lift] at mem
      exact substBounded.capImagesBounded original
        (freeBounded original (by simp [fcv])) varId mem
  | .bound _, _, _, mem => by simp [applyMeta, fcv] at mem
  | .skolem _, _, _, mem => by simp [applyMeta, fcv] at mem
  | .con _ children, freeBounded, varId, mem => by
      apply applyMeta_fcvList_bounded substBounded children freeBounded
        varId
      simpa only [applyMeta, fcv] using mem
  | .prod components, freeBounded, varId, mem => by
      apply applyMeta_fcvList_bounded substBounded components freeBounded
        varId
      simpa only [applyMeta, fcv] using mem

/-- List form of `PolyCap.applyMeta_fcv_bounded`. -/
theorem applyMeta_fcvList_bounded {capArity : Nat}
    {supply : InferenceBase.FreshSupply} {substitution : Subst}
    (substBounded : substitution.BoundedBy supply) :
    ∀ capabilities : List (PolyCap capArity),
      (∀ varId ∈ PolyCap.fcvList capabilities,
        varId.id < supply.nextCap) →
      ∀ varId ∈ PolyCap.fcvList
        (capabilities.map (PolyCap.applyMeta substitution.cap)),
        varId.id < supply.nextCap
  | [], _, _, mem => nomatch mem
  | head :: tail, freeBounded, varId, mem => by
      rcases List.mem_append.mp mem with headMem | tailMem
      · exact applyMeta_fcv_bounded substBounded head
          (fun original originalMem =>
            freeBounded original (List.mem_append.mpr (Or.inl originalMem)))
          varId headMem
      · exact applyMeta_fcvList_bounded substBounded tail
          (fun original originalMem =>
            freeBounded original (List.mem_append.mpr (Or.inr originalMem)))
          varId tailMem

end

end PolyCap

namespace PolyTy

mutual

/-- Ambient paired substitution preserves bounded free metavariables of both
sorts in a polymorphic type. -/
theorem applyMeta_free_bounded {capArity tyArity : Nat}
    {supply : InferenceBase.FreshSupply} {substitution : Subst}
    (substBounded : substitution.BoundedBy supply) :
    ∀ target : PolyTy capArity tyArity,
      (∀ varId ∈ target.fcv, varId.id < supply.nextCap) →
      (∀ varId ∈ target.ftv, varId < supply.nextTy) →
      ((∀ varId ∈ (target.applyMeta substitution).fcv,
          varId.id < supply.nextCap) ∧
       (∀ varId ∈ (target.applyMeta substitution).ftv,
          varId < supply.nextTy))
  | .mvar original, _, freeTys => by
      constructor
      · intro varId mem
        simp only [applyMeta, fcv_lift] at mem
        exact (substBounded.targetImagesBounded original
          (freeTys original (by simp [ftv]))).caps varId mem
      · intro varId mem
        simp only [applyMeta, ftv_lift] at mem
        exact (substBounded.targetImagesBounded original
          (freeTys original (by simp [ftv]))).targets varId mem
  | .bound _, _, _ => by
      constructor <;> intro _ mem <;> simp [applyMeta, fcv, ftv] at mem
  | .skolem _, _, _ => by
      constructor <;> intro _ mem <;> simp [applyMeta, fcv, ftv] at mem
  | .unit, _, _ => by
      constructor <;> intro _ mem <;> simp [applyMeta, fcv, ftv] at mem
  | .int, _, _ => by
      constructor <;> intro _ mem <;> simp [applyMeta, fcv, ftv] at mem
  | .bool, _, _ => by
      constructor <;> intro _ mem <;> simp [applyMeta, fcv, ftv] at mem
  | .data _ children, freeCaps, freeTys => by
      simpa only [applyMeta, fcv, ftv] using
        applyMeta_freeList_bounded substBounded children freeCaps freeTys
  | .prod components, freeCaps, freeTys => by
      simpa only [applyMeta, fcv, ftv] using
        applyMeta_freeList_bounded substBounded components freeCaps freeTys
  | .fn domain codomain, freeCaps, freeTys => by
      have domainBounded := applyMeta_free_bounded substBounded domain
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inl mem)))
        (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inl mem)))
      have codomainBounded := applyMeta_free_bounded substBounded codomain
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inr mem)))
        (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inr mem)))
      constructor
      · intro varId mem
        simp only [applyMeta, fcv, List.mem_append] at mem
        exact mem.elim (domainBounded.1 varId) (codomainBounded.1 varId)
      · intro varId mem
        simp only [applyMeta, ftv, List.mem_append] at mem
        exact mem.elim (domainBounded.2 varId) (codomainBounded.2 varId)
  | .matcher capability target, freeCaps, freeTys => by
      have capabilityBounded := PolyCap.applyMeta_fcv_bounded substBounded
        capability
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inl mem)))
      have targetBounded := applyMeta_free_bounded substBounded target
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inr mem)))
        freeTys
      constructor
      · intro varId mem
        simp only [applyMeta, fcv, List.mem_append] at mem
        exact mem.elim (capabilityBounded varId) (targetBounded.1 varId)
      · intro varId mem
        simp only [applyMeta, ftv] at mem
        exact targetBounded.2 varId mem
  | .slot capability target, freeCaps, freeTys => by
      have capabilityBounded := PolyCap.applyMeta_fcv_bounded substBounded
        capability
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inl mem)))
      have targetBounded := applyMeta_free_bounded substBounded target
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inr mem)))
        freeTys
      constructor
      · intro varId mem
        simp only [applyMeta, fcv, List.mem_append] at mem
        exact mem.elim (capabilityBounded varId) (targetBounded.1 varId)
      · intro varId mem
        simp only [applyMeta, ftv] at mem
        exact targetBounded.2 varId mem

/-- List form of `PolyTy.applyMeta_free_bounded`. -/
theorem applyMeta_freeList_bounded {capArity tyArity : Nat}
    {supply : InferenceBase.FreshSupply} {substitution : Subst}
    (substBounded : substitution.BoundedBy supply) :
    ∀ targets : List (PolyTy capArity tyArity),
      (∀ varId ∈ PolyTy.fcvList targets,
        varId.id < supply.nextCap) →
      (∀ varId ∈ PolyTy.ftvList targets, varId < supply.nextTy) →
      ((∀ varId ∈ PolyTy.fcvList
          (targets.map (PolyTy.applyMeta substitution)),
          varId.id < supply.nextCap) ∧
       (∀ varId ∈ PolyTy.ftvList
          (targets.map (PolyTy.applyMeta substitution)),
          varId < supply.nextTy))
  | [], _, _ => by constructor <;> intro _ mem <;> exact nomatch mem
  | head :: tail, freeCaps, freeTys => by
      have headBounded := applyMeta_free_bounded substBounded head
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inl mem)))
        (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inl mem)))
      have tailBounded := applyMeta_freeList_bounded substBounded tail
        (fun varId mem => freeCaps varId (List.mem_append.mpr (Or.inr mem)))
        (fun varId mem => freeTys varId (List.mem_append.mpr (Or.inr mem)))
      constructor
      · intro varId mem
        simp only [List.map_cons, fcvList, List.mem_append] at mem
        exact mem.elim (headBounded.1 varId) (tailBounded.1 varId)
      · intro varId mem
        simp only [List.map_cons, ftvList, List.mem_append] at mem
        exact mem.elim (headBounded.2 varId) (tailBounded.2 varId)

end

end PolyTy

namespace Scheme

/-- All free solver metavariables of a canonical scheme lie below a supply.
Finite bound indices are excluded structurally by `PolyTy.fcv`/`ftv`. -/
structure BoundedBy (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) : Prop where
  caps : ∀ varId ∈ scheme.fcv, varId.id < supply.nextCap
  targets : ∀ varId ∈ scheme.ftv, varId < supply.nextTy

/-- Scheme boundedness is monotone along supply extension. -/
theorem BoundedBy.mono {supply successor : InferenceBase.FreshSupply}
    {scheme : Scheme} (extends_ : SupplyExtends supply successor)
    (bounded : scheme.BoundedBy supply) : scheme.BoundedBy successor :=
  ⟨fun varId mem => Nat.lt_of_lt_of_le (bounded.caps varId mem) extends_.1,
    fun varId mem =>
      Nat.lt_of_lt_of_le (bounded.targets varId mem) extends_.2⟩

/-- A monomorphic canonical scheme is bounded exactly when its type is. -/
theorem BoundedBy.ofMono {supply : InferenceBase.FreshSupply} {target : Ty}
    (bounded : target.BoundedBy supply) :
    (Scheme.mono target).BoundedBy supply := by
  constructor
  · intro varId mem
    exact bounded.caps varId (by simpa [Scheme.fcv, Scheme.mono] using mem)
  · intro varId mem
    exact bounded.targets varId (by
      simpa [Scheme.ftv, Scheme.mono] using mem)

/-- Closing selected ordinary metavariables into finite indices preserves
boundedness of every remaining free metavariable. -/
theorem BoundedBy.close {supply : InferenceBase.FreshSupply} {target : Ty}
    (bounded : target.BoundedBy supply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (Scheme.close capBinders tyBinders target).BoundedBy supply := by
  let closeCap := fun varId => capBinders.finIdxOf? varId
  let closeTy := fun varId => tyBinders.finIdxOf? varId
  have subset := PolyTy.abstract_free_subset closeCap closeTy target
  constructor
  · intro varId membership
    apply bounded.caps varId
    exact subset.1 varId (by
      simpa [Scheme.close, Scheme.fcv, closeCap, closeTy] using membership)
  · intro varId membership
    apply bounded.targets varId
    exact subset.2 varId (by
      simpa [Scheme.close, Scheme.ftv, closeCap, closeTy] using membership)

/-- Generalization is closing, so it cannot introduce free solver
metavariables beyond those of the generalized type. -/
theorem BoundedBy.generalize {supply : InferenceBase.FreshSupply}
    {target : Ty} (bounded : target.BoundedBy supply)
    (envCaps : List CapVar) (envTys : List TypePM.TyVar) :
    (Scheme.generalize envCaps envTys target).BoundedBy supply := by
  exact Scheme.BoundedBy.close bounded (generalizedCapVars envCaps target)
    (generalizedTyVars envTys target)

/-- Applying a bounded ambient substitution to free scheme metavariables
preserves scheme boundedness. -/
theorem BoundedBy.applyMeta {supply : InferenceBase.FreshSupply}
    {scheme : Scheme} {substitution : Subst}
    (schemeBounded : scheme.BoundedBy supply)
    (substBounded : substitution.BoundedBy supply) :
    (scheme.applyMeta substitution).BoundedBy supply := by
  have bodyBounded := PolyTy.applyMeta_free_bounded substBounded scheme.body
    schemeBounded.caps schemeBounded.targets
  exact ⟨bodyBounded.1, bodyBounded.2⟩

/-- Opening a bounded scheme with bounded images produces a bounded ordinary
type.  The opening remains a dedicated `ValueOpening`, not a `Subst`. -/
theorem openValue_boundedBy {supply : InferenceBase.FreshSupply}
    {scheme : Scheme} (schemeBounded : scheme.BoundedBy supply)
    (opening : scheme.ValueOpening)
    (capImagesBounded : ∀ index,
      (Cap.var (opening.capImage index)).BoundedBy supply)
    (tyImagesBounded : ∀ index,
      (opening.tyImage index).BoundedBy supply) :
    (scheme.openValue opening).BoundedBy supply := by
  exact PolyTy.instantiate_boundedBy
    (fun index => .var (opening.capImage index)) opening.tyImage
    capImagesBounded tyImagesBounded scheme.body schemeBounded.caps
    schemeBounded.targets

/-- Fresh instantiation always advances both counters monotonically. -/
theorem freshInstantiate_supplyExtends
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    SupplyExtends supply (scheme.freshInstantiate supply).supply := by
  constructor
  · rw [freshInstantiate_nextCap]
    exact Nat.le_add_right _ _
  · rw [freshInstantiate_nextTy]
    exact Nat.le_add_right _ _

/-- The canonical fresh opening lies exactly in the half-open interval
reserved between the input and successor supplies. -/
theorem canonicalFreshOpening_between
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    (∀ index,
      supply.nextCap ≤
        ((canonicalFreshOpening supply scheme).capImage index).id ∧
      ((canonicalFreshOpening supply scheme).capImage index).id <
        (scheme.freshInstantiate supply).supply.nextCap) ∧
    (∀ index,
      supply.nextTy ≤
        (canonicalFreshOpening supply scheme).tyImage index ∧
      (canonicalFreshOpening supply scheme).tyImage index <
        (scheme.freshInstantiate supply).supply.nextTy) := by
  exact ⟨fun index =>
      ⟨canonicalFreshOpening_cap_lower supply scheme index,
        canonicalFreshOpening_cap_upper supply scheme index⟩,
    fun index =>
      ⟨canonicalFreshOpening_ty_lower supply scheme index,
        canonicalFreshOpening_ty_upper supply scheme index⟩⟩

/-- Canonical fresh instantiation of a bounded scheme is bounded by its
successor supply. -/
theorem freshInstantiate_value_boundedBy
    {supply : InferenceBase.FreshSupply} {scheme : Scheme}
    (schemeBounded : scheme.BoundedBy supply) :
    (scheme.freshInstantiate supply).value.BoundedBy
      (scheme.freshInstantiate supply).supply := by
  have extends_ := freshInstantiate_supplyExtends supply scheme
  have boundedAtSuccessor := schemeBounded.mono extends_
  rw [freshInstantiate_value]
  apply openValue_boundedBy boundedAtSuccessor
  · intro index
    apply Cap.BoundedBy.varOf
    exact canonicalFreshOpening_cap_upper supply scheme index
  · intro index
    apply Ty.BoundedBy.varOf
    exact canonicalFreshOpening_ty_upper supply scheme index

end Scheme

end TypePM
