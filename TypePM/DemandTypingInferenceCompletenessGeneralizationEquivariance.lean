import TypePM.DemandTypingInferenceCompletenessLocalRenaming
import TypePM.SourceGeneralization

/-!
# Equivariance of canonical generalization under a scoped renaming

Generalized metavariables become canonical finite indices, while variables
free in the environment remain free metas and are transported by the ambient
renaming.  These lemmas isolate that two-part behavior.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessGeneralizationEquivariance

open DemandTypingInferenceCompletenessLocalRenaming

/-! ## Generic finite-list facts -/

theorem List.uniqueVars_map_of_injectiveOn
    {alpha beta : Type} [DecidableEq alpha] [DecidableEq beta]
    (rename : alpha → beta) : ∀ items : List alpha,
    (∀ {left right}, left ∈ items → right ∈ items →
      rename left = rename right → left = right) →
    uniqueVars (items.map rename) = (uniqueVars items).map rename := by
  intro items injective
  induction items with
  | nil => rfl
  | cons head tail induction =>
      have tailInjective : ∀ {left right}, left ∈ tail → right ∈ tail →
          rename left = rename right → left = right := by
        intro left right leftMem rightMem equal
        exact injective (by simp [leftMem]) (by simp [rightMem]) equal
      have memberIff : rename head ∈ tail.map rename ↔ head ∈ tail := by
        constructor
        · intro member
          rcases List.mem_map.mp member with ⟨source, sourceMem, equal⟩
          exact (injective (by simp) (by simp [sourceMem]) equal.symm) ▸ sourceMem
        · exact fun member => List.mem_map.mpr ⟨head, member, rfl⟩
      simp only [List.map_cons, uniqueVars]
      rw [induction tailInjective]
      split <;> rename_i branch
      · have : head ∈ tail := memberIff.mp branch
        simp [this]
      · have : head ∉ tail := fun member => branch (memberIff.mpr member)
        simp [this]

theorem List.filter_map_of_iff
    {alpha beta : Type} (rename : alpha → beta)
    (leftKeep : beta → Bool) (rightKeep : alpha → Bool) :
    ∀ items : List alpha,
      (∀ item ∈ items, leftKeep (rename item) = rightKeep item) →
      (items.map rename).filter leftKeep =
        (items.filter rightKeep).map rename := by
  intro items agreement
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.filter_cons]
      rw [agreement head (by simp)]
      split
      · simp only [List.map_cons]
        rw [induction (fun item member => agreement item (by simp [member]))]
      · exact induction (fun item member => agreement item (by simp [member]))

/-- Finite-index lookup commutes with an injective renaming on the binder list
and on the queried variable. -/
theorem List.finIdxOf?_map_of_injectiveOn
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (rename : alpha → beta) (query : alpha) : ∀ binders : List alpha,
    (∀ item ∈ binders, rename item = rename query → item = query) →
    (binders.map rename).finIdxOf? (rename query) =
      (binders.finIdxOf? query).map (Fin.cast (by simp)) := by
  intro binders injective
  induction binders with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons]
      rw [List.finIdxOf?_cons, List.finIdxOf?_cons]
      by_cases equal : head = query
      · subst head
        simp
      · have renamedNe : rename head ≠ rename query := by
          intro renamed
          exact equal (injective head (by simp) renamed)
        simp only [beq_iff_eq, renamedNe, equal, ↓reduceIte]
        rw [induction (fun item member renamed =>
          injective item (by simp [member]) renamed)]
        cases tail.finIdxOf? query <;> rfl

/-- Mapping a finite index across an equality of bounds changes only its
dependent type, not the represented index. -/
theorem Option.map_finCast_heq {left right : Nat}
    (bound : left = right) (index : Option (Fin left)) :
    HEq (index.map (Fin.cast bound)) index := by
  subst right
  cases index <;> rfl

/-! ## Pure representatives of a scoped renaming -/

noncomputable def LocalRenamingOn.pureSubst
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope) :
    Subst :=
  { cap := fun varId => .var (certificate.capImage varId)
    target := fun varId => .var (certificate.targetImage varId) }

theorem LocalRenamingOn.forward_apply_eq_pure
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (target : Ty)
    (caps : ∀ varId, varId ∈ target.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ target.ftv → varId ∈ targetScope) :
    forward.apply target = (pureSubst certificate).apply target := by
  apply Subst.apply_eq_of_free_agree
  · intro varId member
    exact certificate.cap_forward (caps varId member)
  · intro varId member
    exact certificate.target_forward (targets varId member)

/-! ## Free-variable traversals under a pure renaming -/

mutual

theorem Ty.fcv_applyTarget_vars (rename : TypePM.TyVar → TypePM.TyVar) :
    ∀ target : Ty,
      (target.applyTarget (fun varId => .var (rename varId))).fcv = target.fcv
  | .var _ => rfl
  | .skolem _ => rfl
  | .unit => rfl
  | .int => rfl
  | .bool => rfl
  | .data name children => by
      simp only [Ty.applyTarget, Ty.fcv]
      exact Ty.fcvList_applyTarget_vars rename children
  | .prod components => by
      simp only [Ty.applyTarget, Ty.fcv]
      exact Ty.fcvList_applyTarget_vars rename components
  | .fn domain codomain => by
      simp only [Ty.applyTarget, Ty.fcv]
      rw [Ty.fcv_applyTarget_vars rename domain,
        Ty.fcv_applyTarget_vars rename codomain]
  | .matcher capability target => by
      simp only [Ty.applyTarget, Ty.fcv]
      rw [Ty.fcv_applyTarget_vars rename target]
  | .slot capability target => by
      simp only [Ty.applyTarget, Ty.fcv]
      rw [Ty.fcv_applyTarget_vars rename target]

theorem Ty.fcvList_applyTarget_vars (rename : TypePM.TyVar → TypePM.TyVar) :
    ∀ targets : List Ty,
      Ty.fcvList (Ty.applyTargetList (fun varId => .var (rename varId)) targets) =
        Ty.fcvList targets
  | [] => rfl
  | target :: targets => by
      simp only [Ty.applyTargetList, Ty.fcvList]
      rw [Ty.fcv_applyTarget_vars rename target,
        Ty.fcvList_applyTarget_vars rename targets]

end

theorem LocalRenamingOn.pure_apply_fcv
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (target : Ty) :
    ((pureSubst certificate).apply target).fcv =
      target.fcv.map certificate.capImage := by
  change
    ((target.applyCapability
      (fun varId => .var (certificate.capImage varId))).applyTarget
        (fun varId => .var (certificate.targetImage varId))).fcv = _
  rw [Ty.fcv_applyTarget_vars, Unification.Ty.fcv_applyCapability]
  induction target.fcv <;> simp_all [Cap.fcv]

theorem LocalRenamingOn.pure_apply_ftv
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (target : Ty) :
    ((pureSubst certificate).apply target).ftv =
      target.ftv.map certificate.targetImage := by
  change
    ((target.applyCapability
      (fun varId => .var (certificate.capImage varId))).applyTarget
        (fun varId => .var (certificate.targetImage varId))).ftv = _
  rw [Unification.Ty.ftv_applyTarget,
    Unification.Ty.ftv_applyCapability]
  induction target.ftv <;> simp_all [Ty.ftv]

/-! ## Closing equivariance -/

mutual

theorem PolyCap.abstract_renaming
    (capRename : CapVar → CapVar) :
    ∀ {capArity : Nat} (leftClose : CapVar → Option (Fin capArity))
      (rightClose : CapVar → Option (Fin capArity)) (capability : Cap),
      (∀ varId ∈ capability.fcv,
        leftClose (capRename varId) = rightClose varId) →
      PolyCap.abstract leftClose
          (capability.apply (fun varId => .var (capRename varId))) =
        (PolyCap.abstract rightClose capability).applyMeta
          (fun varId => .var (capRename varId))
  | _, _, _, .any, _ => by
      simp only [Cap.apply, PolyCap.abstract, PolyCap.applyMeta]
  | _, leftClose, rightClose, .var varId, agreement => by
      simp only [Cap.apply, PolyCap.abstract]
      rw [agreement varId (by simp [Cap.fcv])]
      cases rightClose varId <;>
        simp [PolyCap.applyMeta, PolyCap.lift]
  | _, _, _, .skolem _, _ => by
      simp only [Cap.apply, PolyCap.abstract, PolyCap.applyMeta]
  | _, leftClose, rightClose, .con name children, agreement => by
      simp only [Cap.apply, PolyCap.abstract, PolyCap.applyMeta]
      change PolyCap.con name _ = PolyCap.con name _
      congr 1
      exact PolyCap.abstractList_renaming capRename leftClose rightClose
        children (fun varId member => agreement varId (by
          simpa [Cap.fcv] using member))
  | _, leftClose, rightClose, .prod components, agreement => by
      simp only [Cap.apply, PolyCap.abstract, PolyCap.applyMeta]
      change PolyCap.prod _ = PolyCap.prod _
      congr 1
      exact PolyCap.abstractList_renaming capRename leftClose rightClose
        components (fun varId member => agreement varId (by
          simpa [Cap.fcv] using member))

theorem PolyCap.abstractList_renaming
    (capRename : CapVar → CapVar) {capArity : Nat}
    (leftClose : CapVar → Option (Fin capArity))
    (rightClose : CapVar → Option (Fin capArity)) :
    ∀ capabilities : List Cap,
      (∀ varId ∈ Cap.fcvList capabilities,
        leftClose (capRename varId) = rightClose varId) →
      (Cap.applyList (fun varId => .var (capRename varId)) capabilities).map
          (PolyCap.abstract leftClose) =
        (capabilities.map (PolyCap.abstract rightClose)).map
          (PolyCap.applyMeta (fun varId => .var (capRename varId)))
  | [], _ => rfl
  | capability :: capabilities, agreement => by
      simp only [Cap.applyList, List.map_cons]
      congr 1
      · exact PolyCap.abstract_renaming capRename leftClose rightClose capability
          (fun varId member => agreement varId (by
            simp [Cap.fcvList, member]))
      · exact PolyCap.abstractList_renaming capRename leftClose rightClose
          capabilities (fun varId member => agreement varId (by
            simp [Cap.fcvList, member]))

end

mutual

theorem PolyTy.abstract_renaming
    (capRename : CapVar → CapVar)
    (targetRename : TypePM.TyVar → TypePM.TyVar) :
    ∀ {capArity tyArity : Nat}
      (leftCap : CapVar → Option (Fin capArity))
      (rightCap : CapVar → Option (Fin capArity))
      (leftTy : TypePM.TyVar → Option (Fin tyArity))
      (rightTy : TypePM.TyVar → Option (Fin tyArity))
      (target : Ty),
      (∀ varId ∈ target.fcv,
        leftCap (capRename varId) = rightCap varId) →
      (∀ varId ∈ target.ftv,
        leftTy (targetRename varId) = rightTy varId) →
      PolyTy.abstract leftCap leftTy
          ((Subst.mk (fun varId => .var (capRename varId))
            (fun varId => .var (targetRename varId))).apply target) =
        (PolyTy.abstract rightCap rightTy target).applyMeta
          (Subst.mk (fun varId => .var (capRename varId))
            (fun varId => .var (targetRename varId)))
  | _, _, leftCap, rightCap, leftTy, rightTy, .var varId, _, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract]
      rw [tyAgreement varId (by simp [Ty.ftv])]
      cases rightTy varId <;>
        simp [PolyTy.applyMeta, PolyTy.lift]
  | _, _, _, _, _, _, .skolem _, _, _ => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
  | _, _, _, _, _, _, .unit, _, _ => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
  | _, _, _, _, _, _, .int, _, _ => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
  | _, _, _, _, _, _, .bool, _, _ => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
  | _, _, leftCap, rightCap, leftTy, rightTy, .data name children,
      capAgreement, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
      change PolyTy.data name _ = PolyTy.data name _
      congr 1
      exact PolyTy.abstractList_renaming capRename targetRename leftCap
        rightCap leftTy rightTy children
        (fun varId member => capAgreement varId (by
          simpa [Ty.fcv] using member))
        (fun varId member => tyAgreement varId (by
          simpa [Ty.ftv] using member))
  | _, _, leftCap, rightCap, leftTy, rightTy, .prod components,
      capAgreement, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
      change PolyTy.prod _ = PolyTy.prod _
      congr 1
      exact PolyTy.abstractList_renaming capRename targetRename leftCap
        rightCap leftTy rightTy components
        (fun varId member => capAgreement varId (by
          simpa [Ty.fcv] using member))
        (fun varId member => tyAgreement varId (by
          simpa [Ty.ftv] using member))
  | _, _, leftCap, rightCap, leftTy, rightTy, .fn domain codomain,
      capAgreement, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
      change PolyTy.fn _ _ = PolyTy.fn _ _
      congr 1
      · exact PolyTy.abstract_renaming capRename targetRename leftCap rightCap
          leftTy rightTy domain
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
          (fun varId member => tyAgreement varId (by simp [Ty.ftv, member]))
      · exact PolyTy.abstract_renaming capRename targetRename leftCap rightCap
          leftTy rightTy codomain
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
          (fun varId member => tyAgreement varId (by simp [Ty.ftv, member]))
  | _, _, leftCap, rightCap, leftTy, rightTy, .matcher capability target,
      capAgreement, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
      change PolyTy.matcher _ _ = PolyTy.matcher _ _
      congr 1
      · exact PolyCap.abstract_renaming capRename leftCap rightCap capability
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
      · exact PolyTy.abstract_renaming capRename targetRename leftCap rightCap
          leftTy rightTy target
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
          tyAgreement
  | _, _, leftCap, rightCap, leftTy, rightTy, .slot capability target,
      capAgreement, tyAgreement => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        PolyTy.abstract, PolyTy.applyMeta]
      change PolyTy.slot _ _ = PolyTy.slot _ _
      congr 1
      · exact PolyCap.abstract_renaming capRename leftCap rightCap capability
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
      · exact PolyTy.abstract_renaming capRename targetRename leftCap rightCap
          leftTy rightTy target
          (fun varId member => capAgreement varId (by simp [Ty.fcv, member]))
          tyAgreement

theorem PolyTy.abstractList_renaming
    (capRename : CapVar → CapVar)
    (targetRename : TypePM.TyVar → TypePM.TyVar)
    {capArity tyArity : Nat}
    (leftCap : CapVar → Option (Fin capArity))
    (rightCap : CapVar → Option (Fin capArity))
    (leftTy : TypePM.TyVar → Option (Fin tyArity))
    (rightTy : TypePM.TyVar → Option (Fin tyArity)) :
    ∀ targets : List Ty,
      (∀ varId ∈ Ty.fcvList targets,
        leftCap (capRename varId) = rightCap varId) →
      (∀ varId ∈ Ty.ftvList targets,
        leftTy (targetRename varId) = rightTy varId) →
      (Ty.applyTargetList (fun varId => .var (targetRename varId))
        (Ty.applyCapabilityList (fun varId => .var (capRename varId))
          targets)).map (PolyTy.abstract leftCap leftTy) =
        (targets.map (PolyTy.abstract rightCap rightTy)).map
          (PolyTy.applyMeta
            (Subst.mk (fun varId => .var (capRename varId))
              (fun varId => .var (targetRename varId))))
  | [], _, _ => rfl
  | target :: targets, capAgreement, tyAgreement => by
      simp only [Ty.applyCapabilityList, Ty.applyTargetList, List.map_cons]
      congr 1
      · exact PolyTy.abstract_renaming capRename targetRename leftCap rightCap
          leftTy rightTy target
          (fun varId member => capAgreement varId (by
            simp [Ty.fcvList, member]))
          (fun varId member => tyAgreement varId (by
            simp [Ty.ftvList, member]))
      · exact PolyTy.abstractList_renaming capRename targetRename leftCap
          rightCap leftTy rightTy targets
          (fun varId member => capAgreement varId (by
            simp [Ty.fcvList, member]))
          (fun varId member => tyAgreement varId (by
            simp [Ty.ftvList, member]))

end

/-- Heterogeneous-arities form of `PolyTy.abstract_renaming`.  This is the
form needed by `Scheme.close`, whose binder lists are pointwise renamed and
therefore propositionally, rather than definitionally, equal in length. -/
theorem PolyTy.abstract_renaming_heq
    (capRename : CapVar → CapVar)
    (targetRename : TypePM.TyVar → TypePM.TyVar)
    {leftCapArity rightCapArity leftTyArity rightTyArity : Nat}
    (capArity : leftCapArity = rightCapArity)
    (tyArity : leftTyArity = rightTyArity)
    (leftCap : CapVar → Option (Fin leftCapArity))
    (rightCap : CapVar → Option (Fin rightCapArity))
    (leftTy : TypePM.TyVar → Option (Fin leftTyArity))
    (rightTy : TypePM.TyVar → Option (Fin rightTyArity))
    (target : Ty)
    (caps : ∀ varId ∈ target.fcv,
      HEq (leftCap (capRename varId)) (rightCap varId))
    (targets : ∀ varId ∈ target.ftv,
      HEq (leftTy (targetRename varId)) (rightTy varId)) :
    HEq
      (PolyTy.abstract leftCap leftTy
        ((Subst.mk (fun varId => .var (capRename varId))
          (fun varId => .var (targetRename varId))).apply target))
      ((PolyTy.abstract rightCap rightTy target).applyMeta
        (Subst.mk (fun varId => .var (capRename varId))
          (fun varId => .var (targetRename varId)))) := by
  subst rightCapArity
  subst rightTyArity
  apply heq_of_eq
  apply PolyTy.abstract_renaming capRename targetRename
  · intro varId member
    exact eq_of_heq (caps varId member)
  · intro varId member
    exact eq_of_heq (targets varId member)

end DemandTypingInferenceCompletenessGeneralizationEquivariance
end TypePM
