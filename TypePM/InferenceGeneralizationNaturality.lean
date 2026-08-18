import TypePM.DamasMilnerWLetStability

/-!
# Two-sorted naturality of let generalization

Terminal let stability ultimately needs closing to commute with a paired
capability/type substitution.  The Damas--Milner fragment only needs the
target-only specialization.  This module establishes the corresponding
capture-avoiding algebra for both metavariable sorts.
-/

namespace TypePM
namespace DM

mutual

/-- Capability abstraction commutes with a structural substitution which
fixes abstracted variables and whose free images do not capture them. -/
theorem PolyCap.abstract_applyMeta_paired {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) (C : CapSubst) :
    ∀ capability : Cap,
    (∀ varId index, closeCap varId = some index → C varId = .var varId) →
    (∀ varId, closeCap varId = none → ∀ image,
      image ∈ (C varId).fcv → closeCap image = none) →
    (PolyCap.abstract closeCap capability).applyMeta C =
      PolyCap.abstract closeCap (capability.apply C)
  | .any, _, _ => by simp [PolyCap.abstract, PolyCap.applyMeta, Cap.apply]
  | .var varId, fixed, avoids => by
      cases closing : closeCap varId with
      | some index =>
          simp [PolyCap.abstract, PolyCap.applyMeta, Cap.apply, closing,
            fixed varId index closing]
      | none =>
          simp only [PolyCap.abstract, PolyCap.applyMeta, Cap.apply, closing]
          symm
          exact PolyCap.abstract_eq_lift_of_none closeCap (C varId)
            (by intro image membership
                exact avoids varId closing image membership)
  | .skolem _, _, _ => by
      simp [PolyCap.abstract, PolyCap.applyMeta, Cap.apply]
  | .con name children, fixed, avoids => by
      simp only [PolyCap.abstract, PolyCap.applyMeta, Cap.apply, List.map_map]
      congr 1
      simpa only [List.map_map, Function.comp_def] using
        (PolyCap.abstractList_applyMeta_paired closeCap C children fixed
          avoids)
  | .prod components, fixed, avoids => by
      simp only [PolyCap.abstract, PolyCap.applyMeta, Cap.apply, List.map_map]
      congr 1
      simpa only [List.map_map, Function.comp_def] using
        (PolyCap.abstractList_applyMeta_paired closeCap C components fixed
          avoids)

/-- List form of `PolyCap.abstract_applyMeta_paired`. -/
theorem PolyCap.abstractList_applyMeta_paired {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) (C : CapSubst) :
    ∀ capabilities : List Cap,
    (∀ varId index, closeCap varId = some index → C varId = .var varId) →
    (∀ varId, closeCap varId = none → ∀ image,
      image ∈ (C varId).fcv → closeCap image = none) →
    (capabilities.map (PolyCap.abstract closeCap)).map
        (PolyCap.applyMeta C) =
      (Cap.applyList C capabilities).map (PolyCap.abstract closeCap)
  | [], _, _ => rfl
  | head :: tail, fixed, avoids => by
      simp only [List.map_cons, Cap.applyList]
      rw [PolyCap.abstract_applyMeta_paired closeCap C head fixed avoids,
        PolyCap.abstractList_applyMeta_paired closeCap C tail fixed avoids]

end

mutual

/-- Two-sorted abstraction commutes with a paired structural substitution
when neither substitution range can capture an abstracted variable. -/
theorem PolyTy.abstract_applyMeta_paired {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (S : Subst) :
    ∀ target : Ty,
    (∀ varId index, closeCap varId = some index →
      S.cap varId = .var varId) →
    (∀ varId, closeCap varId = none → ∀ image,
      image ∈ (S.cap varId).fcv → closeCap image = none) →
    (∀ varId index, closeTy varId = some index →
      S.target varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (S.target varId).ftv → closeTy image = none) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (S.target varId).fcv → closeCap image = none) →
    (PolyTy.abstract closeCap closeTy target).applyMeta S =
      PolyTy.abstract closeCap closeTy (S.apply target)
  | .var varId, _, _, fixedTy, avoidsTy, avoidsCap => by
      cases closing : closeTy varId with
      | some index =>
          simp [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
            Ty.applyCapability, Ty.applyTarget, closing,
            fixedTy varId index closing]
      | none =>
          simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
            Ty.applyCapability, Ty.applyTarget, closing]
          symm
          exact PolyTy.abstract_eq_lift_of_none closeCap closeTy
            (S.target varId)
            (by intro image membership
                exact avoidsCap varId closing image membership)
            (by intro image membership
                exact avoidsTy varId closing image membership)
  | .skolem _, _, _, _, _, _ => by
      simp [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .unit, _, _, _, _, _ => by
      simp [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .int, _, _, _, _, _ => by
      simp [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .bool, _, _, _, _, _ => by
      simp [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .data name children, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget, List.map_map]
      congr 1
      simpa only [Subst.applyList_eq_map, List.map_map,
        Function.comp_def] using
        (PolyTy.abstractList_applyMeta_paired closeCap closeTy S children
          fixedCap avoidsCap fixedTy avoidsTy targetCapsAvoid)
  | .prod components, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget, List.map_map]
      congr 1
      simpa only [Subst.applyList_eq_map, List.map_map,
        Function.comp_def] using
        (PolyTy.abstractList_applyMeta_paired closeCap closeTy S components
          fixedCap avoidsCap fixedTy avoidsTy targetCapsAvoid)
  | .fn domain codomain, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyTy.abstract_applyMeta_paired closeCap closeTy S domain
          fixedCap avoidsCap fixedTy avoidsTy targetCapsAvoid,
        PolyTy.abstract_applyMeta_paired closeCap closeTy S codomain
          fixedCap avoidsCap fixedTy avoidsTy targetCapsAvoid]
      rfl
  | .matcher capability target, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyCap.abstract_applyMeta_paired closeCap S.cap capability fixedCap
          avoidsCap,
        PolyTy.abstract_applyMeta_paired closeCap closeTy S target fixedCap
          avoidsCap fixedTy avoidsTy targetCapsAvoid]
      rfl
  | .slot capability target, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyCap.abstract_applyMeta_paired closeCap S.cap capability fixedCap
          avoidsCap,
        PolyTy.abstract_applyMeta_paired closeCap closeTy S target fixedCap
          avoidsCap fixedTy avoidsTy targetCapsAvoid]
      rfl

/-- List form of `PolyTy.abstract_applyMeta_paired`. -/
theorem PolyTy.abstractList_applyMeta_paired {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (S : Subst) :
    ∀ targets : List Ty,
    (∀ varId index, closeCap varId = some index →
      S.cap varId = .var varId) →
    (∀ varId, closeCap varId = none → ∀ image,
      image ∈ (S.cap varId).fcv → closeCap image = none) →
    (∀ varId index, closeTy varId = some index →
      S.target varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (S.target varId).ftv → closeTy image = none) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (S.target varId).fcv → closeCap image = none) →
    (targets.map (PolyTy.abstract closeCap closeTy)).map
        (PolyTy.applyMeta S) =
      (targets.map (S.apply)).map (PolyTy.abstract closeCap closeTy)
  | [], _, _, _, _, _ => rfl
  | head :: tail, fixedCap, avoidsCap, fixedTy, avoidsTy,
      targetCapsAvoid => by
      simp only [List.map_cons]
      rw [PolyTy.abstract_applyMeta_paired closeCap closeTy S head fixedCap
          avoidsCap fixedTy avoidsTy targetCapsAvoid,
        PolyTy.abstractList_applyMeta_paired closeCap closeTy S tail fixedCap
          avoidsCap fixedTy avoidsTy targetCapsAvoid]

end

/-- Closing commutes with an arbitrary paired substitution under the exact
finite capture-avoidance conditions needed by let stability. -/
theorem Scheme.close_applyMeta_paired
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (target : Ty) (S : Subst)
    (capFixed : ∀ varId, varId ∈ capBinders →
      S.cap varId = .var varId)
    (capAvoids : ∀ varId, varId ∉ capBinders → ∀ image,
      image ∈ (S.cap varId).fcv → image ∉ capBinders)
    (tyFixed : ∀ varId, varId ∈ tyBinders →
      S.target varId = .var varId)
    (tyAvoids : ∀ varId, varId ∉ tyBinders → ∀ image,
      image ∈ (S.target varId).ftv → image ∉ tyBinders)
    (targetCapsAvoid : ∀ varId, varId ∉ tyBinders → ∀ image,
      image ∈ (S.target varId).fcv → image ∉ capBinders) :
    (Scheme.close capBinders tyBinders target).applyMeta S =
      Scheme.close capBinders tyBinders (S.apply target) := by
  unfold Scheme.close Scheme.applyMeta
  congr 1
  apply PolyTy.abstract_applyMeta_paired
  · intro varId index closing
    apply capFixed varId
    exact Classical.byContradiction (fun outside => by
      have noneEq := List.finIdxOf?_eq_none_iff.mpr outside
      rw [noneEq] at closing
      contradiction)
  · intro varId closing image membership
    apply List.finIdxOf?_eq_none_iff.mpr
    exact capAvoids varId (List.finIdxOf?_eq_none_iff.mp closing) image
      membership
  · intro varId index closing
    apply tyFixed varId
    exact Classical.byContradiction (fun outside => by
      have noneEq := List.finIdxOf?_eq_none_iff.mpr outside
      rw [noneEq] at closing
      contradiction)
  · intro varId closing image membership
    apply List.finIdxOf?_eq_none_iff.mpr
    exact tyAvoids varId (List.finIdxOf?_eq_none_iff.mp closing) image
      membership
  · intro varId closing image membership
    apply List.finIdxOf?_eq_none_iff.mpr
    exact targetCapsAvoid varId (List.finIdxOf?_eq_none_iff.mp closing) image
      membership

/-- Signature-aware generalization commutes with a paired substitution once
the ordered binder lists are known to be unchanged.  The remaining premises
are exactly the finite support/range separation facts needed to avoid capture
by those binders. -/
theorem FrozenSig.generalize_apply_of_binders_eq
    (signature : FrozenSig) (context : Context) (target : Ty) (S : Subst)
    (capBindersEq :
      signature.generalizedCapVars (context.applySubst S) (S.apply target) =
        signature.generalizedCapVars context target)
    (tyBindersEq :
      signature.generalizedTyVars (context.applySubst S) (S.apply target) =
        signature.generalizedTyVars context target)
    (capFixed : ∀ varId,
      varId ∈ signature.generalizedCapVars context target →
        S.cap varId = .var varId)
    (capAvoids : ∀ varId,
      varId ∉ signature.generalizedCapVars context target → ∀ image,
        image ∈ (S.cap varId).fcv →
          image ∉ signature.generalizedCapVars context target)
    (tyFixed : ∀ varId,
      varId ∈ signature.generalizedTyVars context target →
        S.target varId = .var varId)
    (tyAvoids : ∀ varId,
      varId ∉ signature.generalizedTyVars context target → ∀ image,
        image ∈ (S.target varId).ftv →
          image ∉ signature.generalizedTyVars context target)
    (targetCapsAvoid : ∀ varId,
      varId ∉ signature.generalizedTyVars context target → ∀ image,
        image ∈ (S.target varId).fcv →
          image ∉ signature.generalizedCapVars context target) :
    (signature.generalize context target).applyMeta S =
      signature.generalize (context.applySubst S) (S.apply target) := by
  unfold FrozenSig.generalize Scheme.generalize
  change
    (Scheme.close (signature.generalizedCapVars context target)
      (signature.generalizedTyVars context target) target).applyMeta S =
      Scheme.close
        (signature.generalizedCapVars (context.applySubst S) (S.apply target))
        (signature.generalizedTyVars (context.applySubst S) (S.apply target))
        (S.apply target)
  rw [capBindersEq, tyBindersEq]
  exact Scheme.close_applyMeta_paired
    (signature.generalizedCapVars context target)
    (signature.generalizedTyVars context target) target S capFixed capAvoids
    tyFixed tyAvoids targetCapsAvoid

/-- Full two-sorted solver step safety follows from ordinary exact-MGU
support/range confinement and preservation of the two ordered generalization
binder lists.  Unlike the earlier target-only theorem, this permits genuine
capability constraints. -/
theorem OriginSafeExactPairedMGU.letGeneralizationStepSafe_of_binders_eq
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    (capBindersEq :
      signature.generalizedCapVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedCapVars
          (cut.context.applySubst current) (current.apply cut.target))
    (tyBindersEq :
      signature.generalizedTyVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target)) :
    LetGeneralizationStepSafe signature current delta cut := by
  let context := cut.context.applySubst current
  let target := current.apply cut.target
  have capFixed : ∀ varId,
      varId ∈ signature.generalizedCapVars context target →
        delta.cap varId = .var varId := by
    intro varId generalized
    exact TypePM.DM.OriginSafeExactPairedMGU.cap_fixed_of_letSeparated
      exact separated generalized
  have capAvoids : ∀ varId,
      varId ∉ signature.generalizedCapVars context target → ∀ image,
        image ∈ (delta.cap varId).fcv →
          image ∉ signature.generalizedCapVars context target := by
    intro source sourceOutside image imageIn
    by_cases sourceIn : source ∈ left.fcv ++ right.fcv
    · exact TypePM.DM.OriginSafeExactPairedMGU.cap_range_avoids_letGeneralized
        exact separated sourceIn imageIn
    · have fixed := exact.exact.2.1 source sourceIn
      rw [fixed] at imageIn
      have imageEq : image = source := by simpa [Cap.fcv] using imageIn
      subst image
      exact sourceOutside
  have tyFixed : ∀ varId,
      varId ∈ signature.generalizedTyVars context target →
        delta.target varId = .var varId := by
    intro varId generalized
    exact TypePM.DM.OriginSafeExactPairedMGU.target_fixed_of_letSeparated
      exact separated generalized
  have tyAvoids : ∀ varId,
      varId ∉ signature.generalizedTyVars context target → ∀ image,
        image ∈ (delta.target varId).ftv →
          image ∉ signature.generalizedTyVars context target := by
    intro source sourceOutside image imageIn
    by_cases sourceIn : source ∈ left.ftv ++ right.ftv
    · exact TypePM.DM.OriginSafeExactPairedMGU.target_range_avoids_letGeneralized
        exact separated sourceIn imageIn
    · have fixed := exact.exact.2.2.1 source sourceIn
      rw [fixed] at imageIn
      have imageEq : image = source := by simpa [Ty.ftv] using imageIn
      subst image
      exact sourceOutside
  have targetCapsAvoid : ∀ varId,
      varId ∉ signature.generalizedTyVars context target → ∀ image,
        image ∈ (delta.target varId).fcv →
          image ∉ signature.generalizedCapVars context target := by
    intro source _sourceOutside image imageIn
    by_cases sourceIn : source ∈ left.ftv ++ right.ftv
    · exact
        TypePM.DM.OriginSafeExactPairedMGU.target_cap_range_avoids_letGeneralized
          exact separated sourceIn imageIn
    · have fixed := exact.exact.2.2.1 source sourceIn
      rw [fixed] at imageIn
      simp [Ty.fcv] at imageIn
  unfold LetGeneralizationStepSafe
  rw [Context.applySubst_seq, Subst.seq_apply]
  change (signature.generalize context target).applyMeta delta =
    signature.generalize (context.applySubst delta) (delta.apply target)
  apply FrozenSig.generalize_apply_of_binders_eq signature context target delta
  · simpa [context, target, Context.applySubst_seq, Subst.seq_apply] using
      capBindersEq
  · simpa [context, target, Context.applySubst_seq, Subst.seq_apply] using
      tyBindersEq
  · exact capFixed
  · exact capAvoids
  · exact tyFixed
  · exact tyAvoids
  · exact targetCapsAvoid

end DM
end TypePM
