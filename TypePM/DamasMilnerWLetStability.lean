import TypePM.DamasMilnerWLet
import TypePM.DemandTypingInferenceCompletenessContextBisimulation

/-!
# Terminal stability of Algorithm W let cuts

The public demand-typing certificate records one exact generalization
equation for every `let`.  A raw W derivation and its residual equations do
not imply that equation: a later solver may otherwise specialize a variable
which was generalized at the cut.  This module makes the missing invariant
explicit and threads it beside `WProtectedFrameAt`.

`LetGeneralizationStepSafe` is the solver-facing boundary.  It says precisely
that one later substitution commutes with the generalization selected at a
pending cut.  Fresh scheme opening changes only the semantic residual and
therefore needs no such premise.  An ordinary exact cut changes the
prevailing substitution and must supply the premise for every pending cut.
-/

namespace TypePM
namespace DM

open DemandTypingInferenceCompletenessContextBisimulation

/-! ## Free-target-variable accounting through scheme substitution -/

mutual

theorem PolyTy.ftv_applyMeta_flatMap {capArity tyArity : Nat}
    (substitution : Subst) : ∀ target : PolyTy capArity tyArity,
    (target.applyMeta substitution).ftv =
      target.ftv.flatMap fun varId => (substitution.target varId).ftv
  | .mvar varId => by
      simp [PolyTy.applyMeta, PolyTy.ftv, PolyTy.ftv_lift]
  | .bound _ => by simp [PolyTy.applyMeta, PolyTy.ftv]
  | .skolem _ => by simp [PolyTy.applyMeta, PolyTy.ftv]
  | .unit => by simp [PolyTy.applyMeta, PolyTy.ftv]
  | .int => by simp [PolyTy.applyMeta, PolyTy.ftv]
  | .bool => by simp [PolyTy.applyMeta, PolyTy.ftv]
  | .data _ children => by
      simp [PolyTy.applyMeta, PolyTy.ftv,
        PolyTy.ftvList_applyMeta_flatMap substitution children]
  | .prod components => by
      simp [PolyTy.applyMeta, PolyTy.ftv,
        PolyTy.ftvList_applyMeta_flatMap substitution components]
  | .fn domain codomain => by
      simp [PolyTy.applyMeta, PolyTy.ftv, List.flatMap_append,
        PolyTy.ftv_applyMeta_flatMap substitution domain,
        PolyTy.ftv_applyMeta_flatMap substitution codomain]
  | .matcher _ target => by
      simp [PolyTy.applyMeta, PolyTy.ftv,
        PolyTy.ftv_applyMeta_flatMap substitution target]
  | .slot _ target => by
      simp [PolyTy.applyMeta, PolyTy.ftv,
        PolyTy.ftv_applyMeta_flatMap substitution target]

theorem PolyTy.ftvList_applyMeta_flatMap {capArity tyArity : Nat}
    (substitution : Subst) : ∀ targets : List (PolyTy capArity tyArity),
    PolyTy.ftvList (targets.map (PolyTy.applyMeta substitution)) =
      (PolyTy.ftvList targets).flatMap fun varId =>
        (substitution.target varId).ftv
  | [] => by simp [PolyTy.ftvList]
  | target :: targets => by
      simp [PolyTy.ftvList, List.flatMap_append,
        PolyTy.ftv_applyMeta_flatMap substitution target,
        PolyTy.ftvList_applyMeta_flatMap substitution targets]

end

/-
mutual

theorem PolyTy.abstract_target_eq_lift_of_none {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) : ∀ target : Ty,
    (∀ varId, varId ∈ target.ftv → closeTy varId = none) →
    PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy target =
      PolyTy.lift target
  | .var varId, allNone => by
      have closing := allNone varId (by simp [Ty.ftv])
      simp [PolyTy.abstract, PolyTy.lift, closing]
  | .skolem _, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .unit, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .int, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .bool, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .data name children, allNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact PolyTy.abstractTargetList_eq_lift_of_none closeTy children (by
        intro varId member; exact allNone varId (by simpa [Ty.ftv] using member))
  | .prod components, allNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact PolyTy.abstractTargetList_eq_lift_of_none closeTy components (by
        intro varId member; exact allNone varId (by simpa [Ty.ftv] using member))
  | .fn domain codomain, allNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyTy.abstract_target_eq_lift_of_none closeTy domain
          (by intro varId member; exact allNone varId (by simp [Ty.ftv, member])),
        PolyTy.abstract_target_eq_lift_of_none closeTy codomain
          (by intro varId member; exact allNone varId (by simp [Ty.ftv, member]))]
  | .matcher capability target, allNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_none_eq_lift,
        PolyTy.abstract_target_eq_lift_of_none closeTy target
          (by intro varId member; exact allNone varId (by simpa [Ty.ftv] using member))]
  | .slot capability target, allNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_none_eq_lift,
        PolyTy.abstract_target_eq_lift_of_none closeTy target
          (by intro varId member; exact allNone varId (by simpa [Ty.ftv] using member))]

theorem PolyTy.abstractTargetList_eq_lift_of_none {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) : ∀ targets : List Ty,
    (∀ varId, varId ∈ Ty.ftvList targets → closeTy varId = none) →
    targets.map
        (PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy) =
      targets.map PolyTy.lift
  | [], _ => rfl
  | head :: tail, allNone => by
      simp only [List.map_cons]
      rw [PolyTy.abstract_target_eq_lift_of_none closeTy head
          (by intro varId member; exact allNone varId (by simp [Ty.ftvList, member])),
        PolyTy.abstractTargetList_eq_lift_of_none closeTy tail
          (by intro varId member; exact allNone varId (by simp [Ty.ftvList, member]))]

end

mutual

theorem PolyTy.abstract_targetOnly_apply {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (targetSubst : TySubst) :
    ∀ target : Ty,
    (∀ varId index, closeTy varId = some index →
      targetSubst varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (targetSubst varId).ftv → closeTy image = none) →
    (PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy target).applyMeta
        { cap := CapSubst.id, target := targetSubst } =
      PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy
        (target.applyTarget targetSubst)
  | .var varId, fixed, avoids => by
      cases closing : closeTy varId with
      | some index =>
          have fixedVar := fixed varId index closing
          simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, closing,
            fixedVar]
      | none =>
          simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, closing]
          symm
          exact PolyTy.abstract_target_eq_lift_of_none closeTy
            (targetSubst varId)
            (by intro image member; exact avoids varId closing image member)
  | .skolem _, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .unit, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .int, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .bool, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .data name children, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget,
        List.map_map]
      congr 1
      exact PolyTy.abstractList_targetOnly_apply closeTy targetSubst children
        fixed avoids
  | .prod components, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget,
        List.map_map]
      congr 1
      exact PolyTy.abstractList_targetOnly_apply closeTy targetSubst components
        fixed avoids
  | .fn domain codomain, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      rw [PolyTy.abstract_targetOnly_apply closeTy targetSubst domain fixed avoids,
        PolyTy.abstract_targetOnly_apply closeTy targetSubst codomain fixed avoids]
  | .matcher capability target, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      rw [PolyCap.abstract_none_eq_lift, PolyCap.applyMeta_lift,
        Cap.apply_id,
        PolyTy.abstract_targetOnly_apply closeTy targetSubst target fixed avoids]
  | .slot capability target, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      rw [PolyCap.abstract_none_eq_lift, PolyCap.applyMeta_lift,
        Cap.apply_id,
        PolyTy.abstract_targetOnly_apply closeTy targetSubst target fixed avoids]

theorem PolyTy.abstractList_targetOnly_apply {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (targetSubst : TySubst) :
    ∀ targets : List Ty,
    (∀ varId index, closeTy varId = some index →
      targetSubst varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (targetSubst varId).ftv → closeTy image = none) →
    (targets.map (PolyTy.abstract
      (fun _ : CapVar => (none : Option (Fin 0))) closeTy)).map
        (PolyTy.applyMeta { cap := CapSubst.id, target := targetSubst }) =
      (Ty.applyTargetList targetSubst targets).map
        (PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy)
  | [], _, _ => rfl
  | head :: tail, fixed, avoids => by
      simp only [List.map_cons, Ty.applyTargetList]
      rw [PolyTy.abstract_targetOnly_apply closeTy targetSubst head fixed avoids,
        PolyTy.abstractList_targetOnly_apply closeTy targetSubst tail fixed avoids]

end


/-- Target-only closing commutes with a structural substitution when closed
variables are fixed and no free-variable image introduces one of them. -/
theorem Scheme.close_nil_applyMeta_targetOnly
    (tyBinders : List TypePM.TyVar) (target : Ty) (targetSubst : TySubst)
    (fixed : ∀ varId, varId ∈ tyBinders →
      targetSubst varId = .var varId)
    (avoids : ∀ varId, varId ∉ tyBinders → ∀ image,
      image ∈ (targetSubst varId).ftv → image ∉ tyBinders) :
    (Scheme.close [] tyBinders target).applyMeta
        { cap := CapSubst.id, target := targetSubst } =
      Scheme.close [] tyBinders (target.applyTarget targetSubst) := by
  unfold Scheme.close Scheme.applyMeta
  congr 1
  apply PolyTy.abstract_targetOnly_apply
  · intro varId index closing
    exact fixed varId (List.finIdxOf?_isSome.mp ⟨index, closing⟩)
  · intro varId closing image member
    apply List.finIdxOf?_eq_none_iff.mpr
    exact avoids varId (List.finIdxOf?_eq_none_iff.mp closing) image member

theorem Scheme.ftv_applyMeta_flatMap (substitution : Subst)
-/
theorem Scheme.ftv_applyMeta_flatMap (substitution : Subst)
    (scheme : Scheme) :
    (scheme.applyMeta substitution).ftv =
      scheme.ftv.flatMap fun varId => (substitution.target varId).ftv := by
  exact PolyTy.ftv_applyMeta_flatMap substitution scheme.body

theorem Context.ftv_applySubst_flatMap (substitution : Subst)
    (context : Context) :
    (context.applySubst substitution).ftv =
      context.ftv.flatMap fun varId => (substitution.target varId).ftv := by
  induction context with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨name, scheme⟩
      change (scheme.applyMeta substitution).ftv ++
          Context.ftv (Context.applySubst substitution rest) =
        (scheme.ftv ++ Context.ftv rest).flatMap fun varId =>
          (substitution.target varId).ftv
      rw [Scheme.ftv_applyMeta_flatMap, induction, List.flatMap_append]

mutual

theorem PolyTy.fcv_applyMeta_targetOnly_eq {capArity tyArity : Nat}
    (T : TySubst) (imagesCapFree : ∀ varId, (T varId).fcv = []) :
    ∀ target : PolyTy capArity tyArity,
    (target.applyMeta { cap := CapSubst.id, target := T }).fcv = target.fcv
  | .mvar varId => by
      simp [PolyTy.applyMeta, PolyTy.fcv, PolyTy.fcv_lift,
        imagesCapFree varId]
  | .bound _ => by simp [PolyTy.applyMeta, PolyTy.fcv]
  | .skolem _ => by simp [PolyTy.applyMeta, PolyTy.fcv]
  | .unit => by simp [PolyTy.applyMeta, PolyTy.fcv]
  | .int => by simp [PolyTy.applyMeta, PolyTy.fcv]
  | .bool => by simp [PolyTy.applyMeta, PolyTy.fcv]
  | .data name children => by
      simp only [PolyTy.applyMeta, PolyTy.fcv]
      exact PolyTy.fcvList_applyMeta_targetOnly_eq T imagesCapFree children
  | .prod components => by
      simp only [PolyTy.applyMeta, PolyTy.fcv]
      exact PolyTy.fcvList_applyMeta_targetOnly_eq T imagesCapFree components
  | .fn domain codomain => by
      simp [PolyTy.applyMeta, PolyTy.fcv,
        PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree domain,
        PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree codomain]
  | .matcher capability target => by
      simp [PolyTy.applyMeta, PolyTy.fcv, PolyCap.applyMeta_id,
        PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree target]
  | .slot capability target => by
      simp [PolyTy.applyMeta, PolyTy.fcv, PolyCap.applyMeta_id,
        PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree target]

theorem PolyTy.fcvList_applyMeta_targetOnly_eq {capArity tyArity : Nat}
    (T : TySubst) (imagesCapFree : ∀ varId, (T varId).fcv = []) :
    ∀ targets : List (PolyTy capArity tyArity),
    PolyTy.fcvList (targets.map
      (PolyTy.applyMeta { cap := CapSubst.id, target := T })) =
      PolyTy.fcvList targets
  | [] => rfl
  | head :: tail => by
      simp [PolyTy.fcvList, PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree,
        PolyTy.fcvList_applyMeta_targetOnly_eq T imagesCapFree tail]

end

theorem Scheme.fcv_applyMeta_targetOnly_eq (T : TySubst)
    (imagesCapFree : ∀ varId, (T varId).fcv = []) (scheme : Scheme) :
    (scheme.applyMeta { cap := CapSubst.id, target := T }).fcv = scheme.fcv :=
  PolyTy.fcv_applyMeta_targetOnly_eq T imagesCapFree scheme.body

theorem Context.fcv_applySubst_targetOnly_eq (T : TySubst)
    (imagesCapFree : ∀ varId, (T varId).fcv = []) (context : Context) :
    (context.applySubst { cap := CapSubst.id, target := T }).fcv = context.fcv := by
  induction context with
  | nil => rfl
  | cons entry tail induction =>
      rcases entry with ⟨name, scheme⟩
      change (scheme.applyMeta { cap := CapSubst.id, target := T }).fcv ++
          Context.fcv (Context.applySubst
            { cap := CapSubst.id, target := T } tail) =
        scheme.fcv ++ Context.fcv tail
      rw [Scheme.fcv_applyMeta_targetOnly_eq T imagesCapFree, induction]

/-- Filtering a flat-mapped list keeps exactly the source items classified
as selected when selected items map to themselves and every unselected image
is rejected by the output classifier. -/
theorem List.filter_flatMap_partition
    {α : Type} [DecidableEq α]
    (items : List α) (image : α → List α)
    (sourceSelected outputSelected : α → Bool)
    (selectedImage : ∀ item, item ∈ items → sourceSelected item = true →
      image item = [item])
    (selectedOutput : ∀ item, item ∈ items → sourceSelected item = true →
      outputSelected item = true)
    (unselectedOutput : ∀ item, item ∈ items → sourceSelected item = false →
      ∀ result, result ∈ image item → outputSelected result = false) :
    (items.flatMap image).filter outputSelected =
      items.filter sourceSelected := by
  induction items with
  | nil => simp
  | cons head tail induction =>
      by_cases selected : sourceSelected head = true
      · have imageEq := selectedImage head (by simp) selected
        have output := selectedOutput head (by simp) selected
        simp only [List.flatMap_cons, List.filter_append, imageEq,
          List.filter_cons, output, selected]
        simp only [if_true, List.filter_nil]
        apply congrArg (head :: ·)
        exact induction
          (fun item member => selectedImage item (by simp [member]))
          (fun item member => selectedOutput item (by simp [member]))
          (fun item member => unselectedOutput item (by simp [member]))
      · have notSelected : sourceSelected head = false := by
          cases equation : sourceSelected head
          · rfl
          · exact (selected equation).elim
        have rejected : (image head).filter outputSelected = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro result member
          intro accepted
          have rejected :=
            unselectedOutput head (by simp) notSelected result member
          rw [rejected] at accepted
          contradiction
        simp only [List.flatMap_cons, List.filter_append, rejected,
          List.nil_append, List.filter_cons, notSelected]
        change List.filter outputSelected (List.flatMap image tail) =
          List.filter sourceSelected tail
        exact induction
          (fun item member => selectedImage item (by simp [member]))
          (fun item member => selectedOutput item (by simp [member]))
          (fun item member => unselectedOutput item (by simp [member]))

/-- Ordinary-variable generalized binders commute exactly with a substitution
which fixes the currently generalized sources.  Environment sources need no
range restriction: every variable in their image also occurs in the
substituted environment, and is therefore filtered out on the right. -/
theorem generalizedTyVars_apply_exact
    (context : Context) (target : Ty) (delta : Subst)
    (fixed : ∀ varId,
      varId ∈ generalizedTyVars context.ftv target →
      delta.target varId = .var varId)
    (environmentAvoids : ∀ {source image : TypePM.TyVar},
      source ∈ context.ftv → image ∈ (delta.target source).ftv →
      image ∉ generalizedTyVars context.ftv target) :
    generalizedTyVars (context.applySubst delta).ftv (delta.apply target) =
      generalizedTyVars context.ftv target := by
  have targetFtv : (delta.apply target).ftv =
      target.ftv.flatMap fun varId => (delta.target varId).ftv := by
    unfold Subst.apply
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability]
  have contextFtv : (context.applySubst delta).ftv =
      context.ftv.flatMap fun varId => (delta.target varId).ftv :=
    Context.ftv_applySubst_flatMap delta context
  unfold generalizedTyVars
  rw [targetFtv, contextFtv]
  congr 1
  apply List.filter_flatMap_partition target.ftv
    (fun varId => (delta.target varId).ftv)
    (fun varId => decide (varId ∉ context.ftv))
    (fun varId => decide
      (varId ∉ context.ftv.flatMap fun source =>
        (delta.target source).ftv))
  · intro varId free outside
    have outsideContext : varId ∉ context.ftv := by
      simpa only [decide_eq_true_eq] using outside
    rw [fixed varId (mem_generalizedTyVars free outsideContext)]
    rfl
  · intro varId free outside
    have outsideContext : varId ∉ context.ftv := by
      simpa only [decide_eq_true_eq] using outside
    have generalized := mem_generalizedTyVars free outsideContext
    have fixedVar := fixed varId generalized
    simp only [decide_eq_true_eq]
    intro inEnvironmentImage
    rcases List.mem_flatMap.mp inEnvironmentImage with
      ⟨source, sourceIn, imageIn⟩
    exact environmentAvoids sourceIn imageIn generalized
  · intro source sourceFree inContext image imageFree
    have sourceIn : source ∈ context.ftv := by
      by_cases member : source ∈ context.ftv
      · exact member
      · have decided : decide (source ∉ context.ftv) = true := by
          simp [member]
        rw [decided] at inContext
        contradiction
    have imageIn : image ∈ context.ftv.flatMap
        (fun candidate => (delta.target candidate).ftv) :=
      List.mem_flatMap.mpr ⟨source, sourceIn, imageFree⟩
    simp [imageIn]

/-! ## Closing commutes with a structural target-only action -/

mutual

theorem PolyCap.abstract_eq_lift_of_none {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) : ∀ capability : Cap,
    (∀ varId, varId ∈ capability.fcv → closeCap varId = none) →
    PolyCap.abstract closeCap capability = PolyCap.lift capability
  | .any, _ => by simp [PolyCap.abstract, PolyCap.lift]
  | .var varId, allNone => by
      have closing := allNone varId (by simp [Cap.fcv])
      simp [PolyCap.abstract, PolyCap.lift, closing]
  | .skolem _, _ => by simp [PolyCap.abstract, PolyCap.lift]
  | .con name children, allNone => by
      simp only [PolyCap.abstract, PolyCap.lift]
      congr 1
      exact PolyCap.abstractList_eq_lift_of_none closeCap children (by
        intro varId member
        exact allNone varId (by simpa [Cap.fcv] using member))
  | .prod components, allNone => by
      simp only [PolyCap.abstract, PolyCap.lift]
      congr 1
      exact PolyCap.abstractList_eq_lift_of_none closeCap components (by
        intro varId member
        exact allNone varId (by simpa [Cap.fcv] using member))

theorem PolyCap.abstractList_eq_lift_of_none {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) : ∀ capabilities : List Cap,
    (∀ varId, varId ∈ Cap.fcvList capabilities → closeCap varId = none) →
    capabilities.map (PolyCap.abstract closeCap) =
      capabilities.map PolyCap.lift
  | [], _ => rfl
  | head :: tail, allNone => by
      simp only [List.map_cons]
      congr 1
      · exact PolyCap.abstract_eq_lift_of_none closeCap head (by
          intro varId member
          exact allNone varId (by simp [Cap.fcvList, member]))
      · exact PolyCap.abstractList_eq_lift_of_none closeCap tail (by
          intro varId member
          exact allNone varId (by simp [Cap.fcvList, member]))

end


mutual

theorem PolyTy.abstract_eq_lift_of_none {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) : ∀ target : Ty,
    (∀ varId, varId ∈ target.fcv → closeCap varId = none) →
    (∀ varId, varId ∈ target.ftv → closeTy varId = none) →
    PolyTy.abstract closeCap closeTy target = PolyTy.lift target
  | .var varId, _, tyNone => by
      have closing := tyNone varId (by simp [Ty.ftv])
      simp [PolyTy.abstract, PolyTy.lift, closing]
  | .skolem _, _, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .unit, _, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .int, _, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .bool, _, _ => by simp [PolyTy.abstract, PolyTy.lift]
  | .data name children, capNone, tyNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact PolyTy.abstractList_eq_lift_of_none closeCap closeTy children
        (by intro varId member; exact capNone varId (by simpa [Ty.fcv] using member))
        (by intro varId member; exact tyNone varId (by simpa [Ty.ftv] using member))
  | .prod components, capNone, tyNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      congr 1
      exact PolyTy.abstractList_eq_lift_of_none closeCap closeTy components
        (by intro varId member; exact capNone varId (by simpa [Ty.fcv] using member))
        (by intro varId member; exact tyNone varId (by simpa [Ty.ftv] using member))
  | .fn domain codomain, capNone, tyNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyTy.abstract_eq_lift_of_none closeCap closeTy domain
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member]))
          (by intro varId member; exact tyNone varId (by simp [Ty.ftv, member])),
        PolyTy.abstract_eq_lift_of_none closeCap closeTy codomain
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member]))
          (by intro varId member; exact tyNone varId (by simp [Ty.ftv, member]))]
  | .matcher capability target, capNone, tyNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_eq_lift_of_none closeCap capability
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member])),
        PolyTy.abstract_eq_lift_of_none closeCap closeTy target
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member]))
          (by intro varId member; exact tyNone varId (by simpa [Ty.ftv] using member))]
  | .slot capability target, capNone, tyNone => by
      simp only [PolyTy.abstract, PolyTy.lift]
      rw [PolyCap.abstract_eq_lift_of_none closeCap capability
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member])),
        PolyTy.abstract_eq_lift_of_none closeCap closeTy target
          (by intro varId member; exact capNone varId (by simp [Ty.fcv, member]))
          (by intro varId member; exact tyNone varId (by simpa [Ty.ftv] using member))]

theorem PolyTy.abstractList_eq_lift_of_none {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) :
    ∀ targets : List Ty,
    (∀ varId, varId ∈ Ty.fcvList targets → closeCap varId = none) →
    (∀ varId, varId ∈ Ty.ftvList targets → closeTy varId = none) →
    targets.map (PolyTy.abstract closeCap closeTy) =
      targets.map PolyTy.lift
  | [], _, _ => rfl
  | head :: tail, capNone, tyNone => by
      simp only [List.map_cons]
      congr 1
      · exact PolyTy.abstract_eq_lift_of_none closeCap closeTy head
          (by intro varId member; exact capNone varId (by simp [Ty.fcvList, member]))
          (by intro varId member; exact tyNone varId (by simp [Ty.ftvList, member]))
      · exact PolyTy.abstractList_eq_lift_of_none closeCap closeTy tail
          (by intro varId member; exact capNone varId (by simp [Ty.fcvList, member]))
          (by intro varId member; exact tyNone varId (by simp [Ty.ftvList, member]))

end

mutual

theorem PolyTy.abstract_targetOnly_apply' {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (T : TySubst) :
    ∀ target : Ty,
    (∀ varId index, closeTy varId = some index → T varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (T varId).ftv → closeTy image = none) →
    (PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy target).applyMeta
        { cap := CapSubst.id, target := T } =
      PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy
        (target.applyTarget T)
  | .var varId, fixed, avoids => by
      cases closing : closeTy varId with
      | some index =>
          simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, closing,
            fixed varId index closing]
      | none =>
          simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, closing]
          symm
          exact PolyTy.abstract_eq_lift_of_none
            (fun _ : CapVar => (none : Option (Fin 0))) closeTy (T varId)
            (by intro _ _; rfl)
            (by intro image member; exact avoids varId closing image member)
  | .skolem _, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .unit, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .int, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .bool, _, _ => by simp [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
  | .data name children, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, List.map_map]
      congr 1
      simpa only [List.map_map, Function.comp_def] using
        (PolyTy.abstractList_targetOnly_apply' closeTy T children fixed avoids)
  | .prod components, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget, List.map_map]
      congr 1
      simpa only [List.map_map, Function.comp_def] using
        (PolyTy.abstractList_targetOnly_apply' closeTy T components fixed avoids)
  | .fn domain codomain, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      rw [PolyTy.abstract_targetOnly_apply' closeTy T domain fixed avoids,
        PolyTy.abstract_targetOnly_apply' closeTy T codomain fixed avoids]
  | .matcher capability target, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      have capFixed : (PolyCap.abstract
          (fun _ : CapVar => (none : Option (Fin 0))) capability).applyMeta
          CapSubst.id = PolyCap.abstract
            (fun _ : CapVar => (none : Option (Fin 0))) capability :=
        PolyCap.applyMeta_id _
      rw [capFixed,
        PolyTy.abstract_targetOnly_apply' closeTy T target fixed avoids]
  | .slot capability target, fixed, avoids => by
      simp only [PolyTy.abstract, PolyTy.applyMeta, Ty.applyTarget]
      have capFixed : (PolyCap.abstract
          (fun _ : CapVar => (none : Option (Fin 0))) capability).applyMeta
          CapSubst.id = PolyCap.abstract
            (fun _ : CapVar => (none : Option (Fin 0))) capability :=
        PolyCap.applyMeta_id _
      rw [capFixed,
        PolyTy.abstract_targetOnly_apply' closeTy T target fixed avoids]

theorem PolyTy.abstractList_targetOnly_apply' {tyArity : Nat}
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) (T : TySubst) :
    ∀ targets : List Ty,
    (∀ varId index, closeTy varId = some index → T varId = .var varId) →
    (∀ varId, closeTy varId = none → ∀ image,
      image ∈ (T varId).ftv → closeTy image = none) →
    (targets.map (PolyTy.abstract
      (fun _ : CapVar => (none : Option (Fin 0))) closeTy)).map
        (PolyTy.applyMeta { cap := CapSubst.id, target := T }) =
      (Ty.applyTargetList T targets).map
        (PolyTy.abstract (fun _ : CapVar => (none : Option (Fin 0))) closeTy)
  | [], _, _ => rfl
  | head :: tail, fixed, avoids => by
      simp only [List.map_cons, Ty.applyTargetList]
      rw [PolyTy.abstract_targetOnly_apply' closeTy T head fixed avoids,
        PolyTy.abstractList_targetOnly_apply' closeTy T tail fixed avoids]

end

/-- Target-only closing commutes with a structural substitution when closed
variables are fixed and no free-variable image introduces one of them. -/
theorem Scheme.close_nil_applyMeta_targetOnly'
    (tyBinders : List TypePM.TyVar) (target : Ty) (T : TySubst)
    (fixed : ∀ varId, varId ∈ tyBinders → T varId = .var varId)
    (avoids : ∀ varId, varId ∉ tyBinders → ∀ image,
      image ∈ (T varId).ftv → image ∉ tyBinders) :
    (Scheme.close [] tyBinders target).applyMeta
        { cap := CapSubst.id, target := T } =
      Scheme.close [] tyBinders (target.applyTarget T) := by
  unfold Scheme.close Scheme.applyMeta
  congr 1
  apply PolyTy.abstract_targetOnly_apply'
  · intro varId index closing
    apply fixed varId
    exact Classical.byContradiction (fun outside => by
      have noneEq := List.finIdxOf?_eq_none_iff.mpr outside
      rw [noneEq] at closing
      contradiction)
  · intro varId closing image member
    apply List.finIdxOf?_eq_none_iff.mpr
    exact avoids varId (List.finIdxOf?_eq_none_iff.mp closing) image member

/-- Non-oracle target-only naturality of canonical generalization. -/
theorem FrozenSig.generalize_targetOnly_apply_exact
    (signature : FrozenSig) (context : Context) (target : Ty) (T : TySubst)
    (signatureCaps : signature.fcv = [])
    (signatureTargets : signature.ftv = [])
    (contextCaps : context.fcv = [])
    (targetCaps : target.fcv = [])
    (appliedContextCaps :
      (context.applySubst { cap := CapSubst.id, target := T }).fcv = [])
    (appliedTargetCaps :
      (({ cap := CapSubst.id, target := T } : Subst).apply target).fcv = [])
    (fixed : ∀ varId,
      varId ∈ generalizedTyVars context.ftv target → T varId = .var varId)
    (environmentAvoids : ∀ {source image : TypePM.TyVar},
      source ∈ context.ftv → image ∈ (T source).ftv →
      image ∉ generalizedTyVars context.ftv target)
    (allFreeAvoid : ∀ {source image : TypePM.TyVar},
      source ∉ generalizedTyVars context.ftv target →
      image ∈ (T source).ftv →
      image ∉ generalizedTyVars context.ftv target) :
    (signature.generalize context target).applyMeta
        { cap := CapSubst.id, target := T } =
      signature.generalize
        (context.applySubst { cap := CapSubst.id, target := T })
        (({ cap := CapSubst.id, target := T } : Subst).apply target) := by
  let delta : Subst := { cap := CapSubst.id, target := T }
  have appliedTarget : delta.apply target = target.applyTarget T := by
    unfold delta Subst.apply
    rw [Ty.applyCapability_id]
  have binderEq := generalizedTyVars_apply_exact context target delta
    fixed environmentAvoids
  unfold FrozenSig.generalize Scheme.generalize
  rw [signatureCaps, signatureTargets, contextCaps, appliedContextCaps]
  simp only [List.nil_append]
  have leftCaps : generalizedCapVars [] target = [] := by
    unfold generalizedCapVars
    rw [targetCaps]
    rfl
  have rightCaps : generalizedCapVars []
      (({ cap := CapSubst.id, target := T } : Subst).apply target) = [] := by
    unfold generalizedCapVars
    rw [appliedTargetCaps]
    rfl
  rw [leftCaps, rightCaps]
  change (Scheme.close [] (generalizedTyVars context.ftv target) target).applyMeta
      { cap := CapSubst.id, target := T } =
    Scheme.close []
      (generalizedTyVars (context.applySubst delta).ftv (delta.apply target))
      (delta.apply target)
  rw [binderEq, appliedTarget]
  exact Scheme.close_nil_applyMeta_targetOnly'
    (generalizedTyVars context.ftv target) target T fixed
    (fun varId outside image imageFree => allFreeAvoid outside imageFree)

/-- The source data retained for one already-traversed `let` boundary. -/
structure PendingLetCut where
  context : Context
  target : Ty
  valueSubst : Subst

/-- The generalized scheme created when the value traversal finished. -/
def PendingLetCut.localScheme (signature : FrozenSig)
    (cut : PendingLetCut) : Scheme :=
  signature.generalize (cut.context.applySubst cut.valueSubst)
    (cut.valueSubst.apply cut.target)

/-- Exact public terminal-audit equation for one pending `let`. -/
def PendingLetCut.StableAt (signature : FrozenSig)
    (terminal : Subst) (cut : PendingLetCut) : Prop :=
  (cut.localScheme signature).applyMeta terminal =
    signature.generalize (cut.context.applySubst terminal)
      (terminal.apply cut.target)

/-- The extra property required of a later solver step.  This is deliberately
an equality of generalized schemes, rather than only a type equation or a
residual-realization statement: those weaker facts do not preserve the
public terminal audit. -/
def LetGeneralizationStepSafe (signature : FrozenSig)
    (current delta : Subst) (cut : PendingLetCut) : Prop :=
  (signature.generalize (cut.context.applySubst current)
      (current.apply cut.target)).applyMeta delta =
    signature.generalize
      (cut.context.applySubst (Subst.seq delta current))
      ((Subst.seq delta current).apply cut.target)

/-- All earlier let cuts are stable at the displayed prevailing
substitution. -/
def PendingLetStability (signature : FrozenSig) (terminal : Subst)
    (pending : List PendingLetCut) : Prop :=
  ∀ cut ∈ pending, cut.StableAt signature terminal

/-- One solver step is safe for every pending generalization boundary. -/
def PendingLetStepsSafe (signature : FrozenSig) (current delta : Subst)
    (pending : List PendingLetCut) : Prop :=
  ∀ cut ∈ pending, LetGeneralizationStepSafe signature current delta cut

/-! ## What exact-solver support and range do provide -/

/-- The variables closed by re-generalization at the current cut are absent
from the ordinary exact constraint.  Exact MGU support/range confinement then
proves that the delta neither rewrites those variables nor introduces them
through an image of a constraint variable.

Together with a closed signature and capability-inert normalized cut data,
this separation lets exact support/range facts identify the freshly computed
ordered binder lists and derive `LetGeneralizationStepSafe`. -/
structure LetCutConstraintSeparated (signature : FrozenSig)
    (current : Subst) (cut : PendingLetCut) (left right : Ty) : Prop where
  caps : ∀ varId,
    varId ∈ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ left.fcv ++ right.fcv
  targets : ∀ varId,
    varId ∈ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ left.ftv ++ right.ftv

theorem OriginSafeExactPairedMGU.cap_fixed_of_letSeparated
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    {varId : CapVar}
    (generalized : varId ∈ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target)) :
    delta.cap varId = .var varId :=
  exact.exact.2.1 varId (separated.caps varId generalized)

theorem OriginSafeExactPairedMGU.target_fixed_of_letSeparated
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    {varId : TypePM.TyVar}
    (generalized : varId ∈ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target)) :
    delta.target varId = .var varId :=
  exact.exact.2.2.1 varId (separated.targets varId generalized)

/-- Exact capability ranges cannot introduce a separated generalized
capability variable. -/
theorem OriginSafeExactPairedMGU.cap_range_avoids_letGeneralized
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    {source image : CapVar} (sourceIn : source ∈ left.fcv ++ right.fcv)
    (imageIn : image ∈ (delta.cap source).fcv) :
    image ∉ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) := by
  intro generalized
  exact separated.caps image generalized
    (exact.exact.2.2.2.1 source sourceIn image imageIn)

/-- Exact target ranges cannot introduce a separated generalized target
variable. -/
theorem OriginSafeExactPairedMGU.target_range_avoids_letGeneralized
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    {source image : TypePM.TyVar}
    (sourceIn : source ∈ left.ftv ++ right.ftv)
    (imageIn : image ∈ (delta.target source).ftv) :
    image ∉ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target) := by
  intro generalized
  exact separated.targets image generalized
    (exact.exact.2.2.2.2.1 source sourceIn image imageIn)

/-- Capability leaves occurring inside target-substitution images obey the
same separation boundary. -/
theorem OriginSafeExactPairedMGU.target_cap_range_avoids_letGeneralized
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    {source : TypePM.TyVar} {image : CapVar}
    (sourceIn : source ∈ left.ftv ++ right.ftv)
    (imageIn : image ∈ (delta.target source).fcv) :
    image ∉ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) := by
  intro generalized
  exact separated.caps image generalized
    (exact.exact.2.2.2.2.2.1 source sourceIn image imageIn)

/-- If an exact paired constraint contains no capability variables, its
capability component is extensionally the identity. -/
theorem OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    delta.cap = CapSubst.id := by
  funext varId
  exact exact.exact.2.1 varId (by simp [leftCapFree, rightCapFree])

/-- If an exact paired constraint contains no capability variables, no
target-substitution image contains one either.  Sources outside the target
support are fixed; sources inside it use exact cap-range confinement. -/
theorem OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree
    {left right : Ty} {delta : Subst}
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    ∀ source, (delta.target source).fcv = [] := by
  intro source
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro image imageIn
  by_cases sourceIn : source ∈ left.ftv ++ right.ftv
  · have imageConstraint :=
      exact.exact.2.2.2.2.2.1 source sourceIn image imageIn
    rw [leftCapFree, rightCapFree] at imageConstraint
    exact List.not_mem_nil imageConstraint
  · have fixed := exact.exact.2.2.1 source sourceIn
    rw [fixed] at imageIn
    exact List.not_mem_nil (by simpa only [Ty.fcv] using imageIn)

/-- Applying a target substitution whose images are capability-free preserves
capability-freeness of a monotype. -/
theorem Ty.fcv_applyTarget_eq_nil_of_capFree
    (target : Ty) (T : TySubst)
    (targetCapFree : target.fcv = [])
    (imagesCapFree : ∀ source, (T source).fcv = []) :
    (target.applyTarget T).fcv = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro image imageIn
  rcases Unification.Ty.mem_fcv_applyTarget target T image imageIn with
    original | introduced
  · rw [targetCapFree] at original
    exact List.not_mem_nil original
  · rcases introduced with ⟨source, _sourceIn, imageInSource⟩
    rw [imagesCapFree source] at imageInSource
    exact List.not_mem_nil imageInSource

/-- The exact solver certificate entails stability of one pending let cut in
the capability-inert Damas--Milner fragment.  No generalization equation is
assumed: fixed generalized sources and both required avoidance conditions are
derived by splitting on membership in the exact constraint support. -/
theorem OriginSafeExactPairedMGU.letGeneralizationStepSafe_targetOnly
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (signatureClosed : signature.SchemesClosed)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (contextCapFree : (cut.context.applySubst current).fcv = [])
    (targetCapFree : (current.apply cut.target).fcv = []) :
    LetGeneralizationStepSafe signature current delta cut := by
  let context := cut.context.applySubst current
  let target := current.apply cut.target
  have capEq : delta.cap = CapSubst.id :=
    TypePM.DM.OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
      exact leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    TypePM.DM.OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
        leftCapFree rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  have generalizedEq :
      signature.generalizedTyVars context target =
        generalizedTyVars context.ftv target := by
    simp [FrozenSig.generalizedTyVars, signatureClosed.signatureTargets]
  have fixed : ∀ varId,
      varId ∈ generalizedTyVars context.ftv target →
      delta.target varId = .var varId := by
    intro varId generalized
    apply TypePM.DM.OriginSafeExactPairedMGU.target_fixed_of_letSeparated
      exact separated
    change varId ∈ signature.generalizedTyVars context target
    rw [generalizedEq]
    exact generalized
  have environmentAvoids : ∀ {source image : TypePM.TyVar},
      source ∈ context.ftv → image ∈ (delta.target source).ftv →
      image ∉ generalizedTyVars context.ftv target := by
    intro source image sourceIn imageIn generalizedImage
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · apply separated.targets image
        (show image ∈ signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target) by
          change image ∈ signature.generalizedTyVars context target
          rw [generalizedEq]
          exact generalizedImage)
      exact exact.exact.2.2.2.2.1 source sourceConstraint image imageIn
    · have sourceFixed := exact.exact.2.2.1 source sourceConstraint
      rw [sourceFixed] at imageIn
      have imageEq : image = source := by simpa [Ty.ftv] using imageIn
      subst image
      exact (mem_generalizedTyVars_not_env generalizedImage) sourceIn
  have allFreeAvoid : ∀ {source image : TypePM.TyVar},
      source ∉ generalizedTyVars context.ftv target →
      image ∈ (delta.target source).ftv →
      image ∉ generalizedTyVars context.ftv target := by
    intro source image sourceOutside imageIn generalizedImage
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · apply separated.targets image
        (show image ∈ signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target) by
          change image ∈ signature.generalizedTyVars context target
          rw [generalizedEq]
          exact generalizedImage)
      exact exact.exact.2.2.2.2.1 source sourceConstraint image imageIn
    · have sourceFixed := exact.exact.2.2.1 source sourceConstraint
      rw [sourceFixed] at imageIn
      have imageEq : image = source := by simpa [Ty.ftv] using imageIn
      subst image
      exact sourceOutside generalizedImage
  have appliedContextCapFree :
      (context.applySubst
        { cap := CapSubst.id, target := delta.target }).fcv = [] := by
    rw [Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree,
      contextCapFree]
  have appliedTargetCapFree :
      (({ cap := CapSubst.id, target := delta.target } : Subst).apply
        target).fcv = [] := by
    unfold Subst.apply
    rw [Ty.applyCapability_id]
    exact Ty.fcv_applyTarget_eq_nil_of_capFree target delta.target
      targetCapFree imagesCapFree
  unfold LetGeneralizationStepSafe
  rw [Context.applySubst_seq, Subst.seq_apply]
  change (signature.generalize context target).applyMeta delta =
    signature.generalize (context.applySubst delta) (delta.apply target)
  rw [deltaEq]
  exact FrozenSig.generalize_targetOnly_apply_exact signature context target
    delta.target signatureClosed.signatureCaps
    signatureClosed.signatureTargets contextCapFree targetCapFree
    appliedContextCapFree appliedTargetCapFree fixed environmentAvoids
    allFreeAvoid

/-- Pointwise exact-solver construction for every pending let cut. -/
theorem OriginSafeExactPairedMGU.pendingLetStepsSafe_targetOnly
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {left right : Ty} {delta : Subst}
    (signatureClosed : signature.SchemesClosed)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : ∀ cut ∈ pending,
      LetCutConstraintSeparated signature current cut left right)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (contextsCapFree : ∀ cut ∈ pending,
      (cut.context.applySubst current).fcv = [])
    (targetsCapFree : ∀ cut ∈ pending,
      (current.apply cut.target).fcv = []) :
    PendingLetStepsSafe signature current delta pending := by
  intro cut member
  exact TypePM.DM.OriginSafeExactPairedMGU.letGeneralizationStepSafe_targetOnly
      signatureClosed exact
      (separated cut member) leftCapFree rightCapFree
      (contextsCapFree cut member) (targetsCapFree cut member)

/-- Exact target support/range preserves the ordered list of generalized
target variables at one pending cut. -/
theorem OriginSafeExactPairedMGU.letGeneralizedTyVars_eq_targetOnly
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (signatureClosed : signature.SchemesClosed)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right) :
    signature.generalizedTyVars
        (cut.context.applySubst (Subst.seq delta current))
        ((Subst.seq delta current).apply cut.target) =
      signature.generalizedTyVars
        (cut.context.applySubst current) (current.apply cut.target) := by
  let context := cut.context.applySubst current
  let target := current.apply cut.target
  have generalizedEq :
      signature.generalizedTyVars context target =
        generalizedTyVars context.ftv target := by
    simp [FrozenSig.generalizedTyVars, signatureClosed.signatureTargets]
  have fixed : ∀ varId,
      varId ∈ generalizedTyVars context.ftv target →
      delta.target varId = .var varId := by
    intro varId generalized
    apply TypePM.DM.OriginSafeExactPairedMGU.target_fixed_of_letSeparated
      exact separated
    change varId ∈ signature.generalizedTyVars context target
    rw [generalizedEq]
    exact generalized
  have environmentAvoids : ∀ {source image : TypePM.TyVar},
      source ∈ context.ftv → image ∈ (delta.target source).ftv →
      image ∉ generalizedTyVars context.ftv target := by
    intro source image sourceIn imageIn generalizedImage
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · apply separated.targets image
        (show image ∈ signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target) by
          change image ∈ signature.generalizedTyVars context target
          rw [generalizedEq]
          exact generalizedImage)
      exact exact.exact.2.2.2.2.1 source sourceConstraint image imageIn
    · have sourceFixed := exact.exact.2.2.1 source sourceConstraint
      rw [sourceFixed] at imageIn
      have imageEq : image = source := by simpa [Ty.ftv] using imageIn
      subst image
      exact (mem_generalizedTyVars_not_env generalizedImage) sourceIn
  rw [Context.applySubst_seq, Subst.seq_apply]
  change signature.generalizedTyVars (context.applySubst delta)
      (delta.apply target) = signature.generalizedTyVars context target
  unfold FrozenSig.generalizedTyVars
  rw [signatureClosed.signatureTargets]
  simp only [List.nil_append]
  exact generalizedTyVars_apply_exact context target delta fixed
    environmentAvoids

/-- In the capability-inert fragment both generalized capability lists are
empty, hence are preserved exactly by the exact target-only cut. -/
theorem OriginSafeExactPairedMGU.letGeneralizedCapVars_eq_targetOnly
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right : Ty} {delta : Subst}
    (signatureClosed : signature.SchemesClosed)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (contextCapFree : (cut.context.applySubst current).fcv = [])
    (targetCapFree : (current.apply cut.target).fcv = []) :
    signature.generalizedCapVars
        (cut.context.applySubst (Subst.seq delta current))
        ((Subst.seq delta current).apply cut.target) =
      signature.generalizedCapVars
        (cut.context.applySubst current) (current.apply cut.target) := by
  let context := cut.context.applySubst current
  let target := current.apply cut.target
  have capEq : delta.cap = CapSubst.id :=
    TypePM.DM.OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
      exact leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    TypePM.DM.OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree
      exact leftCapFree rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  rw [Context.applySubst_seq, Subst.seq_apply]
  change signature.generalizedCapVars (context.applySubst delta)
      (delta.apply target) = signature.generalizedCapVars context target
  rw [deltaEq]
  unfold FrozenSig.generalizedCapVars
  rw [signatureClosed.signatureCaps,
    Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree]
  simp only [List.nil_append]
  unfold generalizedCapVars
  rw [contextCapFree, targetCapFree]
  have appliedTargetCapFree :
      (({ cap := CapSubst.id, target := delta.target } : Subst).apply
        target).fcv = [] := by
    unfold Subst.apply
    rw [Ty.applyCapability_id]
    exact Ty.fcv_applyTarget_eq_nil_of_capFree target delta.target
      targetCapFree imagesCapFree
  rw [appliedTargetCapFree]

/-- Solver certificate needed by W when pending let cuts exist.  All fields
are ordinary exactness/freshness or capability-inertness facts; the scheme
generalization equations are derived, not stored as an oracle. -/
structure LetStableExactPairedCut (signature : FrozenSig)
    (current : Subst) (pending : List PendingLetCut)
    (left right : Ty) (delta : Subst) : Prop where
  exact : OriginSafeExactPairedMGU [] left right delta
  leftCapFree : left.fcv = []
  rightCapFree : right.fcv = []
  separated : ∀ cut ∈ pending,
    LetCutConstraintSeparated signature current cut left right
  contextsCapFree : ∀ cut ∈ pending,
    (cut.context.applySubst current).fcv = []
  targetsCapFree : ∀ cut ∈ pending,
    (current.apply cut.target).fcv = []

/-- Exact support/range confinement constructs the pending generalization
stability payload exposed by the strengthened cut certificate. -/
theorem LetStableExactPairedCut.generalizations
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {left right : Ty} {delta : Subst}
    (cut : LetStableExactPairedCut signature current pending left right delta)
    (signatureClosed : signature.SchemesClosed) :
    PendingLetStepsSafe signature current delta pending :=
  TypePM.DM.OriginSafeExactPairedMGU.pendingLetStepsSafe_targetOnly
    signatureClosed cut.exact cut.separated cut.leftCapFree cut.rightCapFree
    cut.contextsCapFree cut.targetsCapFree

/-- Ordered target-binder preservation projected directly from a stable exact
cut certificate. -/
theorem LetStableExactPairedCut.generalizedTyVars
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {left right : Ty} {delta : Subst}
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta)
    (signatureClosed : signature.SchemesClosed) {cut : PendingLetCut}
    (member : cut ∈ pending) :
    signature.generalizedTyVars
        (cut.context.applySubst (Subst.seq delta current))
        ((Subst.seq delta current).apply cut.target) =
      signature.generalizedTyVars
        (cut.context.applySubst current) (current.apply cut.target) :=
  TypePM.DM.OriginSafeExactPairedMGU.letGeneralizedTyVars_eq_targetOnly
    signatureClosed solverCut.exact (solverCut.separated cut member)

/-- Ordered capability-binder preservation projected directly from a stable
exact cut certificate. -/
theorem LetStableExactPairedCut.generalizedCapVars
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {left right : Ty} {delta : Subst}
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta)
    (signatureClosed : signature.SchemesClosed) {cut : PendingLetCut}
    (member : cut ∈ pending) :
    signature.generalizedCapVars
        (cut.context.applySubst (Subst.seq delta current))
        ((Subst.seq delta current).apply cut.target) =
      signature.generalizedCapVars
        (cut.context.applySubst current) (current.apply cut.target) :=
  TypePM.DM.OriginSafeExactPairedMGU.letGeneralizedCapVars_eq_targetOnly
    signatureClosed solverCut.exact solverCut.leftCapFree
    solverCut.rightCapFree (solverCut.contextsCapFree cut member)
    (solverCut.targetsCapFree cut member)

/-- At the cut itself, idempotence gives the initial stability equation. -/
theorem PendingLetCut.stableAt_valueSubst
    {signature : FrozenSig} {cut : PendingLetCut}
    (idempotent : cut.valueSubst.Idempotent) :
    cut.StableAt signature cut.valueSubst := by
  exact FrozenSig.generalize_image_fixed signature cut.context cut.target
    cut.valueSubst idempotent

/-- A commuting solver step advances one exact terminal-audit equation. -/
theorem PendingLetCut.StableAt.seq
    {signature : FrozenSig} {current delta : Subst} {cut : PendingLetCut}
    (stable : cut.StableAt signature current)
    (stepSafe : LetGeneralizationStepSafe signature current delta cut) :
    cut.StableAt signature (Subst.seq delta current) := by
  unfold PendingLetCut.StableAt at stable ⊢
  unfold LetGeneralizationStepSafe at stepSafe
  rw [Scheme.applyMeta_seq, stable]
  exact stepSafe

/-- Pointwise lifting of `PendingLetCut.StableAt.seq`. -/
theorem PendingLetStability.seq
    {signature : FrozenSig} {current delta : Subst}
    {pending : List PendingLetCut}
    (stable : PendingLetStability signature current pending)
    (stepSafe : PendingLetStepsSafe signature current delta pending) :
    PendingLetStability signature (Subst.seq delta current) pending := by
  intro cut member
  exact PendingLetCut.StableAt.seq (stable cut member)
    (stepSafe cut member)

/-- Register the current let cut.  Older cuts remain unchanged. -/
theorem PendingLetStability.consCurrent
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {cut : PendingLetCut}
    (older : PendingLetStability signature current pending)
    (atCut : cut.StableAt signature current) :
    PendingLetStability signature current (cut :: pending) := by
  intro candidate member
  rcases List.mem_cons.mp member with equality | olderMember
  · cases equality
    exact atCut
  · exact older candidate olderMember

/-- Convenient registration API when the retained substitution is the
current idempotent W state. -/
theorem PendingLetStability.consValueCut
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {context : Context} {target : Ty}
    (older : PendingLetStability signature current pending)
    (idempotent : current.Idempotent) :
    PendingLetStability signature current
      (⟨context, target, current⟩ :: pending) := by
  exact older.consCurrent
    (PendingLetCut.stableAt_valueSubst idempotent)

/-- Extract exactly the `LetFacts` payload consumed by the recursive public
terminal audit. -/
theorem PendingLetStability.letFacts
    {signature : FrozenSig} {terminal : Subst}
    {pending : List PendingLetCut} {cut : PendingLetCut}
    (stable : PendingLetStability signature terminal pending)
    (member : cut ∈ pending) :
    DDTerminalAudit.LetFacts terminal signature cut.context cut.target
      cut.valueSubst := by
  exact ⟨stable cut member⟩

/-! ## Coupling with the protected W frame -/

/-- Protected W equations together with all exact pending let equations. -/
structure WLetStableFrameAt (signature : FrozenSig)
    (supply : InferenceBase.FreshSupply) (post prevailing : Subst)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Prop where
  frame : WProtectedFrameAt supply post prevailing frames frontier
  lets : PendingLetStability signature prevailing pending

/-- Canonical variable opening extends only `post`; the prevailing state and
every terminal-stability equation are literally unchanged. -/
theorem WLetStableFrameAt.extendSchemeOpening
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {base prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {scheme : Scheme}
    (stable : WLetStableFrameAt signature supply base prevailing frames
      frontier pending)
    (opening : (scheme.applyMeta base).ValueOpening) :
    WLetStableFrameAt signature supply
      (DM.extendSchemeOpening base supply scheme opening) prevailing
      frames frontier pending :=
  ⟨stable.frame.extendSchemeOpening opening, stable.lets⟩

/-- Ordinary exact solver transport.  MGU exactness transports the W frame;
the generic form accepts an already-derived pending-step certificate.  The
exact target-only API below constructs it from solver support/range facts. -/
theorem WLetStableFrameAt.applyOrdinaryCut
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    (stable : WLetStableFrameAt signature supply post prevailing frames
      frontier pending)
    (factor : post = Subst.seq residual delta)
    (deltaBounded : delta.BoundedBy supply)
    (stepSafe : PendingLetStepsSafe signature prevailing delta pending) :
    WLetStableFrameAt signature supply residual
      (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending :=
  ⟨stable.frame.applySubst factor deltaBounded,
    stable.lets.seq stepSafe⟩

/-- Specialized spelling for the low-level executable ordinary exact cut.
Higher-level callers should use `applyLetStableExactPairedCut`, which derives
the generalization-preservation certificate. -/
theorem WLetStableFrameAt.applyOriginSafeExactPairedMGU
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {left right : Ty}
    (stable : WLetStableFrameAt signature supply post prevailing frames
      frontier pending)
    (cut : OriginSafeExactPairedMGU [] left right delta)
    (leftBounded : left.BoundedBy supply)
    (rightBounded : right.BoundedBy supply)
    (factor : post = Subst.seq residual delta)
    (stepSafe : PendingLetStepsSafe signature prevailing delta pending) :
    WLetStableFrameAt signature supply residual
      (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  exact stable.applyOrdinaryCut factor
    (cut.exact.boundedBy leftBounded rightBounded) stepSafe

/-- One-step transport using the strengthened solver certificate as a single
argument. -/
theorem WLetStableFrameAt.applyLetStableExactPairedCut
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {left right : Ty}
    (stable : WLetStableFrameAt signature supply post prevailing frames
      frontier pending)
    (cut : LetStableExactPairedCut signature prevailing pending left right
      delta)
    (signatureClosed : signature.SchemesClosed)
    (leftBounded : left.BoundedBy supply)
    (rightBounded : right.BoundedBy supply)
    (factor : post = Subst.seq residual delta) :
    WLetStableFrameAt signature supply residual
      (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending :=
  stable.applyOriginSafeExactPairedMGU cut.exact leftBounded rightBounded
    factor (cut.generalizations signatureClosed)

/-- Add a just-finished let cut to the coupled frame. -/
theorem WLetStableFrameAt.registerLet
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {context : Context} {target : Ty}
    (stable : WLetStableFrameAt signature supply post prevailing frames
      frontier pending)
    (idempotent : prevailing.Idempotent) :
    WLetStableFrameAt signature supply post prevailing frames frontier
      (⟨context, target, prevailing⟩ :: pending) :=
  ⟨stable.frame, stable.lets.consValueCut idempotent⟩

/-- Final extraction API at the root terminal. -/
theorem WLetStableFrameAt.letFacts
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post terminal : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {cut : PendingLetCut}
    (stable : WLetStableFrameAt signature supply post terminal frames
      frontier pending)
    (member : cut ∈ pending) :
    DDTerminalAudit.LetFacts terminal signature cut.context cut.target
      cut.valueSubst :=
  stable.lets.letFacts member

end DM
end TypePM
