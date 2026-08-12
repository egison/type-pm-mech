import TypePM.DemandTypingInferenceCompletenessGeneralizationEquivariance

namespace TypePM
namespace DemandTypingInferenceCompletenessGeneralizationEquivariance

open DemandTypingInferenceCompletenessLocalRenaming

/-- Closing commutes with a scoped renaming. -/
theorem Scheme.close_forward
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (target : Ty)
    (caps : ∀ varId, varId ∈ target.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ target.ftv → varId ∈ targetScope)
    (capBindersFree : ∀ varId, varId ∈ capBinders → varId ∈ target.fcv)
    (tyBindersFree : ∀ varId, varId ∈ tyBinders → varId ∈ target.ftv) :
    Scheme.close (capBinders.map certificate.capImage)
        (tyBinders.map certificate.targetImage) (forward.apply target) =
      (Scheme.close capBinders tyBinders target).applyMeta forward := by
  have targetPure :=
    DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
      certificate target caps targets
  have schemeActionsAgree :
      (Scheme.close capBinders tyBinders target).applyMeta forward =
        (Scheme.close capBinders tyBinders target).applyMeta
          (TypePM.DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
            certificate) := by
    apply Scheme.applyMeta_eq_of_free_agree
    · intro varId free
      have sourceFree :=
        (PolyTy.abstract_free_subset
          (fun candidate => capBinders.finIdxOf? candidate)
          (fun candidate => tyBinders.finIdxOf? candidate) target).1
          varId free
      exact certificate.cap_forward (caps varId sourceFree)
    · intro varId free
      have sourceFree :=
        (PolyTy.abstract_free_subset
          (fun candidate => capBinders.finIdxOf? candidate)
          (fun candidate => tyBinders.finIdxOf? candidate) target).2
          varId free
      exact certificate.target_forward (targets varId sourceFree)
  rw [targetPure, schemeActionsAgree]
  unfold Scheme.close Scheme.applyMeta
  congr 1
  · exact List.length_map _
  · exact List.length_map _
  apply PolyTy.abstract_renaming_heq certificate.capImage certificate.targetImage
    (List.length_map _) (List.length_map _)
  · intro varId free
    have equation :=
      List.finIdxOf?_map_of_injectiveOn certificate.capImage varId capBinders
        (fun item itemMem equal => certificate.capImage_injectiveOn
          (caps item (capBindersFree item itemMem)) (caps varId free) equal)
    exact (heq_of_eq equation).trans
      (Option.map_finCast_heq (List.length_map certificate.capImage).symm
        (capBinders.finIdxOf? varId))
  · intro varId free
    have equation :=
      List.finIdxOf?_map_of_injectiveOn certificate.targetImage varId tyBinders
        (fun item itemMem equal => certificate.targetImage_injectiveOn
          (targets item (tyBindersFree item itemMem))
          (targets varId free) equal)
    exact (heq_of_eq equation).trans
      (Option.map_finCast_heq (List.length_map certificate.targetImage).symm
        (tyBinders.finIdxOf? varId))

theorem generalizedCapVars_forward
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (leftEnv rightEnv : List CapVar) (target : Ty)
    (caps : ∀ varId, varId ∈ target.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ target.ftv → varId ∈ targetScope)
    (environment : ∀ varId, varId ∈ target.fcv →
      (certificate.capImage varId ∈ leftEnv ↔ varId ∈ rightEnv)) :
    generalizedCapVars leftEnv (forward.apply target) =
      (generalizedCapVars rightEnv target).map certificate.capImage := by
  have targetPure :=
    DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
      certificate target caps targets
  have freeVars : (forward.apply target).fcv =
      target.fcv.map certificate.capImage := by
    rw [targetPure,
      TypePM.DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv]
  unfold generalizedCapVars
  rw [freeVars]
  rw [List.filter_map_of_iff certificate.capImage
    (fun varId => varId ∉ leftEnv) (fun varId => varId ∉ rightEnv)
    target.fcv]
  · apply List.uniqueVars_map_of_injectiveOn
    intro left right leftMem rightMem equal
    exact certificate.capImage_injectiveOn
      (caps left (List.mem_filter.mp leftMem).1)
      (caps right (List.mem_filter.mp rightMem).1) equal
  · intro varId free
    have environmentIff : certificate.capImage varId ∈ leftEnv ↔
        varId ∈ rightEnv := by
      exact @environment varId free
    change decide (¬certificate.capImage varId ∈ leftEnv) =
      decide (¬varId ∈ rightEnv)
    simpa only [decide_eq_decide] using not_congr environmentIff

theorem generalizedTyVars_forward
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (leftEnv rightEnv : List TypePM.TyVar) (target : Ty)
    (caps : ∀ varId, varId ∈ target.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ target.ftv → varId ∈ targetScope)
    (environment : ∀ varId, varId ∈ target.ftv →
      (certificate.targetImage varId ∈ leftEnv ↔ varId ∈ rightEnv)) :
    generalizedTyVars leftEnv (forward.apply target) =
      (generalizedTyVars rightEnv target).map certificate.targetImage := by
  have targetPure :=
    DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
      certificate target caps targets
  have freeVars : (forward.apply target).ftv =
      target.ftv.map certificate.targetImage := by
    rw [targetPure,
      TypePM.DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_ftv]
  unfold generalizedTyVars
  rw [freeVars]
  rw [List.filter_map_of_iff certificate.targetImage
    (fun varId => varId ∉ leftEnv) (fun varId => varId ∉ rightEnv)
    target.ftv]
  · apply List.uniqueVars_map_of_injectiveOn
    intro left right leftMem rightMem equal
    exact certificate.targetImage_injectiveOn
      (targets left (List.mem_filter.mp leftMem).1)
      (targets right (List.mem_filter.mp rightMem).1) equal
  · intro varId free
    have environmentIff : certificate.targetImage varId ∈ leftEnv ↔
        varId ∈ rightEnv := by
      exact @environment varId free
    change decide (¬certificate.targetImage varId ∈ leftEnv) =
      decide (¬varId ∈ rightEnv)
    simpa only [decide_eq_decide] using not_congr environmentIff

/-- Canonical generalization is equivariant under a scoped two-sort
renaming. -/
theorem Scheme.generalize_forward
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    (leftCaps rightCaps : List CapVar)
    (leftTargets rightTargets : List TypePM.TyVar) (target : Ty)
    (caps : ∀ varId, varId ∈ target.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ target.ftv → varId ∈ targetScope)
    (capEnvironment : ∀ varId, varId ∈ target.fcv →
      (certificate.capImage varId ∈ leftCaps ↔ varId ∈ rightCaps))
    (targetEnvironment : ∀ varId, varId ∈ target.ftv →
      (certificate.targetImage varId ∈ leftTargets ↔ varId ∈ rightTargets)) :
    Scheme.generalize leftCaps leftTargets (forward.apply target) =
      (Scheme.generalize rightCaps rightTargets target).applyMeta forward := by
  unfold Scheme.generalize
  rw [generalizedCapVars_forward certificate leftCaps rightCaps target caps
      targets capEnvironment,
    generalizedTyVars_forward certificate leftTargets rightTargets target caps
      targets targetEnvironment]
  apply Scheme.close_forward certificate
  · exact caps
  · exact targets
  · intro varId member
    exact (List.mem_filter.mp (mem_uniqueVars.mp member)).1
  · intro varId member
    exact (List.mem_filter.mp (mem_uniqueVars.mp member)).1

/-! ## Free-occurrence propagation through ambient scheme substitution -/

mutual

theorem PolyCap.mem_fcv_applyMeta_of_cap
    {capArity : Nat} (substitution : CapSubst) :
    ∀ (capability : PolyCap capArity) {source image : CapVar},
      source ∈ capability.fcv → substitution source = .var image →
      image ∈ (capability.applyMeta substitution).fcv
  | .any, _, _, membership, _ => nomatch membership
  | .mvar original, source, image, membership, equation => by
      simp only [PolyCap.fcv, List.mem_singleton] at membership
      subst source
      simp [PolyCap.applyMeta, equation, PolyCap.lift, PolyCap.fcv]
  | .bound _, _, _, membership, _ => nomatch membership
  | .skolem _, _, _, membership, _ => nomatch membership
  | .con _ children, source, image, membership, equation => by
      simp only [PolyCap.fcv, PolyCap.applyMeta]
      exact PolyCap.mem_fcvList_applyMeta_of_cap substitution children
        membership equation
  | .prod components, source, image, membership, equation => by
      simp only [PolyCap.fcv, PolyCap.applyMeta]
      exact PolyCap.mem_fcvList_applyMeta_of_cap substitution components
        membership equation

theorem PolyCap.mem_fcvList_applyMeta_of_cap
    {capArity : Nat} (substitution : CapSubst) :
    ∀ (capabilities : List (PolyCap capArity)) {source image : CapVar},
      source ∈ PolyCap.fcvList capabilities →
      substitution source = .var image →
      image ∈ PolyCap.fcvList (capabilities.map (PolyCap.applyMeta substitution))
  | [], _, _, membership, _ => nomatch membership
  | capability :: capabilities, source, image, membership, equation => by
      simp only [PolyCap.fcvList, List.mem_append, List.map_cons] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyCap.mem_fcv_applyMeta_of_cap substitution capability here equation)
        (Or.inr ∘ fun there =>
          PolyCap.mem_fcvList_applyMeta_of_cap substitution capabilities there
            equation)

end

mutual

theorem PolyTy.mem_fcv_applyMeta_of_cap
    {capArity tyArity : Nat} (substitution : Subst) :
    ∀ (target : PolyTy capArity tyArity) {source image : CapVar},
      source ∈ target.fcv → substitution.cap source = .var image →
      image ∈ (target.applyMeta substitution).fcv
  | .mvar _, _, _, membership, _ => nomatch membership
  | .bound _, _, _, membership, _ => nomatch membership
  | .skolem _, _, _, membership, _ => nomatch membership
  | .unit, _, _, membership, _ => nomatch membership
  | .int, _, _, membership, _ => nomatch membership
  | .bool, _, _, membership, _ => nomatch membership
  | .data _ children, source, image, membership, equation =>
      by simpa [PolyTy.applyMeta, PolyTy.fcv] using
        PolyTy.mem_fcvList_applyMeta_of_cap substitution children membership
          equation
  | .prod components, source, image, membership, equation =>
      by simpa [PolyTy.applyMeta, PolyTy.fcv] using
        PolyTy.mem_fcvList_applyMeta_of_cap substitution components membership
          equation
  | .fn domain codomain, source, image, membership, equation => by
      simp only [PolyTy.fcv, PolyTy.applyMeta, List.mem_append] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyTy.mem_fcv_applyMeta_of_cap substitution domain here equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_fcv_applyMeta_of_cap substitution codomain there equation)
  | .matcher capability target, source, image, membership, equation => by
      simp only [PolyTy.fcv, PolyTy.applyMeta, List.mem_append] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyCap.mem_fcv_applyMeta_of_cap substitution.cap capability here
            equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_fcv_applyMeta_of_cap substitution target there equation)
  | .slot capability target, source, image, membership, equation => by
      simp only [PolyTy.fcv, PolyTy.applyMeta, List.mem_append] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyCap.mem_fcv_applyMeta_of_cap substitution.cap capability here
            equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_fcv_applyMeta_of_cap substitution target there equation)

theorem PolyTy.mem_fcvList_applyMeta_of_cap
    {capArity tyArity : Nat} (substitution : Subst) :
    ∀ (targets : List (PolyTy capArity tyArity)) {source image : CapVar},
      source ∈ PolyTy.fcvList targets → substitution.cap source = .var image →
      image ∈ PolyTy.fcvList (targets.map (PolyTy.applyMeta substitution))
  | [], _, _, membership, _ => nomatch membership
  | target :: targets, source, image, membership, equation => by
      simp only [PolyTy.fcvList, List.mem_append, List.map_cons] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyTy.mem_fcv_applyMeta_of_cap substitution target here equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_fcvList_applyMeta_of_cap substitution targets there equation)

end

mutual

theorem PolyTy.mem_ftv_applyMeta_of_target
    {capArity tyArity : Nat} (substitution : Subst) :
    ∀ (target : PolyTy capArity tyArity) {source image : TypePM.TyVar},
      source ∈ target.ftv → substitution.target source = .var image →
      image ∈ (target.applyMeta substitution).ftv
  | .mvar original, source, image, membership, equation => by
      simp only [PolyTy.ftv, List.mem_singleton] at membership
      subst source
      simp [PolyTy.applyMeta, equation, PolyTy.lift, PolyTy.ftv]
  | .bound _, _, _, membership, _ => nomatch membership
  | .skolem _, _, _, membership, _ => nomatch membership
  | .unit, _, _, membership, _ => nomatch membership
  | .int, _, _, membership, _ => nomatch membership
  | .bool, _, _, membership, _ => nomatch membership
  | .data _ children, source, image, membership, equation =>
      by simpa [PolyTy.applyMeta, PolyTy.ftv] using
        PolyTy.mem_ftvList_applyMeta_of_target substitution children membership
          equation
  | .prod components, source, image, membership, equation =>
      by simpa [PolyTy.applyMeta, PolyTy.ftv] using
        PolyTy.mem_ftvList_applyMeta_of_target substitution components membership
          equation
  | .fn domain codomain, source, image, membership, equation => by
      simp only [PolyTy.ftv, PolyTy.applyMeta, List.mem_append] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyTy.mem_ftv_applyMeta_of_target substitution domain here equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_ftv_applyMeta_of_target substitution codomain there equation)
  | .matcher _ target, source, image, membership, equation => by
      simpa [PolyTy.applyMeta, PolyTy.ftv] using
        PolyTy.mem_ftv_applyMeta_of_target substitution target membership
          equation
  | .slot _ target, source, image, membership, equation => by
      simpa [PolyTy.applyMeta, PolyTy.ftv] using
        PolyTy.mem_ftv_applyMeta_of_target substitution target membership
          equation

theorem PolyTy.mem_ftvList_applyMeta_of_target
    {capArity tyArity : Nat} (substitution : Subst) :
    ∀ (targets : List (PolyTy capArity tyArity))
      {source image : TypePM.TyVar},
      source ∈ PolyTy.ftvList targets →
      substitution.target source = .var image →
      image ∈ PolyTy.ftvList (targets.map (PolyTy.applyMeta substitution))
  | [], _, _, membership, _ => nomatch membership
  | target :: targets, source, image, membership, equation => by
      simp only [PolyTy.ftvList, List.mem_append, List.map_cons] at membership ⊢
      exact membership.elim
        (Or.inl ∘ fun here =>
          PolyTy.mem_ftv_applyMeta_of_target substitution target here equation)
        (Or.inr ∘ fun there =>
          PolyTy.mem_ftvList_applyMeta_of_target substitution targets there
            equation)

end

theorem Scheme.mem_fcv_applyMeta_of_cap
    (scheme : Scheme) (substitution : Subst) {source image : CapVar}
    (membership : source ∈ scheme.fcv)
    (equation : substitution.cap source = .var image) :
    image ∈ (scheme.applyMeta substitution).fcv := by
  cases scheme
  exact PolyTy.mem_fcv_applyMeta_of_cap substitution _ membership equation

theorem Scheme.mem_ftv_applyMeta_of_target
    (scheme : Scheme) (substitution : Subst) {source image : TypePM.TyVar}
    (membership : source ∈ scheme.ftv)
    (equation : substitution.target source = .var image) :
    image ∈ (scheme.applyMeta substitution).ftv := by
  cases scheme
  exact PolyTy.mem_ftv_applyMeta_of_target substitution _ membership equation

theorem Context.mem_fcv_applySubst_of_cap
    (context : Context) (substitution : Subst) {source image : CapVar}
    (membership : source ∈ context.fcv)
    (equation : substitution.cap source = .var image) :
    image ∈ (context.applySubst substitution).fcv := by
  rcases List.mem_flatMap.mp membership with ⟨entry, entryMem, free⟩
  apply List.mem_flatMap.mpr
  exact ⟨(entry.1, entry.2.applyMeta substitution),
    List.mem_map.mpr ⟨entry, entryMem, rfl⟩,
    Scheme.mem_fcv_applyMeta_of_cap entry.2 substitution free equation⟩

theorem Context.mem_ftv_applySubst_of_target
    (context : Context) (substitution : Subst)
    {source image : TypePM.TyVar}
    (membership : source ∈ context.ftv)
    (equation : substitution.target source = .var image) :
    image ∈ (context.applySubst substitution).ftv := by
  rcases List.mem_flatMap.mp membership with ⟨entry, entryMem, free⟩
  apply List.mem_flatMap.mpr
  exact ⟨(entry.1, entry.2.applyMeta substitution),
    List.mem_map.mpr ⟨entry, entryMem, rfl⟩,
    Scheme.mem_ftv_applyMeta_of_target entry.2 substitution free equation⟩

end DemandTypingInferenceCompletenessGeneralizationEquivariance
end TypePM
