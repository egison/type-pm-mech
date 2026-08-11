import TypePM.PolyScheme

/-!
# Substitution algebra for capture-free scheme payloads

Ambient substitution acts only on `mvar` nodes.  Bound `Fin` indices are
copied in every equation below, so the ordinary paired-substitution algebra
lifts without a capture or binder-support premise.
-/

namespace TypePM

/-! ## Applying a substitution to lifted ordinary syntax -/

mutual

theorem PolyCap.applyMeta_lift {capArity : Nat} (S : CapSubst) :
    ∀ capability : Cap,
      (PolyCap.lift (capArity := capArity) capability).applyMeta S =
        PolyCap.lift (capArity := capArity) (capability.apply S)
  | .any => by simp [PolyCap.lift, PolyCap.applyMeta, Cap.apply]
  | .var _ => by simp [PolyCap.lift, PolyCap.applyMeta, Cap.apply]
  | .skolem _ => by simp [PolyCap.lift, PolyCap.applyMeta, Cap.apply]
  | .con name children => by
      simp only [PolyCap.lift, PolyCap.applyMeta, Cap.apply]
      congr 1
      exact PolyCap.map_applyMeta_lift S children
  | .prod components => by
      simp only [PolyCap.lift, PolyCap.applyMeta, Cap.apply]
      congr 1
      exact PolyCap.map_applyMeta_lift S components

theorem PolyCap.map_applyMeta_lift {capArity : Nat} (S : CapSubst) :
    ∀ capabilities : List Cap,
      (capabilities.map (PolyCap.lift (capArity := capArity))).map
          (PolyCap.applyMeta S) =
        (Cap.applyList S capabilities).map
          (PolyCap.lift (capArity := capArity))
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons, Cap.applyList]
      rw [PolyCap.applyMeta_lift S capability,
        PolyCap.map_applyMeta_lift S capabilities]

end

mutual

theorem PolyTy.applyMeta_lift {capArity tyArity : Nat} (S : Subst) :
    ∀ target : Ty,
      (PolyTy.lift (capArity := capArity) (tyArity := tyArity) target).applyMeta S =
        PolyTy.lift (capArity := capArity) (tyArity := tyArity)
          (S.apply target)
  | .var _ => by simp [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .skolem _ => by simp [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .unit => by simp [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .int => by simp [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .bool => by simp [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
      Ty.applyCapability, Ty.applyTarget]
  | .data name children => by
      simp only [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr 1
      exact PolyTy.map_applyMeta_lift S children
  | .prod components => by
      simp only [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr 1
      exact PolyTy.map_applyMeta_lift S components
  | .fn domain codomain => by
      simp only [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyTy.applyMeta_lift S domain,
        PolyTy.applyMeta_lift S codomain]
      rfl
  | .matcher capability target => by
      simp only [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyCap.applyMeta_lift S.cap capability,
        PolyTy.applyMeta_lift S target]
      rfl
  | .slot capability target => by
      simp only [PolyTy.lift, PolyTy.applyMeta, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      rw [PolyCap.applyMeta_lift S.cap capability,
        PolyTy.applyMeta_lift S target]
      rfl

theorem PolyTy.map_applyMeta_lift {capArity tyArity : Nat} (S : Subst) :
    ∀ targets : List Ty,
      (targets.map (PolyTy.lift (capArity := capArity)
        (tyArity := tyArity))).map (PolyTy.applyMeta S) =
        (Ty.applyTargetList S.target
          (Ty.applyCapabilityList S.cap targets)).map
            (PolyTy.lift (capArity := capArity) (tyArity := tyArity))
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons, Ty.applyCapabilityList, Ty.applyTargetList]
      rw [PolyTy.applyMeta_lift S target,
        PolyTy.map_applyMeta_lift S targets]
      rfl

end


/-! ## Identity -/

mutual

@[simp] theorem PolyCap.applyMeta_id {capArity : Nat} :
    ∀ capability : PolyCap capArity,
      capability.applyMeta CapSubst.id = capability
  | .any => by simp [PolyCap.applyMeta]
  | .mvar _ => by simp [PolyCap.applyMeta, PolyCap.lift, CapSubst.id]
  | .bound _ => by simp [PolyCap.applyMeta]
  | .skolem _ => by simp [PolyCap.applyMeta]
  | .con name children => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_id children
  | .prod components => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_id components

@[simp] theorem PolyCap.map_applyMeta_id {capArity : Nat} :
    ∀ capabilities : List (PolyCap capArity),
      capabilities.map (PolyCap.applyMeta CapSubst.id) = capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [PolyCap.applyMeta_id capability,
        PolyCap.map_applyMeta_id capabilities]

end

mutual

@[simp] theorem PolyTy.applyMeta_id {capArity tyArity : Nat} :
    ∀ target : PolyTy capArity tyArity,
      target.applyMeta Subst.id = target
  | .mvar _ => by simp [PolyTy.applyMeta, PolyTy.lift, Subst.id,
      TySubst.id]
  | .bound _ => by simp [PolyTy.applyMeta]
  | .skolem _ => by simp [PolyTy.applyMeta]
  | .unit => by simp [PolyTy.applyMeta]
  | .int => by simp [PolyTy.applyMeta]
  | .bool => by simp [PolyTy.applyMeta]
  | .data name children => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_id children
  | .prod components => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_id components
  | .fn domain codomain => by
      simp only [PolyTy.applyMeta]
      rw [PolyTy.applyMeta_id domain, PolyTy.applyMeta_id codomain]
  | .matcher capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.matcher (capability.applyMeta CapSubst.id)
          (target.applyMeta Subst.id) = PolyTy.matcher capability target
      rw [PolyCap.applyMeta_id capability, PolyTy.applyMeta_id target]
  | .slot capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.slot (capability.applyMeta CapSubst.id)
          (target.applyMeta Subst.id) = PolyTy.slot capability target
      rw [PolyCap.applyMeta_id capability, PolyTy.applyMeta_id target]

@[simp] theorem PolyTy.map_applyMeta_id {capArity tyArity : Nat} :
    ∀ targets : List (PolyTy capArity tyArity),
      targets.map (PolyTy.applyMeta Subst.id) = targets
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [PolyTy.applyMeta_id target, PolyTy.map_applyMeta_id targets]

end


/-! ## Composition -/

mutual

theorem PolyCap.applyMeta_comp {capArity : Nat} (S₂ S₁ : CapSubst) :
    ∀ capability : PolyCap capArity,
      capability.applyMeta (CapSubst.comp S₂ S₁) =
        (capability.applyMeta S₁).applyMeta S₂
  | .any => by simp [PolyCap.applyMeta]
  | .mvar varId => by
      simp only [PolyCap.applyMeta, CapSubst.comp]
      rw [PolyCap.applyMeta_lift S₂ (S₁ varId)]
  | .bound _ => by simp [PolyCap.applyMeta]
  | .skolem _ => by simp [PolyCap.applyMeta]
  | .con name children => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_comp S₂ S₁ children
  | .prod components => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_comp S₂ S₁ components

theorem PolyCap.map_applyMeta_comp {capArity : Nat} (S₂ S₁ : CapSubst) :
    ∀ capabilities : List (PolyCap capArity),
      capabilities.map (PolyCap.applyMeta (CapSubst.comp S₂ S₁)) =
        (capabilities.map (PolyCap.applyMeta S₁)).map
          (PolyCap.applyMeta S₂)
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [PolyCap.applyMeta_comp S₂ S₁ capability,
        PolyCap.map_applyMeta_comp S₂ S₁ capabilities]

end

mutual

theorem PolyTy.applyMeta_comp {capArity tyArity : Nat}
    (S₂ S₁ : Subst)
    (crossFixed : (Subst.mk S₂.cap S₁.target).RangeFixed) :
    ∀ target : PolyTy capArity tyArity,
      target.applyMeta (Subst.comp S₂ S₁) =
        (target.applyMeta S₁).applyMeta S₂
  | .mvar varId => by
      simp only [PolyTy.applyMeta]
      rw [PolyTy.applyMeta_lift S₂ (S₁.target varId)]
      exact congrArg PolyTy.lift
        (Subst.apply_comp S₂ S₁ crossFixed (.var varId))
  | .bound _ => by simp [PolyTy.applyMeta]
  | .skolem _ => by simp [PolyTy.applyMeta]
  | .unit => by simp [PolyTy.applyMeta]
  | .int => by simp [PolyTy.applyMeta]
  | .bool => by simp [PolyTy.applyMeta]
  | .data name children => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_comp S₂ S₁ crossFixed children
  | .prod components => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_comp S₂ S₁ crossFixed components
  | .fn domain codomain => by
      simp only [PolyTy.applyMeta]
      rw [PolyTy.applyMeta_comp S₂ S₁ crossFixed domain,
        PolyTy.applyMeta_comp S₂ S₁ crossFixed codomain]
  | .matcher capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.matcher
          (capability.applyMeta (CapSubst.comp S₂.cap S₁.cap))
          (target.applyMeta (Subst.comp S₂ S₁)) =
        PolyTy.matcher ((capability.applyMeta S₁.cap).applyMeta S₂.cap)
          ((target.applyMeta S₁).applyMeta S₂)
      rw [PolyCap.applyMeta_comp S₂.cap S₁.cap capability,
        PolyTy.applyMeta_comp S₂ S₁ crossFixed target]
  | .slot capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.slot
          (capability.applyMeta (CapSubst.comp S₂.cap S₁.cap))
          (target.applyMeta (Subst.comp S₂ S₁)) =
        PolyTy.slot ((capability.applyMeta S₁.cap).applyMeta S₂.cap)
          ((target.applyMeta S₁).applyMeta S₂)
      rw [PolyCap.applyMeta_comp S₂.cap S₁.cap capability,
        PolyTy.applyMeta_comp S₂ S₁ crossFixed target]

theorem PolyTy.map_applyMeta_comp {capArity tyArity : Nat}
    (S₂ S₁ : Subst)
    (crossFixed : (Subst.mk S₂.cap S₁.target).RangeFixed) :
    ∀ targets : List (PolyTy capArity tyArity),
      targets.map (PolyTy.applyMeta (Subst.comp S₂ S₁)) =
        (targets.map (PolyTy.applyMeta S₁)).map (PolyTy.applyMeta S₂)
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [PolyTy.applyMeta_comp S₂ S₁ crossFixed target,
        PolyTy.map_applyMeta_comp S₂ S₁ crossFixed targets]

end

/-! ## Unconditional sequential paired composition -/

mutual

/-- Cross-sort-aware `Subst.seq` composes ambient actions on polymorphic
payloads without a capture or cross-range premise. -/
theorem PolyTy.applyMeta_seq {capArity tyArity : Nat}
    (later earlier : Subst) :
    ∀ target : PolyTy capArity tyArity,
      target.applyMeta (Subst.seq later earlier) =
        (target.applyMeta earlier).applyMeta later
  | .mvar varId => by
      simp only [PolyTy.applyMeta]
      rw [PolyTy.applyMeta_lift later (earlier.target varId)]
      exact congrArg PolyTy.lift
        (Subst.seq_apply later earlier (.var varId))
  | .bound _ => by simp [PolyTy.applyMeta]
  | .skolem _ => by simp [PolyTy.applyMeta]
  | .unit => by simp [PolyTy.applyMeta]
  | .int => by simp [PolyTy.applyMeta]
  | .bool => by simp [PolyTy.applyMeta]
  | .data name children => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_seq later earlier children
  | .prod components => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_seq later earlier components
  | .fn domain codomain => by
      simp only [PolyTy.applyMeta]
      rw [PolyTy.applyMeta_seq later earlier domain,
        PolyTy.applyMeta_seq later earlier codomain]
  | .matcher capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.matcher
          (capability.applyMeta (CapSubst.comp later.cap earlier.cap))
          (target.applyMeta (Subst.seq later earlier)) =
        PolyTy.matcher
          ((capability.applyMeta earlier.cap).applyMeta later.cap)
          ((target.applyMeta earlier).applyMeta later)
      rw [PolyCap.applyMeta_comp later.cap earlier.cap capability,
        PolyTy.applyMeta_seq later earlier target]
  | .slot capability target => by
      simp only [PolyTy.applyMeta]
      change PolyTy.slot
          (capability.applyMeta (CapSubst.comp later.cap earlier.cap))
          (target.applyMeta (Subst.seq later earlier)) =
        PolyTy.slot
          ((capability.applyMeta earlier.cap).applyMeta later.cap)
          ((target.applyMeta earlier).applyMeta later)
      rw [PolyCap.applyMeta_comp later.cap earlier.cap capability,
        PolyTy.applyMeta_seq later earlier target]

/-- List form of `PolyTy.applyMeta_seq`. -/
theorem PolyTy.map_applyMeta_seq {capArity tyArity : Nat}
    (later earlier : Subst) :
    ∀ targets : List (PolyTy capArity tyArity),
      targets.map (PolyTy.applyMeta (Subst.seq later earlier)) =
        (targets.map (PolyTy.applyMeta earlier)).map
          (PolyTy.applyMeta later)
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [PolyTy.applyMeta_seq later earlier target,
        PolyTy.map_applyMeta_seq later earlier targets]

end


namespace Scheme

@[simp] theorem applyMeta_mono (substitution : Subst) (target : Ty) :
    (Scheme.mono target).applyMeta substitution =
      Scheme.mono (substitution.apply target) := by
  simp [Scheme.mono, Scheme.applyMeta, PolyTy.applyMeta_lift]

@[simp] theorem applyMeta_id (scheme : Scheme) :
    scheme.applyMeta Subst.id = scheme := by
  cases scheme with
  | mk capArity tyArity body =>
      simp [Scheme.applyMeta, PolyTy.applyMeta_id]

theorem applyMeta_comp (S₂ S₁ : Subst)
    (crossFixed : (Subst.mk S₂.cap S₁.target).RangeFixed)
    (scheme : Scheme) :
    scheme.applyMeta (Subst.comp S₂ S₁) =
      (scheme.applyMeta S₁).applyMeta S₂ := by
  cases scheme with
  | mk capArity tyArity body =>
      simp only [Scheme.applyMeta]
      congr 1
      exact PolyTy.applyMeta_comp S₂ S₁ crossFixed body

/-- Canonical schemes inherit unconditional cross-sort sequential
composition because bound indices are unaffected by ambient actions. -/
theorem applyMeta_seq (later earlier : Subst) (scheme : Scheme) :
    scheme.applyMeta (Subst.seq later earlier) =
      (scheme.applyMeta earlier).applyMeta later := by
  cases scheme with
  | mk capArity tyArity body =>
      simp only [Scheme.applyMeta]
      congr 1
      exact PolyTy.applyMeta_seq later earlier body

end Scheme
end TypePM
