import TypePM.Source

/-!
# Substitution boundary for the two-sorted source layer

The source rules contain fresh leaves, quantified schemes, frozen signature
instances, and opaque frozen exhaustiveness code.  Consequently an
unqualified statement saying that every paired substitution preserves every
source derivation is false: substitution can capture a scheme binder, rewrite
a freshly generated leaf, or change the answer of `armExhaustive`.

This file proves the occurrence-wide transport that is valid without such a
claim.  It separates three obligations:

* semantic composition and range-fixedness of paired substitutions;
* binder-local masking and capture avoidance for quantified schemes;
* algebraic composition of fresh signature-instantiation witnesses.

None of these obligations assumes a transported source-typing conclusion.
Evidence non-seeding and capability coverage are proved independently of the
target side.
-/

namespace TypePM

/-! ## Finite capability-variable posts -/

/--
Package a finite capability-variable mapping and a finite target
substitution as one restricted post.  Only the declared capability domain
needs a variable-image proof: finite support makes every other variable map
to itself.  No global injectivity or permutation is required.
-/
def RestrictedPost.ofVariableSubstitution
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar}
    (capPost : CapSubst) (targetPost : TySubst)
    (capSupport : capPost.SupportWithin capDomain)
    (targetSupport : targetPost.SupportWithin tyDomain)
    (capDomainNodup : capDomain.Nodup)
    (tyDomainNodup : tyDomain.Nodup)
    (capImageVars : capDomain.map capPost = capImages.map Cap.var)
    (capImagesNodup : capImages.Nodup)
    (capDomainFresh :
      ∀ varId, varId ∈ capDomain → varId ∉ fixedCaps)
    (tyDomainFresh :
      ∀ varId, varId ∈ tyDomain → varId ∉ fixedTys)
    (capImagesFixedFresh :
      ∀ varId, varId ∈ capImages → varId ∉ fixedCaps)
    (capImagesFresh :
      ∀ varId, varId ∈ capImages → varId ∉ reservedCaps) :
    RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages
      (Subst.mk capPost targetPost) where
  capSupport := by
    intro varId outside
    apply capSupport varId
    intro membership
    exact outside (List.mem_append_left capImages membership)
  tySupport := targetSupport
  capDomainNodup := capDomainNodup
  tyDomainNodup := tyDomainNodup
  capImageVars := capImageVars
  capImagesNodup := capImagesNodup
  capVariable := by
    intro varId
    by_cases membership : varId ∈ capDomain
    · have imageMembership : capPost varId ∈ capImages.map Cap.var := by
        rw [← capImageVars]
        exact List.mem_map.mpr ⟨varId, membership, rfl⟩
      rcases List.mem_map.mp imageMembership with ⟨image, _, equality⟩
      exact ⟨image, equality.symm⟩
    · exact ⟨varId, capSupport varId membership⟩
  capDomainFresh := capDomainFresh
  tyDomainFresh := tyDomainFresh
  capImagesFixedFresh := capImagesFixedFresh
  capImagesFresh := capImagesFresh

/-- Forget ambient freshness scopes while retaining the finite post itself. -/
def RestrictedPost.forgetScopes
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar} {post : Subst}
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages post) :
    RestrictedPost [] [] [] [] capDomain tyDomain capImages post where
  capSupport := restricted.capSupport
  tySupport := restricted.tySupport
  capDomainNodup := restricted.capDomainNodup
  tyDomainNodup := restricted.tyDomainNodup
  capImageVars := restricted.capImageVars
  capImagesNodup := restricted.capImagesNodup
  capVariable := restricted.capVariable
  capDomainFresh := by intros; simp
  tyDomainFresh := by intros; simp
  capImagesFixedFresh := by intros; simp
  capImagesFresh := by intros; simp

/-- Forget the common ambient scopes of every node in a post chain. -/
def RestrictedPost.Chain.forgetScopes
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post) :
    RestrictedPost.Chain [] [] [] [] post := by
  induction chain with
  | one restricted => exact .one restricted.forgetScopes
  | comp earlier later induction =>
      exact .comp induction later.forgetScopes

/-- Append one atomic post to the right end of a certified chain. -/
def RestrictedPost.Chain.snoc
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {earlier later : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      earlier)
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages later) :
    RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      (Subst.seq later earlier) :=
  .comp chain restricted

/-! ## Finite-support fixing lemmas -/

mutual

/-- A capability substitution fixing every free leaf fixes the capability. -/
theorem Cap.apply_eq_self_of_fcv_fixed (C : CapSubst) :
    ∀ capability : Cap,
      (∀ varId, varId ∈ capability.fcv → C varId = .var varId) →
      capability.apply C = capability
  | .none, _ => rfl
  | .var varId, fixed => fixed varId (by simp [Cap.fcv])
  | .skolem _, _ => rfl
  | .con name children, fixed => by
      simp only [Cap.apply]
      congr 1
      exact Cap.applyList_eq_self_of_fcv_fixed C children
        (fun varId membership => fixed varId (by
          simpa [Cap.fcv] using membership))
  | .prod components, fixed => by
      simp only [Cap.apply]
      congr 1
      exact Cap.applyList_eq_self_of_fcv_fixed C components
        (fun varId membership => fixed varId (by
          simpa [Cap.fcv] using membership))

/-- List form of `Cap.apply_eq_self_of_fcv_fixed`. -/
theorem Cap.applyList_eq_self_of_fcv_fixed (C : CapSubst) :
    ∀ capabilities : List Cap,
      (∀ varId, varId ∈ Cap.fcvList capabilities →
        C varId = .var varId) →
      Cap.applyList C capabilities = capabilities
  | [], _ => rfl
  | capability :: capabilities, fixed => by
      simp only [Cap.applyList]
      congr 1
      · exact Cap.apply_eq_self_of_fcv_fixed C capability
          (fun varId membership => fixed varId (by
            simp [Cap.fcvList, membership]))
      · exact Cap.applyList_eq_self_of_fcv_fixed C capabilities
          (fun varId membership => fixed varId (by
            simp [Cap.fcvList, membership]))

end

mutual

/-- Fixing all free capability leaves fixes capability substitution in a type. -/
theorem Ty.applyCapability_eq_self_of_fcv_fixed (C : CapSubst) :
    ∀ target : Ty,
      (∀ varId, varId ∈ target.fcv → C varId = .var varId) →
      target.applyCapability C = target
  | .var _, _ => rfl
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data name arguments, fixed => by
      simp only [Ty.applyCapability]
      congr 1
      exact Ty.applyCapabilityList_eq_self_of_fcv_fixed C arguments
        (fun varId membership => fixed varId (by
          simpa [Ty.fcv] using membership))
  | .prod components, fixed => by
      simp only [Ty.applyCapability]
      congr 1
      exact Ty.applyCapabilityList_eq_self_of_fcv_fixed C components
        (fun varId membership => fixed varId (by
          simpa [Ty.fcv] using membership))
  | .fn domain codomain, fixed => by
      simp only [Ty.applyCapability]
      congr 1
      · exact Ty.applyCapability_eq_self_of_fcv_fixed C domain
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))
      · exact Ty.applyCapability_eq_self_of_fcv_fixed C codomain
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))
  | .matcher capability target, fixed => by
      simp only [Ty.applyCapability]
      congr 1
      · exact Cap.apply_eq_self_of_fcv_fixed C capability
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))
      · exact Ty.applyCapability_eq_self_of_fcv_fixed C target
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))
  | .slot capability target, fixed => by
      simp only [Ty.applyCapability]
      congr 1
      · exact Cap.apply_eq_self_of_fcv_fixed C capability
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))
      · exact Ty.applyCapability_eq_self_of_fcv_fixed C target
          (fun varId membership => fixed varId (by
            simp [Ty.fcv, membership]))

/-- List form of `Ty.applyCapability_eq_self_of_fcv_fixed`. -/
theorem Ty.applyCapabilityList_eq_self_of_fcv_fixed (C : CapSubst) :
    ∀ targets : List Ty,
      (∀ varId, varId ∈ Ty.fcvList targets →
        C varId = .var varId) →
      Ty.applyCapabilityList C targets = targets
  | [], _ => rfl
  | target :: targets, fixed => by
      simp only [Ty.applyCapabilityList]
      congr 1
      · exact Ty.applyCapability_eq_self_of_fcv_fixed C target
          (fun varId membership => fixed varId (by
            simp [Ty.fcvList, membership]))
      · exact Ty.applyCapabilityList_eq_self_of_fcv_fixed C targets
          (fun varId membership => fixed varId (by
            simp [Ty.fcvList, membership]))

end

mutual

/-- A target substitution fixing every free target leaf fixes the type. -/
theorem Ty.applyTarget_eq_self_of_ftv_fixed (T : TySubst) :
    ∀ target : Ty,
      (∀ varId, varId ∈ target.ftv → T varId = .var varId) →
      target.applyTarget T = target
  | .var varId, fixed => fixed varId (by simp [Ty.ftv])
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data name arguments, fixed => by
      simp only [Ty.applyTarget]
      congr 1
      exact Ty.applyTargetList_eq_self_of_ftv_fixed T arguments
        (fun varId membership => fixed varId (by
          simpa [Ty.ftv] using membership))
  | .prod components, fixed => by
      simp only [Ty.applyTarget]
      congr 1
      exact Ty.applyTargetList_eq_self_of_ftv_fixed T components
        (fun varId membership => fixed varId (by
          simpa [Ty.ftv] using membership))
  | .fn domain codomain, fixed => by
      simp only [Ty.applyTarget]
      congr 1
      · exact Ty.applyTarget_eq_self_of_ftv_fixed T domain
          (fun varId membership => fixed varId (by
            simp [Ty.ftv, membership]))
      · exact Ty.applyTarget_eq_self_of_ftv_fixed T codomain
          (fun varId membership => fixed varId (by
            simp [Ty.ftv, membership]))
  | .matcher capability target, fixed => by
      simp only [Ty.applyTarget]
      congr 1
      exact Ty.applyTarget_eq_self_of_ftv_fixed T target fixed
  | .slot capability target, fixed => by
      simp only [Ty.applyTarget]
      congr 1
      exact Ty.applyTarget_eq_self_of_ftv_fixed T target fixed

/-- List form of `Ty.applyTarget_eq_self_of_ftv_fixed`. -/
theorem Ty.applyTargetList_eq_self_of_ftv_fixed (T : TySubst) :
    ∀ targets : List Ty,
      (∀ varId, varId ∈ Ty.ftvList targets →
        T varId = .var varId) →
      Ty.applyTargetList T targets = targets
  | [], _ => rfl
  | target :: targets, fixed => by
      simp only [Ty.applyTargetList]
      congr 1
      · exact Ty.applyTarget_eq_self_of_ftv_fixed T target
          (fun varId membership => fixed varId (by
            simp [Ty.ftvList, membership]))
      · exact Ty.applyTargetList_eq_self_of_ftv_fixed T targets
          (fun varId membership => fixed varId (by
            simp [Ty.ftvList, membership]))

end

/-- A paired substitution fixing both free-variable sorts fixes the type. -/
theorem Subst.apply_eq_self_of_free_fixed
    (post : Subst) (target : Ty)
    (capFixed : ∀ varId, varId ∈ target.fcv →
      post.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ target.ftv →
      post.target varId = .var varId) :
    post.apply target = target := by
  unfold Subst.apply
  rw [Ty.applyCapability_eq_self_of_fcv_fixed post.cap target capFixed]
  exact Ty.applyTarget_eq_self_of_ftv_fixed post.target target tyFixed

mutual

/-- Capability application depends only on the free leaves of its input. -/
theorem Cap.apply_eq_of_fcv_agree (left right : CapSubst) :
    ∀ capability : Cap,
      (∀ varId, varId ∈ capability.fcv →
        left varId = right varId) →
      capability.apply left = capability.apply right
  | .none, _ => rfl
  | .var varId, agree => agree varId (by simp [Cap.fcv])
  | .skolem _, _ => rfl
  | .con name children, agree => by
      simp only [Cap.apply]
      congr 1
      exact Cap.applyList_eq_of_fcv_agree left right children
        (fun varId membership => agree varId (by
          simpa [Cap.fcv] using membership))
  | .prod components, agree => by
      simp only [Cap.apply]
      congr 1
      exact Cap.applyList_eq_of_fcv_agree left right components
        (fun varId membership => agree varId (by
          simpa [Cap.fcv] using membership))

/-- List form of `Cap.apply_eq_of_fcv_agree`. -/
theorem Cap.applyList_eq_of_fcv_agree (left right : CapSubst) :
    ∀ capabilities : List Cap,
      (∀ varId, varId ∈ Cap.fcvList capabilities →
        left varId = right varId) →
      Cap.applyList left capabilities = Cap.applyList right capabilities
  | [], _ => rfl
  | capability :: capabilities, agree => by
      simp only [Cap.applyList]
      congr 1
      · exact Cap.apply_eq_of_fcv_agree left right capability
          (fun varId membership => agree varId (by
            simp [Cap.fcvList, membership]))
      · exact Cap.applyList_eq_of_fcv_agree left right capabilities
          (fun varId membership => agree varId (by
            simp [Cap.fcvList, membership]))

end

mutual

/-- Paired application depends only on the two free-variable lists. -/
theorem Subst.apply_eq_of_free_agree (left right : Subst) :
    ∀ target : Ty,
      (∀ varId, varId ∈ target.fcv →
        left.cap varId = right.cap varId) →
      (∀ varId, varId ∈ target.ftv →
        left.target varId = right.target varId) →
      left.apply target = right.apply target
  | .var varId, _, tyAgree => tyAgree varId (by simp [Ty.ftv])
  | .skolem _, _, _ => rfl
  | .unit, _, _ => rfl
  | .int, _, _ => rfl
  | .bool, _, _ => rfl
  | .data name arguments, capAgree, tyAgree => by
      change Ty.data name _ = Ty.data name _
      congr 1
      exact Subst.applyList_eq_of_free_agree left right arguments
        (fun varId membership => capAgree varId (by
          simpa [Ty.fcv] using membership))
        (fun varId membership => tyAgree varId (by
          simpa [Ty.ftv] using membership))
  | .prod components, capAgree, tyAgree => by
      change Ty.prod _ = Ty.prod _
      congr 1
      exact Subst.applyList_eq_of_free_agree left right components
        (fun varId membership => capAgree varId (by
          simpa [Ty.fcv] using membership))
        (fun varId membership => tyAgree varId (by
          simpa [Ty.ftv] using membership))
  | .fn domain codomain, capAgree, tyAgree => by
      change Ty.fn _ _ = Ty.fn _ _
      congr 1
      · exact Subst.apply_eq_of_free_agree left right domain
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simp [Ty.ftv, membership]))
      · exact Subst.apply_eq_of_free_agree left right codomain
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simp [Ty.ftv, membership]))
  | .matcher capability target, capAgree, tyAgree => by
      change Ty.matcher _ _ = Ty.matcher _ _
      congr 1
      · exact Cap.apply_eq_of_fcv_agree left.cap right.cap capability
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership]))
      · exact Subst.apply_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership])) tyAgree
  | .slot capability target, capAgree, tyAgree => by
      change Ty.slot _ _ = Ty.slot _ _
      congr 1
      · exact Cap.apply_eq_of_fcv_agree left.cap right.cap capability
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership]))
      · exact Subst.apply_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [Ty.fcv, membership])) tyAgree

/-- List form of `Subst.apply_eq_of_free_agree`. -/
theorem Subst.applyList_eq_of_free_agree (left right : Subst) :
    ∀ targets : List Ty,
      (∀ varId, varId ∈ Ty.fcvList targets →
        left.cap varId = right.cap varId) →
      (∀ varId, varId ∈ Ty.ftvList targets →
        left.target varId = right.target varId) →
      Ty.applyTargetList left.target
          (Ty.applyCapabilityList left.cap targets) =
        Ty.applyTargetList right.target
          (Ty.applyCapabilityList right.cap targets)
  | [], _, _ => rfl
  | target :: targets, capAgree, tyAgree => by
      simp only [Ty.applyCapabilityList, Ty.applyTargetList]
      congr 1
      · exact Subst.apply_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [Ty.fcvList, membership]))
          (fun varId membership => tyAgree varId (by
            simp [Ty.ftvList, membership]))
      · exact Subst.applyList_eq_of_free_agree left right targets
          (fun varId membership => capAgree varId (by
            simp [Ty.fcvList, membership]))
          (fun varId membership => tyAgree varId (by
            simp [Ty.ftvList, membership]))

end

/-! ## Pointwise paired-substitution composition -/

/-- Cross-sort-aware sequential composition on a dual is unconditional. -/
theorem Dual.applySubst_seq
    (later earlier : Subst) (dual : Dual) :
    dual.applySubst (Subst.seq later earlier) =
      (dual.applySubst earlier).applySubst later := by
  cases dual with
  | mk capability target =>
      change
        Dual.mk
            (capability.apply (CapSubst.comp later.cap earlier.cap))
            ((Subst.seq later earlier).apply target) =
          Dual.mk
            ((capability.apply earlier.cap).apply later.cap)
            (later.apply (earlier.apply target))
      rw [Cap.apply_comp, Subst.seq_apply]

/-- List form of unconditional sequential dual composition. -/
theorem Dual.map_applySubst_seq
    (later earlier : Subst) (duals : List Dual) :
    duals.map (Dual.applySubst (Subst.seq later earlier)) =
      (duals.map (Dual.applySubst earlier)).map
        (Dual.applySubst later) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp only [List.map_cons, Dual.applySubst_seq, induction]

/-- List form of unconditional sequential type application. -/
theorem Subst.map_apply_seq
    (later earlier : Subst) (targets : List Ty) :
    targets.map (Subst.seq later earlier).apply =
      (targets.map earlier.apply).map later.apply := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [List.map_cons, Subst.seq_apply, induction]

/-- Monomorphic contexts respect unconditional sequential composition. -/
theorem MonoCtx.applySubst_seq
    (later earlier : Subst) (context : MonoCtx) :
    context.applySubst (Subst.seq later earlier) =
      (context.applySubst earlier).applySubst later := by
  induction context with
  | nil => rfl
  | cons entry context induction =>
      cases entry with
      | mk name target =>
          simp only [MonoCtx.applySubst, List.map_cons]
          rw [Subst.seq_apply]
          congr 1

/-- Pattern-parameter contexts respect unconditional sequential composition. -/
theorem PatternCtx.applySubst_seq
    (later earlier : Subst) (context : PatternCtx) :
    context.applySubst (Subst.seq later earlier) =
      (context.applySubst earlier).applySubst later := by
  induction context with
  | nil => rfl
  | cons entry context induction =>
      cases entry with
      | mk name dual =>
          simp only [PatternCtx.applySubst, List.map_cons]
          rw [Dual.applySubst_seq]
          congr 1

/-- Sequentially applying a post after identity is the post itself. -/
@[simp] theorem Subst.seq_id_right (later : Subst) :
    Subst.seq later Subst.id = later := by
  cases later
  congr <;> funext varId <;> rfl

/-- Applying a composed paired substitution to a dual is occurrence-wide. -/
theorem Dual.applySubst_comp
    (S₂ S₁ : Subst)
    (hlaterFixesEarlier :
      (Subst.mk S₂.cap S₁.target).RangeFixed)
    (dual : Dual) :
    dual.applySubst (Subst.comp S₂ S₁) =
      (dual.applySubst S₁).applySubst S₂ := by
  cases dual with
  | mk capability target =>
      change
        Dual.mk
            (capability.apply (CapSubst.comp S₂.cap S₁.cap))
            ((Subst.comp S₂ S₁).apply target) =
          Dual.mk
            ((capability.apply S₁.cap).apply S₂.cap)
            (S₂.apply (S₁.apply target))
      rw [Cap.apply_comp S₂.cap S₁.cap capability,
        Subst.apply_comp S₂ S₁ hlaterFixesEarlier target]

/-- List form of occurrence-wide dual composition. -/
theorem Dual.map_applySubst_comp
    (S₂ S₁ : Subst)
    (hlaterFixesEarlier :
      (Subst.mk S₂.cap S₁.target).RangeFixed)
    (duals : List Dual) :
    duals.map (Dual.applySubst (Subst.comp S₂ S₁)) =
      (duals.map (Dual.applySubst S₁)).map (Dual.applySubst S₂) := by
  induction duals with
  | nil => rfl
  | cons dual duals ih =>
      simp only [List.map_cons, Dual.applySubst_comp S₂ S₁
        hlaterFixesEarlier, ih]

/-- Monomorphic contexts compose whenever paired type application composes. -/
theorem MonoCtx.applySubst_comp
    (S₂ S₁ : Subst)
    (hlaterFixesEarlier :
      (Subst.mk S₂.cap S₁.target).RangeFixed)
    (context : MonoCtx) :
    context.applySubst (Subst.comp S₂ S₁) =
      (context.applySubst S₁).applySubst S₂ := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      cases entry with
      | mk name target =>
          simp only [MonoCtx.applySubst, List.map_cons]
          rw [Subst.apply_comp S₂ S₁ hlaterFixesEarlier target]
          congr 1

/-- Pattern-parameter dual contexts compose occurrence-wide. -/
theorem PatternCtx.applySubst_comp
    (S₂ S₁ : Subst)
    (hlaterFixesEarlier :
      (Subst.mk S₂.cap S₁.target).RangeFixed)
    (context : PatternCtx) :
    context.applySubst (Subst.comp S₂ S₁) =
      (context.applySubst S₁).applySubst S₂ := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      cases entry with
      | mk name dual =>
          simp only [PatternCtx.applySubst, List.map_cons]
          rw [Dual.applySubst_comp S₂ S₁ hlaterFixesEarlier dual]
          congr 1

/-! ## Scheme masking and context lookup -/

/-- Masking at an empty capability-binder list is the identity. -/
@[simp] theorem CapSubst.mask_nil (C : CapSubst) : C.mask [] = C := by
  funext varId
  simp [CapSubst.mask]

/-- Masking at an empty target-binder list is the identity. -/
@[simp] theorem TySubst.mask_nil (T : TySubst) : T.mask [] = T := by
  funext varId
  simp [TySubst.mask]

/-- Fixing a scheme's free variables fixes its capture-avoiding body. -/
theorem Scheme.applySubst_eq_self_of_free_fixed
    (post : Subst) (scheme : Scheme)
    (capFixed : ∀ varId, varId ∈ scheme.fcv →
      post.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ scheme.ftv →
      post.target varId = .var varId) :
    scheme.applySubst post = scheme := by
  cases scheme with
  | mk capBinders tyBinders body =>
      change
        Scheme.mk capBinders tyBinders
            ((Subst.mk (post.cap.mask capBinders)
              (post.target.mask tyBinders)).apply body) =
          Scheme.mk capBinders tyBinders body
      congr 1
      apply Subst.apply_eq_self_of_free_fixed
      · intro varId membership
        by_cases bound : varId ∈ capBinders
        · simp [CapSubst.mask, bound]
        · simp only [CapSubst.mask, bound, if_false]
          apply capFixed varId
          exact List.mem_filter.mpr ⟨membership, by simp [bound]⟩
      · intro varId membership
        by_cases bound : varId ∈ tyBinders
        · simp [TySubst.mask, bound]
        · simp only [TySubst.mask, bound, if_false]
          apply tyFixed varId
          exact List.mem_filter.mpr ⟨membership, by simp [bound]⟩

/-- Fixing all free variables of a context fixes the entire context. -/
theorem Context.applySubst_eq_self_of_free_fixed
    (post : Subst) (context : Context)
    (capFixed : ∀ varId, varId ∈ context.fcv →
      post.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ context.ftv →
      post.target varId = .var varId) :
    context.applySubst post = context := by
  induction context with
  | nil => rfl
  | cons entry context induction =>
      cases entry with
      | mk name scheme =>
          simp only [Context.applySubst, List.map_cons]
          rw [Scheme.applySubst_eq_self_of_free_fixed post scheme]
          · congr 1
            apply induction
            · intro varId membership
              apply capFixed varId
              simp only [Context.fcv, List.flatMap_cons,
                List.mem_append]
              exact Or.inr membership
            · intro varId membership
              apply tyFixed varId
              simp only [Context.ftv, List.flatMap_cons,
                List.mem_append]
              exact Or.inr membership
          · intro varId membership
            exact capFixed varId (by
              simp [Context.fcv, membership])
          · intro varId membership
            exact tyFixed varId (by
              simp [Context.ftv, membership])

/-! ## Signature-aware generalized value instances -/

/-- A constructor scheme's free capability names occur among all its names. -/
theorem CtorScheme.mem_capVars_of_mem_fcv
    (scheme : CtorScheme) {varId : CapVar}
    (membership : varId ∈ scheme.fcv) :
    varId ∈ scheme.capVars := by
  unfold CtorScheme.fcv at membership
  unfold CtorScheme.capVars
  simp only [List.mem_append] at ⊢
  have rawMembership := List.mem_append.mp
    (List.mem_filter.mp membership).1
  rcases rawMembership with argumentMembership | resultMembership
  · exact Or.inl (Or.inr argumentMembership)
  · exact Or.inr resultMembership

/-- A constructor scheme's free ordinary names occur among all its names. -/
theorem CtorScheme.mem_tyVars_of_mem_ftv
    (scheme : CtorScheme) {varId : TypePM.TyVar}
    (membership : varId ∈ scheme.ftv) :
    varId ∈ scheme.tyVars := by
  unfold CtorScheme.ftv at membership
  unfold CtorScheme.tyVars
  simp only [List.mem_append] at ⊢
  have rawMembership := List.mem_append.mp
    (List.mem_filter.mp membership).1
  rcases rawMembership with argumentMembership | resultMembership
  · exact Or.inl (Or.inr argumentMembership)
  · exact Or.inr resultMembership

/-- A dual scheme's free capability names occur among all its names. -/
theorem DualScheme.mem_capVars_of_mem_fcv
    (scheme : DualScheme) {varId : CapVar}
    (membership : varId ∈ scheme.fcv) :
    varId ∈ scheme.capVars := by
  unfold DualScheme.fcv at membership
  unfold DualScheme.capVars
  have bodyMembership := (List.mem_filter.mp membership).1
  simp only [Dual.fcv, List.mem_append] at bodyMembership ⊢
  rcases bodyMembership with argumentMembership | resultCapMembership |
    resultTargetMembership
  · exact Or.inl (Or.inl (Or.inr argumentMembership))
  · exact Or.inl (Or.inr resultCapMembership)
  · exact Or.inr resultTargetMembership

/-- A dual scheme's free ordinary names occur among all its names. -/
theorem DualScheme.mem_tyVars_of_mem_ftv
    (scheme : DualScheme) {varId : TypePM.TyVar}
    (membership : varId ∈ scheme.ftv) :
    varId ∈ scheme.tyVars := by
  unfold DualScheme.ftv at membership
  unfold DualScheme.tyVars
  simp only [List.mem_append] at ⊢
  have rawMembership := List.mem_append.mp
    (List.mem_filter.mp membership).1
  rcases rawMembership with argumentMembership | resultMembership
  · exact Or.inl (Or.inr argumentMembership)
  · exact Or.inr resultMembership

/-- An expression scheme's free capability names occur among all its names. -/
theorem Scheme.mem_allCapVars_of_mem_fcv
    (scheme : Scheme) {varId : CapVar}
    (membership : varId ∈ scheme.fcv) :
    varId ∈ scheme.allCapVars := by
  unfold Scheme.fcv at membership
  unfold Scheme.allCapVars
  exact List.mem_append.mpr (Or.inr (List.mem_filter.mp membership).1)

/-- An expression scheme's free ordinary names occur among all its names. -/
theorem Scheme.mem_allTyVars_of_mem_ftv
    (scheme : Scheme) {varId : TypePM.TyVar}
    (membership : varId ∈ scheme.ftv) :
    varId ∈ scheme.allTyVars := by
  unfold Scheme.ftv at membership
  unfold Scheme.allTyVars
  exact List.mem_append.mpr (Or.inr (List.mem_filter.mp membership).1)

/-! Lookup membership in the frozen signature's free-variable scopes. -/

theorem FrozenSig.dataCtor_fcv_mem
    {signature : FrozenSig} {name : String} {scheme : CtorScheme}
    (lookup : signature.findDataCtor name = some scheme)
    {varId : CapVar} (membership : varId ∈ scheme.fcv) :
    varId ∈ signature.fcv := by
  unfold FrozenSig.findDataCtor at lookup
  cases found : signature.dataCtors.find? (fun entry => entry.1 == name) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.fcv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember, membership⟩))

theorem FrozenSig.dataCtor_ftv_mem
    {signature : FrozenSig} {name : String} {scheme : CtorScheme}
    (lookup : signature.findDataCtor name = some scheme)
    {varId : TypePM.TyVar} (membership : varId ∈ scheme.ftv) :
    varId ∈ signature.ftv := by
  unfold FrozenSig.findDataCtor at lookup
  cases found : signature.dataCtors.find? (fun entry => entry.1 == name) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.ftv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember, membership⟩))

theorem FrozenSig.patternCtor_fcv_mem
    {signature : FrozenSig} {name : String}
    {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    {varId : CapVar} (membership : varId ∈ entry.scheme.fcv) :
    varId ∈ signature.fcv := by
  unfold FrozenSig.findPatternCtor at lookup
  cases found : signature.patternCtors.find?
      (fun candidate => candidate.1 == name) with
  | none => simp [found] at lookup
  | some foundEntry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have entryEquality : foundEntry.2 = entry := Option.some.inj lookup
      subst entry
      simp only [FrozenSig.fcv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr
        ⟨foundEntry, entryMember, membership⟩))

theorem FrozenSig.patternCtor_ftv_mem
    {signature : FrozenSig} {name : String}
    {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    {varId : TypePM.TyVar} (membership : varId ∈ entry.scheme.ftv) :
    varId ∈ signature.ftv := by
  unfold FrozenSig.findPatternCtor at lookup
  cases found : signature.patternCtors.find?
      (fun candidate => candidate.1 == name) with
  | none => simp [found] at lookup
  | some foundEntry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have entryEquality : foundEntry.2 = entry := Option.some.inj lookup
      subst entry
      simp only [FrozenSig.ftv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr
        ⟨foundEntry, entryMember, membership⟩))

theorem FrozenSig.patternFun_fcv_mem
    {signature : FrozenSig} {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    {varId : CapVar} (membership : varId ∈ scheme.fcv) :
    varId ∈ signature.fcv := by
  unfold FrozenSig.findPatternFun at lookup
  cases found : signature.patternFuns.find?
      (fun entry => entry.1 == name) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.fcv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨entry, entryMember, membership⟩)

theorem FrozenSig.patternFun_ftv_mem
    {signature : FrozenSig} {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    {varId : TypePM.TyVar} (membership : varId ∈ scheme.ftv) :
    varId ∈ signature.ftv := by
  unfold FrozenSig.findPatternFun at lookup
  cases found : signature.patternFuns.find?
      (fun entry => entry.1 == name) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.ftv, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨entry, entryMember, membership⟩)

theorem FrozenSig.primitive_fcv_mem
    {signature : FrozenSig} {op : PrimOp} {scheme : CtorScheme}
    (lookup : signature.findPrimitive op = some scheme)
    {varId : CapVar} (membership : varId ∈ scheme.fcv) :
    varId ∈ signature.fcv := by
  unfold FrozenSig.findPrimitive at lookup
  cases found : signature.primitives.find?
      (fun entry => entry.1 == op) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.fcv, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨entry, entryMember, membership⟩

theorem FrozenSig.primitive_ftv_mem
    {signature : FrozenSig} {op : PrimOp} {scheme : CtorScheme}
    (lookup : signature.findPrimitive op = some scheme)
    {varId : TypePM.TyVar} (membership : varId ∈ scheme.ftv) :
    varId ∈ signature.ftv := by
  unfold FrozenSig.findPrimitive at lookup
  cases found : signature.primitives.find?
      (fun entry => entry.1 == op) with
  | none => simp [found] at lookup
  | some entry =>
      simp only [found, Option.map] at lookup
      have entryMember := List.mem_of_find?_eq_some found
      have schemeEquality : entry.2 = scheme := Option.some.inj lookup
      subst scheme
      simp only [FrozenSig.ftv, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨entry, entryMember, membership⟩

/-- Lookup after context substitution returns the substituted lookup result. -/
theorem Context.find?_applySubst
    (S : Subst) (context : Context) (name : String) :
    (context.applySubst S).find? name =
      (context.find? name).map (Scheme.applySubst S) := by
  simp [Context.applySubst, Context.find?, Function.comp_def,
    Option.map_map]

/-! ## Algebraic composition of instantiation witnesses -/

/--
Concrete, non-circular witness for transporting one scheme instantiation.
The final equation is substitution algebra; it does not assume an `Inst` or
source-typing conclusion for the transported term.
-/
structure Scheme.InstCompositionAt
    (external : Subst) (scheme : Scheme)
    (originalCap : CapSubst) (originalTarget : TySubst) where
  composedCap : CapSubst
  composedTarget : TySubst
  capSupport : composedCap.SupportWithin scheme.capBinders
  targetSupport : composedTarget.SupportWithin scheme.tyBinders
  rangeFixed : (Subst.mk composedCap composedTarget).RangeFixed
  bodyEquation :
    (Subst.mk composedCap composedTarget).apply
        (scheme.applySubst external).body =
      external.apply
        ((Subst.mk originalCap originalTarget).apply scheme.body)

/-- An algebraic composition witness transports an explicit instantiation. -/
theorem Scheme.InstAt.transport
    {external : Subst} {scheme : Scheme} {target : Ty}
    {C : CapSubst} {T : TySubst}
    (typing : scheme.InstAt C T target)
    (composition : scheme.InstCompositionAt external C T) :
    (scheme.applySubst external).Inst (external.apply target) := by
  refine ⟨composition.composedCap, composition.composedTarget,
    composition.capSupport, composition.targetSupport,
    composition.rangeFixed, ?_⟩
  calc
    (Subst.mk composition.composedCap composition.composedTarget).apply
        (scheme.applySubst external).body =
        external.apply ((Subst.mk C T).apply scheme.body) :=
      composition.bodyEquation
    _ = external.apply target := by rw [typing.2.2.2]

/-- Closed/fixed schemes and results transport with the original witness. -/
theorem Scheme.InstAt.transport_of_fixed
    {external : Subst} {scheme : Scheme} {target : Ty}
    {C : CapSubst} {T : TySubst}
    (typing : scheme.InstAt C T target)
    (schemeFixed : scheme.applySubst external = scheme)
    (targetFixed : external.apply target = target) :
    (scheme.applySubst external).Inst (external.apply target) := by
  refine ⟨C, T, typing.1, typing.2.1, typing.2.2.1, ?_⟩
  rw [schemeFixed, typing.2.2.2, targetFixed]

/-- Identity external substitution supplies an explicit composition witness. -/
def Scheme.InstAt.identityComposition
    {scheme : Scheme} {target : Ty} {C : CapSubst} {T : TySubst}
    (typing : scheme.InstAt C T target) :
    scheme.InstCompositionAt Subst.id C T where
  composedCap := C
  composedTarget := T
  capSupport := typing.1
  targetSupport := typing.2.1
  rangeFixed := typing.2.2.1
  bodyEquation := by
    rw [Scheme.applySubst_id, Subst.apply_id]

/-- Every fresh instantiation witness can be algebraically composed. -/
def Scheme.InstCompositionAdm
    (external : Subst) (scheme : Scheme) : Prop :=
  ∀ C T,
    C.SupportWithin scheme.capBinders →
    T.SupportWithin scheme.tyBinders →
    (Subst.mk C T).RangeFixed →
    Nonempty (scheme.InstCompositionAt external C T)

/-- Scheme instantiation is covariant under an algebraic composition proof. -/
theorem Scheme.Inst.transport
    {external : Subst} {scheme : Scheme} {target : Ty}
    (typing : scheme.Inst target)
    (admissible : scheme.InstCompositionAdm external) :
    (scheme.applySubst external).Inst (external.apply target) := by
  rcases typing with ⟨C, T, hcap, htarget, hrange, hbody⟩
  obtain ⟨composition⟩ := admissible C T hcap htarget hrange
  exact Scheme.InstAt.transport
    ⟨hcap, htarget, hrange, hbody⟩ composition

/-- Identity substitution composes with every scheme instantiation witness. -/
theorem Scheme.instCompositionAdm_id (scheme : Scheme) :
    scheme.InstCompositionAdm Subst.id := by
  intro C T hcap htarget hrange
  have explicit : scheme.InstAt C T ((Subst.mk C T).apply scheme.body) :=
    ⟨hcap, htarget, hrange, rfl⟩
  exact ⟨explicit.identityComposition⟩

/-! ### Declarative capability-variable/structural-target value flow -/

/-- Compose an external capability action only at local scheme binders. -/
def Scheme.postCap
    (external : Subst) (scheme : Scheme) (original : CapSubst) : CapSubst :=
  fun varId =>
    if varId ∈ scheme.capBinders then
      (original varId).apply external.cap
    else
      .var varId

/-- Compose the ordered external action only at local target binders. -/
def Scheme.postTarget
    (external : Subst) (scheme : Scheme) (original : TySubst) : TySubst :=
  fun varId =>
    if varId ∈ scheme.tyBinders then
      external.apply (original varId)
    else
      .var varId

theorem Scheme.postCap_support
    (external : Subst) (scheme : Scheme) (original : CapSubst) :
    (scheme.postCap external original).SupportWithin scheme.capBinders := by
  intro varId outside
  simp [Scheme.postCap, outside]

theorem Scheme.postTarget_support
    (external : Subst) (scheme : Scheme) (original : TySubst) :
    (scheme.postTarget external original).SupportWithin scheme.tyBinders := by
  intro varId outside
  simp [Scheme.postTarget, outside]

/--
Binder-local composition agrees with sequential application on a scheme body
when the external substitution fixes the scheme's genuinely free variables.
-/
theorem Scheme.post_apply
    {external : Subst} {scheme : Scheme}
    {originalCap : CapSubst} {originalTarget : TySubst}
    (originalCapSupport : originalCap.SupportWithin scheme.capBinders)
    (originalTargetSupport : originalTarget.SupportWithin scheme.tyBinders)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId) :
    (Subst.mk (scheme.postCap external originalCap)
        (scheme.postTarget external originalTarget)).apply scheme.body =
      external.apply
        ((Subst.mk originalCap originalTarget).apply scheme.body) := by
  rw [← Subst.seq_apply]
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    by_cases bound : varId ∈ scheme.capBinders
    · simp [Scheme.postCap, Subst.seq, CapSubst.comp, bound]
    · have free : varId ∈ scheme.fcv :=
        List.mem_filter.mpr ⟨membership, by simpa⟩
      simp only [Scheme.postCap, bound, if_false, Subst.seq,
        CapSubst.comp, originalCapSupport varId bound, Cap.apply]
      exact (externalCapFixed varId free).symm
  · intro varId membership
    by_cases bound : varId ∈ scheme.tyBinders
    · simp [Scheme.postTarget, Subst.seq, bound]
    · have free : varId ∈ scheme.ftv :=
        List.mem_filter.mpr ⟨membership, by simpa⟩
      simp only [Scheme.postTarget, bound, if_false, Subst.seq,
        originalTargetSupport varId bound, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      exact (externalTargetFixed varId free).symm

/-- Declarative value flow is closed under an ordered external action. -/
theorem Scheme.ValueFlowInst.transport
    {external : Subst} {scheme : Scheme} {target : Ty}
    (typing : scheme.ValueFlowInst target)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    (externalCapVariable : ∀ varId, ∃ image,
      external.cap varId = .var image) :
    scheme.ValueFlowInst (external.apply target) := by
  rcases typing with ⟨C, T, instanceTyping⟩
  refine ⟨scheme.postCap external C, scheme.postTarget external T, ?_⟩
  refine
    { capSupport := scheme.postCap_support external C
      tySupport := scheme.postTarget_support external T
      capBinderVariable := ?_
      result := ?_ }
  · intro varId membership
    rcases instanceTyping.capBinderVariable varId membership with
      ⟨middle, middleEquation⟩
    rcases externalCapVariable middle with ⟨image, imageEquation⟩
    exact ⟨image, by
      simp [Scheme.postCap, membership, middleEquation, Cap.apply,
        imageEquation]⟩
  · rw [Scheme.post_apply instanceTyping.capSupport instanceTyping.tySupport
      externalCapFixed externalTargetFixed, instanceTyping.result]

/-! ### Frozen constructor and dual-scheme instances -/

/-- A variable of a member target occurs in the corresponding target list. -/
theorem Ty.mem_fcvList_of_mem
    {target : Ty} {targets : List Ty} (targetMember : target ∈ targets)
    {varId : CapVar} (variableMember : varId ∈ target.fcv) :
    varId ∈ Ty.fcvList targets := by
  induction targets with
  | nil => contradiction
  | cons head tail induction =>
      simp only [List.mem_cons] at targetMember
      simp only [Ty.fcvList, List.mem_append]
      rcases targetMember with rfl | targetMember
      · exact Or.inl variableMember
      · exact Or.inr (induction targetMember)

/-- Ordinary-variable counterpart of `Ty.mem_fcvList_of_mem`. -/
theorem Ty.mem_ftvList_of_mem
    {target : Ty} {targets : List Ty} (targetMember : target ∈ targets)
    {varId : TypePM.TyVar} (variableMember : varId ∈ target.ftv) :
    varId ∈ Ty.ftvList targets := by
  induction targets with
  | nil => contradiction
  | cons head tail induction =>
      simp only [List.mem_cons] at targetMember
      simp only [Ty.ftvList, List.mem_append]
      rcases targetMember with rfl | targetMember
      · exact Or.inl variableMember
      · exact Or.inr (induction targetMember)

/--
Re-encode external capability action only at a constructor's local binders.
Names outside the binder list stay untouched, including numerically equal
binders belonging to another declaration.
-/
def CtorScheme.postCap
    (external : Subst) (scheme : CtorScheme) (original : CapSubst) :
    CapSubst :=
  fun varId =>
    if varId ∈ scheme.capBinders then
      (original varId).apply external.cap
    else
      .var varId

/-- Ordered target counterpart of `CtorScheme.postCap`. -/
def CtorScheme.postTarget
    (external : Subst) (scheme : CtorScheme) (original : TySubst) :
    TySubst :=
  fun varId =>
    if varId ∈ scheme.tyBinders then
      external.apply (original varId)
    else
      .var varId

theorem CtorScheme.postCap_support
    (external : Subst) (scheme : CtorScheme) (original : CapSubst) :
    (scheme.postCap external original).SupportWithin scheme.capBinders := by
  intro varId outside
  simp [CtorScheme.postCap, outside]

theorem CtorScheme.postTarget_support
    (external : Subst) (scheme : CtorScheme) (original : TySubst) :
    (scheme.postTarget external original).SupportWithin scheme.tyBinders := by
  intro varId outside
  simp [CtorScheme.postTarget, outside]

/--
The binder-local re-encoding agrees with sequential external application on
one constructor target.  Only genuinely free declaration variables need to
be fixed; no combined range-fixed equation is used.
-/
theorem CtorScheme.post_apply
    {external : Subst} {scheme : CtorScheme}
    {originalCap : CapSubst} {originalTarget : TySubst}
    (originalCapSupport : originalCap.SupportWithin scheme.capBinders)
    (originalTargetSupport : originalTarget.SupportWithin scheme.tyBinders)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    {target : Ty}
    (targetCapVars : ∀ varId, varId ∈ target.fcv →
      varId ∈ Ty.fcvList scheme.args ++ scheme.result.fcv)
    (targetTyVars : ∀ varId, varId ∈ target.ftv →
      varId ∈ Ty.ftvList scheme.args ++ scheme.result.ftv) :
    (Subst.mk (scheme.postCap external originalCap)
        (scheme.postTarget external originalTarget)).apply target =
      external.apply ((Subst.mk originalCap originalTarget).apply target) := by
  rw [← Subst.seq_apply]
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    by_cases bound : varId ∈ scheme.capBinders
    · simp [CtorScheme.postCap, Subst.seq, CapSubst.comp, bound]
    · have free : varId ∈ scheme.fcv := by
        exact List.mem_filter.mpr ⟨targetCapVars varId membership, by simpa⟩
      simp only [CtorScheme.postCap, bound, if_false, Subst.seq,
        CapSubst.comp, originalCapSupport varId bound, Cap.apply]
      exact (externalCapFixed varId free).symm
  · intro varId membership
    by_cases bound : varId ∈ scheme.tyBinders
    · simp [CtorScheme.postTarget, Subst.seq, bound]
    · have free : varId ∈ scheme.ftv := by
        exact List.mem_filter.mpr ⟨targetTyVars varId membership, by simpa⟩
      simp only [CtorScheme.postTarget, bound, if_false, Subst.seq,
        originalTargetSupport varId bound, Subst.apply, Ty.applyCapability,
        Ty.applyTarget]
      exact (externalTargetFixed varId free).symm

/--
Algebraic composition for one frozen ordinary constructor instance.  The
signature scheme itself stays frozen; only its fresh instance is composed.
-/
def CtorScheme.InstCompositionAt
    (external : Subst) (scheme : CtorScheme)
    (originalCap : CapSubst) (originalTarget : TySubst) : Prop :=
  ∃ composedCap composedTarget,
    composedCap.SupportWithin scheme.capBinders ∧
    composedTarget.SupportWithin scheme.tyBinders ∧
    scheme.args.map (Subst.mk composedCap composedTarget).apply =
      (scheme.args.map (Subst.mk originalCap originalTarget).apply).map
        external.apply ∧
    (Subst.mk composedCap composedTarget).apply scheme.result =
      external.apply
        ((Subst.mk originalCap originalTarget).apply scheme.result)

/-- Every fresh ordinary instance admits the required algebraic composition. -/
def CtorScheme.InstCompositionAdm
    (external : Subst) (scheme : CtorScheme) : Prop :=
  ∀ C T,
    C.SupportWithin scheme.capBinders →
    T.SupportWithin scheme.tyBinders →
    scheme.InstCompositionAt external C T

/-- Frozen constructor instantiation composes without a typing assumption. -/
theorem CtorScheme.Inst.transport
    {external : Subst} {scheme : CtorScheme}
    {args : List Ty} {result : Ty}
    (typing : scheme.Inst args result)
    (admissible : scheme.InstCompositionAdm external) :
    scheme.Inst (args.map external.apply) (external.apply result) := by
  rcases typing with ⟨C, T, hcap, htarget, hargs, hresult⟩
  rcases admissible C T hcap htarget with
    ⟨composedCap, composedTarget, hcomposedCap, hcomposedTarget,
      hcomposedArgs, hcomposedResult⟩
  refine ⟨composedCap, composedTarget, hcomposedCap, hcomposedTarget,
    ?_, ?_⟩
  · rw [hcomposedArgs, hargs]
  · rw [hcomposedResult, hresult]

/-- Identity composes every frozen ordinary constructor instance. -/
theorem CtorScheme.instCompositionAdm_id (scheme : CtorScheme) :
    scheme.InstCompositionAdm Subst.id := by
  intro C T hcap htarget
  refine ⟨C, T, hcap, htarget, ?_, ?_⟩
  · simp [Subst.apply_id]
  · rw [Subst.apply_id]

/--
Every ordered external post that fixes a declaration's free names composes
with its binder-local constructor instance.  Binder identifiers may collide
with identifiers outside the declaration; masking occurs before composition.
-/
theorem CtorScheme.instCompositionAdm_of_free_fixed
    {external : Subst} {scheme : CtorScheme}
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId) :
    scheme.InstCompositionAdm external := by
  intro C T capSupport targetSupport
  refine ⟨scheme.postCap external C, scheme.postTarget external T,
    scheme.postCap_support external C,
    scheme.postTarget_support external T, ?_, ?_⟩
  · rw [List.map_map]
    apply List.map_congr_left
    intro target targetMember
    apply CtorScheme.post_apply capSupport targetSupport
        externalCapFixed externalTargetFixed
    · intro varId membership
      exact List.mem_append_left _
        (Ty.mem_fcvList_of_mem targetMember membership)
    · intro varId membership
      exact List.mem_append_left _
        (Ty.mem_ftvList_of_mem targetMember membership)
  · apply CtorScheme.post_apply capSupport targetSupport
      externalCapFixed externalTargetFixed
    · intro varId membership
      simp [membership]
    · intro varId membership
      simp [membership]

/-- Binder-local capability composition for a frozen dual scheme. -/
def DualScheme.postCap
    (external : Subst) (scheme : DualScheme) (original : CapSubst) :
    CapSubst :=
  fun varId =>
    if varId ∈ scheme.capBinders then
      (original varId).apply external.cap
    else
      .var varId

/-- Ordered target counterpart of `DualScheme.postCap`. -/
def DualScheme.postTarget
    (external : Subst) (scheme : DualScheme) (original : TySubst) :
    TySubst :=
  fun varId =>
    if varId ∈ scheme.tyBinders then
      external.apply (original varId)
    else
      .var varId

theorem DualScheme.postCap_support
    (external : Subst) (scheme : DualScheme) (original : CapSubst) :
    (scheme.postCap external original).SupportWithin scheme.capBinders := by
  intro varId outside
  simp [DualScheme.postCap, outside]

theorem DualScheme.postTarget_support
    (external : Subst) (scheme : DualScheme) (original : TySubst) :
    (scheme.postTarget external original).SupportWithin scheme.tyBinders := by
  intro varId outside
  simp [DualScheme.postTarget, outside]

/-- A binder-local dual instance agrees with ordered external application. -/
theorem DualScheme.post_apply
    {external : Subst} {scheme : DualScheme}
    {originalCap : CapSubst} {originalTarget : TySubst}
    (originalCapSupport : originalCap.SupportWithin scheme.capBinders)
    (originalTargetSupport : originalTarget.SupportWithin scheme.tyBinders)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    {dual : Dual}
    (dualCapVars : ∀ varId, varId ∈ dual.fcv →
      varId ∈ scheme.args.flatMap Dual.fcv ++ scheme.result.fcv)
    (dualTyVars : ∀ varId, varId ∈ dual.ftv →
      varId ∈ scheme.args.flatMap Dual.ftv ++ scheme.result.ftv) :
    dual.apply (scheme.postCap external originalCap)
        (scheme.postTarget external originalTarget) =
      (dual.apply originalCap originalTarget).applySubst external := by
  cases dual with
  | mk capability target =>
      simp only [Dual.apply, Dual.applySubst]
      congr 1
      · rw [← Cap.apply_comp]
        apply Cap.apply_eq_of_fcv_agree
        intro varId membership
        by_cases bound : varId ∈ scheme.capBinders
        · simp [DualScheme.postCap, CapSubst.comp, bound]
        · have free : varId ∈ scheme.fcv := by
            apply List.mem_filter.mpr
            exact ⟨dualCapVars varId (by
              simp [Dual.fcv, membership]), by simpa⟩
          simp only [DualScheme.postCap, bound, if_false, CapSubst.comp,
            originalCapSupport varId bound, Cap.apply]
          exact (externalCapFixed varId free).symm
      · rw [← Subst.seq_apply]
        apply Subst.apply_eq_of_free_agree
        · intro varId membership
          by_cases bound : varId ∈ scheme.capBinders
          · simp [DualScheme.postCap, Subst.seq, CapSubst.comp, bound]
          · have free : varId ∈ scheme.fcv := by
              apply List.mem_filter.mpr
              exact ⟨dualCapVars varId (by
                simp [Dual.fcv, membership]), by simpa⟩
            simp only [DualScheme.postCap, bound, if_false, Subst.seq,
              CapSubst.comp, originalCapSupport varId bound, Cap.apply]
            exact (externalCapFixed varId free).symm
        · intro varId membership
          by_cases bound : varId ∈ scheme.tyBinders
          · simp [DualScheme.postTarget, Subst.seq, bound]
          · have free : varId ∈ scheme.ftv := by
              apply List.mem_filter.mpr
              exact ⟨dualTyVars varId membership, by simpa⟩
            simp only [DualScheme.postTarget, bound, if_false, Subst.seq,
              originalTargetSupport varId bound, Subst.apply,
              Ty.applyCapability, Ty.applyTarget]
            exact (externalTargetFixed varId free).symm

/-- Algebraic composition for a separately quantified pattern-function dual. -/
def DualScheme.InstCompositionAt
    (external : Subst) (scheme : DualScheme)
    (originalCap : CapSubst) (originalTarget : TySubst) : Prop :=
  ∃ composedCap composedTarget,
    composedCap.SupportWithin scheme.capBinders ∧
    composedTarget.SupportWithin scheme.tyBinders ∧
    scheme.args.map (Dual.apply composedCap composedTarget) =
      (scheme.args.map (Dual.apply originalCap originalTarget)).map
        (Dual.applySubst external) ∧
    scheme.result.apply composedCap composedTarget =
      (scheme.result.apply originalCap originalTarget).applySubst external

/-- Every fresh dual instance admits the required algebraic composition. -/
def DualScheme.InstCompositionAdm
    (external : Subst) (scheme : DualScheme) : Prop :=
  ∀ C T,
    C.SupportWithin scheme.capBinders →
    T.SupportWithin scheme.tyBinders →
    scheme.InstCompositionAt external C T

/-- Frozen dual-scheme instantiation composes occurrence-wide. -/
theorem DualScheme.Inst.transport
    {external : Subst} {scheme : DualScheme}
    {args : List Dual} {result : Dual}
    (typing : scheme.Inst args result)
    (admissible : scheme.InstCompositionAdm external) :
    scheme.Inst (args.map (Dual.applySubst external))
      (result.applySubst external) := by
  rcases typing with ⟨C, T, hcap, htarget, hargs, hresult⟩
  rcases admissible C T hcap htarget with
    ⟨composedCap, composedTarget, hcomposedCap, hcomposedTarget,
      hcomposedArgs, hcomposedResult⟩
  refine ⟨composedCap, composedTarget, hcomposedCap, hcomposedTarget,
    ?_, ?_⟩
  · rw [hcomposedArgs, hargs]
  · rw [hcomposedResult, hresult]

/-- Identity composes every frozen dual-scheme instance. -/
theorem DualScheme.instCompositionAdm_id (scheme : DualScheme) :
    scheme.InstCompositionAdm Subst.id := by
  intro C T hcap htarget
  refine ⟨C, T, hcap, htarget, ?_, ?_⟩
  · simp [Dual.applySubst_id]
  · rw [Dual.applySubst_id]

/-- Free-name fixing suffices for ordered binder-local dual composition. -/
theorem DualScheme.instCompositionAdm_of_free_fixed
    {external : Subst} {scheme : DualScheme}
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId) :
    scheme.InstCompositionAdm external := by
  intro C T capSupport targetSupport
  refine ⟨scheme.postCap external C, scheme.postTarget external T,
    scheme.postCap_support external C,
    scheme.postTarget_support external T, ?_, ?_⟩
  · rw [List.map_map]
    apply List.map_congr_left
    intro dual dualMember
    apply DualScheme.post_apply capSupport targetSupport
        externalCapFixed externalTargetFixed
    · intro varId membership
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨dual, dualMember, membership⟩
    · intro varId membership
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨dual, dualMember, membership⟩
  · apply DualScheme.post_apply capSupport targetSupport
      externalCapFixed externalTargetFixed
    · intro varId membership
      simp [membership]
    · intro varId membership
      simp [membership]

/-- Declarative dual value flow is closed under an ordered external action. -/
theorem DualScheme.ValueFlowInst.transport
    {external : Subst} {scheme : DualScheme}
    {args : List Dual} {result : Dual}
    (typing : scheme.ValueFlowInst args result)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    (externalCapVariable : ∀ varId, ∃ image,
      external.cap varId = .var image) :
    scheme.ValueFlowInst (args.map (Dual.applySubst external))
      (result.applySubst external) := by
  rcases typing with ⟨C, T, instanceTyping⟩
  refine ⟨scheme.postCap external C, scheme.postTarget external T, ?_⟩
  refine
    { capSupport := scheme.postCap_support external C
      tySupport := scheme.postTarget_support external T
      capBinderVariable := ?_
      argsResult := ?_
      resultResult := ?_ }
  · intro varId membership
    rcases instanceTyping.capBinderVariable varId membership with
      ⟨middle, middleEquation⟩
    rcases externalCapVariable middle with ⟨image, imageEquation⟩
    exact ⟨image, by
      simp [DualScheme.postCap, membership, middleEquation, Cap.apply,
        imageEquation]⟩
  · rw [← instanceTyping.argsResult, List.map_map]
    apply List.map_congr_left
    intro dual dualMembership
    apply DualScheme.post_apply instanceTyping.capSupport
        instanceTyping.tySupport externalCapFixed externalTargetFixed
    · intro varId variableMembership
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMembership, variableMembership⟩)
    · intro varId variableMembership
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMembership, variableMembership⟩)
  · rw [← instanceTyping.resultResult]
    apply DualScheme.post_apply instanceTyping.capSupport
        instanceTyping.tySupport externalCapFixed externalTargetFixed
    · intro varId variableMembership
      exact List.mem_append_right _ variableMembership
    · intro varId variableMembership
      exact List.mem_append_right _ variableMembership

/-! ## Clause-evidence covariance -/

mutual

/-- A successful clause-evidence worker run is capability-renaming covariant. -/
theorem clauseEvidenceGo_applyRen_of_success
    (r : CapVar → CapVar) (signature : FrozenMatcherSig) :
    ∀ (atRoot : Bool) (pattern : PPat) (capabilities : List Cap)
      (evidence : Shape.Evidence) (remaining : List Cap),
      clauseEvidenceGo signature atRoot pattern capabilities =
          some (evidence, remaining) →
      clauseEvidenceGo signature atRoot pattern
          (Cap.applyRenList r capabilities) =
        some (evidence.applyRen r, Cap.applyRenList r remaining)
  | atRoot, .hole, [], evidence, remaining, success => by
      simp [clauseEvidenceGo] at success
  | atRoot, .hole, capability :: capabilities, evidence, remaining,
      success => by
      simp only [clauseEvidenceGo, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨evidenceEquality, remainingEquality⟩
      subst evidence
      subst remaining
      cases atRoot <;>
        simp [clauseEvidenceGo, Cap.applyRenList,
          Shape.Evidence.applyRen, Shape.ofCap_applyRen]
  | atRoot, .wild, capabilities, evidence, remaining, success => by
      simp only [clauseEvidenceGo, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨evidenceEquality, remainingEquality⟩
      subst evidence
      subst remaining
      simp [clauseEvidenceGo, Shape.Evidence.applyRen]
  | atRoot, .pval name, capabilities, evidence, remaining, success => by
      simp only [clauseEvidenceGo, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨evidenceEquality, remainingEquality⟩
      subst evidence
      subst remaining
      simp [clauseEvidenceGo, Shape.Evidence.applyRen]
  | atRoot, .ctor name patterns, capabilities, evidence, remaining,
      success => by
      cases lookup : signature.findPatternConstructor? name with
      | none =>
          simp [clauseEvidenceGo, lookup] at success
      | some constructor =>
          cases childrenRun :
              clauseEvidenceListGo signature patterns capabilities with
          | none =>
              simp [clauseEvidenceGo, lookup, childrenRun] at success
          | some result =>
              rcases result with ⟨children, afterChildren⟩
              cases projection :
                  Projection.projectClauseSignature constructor children with
              | none =>
                  simp [clauseEvidenceGo, lookup, childrenRun,
                    projection] at success
              | some projected =>
                  have equality :
                      projected = evidence ∧ afterChildren = remaining := by
                    simpa [clauseEvidenceGo, lookup, childrenRun,
                      projection] using success
                  rcases equality with ⟨rfl, rfl⟩
                  have renamedChildren :=
                    clauseEvidenceListGo_applyRen_of_success r signature
                      patterns capabilities children afterChildren childrenRun
                  have renamedProjection :=
                    Projection.projectClauseSignature_rename_of_success r
                      constructor projection
                  simp [clauseEvidenceGo, lookup, renamedChildren,
                    renamedProjection]
  | atRoot, .tuple patterns, capabilities, evidence, remaining,
      success => by
      cases childrenRun :
          clauseEvidenceListGo signature patterns capabilities with
      | none =>
          simp [clauseEvidenceGo, childrenRun] at success
      | some result =>
          rcases result with ⟨children, afterChildren⟩
          have equality :
              (.prod children : Shape.Evidence) = evidence ∧
                afterChildren = remaining := by
            simpa [clauseEvidenceGo, childrenRun] using success
          rcases equality with ⟨rfl, rfl⟩
          have renamedChildren :=
            clauseEvidenceListGo_applyRen_of_success r signature
              patterns capabilities children afterChildren childrenRun
          simp [clauseEvidenceGo, renamedChildren,
            Shape.Evidence.applyRen]

/-- List worker form of clause-evidence capability covariance. -/
theorem clauseEvidenceListGo_applyRen_of_success
    (r : CapVar → CapVar) (signature : FrozenMatcherSig) :
    ∀ (patterns : List PPat) (capabilities : List Cap)
      (evidence : List Shape.Evidence) (remaining : List Cap),
      clauseEvidenceListGo signature patterns capabilities =
          some (evidence, remaining) →
      clauseEvidenceListGo signature patterns
          (Cap.applyRenList r capabilities) =
        some (Shape.Evidence.applyRenList r evidence,
          Cap.applyRenList r remaining)
  | [], capabilities, evidence, remaining, success => by
      simp only [clauseEvidenceListGo, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨evidenceEquality, remainingEquality⟩
      subst evidence
      subst remaining
      rfl
  | pattern :: patterns, capabilities, evidence, remaining, success => by
      cases headRun :
          clauseEvidenceGo signature false pattern capabilities with
      | none =>
          simp [clauseEvidenceListGo, headRun] at success
      | some headResult =>
          rcases headResult with ⟨head, afterHead⟩
          cases tailRun :
              clauseEvidenceListGo signature patterns afterHead with
          | none =>
              simp [clauseEvidenceListGo, headRun, tailRun] at success
          | some tailResult =>
              rcases tailResult with ⟨tail, afterTail⟩
              have equality :
                  head :: tail = evidence ∧ afterTail = remaining := by
                simpa [clauseEvidenceListGo, headRun, tailRun] using success
              rcases equality with ⟨rfl, rfl⟩
              have renamedHead :=
                clauseEvidenceGo_applyRen_of_success r signature false pattern
                  capabilities head afterHead headRun
              have renamedTail :=
                clauseEvidenceListGo_applyRen_of_success r signature patterns
                  afterHead tail afterTail tailRun
              simp [clauseEvidenceListGo, renamedHead, renamedTail,
                Shape.Evidence.applyRenList]

end

/-- The complete deterministic clause-evidence checker is renaming covariant. -/
theorem clauseEvidence_applyRen_of_success
    (r : CapVar → CapVar)
    {signature : FrozenMatcherSig} {pattern : PPat}
    {capabilities : List Cap} {evidence : Shape.Evidence}
    (success : clauseEvidence signature pattern capabilities = some evidence) :
    clauseEvidence signature pattern (Cap.applyRenList r capabilities) =
      some (evidence.applyRen r) := by
  have lengthEquality := clauseEvidence_holeCount success
  unfold clauseEvidence at success ⊢
  have orderCheck : pattern.coreOrderCheck = true := by
    cases checkEq : pattern.coreOrderCheck with
    | false => simp [checkEq] at success
    | true => rfl
  rw [orderCheck] at success ⊢
  simp only [if_true] at success ⊢
  rw [lengthEquality] at success
  simp only [if_true] at success
  rw [Cap.applyRenList_length, lengthEquality]
  simp only [if_true]
  have workerSuccess := finishClauseEvidence_eq_some success
  have renamedWorker :=
    clauseEvidenceGo_applyRen_of_success r signature true pattern capabilities
      evidence [] workerSuccess
  simpa [finishClauseEvidence, Cap.applyRenList] using
    congrArg finishClauseEvidence renamedWorker

/-! ## Frozen arm-checker transport -/

/-- At the closed boundary no covariance property of the checker is needed. -/
theorem ArmExhaustive.transport_of_fixed
    {signature : FrozenSig} {S : Subst}
    {clauses : List Clause} {target : Ty}
    (targetFixed : S.apply target = target)
    (exhaustive : ArmExhaustive signature clauses target) :
    ArmExhaustive signature clauses (S.apply target) := by
  simpa [targetFixed] using exhaustive

/-- Applying types pointwise does not change monomorphic binding names. -/
@[simp] theorem MonoCtx.names_applySubst
    (S : Subst) (bindings : MonoCtx) :
    (bindings.applySubst S).names = bindings.names := by
  simp [MonoCtx.applySubst, MonoCtx.names, List.map_map,
    Function.comp_def]

/-- Signature-wide algebraic transport for fresh pattern-constructor instances. -/
def FrozenSig.PatternCtorInstCompositionAdm
    (signature : FrozenSig) (S : Subst) : Prop :=
  ∀ {name : String}
    {entry : PatternCtorScheme signature.observability},
    signature.findPatternCtor name = some entry →
    entry.scheme.InstCompositionAdm S

/-- Fixing the frozen signature's free names supplies every pattern entry. -/
theorem FrozenSig.patternCtorInstCompositionAdm_of_free_fixed
    {signature : FrozenSig} {S : Subst}
    (capFixed : ∀ varId, varId ∈ signature.fcv →
      S.cap varId = .var varId)
    (targetFixed : ∀ varId, varId ∈ signature.ftv →
      S.target varId = .var varId) :
    signature.PatternCtorInstCompositionAdm S := by
  intro name entry lookup
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    exact capFixed varId (signature.patternCtor_fcv_mem lookup membership)
  · intro varId membership
    exact targetFixed varId (signature.patternCtor_ftv_mem lookup membership)

/-! ## Extending aligned primitive-pattern resolutions -/

mutual

/--
Resolve an already typed raw primitive pattern under a later post.  Raw fresh
leaves are retained; only the constructor's actual instance certificate is
composed.  Thus this lemma needs no fresh-leaf transport premise.
-/
theorem PPatTy.resolveUnder
    {signature : FrozenSig} {S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : PPatTy signature pattern target holes bindings) :
    PPatResolution signature S pattern target holes bindings := by
  cases typing with
  | hole fresh => exact PPatResolution.hole fresh
  | wild => exact PPatResolution.wild
  | pval => exact PPatResolution.pval
  | ctor lookup children instantiated =>
      exact PPatResolution.ctor lookup
        (PPatTys.resolveUnder constructorInstances children)
        instantiated
        (CtorScheme.Inst.transport instantiated
          (constructorInstances lookup))
  | tuple children =>
      exact PPatResolution.tuple
        (PPatTys.resolveUnder constructorInstances children)

/-- List form of resolving raw primitive patterns under a later post. -/
theorem PPatTys.resolveUnder
    {signature : FrozenSig} {S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : PPatTys signature patterns targets holes bindings) :
    PPatResolutions signature S patterns targets holes bindings := by
  cases typing with
  | nil => exact PPatResolutions.nil
  | cons head tail distinct =>
      exact PPatResolutions.cons
        (PPatTy.resolveUnder constructorInstances head)
        (PPatTys.resolveUnder constructorInstances tail) distinct

end

mutual

/-- Append one algebraically admissible post to an aligned PP resolution. -/
theorem PPatResolution.extend
    {signature : FrozenSig} {prevailing S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : PPatResolution signature prevailing pattern target holes
      bindings) :
    PPatResolution signature (Subst.seq S prevailing) pattern target holes
      bindings := by
  cases typing with
  | identity equality rawTyping =>
      subst prevailing
      simpa only [Subst.seq_id_right] using
        PPatTy.resolveUnder constructorInstances rawTyping
  | hole fresh => exact PPatResolution.hole fresh
  | wild => exact PPatResolution.wild
  | pval => exact PPatResolution.pval
  | ctor lookup children rawInstance actualInstance =>
      have transportedActual :=
        CtorScheme.Inst.transport actualInstance
          (constructorInstances lookup)
      exact PPatResolution.ctor lookup
        (PPatResolutions.extend constructorInstances children)
        rawInstance (by
          simpa only [PatternCtorScheme.Inst,
            Subst.map_apply_seq, Subst.seq_apply] using transportedActual)
  | tuple children =>
      exact PPatResolution.tuple
        (PPatResolutions.extend constructorInstances children)

/-- List form of appending a post to aligned PP resolutions. -/
theorem PPatResolutions.extend
    {signature : FrozenSig} {prevailing S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : PPatResolutions signature prevailing patterns targets holes
      bindings) :
    PPatResolutions signature (Subst.seq S prevailing) patterns targets holes
      bindings := by
  cases typing with
  | identity equality rawTyping =>
      subst prevailing
      simpa only [Subst.seq_id_right] using
        PPatTys.resolveUnder constructorInstances rawTyping
  | nil => exact PPatResolutions.nil
  | cons head tail distinct =>
      exact PPatResolutions.cons
        (PPatResolution.extend constructorInstances head)
        (PPatResolutions.extend constructorInstances tail) distinct

end

mutual

/-- Append one algebraically admissible post to a terminal PP resolution. -/
theorem TerminalPPatResolution.extend
    {signature : FrozenSig} {prevailing S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : TerminalPPatResolution signature prevailing pattern target holes
      bindings) :
    TerminalPPatResolution signature (Subst.seq S prevailing) pattern
      (S.apply target) (holes.map (Dual.applySubst S))
      (bindings.applySubst S) := by
  cases typing with
  | hole fresh =>
      simpa only [Subst.seq_apply, Dual.map_applySubst_seq, List.map_nil,
        MonoCtx.applySubst] using
        (TerminalPPatResolution.hole
          (prevailing := Subst.seq S prevailing) fresh)
  | wild =>
      simpa only [Subst.seq_apply, List.map_nil, MonoCtx.applySubst] using
        (TerminalPPatResolution.wild (signature := signature)
          (prevailing := Subst.seq S prevailing) (rawTarget := _))
  | pval =>
      simpa only [Subst.seq_apply, MonoCtx.applySubst_seq, List.map_nil] using
        (TerminalPPatResolution.pval (signature := signature)
          (prevailing := Subst.seq S prevailing) (rawTarget := _))
  | ctor lookup children instantiated =>
      exact TerminalPPatResolution.ctor lookup
        (TerminalPPatResolutions.extend constructorInstances children)
        (CtorScheme.Inst.transport instantiated
          (constructorInstances lookup))
  | tuple children =>
      simpa only [Subst.apply_prod] using
        TerminalPPatResolution.tuple
          (TerminalPPatResolutions.extend constructorInstances children)

/-- List form of appending a post to terminal PP resolutions. -/
theorem TerminalPPatResolutions.extend
    {signature : FrozenSig} {prevailing S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : TerminalPPatResolutions signature prevailing patterns targets
      holes bindings) :
    TerminalPPatResolutions signature (Subst.seq S prevailing) patterns
      (targets.map S.apply) (holes.map (Dual.applySubst S))
      (bindings.applySubst S) := by
  cases typing with
  | nil => exact TerminalPPatResolutions.nil
  | cons head tail distinct =>
      rename_i pattern target holes bindings patterns targets restHoles
        restBindings
      have transportedDistinct :
          ∀ name,
            name ∈ (bindings.applySubst S).names →
            name ∉ (restBindings.applySubst S).names := by
        simpa only [MonoCtx.names_applySubst] using distinct
      simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
        TerminalPPatResolutions.cons
          (TerminalPPatResolution.extend constructorInstances head)
          (TerminalPPatResolutions.extend constructorInstances tail)
          transportedDistinct

end

/-- Extend the prevailing substitution stored by an actual primitive pattern. -/
theorem ResolvedPPatTy.transport
    {signature : FrozenSig} {prevailing S : Subst}
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing pattern target holes
      bindings) :
    ResolvedPPatTy signature (Subst.seq S prevailing) pattern
      (S.apply target) (holes.map (Dual.applySubst S))
      (bindings.applySubst S) := by
  cases typing with
  | ofAligned resolution =>
      have extended := PPatResolution.extend constructorInstances resolution
      simpa only [Subst.seq_apply, Dual.map_applySubst_seq,
        MonoCtx.applySubst_seq] using
        ResolvedPPatTy.ofAligned extended
  | ofTerminal resolution =>
      exact ResolvedPPatTy.ofTerminal
        (TerminalPPatResolution.extend constructorInstances resolution)

/-! ## Capability alignment and data-pattern covariance -/

/-- Capability substitution distributes over list concatenation. -/
theorem Cap.applyList_append
    (C : CapSubst) (left right : List Cap) :
    Cap.applyList C (left ++ right) =
      Cap.applyList C left ++ Cap.applyList C right := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, Cap.applyList]
      rw [induction]

mutual

/--
Primitive-pattern capability alignment is covariant under every declarative
capability-variable post.  This is the occurrence at which the projection
covariance theorem is consumed; no target information is involved.
-/
theorem PPatCapsAt.transport
    {signature : FrozenSig} {post : Subst}
    (postVariable : VariablePost post)
    {atRoot : Bool} {pattern : PPat} {holes : List Cap}
    {capability : Cap}
    (typing : PPatCapsAt signature atRoot pattern holes capability) :
    PPatCapsAt signature atRoot pattern
      (Cap.applyList post.cap holes) (capability.apply post.cap) := by
  cases typing with
  | rootHole =>
      exact PPatCapsAt.rootHole
  | childHole =>
      exact PPatCapsAt.childHole
  | wild =>
      exact PPatCapsAt.wild
  | pval =>
      exact PPatCapsAt.pval
  | ctor lookup children compatible =>
      have transportedChildren :=
        PPatCapsList.transport postVariable children
      have renamedCompatible :=
        compatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      exact PPatCapsAt.ctor lookup transportedChildren renamedCompatible
  | tuple children =>
      exact PPatCapsAt.tuple
        (PPatCapsList.transport postVariable children)

/-- List form of certified capability-alignment covariance. -/
theorem PPatCapsList.transport
    {signature : FrozenSig} {post : Subst}
    (postVariable : VariablePost post)
    {patterns : List PPat} {holes children : List Cap}
    (typing : PPatCapsList signature patterns holes children) :
    PPatCapsList signature patterns
      (Cap.applyList post.cap holes) (Cap.applyList post.cap children) := by
  cases typing with
  | nil => exact PPatCapsList.nil
  | cons head tail =>
      simpa only [Cap.applyList, Cap.applyList_append] using
        PPatCapsList.cons
          (PPatCapsAt.transport postVariable head)
          (PPatCapsList.transport postVariable tail)

end

/-- Signature-wide algebraic transport for data-constructor instances. -/
def FrozenSig.DataCtorInstCompositionAdm
    (signature : FrozenSig) (S : Subst) : Prop :=
  ∀ {name : String} {scheme : CtorScheme},
    signature.findDataCtor name = some scheme →
    scheme.InstCompositionAdm S

/-- Fixing signature free names supplies every data-constructor instance. -/
theorem FrozenSig.dataCtorInstCompositionAdm_of_free_fixed
    {signature : FrozenSig} {S : Subst}
    (capFixed : ∀ varId, varId ∈ signature.fcv →
      S.cap varId = .var varId)
    (targetFixed : ∀ varId, varId ∈ signature.ftv →
      S.target varId = .var varId) :
    signature.DataCtorInstCompositionAdm S := by
  intro name scheme lookup
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    exact capFixed varId (signature.dataCtor_fcv_mem lookup membership)
  · intro varId membership
    exact targetFixed varId (signature.dataCtor_ftv_mem lookup membership)

mutual

/-- Data-pattern typing is covariant under constructor-instance composition. -/
theorem DPatTy.transport
    {signature : FrozenSig} {S : Subst}
    (constructorInstances : signature.DataCtorInstCompositionAdm S)
    {pattern : DPat} {target : Ty} {bindings : MonoCtx}
    (typing : DPatTy signature pattern target bindings) :
    DPatTy signature pattern (S.apply target) (bindings.applySubst S) := by
  cases typing with
  | var =>
      exact DPatTy.var
  | wild =>
      exact DPatTy.wild
  | ctor lookup children instantiated =>
      exact DPatTy.ctor lookup
        (DPatTys.transport constructorInstances children)
        (CtorScheme.Inst.transport instantiated
          (constructorInstances lookup))
  | tuple children =>
      simpa only [Subst.apply_prod] using
        DPatTy.tuple (DPatTys.transport constructorInstances children)

/-- List form of data-pattern covariance. -/
theorem DPatTys.transport
    {signature : FrozenSig} {S : Subst}
    (constructorInstances : signature.DataCtorInstCompositionAdm S)
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    (typing : DPatTys signature patterns targets bindings) :
    DPatTys signature patterns (targets.map S.apply)
      (bindings.applySubst S) := by
  cases typing with
  | nil => exact DPatTys.nil
  | cons head tail distinct =>
      rename_i pattern target bindings patterns targets restBindings
      have transportedDistinct :
          ∀ name,
            name ∈ (bindings.applySubst S).names →
            name ∉ (restBindings.applySubst S).names := by
        simpa only [MonoCtx.names_applySubst] using distinct
      simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
        DPatTys.cons
          (DPatTy.transport constructorInstances head)
          (DPatTys.transport constructorInstances tail)
          transportedDistinct

end

/-! ## Algebraic boundary for occurrence-wide source transport -/

/-- Primitive declarations need the same non-circular instance composition. -/
def FrozenSig.PrimitiveInstCompositionAdm
    (signature : FrozenSig) (S : Subst) : Prop :=
  ∀ {op : PrimOp} {scheme : CtorScheme},
    signature.findPrimitive op = some scheme →
    scheme.InstCompositionAdm S

/-- Fixing signature free names supplies every primitive instance. -/
theorem FrozenSig.primitiveInstCompositionAdm_of_free_fixed
    {signature : FrozenSig} {S : Subst}
    (capFixed : ∀ varId, varId ∈ signature.fcv →
      S.cap varId = .var varId)
    (targetFixed : ∀ varId, varId ∈ signature.ftv →
      S.target varId = .var varId) :
    signature.PrimitiveInstCompositionAdm S := by
  intro op scheme lookup
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    exact capFixed varId (signature.primitive_fcv_mem lookup membership)
  · intro varId membership
    exact targetFixed varId (signature.primitive_ftv_mem lookup membership)

/-- Pattern-context lookup commutes with pointwise paired substitution. -/
theorem PatternCtx.find?_applySubst
    (S : Subst) (context : PatternCtx) (name : String) :
    (context.applySubst S).find? name =
      (context.find? name).map (Dual.applySubst S) := by
  simp [PatternCtx.applySubst, PatternCtx.find?, Function.comp_def,
    Option.map_map]

/-- Pointwise source-context substitution distributes over concatenation. -/
theorem Context.applySubst_append
    (S : Subst) (left right : Context) :
    (left ++ right).applySubst S =
      left.applySubst S ++ right.applySubst S := by
  simp [Context.applySubst, List.map_append]

/-- Monomorphic bindings commute with their embedding as mono schemes. -/
theorem MonoCtx.toContext_applySubst
    (S : Subst) (bindings : MonoCtx) :
    (bindings.applySubst S).toContext =
      bindings.toContext.applySubst S := by
  induction bindings with
  | nil => rfl
  | cons entry bindings induction =>
      cases entry with
      | mk name target =>
          simp [MonoCtx.applySubst, MonoCtx.toContext,
            Context.applySubst, Scheme.mono, Scheme.applySubst,
            induction]

/-- Slot targets built from duals commute with paired substitution. -/
theorem Dual.map_slot_applySubst
    (S : Subst) (duals : List Dual) :
    (duals.map (Dual.applySubst S)).map
        (fun dual => Ty.slot dual.cap dual.target) =
      (duals.map (fun dual => Ty.slot dual.cap dual.target)).map S.apply := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      cases dual with
      | mk capability target =>
          simp only [List.map_cons, Dual.applySubst, Dual.cap, Dual.target,
            Dual.apply, induction]
          rfl

/-- `prodTy` commutes with occurrence-wide paired substitution. -/
theorem Subst.apply_prodTy (S : Subst) :
    ∀ targets : List Ty,
      S.apply (prodTy targets) = prodTy (targets.map S.apply)
  | [] => by simp [prodTy, Subst.apply_prod]
  | [target] => rfl
  | first :: second :: rest => by
      simp only [prodTy, Subst.apply_prod, List.map_cons]

/-! Structural paired-application equations used by the source recursor. -/

@[simp] theorem Subst.apply_unit (S : Subst) : S.apply .unit = .unit := rfl
@[simp] theorem Subst.apply_int (S : Subst) : S.apply .int = .int := rfl
@[simp] theorem Subst.apply_bool (S : Subst) : S.apply .bool = .bool := rfl

@[simp] theorem Subst.apply_fn (S : Subst) (domain codomain : Ty) :
    S.apply (.fn domain codomain) = .fn (S.apply domain) (S.apply codomain) :=
  rfl

@[simp] theorem Subst.apply_matcher
    (S : Subst) (capability : Cap) (target : Ty) :
    S.apply (.matcher capability target) =
      .matcher (capability.apply S.cap) (S.apply target) :=
  rfl

@[simp] theorem Subst.apply_slot
    (S : Subst) (capability : Cap) (target : Ty) :
    S.apply (.slot capability target) =
      .slot (capability.apply S.cap) (S.apply target) :=
  rfl

@[simp] theorem Subst.apply_listT (S : Subst) (target : Ty) :
    S.apply target.listT = (S.apply target).listT := rfl

@[simp] theorem Scheme.applySubst_mono (S : Subst) (target : Ty) :
    (Scheme.mono target).applySubst S = Scheme.mono (S.apply target) := by
  rfl

/-- Resolution packaging exposes the one shared substitution, not one per clause. -/
theorem ResolvedClausesTy.exists_shared
    {signature : FrozenSig} {context : Context} {clauses : List Clause}
    {capability : Cap} {target : Ty} {evidence : List Shape.Evidence}
    (typing :
      ResolvedClausesTy signature context clauses capability target evidence) :
    ∃ prevailing,
      ClausesTy signature prevailing context clauses capability target
        evidence := by
  cases typing with
  | ofShared clausesTyped =>
      exact ⟨_, clausesTyped⟩

end TypePM
