import TypePM.DamasMilner
import TypePM.TypeInstance
import TypePM.InferenceBase
import TypePM.PolyCloseLaws

/-!
# Executable acceptance of the Damas--Milner fragment

This module develops the one-sort substitution and environment algebra needed
by the Algorithm W completeness invariant.  The final invariant relates a DM
typing derivation, whose displayed type may be an arbitrary specialization, to
the fresh type and normalized context produced by the public two-sort
inference traversal.  It never attempts to turn `TypingInvariant` or coherent
reconstruction backwards into source acceptance.
-/

namespace TypePM
namespace DM

/-! ## One-sort substitution algebra -/

/-- Identity one-sort substitution. -/
def SSubst.id : SSubst :=
  fun name => .var name

/-- Chronological composition: apply `earlier`, then `later`. -/
def SSubst.comp (later earlier : SSubst) : SSubst :=
  fun name => (earlier name).applySubst later

@[simp] theorem SSubst.id_apply (name : TypePM.TyVar) :
    SSubst.id name = .var name := rfl

theorem SSubst.id_supportWithin (variables : List TypePM.TyVar) :
    SSubst.id.SupportWithin variables := by
  intro name _outside
  rfl

mutual

@[simp] theorem STy.applySubst_id : ∀ target : STy,
    target.applySubst SSubst.id = target
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      rw [STy.applySubst, STy.applySubst_id domain,
        STy.applySubst_id codomain]
  | .prod components => by
      rw [STy.applySubst, STy.applySubstList_id components]

@[simp] theorem STy.applySubstList_id : ∀ targets : List STy,
    STy.applySubstList SSubst.id targets = targets
  | [] => rfl
  | target :: targets => by
      rw [STy.applySubstList, STy.applySubst_id target,
        STy.applySubstList_id targets]

end

mutual

/-- Substitution application respects chronological composition. -/
theorem STy.applySubst_comp (later earlier : SSubst) : ∀ target : STy,
    (target.applySubst earlier).applySubst later =
      target.applySubst (SSubst.comp later earlier)
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      simp only [STy.applySubst]
      rw [STy.applySubst_comp later earlier domain,
        STy.applySubst_comp later earlier codomain]
  | .prod components => by
      simp only [STy.applySubst]
      rw [STy.applySubstList_comp later earlier components]

/-- List form of `STy.applySubst_comp`. -/
theorem STy.applySubstList_comp (later earlier : SSubst) :
    ∀ targets : List STy,
      STy.applySubstList later (STy.applySubstList earlier targets) =
        STy.applySubstList (SSubst.comp later earlier) targets
  | [] => rfl
  | target :: targets => by
      simp only [STy.applySubstList]
      rw [STy.applySubst_comp later earlier target,
        STy.applySubstList_comp later earlier targets]

end

/-- Composition preserves a displayed support when the later substitution is
identity on every variable that can be introduced by the earlier one outside
that support. -/
theorem SSubst.comp_supportWithin
    {later earlier : SSubst} {variables : List TypePM.TyVar}
    (earlierSupport : earlier.SupportWithin variables)
    (laterFixed : ∀ name, name ∉ variables → later name = .var name) :
    (SSubst.comp later earlier).SupportWithin variables := by
  intro name outside
  rw [SSubst.comp, earlierSupport name outside]
  simpa [STy.applySubst] using laterFixed name outside

/-- Restrict a total one-sort substitution to a finite mutable scope. -/
def SSubst.restrict (variables : List TypePM.TyVar)
    (post : SSubst) : SSubst :=
  fun name => if name ∈ variables then post name else .var name

@[simp] theorem SSubst.restrict_of_mem
    (post : SSubst) {variables : List TypePM.TyVar}
    {name : TypePM.TyVar} (member : name ∈ variables) :
    SSubst.restrict variables post name = post name := by
  simp [SSubst.restrict, member]

theorem SSubst.restrict_supportWithin
    (variables : List TypePM.TyVar) (post : SSubst) :
    (SSubst.restrict variables post).SupportWithin variables := by
  intro name outside
  simp [SSubst.restrict, outside]

mutual

/-- Substitutions agreeing on all free variables act identically. -/
theorem STy.applySubst_eq_of_ftv_agree
    {left right : SSubst} : ∀ target : STy,
    (∀ name, name ∈ target.ftv → left name = right name) →
      target.applySubst left = target.applySubst right
  | .var name, agree => by
      exact agree name (by simp [STy.ftv])
  | .int, _agree => rfl
  | .fn domain codomain, agree => by
      simp only [STy.applySubst]
      rw [STy.applySubst_eq_of_ftv_agree domain (by
            intro name member
            exact agree name (by simp [STy.ftv, member])),
        STy.applySubst_eq_of_ftv_agree codomain (by
            intro name member
            exact agree name (by simp [STy.ftv, member]))]
  | .prod components, agree => by
      simp only [STy.applySubst]
      exact congrArg STy.prod
        (STy.applySubstList_eq_of_ftv_agree components agree)

/-- List form of `STy.applySubst_eq_of_ftv_agree`. -/
theorem STy.applySubstList_eq_of_ftv_agree
    {left right : SSubst} : ∀ targets : List STy,
    (∀ name, name ∈ STy.ftvList targets → left name = right name) →
      STy.applySubstList left targets = STy.applySubstList right targets
  | [], _agree => rfl
  | target :: targets, agree => by
      simp only [STy.applySubstList]
      rw [STy.applySubst_eq_of_ftv_agree target (by
            intro name member
            exact agree name (by simp [STy.ftvList, member])),
        STy.applySubstList_eq_of_ftv_agree targets (by
            intro name member
            exact agree name (by simp [STy.ftvList, member]))]

end

/-- Restriction is invisible on a type whose actual free-variable list is the
selected scope. -/
theorem STy.applySubst_restrict (post : SSubst) (target : STy) :
    target.applySubst (SSubst.restrict target.ftv post) =
      target.applySubst post := by
  apply STy.applySubst_eq_of_ftv_agree
  intro name member
  exact SSubst.restrict_of_mem post member

/-! ## Monotype and environment generality -/

/-- One DM monotype is more general than another when the latter is obtained
by changing only free variables of the former. -/
def STy.Instance (source target : STy) : Prop :=
  ∃ post : SSubst,
    post.SupportWithin source.ftv ∧ source.applySubst post = target

namespace STy.Instance

theorem refl (source : STy) : source.Instance source := by
  exact ⟨SSubst.id, SSubst.id_supportWithin source.ftv,
    STy.applySubst_id source⟩

theorem trans {source middle target : STy}
    (sourceMiddle : source.Instance middle)
    (middleTarget : middle.Instance target) :
    source.Instance target := by
  rcases sourceMiddle with ⟨earlier, _earlierSupport, sourceEq⟩
  rcases middleTarget with ⟨later, _laterSupport, middleEq⟩
  let composite := SSubst.comp later earlier
  let restricted := SSubst.restrict source.ftv composite
  refine ⟨restricted, SSubst.restrict_supportWithin source.ftv composite, ?_⟩
  calc
    source.applySubst restricted = source.applySubst composite :=
      STy.applySubst_restrict composite source
    _ = (source.applySubst earlier).applySubst later := by
      rw [STy.applySubst_comp]
    _ = target := by rw [sourceEq, middleEq]

end STy.Instance

/-- Scheme generality, stated semantically to avoid choosing binder names:
every use admitted by `specific` is also admitted by `general`. -/
def SScheme.MoreGeneral (general specific : SScheme) : Prop :=
  ∀ {target : STy}, specific.Inst target → general.Inst target

namespace SScheme.MoreGeneral

theorem refl (scheme : SScheme) : scheme.MoreGeneral scheme :=
  fun instantiation => instantiation

theorem trans {first second third : SScheme}
    (firstSecond : first.MoreGeneral second)
    (secondThird : second.MoreGeneral third) :
    first.MoreGeneral third :=
  fun instantiation => firstSecond (secondThird instantiation)

end SScheme.MoreGeneral

/-- Pointwise environment generality with lookup/shadowing interpreted by the
same `SCtx.find?` operation used in `DM.Typing.var`. -/
def SCtx.MoreGeneral (general specific : SCtx) : Prop :=
  ∀ {name : String} {specificScheme : SScheme},
    specific.find? name = some specificScheme →
      ∃ generalScheme,
        general.find? name = some generalScheme ∧
        generalScheme.MoreGeneral specificScheme

namespace SCtx.MoreGeneral

theorem refl (context : SCtx) : context.MoreGeneral context := by
  intro name scheme found
  exact ⟨scheme, found, SScheme.MoreGeneral.refl scheme⟩

theorem trans {first second third : SCtx}
    (firstSecond : first.MoreGeneral second)
    (secondThird : second.MoreGeneral third) :
    first.MoreGeneral third := by
  intro name thirdScheme found
  obtain ⟨secondScheme, secondFound, secondGeneral⟩ := secondThird found
  obtain ⟨firstScheme, firstFound, firstGeneral⟩ := firstSecond secondFound
  exact ⟨firstScheme, firstFound,
    SScheme.MoreGeneral.trans firstGeneral secondGeneral⟩

end SCtx.MoreGeneral

/-! ## Principal canonical scheme openings -/

/-- The one-sort view of the finite positional opening used by executable
scheme instantiation. -/
def SSubst.canonicalOpening (next : Nat)
    (binders : List TypePM.TyVar) : SSubst :=
  fun name =>
    match binders.finIdxOf? name with
    | some index => .var (next + index.val)
    | none => .var name

theorem SSubst.canonicalOpening_supportWithin
    (next : Nat) (binders : List TypePM.TyVar) :
    (SSubst.canonicalOpening next binders).SupportWithin binders := by
  intro name outside
  simp [SSubst.canonicalOpening, List.finIdxOf?_eq_none_iff.mpr outside]

/-- Read a chosen DM binder instance back through the fresh positional range.
Outside that range this is the identity. -/
def SSubst.postOfCanonicalOpening (next : Nat)
    (binders : List TypePM.TyVar) (chosen : SSubst) : SSubst :=
  fun candidate =>
    if bounded : next ≤ candidate ∧ candidate - next < binders.length then
      chosen (binders.get ⟨candidate - next, bounded.2⟩)
    else
      .var candidate

/-- Pointwise factorization of an arbitrary binder-supported instance through
the canonical positional opening.  Ambient variables must lie below the fresh
range, exactly as guaranteed by the inference supply invariant. -/
theorem SSubst.post_canonicalOpening
    {next : Nat} {binders : List TypePM.TyVar} {chosen : SSubst}
    (support : chosen.SupportWithin binders)
    {name : TypePM.TyVar} (below : name < next) :
    ((SSubst.canonicalOpening next binders name).applySubst
      (SSubst.postOfCanonicalOpening next binders chosen)) = chosen name := by
  unfold SSubst.canonicalOpening
  cases found : binders.finIdxOf? name with
  | none =>
      have outside : name ∉ binders := List.finIdxOf?_eq_none_iff.mp found
      rw [support name outside]
      simp [STy.applySubst, SSubst.postOfCanonicalOpening,
        Nat.not_le_of_lt below]
  | some index =>
      have nameEq : binders.get index = name :=
        List.get_eq_of_finIdxOf?_eq_some found
      simp only [STy.applySubst]
      unfold SSubst.postOfCanonicalOpening
      have lower : next ≤ next + index.val := Nat.le_add_right _ _
      have subtract : next + index.val - next = index.val := by omega
      simp only [lower, subtract, index.isLt, and_self, dite_true]
      rw [nameEq]

/-- The canonical fresh monotype produced by opening a DM scheme at `next`. -/
def SScheme.canonicalTarget (scheme : SScheme) (next : Nat) : STy :=
  scheme.body.applySubst
    (SSubst.canonicalOpening next scheme.binders)

/-- A list of variables lies strictly below a target supply. -/
def TyVarsBelow (next : Nat) (variables : List TypePM.TyVar) : Prop :=
  ∀ name, name ∈ variables → name < next

/-- Every declared DM instance factors through a sufficiently fresh canonical
opening.  This is the variable case of the Algorithm W completeness invariant. -/
theorem SScheme.canonicalTarget_principal
    {scheme : SScheme} {target : STy} {next : Nat}
    (instantiation : scheme.Inst target)
    (fresh : TyVarsBelow next scheme.body.ftv) :
    (scheme.canonicalTarget next).Instance target := by
  rcases instantiation with ⟨chosen, support, result⟩
  let post := SSubst.postOfCanonicalOpening next scheme.binders chosen
  refine ⟨SSubst.restrict (scheme.canonicalTarget next).ftv post,
    SSubst.restrict_supportWithin _ _, ?_⟩
  rw [STy.applySubst_restrict]
  unfold SScheme.canonicalTarget
  rw [STy.applySubst_comp]
  calc
    scheme.body.applySubst
        (SSubst.comp post
          (SSubst.canonicalOpening next scheme.binders)) =
        scheme.body.applySubst chosen := by
      apply STy.applySubst_eq_of_ftv_agree
      intro name member
      exact SSubst.post_canonicalOpening support (fresh name member)
    _ = target := result

/-! ## Embedding compatibility -/

/-- Executable finite opening of an embedded DM scheme agrees with the
one-sort canonical target above. -/
theorem SScheme.canonicalTarget_emb
    (scheme : SScheme) (supply : InferenceBase.FreshSupply) :
    (InferenceBase.instantiateScheme supply scheme.emb).value =
      (scheme.canonicalTarget supply.nextTy).emb := by
  rw [InferenceBase.instantiateScheme_value]
  unfold SScheme.emb
  rw [Scheme.openValue_close]
  simp only [Subst.apply, STy.emb_applyCapability,
    Scheme.FreshOpening.toValueOpening]
  simp only [Scheme.canonicalFreshOpening_tyImage]
  change Ty.applyTarget
      (openingTySubst scheme.binders
        (fun index => .var (supply.nextTy + index.val)))
      scheme.body.emb =
    (scheme.canonicalTarget supply.nextTy).emb
  unfold SScheme.canonicalTarget
  rw [← STy.emb_applyTarget
    (SSubst.canonicalOpening supply.nextTy scheme.binders) scheme.body]
  congr 1
  funext name
  unfold SSubst.canonicalOpening openingTySubst SSubst.emb
  cases found : scheme.binders.finIdxOf? name <;> simp [found, STy.emb]

/-- A one-sort monotype instance embeds as a two-sort type instance with an
identity capability component. -/
theorem STy.Instance.emb {source target : STy}
    (instanceOf : source.Instance target) :
    TypePM.TypeInstance source.emb target.emb := by
  rcases instanceOf with ⟨post, _support, equation⟩
  apply TypeInstance.of_apply
    { cap := CapSubst.id, target := SSubst.emb post }
  simp only [Subst.apply, STy.emb_applyCapability,
    STy.emb_applyTarget, equation]

/-- Executable lookup instantiation is principal for every DM use selected by
the declarative variable rule. -/
theorem SScheme.instantiateScheme_principal
    {scheme : SScheme} {target : STy}
    (supply : InferenceBase.FreshSupply)
    (instantiation : scheme.Inst target)
    (fresh : TyVarsBelow supply.nextTy scheme.body.ftv) :
    TypeInstance
      (InferenceBase.instantiateScheme supply scheme.emb).value
      target.emb := by
  rw [SScheme.canonicalTarget_emb]
  exact (SScheme.canonicalTarget_principal instantiation fresh).emb

end DM
end TypePM
