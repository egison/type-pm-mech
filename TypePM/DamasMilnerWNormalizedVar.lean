import TypePM.DamasMilnerWNormalized
import TypePM.DamasMilnerWRetired
import TypePM.SchemeOpeningLists

/-!
# Canonical normalized result for a Damas--Milner variable

A declarative variable instance factors through the executable canonical
opening.  This file packages the resulting one-sort residual together with
the exact executable raw target and the freshness facts needed by the retired
let invariant.
-/

namespace TypePM
namespace DM

/-! ## Recovering a one-sort residual from a core equation -/

/-- Decode the image of a target metavariable when it remains in the DM
fragment, defaulting only for variables irrelevant to the source equation. -/
def SSubst.ofCore (post : Subst) : SSubst :=
  fun varId => (STy.ofTy? (post.apply (.var varId))).getD .int

mutual

/-- An equation between embedded simple types under an arbitrary paired post
can be read back as one shared one-sort substitution equation. -/
theorem STy.applySubst_ofCore_eq_of_apply_emb
    (post : Subst) : ∀ source target : STy,
    post.apply source.emb = target.emb →
      source.applySubst (SSubst.ofCore post) = target
  | .var varId, target, equation => by
      simp only [STy.applySubst, SSubst.ofCore]
      have equation' : post.apply (.var varId) = target.emb := by
        simpa [STy.emb] using equation
      rw [equation', STy.ofTy?_emb]
      rfl
  | .int, .int, _ => rfl
  | .int, .var _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .int, .fn _ _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .int, .prod _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .fn _ _, .var _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .fn domain codomain, .fn selectedDomain selectedCodomain, equation => by
      simp only [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
      injection equation with domainEq codomainEq
      simp only [STy.applySubst]
      rw [STy.applySubst_ofCore_eq_of_apply_emb post domain selectedDomain
          domainEq,
        STy.applySubst_ofCore_eq_of_apply_emb post codomain selectedCodomain
          codomainEq]
  | .fn _ _, .int, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .fn _ _, .prod _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .prod _, .var _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .prod _, .int, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .prod _, .fn _ _, equation => by
      simp [STy.emb, Subst.apply, Ty.applyCapability,
        Ty.applyTarget] at equation
  | .prod components, .prod selected, equation => by
      simp only [STy.emb, Subst.apply_prod] at equation
      injection equation with componentsEq
      exact congrArg STy.prod
        (STy.applySubstList_ofCore_eq_of_apply_emb post components selected
          componentsEq)

/-- List form of `STy.applySubst_ofCore_eq_of_apply_emb`. -/
theorem STy.applySubstList_ofCore_eq_of_apply_emb
    (post : Subst) : ∀ source target : List STy,
    (STy.embList source).map post.apply = STy.embList target →
      STy.applySubstList (SSubst.ofCore post) source = target
  | [], [], _ => rfl
  | [], _ :: _, equation => by simp [STy.embList] at equation
  | _ :: _, [], equation => by simp [STy.embList] at equation
  | head :: tail, selectedHead :: selectedTail, equation => by
      simp only [STy.embList, List.map_cons, List.cons.injEq] at equation
      rcases equation with ⟨headEq, tailEq⟩
      simp only [STy.applySubstList]
      rw [STy.applySubst_ofCore_eq_of_apply_emb post head selectedHead headEq,
        STy.applySubstList_ofCore_eq_of_apply_emb post tail selectedTail tailEq]

end

/-- Embedded endpoints turn a core factor into a supported one-sort
monotype instance. -/
theorem STy.instance_of_core_apply
    {source target : STy} {post : Subst}
    (equation : post.apply source.emb = target.emb) : source.Instance target := by
  let residual := SSubst.restrict source.ftv (SSubst.ofCore post)
  refine ⟨residual, SSubst.restrict_supportWithin source.ftv _, ?_⟩
  calc
    source.applySubst residual =
        source.applySubst (SSubst.ofCore post) :=
      STy.applySubst_restrict _ source
    _ = target := STy.applySubst_ofCore_eq_of_apply_emb post source target
      equation

/-- Embedded context lookup is exactly the mapped one-sort lookup, including
the `none` case needed when recovering an algorithm scheme from a core W
frame. -/
theorem SCtx.find?_emb_eq (context : SCtx) (name : String) :
    Context.find? context.emb name =
      (SCtx.find? context name).map SScheme.emb := by
  induction context with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨entryName, scheme⟩
      change Context.find? ((entryName, scheme.emb) :: SCtx.emb rest) name =
        Option.map SScheme.emb
          (SCtx.find? ((entryName, scheme) :: rest) name)
      unfold Context.find? SCtx.find?
      simp only [List.find?_cons]
      split
      · rfl
      · change Context.find? (SCtx.emb rest) name =
          Option.map SScheme.emb (SCtx.find? rest name)
        exact induction

/-! ## Free variables of one-sort substitution images -/

mutual

/-- A free variable after one-sort substitution comes from an image of a free
source variable. -/
theorem STy.mem_ftv_applySubst
    (post : SSubst) : ∀ (target : STy) (image : TypePM.TyVar),
    image ∈ (target.applySubst post).ftv →
    ∃ source, source ∈ target.ftv ∧ image ∈ (post source).ftv
  | .var source, _, membership =>
      ⟨source, by simp [STy.ftv], membership⟩
  | .int, _, membership => by
      simp [STy.applySubst, STy.ftv] at membership
  | .fn domain codomain, image, membership => by
      simp only [STy.applySubst, STy.ftv, List.mem_append] at membership ⊢
      rcases membership with domainMember | codomainMember
      · obtain ⟨source, sourceMember, imageMember⟩ :=
          STy.mem_ftv_applySubst post domain image domainMember
        exact ⟨source, Or.inl sourceMember, imageMember⟩
      · obtain ⟨source, sourceMember, imageMember⟩ :=
          STy.mem_ftv_applySubst post codomain image codomainMember
        exact ⟨source, Or.inr sourceMember, imageMember⟩
  | .prod components, image, membership =>
      STy.mem_ftvList_applySubstList post components image membership

/-- List form of `STy.mem_ftv_applySubst`. -/
theorem STy.mem_ftvList_applySubstList
    (post : SSubst) : ∀ (targets : List STy) (image : TypePM.TyVar),
    image ∈ STy.ftvList (STy.applySubstList post targets) →
    ∃ source, source ∈ STy.ftvList targets ∧ image ∈ (post source).ftv
  | [], _, membership => by
      simp [STy.applySubstList, STy.ftvList] at membership
  | head :: tail, image, membership => by
      simp only [STy.applySubstList, STy.ftvList,
        List.mem_append] at membership ⊢
      rcases membership with headMember | tailMember
      · obtain ⟨source, sourceMember, imageMember⟩ :=
          STy.mem_ftv_applySubst post head image headMember
        exact ⟨source, Or.inl sourceMember, imageMember⟩
      · obtain ⟨source, sourceMember, imageMember⟩ :=
          STy.mem_ftvList_applySubstList post tail image tailMember
        exact ⟨source, Or.inr sourceMember, imageMember⟩

end

/-! ## Canonical-opening occurrence split -/

/-- Every free variable of the canonical target is either an ambient free
variable of the selected scheme or one of the freshly allocated positional
images. -/
theorem SScheme.mem_canonicalTarget_ftv
    (scheme : SScheme) (supply : InferenceBase.FreshSupply)
    {image : TypePM.TyVar}
    (membership : image ∈ (scheme.canonicalTarget supply.nextTy).ftv) :
    image ∈ scheme.ftv ∨
      image ∈ Scheme.canonicalTyImages supply scheme.emb := by
  obtain ⟨source, sourceFree, imageIn⟩ :=
    STy.mem_ftv_applySubst
      (SSubst.canonicalOpening supply.nextTy scheme.binders)
      scheme.body image membership
  unfold SSubst.canonicalOpening at imageIn
  cases found : scheme.binders.finIdxOf? source with
  | none =>
      have outside : source ∉ scheme.binders :=
        List.finIdxOf?_eq_none_iff.mp found
      have imageEq : image = source := by
        simpa [found, STy.ftv] using imageIn
      subst image
      exact Or.inl (by
        exact List.mem_filter.mpr ⟨sourceFree, by simp [outside]⟩)
  | some index =>
      have imageEq : image = supply.nextTy + index.val := by
        simpa [found, STy.ftv] using imageIn
      subst image
      apply Or.inr
      unfold Scheme.canonicalTyImages Scheme.FreshOpening.tyImages
      rw [List.mem_ofFn]
      refine ⟨index, ?_⟩
      rfl

/-- Allocated variables occurring in the canonical target lie in the exact
half-open supply interval consumed by executable instantiation. -/
theorem SScheme.canonicalTarget_allocated_bounds
    (scheme : SScheme) (supply : InferenceBase.FreshSupply)
    {image : TypePM.TyVar}
    (allocated : image ∈ Scheme.canonicalTyImages supply scheme.emb) :
    supply.nextTy ≤ image ∧
      image < (InferenceBase.instantiateScheme supply scheme.emb).supply.nextTy := by
  exact Scheme.mem_canonicalTyImages_bounds allocated

/-- A free target variable of a scheme returned by context lookup is free in
the containing canonical context. -/
theorem Context.mem_ftv_of_find?
    {context : Context} {name : String} {scheme : Scheme}
    (found : context.find? name = some scheme) {varId : TypePM.TyVar}
    (free : varId ∈ scheme.ftv) : varId ∈ context.ftv := by
  unfold Context.find? at found
  rw [Option.map_eq_some_iff] at found
  obtain ⟨entry, selected, schemeEq⟩ := found
  have entryMember : entry ∈ context :=
    List.mem_of_find?_eq_some selected
  unfold Context.ftv
  apply List.mem_flatMap.mpr
  refine ⟨entry, entryMember, ?_⟩
  simpa [schemeEq] using free

/-! ## Variable result package -/

/-- Canonical normalized output of the variable branch.  The only premise
specific to retired lets concerns ambient free variables of the selected
scheme; freshly opened binders are discharged from `PendingBelow`. -/
structure NormalizedDMVarResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (current : Subst) (pending : List PendingLetCut)
    (algorithmScheme selectedScheme : SScheme)
    (selectedTarget : STy) : Prop where
  residual : ∃ residual : SSubst,
    residual.SupportWithin
        (algorithmScheme.canonicalTarget supply.nextTy).ftv ∧
      (algorithmScheme.canonicalTarget supply.nextTy).applySubst residual =
        selectedTarget
  rawTarget_eq :
    (InferenceBase.instantiateScheme supply algorithmScheme.emb).value =
      (algorithmScheme.canonicalTarget supply.nextTy).emb
  occurrence : ∀ {image},
    image ∈ (algorithmScheme.canonicalTarget supply.nextTy).ftv →
    image ∈ algorithmScheme.ftv ∨
      image ∈ Scheme.canonicalTyImages supply algorithmScheme.emb
  allocatedBounds : ∀ {image},
    image ∈ Scheme.canonicalTyImages supply algorithmScheme.emb →
    supply.nextTy ≤ image ∧
      image < (InferenceBase.instantiateScheme supply
        algorithmScheme.emb).supply.nextTy
  retired : ∀ cut ∈ pending,
    cut.AvoidsTy signature current
      (algorithmScheme.canonicalTarget supply.nextTy).emb

/-- The executable canonical opening of a scheme found in a retired-fresh
normalized context is itself retired-fresh.  Ambient free variables come
from the context; freshly allocated binder images lie at or above the input
supply, while every retired binder lies strictly below it. -/
theorem SScheme.canonicalTarget_avoids_of_lookup
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    {normalizedContext : Context} {name : String} {scheme : SScheme}
    (lookup : normalizedContext.find? name = some scheme.emb)
    (pendingBelow : PendingLetsBelow signature supply current pending)
    (contextFresh : ∀ cut ∈ pending,
      cut.AvoidsContext signature current normalizedContext) :
    ∀ cut ∈ pending,
      cut.AvoidsTy signature current
        (scheme.canonicalTarget supply.nextTy).emb := by
  intro cut cutMember
  constructor
  · intro capVar _generalized free
    rw [STy.emb_fcv] at free
    exact List.not_mem_nil free
  · intro varId generalized free
    rw [STy.emb_ftv] at free
    rcases scheme.mem_canonicalTarget_ftv supply free with ambient | allocated
    · apply (contextFresh cut cutMember).targets varId generalized
      apply Context.mem_ftv_of_find? lookup
      rw [SScheme.emb_ftv]
      exact ambient
    · have lower := (scheme.canonicalTarget_allocated_bounds supply allocated).1
      have retiredBelow := (pendingBelow cut cutMember).2 varId generalized
      exact (Nat.not_lt_of_ge lower) retiredBelow

/-- Generic variable constructor for an algorithm scheme which is semantically
more general than the selected declarative scheme under the current one-sort
residual.  No syntactic equality between the two schemes is required. -/
theorem NormalizedDMVarResult.ofRealizedLookup
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    {normalizedContext : Context} {name : String}
    {contextResidual : SSubst}
    {algorithmScheme selectedScheme : SScheme} {selectedTarget : STy}
    (instantiation : selectedScheme.Inst selectedTarget)
    (realizes : selectedScheme.RealizedBy
      (SSubst.paired contextResidual) algorithmScheme.emb)
    (algorithmBounded : algorithmScheme.emb.BoundedBy supply)
    (pendingBelow : PendingLetsBelow signature supply current pending)
    (lookup : normalizedContext.find? name = some algorithmScheme.emb)
    (contextFresh : ∀ cut ∈ pending,
      cut.AvoidsContext signature current normalizedContext) :
    NormalizedDMVarResult signature supply current pending algorithmScheme
      selectedScheme selectedTarget := by
  have selectedUse := realizes instantiation
  let opening := Classical.choose selectedUse
  let coreResidual := extendSchemeOpening (SSubst.paired contextResidual)
    supply algorithmScheme.emb opening
  have coreEquation : coreResidual.apply
      (algorithmScheme.canonicalTarget supply.nextTy).emb =
        selectedTarget.emb := by
    rw [← algorithmScheme.canonicalTarget_emb supply]
    exact canonicalSchemeOpening_principal_relative
      (SSubst.paired contextResidual) supply algorithmScheme.emb
      algorithmBounded selectedUse
  have principal := STy.instance_of_core_apply coreEquation
  rcases principal with ⟨residual, residualSupport, residualEq⟩
  refine
    { residual := ⟨residual, residualSupport, residualEq⟩
      rawTarget_eq := algorithmScheme.canonicalTarget_emb supply
      occurrence := algorithmScheme.mem_canonicalTarget_ftv supply
      allocatedBounds := algorithmScheme.canonicalTarget_allocated_bounds supply
      retired := algorithmScheme.canonicalTarget_avoids_of_lookup lookup
        pendingBelow contextFresh }

end DM
end TypePM
