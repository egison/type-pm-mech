import TypePM.DamasMilnerWCutNormalization
import TypePM.DamasMilnerConservativity

/-!
# Let generalization from an erasure-stable W boundary

An absorbed W cut need not leave the protected context literally embedded.
Let generalization, however, observes only the context's free-variable list.
This file reifies that finite list as a harmless synthetic DM context and
uses the existing residual-generalization theorem there.  Consequently no
scheme binder is renamed through an ambient substitution, avoiding the
binder-capture problem of a direct `Scheme.applyMeta` decoder.
-/

namespace TypePM
namespace DM

/-- A synthetic one-sort context whose only purpose is to reproduce a given
ordered list of free target metavariables.  Distinct entry names are
irrelevant because this context is used only by generalization. -/
def SCtx.scopeOfTyVars (variables : List TypePM.TyVar) : SCtx :=
  variables.map fun varId => ("", SScheme.mono (.var varId))

@[simp] theorem SCtx.ftv_scopeOfTyVars (variables : List TypePM.TyVar) :
    (SCtx.scopeOfTyVars variables).ftv = variables := by
  induction variables with
  | nil => rfl
  | cons varId variables induction =>
      change SCtx.ftv
          (("", SScheme.mono (.var varId)) ::
            SCtx.scopeOfTyVars variables) = varId :: variables
      simp only [SCtx.ftv, List.flatMap_cons]
      have head : (SScheme.mono (.var varId)).ftv = [varId] := by
        simp [SScheme.mono, SScheme.ftv, STy.ftv]
      rw [head]
      change [varId] ++ (SCtx.scopeOfTyVars variables).ftv =
        varId :: variables
      rw [induction]
      rfl

@[simp] theorem SCtx.emb_scopeOfTyVars_ftv
    (variables : List TypePM.TyVar) :
    (SCtx.scopeOfTyVars variables).emb.ftv = variables := by
  rw [SCtx.emb_ftv, SCtx.ftv_scopeOfTyVars]

/-- Generalization over an embedded synthetic scope agrees exactly with
generalization over any core context having that scope.  Capability binders
are empty because the target is an embedded DM type. -/
theorem FrozenSig.generalize_scopeOfTyVars
    (signature : FrozenSig) (coreContext : Context)
    (algorithmTarget : STy) :
    signature.generalize
        (SCtx.scopeOfTyVars coreContext.ftv).emb algorithmTarget.emb =
      signature.generalize coreContext algorithmTarget.emb := by
  unfold FrozenSig.generalize Scheme.generalize
  congr 1
  · unfold generalizedCapVars
    simp [STy.emb_fcv, uniqueVars]
  · rw [SCtx.emb_scopeOfTyVars_ftv]

/-- The separation premise needed at an erased let boundary.  It is stated
directly on the executable context scope, so no exact syntactic decoding of
the context schemes is required. -/
def ErasedLetSeparated (residual : SSubst) (coreContext : Context)
    (selectedContext : SCtx) (selectedTarget : STy) : Prop :=
  ∀ {algorithmVar selectedBinder : TypePM.TyVar},
    algorithmVar ∈ coreContext.ftv →
    selectedBinder ∈
      (SCtx.generalize selectedContext selectedTarget).binders →
    selectedBinder ∉ (residual algorithmVar).ftv

/-- Every residual image of an executable environment variable remains in
the selected environment scope.  Unlike `WContextRel`, this also rules out
unmatched extra executable bindings, which is exactly what let
generalization needs. -/
def ResidualContextScope (residual : SSubst) (coreContext : Context)
    (selectedContext : SCtx) : Prop :=
  ∀ {algorithmVar selectedVar : TypePM.TyVar},
    algorithmVar ∈ coreContext.ftv →
    selectedVar ∈ (residual algorithmVar).ftv →
    selectedVar ∈ selectedContext.ftv

mutual

theorem STy.mem_ftv_applySubst_of_image (post : SSubst) :
    ∀ (target : STy) {source image : TypePM.TyVar},
      source ∈ target.ftv → image ∈ (post source).ftv →
        image ∈ (target.applySubst post).ftv
  | .var source, candidate, image, sourceFree, imageFree => by
      simpa [STy.ftv, STy.applySubst] using
        (show candidate = source from by simpa [STy.ftv] using sourceFree) ▸
          imageFree
  | .int, _, _, sourceFree, _ => by simp [STy.ftv] at sourceFree
  | .fn domain codomain, source, image, sourceFree, imageFree => by
      simp only [STy.ftv, List.mem_append] at sourceFree ⊢
      simp only [STy.applySubst, STy.ftv, List.mem_append]
      rcases sourceFree with domainFree | codomainFree
      · exact Or.inl
          (STy.mem_ftv_applySubst_of_image post domain domainFree imageFree)
      · exact Or.inr
          (STy.mem_ftv_applySubst_of_image post codomain codomainFree imageFree)
  | .prod components, source, image, sourceFree, imageFree =>
      STy.mem_ftvList_applySubstList_of_image post components sourceFree
        imageFree

theorem STy.mem_ftvList_applySubstList_of_image (post : SSubst) :
    ∀ (targets : List STy) {source image : TypePM.TyVar},
      source ∈ STy.ftvList targets → image ∈ (post source).ftv →
        image ∈ STy.ftvList (STy.applySubstList post targets)
  | [], _, _, sourceFree, _ => by simp [STy.ftvList] at sourceFree
  | head :: tail, source, image, sourceFree, imageFree => by
      simp only [STy.ftvList, List.mem_append] at sourceFree ⊢
      simp only [STy.applySubstList, STy.ftvList, List.mem_append]
      rcases sourceFree with headFree | tailFree
      · exact Or.inl
          (STy.mem_ftv_applySubst_of_image post head headFree imageFree)
      · exact Or.inr
          (STy.mem_ftvList_applySubstList_of_image post tail tailFree imageFree)

end

theorem ResidualContextScope.initial (context : SCtx) :
    ResidualContextScope SSubst.id context.emb context := by
  intro algorithmVar selectedVar algorithmFree imageFree
  have algorithmSelected : algorithmVar ∈ context.ftv := by
    simpa [SCtx.emb_ftv] using algorithmFree
  have selectedEq : selectedVar = algorithmVar := by
    simpa [SSubst.id, STy.ftv] using imageFree
  simpa [selectedEq] using algorithmSelected

theorem ResidualContextScope.of_context_eq
    {residual : SSubst} {left right : Context} {selectedContext : SCtx}
    (scope : ResidualContextScope residual left selectedContext)
    (equality : right = left) :
    ResidualContextScope residual right selectedContext := by
  subst right
  exact scope

/-- A scheme opening changes only the fresh allocation interval.  It is
therefore invisible on the free variables of a context bounded by the
incoming supply. -/
theorem ResidualContextScope.extendSchemeOpening
    {base : SSubst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx} {scheme : SScheme}
    (opening : (scheme.emb.applyMeta (SSubst.paired base)).ValueOpening)
    (scope : ResidualContextScope base algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply) :
    ResidualContextScope
      (fun varId => eraseTy
        ((extendSchemeOpening (SSubst.paired base) supply scheme.emb opening)
          |>.target varId))
      algorithmContext selectedContext := by
  intro algorithmVar selectedVar algorithmFree imageFree
  have below : algorithmVar < supply.nextTy := by
    rw [Context.ftv] at algorithmFree
    rcases List.mem_flatMap.mp algorithmFree with
      ⟨entry, entryMember, free⟩
    exact (bounded entry entryMember).targets algorithmVar free
  have imageEq := extendSchemeOpening_target_below
    (SSubst.paired base) supply scheme.emb opening algorithmVar below
  change selectedVar ∈ (eraseTy
    ((DM.extendSchemeOpening (SSubst.paired base) supply scheme.emb opening)
      |>.target algorithmVar)).ftv at imageFree
  rw [imageEq] at imageFree
  have imageFree' : selectedVar ∈ (base algorithmVar).ftv := by
    simpa [SSubst.paired, SSubst.emb, eraseTy_emb] using imageFree
  exact scope algorithmFree imageFree'

/-- Install one monomorphic binding whose algorithm variable is related to
the selected domain, preserving the outer environment scope. -/
theorem ResidualContextScope.consMono
    {residual : SSubst} {algorithmContext : Context}
    {selectedContext : SCtx} {algorithmVar : TypePM.TyVar}
    {selectedDomain : STy} (scope : ResidualContextScope residual
      algorithmContext selectedContext)
    (domainEq : residual algorithmVar = selectedDomain) (name : String) :
    ResidualContextScope residual
      ((name, Scheme.mono (.var algorithmVar)) :: algorithmContext)
      ((name, SScheme.mono selectedDomain) :: selectedContext) := by
  intro source image sourceFree imageFree
  simp only [Context.ftv, List.flatMap_cons, Scheme.mono,
    Scheme.ftv, List.mem_append] at sourceFree
  rw [lift_ftv] at sourceFree
  simp only [Ty.ftv, List.mem_singleton] at sourceFree
  simp only [SCtx.ftv, List.flatMap_cons]
  rcases sourceFree with rfl | outerFree
  · apply List.mem_append.mpr
    left
    have : image ∈ selectedDomain.ftv := by simpa [domainEq] using imageFree
    simpa [SScheme.mono, SScheme.ftv] using this
  · apply List.mem_append.mpr
    right
    exact scope outerFree imageFree

/-- Allocating the two fresh application variables is invisible on a context
bounded by the incoming supply. -/
theorem ResidualContextScope.extendAppTargets
    {residual : SSubst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx}
    (scope : ResidualContextScope residual algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply) (domain codomain : STy) :
    ResidualContextScope
      (SSubst.extendAppTargets residual supply domain codomain)
      algorithmContext selectedContext := by
  intro source image sourceFree imageFree
  have below : source < supply.nextTy := by
    rw [Context.ftv] at sourceFree
    rcases List.mem_flatMap.mp sourceFree with
      ⟨entry, entryMember, free⟩
    exact (bounded entry entryMember).targets source free
  have sourceNeDomain : source ≠ supply.nextTy := Nat.ne_of_lt below
  have sourceNeCodomain : source ≠ supply.nextTy + 1 :=
    Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_succ_self _))
  have unchanged :
      SSubst.extendAppTargets residual supply domain codomain source =
        residual source := by
    simp [SSubst.extendAppTargets, sourceNeDomain, sourceNeCodomain]
  exact scope sourceFree (by simpa [unchanged] using imageFree)

/-- Absorbing a core solver cut preserves environment scope.  The factor
equation says that following a cut image and then the residual cannot expose
any selected variable absent from the old residual image. -/
theorem ResidualContextScope.applyAbsorbed
    {residual : SSubst} {delta : Subst}
    {algorithmContext : Context} {selectedContext : SCtx}
    (scope : ResidualContextScope residual algorithmContext selectedContext)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ResidualContextScope residual (algorithmContext.applySubst delta)
      selectedContext := by
  intro source image sourceFree imageFree
  rw [Context.ftv_applySubst_flatMap] at sourceFree
  rcases List.mem_flatMap.mp sourceFree with
    ⟨oldSource, oldFree, sourceInDelta⟩
  have sourceInErased : source ∈ (eraseTy (delta.target oldSource)).ftv := by
    rw [eraseTy_ftv]
    exact sourceInDelta
  have imageInComposed : image ∈
      ((eraseTy (delta.target oldSource)).applySubst residual).ftv :=
    STy.mem_ftv_applySubst_of_image residual _ sourceInErased imageFree
  have applied : (SSubst.paired residual).apply (.var oldSource) =
      (SSubst.paired residual).apply (delta.apply (.var oldSource)) := by
    calc
      (SSubst.paired residual).apply (.var oldSource) =
          (Subst.seq (SSubst.paired residual) delta).apply
            (.var oldSource) := congrArg (fun post => post.apply (.var oldSource))
              factor
      _ = (SSubst.paired residual).apply
          (delta.apply (.var oldSource)) := Subst.seq_apply _ _ _
  have erased := congrArg eraseTy applied
  have residualImageEq :
      (eraseTy (delta.target oldSource)).applySubst residual =
        residual oldSource := by
    rw [eraseTy_apply_paired, eraseTy_apply_paired] at erased
    simpa [Subst.apply, Ty.applyCapability, Ty.applyTarget, eraseTy,
      STy.applySubst] using erased.symm
  apply scope oldFree
  rwa [residualImageEq] at imageInComposed

/-- The target-independent environment-scope invariant implies binder
separation for every selected value generalized over that environment. -/
theorem ResidualContextScope.letSeparated
    {residual : SSubst} {coreContext : Context}
    {selectedContext : SCtx} (scope : ResidualContextScope residual
      coreContext selectedContext) (selectedTarget : STy) :
    ErasedLetSeparated residual coreContext selectedContext selectedTarget := by
  intro algorithmVar selectedBinder algorithmFree selectedGeneralized
    inResidual
  have outside : selectedBinder ∉ selectedContext.ftv := by
    unfold SCtx.generalize at selectedGeneralized
    exact of_decide_eq_true (List.mem_filter.mp
      (mem_uniqueVars.mp selectedGeneralized)).2
  exact outside (scope algorithmFree inResidual)

/-- An erasure-stable context/target boundary produces the semantic binding
relation required by the executable let body.  Target reflection supplies
the exact one-sort value type; the synthetic scope avoids all alpha-capture
issues while preserving the executable generalizer literally. -/
theorem ErasedDMView.letBinding
    {signature : FrozenSig} (signatureClosed : signature.SchemesClosed)
    {residual : SSubst} {selectedContext : SCtx}
    {selectedTarget : STy} {coreContext : Context} {coreTarget : Ty}
    (view : ErasedDMView residual selectedContext selectedTarget
      coreContext coreTarget)
    (scope : ResidualContextScope residual coreContext selectedContext) :
    WLetBindingRel (SSubst.paired residual) Subst.id
      (signature.generalize coreContext coreTarget)
      (SCtx.generalize selectedContext selectedTarget) := by
  obtain ⟨algorithmTarget, targetView⟩ := view.target.toNormalized
  let algorithmContext := SCtx.scopeOfTyVars coreContext.ftv
  have relation : GeneralizationResidual residual algorithmContext
      selectedContext algorithmTarget selectedTarget := by
    refine ⟨targetView.residual_eq, ?_⟩
    intro algorithmVar selectedBinder algorithmFree selectedGeneralized
    apply scope.letSeparated selectedTarget
    · simpa [algorithmContext] using algorithmFree
    · exact selectedGeneralized
  refine WLetBindingRel.ofRealized ?_ ?_
  · rw [targetView.normalized_eq,
      ← DM.FrozenSig.generalize_scopeOfTyVars signature coreContext
        algorithmTarget]
    rw [DM.generalize_emb signatureClosed.signatureTargets]
    rfl
  · intro target instantiation
    rw [Scheme.applyMeta_id, targetView.normalized_eq,
      ← DM.FrozenSig.generalize_scopeOfTyVars signature coreContext
        algorithmTarget]
    exact relation.realizedBy signatureClosed.signatureTargets
      (post := SSubst.paired residual) rfl instantiation

/-- Consume an erasure-stable value boundary at `let`: build its semantic
generalized binding and register the just-closed variables as retired.  The
result feeds `WRetiredStableFrameAt.protectLetBody` directly. -/
theorem w_prepareErasedLetBindingAndRetire
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing : Subst}
    {frames : List (Context × SCtx)}
    {larger smaller : List (Ty × STy)} {pending : List PendingLetCut}
    {rawContext : Context} {selectedContext : SCtx}
    {rawTarget : Ty} {selectedTarget : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames larger pending)
    (signatureClosed : signature.SchemesClosed)
    (view : ErasedDMView residual selectedContext selectedTarget
      (rawContext.applySubst prevailing) (prevailing.apply rawTarget))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (schemeFixed :
      (signature.generalize (rawContext.applySubst prevailing)
        (prevailing.apply rawTarget)).applyMeta prevailing =
      signature.generalize (rawContext.applySubst prevailing)
        (prevailing.apply rawTarget))
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (newFresh : ∀ pair ∈ smaller,
      (PendingLetCut.mk rawContext rawTarget prevailing).AvoidsTy
        signature prevailing pair.1)
    (newContextsFresh : ∀ pair ∈ frames,
      (PendingLetCut.mk rawContext rawTarget prevailing).AvoidsContext
        signature prevailing (pair.1.applySubst prevailing))
    (newBelow :
      (∀ varId, varId ∈ signature.generalizedCapVars
          (rawContext.applySubst prevailing) (prevailing.apply rawTarget) →
        varId.id < supply.nextCap) ∧
      (∀ varId, varId ∈ signature.generalizedTyVars
          (rawContext.applySubst prevailing) (prevailing.apply rawTarget) →
        varId < supply.nextTy))
    (idempotent : prevailing.Idempotent) :
    WLetBindingRel (SSubst.paired residual) prevailing
        (signature.generalize (rawContext.applySubst prevailing)
          (prevailing.apply rawTarget))
        (SCtx.generalize selectedContext selectedTarget) ∧
      WRetiredStableFrameAt signature supply (SSubst.paired residual)
        prevailing frames smaller
        (PendingLetCut.mk rawContext rawTarget prevailing :: pending) := by
  have bindingAtId := view.letBinding signatureClosed scope
  have binding := bindingAtId.atFixedPrevailing schemeFixed
  exact ⟨binding,
    state.registerLetAfterDrop subset newFresh newContextsFresh newBelow
      idempotent⟩

end DM
end TypePM
