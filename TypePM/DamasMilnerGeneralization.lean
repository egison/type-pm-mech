import TypePM.DamasMilnerAcceptance

/-!
# Residual factorization for Damas--Milner let generalization

Algorithm W reaches a `let` boundary with an algorithmic context and value
type which need not be syntactically equal to the context and type selected by
a declarative DM derivation.  They are related by the current one-sort
residual substitution.  The residual is fixed on variables owned by the
algorithmic environment; variables generalized at the boundary may be chosen
afresh for each subsequent use of the scheme.

The distinction is essential.  Requiring every use to factor through one
fixed total substitution is false even for `forall a. a`: a finite-support
substitution sending `x` to `y` has no preimage for the legal use `x`.
`FactorsUsesAlong` therefore asks for a use-local extension which agrees with
the boundary residual on the displayed rigid scope.
-/

namespace TypePM
namespace DM

/-! ## A residual which is stable across generalization -/

/--
The selected value is the residual image of the algorithmic value, and no
variable generalized by the selected scheme occurs in the residual image of
an algorithmic environment variable.  Consequently a later instantiation of
the selected scheme cannot change the already-established environment part of
the residual.
-/
structure GeneralizationResidual (residual : SSubst)
    (algorithmContext selectedContext : SCtx)
    (algorithmTarget selectedTarget : STy) : Prop where
  target_eq : algorithmTarget.applySubst residual = selectedTarget
  environment_stable :
    ∀ {algorithmVar selectedBinder : TypePM.TyVar},
      algorithmVar ∈ SCtx.ftv algorithmContext →
      selectedBinder ∈ (SCtx.generalize selectedContext selectedTarget).binders →
      selectedBinder ∉ (residual algorithmVar).ftv

/-- A substitution agrees with a boundary residual on a finite rigid scope. -/
def SSubst.ExtendsOn (post residual : SSubst)
    (rigid : List TypePM.TyVar) : Prop :=
  ∀ name, name ∈ rigid → post name = residual name

/--
Every use of `specific` factors through a use of `general`, followed by a
use-local extension of `residual`.  The extension must retain the residual on
the variables owned by the algorithmic environment.
-/
def SScheme.FactorsUsesAlong (residual : SSubst)
    (rigid : List TypePM.TyVar) (general specific : SScheme) : Prop :=
  ∀ {target : STy}, specific.Inst target →
    ∃ raw post,
      general.Inst raw ∧
      post.ExtendsOn residual rigid ∧
      raw.applySubst post = target

/-- Exact compatibility predicate at an executable let-generalization cut.
It deliberately compares schemes after closing their generalized variables:
an equation merely between the two raw value types is not sufficient in the
presence of binder-name collisions. -/
def EmbeddedGeneralizationResidual (post : Subst) (signature : FrozenSig)
    (algorithmContext : SCtx) (algorithmTarget : STy)
    (selectedContext : SCtx) (selectedTarget : STy) : Prop :=
  (signature.generalize algorithmContext.emb algorithmTarget.emb).applyMeta post =
    (SCtx.generalize selectedContext selectedTarget).emb

/-! ## Substitution stability -/

/-- A binder-supported substitution is invisible on a type disjoint from the
binders. -/
theorem STy.applySubst_eq_self_of_binders_disjoint
    {chosen : SSubst} {binders : List TypePM.TyVar} {target : STy}
    (support : chosen.SupportWithin binders)
    (disjoint : ∀ name, name ∈ target.ftv → name ∉ binders) :
    target.applySubst chosen = target := by
  calc
    target.applySubst chosen = target.applySubst SSubst.id := by
      apply STy.applySubst_eq_of_ftv_agree
      intro name free
      simpa [SSubst.id] using support name (disjoint name free)
    _ = target := STy.applySubst_id target

/-- Instantiating the selected generalized variables after the boundary
residual preserves that residual on every algorithmic environment variable. -/
theorem GeneralizationResidual.comp_extendsOn
    {residual chosen : SSubst}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : GeneralizationResidual residual algorithmContext
      selectedContext algorithmTarget selectedTarget)
    (support : chosen.SupportWithin
      (SCtx.generalize selectedContext selectedTarget).binders) :
    (SSubst.comp chosen residual).ExtendsOn residual
      (SCtx.ftv algorithmContext) := by
  intro algorithmVar inEnvironment
  unfold SSubst.comp
  apply STy.applySubst_eq_self_of_binders_disjoint support
  intro selectedVar free inBinders
  exact relation.environment_stable inEnvironment inBinders free

/-! ## Generalization factorization -/

/--
Let generalization transports all subsequent selected-scheme uses through the
same environment residual.  Only the freshly generalized part of the
residual is extended separately for each use.
-/
theorem SCtx.generalize_factorsUsesAlong
    {residual : SSubst}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : GeneralizationResidual residual algorithmContext
      selectedContext algorithmTarget selectedTarget) :
    (SCtx.generalize algorithmContext algorithmTarget).FactorsUsesAlong
      residual (SCtx.ftv algorithmContext)
      (SCtx.generalize selectedContext selectedTarget) := by
  intro target instantiation
  rcases instantiation with ⟨chosen, support, targetEq⟩
  change selectedTarget.applySubst chosen = target at targetEq
  let post := SSubst.comp chosen residual
  refine ⟨algorithmTarget, post, ?_, ?_, ?_⟩
  · exact ⟨SSubst.id,
      SSubst.id_supportWithin
        (SCtx.generalize algorithmContext algorithmTarget).binders,
      STy.applySubst_id algorithmTarget⟩
  · exact relation.comp_extendsOn support
  · unfold post
    rw [← STy.applySubst_comp, relation.target_eq, targetEq]

/-- Exact normalization is the degenerate residual case and recovers ordinary
scheme generality. -/
theorem SCtx.generalize_moreGeneral_of_eq
    {firstContext secondContext : SCtx}
    {firstTarget secondTarget : STy}
    (contextEq : firstContext = secondContext)
    (targetEq : firstTarget = secondTarget) :
    (SCtx.generalize firstContext firstTarget).MoreGeneral
      (SCtx.generalize secondContext secondTarget) := by
  subst secondContext
  subst secondTarget
  exact SScheme.MoreGeneral.refl _

/-! ## Two-sort executable embedding -/

/-- A one-sort use of the algorithmic generalization is a value-flow use of
the executable two-sort generalization. -/
theorem FrozenSig.generalize_emb_valueFlowInst
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {context : SCtx} {source raw : STy}
    (instantiation : (SCtx.generalize context source).Inst raw) :
    (signature.generalize context.emb source.emb).ValueFlowInst raw.emb := by
  rw [generalize_emb signatureClosed]
  exact SScheme.emb_valueFlowInst instantiation

/-- Closed-scheme residual compatibility realizes every use selected by the
DM generalization. -/
theorem EmbeddedGeneralizationResidual.realizedBy
    {post : Subst} {signature : FrozenSig}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : EmbeddedGeneralizationResidual post signature
      algorithmContext algorithmTarget selectedContext selectedTarget) :
    (SCtx.generalize selectedContext selectedTarget).RealizedBy post
      (signature.generalize algorithmContext.emb algorithmTarget.emb) := by
  intro target instantiation
  rw [relation]
  exact SScheme.emb_valueFlowInst instantiation

/-! ## Deriving executable realization from a one-sort residual -/

/-- Every free target metavariable left by an embedded algorithmic
generalization belongs to its local environment. -/
theorem FrozenSig.generalize_emb_ftv_mem_context
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {context : SCtx} {target : STy} {varId : TypePM.TyVar}
    (free : varId ∈ (signature.generalize context.emb target.emb).ftv) :
    varId ∈ SCtx.ftv context := by
  let binders := signature.generalizedTyVars context.emb target.emb
  have sourceFree : varId ∈ target.emb.ftv :=
    (PolyTy.abstract_free_subset
      (fun candidate =>
        (signature.generalizedCapVars context.emb target.emb).finIdxOf?
          candidate)
      (fun candidate => binders.finIdxOf? candidate) target.emb).2 varId free
  have closingNone : binders.finIdxOf? varId = none :=
    (PolyTy.closing_none_of_abstract_free
      (fun candidate =>
        (signature.generalizedCapVars context.emb target.emb).finIdxOf?
          candidate)
      (fun candidate => binders.finIdxOf? candidate) target.emb).2 varId free
  have outside : varId ∉ binders :=
    List.finIdxOf?_eq_none_iff.mp closingNone
  by_cases inEnvironment : varId ∈ SCtx.ftv context
  · exact inEnvironment
  · exact (outside (by
      unfold binders FrozenSig.generalizedTyVars
      apply mem_generalizedTyVars sourceFree
      simpa [signatureClosed, SCtx.emb_ftv] using inEnvironment)).elim

/-- Embedded generalization contains no free capability metavariables. -/
theorem FrozenSig.generalize_emb_fcv_eq_nil
    (signature : FrozenSig) (context : SCtx) (target : STy) :
    (signature.generalize context.emb target.emb).fcv = [] := by
  unfold FrozenSig.generalize Scheme.generalize
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro varId free
  have sourceFree :=
    (PolyTy.abstract_free_subset
      (fun candidate =>
        (generalizedCapVars
          (signature.fcv ++ Context.fcv context.emb) target.emb).finIdxOf?
          candidate)
      (fun candidate =>
        (generalizedTyVars
          (signature.ftv ++ Context.ftv context.emb) target.emb).finIdxOf?
          candidate) target.emb).1 varId free
  rw [STy.emb_fcv] at sourceFree
  contradiction

/--
The one-sort residual condition is sufficient for the executable generalized
scheme to realize every use selected by the DM derivation.  The only extra
premises identify the core post with the target-only embedding of that
residual and close the frozen signature's target metavariables.

The proof applies the residual to the generalized scheme *before* opening its
binders.  A selected use then acts only on the residual image.  The
`environment_stable` field is exactly what makes that second action invisible
on the free part of the executable scheme.
-/
theorem GeneralizationResidual.realizedBy
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {residual : SSubst} {post : Subst}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : GeneralizationResidual residual algorithmContext
      selectedContext algorithmTarget selectedTarget)
    (post_eq : post =
      ({ cap := CapSubst.id, target := SSubst.emb residual } : Subst)) :
    (SCtx.generalize selectedContext selectedTarget).RealizedBy post
      (signature.generalize algorithmContext.emb algorithmTarget.emb) := by
  subst post
  intro target instantiation
  rcases instantiation with ⟨chosen, support, targetEq⟩
  change selectedTarget.applySubst chosen = target at targetEq
  let residualPost : Subst :=
    { cap := CapSubst.id, target := SSubst.emb residual }
  let chosenPost : Subst :=
    { cap := CapSubst.id, target := SSubst.emb chosen }
  have algorithmUse :
      (signature.generalize algorithmContext.emb algorithmTarget.emb).ValueFlowInst
        algorithmTarget.emb := by
    apply FrozenSig.generalize_emb_valueFlowInst signatureClosed
    exact ⟨SSubst.id,
      SSubst.id_supportWithin
        (SCtx.generalize algorithmContext algorithmTarget).binders,
      STy.applySubst_id algorithmTarget⟩
  have afterResidual := algorithmUse.transportVariable residualPost (by
    intro varId
    exact ⟨varId, rfl⟩)
  have residualTarget : residualPost.apply algorithmTarget.emb =
      selectedTarget.emb := by
    simp [residualPost, Subst.apply, STy.emb_applyCapability,
      STy.emb_applyTarget, relation.target_eq]
  rw [residualTarget] at afterResidual
  have afterUse := afterResidual.transportVariable chosenPost (by
    intro varId
    exact ⟨varId, rfl⟩)
  have schemeFixed :
      ((signature.generalize algorithmContext.emb algorithmTarget.emb).applyMeta
          residualPost).applyMeta chosenPost =
        (signature.generalize algorithmContext.emb algorithmTarget.emb).applyMeta
          residualPost := by
    rw [← Scheme.applyMeta_seq]
    apply Scheme.applyMeta_eq_of_free_agree
    · intro varId free
      rw [FrozenSig.generalize_emb_fcv_eq_nil] at free
      contradiction
    · intro varId free
      have inEnvironment := FrozenSig.generalize_emb_ftv_mem_context
        signatureClosed free
      have unchanged : (residual varId).applySubst chosen = residual varId := by
        apply STy.applySubst_eq_self_of_binders_disjoint support
        intro selectedBinder selectedFree selectedBound
        exact relation.environment_stable inEnvironment selectedBound
          selectedFree
      change chosenPost.apply (residual varId).emb = (residual varId).emb
      simp only [chosenPost, Subst.apply, STy.emb_applyCapability]
      rw [STy.emb_applyTarget, unchanged]
  rw [schemeFixed] at afterUse
  have chosenTarget : chosenPost.apply selectedTarget.emb = target.emb := by
    simp only [chosenPost, Subst.apply, STy.emb_applyCapability]
    rw [STy.emb_applyTarget, targetEq]
  rwa [chosenTarget] at afterUse

/--
Executable spelling of `SCtx.generalize_factorsUsesAlong`.  Each selected DM
use is obtained by opening the algorithmic executable scheme and then applying
a target-only extension of the same boundary residual.  Capability action is
identity throughout.
-/
theorem FrozenSig.generalize_emb_factorsUsesAlong
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {residual : SSubst}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : GeneralizationResidual residual algorithmContext
      selectedContext algorithmTarget selectedTarget) :
    ∀ {target : STy},
      (SCtx.generalize selectedContext selectedTarget).Inst target →
      ∃ (raw : STy) (post : SSubst),
        (signature.generalize algorithmContext.emb algorithmTarget.emb).ValueFlowInst
          raw.emb ∧
        post.ExtendsOn residual (SCtx.ftv algorithmContext) ∧
        ({ cap := CapSubst.id, target := SSubst.emb post } : Subst).apply raw.emb =
          target.emb := by
  intro target instantiation
  rcases SCtx.generalize_factorsUsesAlong relation instantiation with
    ⟨raw, post, rawUse, extension, equation⟩
  refine ⟨raw, post,
    TypePM.DM.FrozenSig.generalize_emb_valueFlowInst signatureClosed rawUse,
    extension, ?_⟩
  simp [Subst.apply, STy.emb_applyCapability, STy.emb_applyTarget, equation]

end DM
end TypePM
