import TypePM.DamasMilnerWLet

/-!
# One-sort normalized views for Damas--Milner Algorithm W

The executable traversal works with the two-sort core syntax, whereas its
completeness competitor is a one-sort Damas--Milner derivation.  This file
records the precise boundary between the two representations.  A normalized
core context and target have explicit one-sort decodings, and one shared
one-sort residual explains both every free context use and the selected
target.

The invariant is deliberately independent of the recursive W result package.
It can therefore be transported structurally before it is installed in the
acceptance theorem.  Let generalization consumes one additional, explicit
binder-separation fact; that fact belongs to the retired-variable invariant,
not to normalization itself.
-/

namespace TypePM
namespace DM

/-! ## The target-only embedding of a one-sort residual -/

/-- Regard a one-sort substitution as a capability-inert core substitution. -/
def SSubst.paired (residual : SSubst) : Subst :=
  { cap := CapSubst.id, target := SSubst.emb residual }

/-- Applying a paired one-sort residual to an embedded simple type stays in
the exact one-sort image. -/
theorem SSubst.paired_apply_emb (residual : SSubst) (target : STy) :
    (SSubst.paired residual).apply target.emb =
      (target.applySubst residual).emb := by
  simp [SSubst.paired, Subst.apply, STy.emb_applyCapability,
    STy.emb_applyTarget]

/-! ## Context and target views -/

/-- A normalized core context has an exact one-sort decoding, and every use
selected from the declarative context is realized through the same residual. -/
structure NormalizedDMContextView (residual : SSubst)
    (algorithmContext selectedContext : SCtx)
    (normalizedContext : Context) : Prop where
  normalized_eq : normalizedContext = algorithmContext.emb
  related : WContextRel (SSubst.paired residual)
    normalizedContext selectedContext

/-- A normalized core target has an exact one-sort decoding whose residual
image is the target selected by the declarative derivation. -/
structure NormalizedDMTargetView (residual : SSubst)
    (algorithmTarget selectedTarget : STy)
    (normalizedTarget : Ty) : Prop where
  normalized_eq : normalizedTarget = algorithmTarget.emb
  residual_eq : algorithmTarget.applySubst residual = selectedTarget

/-- The context and target views used at one W synthesis boundary. -/
structure NormalizedDMView (residual : SSubst)
    (algorithmContext selectedContext : SCtx)
    (algorithmTarget selectedTarget : STy)
    (normalizedContext : Context) (normalizedTarget : Ty) : Prop where
  context : NormalizedDMContextView residual algorithmContext
    selectedContext normalizedContext
  target : NormalizedDMTargetView residual algorithmTarget
    selectedTarget normalizedTarget

/-- The target decoder succeeds with the displayed algorithmic simple type. -/
theorem NormalizedDMTargetView.decode
    {residual : SSubst} {algorithmTarget selectedTarget : STy}
    {normalizedTarget : Ty}
    (view : NormalizedDMTargetView residual algorithmTarget selectedTarget
      normalizedTarget) :
    STy.ofTy? normalizedTarget = some algorithmTarget := by
  rw [view.normalized_eq]
  exact STy.ofTy?_emb algorithmTarget

/-- In particular, a normalized target is in the exact DM fragment. -/
theorem NormalizedDMTargetView.inDMFragment
    {residual : SSubst} {algorithmTarget selectedTarget : STy}
    {normalizedTarget : Ty}
    (view : NormalizedDMTargetView residual algorithmTarget selectedTarget
      normalizedTarget) :
    InFragmentTy normalizedTarget := by
  rw [view.normalized_eq]
  exact STy.emb_inDMFragment algorithmTarget

/-! ## Initial, variable, and literal boundaries -/

/-- The embedded declarative context is the initial normalized context. -/
theorem NormalizedDMContextView.initial (context : SCtx) :
    NormalizedDMContextView SSubst.id context context context.emb := by
  exact ⟨rfl, WContextRel.emb_id context⟩

/-- An embedded selected target is its own initial normalized target. -/
theorem NormalizedDMTargetView.initial (target : STy) :
    NormalizedDMTargetView SSubst.id target target target.emb := by
  exact ⟨rfl, STy.applySubst_id target⟩

/-- Initial normalization of a complete context/target boundary. -/
theorem NormalizedDMView.initial (context : SCtx) (target : STy) :
    NormalizedDMView SSubst.id context context target target
      context.emb target.emb := by
  exact ⟨NormalizedDMContextView.initial context,
    NormalizedDMTargetView.initial target⟩

/-- A variable occurrence introduces no structural change to an already
normalized context/target boundary.  The lookup and instantiation hypotheses
make the theorem line up exactly with `DM.Typing.var`; production of the raw
opening is handled by the W variable helper. -/
theorem NormalizedDMView.var
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    {normalizedContext : Context} {normalizedTarget : Ty}
    {name : String} {scheme : SScheme}
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget normalizedContext normalizedTarget)
    (_found : selectedContext.find? name = some scheme)
    (_instantiation : scheme.Inst selectedTarget) :
    NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget normalizedContext normalizedTarget :=
  view

/-- Canonical executable instantiation has an exact one-sort target view for
every declarative use of the same DM scheme.  The residual is the principal
one-sort instance supplied by the canonical positional opening. -/
theorem NormalizedDMTargetView.canonicalScheme
    {scheme : SScheme} {selectedTarget : STy}
    (supply : InferenceBase.FreshSupply)
    (instantiation : scheme.Inst selectedTarget)
    (fresh : TyVarsBelow supply.nextTy scheme.body.ftv) :
    ∃ algorithmTarget residual,
      NormalizedDMTargetView residual algorithmTarget selectedTarget
        (InferenceBase.instantiateScheme supply scheme.emb).value := by
  have principal := scheme.canonicalTarget_principal instantiation fresh
  rcases principal with ⟨residual, _support, equation⟩
  exact ⟨scheme.canonicalTarget supply.nextTy, residual,
    { normalized_eq := scheme.canonicalTarget_emb supply
      residual_eq := equation }⟩

/-- Variable normalization combines an unchanged normalized context with the
canonical one-sort target produced by executable scheme instantiation. -/
theorem NormalizedDMTargetView.canonicalVar
    {scheme : SScheme}
    {selectedTarget : STy}
    (supply : InferenceBase.FreshSupply)
    (instantiation : scheme.Inst selectedTarget)
    (fresh : TyVarsBelow supply.nextTy scheme.body.ftv) :
    ∃ algorithmTarget targetResidual,
      NormalizedDMTargetView targetResidual algorithmTarget selectedTarget
        (InferenceBase.instantiateScheme supply scheme.emb).value :=
  NormalizedDMTargetView.canonicalScheme supply instantiation fresh

/-- Integer literals have the canonical one-sort target under every residual. -/
theorem NormalizedDMTargetView.lit (residual : SSubst) :
    NormalizedDMTargetView residual STy.int STy.int Ty.int := by
  exact ⟨rfl, rfl⟩

/-- Literal normalization over any already-normalized context. -/
theorem NormalizedDMView.lit
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {normalizedContext : Context}
    (context : NormalizedDMContextView residual algorithmContext
      selectedContext normalizedContext) :
    NormalizedDMView residual algorithmContext selectedContext
      STy.int STy.int normalizedContext Ty.int :=
  ⟨context, NormalizedDMTargetView.lit residual⟩

/-! ## Lambda structure -/

/-- A residual-related monomorphic binding extends a normalized context. -/
theorem NormalizedDMContextView.consMono
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {normalizedContext : Context} {algorithmDomain selectedDomain : STy}
    (outer : NormalizedDMContextView residual algorithmContext
      selectedContext normalizedContext)
    (domain : algorithmDomain.applySubst residual = selectedDomain)
    (name : String) :
    NormalizedDMContextView residual
      ((name, SScheme.mono algorithmDomain) :: algorithmContext)
      ((name, SScheme.mono selectedDomain) :: selectedContext)
      ((name, Scheme.mono algorithmDomain.emb) :: normalizedContext) := by
  refine ⟨?_, ?_⟩
  · rw [outer.normalized_eq]
    simp only [SCtx.emb, List.map_cons, SScheme.emb_mono]
  · apply WContextRel.cons (name := name) rfl
    · apply SScheme.mono_realizedBy
      rw [SSubst.paired_apply_emb, domain]
    · exact outer.related

/-- Function formation preserves a common one-sort residual. -/
theorem NormalizedDMTargetView.fn
    {residual : SSubst}
    {algorithmDomain selectedDomain algorithmCodomain selectedCodomain : STy}
    {normalizedDomain normalizedCodomain : Ty}
    (domain : NormalizedDMTargetView residual algorithmDomain selectedDomain
      normalizedDomain)
    (codomain : NormalizedDMTargetView residual algorithmCodomain
      selectedCodomain normalizedCodomain) :
    NormalizedDMTargetView residual
      (.fn algorithmDomain algorithmCodomain)
      (.fn selectedDomain selectedCodomain)
      (.fn normalizedDomain normalizedCodomain) := by
  constructor
  · rw [domain.normalized_eq, codomain.normalized_eq]
    rfl
  · simp only [STy.applySubst, domain.residual_eq, codomain.residual_eq]

/-- Close a normalized lambda body back over its outer context. -/
theorem NormalizedDMView.lam
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {normalizedContext : Context}
    {algorithmDomain selectedDomain algorithmCodomain selectedCodomain : STy}
    {normalizedDomain normalizedCodomain : Ty}
    (outer : NormalizedDMContextView residual algorithmContext
      selectedContext normalizedContext)
    (domain : NormalizedDMTargetView residual algorithmDomain selectedDomain
      normalizedDomain)
    (codomain : NormalizedDMTargetView residual algorithmCodomain
      selectedCodomain normalizedCodomain) :
    NormalizedDMView residual algorithmContext selectedContext
      (.fn algorithmDomain algorithmCodomain)
      (.fn selectedDomain selectedCodomain)
      normalizedContext (.fn normalizedDomain normalizedCodomain) :=
  ⟨outer, NormalizedDMTargetView.fn domain codomain⟩

/-! ## Tuple structure -/

/-- Pointwise normalized views for a tuple's target list. -/
inductive NormalizedDMTargetsView (residual : SSubst) :
    List STy → List STy → List Ty → Prop where
  | nil : NormalizedDMTargetsView residual [] [] []
  | cons {algorithmTarget selectedTarget : STy} {normalizedTarget : Ty}
      {algorithmTargets selectedTargets : List STy}
      {normalizedTargets : List Ty} :
      NormalizedDMTargetView residual algorithmTarget selectedTarget
        normalizedTarget →
      NormalizedDMTargetsView residual algorithmTargets selectedTargets
        normalizedTargets →
      NormalizedDMTargetsView residual
        (algorithmTarget :: algorithmTargets)
        (selectedTarget :: selectedTargets)
        (normalizedTarget :: normalizedTargets)

/-- Tuple formation folds pointwise views into a product view. -/
theorem NormalizedDMTargetsView.prod
    {residual : SSubst} {algorithmTargets selectedTargets : List STy}
    {normalizedTargets : List Ty}
    (views : NormalizedDMTargetsView residual algorithmTargets
      selectedTargets normalizedTargets) :
    NormalizedDMTargetView residual (.prod algorithmTargets)
      (.prod selectedTargets) (.prod normalizedTargets) := by
  induction views with
  | nil => exact ⟨rfl, rfl⟩
  | @cons algorithmTarget selectedTarget normalizedTarget
      algorithmTargets selectedTargets normalizedTargets head tail induction =>
      constructor
      · simp only [STy.emb, STy.embList]
        apply congrArg Ty.prod
        rw [head.normalized_eq]
        exact congrArg (List.cons algorithmTarget.emb)
          (Ty.prod.inj induction.normalized_eq)
      · simp only [STy.applySubst, STy.applySubstList]
        apply congrArg STy.prod
        rw [head.residual_eq]
        exact congrArg (List.cons selectedTarget)
          (STy.prod.inj induction.residual_eq)

/-- Tuple normalization over a shared normalized context. -/
theorem NormalizedDMView.tuple
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {normalizedContext : Context}
    {algorithmTargets selectedTargets : List STy}
    {normalizedTargets : List Ty}
    (context : NormalizedDMContextView residual algorithmContext
      selectedContext normalizedContext)
    (targets : NormalizedDMTargetsView residual algorithmTargets
      selectedTargets normalizedTargets) :
    NormalizedDMView residual algorithmContext selectedContext
      (.prod algorithmTargets) (.prod selectedTargets)
      normalizedContext (.prod normalizedTargets) :=
  ⟨context, targets.prod⟩

/-! ## Let-generalization bridge -/

/-- Binder separation upgrades a normalized view to the residual relation
consumed by DM let generalization. -/
theorem NormalizedDMView.generalizationResidual
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    {normalizedContext : Context} {normalizedTarget : Ty}
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget normalizedContext normalizedTarget)
    (separated :
      ∀ {algorithmVar selectedBinder : TypePM.TyVar},
        algorithmVar ∈ SCtx.ftv algorithmContext →
        selectedBinder ∈
          (SCtx.generalize selectedContext selectedTarget).binders →
        selectedBinder ∉ (residual algorithmVar).ftv) :
    GeneralizationResidual residual algorithmContext selectedContext
      algorithmTarget selectedTarget :=
  ⟨view.target.residual_eq, separated⟩

/-- A normalized view plus retired-variable separation supplies the precise
generalized binding relation used by the executable let body. -/
theorem NormalizedDMView.letBinding
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    {normalizedContext : Context} {normalizedTarget : Ty}
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget normalizedContext normalizedTarget)
    (separated :
      ∀ {algorithmVar selectedBinder : TypePM.TyVar},
        algorithmVar ∈ SCtx.ftv algorithmContext →
        selectedBinder ∈
          (SCtx.generalize selectedContext selectedTarget).binders →
        selectedBinder ∉ (residual algorithmVar).ftv) :
    WLetBindingRel (SSubst.paired residual) Subst.id
      (signature.generalize normalizedContext normalizedTarget)
      (SCtx.generalize selectedContext selectedTarget) := by
  have relation := view.generalizationResidual separated
  rw [view.context.normalized_eq, view.target.normalized_eq]
  refine WLetBindingRel.ofRealized ?_ ?_
  · rw [DM.generalize_emb signatureClosed]
    rfl
  · intro target instantiation
    have use := relation.realizedBy signatureClosed
      (post := SSubst.paired residual) rfl instantiation
    simpa only [SSubst.paired, Scheme.applyMeta_id] using use

end DM
end TypePM
