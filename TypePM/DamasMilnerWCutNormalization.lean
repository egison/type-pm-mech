import TypePM.DamasMilnerWCompleteSteps
import TypePM.DamasMilnerWNormalizedOpening

/-!
# Erasure-stable normalization across Algorithm W cuts

Exact embedding is useful at constructor boundaries, but an intermediate
paired MGU is specified semantically and need not expose a syntactic
one-sort image.  The relations below retain precisely the facts needed after
such a cut: the core context still realizes the selected DM context under one
paired residual, and the core target erases to a one-sort target whose image
under that residual is the selected target.
-/

namespace TypePM
namespace DM

/-! ## Erasure commutes with paired one-sort substitution -/

mutual

theorem eraseTy_applyTarget_emb (residual : SSubst) : ∀ target : Ty,
    eraseTy (target.applyTarget (SSubst.emb residual)) =
      (eraseTy target).applySubst residual
  | .var name => by
      simp [Ty.applyTarget, eraseTy, STy.applySubst, SSubst.emb]
  | .skolem name => by
      simp [Ty.applyTarget, eraseTy, STy.applySubst]
  | .unit => by
      simp [Ty.applyTarget, eraseTy, STy.applySubst]
  | .int => by
      simp [Ty.applyTarget, eraseTy, STy.applySubst]
  | .bool => by
      simp [Ty.applyTarget, eraseTy, STy.applySubst]
  | .data name children => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      congr 1
      exact eraseTys_applyTarget_emb residual children
  | .prod components => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      congr 1
      exact eraseTys_applyTarget_emb residual components
  | .fn domain codomain => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      rw [eraseTy_applyTarget_emb residual domain,
        eraseTy_applyTarget_emb residual codomain]
  | .matcher capability target => by
      simp only [Ty.applyTarget, eraseTy]
      exact eraseTy_applyTarget_emb residual target
  | .slot capability target => by
      simp only [Ty.applyTarget, eraseTy]
      exact eraseTy_applyTarget_emb residual target

theorem eraseTys_applyTarget_emb (residual : SSubst) : ∀ targets : List Ty,
    eraseTys (Ty.applyTargetList (SSubst.emb residual) targets) =
      STy.applySubstList residual (eraseTys targets)
  | [] => rfl
  | target :: targets => by
      simp only [Ty.applyTargetList, eraseTys, STy.applySubstList]
      rw [eraseTy_applyTarget_emb residual target,
        eraseTys_applyTarget_emb residual targets]

end

theorem eraseTy_apply_paired (residual : SSubst) (target : Ty) :
    eraseTy ((SSubst.paired residual).apply target) =
      (eraseTy target).applySubst residual := by
  rw [SSubst.paired, Subst.apply, Ty.applyCapability_id]
  exact eraseTy_applyTarget_emb residual target

/-! ## Total erasure decoding of an arbitrary core substitution -/

/-- Decode a core substitution by erasing each target image.  Unlike exact
decoding, this operation is total even when a solver image contains a core
wrapper or another type constructor outside the DM image. -/
def SSubst.eraseCore (delta : Subst) : SSubst :=
  fun varId => eraseTy (delta.target varId)

mutual

theorem eraseTy_applyCapability (capability : CapSubst) : ∀ target : Ty,
    eraseTy (target.applyCapability capability) = eraseTy target
  | .var _ => rfl
  | .skolem _ => rfl
  | .unit => rfl
  | .int => rfl
  | .bool => rfl
  | .data _ children => by
      simp only [Ty.applyCapability, eraseTy]
      congr 1
      exact eraseTys_applyCapability capability children
  | .prod components => by
      simp only [Ty.applyCapability, eraseTy]
      congr 1
      exact eraseTys_applyCapability capability components
  | .fn domain codomain => by
      simp only [Ty.applyCapability, eraseTy]
      rw [eraseTy_applyCapability capability domain,
        eraseTy_applyCapability capability codomain]
  | .matcher _ target => by
      simp only [Ty.applyCapability, eraseTy]
      exact eraseTy_applyCapability capability target
  | .slot _ target => by
      simp only [Ty.applyCapability, eraseTy]
      exact eraseTy_applyCapability capability target

theorem eraseTys_applyCapability (capability : CapSubst) : ∀ targets : List Ty,
    eraseTys (Ty.applyCapabilityList capability targets) = eraseTys targets
  | [] => rfl
  | target :: targets => by
      simp only [Ty.applyCapabilityList, eraseTys]
      rw [eraseTy_applyCapability capability target,
        eraseTys_applyCapability capability targets]

end

mutual

theorem eraseTy_applyTarget (targetSubst : TySubst) : ∀ target : Ty,
    eraseTy (target.applyTarget targetSubst) =
      (eraseTy target).applySubst (fun varId => eraseTy (targetSubst varId))
  | .var name => rfl
  | .skolem _ => rfl
  | .unit => rfl
  | .int => rfl
  | .bool => rfl
  | .data _ children => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      congr 1
      exact eraseTys_applyTarget targetSubst children
  | .prod components => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      congr 1
      exact eraseTys_applyTarget targetSubst components
  | .fn domain codomain => by
      simp only [Ty.applyTarget, eraseTy, STy.applySubst]
      rw [eraseTy_applyTarget targetSubst domain,
        eraseTy_applyTarget targetSubst codomain]
  | .matcher _ target => by
      simp only [Ty.applyTarget, eraseTy]
      exact eraseTy_applyTarget targetSubst target
  | .slot _ target => by
      simp only [Ty.applyTarget, eraseTy]
      exact eraseTy_applyTarget targetSubst target

theorem eraseTys_applyTarget (targetSubst : TySubst) : ∀ targets : List Ty,
    eraseTys (Ty.applyTargetList targetSubst targets) =
      STy.applySubstList (fun varId => eraseTy (targetSubst varId))
        (eraseTys targets)
  | [] => rfl
  | target :: targets => by
      simp only [Ty.applyTargetList, eraseTys, STy.applySubstList]
      rw [eraseTy_applyTarget targetSubst target,
        eraseTys_applyTarget targetSubst targets]

end

/-- Erasure commutes with every core substitution after total decoding. -/
theorem eraseTy_apply_core (delta : Subst) (target : Ty) :
    eraseTy (delta.apply target) =
      (eraseTy target).applySubst (SSubst.eraseCore delta) := by
  rw [Subst.apply, eraseTy_applyTarget,
    eraseTy_applyCapability delta.cap target]
  rfl

/-! ## Reflection of a paired equation -/

mutual

/-- A paired one-sort post-substitution cannot hide a core-only constructor:
if its result is embedded, its input was already embedded. -/
theorem exists_eq_emb_of_paired_apply_eq_emb (residual : SSubst) :
    ∀ (core : Ty) (selected : STy),
      (SSubst.paired residual).apply core = selected.emb →
        ∃ algorithm : STy, core = algorithm.emb
  | .var name, _, _ => ⟨.var name, rfl⟩
  | .skolem _, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation
  | .unit, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation
  | .int, _, _ => ⟨.int, rfl⟩
  | .bool, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation
  | .data name children, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation
  | .prod components, selected, equation => by
      cases selected with
      | prod selected =>
          simp only [SSubst.paired, Subst.apply, Ty.applyCapability_id,
            Ty.applyTarget, STy.emb] at equation
          injection equation with componentsEq
          obtain ⟨algorithm, algorithmEq⟩ :=
            exists_eq_embList_of_paired_apply_eq_emb residual components
              selected componentsEq
          exact ⟨.prod algorithm, congrArg Ty.prod algorithmEq⟩
      | var _ =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
      | int =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
      | fn _ _ =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
  | .fn domain codomain, selected, equation => by
      cases selected with
      | fn selectedDomain selectedCodomain =>
          simp only [SSubst.paired, Subst.apply, Ty.applyCapability_id,
            Ty.applyTarget, STy.emb] at equation
          injection equation with domainEq codomainEq
          have domainEq' : (SSubst.paired residual).apply domain =
              selectedDomain.emb := by
            simpa [SSubst.paired, Subst.apply, Ty.applyCapability_id] using
              domainEq
          have codomainEq' : (SSubst.paired residual).apply codomain =
              selectedCodomain.emb := by
            simpa [SSubst.paired, Subst.apply, Ty.applyCapability_id] using
              codomainEq
          obtain ⟨algorithmDomain, rfl⟩ :=
            exists_eq_emb_of_paired_apply_eq_emb residual domain selectedDomain
              domainEq'
          obtain ⟨algorithmCodomain, rfl⟩ :=
            exists_eq_emb_of_paired_apply_eq_emb residual codomain
              selectedCodomain codomainEq'
          exact ⟨.fn algorithmDomain algorithmCodomain, rfl⟩
      | var _ =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
      | int =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
      | prod _ =>
          simp [SSubst.paired, Subst.apply, Ty.applyCapability,
            Ty.applyTarget, STy.emb] at equation
  | .matcher capability target, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation
  | .slot capability target, selected, equation => by
      cases selected <;>
        simp [SSubst.paired, Subst.apply, Ty.applyCapability,
          Ty.applyTarget, STy.emb] at equation

theorem exists_eq_embList_of_paired_apply_eq_emb (residual : SSubst) :
    ∀ (cores : List Ty) (selected : List STy),
      Ty.applyTargetList (SSubst.emb residual) cores =
          STy.embList selected →
        ∃ algorithms : List STy, cores = STy.embList algorithms
  | [], [], _ => ⟨[], rfl⟩
  | [], _ :: _, equation => by
      simp [Ty.applyTargetList, STy.embList] at equation
  | _ :: _, [], equation => by
      simp [Ty.applyTargetList, STy.embList] at equation
  | core :: cores, selected :: selecteds, equation => by
      simp only [Ty.applyTargetList, STy.embList, List.cons.injEq] at equation
      obtain ⟨headEq, tailEq⟩ := equation
      have pairedHead : (SSubst.paired residual).apply core = selected.emb := by
        simpa [SSubst.paired, Subst.apply, Ty.applyCapability_id] using headEq
      obtain ⟨algorithm, algorithmEq⟩ :=
        exists_eq_emb_of_paired_apply_eq_emb residual core selected pairedHead
      obtain ⟨algorithms, algorithmsEq⟩ :=
        exists_eq_embList_of_paired_apply_eq_emb residual cores selecteds tailEq
      exact ⟨algorithm :: algorithms, by
        simp only [STy.embList]
        rw [algorithmEq, algorithmsEq]⟩

end

/-! ## Weak normalized views -/

/-- Semantic context view stable under every ordinary W cut. -/
structure ErasedDMContextView (residual : SSubst)
    (selectedContext : SCtx) (coreContext : Context) : Prop where
  related : WContextRel (SSubst.paired residual) coreContext selectedContext

/-- Target view which permits extra core syntax but fixes its one-sort
meaning under the displayed residual. -/
structure ErasedDMTargetView (residual : SSubst)
    (selectedTarget : STy) (coreTarget : Ty) : Prop where
  realized : (SSubst.paired residual).apply coreTarget = selectedTarget.emb

structure ErasedDMView (residual : SSubst)
    (selectedContext : SCtx) (selectedTarget : STy)
    (coreContext : Context) (coreTarget : Ty) : Prop where
  context : ErasedDMContextView residual selectedContext coreContext
  target : ErasedDMTargetView residual selectedTarget coreTarget

theorem ErasedDMTargetView.erasure
    {residual : SSubst} {selectedTarget : STy} {coreTarget : Ty}
    (view : ErasedDMTargetView residual selectedTarget coreTarget) :
    (eraseTy coreTarget).applySubst residual = selectedTarget := by
  rw [← eraseTy_apply_paired]
  rw [view.realized, eraseTy_emb]

/-- A paired target equation reflects all the way back to an exact normalized
target.  This is the target-only recovery used for retained frontier entries
after one or more absorbed cuts. -/
theorem ErasedDMTargetView.toNormalized
    {residual : SSubst} {selectedTarget : STy} {coreTarget : Ty}
    (view : ErasedDMTargetView residual selectedTarget coreTarget) :
    ∃ algorithmTarget : STy,
      NormalizedDMTargetView residual algorithmTarget selectedTarget
        coreTarget := by
  obtain ⟨algorithmTarget, normalized⟩ :=
    exists_eq_emb_of_paired_apply_eq_emb residual coreTarget selectedTarget
      view.realized
  refine ⟨algorithmTarget, normalized, ?_⟩
  have embedded :
      (algorithmTarget.applySubst residual).emb = selectedTarget.emb := by
    rw [← SSubst.paired_apply_emb, ← normalized]
    exact view.realized
  exact STy.emb_injective embedded

/-- Direct target-only form for a paired frontier equation. -/
theorem NormalizedDMTargetView.ofPairedEquation
    {residual : SSubst} {selectedTarget : STy} {coreTarget : Ty}
    (equation : (SSubst.paired residual).apply coreTarget =
      selectedTarget.emb) :
    ∃ algorithmTarget : STy,
      NormalizedDMTargetView residual algorithmTarget selectedTarget
        coreTarget :=
  ErasedDMTargetView.toNormalized ⟨equation⟩

/-- Exact normalization implies the erasure-stable view. -/
theorem NormalizedDMView.toErased
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    {coreContext : Context} {coreTarget : Ty}
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget coreContext coreTarget) :
    ErasedDMView residual selectedContext selectedTarget coreContext
      coreTarget := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact view.context.related
  · rw [view.target.normalized_eq, SSubst.paired_apply_emb,
      view.target.residual_eq]

/-! ## Cut transport -/

/-- Absorbing an arbitrary core cut into the common post-substitution keeps
the selected context realized.  This is the context half of cut
normalization and requires no syntactic closure property of the cut image. -/
theorem ErasedDMContextView.applyAbsorbed
    {residual : SSubst} {delta : Subst}
    {selectedContext : SCtx} {coreContext : Context}
    (view : ErasedDMContextView residual selectedContext coreContext)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ErasedDMContextView residual selectedContext
      (coreContext.applySubst delta) := by
  exact ⟨WContextRel.applySubst view.related factor⟩

/-- Absorbing an arbitrary core cut into the common post-substitution keeps
the selected target realized. -/
theorem ErasedDMTargetView.applyAbsorbed
    {residual : SSubst} {delta : Subst}
    {selectedTarget : STy} {coreTarget : Ty}
    (view : ErasedDMTargetView residual selectedTarget coreTarget)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ErasedDMTargetView residual selectedTarget (delta.apply coreTarget) := by
  refine ⟨?_⟩
  rw [← Subst.seq_apply, ← factor]
  exact view.realized

/-- Exact target normalization is recovered after an absorbed cut by paired
reflection.  The decoder is existential because an abstract solver cut need
not expose a syntactic one-sort substitution. -/
theorem NormalizedDMTargetView.applyAbsorbedCut
    {residual : SSubst} {delta : Subst}
    {algorithmTarget selectedTarget : STy} {coreTarget : Ty}
    (view : NormalizedDMTargetView residual algorithmTarget selectedTarget
      coreTarget)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ∃ algorithmTarget' : STy,
      NormalizedDMTargetView residual algorithmTarget' selectedTarget
        (delta.apply coreTarget) := by
  let erased : ErasedDMTargetView residual selectedTarget coreTarget :=
    ⟨by
      rw [view.normalized_eq, SSubst.paired_apply_emb,
        view.residual_eq]⟩
  exact (erased.applyAbsorbed factor).toNormalized

/-- Combined erasure-stable transport across an absorbed core cut. -/
theorem ErasedDMView.applyAbsorbed
    {residual : SSubst} {delta : Subst}
    {selectedContext : SCtx} {selectedTarget : STy}
    {coreContext : Context} {coreTarget : Ty}
    (view : ErasedDMView residual selectedContext selectedTarget
      coreContext coreTarget)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ErasedDMView residual selectedContext selectedTarget
      (coreContext.applySubst delta) (delta.apply coreTarget) := by
  exact ⟨view.context.applyAbsorbed factor,
    view.target.applyAbsorbed factor⟩

/-- The moved protected frame supplies an erasure-stable view immediately
after an exact paired cut.  No claim that the MGU exposes an embedded syntax
tree is needed. -/
theorem ErasedDMView.afterLetStableExactPairedCut
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing delta : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {left right : Ty}
    {leftSelected rightSelected : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames frontier pending)
    (solverCut : LetStableExactPairedCut signature prevailing pending
      left right delta)
    (signatureClosed : signature.SchemesClosed)
    (leftMember : (left, leftSelected) ∈ frontier)
    (rightMember : (right, rightSelected) ∈ frontier)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta)
    {rawContext : Context} {selectedContext : SCtx}
    (active : (rawContext, selectedContext) ∈ frames)
    {oldTarget : Ty} {selectedTarget : STy}
    (targetMember : (oldTarget, selectedTarget) ∈ frontier) :
    ErasedDMView residual selectedContext selectedTarget
      (rawContext.applySubst (Subst.seq delta prevailing))
      (delta.apply oldTarget) := by
  let moved := state.applyLetStableExactPairedCut solverCut signatureClosed
    leftMember rightMember factor
  have mappedMember : (delta.apply oldTarget, selectedTarget) ∈
      frontier.map (fun pair => (delta.apply pair.1, pair.2)) :=
    List.mem_map.mpr ⟨(oldTarget, selectedTarget), targetMember, rfl⟩
  exact
    { context := ⟨moved.stable.frame.contexts active⟩
      target := ⟨moved.stable.frame.types mappedMember⟩ }

/-! ## Let-opening connection -/

/-- The normalized-opening theorem supplies the exact paired residual needed
to lift a selected DM use back to a core value opening.  This is the local
inverse direction absent from `SchemeErases`; it is the building block for
an erasure-based let-generalization bridge. -/
theorem SScheme.erasedOpeningLift
    (scheme : SScheme) (ambient : SSubst)
    (supply : InferenceBase.FreshSupply) {target : STy}
    (instantiation :
      (scheme.emb.applyMeta (SSubst.paired ambient)).ValueFlowInst target.emb) :
    ∃ opening residual,
      (scheme.emb.applyMeta (SSubst.paired ambient)).openValue opening =
        target.emb ∧
      extendSchemeOpening (SSubst.paired ambient) supply scheme.emb opening =
        SSubst.paired residual := by
  obtain ⟨opening, residual, opened, _normalized, paired⟩ :=
    scheme.normalized_valueFlowInst_pairedExtension ambient supply instantiation
  exact ⟨opening, residual, opened, paired⟩

end DM
end TypePM
