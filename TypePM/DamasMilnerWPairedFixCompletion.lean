import TypePM.DamasMilnerWConstructorCompletion

/-!
# Paired direct-self fix completion

This module keeps the direct-self continuation construction separate from the
application package.  The recursive function and its argument allocate two
fresh one-sort targets, protect them on the old-free surface, and expose the
whole prepared frontier on the paired continuation surface.
-/

namespace TypePM
namespace DM

/-- Install a monomorphic function binding from two residual equations. -/
theorem ResidualContextScope.consMonoFn
    {residual : SSubst} {algorithmContext : Context}
    {selectedContext : SCtx} {domainVar codomainVar : TypePM.TyVar}
    {domain codomain : STy}
    (scope : ResidualContextScope residual algorithmContext selectedContext)
    (domainEq : residual domainVar = domain)
    (codomainEq : residual codomainVar = codomain) (name : String) :
    ResidualContextScope residual
      ((name, Scheme.mono (.fn (.var domainVar) (.var codomainVar))) ::
        algorithmContext)
      ((name, SScheme.mono (.fn domain codomain)) :: selectedContext) := by
  intro source image sourceFree imageFree
  simp only [Context.ftv, List.flatMap_cons, Scheme.ftv, Scheme.mono,
    PolyTy.ftv_lift, List.mem_append] at sourceFree
  simp only [SCtx.ftv, List.flatMap_cons]
  rcases sourceFree with head | outer
  · apply List.mem_append.mpr
    left
    rcases (by simpa [Ty.ftv] using head :
      source = domainVar ∨ source = codomainVar) with rfl | rfl
    · have inDomain : image ∈ domain.ftv := by
        simpa [domainEq] using imageFree
      simpa [SScheme.mono, SScheme.ftv, STy.ftv] using Or.inl inDomain
    · have inCodomain : image ∈ codomain.ftv := by
        simpa [codomainEq] using imageFree
      simpa [SScheme.mono, SScheme.ftv, STy.ftv] using Or.inr inCodomain
  · exact List.mem_append.mpr (Or.inr (scope outer imageFree))

private theorem OldContextCoveredAt.consFixTargetsAbove
    {floor supply : InferenceBase.FreshSupply} {owner active : Context}
    {self argument : String}
    (covered : OldContextCoveredAt floor owner active)
    (above : floor.nextTy ≤ supply.nextTy) :
    OldContextCoveredAt floor owner
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: active) := by
  have functionCovered : OldContextCoveredAt floor owner
      ((self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: active) := by
    constructor
    · intro varId free below
      simp only [Context.fcv, List.flatMap_cons, Scheme.fcv, Scheme.mono,
        PolyTy.fcv_lift, List.mem_append] at free
      rcases free with head | outer
      · simp [Ty.fcv] at head
      · exact covered.caps varId outer below
    · intro varId free below
      simp only [Context.ftv, List.flatMap_cons, Scheme.ftv, Scheme.mono,
        PolyTy.ftv_lift, List.mem_append] at free
      rcases free with head | outer
      · rcases (by simpa [Ty.ftv] using head :
          varId = supply.nextTy ∨ varId = supply.nextTy + 1) with rfl | rfl
        · exact False.elim (Nat.not_lt_of_ge above below)
        · exact False.elim
            (Nat.not_lt_of_ge (Nat.le_trans above (Nat.le_succ _)) below)
      · exact covered.targets varId outer below
  exact functionCovered.consFreshTargetAbove above

private theorem ProtectedContextsSuffix.consFixBody
    {rawContext : Context} {frames : List (Context × SCtx)}
    {self argument : String} {supply : InferenceBase.FreshSupply}
    {selectedBody : SCtx}
    (suffixes : ProtectedContextsSuffix rawContext frames) :
    ProtectedContextsSuffix
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
      (((argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
        selectedBody) :: frames) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨[], rfl⟩
  · rcases suffixes pair old with ⟨pre, equality⟩
    exact ⟨(argument, Scheme.mono (.var supply.nextTy)) ::
      (self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: pre,
      by simp [equality]⟩

/-- Prepare the fresh recursive function/argument bindings and the paired
continuation state consumed by the body callback. -/
theorem w_preparePairedFixBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {self argument : String}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {residual : SSubst}
    (state : WRetiredStableFrameAt signature supply (SSubst.paired residual)
      prevailing frames frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes residual prevailing frames)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (rawSuffix : ProvenanceContextSuffix provenanceContext rawContext)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing) provenanceFrames prevailing)
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations
      prevailing)
    (surfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations prevailing)
    (surfacesMembers : GenerativitySurfaceMembersAt generativityObligations
      prevailing frontier)
    (frontierNormalized : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1)
    (generativityContexts : GenerativitySurfaceContextsAt
      generativityObligations prevailing (rawContext.applySubst prevailing))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    (postAdmissible : AdmissiblePost [] (SSubst.paired residual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    Nonempty (WFixBodyPrepared signature supply prevailing rawContext self
      argument selectedContext domain codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending) := by
  let bodySupply : InferenceBase.FreshSupply :=
    { supply with nextTy := supply.nextTy + 2 }
  let bodyRawContext : Context :=
    (argument, Scheme.mono (.var supply.nextTy)) ::
      (self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext
  let bodySelectedContext : SCtx :=
    (argument, SScheme.mono domain) ::
      (self, SScheme.mono (.fn domain codomain)) :: selectedContext
  let bodyFrontier : List (Ty × STy) :=
    (.var supply.nextTy, domain) ::
      (.var (supply.nextTy + 1), codomain) :: frontier
  let bodyFrames : List (Context × SCtx) :=
    (bodyRawContext, bodySelectedContext) :: frames
  let residual' := SSubst.extendAppTargets residual supply domain codomain
  have preparedState : WRetiredStableFrameAt signature bodySupply
      (SSubst.paired residual') prevailing bodyFrames bodyFrontier pending := by
    rw [SSubst.paired_extendAppTargets]
    exact state.prepareFixBody active prevailingBounded state.pendingBelow
      domain codomain
  have domainEq : residual' supply.nextTy = domain := by
    simp [residual']
  have codomainEq : residual' (supply.nextTy + 1) = codomain := by
    simp [residual']
  have domainFixed : prevailing.apply (.var supply.nextTy) =
      .var supply.nextTy := Subst.BoundedBy.apply_freshTarget prevailingBounded
  have codomainFixed : prevailing.apply (.var (supply.nextTy + 1)) =
      .var (supply.nextTy + 1) :=
    Subst.BoundedBy.apply_targetAbove prevailingBounded (Nat.le_succ _)
  have extendedScope : ResidualContextScope residual'
      (rawContext.applySubst prevailing) selectedContext :=
    ResidualContextScope.extendAppTargets scope
      (state.stable.frame.contextsBounded active) domain codomain
  have selfScope : ResidualContextScope residual'
      ((self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext.applySubst prevailing)
      ((self, SScheme.mono (.fn domain codomain)) :: selectedContext) :=
    ResidualContextScope.consMonoFn extendedScope domainEq codomainEq self
  have bodyScope0 : ResidualContextScope residual'
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext.applySubst prevailing)
      ((argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) :=
    ResidualContextScope.consMono selfScope domainEq argument
  have bodyScope : ResidualContextScope residual'
      (bodyRawContext.applySubst prevailing) bodySelectedContext := by
    unfold bodyRawContext bodySelectedContext
    simp only [Context.applySubst, List.map_cons, Scheme.applyMeta_mono,
      Subst.apply_fn, domainFixed, codomainFixed]
    exact bodyScope0
  have bodyProtectedScopes : ProtectedResidualScopes residual' prevailing
      bodyFrames := by
    intro pair member
    rcases List.mem_cons.mp member with rfl | old
    · exact bodyScope
    · exact ResidualContextScope.extendAppTargets (protectedScopes pair old)
        (state.stable.frame.contextsBounded old) domain codomain
  have bodyContextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (bodyRawContext.applySubst prevailing) := by
    simpa [bodyRawContext, Context.applySubst, domainFixed, codomainFixed,
      Subst.apply_fn] using contextOld.consFixTargetsAbove floorTargets
  have bodyRawSuffix : ProvenanceContextSuffix provenanceContext
      bodyRawContext := by
    exact (rawSuffix.consActive self
      (Scheme.mono (.fn (.var supply.nextTy)
        (.var (supply.nextTy + 1))))).consActive argument
          (Scheme.mono (.var supply.nextTy))
  have bodyContextSuffix : ProtectedContextsSuffix bodyRawContext bodyFrames :=
    contextSuffix.consFixBody
  have bodyContextCapFree :
      (bodyRawContext.applySubst prevailing).fcv = [] := by
    have appliedEq : bodyRawContext.applySubst prevailing =
        (argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
          rawContext.applySubst prevailing := by
      unfold bodyRawContext
      simp only [Context.applySubst, List.map_cons, Scheme.applyMeta_mono,
        Subst.apply_fn, domainFixed, codomainFixed]
    rw [appliedEq]
    simpa [Context.fcv, Scheme.fcv, Scheme.mono, Ty.fcv] using contextCapFree
  have bodyProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (algorithm, selected) ∈ bodyFrontier := by
    intro algorithm selected member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (provenanceRetains algorithm selected member))
  let outerProtected := GenerativitySurfaceObligations.protectToken
    (.var supply.nextTy) (GenerativitySurfaceObligations.protectToken
      (.var (supply.nextTy + 1)) generativityObligations)
  have below : ∀ obligation ∈ generativityObligations,
      obligation.floor.nextTy ≤ supply.nextTy := by
    intro obligation member
    exact (generativityValid obligation member).1.2
  have outerFrame : GenerativitySurfaceFrameAt outerProtected prevailing := by
    have codomainProtected := generativity.protectToken (raw :=
      .var (supply.nextTy + 1)) (by
        intro obligation member
        rw [codomainFixed]
        exact OldFreeInContextAt.var _ _ _
          (Nat.le_trans (below obligation member) (Nat.le_succ _)))
    exact codomainProtected.protectToken (raw := .var supply.nextTy) (by
      intro obligation member
      rcases List.mem_map.mp member with ⟨old, oldMember, rfl⟩
      simp only [GenerativitySurfaceObligation.protectToken]
      rw [domainFixed]
      exact OldFreeInContextAt.var _ _ _ (below old oldMember))
  have outerContexts : GenerativitySurfaceContextsAt outerProtected prevailing
      (bodyRawContext.applySubst prevailing) := by
    intro obligation member
    rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
    rcases List.mem_map.mp ‹codomainProtected ∈ _› with ⟨old, oldMember, rfl⟩
    have oldCovered := generativityContexts old oldMember
    simpa [GenerativitySurfaceObligation.protectToken, bodyRawContext,
      Context.applySubst, domainFixed, codomainFixed, Subst.apply_fn] using
      oldCovered.consFixTargetsAbove (below old oldMember)
  have outerValid : GenerativitySurfaceValid bodySupply bodyRawContext
      outerProtected :=
    (generativityValid.protectToken.protectToken
      |>.monoSupply (SupplyExtends.bumpTy supply 2)
      |>.consActive self (Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1))))
      |>.consActive argument (Scheme.mono (.var supply.nextTy)))
  let shadow := provenanceControlObligation provenanceFloor provenanceContext
    supply.nextTy
  have shadowFrame : GenerativitySurfaceFrameAt [shadow] prevailing := by
    intro obligation member raw rawMember
    have obligationEq : obligation = shadow := List.mem_singleton.mp member
    subst obligation
    change OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) (prevailing.apply raw)
    change raw ∈ [.var supply.nextTy, .var (supply.nextTy + 1)] at rawMember
    rcases List.mem_cons.mp rawMember with rfl | rawMember
    · simpa [domainFixed] using
        (OldFreeInContextAt.var provenanceFloor
          (provenanceContext.applySubst prevailing) supply.nextTy floorTargets)
    · rcases List.mem_singleton.mp rawMember with rfl
      simpa [codomainFixed] using
        (OldFreeInContextAt.var provenanceFloor
          (provenanceContext.applySubst prevailing) (supply.nextTy + 1)
          (Nat.le_trans floorTargets (Nat.le_succ _)))
  let childObligations := GenerativitySurfaceObligation.currentPaired
      bodySupply bodyRawContext bodyFrontier ::
    GenerativitySurfaceObligation.current bodySupply bodyRawContext ::
      shadow ::
      outerProtected
  have shadowOuterFrame : GenerativitySurfaceFrameAt (shadow :: outerProtected)
      prevailing := by
    intro obligation member raw rawMember
    rcases List.mem_cons.mp member with rfl | member
    · exact shadowFrame shadow List.mem_cons_self raw rawMember
    · exact outerFrame obligation member raw rawMember
  have childFrame : GenerativitySurfaceFrameAt childObligations prevailing :=
    (shadowOuterFrame.registerEmpty bodySupply bodyRawContext).registerPaired
      bodySupply bodyRawContext bodyFrontier
  have childContexts : GenerativitySurfaceContextsAt childObligations prevailing
      (bodyRawContext.applySubst prevailing) :=
    (by
      have shadowOuterContexts : GenerativitySurfaceContextsAt
          (shadow :: outerProtected) prevailing
          (bodyRawContext.applySubst prevailing) := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | member
        · exact bodyContextOld
        · exact outerContexts obligation member
      exact (shadowOuterContexts.registerCurrent bodySupply).registerCurrentPaired
        bodySupply bodyFrontier)
  have childValid : GenerativitySurfaceValid bodySupply bodyRawContext
      childObligations :=
    (by
      have shadowOuterValid : GenerativitySurfaceValid bodySupply bodyRawContext
          (shadow :: outerProtected) := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨⟨Nat.le_trans floorCaps (Nat.le_refl _),
              Nat.le_trans floorTargets (Nat.le_add_right _ _)⟩,
            bodyRawSuffix⟩
        · exact outerValid obligation member
      exact shadowOuterValid.registerCurrent.registerCurrentPaired bodyFrontier)
  have bodyFrontierNormalized : ∀ pair ∈ bodyFrontier,
      prevailing.apply pair.1 = pair.1 := by
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact domainFixed
    rcases List.mem_cons.mp member with rfl | old
    · exact codomainFixed
    · exact frontierNormalized pair old
  have bodyFrontierBounded : ∀ pair ∈ bodyFrontier,
      (prevailing.apply pair.1).BoundedBy bodySupply := by
    intro pair member
    rw [bodyFrontierNormalized pair member]
    exact preparedState.stable.frame.frontierBounded pair member
  have childRetained : GenerativitySurfaceRetainedAt childObligations
      prevailing := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | member
    · constructor
      · intro pair pairMember varId free
        exact Or.inl ((bodyFrontierBounded pair pairMember).caps varId free)
      · intro pair pairMember varId free
        exact Or.inl ((bodyFrontierBounded pair pairMember).targets varId free)
    rcases List.mem_cons.mp member with rfl | member
    · exact RetainedOldOrContextAt.nil bodySupply
        (bodyRawContext.applySubst prevailing) prevailing
    rcases List.mem_cons.mp member with rfl | member
    · exact RetainedOldOrContextAt.nil provenanceFloor
        (provenanceContext.applySubst prevailing) prevailing
    · exact (surfacesRetained.protectToken
          (raw := .var (supply.nextTy + 1)) |>.protectToken
          (raw := .var supply.nextTy)) obligation member
  have childMembers : GenerativitySurfaceMembersAt childObligations prevailing
      bodyFrontier := by
    intro obligation member pair pairMember
    rcases List.mem_cons.mp member with rfl | member
    · rw [bodyFrontierNormalized pair pairMember]
      exact pairMember
    rcases List.mem_cons.mp member with rfl | member
    · simp [GenerativitySurfaceObligation.current] at pairMember
    rcases List.mem_cons.mp member with rfl | member
    · simp [shadow, provenanceControlObligation] at pairMember
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        ((surfacesMembers.protectToken
          (raw := .var (supply.nextTy + 1)) |>.protectToken
          (raw := .var supply.nextTy)) obligation member pair pairMember))
  have bodyAdmissible : AdmissiblePost [] (SSubst.paired residual') := by
    rw [SSubst.paired_extendAppTargets]
    exact DM.AdmissiblePost.extendAppTargets postAdmissible
  exact ⟨
    { residual := residual'
      state := preparedState
      context := ⟨preparedState.stable.frame.contexts List.mem_cons_self⟩
      scope := bodyScope
      protectedScopes := bodyProtectedScopes
      postAdmissible := bodyAdmissible
      prevailingBounded := prevailingBounded.mono (SupplyExtends.bumpTy supply 2)
      prevailingIdempotent := prevailingIdempotent
      pendingCapFree := pendingCapFree
      contextCapFree := bodyContextCapFree
      floorCaps := floorCaps
      floorTargets := Nat.le_trans floorTargets (Nat.le_add_right _ _)
      contextOld := bodyContextOld
      contextProvenanceSuffix := bodyRawSuffix
      provenanceIncluded := bodyRawSuffix.toIncluded prevailing
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := bodyProvenanceRetains
      childObligations := childObligations
      outerMember := by
        intro obligation member
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ member))
      shadowMember := List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)
      childGenerativity := childFrame
      childGenerativityContexts := childContexts
      childGenerativityValid := childValid
      childCurrentObligation := List.mem_cons_of_mem _ List.mem_cons_self
      childCurrentPaired := List.mem_cons_self
      childRetained := childRetained
      childMembers := childMembers
      frontierNormalized := bodyFrontierNormalized
      protectedCovered := bodyContextSuffix.toProtectedFreeCovered prevailing
      contextSuffix := bodyContextSuffix
      domainMember := by simp [domainFixed]
      codomainMember := by simp [codomainFixed] }⟩

/-- Oracle-free paired direct-self constructor.  The only callback is the
recursive body at the prepared two-binder state. -/
theorem Typing.w_paired_normalized_fix
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {self argument : String}
    {body : Expr} {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {residual : SSubst}
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (signatureClosed : signature.SchemesClosed)
    (state : WRetiredStableFrameAt signature supply (SSubst.paired residual)
      prevailing frames frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes residual prevailing frames)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (rawSuffix : ProvenanceContextSuffix provenanceContext rawContext)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing) provenanceFrames prevailing)
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing)
    (surfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations prevailing)
    (surfacesMembers : GenerativitySurfaceMembersAt generativityObligations
      prevailing frontier)
    (frontierNormalized : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1)
    (generativityContexts : GenerativitySurfaceContextsAt
      generativityObligations prevailing (rawContext.applySubst prevailing))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (currentPaired : GenerativitySurfaceObligation.currentPaired supply
      rawContext frontier ∈ generativityObligations)
    (_coverage : ProtectedFreeCovered (rawContext.applySubst prevailing)
      frames prevailing)
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    (postAdmissible : AdmissiblePost [] (SSubst.paired residual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending)
    (bodyContinuation : ∀ prepared : WFixBodyPrepared signature supply
      prevailing rawContext self argument selectedContext domain codomain
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending,
      WPairedNormalizedCompleteResult signature
        { supply with nextTy := supply.nextTy + 2 } prevailing
        ((argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
        body
        ((argument, SScheme.mono domain) ::
          (self, SScheme.mono (.fn domain codomain)) :: selectedContext)
        codomain provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier
        (WFixBodyPrepared.childObligations prepared)
        (((argument, Scheme.mono (.var supply.nextTy)) ::
            (self, Scheme.mono
              (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
          (argument, SScheme.mono domain) ::
            (self, SScheme.mono (.fn domain codomain)) :: selectedContext) ::
          frames)
        ((.var supply.nextTy, domain) ::
          (.var (supply.nextTy + 1), codomain) :: frontier) pending) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.fix self argument body) selectedContext (.fn domain codomain)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  obtain ⟨prepared⟩ := w_preparePairedFixBody state active scope
    protectedScopes floorCaps floorTargets contextOld rawSuffix
    provenanceSuffix provenanceCovered retainedOuter provenanceRetains
    generativity surfacesRetained surfacesMembers frontierNormalized
    generativityContexts generativityValid contextSuffix contextCapFree
    postAdmissible prevailingBounded prevailingIdempotent pendingCapFree
  obtain ⟨bodyResult⟩ := bodyContinuation prepared
  let result := bodyResult.normalized.complete
  have codomainRetained :
      (result.prevailing'.apply (.var (supply.nextTy + 1)), codomain) ∈
        result.frontier := by
    have retained := result.frontierRetains _ _
      (WFixBodyPrepared.codomainMember prepared)
    simpa only [result.prevailing_eq, Subst.seq_apply] using retained
  have bodyState := result.retiredState.dropContextHead
  rw [bodyResult.normalized.post_eq] at bodyState
  have codomainEquation : (SSubst.paired bodyResult.normalized.residual).apply
      (result.prevailing'.apply (.var (supply.nextTy + 1))) = codomain.emb := by
    rw [← bodyResult.normalized.post_eq]
    exact result.frame.types codomainRetained
  obtain ⟨algorithmCodomain, codomainView⟩ :=
    NormalizedDMTargetView.ofPairedEquation
      codomainEquation
  obtain ⟨delta, solverCut, factor, alignedRaw, moved⟩ :=
    w_alignNormalizedRetired bodyState signatureClosed
      bodyResult.normalized.target.normalized_eq codomainView.normalized_eq
      bodyResult.normalized.target.residual_eq codomainView.residual_eq
      result.targetMember codomainRetained result.pendingCapFree
  let finalPrevailing := Subst.seq delta result.prevailing'
  let finalFrontier := result.frontier.map
    (fun pair => (delta.apply pair.1, pair.2))
  let aligned : DemandAlignTypesWithLedger [] result.prevailing'
      result.rawTarget (.var (supply.nextTy + 1)) finalPrevailing :=
    DemandAlignTypesWithLedger.ordinary
      (alignPairClass_ordinary_of_realized_emb
        (by rw [bodyResult.normalized.target.normalized_eq,
          SSubst.paired_apply_emb, bodyResult.normalized.target.residual_eq])
        codomainEquation) solverCut.exact
  let derived : DemandSynth signature supply prevailing rawContext
      (.fix self argument body)
      (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
      result.successor finalPrevailing :=
    DemandSynth.fix distinct direct nonMatcher result.derived aligned.erase
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.fix distinct direct nonMatcher result.origin aligned
  let fixPlan : WSynthAuditPlan signature (origin := origin) :=
    WSynthAuditPlan.fix (distinct := distinct) (direct := direct)
      (nonMatcher := nonMatcher) (aligned := aligned) result.auditPlan
  let planned : PlannedSynth signature supply prevailing rawContext
      (.fix self argument body)
      (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
      result.successor finalPrevailing := ⟨derived, origin, fixPlan⟩
  have finalPendingCapFree : PendingLetsCapFree finalPrevailing result.pending :=
    result.pendingCapFree.applyLetStableExactPairedCut solverCut
  have outerContextCapFreeBefore :
      (rawContext.applySubst result.prevailing').fcv = [] := by
    have full := bodyResult.contextCapFree
    have tailSubset : ∀ varId,
        varId ∈ (rawContext.applySubst result.prevailing').fcv →
        varId ∈ (Context.applySubst result.prevailing'
          ((argument, Scheme.mono (.var supply.nextTy)) ::
            (self, Scheme.mono
              (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
            rawContext)).fcv := by
      intro varId member
      simp only [Context.applySubst, List.map_cons, Context.fcv,
        List.flatMap_cons, List.mem_append]
      exact Or.inr (Or.inr member)
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro varId member
    have impossible := tailSubset varId member
    rw [full] at impossible
    exact List.not_mem_nil impossible
  have finalContextCapFree :
      (rawContext.applySubst finalPrevailing).fcv = [] := by
    change (rawContext.applySubst (Subst.seq delta result.prevailing')).fcv = []
    exact ContextCapFree.applyLetStableExactPairedCut
      outerContextCapFreeBefore solverCut
  have finalBounded : finalPrevailing.BoundedBy result.successor := by
    exact (solverCut.exact.exact.boundedBy
      (result.frame.frontierBounded _ result.targetMember)
      (result.frame.frontierBounded _ codomainRetained)).seq
        result.prevailingBounded
  have finalIdempotent : finalPrevailing.Idempotent :=
    DemandTypingIdempotence.DemandAlignTypes.idempotent alignedRaw
      result.prevailingIdempotent
  have domainRetained :
      (result.prevailing'.apply (.var supply.nextTy), domain) ∈ result.frontier := by
    have retained := result.frontierRetains _ _
      (WFixBodyPrepared.domainMember prepared)
    simpa only [result.prevailing_eq, Subst.seq_apply] using retained
  have finalDomainMember :
      (finalPrevailing.apply (.var supply.nextTy), domain) ∈ finalFrontier := by
    apply List.mem_map.mpr
    exact ⟨_, domainRetained, by simp only [finalPrevailing, Subst.seq_apply]⟩
  have finalCodomainMember :
      (finalPrevailing.apply (.var (supply.nextTy + 1)), codomain) ∈
        finalFrontier := by
    apply List.mem_map.mpr
    exact ⟨_, codomainRetained, by simp only [finalPrevailing, Subst.seq_apply]⟩
  obtain ⟨algorithmDomain, domainView⟩ :=
    NormalizedDMTargetView.ofPairedEquation
      (moved.stable.frame.types finalDomainMember)
  obtain ⟨algorithmCodomainFinal, codomainViewFinal⟩ :=
    NormalizedDMTargetView.ofPairedEquation
      (moved.stable.frame.types finalCodomainMember)
  have finalTarget : NormalizedDMTargetView bodyResult.normalized.residual
      (.fn algorithmDomain algorithmCodomainFinal) (.fn domain codomain)
      (finalPrevailing.apply
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) := by
    simpa only [Subst.apply_fn] using
      NormalizedDMTargetView.fn domainView codomainViewFinal
  let outputRaw := finalPrevailing.apply
    (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)) )
  let outputFrontier : List (Ty × STy) :=
    (outputRaw, .fn domain codomain) :: finalFrontier
  have outputState : WRetiredStableFrameAt signature result.successor
      (SSubst.paired bodyResult.normalized.residual) finalPrevailing frames
      outputFrontier result.pending := by
    simpa only [outputRaw, outputFrontier, Subst.apply_fn] using
      moved.protectFnOfMembers finalDomainMember finalCodomainMember
  have outerScope0 : ResidualContextScope bodyResult.normalized.residual
      (rawContext.applySubst result.prevailing') selectedContext :=
    bodyResult.normalized.protectedScopes
      (rawContext, selectedContext) (List.mem_cons_of_mem _ active)
  have finalScope : ResidualContextScope bodyResult.normalized.residual
      (rawContext.applySubst finalPrevailing) selectedContext := by
    rw [Context.applySubst_seq]
    exact ResidualContextScope.applyAbsorbed outerScope0 factor
  have finalScopes : ProtectedResidualScopes bodyResult.normalized.residual
      finalPrevailing frames := by
    intro pair member
    rw [Context.applySubst_seq]
    exact ResidualContextScope.applyAbsorbed
      (bodyResult.normalized.protectedScopes pair
        (List.mem_cons_of_mem _ member)) factor
  have finalContext : ErasedDMContextView bodyResult.normalized.residual
      selectedContext (rawContext.applySubst finalPrevailing) :=
    ⟨moved.stable.frame.contexts active⟩
  have bodyOld := bodyResult.contextOld
  have leftOuterOld := bodyResult.targetOld
  have rightOuterOld := bodyResult.normalized.generativity
    (provenanceControlObligation provenanceFloor provenanceContext supply.nextTy)
    (WFixBodyPrepared.shadowMember prepared)
    (.var (supply.nextTy + 1)) (by
      change Ty.var (supply.nextTy + 1) ∈
        [Ty.var supply.nextTy, Ty.var (supply.nextTy + 1)]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
  have activeProtected : ProtectedOldFreeAt provenanceFloor
      (Context.applySubst result.prevailing' ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)) [] :=
    ProtectedOldFreeAt.nil _ _
  obtain ⟨finalContextOldFull, finalProtectedOld⟩ :=
    bodyOld.applyOriginSafeExactPairedMGU_and_protected activeProtected
      leftOuterOld rightOuterOld solverCut.exact solverCut.leftCapFree
      solverCut.rightCapFree
  have finalIncluded := rawSuffix.toIncluded finalPrevailing
  have finalContextOld := finalContextOldFull.dropActiveHead.dropActiveHead
  have finalRetained := bodyResult.retainedOuter
    |>.applyOriginSafeExactPairedMGU_of_endpointsOld
    leftOuterOld rightOuterOld solverCut.exact solverCut.leftCapFree
    solverCut.rightCapFree
  have finalProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        ((Subst.seq delta result.suffix).apply algorithm, selected) ∈
          finalFrontier := by
    intro algorithm selected member
    apply List.mem_map.mpr
    exact ⟨_, result.frontierRetains _ _
      (WFixBodyPrepared.provenanceRetains prepared
        algorithm selected member), by
        simp [Subst.seq_apply]⟩
  let outerProtected := GenerativitySurfaceObligations.protectToken
    (.var supply.nextTy) (GenerativitySurfaceObligations.protectToken
      (.var (supply.nextTy + 1)) generativityObligations)
  have outerMember : ∀ {obligation}, obligation ∈ outerProtected →
      obligation ∈ WFixBodyPrepared.childObligations
        (self := self) (argument := argument) prepared := by
    intro obligation member
    exact WFixBodyPrepared.outerMember (self := self) (argument := argument)
      prepared obligation member
  have outerFrameBefore : GenerativitySurfaceFrameAt outerProtected
      result.prevailing' :=
    bodyResult.normalized.generativity.of_obligations_subset (by
      intro obligation member
      exact outerMember member)
  have outerLeftOld : ∀ obligation ∈ outerProtected,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    exact bodyResult.normalized.targetGenerative obligation
      (outerMember member)
  have outerRightOld : ∀ obligation ∈ outerProtected,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply (.var (supply.nextTy + 1))) := by
    intro obligation member
    exact bodyResult.normalized.generativity obligation
      (outerMember member) _ (by
        rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
        rcases List.mem_map.mp ‹codomainProtected ∈ _› with ⟨old, _, rfl⟩
        simp [GenerativitySurfaceObligation.protectToken])
  have outerFrameAfter : GenerativitySurfaceFrameAt outerProtected
      finalPrevailing := by
    simpa [finalPrevailing] using outerFrameBefore.applyOriginSafeExactPairedMGU
      outerLeftOld outerRightOld solverCut.exact solverCut.leftCapFree
      solverCut.rightCapFree
  have finalGenerativity := outerFrameAfter.unprotectToken.unprotectToken
  have outerContextsBefore : GenerativitySurfaceContextsAt outerProtected
      result.prevailing' (rawContext.applySubst result.prevailing') := by
    intro obligation member
    have covered := bodyResult.normalized.generativityContexts obligation
      (outerMember member)
    exact covered.dropActiveHead.dropActiveHead
  have finalGenerativityContexts : GenerativitySurfaceContextsAt
      generativityObligations finalPrevailing
      (rawContext.applySubst finalPrevailing) := by
    have movedContexts := outerContextsBefore.applyOriginSafeExactPairedMGU
      outerLeftOld outerRightOld solverCut.exact solverCut.leftCapFree
      solverCut.rightCapFree
    simpa [finalPrevailing, Context.applySubst_seq] using
      movedContexts.unprotectToken.unprotectToken
  have finalTargetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst finalPrevailing)
        (finalPrevailing.apply
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) := by
    intro obligation member
    exact OldFreeInContextAt.fn
      (outerFrameAfter _ (List.mem_map.mpr
        ⟨obligation.protectToken (.var (supply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩)
        _ (by simp [GenerativitySurfaceObligation.protectToken]))
      (outerFrameAfter _ (List.mem_map.mpr
        ⟨obligation.protectToken (.var (supply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩)
        _ (by simp [GenerativitySurfaceObligation.protectToken]))
  have finalPairedState : GenerativityPairedStateAt generativityObligations
      finalPrevailing finalFrontier := by
    have before : GenerativityPairedStateAt outerProtected result.prevailing'
        result.frontier :=
      ⟨bodyResult.surfacesRetained.of_obligations_subset (by
          intro obligation member
          exact outerMember member),
        bodyResult.surfacesMembers.of_obligations_subset (by
          intro obligation member
          exact outerMember member)⟩
    have after := before.applyOriginSafeExactPairedMGU outerLeftOld
      outerRightOld solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
    simpa [finalPrevailing, finalFrontier] using
      ⟨after.retained.unprotectToken.unprotectToken,
        after.members.unprotectToken.unprotectToken⟩
  have outputPairedState : GenerativityPairedStateAt generativityObligations
      finalPrevailing outputFrontier :=
    { retained := finalPairedState.retained
      members := by
        intro obligation obligationMember pair pairMember
        exact List.mem_cons_of_mem _
          (finalPairedState.members obligation obligationMember pair pairMember) }
  have finalFrontierNormalized : ∀ pair ∈ finalFrontier,
      finalPrevailing.apply pair.1 = pair.1 := by
    intro pair member
    rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    have sourceFixed := bodyResult.frontierNormalized source sourceMember
    have finalSource : finalPrevailing.apply source.1 = delta.apply source.1 := by
      change (Subst.seq delta result.prevailing').apply source.1 = _
      rw [Subst.seq_apply, sourceFixed]
    calc
      finalPrevailing.apply (delta.apply source.1) =
          finalPrevailing.apply (finalPrevailing.apply source.1) := by
        rw [finalSource]
      _ = finalPrevailing.apply source.1 := finalIdempotent source.1
      _ = delta.apply source.1 := finalSource
  have outputFrontierNormalized : ∀ pair ∈ outputFrontier,
      finalPrevailing.apply pair.1 = pair.1 := by
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact finalIdempotent _
    · exact finalFrontierNormalized pair tail
  have finalRetains : ∀ cut, cut ∈ pending → cut ∈ result.pending :=
    fun cut member => result.retains cut member
  have finalAuditCuts : ∀ cut, cut ∈ planned.plan.cuts →
      cut ∈ result.pending := by
    intro cut member
    exact result.auditCuts cut (by
      change cut ∈ result.auditPlan.cuts
      exact member)
  let suffix := Subst.seq delta result.suffix
  have finalPrevailingEq : finalPrevailing = Subst.seq suffix prevailing := by
    simp only [finalPrevailing, result.prevailing_eq]
    simp [suffix, PhasedPost.seq_assoc]
  have finalFrontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ frontier →
        (suffix.apply algorithm, selected) ∈ finalFrontier := by
    intro algorithm selected member
    apply List.mem_map.mpr
    exact ⟨_, result.frontierRetains _ _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)), by
      simp only [suffix, Subst.seq_apply]⟩
  have outputFrontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ frontier →
        (suffix.apply algorithm, selected) ∈ outputFrontier := by
    intro algorithm selected member
    exact List.mem_cons_of_mem _ (finalFrontierRetains algorithm selected member)
  have outputProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ outputFrontier := by
    intro algorithm selected member
    exact List.mem_cons_of_mem _
      (finalProvenanceRetains algorithm selected member)
  have outputTargetOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst finalPrevailing) outputRaw := by
    let shadow := provenanceControlObligation provenanceFloor provenanceContext
      supply.nextTy
    have before : GenerativitySurfaceFrameAt [shadow] result.prevailing' := by
      intro obligation member raw rawMember
      have eq : obligation = shadow := List.mem_singleton.mp member
      subst obligation
      exact bodyResult.normalized.generativity _
        (WFixBodyPrepared.shadowMember prepared) raw rawMember
    have after := before.applyOriginSafeExactPairedMGU
      (fun obligation member => by
        have eq : obligation = shadow := List.mem_singleton.mp member
        subst obligation
        exact leftOuterOld)
      (fun obligation member => by
        have eq : obligation = shadow := List.mem_singleton.mp member
        subst obligation
        exact rightOuterOld) solverCut.exact solverCut.leftCapFree
      solverCut.rightCapFree
    have domainOld := after shadow List.mem_cons_self (.var supply.nextTy) (by
      change Ty.var supply.nextTy ∈
        [Ty.var supply.nextTy, Ty.var (supply.nextTy + 1)]
      exact List.mem_cons_self)
    have codomainOld := after shadow List.mem_cons_self _ (by
      change Ty.var (supply.nextTy + 1) ∈
        [Ty.var supply.nextTy, Ty.var (supply.nextTy + 1)]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    simpa [shadow, provenanceControlObligation, finalPrevailing,
      Context.applySubst_seq, outputRaw, Subst.apply_fn] using
      OldFreeInContextAt.fn domainOld codomainOld
  have outputContextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst finalPrevailing)
      (rawContext.applySubst finalPrevailing) := by
    dsimp only [finalPrevailing]
    rw [Context.applySubst_seq, Context.applySubst_seq]
    exact finalContextOld
  have finalAdmissible : AdmissiblePost []
      (SSubst.paired bodyResult.normalized.residual) := by
    rw [← bodyResult.normalized.post_eq]
    exact result.postAdmissible
  obtain ⟨completed⟩ := w_normalized_complete_core
    (algorithmContext := bodyResult.normalized.algorithmContext)
    planned outputState rfl finalContext finalScope finalScopes suffix finalTarget
    InferenceBase.FreshSupply.empty [] [] (by simp [InferenceBase.FreshSupply.empty])
    (by simp [InferenceBase.FreshSupply.empty])
    (by constructor <;> intro varId free below <;>
      simp [InferenceBase.FreshSupply.empty] at below)
    ⟨rawContext, List.append_nil rawContext⟩
    (by constructor <;> intro varId free <;>
      simp [Context.applySubst, Context.fcv, Context.ftv] at free)
    (by intro pair member; constructor <;> intro varId free below <;>
      simp [InferenceBase.FreshSupply.empty] at below)
    (by simp [ProtectedContextsSuffix])
    (by constructor <;> intro pair member <;> simp at member)
    (RetainedOldOrContextAt.nil InferenceBase.FreshSupply.empty [] suffix)
    (by intro algorithm selected member; cases member)
    finalGenerativity finalGenerativityContexts
    generativityValid currentObligation finalTargetGenerative
    (finalTargetGenerative _ currentObligation)
    (contextSuffix.toProtectedFreeCovered finalPrevailing) contextSuffix
    finalPendingCapFree finalAdmissible finalBounded finalIdempotent
    finalRetains finalAuditCuts finalPrevailingEq
    outputFrontierRetains
    (by simp [outputFrontier, outputRaw])
  exact ⟨
    { normalized := completed.result
      contextCapFree := by
        rw [completed.prevailing_eq]
        exact finalContextCapFree
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := by
        rw [completed.prevailing_eq]
        exact outputContextOld
      contextProvenanceSuffix := rawSuffix
      provenanceIncluded := by
        rw [completed.prevailing_eq]
        exact finalIncluded
      targetOld := by
        rw [completed.prevailing_eq, completed.rawTarget_eq]
        exact outputTargetOld
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceSuffix.toProtectedFreeCovered _
      retainedOuter := by
        rw [completed.prevailing_eq, completed.suffix_eq]
        simpa [suffix, finalPrevailing, Context.applySubst_seq] using finalRetained
      provenanceRetains := by
        rw [completed.suffix_eq, completed.frontier_eq]
        exact outputProvenanceRetains
      inputFrontierNormalized := frontierNormalized
      surfacesRetained := by
        rw [completed.prevailing_eq]
        exact outputPairedState.retained
      surfacesMembers := by
        rw [completed.prevailing_eq, completed.frontier_eq]
        exact outputPairedState.members
      frontierNormalized := by
        rw [completed.prevailing_eq, completed.frontier_eq]
        exact outputFrontierNormalized
      currentPaired := currentPaired }⟩
end DM
end TypePM
