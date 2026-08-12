import TypePM.DamasMilnerWNormalizedStructuralComplete

/-!
# Erasure-stable normalized lambda completeness

Lambda preparation does not require syntactically reifying the outer core
context as an embedded simple context.  This module is the erased-context
counterpart of the structural lambda package.
-/

namespace TypePM
namespace DM

def lambdaShadowObligation (supply : InferenceBase.FreshSupply)
    (owner : Context) (frontier : List (Ty × STy)) (domainRaw : Ty) :
    GenerativitySurfaceObligation :=
  { floor := supply
    owner := owner
    continuation := frontier
    protectedOld := [domainRaw] }

structure WErasedNormalizedLamBody
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (name : String) (body : Expr)
    (selectedContext : SCtx) (domain codomain : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Type where
  result : WNormalizedCompleteWitness signature
    { supply with nextTy := supply.nextTy + 1 } prevailing
    ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) body
    ((name, SScheme.mono domain) :: selectedContext) codomain
    InferenceBase.FreshSupply.empty [] [] []
    (GenerativitySurfaceObligation.currentPaired
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
      ((.var supply.nextTy, domain) :: frontier) ::
    GenerativitySurfaceObligation.current
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
    lambdaShadowObligation provenanceFloor provenanceContext
      provenanceFrontier (.var supply.nextTy) ::
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations)
    ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
        (name, SScheme.mono domain) :: selectedContext)) :: frames)
    ((.var supply.nextTy, domain) :: frontier) pending
  algorithmDomain : STy
  outer : ErasedDMContextView result.residual selectedContext
    (rawContext.applySubst result.complete.prevailing')
  domainView : NormalizedDMTargetView result.residual algorithmDomain domain
    (result.complete.prevailing'.apply (.var supply.nextTy))
  outerScope : ResidualContextScope result.residual
    (rawContext.applySubst result.complete.prevailing') selectedContext
  floorCapsOuter : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargetsOuter : provenanceFloor.nextTy ≤ supply.nextTy
  contextOldOuter : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst result.complete.prevailing')
    (rawContext.applySubst result.complete.prevailing')
  contextProvenanceSuffixOuter : ProvenanceContextSuffix provenanceContext
    rawContext
  provenanceIncludedOuter : ProvenanceContextIncluded
    (provenanceContext.applySubst result.complete.prevailing')
    (rawContext.applySubst result.complete.prevailing')
  protectedCoveredOuter : ProtectedFreeCovered
    (rawContext.applySubst result.complete.prevailing') frames
    result.complete.prevailing'
  contextSuffixOuter : ProtectedContextsSuffix rawContext frames
  contextCapFreeOuter :
    (rawContext.applySubst result.complete.prevailing').fcv = []
  provenanceSuffixOuter : ProtectedContextsSuffix provenanceContext
    provenanceFrames
  provenanceFrontierNormalizedOuter : ∀ pair ∈ provenanceFrontier,
    prevailing.apply pair.1 = pair.1
  generativityValidOuter : GenerativitySurfaceValid supply rawContext
    generativityObligations
  currentObligationOuter : GenerativitySurfaceObligation.current supply
    rawContext ∈
    generativityObligations
  localOldFreeOuter : OldFreeInContextAt supply
    (rawContext.applySubst result.complete.prevailing')
    (result.complete.prevailing'.apply
      (.fn (.var supply.nextTy) result.complete.rawTarget))

/-- Paired continuation certificate for an erased lambda body.  The raw
normalized package carries the semantic outer projections; these four fields
retain the executable continuation surface through the body traversal. -/
structure WPairedErasedNormalizedLamBody
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (name : String) (body : Expr)
    (selectedContext : SCtx) (domain codomain : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Type where
  body : WErasedNormalizedLamBody signature supply prevailing rawContext name
    body selectedContext domain codomain provenanceFloor provenanceContext
    provenanceFrames provenanceFrontier generativityObligations frames
    frontier pending
  surfacesRetained : GenerativitySurfaceRetainedAt
    (GenerativitySurfaceObligation.currentPaired
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
      ((.var supply.nextTy, domain) :: frontier) ::
    GenerativitySurfaceObligation.current
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
    lambdaShadowObligation provenanceFloor provenanceContext
      provenanceFrontier (.var supply.nextTy) ::
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations)
    body.result.complete.prevailing'
  surfacesMembers : GenerativitySurfaceMembersAt
    (GenerativitySurfaceObligation.currentPaired
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
      ((.var supply.nextTy, domain) :: frontier) ::
    GenerativitySurfaceObligation.current
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
    lambdaShadowObligation provenanceFloor provenanceContext
      provenanceFrontier (.var supply.nextTy) ::
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations)
    body.result.complete.prevailing' body.result.complete.frontier
  frontierNormalized : ∀ pair ∈ body.result.complete.frontier,
    body.result.complete.prevailing'.apply pair.1 = pair.1
  currentPairedOuter : GenerativitySurfaceObligation.currentPaired supply
    rawContext frontier ∈ generativityObligations
  inputFrontierNormalizedOuter : ∀ pair ∈ frontier,
    prevailing.apply pair.1 = pair.1

theorem Typing.w_paired_erased_normalized_lam_of_body
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {name : String} {body : Expr}
    {domain codomain : STy} {pending : List PendingLetCut}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (_prepared : WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 1 } post prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      ((.var supply.nextTy, domain) :: frontier) pending)
    (domainMember : (prevailing.apply (.var supply.nextTy), domain) ∈
      ((.var supply.nextTy, domain) :: frontier))
    (bodyResult : WErasedNormalizedLamBody signature supply prevailing
      rawContext name body selectedContext domain codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending)
    (bodySurfacesRetained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligation.currentPaired
        { supply with nextTy := supply.nextTy + 1 }
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
        ((.var supply.nextTy, domain) :: frontier) ::
      GenerativitySurfaceObligation.current
        { supply with nextTy := supply.nextTy + 1 }
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
      lambdaShadowObligation provenanceFloor provenanceContext
        provenanceFrontier (.var supply.nextTy) ::
        GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
          generativityObligations)
      bodyResult.result.complete.prevailing')
    (bodySurfacesMembers : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligation.currentPaired
        { supply with nextTy := supply.nextTy + 1 }
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
        ((.var supply.nextTy, domain) :: frontier) ::
      GenerativitySurfaceObligation.current
        { supply with nextTy := supply.nextTy + 1 }
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
      lambdaShadowObligation provenanceFloor provenanceContext
        provenanceFrontier (.var supply.nextTy) ::
        GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
          generativityObligations)
      bodyResult.result.complete.prevailing'
      bodyResult.result.complete.frontier)
    (bodyFrontierNormalized : ∀ pair ∈ bodyResult.result.complete.frontier,
      bodyResult.result.complete.prevailing'.apply pair.1 = pair.1)
    (currentPairedOuter : GenerativitySurfaceObligation.currentPaired supply
      rawContext frontier ∈ generativityObligations)
    (inputFrontierNormalizedOuter : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.lam name body) selectedContext (.fn domain codomain) provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  let result := bodyResult.result.complete
  have bodyEquation : result.post.apply
      (result.prevailing'.apply result.rawTarget) = codomain.emb :=
    result.frame.types result.targetMember
  have bodyContextRelated : WContextRel result.post
      (Context.applySubst result.prevailing'
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext))
      ((name, SScheme.mono domain) :: selectedContext) :=
    result.frame.contexts List.mem_cons_self
  have domainEquation : result.post.apply
      (result.prevailing'.apply (.var supply.nextTy)) = domain.emb :=
    WContextRel.consMono_head_equation bodyContextRelated
  let derived : DemandSynth signature supply prevailing rawContext
      (.lam name body) (.fn (.var supply.nextTy) result.rawTarget)
      result.successor result.prevailing' := DemandSynth.lam result.derived
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.lam result.origin
  have dropped := result.frame.dropContextHead
  have functionEquation : result.post.apply
      (result.prevailing'.apply (.fn (.var supply.nextTy) result.rawTarget)) =
      (STy.fn domain codomain).emb := by
    simp only [Subst.apply_fn, STy.emb, domainEquation, bodyEquation]
  have functionBounded :
      (result.prevailing'.apply
        (.fn (.var supply.nextTy) result.rawTarget)).BoundedBy
          result.successor := by
    apply Ty.BoundedBy.fnOf
    · apply result.prevailingBounded.apply
      apply Ty.BoundedBy.varOf
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self supply.nextTy)
        result.derived.supplyExtends.2
    · exact result.frame.frontierBounded _ result.targetMember
  have finalDomainMember :
      (result.prevailing'.apply (.var supply.nextTy), domain) ∈
        result.frontier := by
    have retained := result.frontierRetains _ _ domainMember
    rw [result.prevailing_eq, Subst.seq_apply]
    exact retained
  have domainOwnerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (result.prevailing'.apply (.var supply.nextTy)) := by
    exact bodyResult.result.generativity
      (lambdaShadowObligation provenanceFloor provenanceContext
        provenanceFrontier (.var supply.nextTy))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _
      (by simp [lambdaShadowObligation])
  have bodyOwnerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (result.prevailing'.apply result.rawTarget) :=
    bodyResult.result.targetGenerative
      (lambdaShadowObligation provenanceFloor provenanceContext
        provenanceFrontier (.var supply.nextTy))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have functionOwnerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (result.prevailing'.apply (.fn (.var supply.nextTy) result.rawTarget)) := by
    rw [Subst.apply_fn]
    exact OldFreeInContextAt.fn domainOwnerOld bodyOwnerOld
  have functionFresh : ∀ cut ∈ result.pending,
      cut.AvoidsTy signature result.prevailing'
        (result.prevailing'.apply
          (.fn (.var supply.nextTy) result.rawTarget)) := by
    intro cut cutMember
    simp only [Subst.apply_fn]
    apply PendingLetCut.AvoidsTy.fn
    · exact result.retired cut cutMember _ finalDomainMember
    · exact result.retired cut cutMember _ result.targetMember
  have finalFrame : WProtectedFrameAt result.successor result.post
      result.prevailing' frames
      ((result.prevailing'.apply
          (.fn (.var supply.nextTy) result.rawTarget), .fn domain codomain) ::
        result.frontier) := by
    refine
      { contexts := dropped.contexts
        types := WTypeFrame.cons functionEquation dropped.types
        contextsBounded := dropped.contextsBounded
        frontierBounded := ?_ }
    intro pair member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact functionBounded
    · exact dropped.frontierBounded pair oldMember
  let complete : WCompleteWitness signature supply prevailing rawContext
      (.lam name body) (.fn domain codomain) frames frontier pending :=
    { successor := result.successor
      prevailing' := result.prevailing'
      rawTarget := .fn (.var supply.nextTy) result.rawTarget
      post := result.post
      frontier :=
        (result.prevailing'.apply
          (.fn (.var supply.nextTy) result.rawTarget), .fn domain codomain) ::
          result.frontier
      derived := derived
      origin := origin
      auditPlan := WSynthAuditPlan.lam result.auditPlan
      pending := result.pending
      stability := result.stability
      retains := result.retains
      auditCuts := result.auditCuts
      postAdmissible := result.postAdmissible
      prevailingBounded := result.prevailingBounded
      prevailingIdempotent := result.prevailingIdempotent
      frame := finalFrame
      retired := RetiredFrontierFresh.cons functionFresh result.retired
      contextsRetired := by
        intro cut cutMember pair pairMember
        exact result.contextsRetired cut cutMember pair
          (List.mem_cons_of_mem _ pairMember)
      pendingBelow := result.pendingBelow
      pendingCapFree := result.pendingCapFree
      suffix := result.suffix
      prevailing_eq := result.prevailing_eq
      frontierRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (result.frontierRetains algorithm selected
            (List.mem_cons_of_mem _ member))
      targetMember := List.mem_cons_self }
  have functionTarget : NormalizedDMTargetView bodyResult.result.residual
      (.fn bodyResult.algorithmDomain bodyResult.result.algorithmTarget)
      (.fn domain codomain)
      (result.prevailing'.apply
        (.fn (.var supply.nextTy) result.rawTarget)) := by
    rw [Subst.apply_fn]
    exact NormalizedDMTargetView.fn bodyResult.domainView bodyResult.result.target
  have functionGenerativity : GenerativitySurfaceFrameAt
      generativityObligations result.prevailing' := by
    apply GenerativitySurfaceFrameAt.unprotectToken
    intro obligation obligationMember raw rawMember
    exact bodyResult.result.generativity obligation
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ obligationMember))) raw
      rawMember
  have functionGenerativityContexts : GenerativitySurfaceContextsAt
      generativityObligations result.prevailing'
      (rawContext.applySubst result.prevailing') := by
    intro obligation obligationMember
    let protectedObligation := obligation.protectToken (.var supply.nextTy)
    have protectedMember : protectedObligation ∈
        GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
          generativityObligations :=
      List.mem_map.mpr ⟨obligation, obligationMember, rfl⟩
    have covered := bodyResult.result.generativityContexts protectedObligation
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ protectedMember)))
    have coveredCons : OldContextCoveredAt obligation.1
        (obligation.2.applySubst result.prevailing')
        ((name, (Scheme.mono (.var supply.nextTy)).applyMeta
          result.prevailing') :: rawContext.applySubst result.prevailing') := by
      simpa [protectedObligation,
        GenerativitySurfaceObligation.protectToken,
        Context.applySubst, List.map_cons] using covered
    exact coveredCons.dropActiveHead
  let normalizedWitness : WNormalizedCompleteWitness signature supply
      prevailing rawContext (.lam name body) selectedContext
      (.fn domain codomain) InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames frontier pending :=
    { complete := complete
      algorithmContext := []
      algorithmTarget :=
        .fn bodyResult.algorithmDomain bodyResult.result.algorithmTarget
      residual := bodyResult.result.residual
      post_eq := bodyResult.result.post_eq
      context := bodyResult.outer
      scope := bodyResult.outerScope
      protectedScopes := fun pair member =>
        bodyResult.result.protectedScopes pair
          (List.mem_cons_of_mem _ member)
      target := functionTarget
      floorCaps := by simp [InferenceBase.FreshSupply.empty]
      floorTargets := by simp [InferenceBase.FreshSupply.empty]
      contextOld := by
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      contextProvenanceSuffix := ⟨rawContext, List.append_nil rawContext⟩
      provenanceIncluded := by
        constructor <;> intro varId free <;>
          simp [Context.applySubst, Context.fcv, Context.ftv] at free
      protectedOld := by
        intro pair member
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      provenanceSuffix := by simp [ProtectedContextsSuffix]
      provenanceCovered := by
        constructor <;> intro pair member <;> simp at member
      retainedOuter := RetainedOldOrContextAt.nil
        InferenceBase.FreshSupply.empty [] complete.suffix
      provenanceRetains := by intro algorithm selected member; cases member
      generativity := functionGenerativity
      generativityContexts := functionGenerativityContexts
      generativityValid := bodyResult.generativityValidOuter
      currentObligation := bodyResult.currentObligationOuter
      targetGenerative := by
        intro obligation obligationMember
        let protectedObligation := obligation.protectToken (.var supply.nextTy)
        have protectedMember : protectedObligation ∈
            GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
              generativityObligations :=
          List.mem_map.mpr ⟨obligation, obligationMember, rfl⟩
        rw [Subst.apply_fn]
        exact OldFreeInContextAt.fn
          (bodyResult.result.generativity protectedObligation
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ protectedMember))) _
            List.mem_cons_self)
          (bodyResult.result.targetGenerative protectedObligation
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ protectedMember))))
      localOldFree := bodyResult.localOldFreeOuter
      protectedCovered := bodyResult.protectedCoveredOuter
      contextSuffix := bodyResult.contextSuffixOuter
      pendingCapFree := result.pendingCapFree }
  have protectedSurfacesRetained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations) result.prevailing' :=
    bodySurfacesRetained.of_obligations_subset (by
      intro obligation member
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member)))
  have outerSurfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations result.prevailing' :=
    protectedSurfacesRetained.unprotectToken
  have protectedSurfacesMembers : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations) result.prevailing' result.frontier :=
    bodySurfacesMembers.of_obligations_subset (by
      intro obligation member
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member)))
  have outerSurfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations result.prevailing' result.frontier :=
    protectedSurfacesMembers.unprotectToken
  have shadowRetained : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing') result.prevailing'
      provenanceFrontier :=
    bodySurfacesRetained
      (lambdaShadowObligation provenanceFloor provenanceContext
        provenanceFrontier (.var supply.nextTy))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have shadowMembers : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (result.prevailing'.apply algorithm, selected) ∈ result.frontier :=
    by
      intro algorithm selected member
      exact bodySurfacesMembers
        (lambdaShadowObligation provenanceFloor provenanceContext
          provenanceFrontier (.var supply.nextTy))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (algorithm, selected) member
  exact ⟨
    { normalized := normalizedWitness
      contextCapFree := bodyResult.contextCapFreeOuter
      floorCaps := bodyResult.floorCapsOuter
      floorTargets := bodyResult.floorTargetsOuter
      contextOld := bodyResult.contextOldOuter
      contextProvenanceSuffix := bodyResult.contextProvenanceSuffixOuter
      provenanceIncluded := bodyResult.provenanceIncludedOuter
      targetOld := functionOwnerOld
      provenanceSuffix := bodyResult.provenanceSuffixOuter
      provenanceCovered := bodyResult.provenanceSuffixOuter.toProtectedFreeCovered _
      retainedOuter := by
        constructor
        · intro pair member varId free
          apply shadowRetained.caps pair member varId
          simpa [result.prevailing_eq, Subst.seq_apply,
            bodyResult.provenanceFrontierNormalizedOuter pair member] using free
        · intro pair member varId free
          apply shadowRetained.targets pair member varId
          simpa [result.prevailing_eq, Subst.seq_apply,
            bodyResult.provenanceFrontierNormalizedOuter pair member] using free
      provenanceRetains := fun algorithm selected member =>
        List.mem_cons_of_mem _
          (by
            simpa [result.prevailing_eq, Subst.seq_apply,
              bodyResult.provenanceFrontierNormalizedOuter
                (algorithm, selected) member] using
              shadowMembers algorithm selected member)
      surfacesRetained := outerSurfacesRetained
      surfacesMembers := by
        intro obligation obligationMember pair pairMember
        exact List.mem_cons_of_mem _
          (outerSurfacesMembers obligation obligationMember pair pairMember)
      inputFrontierNormalized := inputFrontierNormalizedOuter
      frontierNormalized := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | oldMember
        · exact result.prevailingIdempotent _
        · exact bodyFrontierNormalized pair oldMember
      currentPaired := currentPairedOuter }
    ⟩

theorem Typing.w_paired_erased_normalized_lam
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {contextResidual : SSubst}
    {name : String} {body : Expr} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired contextResidual) prevailing frames frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (_contextView : ErasedDMContextView contextResidual selectedContext
      (rawContext.applySubst prevailing))
    (contextScope : ResidualContextScope contextResidual
      (rawContext.applySubst prevailing) selectedContext)
    (_contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    (postAdmissible : AdmissiblePost [] (SSubst.paired contextResidual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (pendingCapFree : PendingLetsCapFree prevailing pending)
    (bodyContinuation :
      WRetiredStableFrameAt signature
          { supply with nextTy := supply.nextTy + 1 }
          (SSubst.paired (SSubst.extendFreshTarget contextResidual
            supply.nextTy domain)) prevailing
          ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
              (name, SScheme.mono domain) :: selectedContext)) :: frames)
          ((.var supply.nextTy, domain) :: frontier) pending →
      ErasedDMContextView
          (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
          ((name, SScheme.mono domain) :: selectedContext)
          (Context.applySubst prevailing
            ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)) →
      AdmissiblePost [] (SSubst.paired
        (SSubst.extendFreshTarget contextResidual supply.nextTy domain)) →
      PendingLetsCapFree prevailing pending →
      ResidualContextScope
        (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
        (Context.applySubst prevailing
          ((name, Scheme.mono (.var supply.nextTy)) :: rawContext))
        ((name, SScheme.mono domain) :: selectedContext) →
      Nonempty (WPairedErasedNormalizedLamBody signature supply prevailing rawContext
        name body selectedContext domain codomain provenanceFloor
        provenanceContext provenanceFrames provenanceFrontier
        generativityObligations frames frontier pending)) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.lam name body) selectedContext (.fn domain codomain) provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  have preparedCore := state.prepareLamBody (name := name) active
    prevailingBounded state.pendingBelow domain
  have prepared : WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 1 }
      (SSubst.paired (SSubst.extendFreshTarget contextResidual
        supply.nextTy domain)) prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      ((.var supply.nextTy, domain) :: frontier) pending := by
    rw [SSubst.paired_extendFreshTarget]
    exact preparedCore
  have preparedView : ErasedDMContextView
      (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
      ((name, SScheme.mono domain) :: selectedContext)
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)) :=
    ⟨prepared.stable.frame.contexts List.mem_cons_self⟩
  have preparedAdmissible : AdmissiblePost [] (SSubst.paired
      (SSubst.extendFreshTarget contextResidual supply.nextTy domain)) :=
    ⟨postAdmissible.cap⟩
  have extendedOuterScope : ResidualContextScope
      (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
      (rawContext.applySubst prevailing) selectedContext :=
    contextScope.extendFreshTarget
      (state.stable.frame.contextsBounded active) domain
  have preparedScope : ResidualContextScope
      (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext))
      ((name, SScheme.mono domain) :: selectedContext) := by
    have freshFixed := Subst.BoundedBy.apply_freshTarget prevailingBounded
    have consScope : ResidualContextScope
        (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
        ((name, Scheme.mono (.var supply.nextTy)) ::
          rawContext.applySubst prevailing)
        ((name, SScheme.mono domain) :: selectedContext) :=
      extendedOuterScope.consMono
        (algorithmVar := supply.nextTy) (selectedDomain := domain)
        (by simp [SSubst.extendFreshTarget]) name
    intro source image sourceFree imageFree
    apply consScope (algorithmVar := source) (selectedVar := image)
    · simpa [Context.applySubst, freshFixed] using sourceFree
    · exact imageFree
  obtain ⟨bodyPackage⟩ := bodyContinuation prepared preparedView
    preparedAdmissible pendingCapFree preparedScope
  have domainMember :
      (prevailing.apply (.var supply.nextTy), domain) ∈
        ((.var supply.nextTy, domain) :: frontier) := by
    rw [Subst.BoundedBy.apply_freshTarget prevailingBounded]
    exact List.mem_cons_self
  exact Typing.w_paired_erased_normalized_lam_of_body prepared domainMember
    bodyPackage.body bodyPackage.surfacesRetained bodyPackage.surfacesMembers
    bodyPackage.frontierNormalized bodyPackage.currentPairedOuter
    bodyPackage.inputFrontierNormalizedOuter

end DM
end TypePM
