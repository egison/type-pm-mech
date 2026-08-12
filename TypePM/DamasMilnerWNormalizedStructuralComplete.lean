import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerWNormalizedVarComplete
import TypePM.DamasMilnerWRetiredStructural
import TypePM.DamasMilnerWCutNormalization

/-!
# Normalized structural completeness constructors

Cut-free syntax constructors preserve the residual chosen by their recursive
children.  This module packages that fact without reopening solver details.
-/

namespace TypePM
namespace DM

/-- One-sort spelling of installing the fresh lambda domain. -/
def SSubst.extendFreshTarget (base : SSubst) (fresh : TypePM.TyVar)
    (selected : STy) : SSubst :=
  fun name => if name = fresh then selected else base name

theorem SSubst.paired_extendFreshTarget
    (base : SSubst) (fresh : TypePM.TyVar) (selected : STy) :
    SSubst.paired (SSubst.extendFreshTarget base fresh selected) =
      DM.extendFreshTarget (SSubst.paired base) fresh selected := by
  apply PhasedPost.subst_ext
  · rfl
  · funext name
    by_cases equality : name = fresh
    · simp [SSubst.paired, SSubst.emb, SSubst.extendFreshTarget,
        DM.extendFreshTarget, equality]
    · simp [SSubst.paired, SSubst.emb, SSubst.extendFreshTarget,
        DM.extendFreshTarget, equality, Ne.symm equality]

theorem ResidualContextScope.extendFreshTarget
    {residual : SSubst} {algorithmContext : Context}
    {selectedContext : SCtx} (scope : ResidualContextScope residual
      algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply)
    (domain : STy) :
    ResidualContextScope
      (SSubst.extendFreshTarget residual supply.nextTy domain)
      algorithmContext selectedContext := by
  intro algorithmVar selectedVar algorithmFree imageFree
  have below : algorithmVar < supply.nextTy := by
    rw [Context.ftv] at algorithmFree
    rcases List.mem_flatMap.mp algorithmFree with
      ⟨entry, entryMember, free⟩
    exact (bounded entry entryMember).targets algorithmVar free
  have distinct : algorithmVar ≠ supply.nextTy := Nat.ne_of_lt below
  apply scope algorithmFree
  simpa [SSubst.extendFreshTarget, distinct] using imageFree

/-- Normalized context presented to the recursive lambda-body call. -/
theorem NormalizedDMContextView.prepareLamBody
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {normalizedContext rawContext : Context} {prevailing : Subst}
    (view : NormalizedDMContextView residual algorithmContext selectedContext
      normalizedContext)
    (normalizedEq : normalizedContext = rawContext.applySubst prevailing)
    (outerBounded : normalizedContext.BoundedBy supply)
    (bounded : prevailing.BoundedBy supply) (name : String) (domain : STy) :
    NormalizedDMContextView
      (SSubst.extendFreshTarget residual supply.nextTy domain)
      ((name, SScheme.mono (.var supply.nextTy)) :: algorithmContext)
      ((name, SScheme.mono domain) :: selectedContext)
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)) := by
  have freshFixed : prevailing.apply (.var supply.nextTy) =
      .var supply.nextTy :=
    Subst.BoundedBy.apply_freshTarget bounded
  have outer : NormalizedDMContextView
      (SSubst.extendFreshTarget residual supply.nextTy domain)
      algorithmContext selectedContext normalizedContext := by
    refine ⟨view.normalized_eq, ?_⟩
    rw [SSubst.paired_extendFreshTarget]
    exact WContextRel.extendFreshTarget domain view.related
      outerBounded
  have domainEquation :
      STy.applySubst (SSubst.extendFreshTarget residual supply.nextTy domain)
        (.var supply.nextTy) = domain := by
    simp [STy.applySubst, SSubst.extendFreshTarget]
  have cons := outer.consMono domainEquation name
  rw [normalizedEq] at cons
  simpa [Context.applySubst, freshFixed, STy.emb] using cons

/-- The normalized information needed when returning from a lambda body.
The recursive body witness supplies the codomain view; these two projections
identify the outer context and the temporary fresh domain at its final post. -/
structure WNormalizedLamBody
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
    provenanceFloor provenanceContext provenanceFrames provenanceFrontier
    (GenerativitySurfaceObligation.current
      { supply with nextTy := supply.nextTy + 1 }
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) ::
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        generativityObligations)
    ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
        (name, SScheme.mono domain) :: selectedContext)) :: frames)
    ((.var supply.nextTy, domain) :: frontier) pending
  algorithmContext : SCtx
  algorithmDomain : STy
  outer : NormalizedDMContextView result.residual algorithmContext
    selectedContext (rawContext.applySubst result.complete.prevailing')
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
  protectedCoveredOuter : ProtectedFreeCovered
    (rawContext.applySubst result.complete.prevailing') frames
    result.complete.prevailing'
  provenanceIncludedOuter : ProvenanceContextIncluded
    (provenanceContext.applySubst result.complete.prevailing')
    (rawContext.applySubst result.complete.prevailing')
  contextSuffixOuter : ProtectedContextsSuffix rawContext frames
  retainedOuterOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst result.complete.prevailing')
    result.complete.suffix provenanceFrontier
  generativityValidOuter : GenerativitySurfaceValid supply rawContext
    generativityObligations
  currentObligationOuter : GenerativitySurfaceObligation.current supply
    rawContext ∈ generativityObligations
  localOldFreeOuter : OldFreeInContextAt supply
    (rawContext.applySubst result.complete.prevailing')
    (result.complete.prevailing'.apply
      (.fn (.var supply.nextTy) result.complete.rawTarget))

/-- Package a normalized recursive body as a normalized lambda result. -/
theorem Typing.w_normalized_lam_of_body
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
      { supply with nextTy := supply.nextTy + 1 }
      post prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      ((.var supply.nextTy, domain) :: frontier) pending)
    (domainMember : (prevailing.apply (.var supply.nextTy), domain) ∈
      ((.var supply.nextTy, domain) :: frontier))
    (bodyResult : WNormalizedLamBody signature supply prevailing rawContext
      name body selectedContext domain codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.lam name body) selectedContext (.fn domain codomain) provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  let result := bodyResult.result.complete
  have bodyEquation :
      result.post.apply (result.prevailing'.apply result.rawTarget) =
        codomain.emb :=
    result.frame.types result.targetMember
  have bodyContextRelated : WContextRel result.post
      (Context.applySubst result.prevailing'
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext))
      ((name, SScheme.mono domain) :: selectedContext) :=
    result.frame.contexts List.mem_cons_self
  have domainEquation :
      result.post.apply (result.prevailing'.apply (.var supply.nextTy)) =
        domain.emb :=
    WContextRel.consMono_head_equation bodyContextRelated
  let derived : DemandSynth signature supply prevailing rawContext
      (.lam name body) (.fn (.var supply.nextTy) result.rawTarget)
      result.successor result.prevailing' := DemandSynth.lam result.derived
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.lam result.origin
  have dropped := result.frame.dropContextHead
  have functionEquation : result.post.apply
      (result.prevailing'.apply
        (.fn (.var supply.nextTy) result.rawTarget)) =
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
  have domainOwnerOld := bodyResult.result.protectedOld _ finalDomainMember
  have bodyOwnerOld := bodyResult.result.protectedOld _ result.targetMember
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
  have normalized : NormalizedDMView bodyResult.result.residual
      bodyResult.algorithmContext selectedContext
      (.fn bodyResult.algorithmDomain bodyResult.result.algorithmTarget)
      (.fn domain codomain)
      (rawContext.applySubst result.prevailing')
      (result.prevailing'.apply
        (.fn (.var supply.nextTy) result.rawTarget)) := by
    simpa only [Subst.apply_fn] using
      NormalizedDMView.lam bodyResult.outer bodyResult.domainView
        bodyResult.result.target
  have functionGenerativity : GenerativitySurfaceFrameAt
      generativityObligations result.prevailing' := by
    apply GenerativitySurfaceFrameAt.unprotectToken
    intro obligation obligationMember raw rawMember
    exact bodyResult.result.generativity obligation
      (List.mem_cons_of_mem _ obligationMember) raw rawMember
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
      (List.mem_cons_of_mem _ protectedMember)
    have coveredCons : OldContextCoveredAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        ((name, (Scheme.mono (.var supply.nextTy)).applyMeta
          result.prevailing') :: rawContext.applySubst result.prevailing') := by
      simpa [protectedObligation,
        GenerativitySurfaceObligation.protectToken,
        Context.applySubst, List.map_cons] using covered
    exact coveredCons.dropActiveHead
  exact ⟨
    { complete := complete
      algorithmContext := bodyResult.algorithmContext
      algorithmTarget :=
        .fn bodyResult.algorithmDomain bodyResult.result.algorithmTarget
      residual := bodyResult.result.residual
      post_eq := bodyResult.result.post_eq
      context := ⟨normalized.context.related⟩
      scope := bodyResult.outerScope
      protectedScopes := by
        intro pair member
        exact bodyResult.result.protectedScopes pair
          (List.mem_cons_of_mem _ member)
      target := normalized.target
      floorCaps := bodyResult.floorCapsOuter
      floorTargets := bodyResult.floorTargetsOuter
      contextOld := bodyResult.contextOldOuter
      contextProvenanceSuffix := bodyResult.contextProvenanceSuffixOuter
      protectedOld := bodyResult.result.protectedOld.cons functionOwnerOld
      provenanceCovered := bodyResult.result.provenanceCovered
      provenanceIncluded := bodyResult.provenanceIncludedOuter
      provenanceSuffix := bodyResult.result.provenanceSuffix
      retainedOuter := bodyResult.retainedOuterOuter
      provenanceRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (bodyResult.result.provenanceRetains algorithm selected member)
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
            (List.mem_cons_of_mem _ protectedMember) _ List.mem_cons_self)
          (bodyResult.result.targetGenerative protectedObligation
            (List.mem_cons_of_mem _ protectedMember))
      localOldFree := bodyResult.localOldFreeOuter
      protectedCovered := bodyResult.protectedCoveredOuter
      contextSuffix := bodyResult.contextSuffixOuter
      pendingCapFree := result.pendingCapFree }
    ⟩

/-- Continuation-form lambda constructor at the mutual induction boundary.
It prepares the fresh domain with an exactly paired residual, supplies the
normalized body context to recursion, and structurally closes the returned
body witness. -/
theorem Typing.w_normalized_lam
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext algorithmContext : SCtx}
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
    (contextView : NormalizedDMContextView contextResidual algorithmContext
      selectedContext (rawContext.applySubst prevailing))
    (contextScope : ResidualContextScope contextResidual
      (rawContext.applySubst prevailing) selectedContext)
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
      NormalizedDMContextView
          (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
          ((name, SScheme.mono (.var supply.nextTy)) :: algorithmContext)
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
      Nonempty (WNormalizedLamBody signature supply prevailing rawContext
        name body selectedContext domain codomain provenanceFloor
        provenanceContext provenanceFrames provenanceFrontier
        generativityObligations frames
        frontier pending)) :
    WNormalizedCompleteResult signature supply prevailing rawContext
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
  have preparedView : NormalizedDMContextView
      (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
      ((name, SScheme.mono (.var supply.nextTy)) :: algorithmContext)
      ((name, SScheme.mono domain) :: selectedContext)
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)) :=
    contextView.prepareLamBody rfl
      (state.stable.frame.contextsBounded active) prevailingBounded name domain
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
    have freshFixed : prevailing.apply (.var supply.nextTy) =
        .var supply.nextTy :=
      Subst.BoundedBy.apply_freshTarget prevailingBounded
    have consScope : ResidualContextScope
        (SSubst.extendFreshTarget contextResidual supply.nextTy domain)
        ((name, Scheme.mono (.var supply.nextTy)) ::
          rawContext.applySubst prevailing)
        ((name, SScheme.mono domain) :: selectedContext) :=
      extendedOuterScope.consMono (algorithmVar := supply.nextTy)
        (selectedDomain := domain)
        (by simp [SSubst.extendFreshTarget]) name
    intro source image sourceFree imageFree
    apply consScope (algorithmVar := source) (selectedVar := image)
    · simpa [Context.applySubst, freshFixed] using sourceFree
    · exact imageFree
  obtain ⟨bodyResult⟩ := bodyContinuation prepared preparedView
    preparedAdmissible pendingCapFree preparedScope
  have domainMember :
      (prevailing.apply (.var supply.nextTy), domain) ∈
        ((.var supply.nextTy, domain) :: frontier) := by
    rw [Subst.BoundedBy.apply_freshTarget prevailingBounded]
    exact List.mem_cons_self
  exact Typing.w_normalized_lam_of_body prepared domainMember bodyResult

/-- Tail traversal together with the entry-indexed generative projections
that cannot be recovered from a tail result indexed at the head's successor.
The mutual motive constructs this package directly while keeping the original
entry supply and both original continuation surfaces fixed. -/
structure WNormalizedConsTail
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expression : Expr) (expressions : List Expr)
    (selectedContext : SCtx) (selected : STy)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut)
    (head : WNormalizedCompleteWitness signature supply prevailing rawContext
      expression selectedContext selected InferenceBase.FreshSupply.empty []
      [] [] generativityObligations frames
      inputFrontier inputPending) :
    Type where
  result : WNormalizedTypingsWitness signature head.complete.successor
    head.complete.prevailing' rawContext expressions selectedContext
    selectedTargets provenanceFloor provenanceContext provenanceFrames
    (provenanceFrontier.map fun pair =>
      (head.complete.suffix.apply pair.1, pair.2))
    (GenerativitySurfaceObligation.currentPaired head.complete.successor
      rawContext head.complete.frontier ::
    GenerativitySurfaceObligation.current head.complete.successor rawContext ::
      GenerativitySurfaceObligations.protectToken head.complete.rawTarget
        generativityObligations)
    frames head.complete.frontier head.complete.pending
  retainedOuterOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst result.complete.prevailing')
    (Subst.seq result.complete.suffix head.complete.suffix) provenanceFrontier
  provenanceRetainsOuter : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      ((Subst.seq result.complete.suffix head.complete.suffix).apply algorithm,
        selected) ∈ result.complete.frontier
  generativityValidOuter : GenerativitySurfaceValid supply rawContext
    generativityObligations
  currentObligationOuter : GenerativitySurfaceObligation.current supply
    rawContext ∈ generativityObligations
  targetsLocalOldFreeOuter : ∀ raw ∈
      (head.complete.rawTarget :: result.complete.rawTargets),
    OldFreeInContextAt supply
      (rawContext.applySubst result.complete.prevailing')
      (result.complete.prevailing'.apply raw)

/-- Paired continuation strengthening of the chronological tail package. -/
structure WPairedNormalizedConsTail
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expression : Expr) (expressions : List Expr)
    (selectedContext : SCtx) (selected : STy)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut)
    (head : WNormalizedCompleteWitness signature supply prevailing rawContext
      expression selectedContext selected InferenceBase.FreshSupply.empty []
      [] [] generativityObligations frames
      inputFrontier inputPending) : Type where
  result : WPairedNormalizedTypingsWitness signature head.complete.successor
    head.complete.prevailing' rawContext expressions selectedContext
    selectedTargets provenanceFloor provenanceContext provenanceFrames
    (provenanceFrontier.map fun pair =>
      (head.complete.suffix.apply pair.1, pair.2))
    (GenerativitySurfaceObligation.currentPaired head.complete.successor
      rawContext head.complete.frontier ::
    GenerativitySurfaceObligation.current head.complete.successor rawContext ::
      GenerativitySurfaceObligations.protectToken head.complete.rawTarget
        generativityObligations)
    frames head.complete.frontier head.complete.pending
  surfacesRetained : GenerativitySurfaceRetainedAt
    (GenerativitySurfaceObligation.currentPaired head.complete.successor
      rawContext head.complete.frontier ::
    GenerativitySurfaceObligation.current head.complete.successor rawContext ::
      GenerativitySurfaceObligations.protectToken head.complete.rawTarget
        generativityObligations)
    result.normalized.complete.prevailing'
  surfacesMembers : GenerativitySurfaceMembersAt
    (GenerativitySurfaceObligation.currentPaired head.complete.successor
      rawContext head.complete.frontier ::
    GenerativitySurfaceObligation.current head.complete.successor rawContext ::
      GenerativitySurfaceObligations.protectToken head.complete.rawTarget
        generativityObligations)
    result.normalized.complete.prevailing' result.normalized.complete.frontier
  frontierNormalized : ∀ pair ∈ result.normalized.complete.frontier,
    result.normalized.complete.prevailing'.apply pair.1 = pair.1
  currentPairedOuter : GenerativitySurfaceObligation.currentPaired supply
    rawContext inputFrontier ∈ generativityObligations
  inputFrontierNormalizedOuter : ∀ pair ∈ inputFrontier,
    prevailing.apply pair.1 = pair.1

/-- Chronological normalized list cons.  The tail's final paired frame
re-decodes the retained head target, so no direct transport of the head's
earlier algorithm target across the tail residual is required. -/
theorem Typings.w_paired_normalized_cons_of_results
    {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    {rawContext : Context} {expression : Expr} {expressions : List Expr}
    {selectedContext : SCtx} {selected : STy}
    {selectedTargets : List STy} {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (headPackage : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext expression selectedContext selected provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (tailResult : Nonempty (WPairedNormalizedConsTail signature supply prevailing rawContext
        expression expressions selectedContext selected selectedTargets
        provenanceFloor provenanceContext provenanceFrames provenanceFrontier
        generativityObligations frames inputFrontier inputPending
        headPackage.normalized)) :
    WPairedNormalizedTypingsResult signature supply prevailing rawContext
      (expression :: expressions) selectedContext
      (selected :: selectedTargets) provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames
      inputFrontier inputPending := by
  let head := headPackage.normalized
  rcases tailResult with ⟨pairedTailPackage⟩
  let tailPackage := pairedTailPackage.result
  let tail := tailPackage.normalized
  let headComplete := head.complete
  let tailComplete := tail.complete
  let derived : DemandSynths signature supply prevailing rawContext
      (expression :: expressions)
      (headComplete.rawTarget :: tailComplete.rawTargets)
      tailComplete.successor tailComplete.prevailing' :=
    DemandSynths.cons headComplete.derived tailComplete.derived
  let origin : DemandSynthsOrigin signature derived [] [] :=
    DemandSynthsOrigin.cons headComplete.origin tailComplete.origin
  let auditPlan : WSynthsAuditPlan signature (origin := origin) :=
    WSynthsAuditPlan.cons headComplete.auditPlan tailComplete.auditPlan
  have headFinalMember :
      (tailComplete.prevailing'.apply headComplete.rawTarget, selected) ∈
        tailComplete.frontier := by
    have retained := tailComplete.frontierRetains _ _ headComplete.targetMember
    rw [tailComplete.prevailing_eq, Subst.seq_apply]
    exact retained
  have headEquation : tailComplete.post.apply
      (tailComplete.prevailing'.apply headComplete.rawTarget) = selected.emb :=
    tailComplete.frame.types headFinalMember
  have pairedHeadEquation : (SSubst.paired tail.residual).apply
      (tailComplete.prevailing'.apply headComplete.rawTarget) =
        selected.emb := by
    rw [← tail.post_eq]
    exact headEquation
  obtain ⟨algorithmHead, headView⟩ :=
    NormalizedDMTargetView.ofPairedEquation pairedHeadEquation
  have headFinalBounded :
      (tailComplete.prevailing'.apply headComplete.rawTarget).BoundedBy
        tailComplete.successor :=
    tailComplete.frame.frontierBounded _ headFinalMember
  let complete : WTypingsFinalWitness signature supply prevailing rawContext
      (expression :: expressions) (selected :: selectedTargets) frames
      inputFrontier inputPending :=
    { successor := tailComplete.successor
      prevailing' := tailComplete.prevailing'
      rawTargets := headComplete.rawTarget :: tailComplete.rawTargets
      post := tailComplete.post
      frontier := tailComplete.frontier
      derived := derived
      origin := origin
      auditPlan := auditPlan
      pending := tailComplete.pending
      stability := tailComplete.stability
      retains := fun cut member =>
        tailComplete.retains cut (headComplete.retains cut member)
      auditCuts := by
        intro cut member
        rcases List.mem_append.mp member with headMember | tailMember
        · exact tailComplete.retains cut
            (headComplete.auditCuts cut headMember)
        · exact tailComplete.auditCuts cut tailMember
      equations := WTargetListRel.cons headEquation tailComplete.equations
      targetsFresh := by
        intro cut cutMember raw member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact tailComplete.retired cut cutMember _ headFinalMember
        · exact tailComplete.targetsFresh cut cutMember raw tailMember
      targetsBounded := by
        intro raw member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headFinalBounded
        · exact tailComplete.targetsBounded raw tailMember
      postAdmissible := tailComplete.postAdmissible
      prevailingBounded := tailComplete.prevailingBounded
      prevailingIdempotent := tailComplete.prevailingIdempotent
      frame := tailComplete.frame
      retired := tailComplete.retired
      contextsRetired := tailComplete.contextsRetired
      pendingBelow := tailComplete.pendingBelow
      pendingCapFree := tailComplete.pendingCapFree
      suffix := Subst.seq tailComplete.suffix headComplete.suffix
      prevailing_eq := by
        calc
          tailComplete.prevailing' =
              Subst.seq tailComplete.suffix headComplete.prevailing' :=
            tailComplete.prevailing_eq
          _ = Subst.seq tailComplete.suffix
              (Subst.seq headComplete.suffix prevailing) :=
            congrArg (Subst.seq tailComplete.suffix)
              headComplete.prevailing_eq
          _ = Subst.seq
              (Subst.seq tailComplete.suffix headComplete.suffix)
              prevailing :=
            PhasedPost.seq_assoc tailComplete.suffix headComplete.suffix
              prevailing
      frontierRetains := by
        intro algorithm selectedTarget member
        have first := headComplete.frontierRetains algorithm selectedTarget
          member
        have second := tailComplete.frontierRetains _ _ first
        simpa only [Subst.seq_apply] using second }
  let outerWitness : WNormalizedTypingsWitness signature supply
      prevailing rawContext (expression :: expressions) selectedContext
      (selected :: selectedTargets) InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames
      inputFrontier inputPending :=
    { complete := complete
      algorithmContext := tail.algorithmContext
      algorithmTargets := algorithmHead :: tail.algorithmTargets
      residual := tail.residual
      post_eq := tail.post_eq
      context := tail.context
      scope := tail.scope
      protectedScopes := tail.protectedScopes
      targets := NormalizedDMTargetsView.cons headView tail.targets
      floorCaps := by simp [InferenceBase.FreshSupply.empty]
      floorTargets := by simp [InferenceBase.FreshSupply.empty]
      contextOld := tail.contextOld
      contextProvenanceSuffix := tail.contextProvenanceSuffix
      protectedOld := tail.protectedOld
      provenanceCovered := tail.provenanceCovered
      provenanceIncluded := tail.provenanceIncluded
      provenanceSuffix := tail.provenanceSuffix
      retainedOuter := RetainedOldOrContextAt.nil
        InferenceBase.FreshSupply.empty [] complete.suffix
      provenanceRetains := by intro algorithm selected member; cases member
      generativity := by
        apply GenerativitySurfaceFrameAt.unprotectToken
        intro obligation obligationMember raw rawMember
        exact tail.generativity obligation
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ obligationMember)) raw
          rawMember
      generativityContexts := by
        intro obligation obligationMember
        let protectedObligation :=
          obligation.protectToken headComplete.rawTarget
        have protectedMember : protectedObligation ∈
            GenerativitySurfaceObligations.protectToken headComplete.rawTarget
              generativityObligations :=
          List.mem_map.mpr ⟨obligation, obligationMember, rfl⟩
        simpa [protectedObligation,
          GenerativitySurfaceObligation.protectToken] using
          tail.generativityContexts protectedObligation
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ protectedMember))
      generativityValid := head.generativityValid
      currentObligation := head.currentObligation
      targetsLocalOldFree := by
        intro raw rawMember
        let protectedCurrent :=
          (GenerativitySurfaceObligation.current supply rawContext).protectToken
            headComplete.rawTarget
        have protectedCurrentMember : protectedCurrent ∈
            GenerativitySurfaceObligations.protectToken headComplete.rawTarget
              generativityObligations :=
          List.mem_map.mpr ⟨_, head.currentObligation, rfl⟩
        rcases List.mem_cons.mp rawMember with rfl | tailMember
        · exact tail.generativity protectedCurrent
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              protectedCurrentMember)) _ List.mem_cons_self
        · exact tail.targetsGenerative protectedCurrent
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              protectedCurrentMember)) raw tailMember
      targetsGenerative := by
        intro obligation obligationMember raw rawMember
        let protectedObligation := obligation.protectToken headComplete.rawTarget
        have protectedMember : protectedObligation ∈
            GenerativitySurfaceObligations.protectToken headComplete.rawTarget
              generativityObligations :=
          List.mem_map.mpr ⟨obligation, obligationMember, rfl⟩
        rcases List.mem_cons.mp rawMember with rfl | tailMember
        · exact tail.generativity protectedObligation
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ protectedMember)) _
            List.mem_cons_self
        · exact tail.targetsGenerative protectedObligation
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ protectedMember)) raw
            tailMember
      protectedCovered := tail.protectedCovered
      contextSuffix := tail.contextSuffix }
  let normalizedWitness : WNormalizedTypingsWitness signature supply
      prevailing rawContext (expression :: expressions) selectedContext
      (selected :: selectedTargets) InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames inputFrontier inputPending :=
    { complete := complete
      algorithmContext := outerWitness.algorithmContext
      algorithmTargets := outerWitness.algorithmTargets
      residual := outerWitness.residual
      post_eq := outerWitness.post_eq
      context := outerWitness.context
      scope := outerWitness.scope
      protectedScopes := outerWitness.protectedScopes
      targets := outerWitness.targets
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
      generativity := outerWitness.generativity
      generativityContexts := outerWitness.generativityContexts
      generativityValid := outerWitness.generativityValid
      currentObligation := outerWitness.currentObligation
      targetsLocalOldFree := outerWitness.targetsLocalOldFree
      targetsGenerative := outerWitness.targetsGenerative
      protectedCovered := outerWitness.protectedCovered
      contextSuffix := outerWitness.contextSuffix }
  have protectedSurfacesRetained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectToken headComplete.rawTarget
        generativityObligations) tailComplete.prevailing' :=
    pairedTailPackage.surfacesRetained.of_obligations_subset (by
      intro obligation member
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have outerSurfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations tailComplete.prevailing' :=
    protectedSurfacesRetained.unprotectToken
  have protectedSurfacesMembers : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectToken headComplete.rawTarget
        generativityObligations) tailComplete.prevailing'
      tailComplete.frontier :=
    pairedTailPackage.surfacesMembers.of_obligations_subset (by
      intro obligation member
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have outerSurfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations tailComplete.prevailing' tailComplete.frontier :=
    protectedSurfacesMembers.unprotectToken
  exact ⟨
    { normalized := normalizedWitness
      contextCapFree := tailPackage.contextCapFree
      floorCaps := headPackage.floorCaps
      floorTargets := headPackage.floorTargets
      contextOld := tailPackage.contextOld
      contextProvenanceSuffix := headPackage.contextProvenanceSuffix
      provenanceIncluded := headPackage.contextProvenanceSuffix.toIncluded _
      targetsOld := by
        intro raw rawMember
        have localOld := outerWitness.targetsLocalOldFree raw rawMember
        constructor
        · intro varId free below
          exact tailPackage.contextOld.caps varId
            (localOld.caps varId free
              (Nat.lt_of_lt_of_le below headPackage.floorCaps)) below
        · intro varId free below
          exact tailPackage.contextOld.targets varId
            (localOld.targets varId free
              (Nat.lt_of_lt_of_le below headPackage.floorTargets)) below
      provenanceSuffix := headPackage.provenanceSuffix
      provenanceCovered := headPackage.provenanceSuffix.toProtectedFreeCovered _
      retainedOuter := by
        constructor
        · intro pair member varId free
          change varId ∈ ((Subst.seq tailComplete.suffix
            headComplete.suffix).apply pair.1).fcv at free
          apply tailPackage.retainedOuter.caps
            (headComplete.suffix.apply pair.1, pair.2)
            (List.mem_map.mpr ⟨pair, member, rfl⟩) varId
          simpa only [Subst.seq_apply] using free
        · intro pair member varId free
          change varId ∈ ((Subst.seq tailComplete.suffix
            headComplete.suffix).apply pair.1).ftv at free
          apply tailPackage.retainedOuter.targets
            (headComplete.suffix.apply pair.1, pair.2)
            (List.mem_map.mpr ⟨pair, member, rfl⟩) varId
          simpa only [Subst.seq_apply] using free
      provenanceRetains := by
        intro algorithm selected member
        change ((Subst.seq tailComplete.suffix headComplete.suffix).apply
          algorithm, selected) ∈ tailComplete.frontier
        simpa only [Subst.seq_apply] using
          tailPackage.provenanceRetains
            (headComplete.suffix.apply algorithm) selected
            (List.mem_map.mpr ⟨(algorithm, selected), member, rfl⟩)
      surfacesRetained := outerSurfacesRetained
      surfacesMembers := outerSurfacesMembers
      inputFrontierNormalized := headPackage.inputFrontierNormalized
      frontierNormalized := pairedTailPackage.frontierNormalized
      currentPaired := headPackage.currentPaired }
    ⟩

/-- Existing normalized chronological tuple packaging, re-exported beside the
other structural constructors for the mutual induction. -/
theorem Typing.w_normalized_tuple
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {expressions : List Expr} {selectedContext : SCtx}
    {selectedTargets : List STy} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (children : WNormalizedTypingsResult signature supply prevailing rawContext
      expressions selectedContext selectedTargets provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.tuple expressions) selectedContext (.prod selectedTargets)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  rcases children with ⟨children⟩
  let finished := children.complete
  let derived : DemandSynth signature supply prevailing rawContext
      (.tuple expressions) (.prod finished.rawTargets)
      finished.successor finished.prevailing' :=
    DemandSynth.tuple finished.derived
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.tuple finished.origin
  have productFresh : ∀ cut ∈ finished.pending,
      cut.AvoidsTy signature finished.prevailing'
        (finished.prevailing'.apply (.prod finished.rawTargets)) := by
    intro cut cutMember
    simp only [Subst.apply_prod]
    apply PendingLetCut.AvoidsTy.prod
    intro component componentMember
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
    exact finished.targetsFresh cut cutMember raw rawMember
  have finalFrame := finished.frame.protectTupleTarget
    finished.equations finished.targetsBounded
  let complete : WCompleteWitness signature supply prevailing rawContext
      (.tuple expressions) (.prod selectedTargets) frames frontier pending :=
    { successor := finished.successor
      prevailing' := finished.prevailing'
      rawTarget := .prod finished.rawTargets
      post := finished.post
      frontier :=
        (finished.prevailing'.apply (.prod finished.rawTargets),
          .prod selectedTargets) :: finished.frontier
      derived := derived
      origin := origin
      auditPlan := WSynthAuditPlan.tuple finished.auditPlan
      pending := finished.pending
      stability := finished.stability
      retains := finished.retains
      auditCuts := finished.auditCuts
      postAdmissible := finished.postAdmissible
      prevailingBounded := finished.prevailingBounded
      prevailingIdempotent := finished.prevailingIdempotent
      frame := finalFrame
      retired := RetiredFrontierFresh.cons productFresh finished.retired
      contextsRetired := finished.contextsRetired
      pendingBelow := finished.pendingBelow
      pendingCapFree := finished.pendingCapFree
      suffix := finished.suffix
      prevailing_eq := finished.prevailing_eq
      frontierRetains := fun algorithm selected member =>
        List.mem_cons_of_mem _
          (finished.frontierRetains algorithm selected member)
      targetMember := List.mem_cons_self }
  have productOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing')
      (finished.prevailing'.apply (.prod finished.rawTargets)) := by
    rw [Subst.apply_prod]
    exact OldFreeInContextAt.prod (by
      intro component componentMember
      obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
      have localOld := children.targetsLocalOldFree raw rawMember
      constructor
      · intro varId free below
        exact children.contextOld.caps varId
          (localOld.caps varId free
            (Nat.lt_of_lt_of_le below children.floorCaps)) below
      · intro varId free below
        exact children.contextOld.targets varId
          (localOld.targets varId free
            (Nat.lt_of_lt_of_le below children.floorTargets)) below)
  exact ⟨
    { complete := complete
      algorithmContext := children.algorithmContext
      algorithmTarget := .prod children.algorithmTargets
      residual := children.residual
      post_eq := children.post_eq
      context := children.context
      scope := children.scope
      protectedScopes := children.protectedScopes
      target := by
        change NormalizedDMTargetView children.residual
          (.prod children.algorithmTargets) (.prod selectedTargets)
          (finished.prevailing'.apply (.prod finished.rawTargets))
        simpa only [Subst.apply_prod] using children.targets.prod
      floorCaps := children.floorCaps
      floorTargets := children.floorTargets
      contextOld := children.contextOld
      contextProvenanceSuffix := children.contextProvenanceSuffix
      protectedOld := children.protectedOld.cons productOld
      provenanceCovered := children.provenanceCovered
      provenanceIncluded := children.provenanceIncluded
      provenanceSuffix := children.provenanceSuffix
      retainedOuter := children.retainedOuter
      provenanceRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (children.provenanceRetains algorithm selected member)
      generativity := children.generativity
      generativityContexts := children.generativityContexts
      generativityValid := children.generativityValid
      currentObligation := children.currentObligation
      targetGenerative := by
        intro obligation obligationMember
        rw [Subst.apply_prod]
        exact OldFreeInContextAt.prod (by
          intro component componentMember
          obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
          exact children.targetsGenerative obligation obligationMember raw
            rawMember)
      localOldFree := by
        rw [Subst.apply_prod]
        exact OldFreeInContextAt.prod (by
          intro component componentMember
          obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
          exact children.targetsLocalOldFree raw rawMember)
      protectedCovered := children.protectedCovered
      contextSuffix := children.contextSuffix
      pendingCapFree := finished.pendingCapFree }
    ⟩

end DM
end TypePM
