import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerWCompleteSteps
import TypePM.DamasMilnerWCutNormalization
import TypePM.DamasMilnerWGenerativeTransport
import TypePM.DemandTypingIdempotence

/-!
# Final constructor packaging for Damas--Milner W completeness

The recursive constructor proofs first build a raw/origin/audit plan and a
coupled retired state.  This module installs those pieces into the final
normalized completeness witness without repeating the large record literal
in application, fix, and let cases.
-/

namespace TypePM
namespace DM

/-- Real-provenance shadow for the two application/fix controls.  It is kept
separate from paired continuation surfaces because fresh controls
are old-free but need not satisfy the retained disjunction at an older floor. -/
def provenanceControlObligation (floor : InferenceBase.FreshSupply)
    (owner : Context) (first : Nat) : GenerativitySurfaceObligation :=
  { floor := floor
    owner := owner
    continuation := []
    protectedOld := [.var first, .var (first + 1)] }

/-- Application shadow carrying the real provenance continuation together
with the two fresh control metavariables across argument recursion. -/
def provenanceApplicationObligation (floor : InferenceBase.FreshSupply)
    (owner : Context) (first : Nat) (suffix : Subst)
    (frontier : List (Ty × STy)) : GenerativitySurfaceObligation :=
  { floor := floor
    owner := owner
    continuation := frontier.map fun pair => (suffix.apply pair.1, pair.2)
    protectedOld := [.var first, .var (first + 1)] }

/-- Existential input package used by continuation-form constructors. -/
structure NormalizedChild
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (expression : Expr)
    (selectedContext : SCtx) (selectedTarget : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Type where
  result : WNormalizedCompleteWitness signature supply prevailing rawContext
    expression selectedContext selectedTarget provenanceFloor provenanceContext
    provenanceFrames provenanceFrontier generativityObligations frames frontier
    pending

/-- State handed to the application-argument recursive call after the
function result has been aligned with the two fresh W metavariables. -/
structure WAppArgumentPrepared
    (signature : FrozenSig) (rawContext : Context)
    (selectedContext : SCtx) (domain codomain : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (functionResultSupply : InferenceBase.FreshSupply)
    (functionPrevailing : Subst)
    (functionSuffix : Subst)
    (functionFrontier : List (Ty × STy))
    (functionPending : List PendingLetCut) : Type where
  prevailing : Subst
  residual : SSubst
  frontier : List (Ty × STy)
  state : WRetiredStableFrameAt signature
    { functionResultSupply with
      nextTy := functionResultSupply.nextTy + 2 }
    (SSubst.paired residual)
    prevailing frames frontier functionPending
  context : ErasedDMContextView residual selectedContext
    (rawContext.applySubst prevailing)
  scope : ResidualContextScope residual
    (rawContext.applySubst prevailing) selectedContext
  protectedScopes : ProtectedResidualScopes residual prevailing frames
  postAdmissible : AdmissiblePost [] (SSubst.paired residual)
  prevailingBounded : prevailing.BoundedBy
    { functionResultSupply with
      nextTy := functionResultSupply.nextTy + 2 }
  prevailingIdempotent : prevailing.Idempotent
  pendingCapFree : PendingLetsCapFree prevailing functionPending
  functionTarget : Ty
  solverDelta : Subst
  solverCut : LetStableExactPairedCut signature functionPrevailing functionPending
    (functionPrevailing.apply functionTarget)
    (functionPrevailing.apply
      (.fn (.var functionResultSupply.nextTy)
        (.var (functionResultSupply.nextTy + 1)))) solverDelta
  solverPrevailing : prevailing = Subst.seq solverDelta functionPrevailing
  floorCaps : provenanceFloor.nextCap ≤ functionResultSupply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ functionResultSupply.nextTy + 2
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst prevailing)
    (rawContext.applySubst prevailing)
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst prevailing)
    (rawContext.applySubst prevailing)
  protectedOld : ProtectedOldFreeAt provenanceFloor
    (provenanceContext.applySubst prevailing) frontier
  suffix : Subst
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext rawContext
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst prevailing) provenanceFrames prevailing
  retainedSuffix : Subst
  retainedSuffix_eq : retainedSuffix = Subst.seq suffix functionSuffix
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst prevailing) retainedSuffix provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (retainedSuffix.apply algorithm, selected) ∈ frontier
  generativity : GenerativitySurfaceFrameAt generativityObligations prevailing
  generativityContexts : GenerativitySurfaceContextsAt generativityObligations
    prevailing (rawContext.applySubst prevailing)
  generativityValid : GenerativitySurfaceValid
    { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
    rawContext generativityObligations
  childGenerativity : GenerativitySurfaceFrameAt
    (GenerativitySurfaceObligation.current
        { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
        rawContext ::
      GenerativitySurfaceObligations.protectToken
        (.var functionResultSupply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (functionResultSupply.nextTy + 1))
          generativityObligations)) prevailing
  childGenerativityContexts : GenerativitySurfaceContextsAt
    (GenerativitySurfaceObligation.current
        { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
        rawContext ::
      GenerativitySurfaceObligations.protectToken
        (.var functionResultSupply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (functionResultSupply.nextTy + 1))
          generativityObligations)) prevailing (rawContext.applySubst prevailing)
  childGenerativityValid : GenerativitySurfaceValid
    { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
    rawContext
    (GenerativitySurfaceObligation.current
        { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
        rawContext ::
      GenerativitySurfaceObligations.protectToken
        (.var functionResultSupply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (functionResultSupply.nextTy + 1))
          generativityObligations))
  childCurrentObligation : GenerativitySurfaceObligation.current
      { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
      rawContext ∈
    (GenerativitySurfaceObligation.current
        { functionResultSupply with nextTy := functionResultSupply.nextTy + 2 }
        rawContext ::
      GenerativitySurfaceObligations.protectToken
        (.var functionResultSupply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (functionResultSupply.nextTy + 1))
          generativityObligations))
  protectedCovered : ProtectedFreeCovered
    (rawContext.applySubst prevailing) frames prevailing
  contextSuffix : ProtectedContextsSuffix rawContext frames
  domainMember : (prevailing.apply (.var functionResultSupply.nextTy),
    domain) ∈ frontier
  codomainMember :
    (prevailing.apply (.var (functionResultSupply.nextTy + 1)), codomain) ∈
      frontier
  prevailing_eq : prevailing = Subst.seq suffix functionPrevailing
  frontierRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ functionFrontier →
      (suffix.apply algorithm, selected) ∈ frontier
  pairedTransport : GenerativityPairedStateAt generativityObligations
      functionPrevailing functionFrontier →
    GenerativityPairedStateAt generativityObligations prevailing frontier
  frontierNormalizationTransport :
      (∀ pair ∈ functionFrontier,
        functionPrevailing.apply pair.1 = pair.1) →
      ∀ pair ∈ frontier, prevailing.apply pair.1 = pair.1

def WAppArgumentPrepared.supply
    {signature : FrozenSig} {rawContext : Context}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)}
    {functionResultSupply : InferenceBase.FreshSupply}
    {functionPrevailing : Subst}
    {functionSuffix : Subst}
    {functionFrontier : List (Ty × STy)}
    {functionPending : List PendingLetCut}
    (_ : WAppArgumentPrepared signature rawContext selectedContext domain
      codomain provenanceFloor provenanceContext provenanceFrames
      provenanceFrontier generativityObligations frames
      functionResultSupply
      functionPrevailing functionSuffix functionFrontier functionPending) :
      InferenceBase.FreshSupply :=
  { functionResultSupply with
    nextTy := functionResultSupply.nextTy + 2 }

/-- Perform the first application cut and expose exactly the state required
by the recursive argument call.  The one-sort post is extended at the two
fresh variables, then retained unchanged by exact-MGU absorption. -/
theorem WNormalizedCompleteWitness.prepareAppArgument
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {initial : Subst} {rawContext : Context} {function : Expr}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (functionResult : WNormalizedCompleteWitness signature supply initial
      rawContext function selectedContext (.fn domain codomain)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames
      inputFrontier inputPending)
    (active : (rawContext, selectedContext) ∈ frames)
    (signatureClosed : signature.SchemesClosed) :
    ∃ prepared : WAppArgumentPrepared signature rawContext selectedContext
        domain codomain provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations frames
        functionResult.complete.successor
        functionResult.complete.prevailing'
        functionResult.complete.suffix
        functionResult.complete.frontier functionResult.complete.pending,
      DemandAlignTypesWithLedger [] functionResult.complete.prevailing'
        functionResult.complete.rawTarget
        (.fn (.var functionResult.complete.successor.nextTy)
          (.var (functionResult.complete.successor.nextTy + 1)))
        prepared.prevailing ∧
      prepared.functionTarget = functionResult.complete.rawTarget := by
  let result := functionResult.complete
  let q₁ := result.successor
  let residual' := SSubst.extendAppTargets functionResult.residual q₁
    domain codomain
  have oldState := result.retiredState
  rw [functionResult.post_eq] at oldState
  have prepared0 : WRetiredStableFrameAt signature
      { q₁ with nextTy := q₁.nextTy + 2 }
      (SSubst.paired residual') result.prevailing' frames
      ((.var q₁.nextTy, domain) ::
        (.var (q₁.nextTy + 1), codomain) :: result.frontier)
      result.pending := by
    rw [SSubst.paired_extendAppTargets]
    exact oldState.protectAppTargets domain codomain
  have domainMember0 : (Ty.var q₁.nextTy, domain) ∈
      ((.var q₁.nextTy, domain) ::
        (.var (q₁.nextTy + 1), codomain) :: result.frontier) :=
    List.mem_cons_self
  have codomainMember0 : (Ty.var (q₁.nextTy + 1), codomain) ∈
      ((.var q₁.nextTy, domain) ::
        (.var (q₁.nextTy + 1), codomain) :: result.frontier) :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have prepared := prepared0.protectFnOfMembers domainMember0 codomainMember0
  have algorithmBounded : functionResult.algorithmTarget.emb.BoundedBy q₁ := by
    rw [← functionResult.target.normalized_eq]
    exact result.frame.frontierBounded _ result.targetMember
  have algorithmBelow : TyVarsBelow q₁.nextTy
      functionResult.algorithmTarget.ftv := by
    intro varId member
    exact algorithmBounded.targets varId (by
      simpa only [STy.emb_ftv] using member)
  have leftSelected : functionResult.algorithmTarget.applySubst residual' =
      .fn domain codomain := by
    rw [STy.applySubst_extendAppTargets_eq _ _ _ _ _ algorithmBelow]
    exact functionResult.target.residual_eq
  have domainFixed : result.prevailing'.apply (.var q₁.nextTy) =
      .var q₁.nextTy :=
    DM.Subst.BoundedBy.apply_freshTarget result.prevailingBounded
  have codomainFixed : result.prevailing'.apply (.var (q₁.nextTy + 1)) =
      .var (q₁.nextTy + 1) :=
    DM.Subst.BoundedBy.apply_targetAbove result.prevailingBounded
      (Nat.le_succ _)
  have skeletonFixed : result.prevailing'.apply
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) =
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) := by
    simp only [Subst.apply_fn, domainFixed, codomainFixed]
  have leftMember :
      (result.prevailing'.apply result.rawTarget, .fn domain codomain) ∈
        ((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
            .fn domain codomain) ::
          (.var q₁.nextTy, domain) ::
          (.var (q₁.nextTy + 1), codomain) :: result.frontier) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ result.targetMember))
  have rightMember :
      (result.prevailing'.apply
          (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))),
        .fn domain codomain) ∈
        ((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
            .fn domain codomain) ::
          (.var q₁.nextTy, domain) ::
          (.var (q₁.nextTy + 1), codomain) :: result.frontier) := by
    rw [skeletonFixed]
    exact List.mem_cons_self
  obtain ⟨delta, solverCut, factor, aligned, moved⟩ :=
    w_alignNormalizedRetired
      (algorithmLeft := functionResult.algorithmTarget)
      (algorithmRight := .fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))
      prepared signatureClosed functionResult.target.normalized_eq
      (by simpa [STy.emb] using skeletonFixed)
      leftSelected (by
        simp [residual', STy.applySubst])
      leftMember rightMember result.pendingCapFree
  let prevailing₂ := Subst.seq delta result.prevailing'
  have context₂ : ErasedDMContextView residual' selectedContext
      (rawContext.applySubst prevailing₂) := by
    exact ⟨moved.stable.frame.contexts active⟩
  have scope₀ : ResidualContextScope residual'
      (rawContext.applySubst result.prevailing') selectedContext :=
    ResidualContextScope.extendAppTargets functionResult.scope
      (result.frame.contextsBounded active) domain codomain
  have scope₂ : ResidualContextScope residual'
      (rawContext.applySubst prevailing₂) selectedContext := by
    rw [Context.applySubst_seq]
    exact ResidualContextScope.applyAbsorbed scope₀ factor
  have domainMapped :
      (delta.apply (.var q₁.nextTy), domain) ∈
        (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
              .fn domain codomain) ::
            (.var q₁.nextTy, domain) ::
            (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
          fun pair => (delta.apply pair.1, pair.2)) :=
    List.mem_map.mpr ⟨(.var q₁.nextTy, domain),
      List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  have domainMember :
      (prevailing₂.apply (.var q₁.nextTy), domain) ∈
        (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
              .fn domain codomain) ::
            (.var q₁.nextTy, domain) ::
            (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
          fun pair => (delta.apply pair.1, pair.2)) := by
    simp [prevailing₂, Subst.seq_apply, domainFixed] at domainMapped ⊢
  have extendedAdmissible : AdmissiblePost [] (SSubst.paired residual') := by
    rw [SSubst.paired_extendAppTargets]
    have originalAdmissible := result.postAdmissible
    rw [functionResult.post_eq] at originalAdmissible
    exact DM.AdmissiblePost.extendAppTargets originalAdmissible
  have prevailingBounded₂ : prevailing₂.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } := by
    have leftBounded := (result.frame.frontierBounded _ result.targetMember).mono
      (SupplyExtends.bumpTy q₁ 2)
    have rightBounded :
        (result.prevailing'.apply
          (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))).BoundedBy
          { q₁ with nextTy := q₁.nextTy + 2 } := by
      rw [skeletonFixed]
      exact Ty.BoundedBy.fnOf (Ty.BoundedBy.varOf (by simp))
        (Ty.BoundedBy.varOf (by simp))
    exact (solverCut.exact.exact.boundedBy leftBounded rightBounded).seq
      (result.prevailingBounded.mono (SupplyExtends.bumpTy q₁ 2))
  have prevailingIdempotent₂ : prevailing₂.Idempotent :=
    DemandTypingIdempotence.DemandAlignTypes.idempotent aligned
      result.prevailingIdempotent
  have pendingCapFree₂ : PendingLetsCapFree prevailing₂ result.pending :=
    result.pendingCapFree.applyLetStableExactPairedCut solverCut
  have floorLeQ : provenanceFloor.nextTy ≤ q₁.nextTy :=
    Nat.le_trans functionResult.floorTargets
      functionResult.complete.derived.supplyExtends.2
  have freshDomainOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing') (.var q₁.nextTy) :=
    OldFreeInContextAt.var provenanceFloor _ _ floorLeQ
  have freshCodomainOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (.var (q₁.nextTy + 1)) :=
    OldFreeInContextAt.var provenanceFloor _ _
      (Nat.le_trans floorLeQ (Nat.le_succ _))
  have skeletonOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)) ) :=
    OldFreeInContextAt.fn freshDomainOld freshCodomainOld
  have oldFrontierActive : ProtectedOldFreeAt provenanceFloor
      (rawContext.applySubst result.prevailing') result.frontier :=
    functionResult.protectedOld.contextMono
      functionResult.provenanceIncluded.caps
      functionResult.provenanceIncluded.targets
  have freshDomainActive := freshDomainOld.contextMono
    functionResult.provenanceIncluded.caps
    functionResult.provenanceIncluded.targets
  have freshCodomainActive := freshCodomainOld.contextMono
    functionResult.provenanceIncluded.caps
    functionResult.provenanceIncluded.targets
  have skeletonActive := skeletonOld.contextMono
    functionResult.provenanceIncluded.caps
    functionResult.provenanceIncluded.targets
  have expandedOld : ProtectedOldFreeAt provenanceFloor
      (rawContext.applySubst result.prevailing')
      ((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
          .fn domain codomain) ::
        (.var q₁.nextTy, domain) ::
        (.var (q₁.nextTy + 1), codomain) :: result.frontier) :=
    (oldFrontierActive.cons freshCodomainActive).cons freshDomainActive
      |>.cons skeletonActive
  have skeletonAppliedOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (result.prevailing'.apply
        (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) := by
    rw [skeletonFixed]
    exact skeletonOld
  have functionOuterOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst result.prevailing')
      (result.prevailing'.apply result.rawTarget) :=
    functionResult.protectedOld _ result.targetMember
  obtain ⟨contextOld₂, protectedOld₂⟩ :=
    functionResult.contextOld.applyOriginSafeExactPairedMGU_and_protected
      (delta := delta) expandedOld functionOuterOld skeletonAppliedOld
      solverCut.exact
      solverCut.leftCapFree solverCut.rightCapFree
  have included₂ :=
    functionResult.provenanceIncluded.applyOriginSafeExactPairedMGU
      solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
  have retained₂ :=
    functionResult.retainedOuter.applyOriginSafeExactPairedMGU_of_endpointsOld
      functionOuterOld skeletonAppliedOld solverCut.exact
      solverCut.leftCapFree solverCut.rightCapFree
  have contextOld₂' : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing₂)
      (rawContext.applySubst prevailing₂) := by
    simpa only [prevailing₂, Context.applySubst_seq] using contextOld₂
  have protectedOld₂' : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing₂)
      (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
            .fn domain codomain) ::
          (.var q₁.nextTy, domain) ::
          (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
        fun pair => (delta.apply pair.1, pair.2)) := by
    simpa only [prevailing₂, Context.applySubst_seq] using protectedOld₂
  have included₂' : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing₂)
      (rawContext.applySubst prevailing₂) := by
    simpa only [prevailing₂, Context.applySubst_seq] using included₂
  have retained₂' : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing₂)
      (Subst.seq delta result.suffix) provenanceFrontier := by
    simpa only [prevailing₂, Context.applySubst_seq] using retained₂
  have protectedScopes₀ : ProtectedResidualScopes residual'
      result.prevailing' frames := by
    intro pair member
    exact ResidualContextScope.extendAppTargets
      (functionResult.protectedScopes pair member)
      (result.frame.contextsBounded member) domain codomain
  have protectedScopes₂ : ProtectedResidualScopes residual' prevailing₂
      frames := by
    simpa only [prevailing₂] using protectedScopes₀.applyAbsorbed factor
  have obligationBelow : ∀ obligation ∈ generativityObligations,
      obligation.floor.nextTy ≤ q₁.nextTy := by
    intro obligation member
    exact Nat.le_trans
      (functionResult.generativityValid obligation member).1.2
      result.derived.supplyExtends.2
  have functionGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    exact functionResult.targetGenerative obligation member
  have skeletonGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply
          (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) := by
    intro obligation member
    rw [skeletonFixed]
    exact OldFreeInContextAt.fn
      (OldFreeInContextAt.var obligation.floor _ _
        (obligationBelow obligation member))
      (OldFreeInContextAt.var obligation.floor _ _
        (Nat.le_trans (obligationBelow obligation member) (Nat.le_succ _)))
  have generativity₂ : GenerativitySurfaceFrameAt generativityObligations
      prevailing₂ := by
    simpa only [prevailing₂] using
      functionResult.generativity.applyOriginSafeExactPairedMGU
        functionGenerative skeletonGenerative solverCut.exact
        solverCut.leftCapFree solverCut.rightCapFree
  have generativityContexts₂ : GenerativitySurfaceContextsAt
      generativityObligations prevailing₂
      (rawContext.applySubst prevailing₂) := by
    simpa only [prevailing₂, Context.applySubst_seq] using
      functionResult.generativityContexts.applyOriginSafeExactPairedMGU
        functionGenerative skeletonGenerative solverCut.exact
        solverCut.leftCapFree solverCut.rightCapFree
  have generativityValid₂ : GenerativitySurfaceValid
      { q₁ with nextTy := q₁.nextTy + 2 } rawContext
      generativityObligations :=
    functionResult.generativityValid.monoSupply
      (result.derived.supplyExtends.trans (SupplyExtends.bumpTy q₁ 2))
  let protectedObligations := GenerativitySurfaceObligations.protectToken
    (.var q₁.nextTy)
    (GenerativitySurfaceObligations.protectToken
      (.var (q₁.nextTy + 1)) generativityObligations)
  have protectedFunctionOld : ∀ obligation ∈ protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
    rcases List.mem_map.mp ‹codomainProtected ∈ _› with ⟨old, oldMember, rfl⟩
    exact functionGenerative old oldMember
  have protectedSkeletonOld : ∀ obligation ∈ protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply
          (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) := by
    intro obligation member
    rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
    rcases List.mem_map.mp ‹codomainProtected ∈ _› with ⟨old, oldMember, rfl⟩
    exact skeletonGenerative old oldMember
  have protectedGenerativity₀ : GenerativitySurfaceFrameAt
      protectedObligations result.prevailing' := by
    have codomainGenerative : ∀ obligation ∈ generativityObligations,
        OldFreeInContextAt obligation.floor
          (obligation.owner.applySubst result.prevailing')
          (result.prevailing'.apply (.var (q₁.nextTy + 1))) := by
      intro obligation member
      rw [codomainFixed]
      exact OldFreeInContextAt.var obligation.floor _ _
        (Nat.le_trans (obligationBelow obligation member) (Nat.le_succ _))
    have domainGenerative : ∀ obligation ∈
        GenerativitySurfaceObligations.protectToken
          (.var (q₁.nextTy + 1)) generativityObligations,
        OldFreeInContextAt obligation.floor
          (obligation.owner.applySubst result.prevailing')
          (result.prevailing'.apply (.var q₁.nextTy)) := by
      intro obligation member
      rcases List.mem_map.mp member with ⟨old, oldMember, rfl⟩
      rw [domainFixed]
      exact OldFreeInContextAt.var old.floor _ _
        (obligationBelow old oldMember)
    exact (functionResult.generativity.protectToken codomainGenerative)
      |>.protectToken domainGenerative
  have protectedGenerativity₂ : GenerativitySurfaceFrameAt
      protectedObligations prevailing₂ := by
    simpa only [prevailing₂] using
      protectedGenerativity₀.applyOriginSafeExactPairedMGU
        protectedFunctionOld protectedSkeletonOld solverCut.exact
        solverCut.leftCapFree solverCut.rightCapFree
  have protectedContexts₂ : GenerativitySurfaceContextsAt
      protectedObligations prevailing₂ (rawContext.applySubst prevailing₂) := by
    simpa only [prevailing₂, Context.applySubst_seq] using
      (functionResult.generativityContexts.protectToken.protectToken)
        |>.applyOriginSafeExactPairedMGU protectedFunctionOld
          protectedSkeletonOld solverCut.exact solverCut.leftCapFree
          solverCut.rightCapFree
  have childGenerativity := protectedGenerativity₂.registerEmpty
    { q₁ with nextTy := q₁.nextTy + 2 } rawContext
  have childGenerativityContexts := protectedContexts₂.registerCurrent
    { q₁ with nextTy := q₁.nextTy + 2 }
  have childGenerativityValid : GenerativitySurfaceValid
      { q₁ with nextTy := q₁.nextTy + 2 } rawContext
      (GenerativitySurfaceObligation.current
          { q₁ with nextTy := q₁.nextTy + 2 } rawContext ::
        protectedObligations) :=
    (functionResult.generativityValid.protectToken.protectToken
      |>.monoSupply
        (result.derived.supplyExtends.trans (SupplyExtends.bumpTy q₁ 2)))
      |>.registerCurrent
  have provenanceRetains₂ : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        ((Subst.seq delta result.suffix).apply algorithm, selected) ∈
          (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
                .fn domain codomain) ::
              (.var q₁.nextTy, domain) ::
              (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
            fun pair => (delta.apply pair.1, pair.2)) := by
    intro algorithm selected member
    apply List.mem_map.mpr
    exact ⟨(result.suffix.apply algorithm, selected),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (functionResult.provenanceRetains algorithm selected member))), by
        simp only [Subst.seq_apply]⟩
  let preparedResult : WAppArgumentPrepared signature rawContext
      selectedContext domain codomain provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames q₁
      result.prevailing' result.suffix result.frontier result.pending :=
    { prevailing := prevailing₂
      residual := residual'
      frontier := _
      state := moved
      context := context₂
      scope := scope₂
      protectedScopes := protectedScopes₂
      postAdmissible := extendedAdmissible
      prevailingBounded := prevailingBounded₂
      prevailingIdempotent := prevailingIdempotent₂
      pendingCapFree := pendingCapFree₂
      functionTarget := result.rawTarget
      solverDelta := delta
      solverCut := solverCut
      solverPrevailing := rfl
      floorCaps := Nat.le_trans functionResult.floorCaps
        result.derived.supplyExtends.1
      floorTargets := Nat.le_trans
        (Nat.le_trans functionResult.floorTargets
          result.derived.supplyExtends.2)
        (Nat.le_add_right _ _)
      contextOld := contextOld₂'
      provenanceIncluded := included₂'
      protectedOld := protectedOld₂'
      suffix := delta
      contextProvenanceSuffix := functionResult.contextProvenanceSuffix
      provenanceSuffix := functionResult.provenanceSuffix
      provenanceCovered := functionResult.provenanceSuffix.toProtectedFreeCovered
        prevailing₂
      retainedSuffix := Subst.seq delta result.suffix
      retainedSuffix_eq := rfl
      retainedOuter := retained₂'
      provenanceRetains := provenanceRetains₂
      generativity := generativity₂
      generativityContexts := generativityContexts₂
      generativityValid := generativityValid₂
      childGenerativity := childGenerativity
      childGenerativityContexts := childGenerativityContexts
      childGenerativityValid := childGenerativityValid
      childCurrentObligation := List.mem_cons_self
      protectedCovered := functionResult.contextSuffix.toProtectedFreeCovered
        prevailing₂
      contextSuffix := functionResult.contextSuffix
      domainMember := domainMember
      codomainMember := by
        have mapped :
            (delta.apply (.var (q₁.nextTy + 1)), codomain) ∈
              (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
                    .fn domain codomain) ::
                  (.var q₁.nextTy, domain) ::
                  (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
                fun pair => (delta.apply pair.1, pair.2)) :=
          List.mem_map.mpr ⟨(.var (q₁.nextTy + 1), codomain),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
            rfl⟩
        simp [prevailing₂, Subst.seq_apply, codomainFixed] at mapped ⊢
      prevailing_eq := rfl
      frontierRetains := by
        intro algorithm selected member
        apply List.mem_map.mpr
        exact ⟨(algorithm, selected),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ member)), rfl⟩
      pairedTransport := by
        intro paired
        have expandedMembers : GenerativitySurfaceMembersAt
            generativityObligations result.prevailing'
            ((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
                .fn domain codomain) ::
              (.var q₁.nextTy, domain) ::
              (.var (q₁.nextTy + 1), codomain) :: result.frontier) := by
          intro obligation obligationMember pair pairMember
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (paired.members obligation obligationMember pair pairMember)))
        have movedPaired : GenerativityPairedStateAt
            generativityObligations prevailing₂
            (((.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)),
                  .fn domain codomain) ::
                (.var q₁.nextTy, domain) ::
                (.var (q₁.nextTy + 1), codomain) :: result.frontier).map
              fun pair => (delta.apply pair.1, pair.2)) :=
          (show GenerativityPairedStateAt generativityObligations
              result.prevailing' _ from ⟨paired.retained, expandedMembers⟩)
            |>.applyOriginSafeExactPairedMGU functionGenerative
              skeletonGenerative solverCut.exact solverCut.leftCapFree
              solverCut.rightCapFree
        exact movedPaired
      frontierNormalizationTransport := by
        intro oldNormalized pair member
        rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
        have sourceFixed : result.prevailing'.apply source.1 = source.1 := by
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact skeletonFixed
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact domainFixed
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact codomainFixed
          · exact oldNormalized source sourceMember
        calc
          prevailing₂.apply (delta.apply source.1) =
              prevailing₂.apply (prevailing₂.apply source.1) := by
                simp only [prevailing₂, Subst.seq_apply, sourceFixed]
          _ = prevailing₂.apply source.1 := prevailingIdempotent₂ source.1
          _ = delta.apply source.1 := by
            simp only [prevailing₂, Subst.seq_apply, sourceFixed] }
  have ordinaryClass : alignPairClass
      (result.prevailing'.apply result.rawTarget)
      (result.prevailing'.apply
        (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) = .ordinary := by
    have leftEquation : (SSubst.paired residual').apply
        (result.prevailing'.apply result.rawTarget) =
          (STy.fn domain codomain).emb := by
      rw [functionResult.target.normalized_eq,
        SSubst.paired_apply_emb, leftSelected]
    have rightEquation : (SSubst.paired residual').apply
        (result.prevailing'.apply
          (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) =
          (STy.fn domain codomain).emb := by
      rw [skeletonFixed]
      change (SSubst.paired residual').apply
        (STy.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))).emb = _
      rw [SSubst.paired_apply_emb]
      simp [residual', STy.applySubst]
    exact alignPairClass_ordinary_of_realized_emb leftEquation rightEquation
  exact ⟨preparedResult,
    DemandAlignTypesWithLedger.ordinary ordinaryClass solverCut.exact, rfl⟩

/-- The state after checking the application argument against the retained
fresh domain.  It contains every semantic and chronological fact needed by
the final `DemandSynth.app` packaging step. -/
structure WAppFinished
    (signature : FrozenSig) (rawContext : Context)
    (selectedContext : SCtx) (codomain : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    {functionSupply : InferenceBase.FreshSupply}
    {functionPrevailing : Subst} {functionFrontier : List (Ty × STy)}
    {functionSuffix : Subst}
    {functionPending : List PendingLetCut}
    {domain : STy}
    (prepared : WAppArgumentPrepared signature rawContext selectedContext
      domain codomain provenanceFloor provenanceContext provenanceFrames
      provenanceFrontier generativityObligations frames
      functionSupply
      functionPrevailing functionSuffix
      functionFrontier functionPending)
    {argument : Expr}
    (argumentResult : WNormalizedCompleteWitness signature prepared.supply
      prepared.prevailing rawContext argument selectedContext domain
      provenanceFloor provenanceContext provenanceFrames
      (provenanceFrontier.map fun pair =>
        (prepared.retainedSuffix.apply pair.1, pair.2))
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        GenerativitySurfaceObligations.protectToken
          (.var functionSupply.nextTy)
          (GenerativitySurfaceObligations.protectToken
            (.var (functionSupply.nextTy + 1)) generativityObligations)) frames
      prepared.frontier functionPending) : Type where
  delta : Subst
  prevailing : Subst := Subst.seq delta argumentResult.complete.prevailing'
  frontier : List (Ty × STy) :=
    argumentResult.complete.frontier.map
      (fun pair => (delta.apply pair.1, pair.2))
  prevailing_eq : prevailing =
    Subst.seq delta argumentResult.complete.prevailing'
  frontier_eq : frontier = argumentResult.complete.frontier.map
    (fun pair => (delta.apply pair.1, pair.2))
  solverCut : LetStableExactPairedCut signature
    argumentResult.complete.prevailing' argumentResult.complete.pending
    (argumentResult.complete.prevailing'.apply
      argumentResult.complete.rawTarget)
    (argumentResult.complete.prevailing'.apply
      (.var functionSupply.nextTy)) delta
  factor : SSubst.paired argumentResult.residual =
    Subst.seq (SSubst.paired argumentResult.residual) delta
  aligned : DemandAlignWithLedger [] argumentResult.complete.prevailing'
    argumentResult.complete.rawTarget (.var functionSupply.nextTy) prevailing
  state : WRetiredStableFrameAt signature argumentResult.complete.successor
    (SSubst.paired argumentResult.residual) prevailing frames frontier
    argumentResult.complete.pending
  context : ErasedDMContextView argumentResult.residual selectedContext
    (rawContext.applySubst prevailing)
  scope : ResidualContextScope argumentResult.residual
    (rawContext.applySubst prevailing) selectedContext
  algorithmCodomain : STy
  target : NormalizedDMTargetView argumentResult.residual algorithmCodomain
    codomain (prevailing.apply (.var (functionSupply.nextTy + 1)))
  targetMember :
    (prevailing.apply (.var (functionSupply.nextTy + 1)), codomain) ∈ frontier
  pendingCapFree : PendingLetsCapFree prevailing argumentResult.complete.pending
  prevailingBounded : prevailing.BoundedBy argumentResult.complete.successor
  prevailingIdempotent : prevailing.Idempotent
  protectedScopes : ProtectedResidualScopes argumentResult.residual prevailing
    frames
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst prevailing)
    (rawContext.applySubst prevailing)
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst prevailing)
    (rawContext.applySubst prevailing)
  protectedOld : ProtectedOldFreeAt provenanceFloor
    (provenanceContext.applySubst prevailing) frontier
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst prevailing)
    (Subst.seq delta
      (Subst.seq argumentResult.complete.suffix prepared.retainedSuffix))
    provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      ((Subst.seq delta
        (Subst.seq argumentResult.complete.suffix prepared.retainedSuffix)).apply
        algorithm,
        selected) ∈ frontier
  generativity : GenerativitySurfaceFrameAt generativityObligations prevailing
  generativityContexts : GenerativitySurfaceContextsAt generativityObligations
    prevailing (rawContext.applySubst prevailing)
  targetGenerative : ∀ obligation ∈ generativityObligations,
    OldFreeInContextAt obligation.floor
      (obligation.owner.applySubst prevailing)
      (prevailing.apply (.var (functionSupply.nextTy + 1)))
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst prevailing) provenanceFrames prevailing
  protectedCovered : ProtectedFreeCovered
    (rawContext.applySubst prevailing) frames prevailing

/-- Discharge the second application cut after the recursive argument
traversal, retaining the one-sort residual by absorption. -/
theorem WNormalizedCompleteWitness.finishAppArgument
    {signature : FrozenSig} {rawContext : Context}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)}
    {functionSupply : InferenceBase.FreshSupply}
    {functionPrevailing : Subst} {functionFrontier : List (Ty × STy)}
    {functionSuffix : Subst}
    {functionPending : List PendingLetCut}
    (prepared : WAppArgumentPrepared signature rawContext selectedContext
      domain codomain provenanceFloor provenanceContext provenanceFrames
      provenanceFrontier generativityObligations frames
      functionSupply
      functionPrevailing functionSuffix
      functionFrontier functionPending)
    {argument : Expr}
    (argumentResult : WNormalizedCompleteWitness signature prepared.supply
      prepared.prevailing rawContext argument selectedContext domain
      provenanceFloor provenanceContext provenanceFrames
      (provenanceFrontier.map fun pair =>
        (prepared.retainedSuffix.apply pair.1, pair.2))
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        GenerativitySurfaceObligations.protectToken
          (.var functionSupply.nextTy)
          (GenerativitySurfaceObligations.protectToken
            (.var (functionSupply.nextTy + 1)) generativityObligations)) frames
      prepared.frontier functionPending)
    (active : (rawContext, selectedContext) ∈ frames)
    (signatureClosed : signature.SchemesClosed) :
    Nonempty (WAppFinished signature rawContext selectedContext codomain
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames
      prepared
      argumentResult) := by
  let result := argumentResult.complete
  have domainRetained :
      (result.prevailing'.apply (.var functionSupply.nextTy), domain) ∈
        result.frontier := by
    have retained := result.frontierRetains _ _ prepared.domainMember
    simpa only [result.prevailing_eq, Subst.seq_apply] using retained
  have domainEquation : (SSubst.paired argumentResult.residual).apply
      (result.prevailing'.apply (.var functionSupply.nextTy)) = domain.emb := by
    rw [← argumentResult.post_eq]
    exact result.frame.types domainRetained
  obtain ⟨algorithmDomain, domainView⟩ :=
    NormalizedDMTargetView.ofPairedEquation domainEquation
  have argumentState := result.retiredState
  rw [argumentResult.post_eq] at argumentState
  obtain ⟨delta, solverCut, factor, alignedRaw, moved⟩ :=
    w_checkNormalizedRetired argumentState signatureClosed
      argumentResult.target.normalized_eq domainView.normalized_eq
      argumentResult.target.residual_eq domainView.residual_eq
      result.targetMember domainRetained result.pendingCapFree
  let prevailing := Subst.seq delta result.prevailing'
  have codomainRetained :
      (result.prevailing'.apply (.var (functionSupply.nextTy + 1)), codomain) ∈
        result.frontier := by
    have retained := result.frontierRetains _ _ prepared.codomainMember
    simpa only [result.prevailing_eq, Subst.seq_apply] using retained
  have targetMember :
      (prevailing.apply (.var (functionSupply.nextTy + 1)), codomain) ∈
        result.frontier.map (fun pair => (delta.apply pair.1, pair.2)) := by
    have mapped :
        (delta.apply
            (result.prevailing'.apply (.var (functionSupply.nextTy + 1))),
          codomain) ∈
          result.frontier.map (fun pair => (delta.apply pair.1, pair.2)) :=
      List.mem_map.mpr
        ⟨(result.prevailing'.apply (.var (functionSupply.nextTy + 1)),
            codomain), codomainRetained, rfl⟩
    simpa only [prevailing, Subst.seq_apply] using mapped
  have targetEquation : (SSubst.paired argumentResult.residual).apply
      (prevailing.apply (.var (functionSupply.nextTy + 1))) = codomain.emb :=
    moved.stable.frame.types targetMember
  obtain ⟨algorithmCodomain, targetView⟩ :=
    NormalizedDMTargetView.ofPairedEquation targetEquation
  have context : ErasedDMContextView argumentResult.residual selectedContext
      (rawContext.applySubst prevailing) :=
    ⟨moved.stable.frame.contexts active⟩
  have scope : ResidualContextScope argumentResult.residual
      (rawContext.applySubst prevailing) selectedContext := by
    rw [Context.applySubst_seq]
    exact ResidualContextScope.applyAbsorbed argumentResult.scope factor
  have pendingCapFree : PendingLetsCapFree prevailing result.pending :=
    result.pendingCapFree.applyLetStableExactPairedCut solverCut
  have prevailingBounded : prevailing.BoundedBy result.successor := by
    have rawBounded := result.frame.frontierBounded _ result.targetMember
    have domainBounded := result.frame.frontierBounded _ domainRetained
    exact (solverCut.exact.exact.boundedBy rawBounded domainBounded).seq
      result.prevailingBounded
  have prevailingIdempotent : prevailing.Idempotent :=
    DemandTypingIdempotence.DemandAlign.idempotent alignedRaw
      result.prevailingIdempotent
  have argumentOld : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    exact argumentResult.targetGenerative
      ((obligation.protectToken (.var (functionSupply.nextTy + 1)))
        |>.protectToken (.var functionSupply.nextTy))
      (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨obligation.protectToken (.var (functionSupply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩))
  have domainOld : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply (.var functionSupply.nextTy)) := by
    intro obligation member
    exact argumentResult.generativity
      ((obligation.protectToken (.var (functionSupply.nextTy + 1)))
        |>.protectToken (.var functionSupply.nextTy))
      (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨obligation.protectToken (.var (functionSupply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩))
      (.var functionSupply.nextTy) (by simp [GenerativitySurfaceObligation.protectToken])
  let protectedObligations := GenerativitySurfaceObligations.protectToken
    (.var functionSupply.nextTy)
    (GenerativitySurfaceObligations.protectToken
      (.var (functionSupply.nextTy + 1)) generativityObligations)
  have generativityProtected : GenerativitySurfaceFrameAt protectedObligations
      result.prevailing' :=
    argumentResult.generativity.of_obligations_subset (by
      intro obligation member
      exact List.mem_cons_of_mem _ member)
  have protectedArgumentOld : ∀ obligation ∈ protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    exact argumentResult.targetGenerative obligation
      (List.mem_cons_of_mem _ member)
  have protectedDomainOld : ∀ obligation ∈ protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply (.var functionSupply.nextTy)) := by
    intro obligation member
    exact argumentResult.generativity obligation
      (List.mem_cons_of_mem _ member)
      (.var functionSupply.nextTy) (by
        rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
        simp [GenerativitySurfaceObligation.protectToken])
  have allArgumentOld : ∀ obligation ∈
      protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply result.rawTarget) := by
    intro obligation member
    exact argumentResult.targetGenerative obligation
      (List.mem_cons_of_mem _ member)
  have allDomainOld : ∀ obligation ∈
      protectedObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst result.prevailing')
        (result.prevailing'.apply (.var functionSupply.nextTy)) := by
    intro obligation member
    exact argumentResult.generativity obligation
      (List.mem_cons_of_mem _ member)
      (.var functionSupply.nextTy) (by
        rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
        simp [GenerativitySurfaceObligation.protectToken])
  have generativityAllFinal : GenerativitySurfaceFrameAt
      protectedObligations
      prevailing := by
    simpa only [prevailing] using
      (argumentResult.generativity.of_obligations_subset
        (fun obligation member => List.mem_cons_of_mem _ member))
        |>.applyOriginSafeExactPairedMGU
        allArgumentOld allDomainOld solverCut.exact solverCut.leftCapFree
        solverCut.rightCapFree
  have generativityProtectedFinal : GenerativitySurfaceFrameAt
      protectedObligations prevailing := by
    simpa only [prevailing] using
      generativityProtected.applyOriginSafeExactPairedMGU protectedArgumentOld
        protectedDomainOld solverCut.exact solverCut.leftCapFree
        solverCut.rightCapFree
  have generativity : GenerativitySurfaceFrameAt generativityObligations
      prevailing := by
    exact generativityProtectedFinal.unprotectToken.unprotectToken
  have contextsTail : GenerativitySurfaceContextsAt generativityObligations
      result.prevailing' (rawContext.applySubst result.prevailing') := by
    intro obligation member
    exact argumentResult.generativityContexts
      (GenerativitySurfaceObligation.protectToken (.var functionSupply.nextTy)
        (GenerativitySurfaceObligation.protectToken
          (.var (functionSupply.nextTy + 1)) obligation))
      (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨obligation.protectToken (.var (functionSupply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩))
  have generativityContexts : GenerativitySurfaceContextsAt
      generativityObligations prevailing (rawContext.applySubst prevailing) := by
    simpa only [prevailing, Context.applySubst_seq] using
      contextsTail.applyOriginSafeExactPairedMGU argumentOld domainOld
        solverCut.exact
        solverCut.leftCapFree solverCut.rightCapFree
  have contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) := by
    have leftOld := argumentResult.protectedOld _ result.targetMember
    have rightOld := argumentResult.protectedOld _ domainRetained
    have activeProtected := argumentResult.protectedOld.contextMono
      argumentResult.provenanceIncluded.caps
      argumentResult.provenanceIncluded.targets
    have transformed := argumentResult.contextOld
      |>.applyOriginSafeExactPairedMGU_and_protected activeProtected leftOld
        rightOld solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
    simpa only [prevailing, Context.applySubst_seq] using transformed.1
  have provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) :=
    prepared.contextProvenanceSuffix.toIncluded prevailing
  have protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (result.frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
    have leftOld := argumentResult.protectedOld _ result.targetMember
    have rightOld := argumentResult.protectedOld _ domainRetained
    have activeProtected := argumentResult.protectedOld.contextMono
      argumentResult.provenanceIncluded.caps
      argumentResult.provenanceIncluded.targets
    have transformed := argumentResult.contextOld
      |>.applyOriginSafeExactPairedMGU_and_protected
        activeProtected leftOld rightOld solverCut.exact
          solverCut.leftCapFree solverCut.rightCapFree
    simpa only [prevailing, Context.applySubst_seq] using transformed.2
  have retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (Subst.seq delta (Subst.seq result.suffix prepared.retainedSuffix))
      provenanceFrontier := by
    have leftOld := argumentResult.protectedOld _ result.targetMember
    have rightOld := argumentResult.protectedOld _ domainRetained
    have transformed := argumentResult.retainedOuter
      |>.applyOriginSafeExactPairedMGU_of_endpointsOld leftOld rightOld
        solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
    constructor
    · intro pair member varId free
      have mappedMember :
          (prepared.retainedSuffix.apply pair.1, pair.2) ∈
            provenanceFrontier.map (fun candidate =>
              (prepared.retainedSuffix.apply candidate.1, candidate.2)) :=
        List.mem_map.mpr ⟨pair, member, rfl⟩
      have retained := transformed.caps _ mappedMember varId (by
        simpa only [Subst.seq_apply] using free)
      simpa only [prevailing, Context.applySubst_seq] using retained
    · intro pair member varId free
      have mappedMember :
          (prepared.retainedSuffix.apply pair.1, pair.2) ∈
            provenanceFrontier.map (fun candidate =>
              (prepared.retainedSuffix.apply candidate.1, candidate.2)) :=
        List.mem_map.mpr ⟨pair, member, rfl⟩
      have retained := transformed.targets _ mappedMember varId (by
        simpa only [Subst.seq_apply] using free)
      simpa only [prevailing, Context.applySubst_seq] using retained
  have provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
      ((Subst.seq delta
        (Subst.seq result.suffix prepared.retainedSuffix)).apply algorithm,
        selected) ∈
        result.frontier.map (fun pair => (delta.apply pair.1, pair.2)) := by
    intro algorithm selected member
    apply List.mem_map.mpr
    have mappedMember :
        (prepared.retainedSuffix.apply algorithm, selected) ∈
          provenanceFrontier.map (fun pair =>
            (prepared.retainedSuffix.apply pair.1, pair.2)) :=
      List.mem_map.mpr ⟨(algorithm, selected), member, rfl⟩
    exact ⟨(result.suffix.apply (prepared.retainedSuffix.apply algorithm),
        selected),
      argumentResult.provenanceRetains _ _ mappedMember, by
        simp only [Subst.seq_apply]⟩
  have protectedScopes : ProtectedResidualScopes argumentResult.residual
      prevailing frames := by
    simpa only [prevailing] using
      ProtectedResidualScopes.applyAbsorbed argumentResult.protectedScopes factor
  have provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing) provenanceFrames prevailing :=
    prepared.provenanceSuffix.toProtectedFreeCovered prevailing
  have protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing) frames prevailing :=
    argumentResult.contextSuffix.toProtectedFreeCovered prevailing
  have targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing)
        (prevailing.apply (.var (functionSupply.nextTy + 1))) := by
    intro obligation member
    have output := generativityProtectedFinal
      (GenerativitySurfaceObligation.protectToken (.var functionSupply.nextTy)
        (GenerativitySurfaceObligation.protectToken
          (.var (functionSupply.nextTy + 1)) obligation))
      (List.mem_map.mpr
        ⟨obligation.protectToken (.var (functionSupply.nextTy + 1)),
          List.mem_map.mpr ⟨obligation, member, rfl⟩, rfl⟩)
      (.var (functionSupply.nextTy + 1)) (by
        simp [GenerativitySurfaceObligation.protectToken])
    exact output
  have rawEquation : (SSubst.paired argumentResult.residual).apply
      (result.prevailing'.apply result.rawTarget) = domain.emb := by
    rw [argumentResult.target.normalized_eq, SSubst.paired_apply_emb,
      argumentResult.target.residual_eq]
  have ordinaryPair := alignPairClass_ordinary_of_realized_emb
    rawEquation domainEquation
  have ordinaryDemand :=
    demandClass_ordinary_of_expected_realized_emb
      (raw := result.prevailing'.apply result.rawTarget) domainEquation
  let alignedTypes : DemandAlignTypesWithLedger [] result.prevailing'
      result.rawTarget (.var functionSupply.nextTy) prevailing :=
    DemandAlignTypesWithLedger.ordinary ordinaryPair solverCut.exact
  let aligned : DemandAlignWithLedger [] result.prevailing' result.rawTarget
      (.var functionSupply.nextTy) prevailing :=
    DemandAlignWithLedger.ordinary ordinaryDemand alignedTypes
  exact ⟨
    { delta := delta
      prevailing_eq := rfl
      frontier_eq := rfl
      solverCut := solverCut
      factor := factor
      aligned := aligned
      state := moved
      context := context
      scope := scope
      algorithmCodomain := algorithmCodomain
      target := targetView
      targetMember := targetMember
      pendingCapFree := pendingCapFree
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      protectedScopes := protectedScopes
      contextOld := contextOld
      provenanceIncluded := provenanceIncluded
      protectedOld := protectedOld
      retainedOuter := retainedOuter
      provenanceRetains := provenanceRetains
      generativity := generativity
      generativityContexts := generativityContexts
      targetGenerative := targetGenerative
      provenanceCovered := provenanceCovered
      protectedCovered := protectedCovered }⟩

/-- A normalized result whose existential final state is identified with the
concrete state just assembled by a constructor.  Paired continuation
invariants need these equalities; hiding them behind `Nonempty` would lose the
chronology needed to transport the final frontier. -/
structure WNormalizedCompleteAt
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (expression : Expr)
    (selectedContext : SCtx) (selectedTarget : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut)
    (finalPrevailing : Subst) (finalFrontier : List (Ty × STy))
    (finalRawTarget : Ty) (finalSuffix : Subst) where
  result : WNormalizedCompleteWitness signature supply prevailing rawContext
    expression selectedContext selectedTarget provenanceFloor
    provenanceContext provenanceFrames provenanceFrontier
    generativityObligations frames inputFrontier inputPending
  prevailing_eq : result.complete.prevailing' = finalPrevailing
  frontier_eq : result.complete.frontier = finalFrontier
  rawTarget_eq : result.complete.rawTarget = finalRawTarget
  suffix_eq : result.complete.suffix = finalSuffix

def WNormalizedCompleteAt.toResult (result : WNormalizedCompleteAt signature
    supply prevailing rawContext expression selectedContext selectedTarget
    provenanceFloor provenanceContext provenanceFrames provenanceFrontier
    generativityObligations frames inputFrontier inputPending finalPrevailing
    finalFrontier finalRawTarget finalSuffix) :
    WNormalizedCompleteResult signature supply prevailing rawContext expression
      selectedContext selectedTarget provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames
      inputFrontier inputPending :=
  ⟨result.result⟩

/-- Internal record constructor used by the higher-level chronological
constructor theorems below. -/
theorem w_normalized_complete_core
    {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' : Subst}
    {rawContext : Context} {expression : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {frames : List (Context × SCtx)}
    {provenanceFrontier inputFrontier frontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputPending pending : List PendingLetCut}
    {rawTarget : Ty} {post : Subst}
    {algorithmContext : SCtx} {algorithmTarget : STy}
    {residual : SSubst}
    (planned : PlannedSynth signature supply prevailing rawContext expression
      rawTarget successor prevailing')
    (state : WRetiredStableFrameAt signature successor post prevailing'
      frames frontier pending)
    (postEq : post = SSubst.paired residual)
    (context : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing'))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing') selectedContext)
    (protectedScopes : ∀ pair ∈ frames,
      ResidualContextScope residual (pair.1.applySubst prevailing') pair.2)
    (suffix : Subst)
    (target : NormalizedDMTargetView residual algorithmTarget selectedTarget
      (prevailing'.apply rawTarget))
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing') frontier)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing') provenanceFrames prevailing')
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing') suffix provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing')
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing' (rawContext.applySubst prevailing'))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing') (prevailing'.apply rawTarget))
    (localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing') (prevailing'.apply rawTarget))
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing') frames prevailing')
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (pendingCapFree : PendingLetsCapFree prevailing' pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing'.BoundedBy successor)
    (prevailingIdempotent : prevailing'.Idempotent)
    (retains : ∀ cut, cut ∈ inputPending → cut ∈ pending)
    (auditCuts : ∀ cut, cut ∈ planned.plan.cuts → cut ∈ pending)
    (prevailingEq : prevailing' = Subst.seq suffix prevailing)
    (frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (targetMember : (prevailing'.apply rawTarget, selectedTarget) ∈ frontier) :
    Nonempty (WNormalizedCompleteAt signature supply prevailing rawContext
      expression selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending prevailing'
      frontier rawTarget suffix) := by
  let complete : WCompleteWitness signature supply prevailing rawContext
      expression selectedTarget frames inputFrontier inputPending :=
    { successor := successor
      prevailing' := prevailing'
      rawTarget := rawTarget
      post := post
      frontier := frontier
      derived := planned.derived
      origin := planned.origin
      auditPlan := planned.plan
      pending := pending
      stability := state.stable.lets
      retains := retains
      auditCuts := auditCuts
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := state.stable.frame
      retired := state.retired
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := suffix
      prevailing_eq := prevailingEq
      frontierRetains := frontierRetains
      targetMember := targetMember }
  let normalized : WNormalizedCompleteWitness signature supply prevailing
      rawContext expression selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending :=
    { complete := complete
      algorithmContext := algorithmContext
      algorithmTarget := algorithmTarget
      residual := residual
      post_eq := postEq
      context := context
      scope := scope
      protectedScopes := protectedScopes
      target := target
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := contextOld
      contextProvenanceSuffix := contextProvenanceSuffix
      provenanceIncluded := provenanceIncluded
      protectedOld := protectedOld
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := provenanceRetains
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetGenerative := targetGenerative
      localOldFree := localOldFree
      protectedCovered := protectedCovered
      contextSuffix := contextSuffix
      pendingCapFree := pendingCapFree }
  exact ⟨
    { result := normalized
      prevailing_eq := rfl
      frontier_eq := rfl
      rawTarget_eq := rfl
      suffix_eq := rfl }⟩

/-- Final raw/origin/audit and chronology packaging for application once both
ordinary cuts and both recursive children have been completed. -/
theorem w_app_complete_of_finished
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {initial : Subst} {rawContext : Context} {function argument : Expr}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (functionResult : WNormalizedCompleteWitness signature supply initial
      rawContext function selectedContext (.fn domain codomain)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames
      inputFrontier inputPending)
    (prepared : WAppArgumentPrepared signature rawContext selectedContext
      domain codomain provenanceFloor provenanceContext provenanceFrames
      provenanceFrontier generativityObligations frames
      functionResult.complete.successor
      functionResult.complete.prevailing' functionResult.complete.suffix
      functionResult.complete.frontier
      functionResult.complete.pending)
    (functionAligned : DemandAlignTypesWithLedger []
      functionResult.complete.prevailing' functionResult.complete.rawTarget
      (.fn (.var functionResult.complete.successor.nextTy)
        (.var (functionResult.complete.successor.nextTy + 1)))
      prepared.prevailing)
    (argumentResult : WNormalizedCompleteWitness signature prepared.supply
      prepared.prevailing rawContext argument selectedContext domain
      provenanceFloor provenanceContext provenanceFrames
      (provenanceFrontier.map fun pair =>
        (prepared.retainedSuffix.apply pair.1, pair.2))
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        GenerativitySurfaceObligations.protectToken
          (.var functionResult.complete.successor.nextTy)
          (GenerativitySurfaceObligations.protectToken
            (.var (functionResult.complete.successor.nextTy + 1))
            generativityObligations)) frames
      prepared.frontier functionResult.complete.pending)
    (finished : WAppFinished signature rawContext selectedContext codomain
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames
      prepared
      argumentResult)
    :
    Nonempty (WNormalizedCompleteAt signature supply initial rawContext
      (.app function argument) selectedContext codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending
      finished.prevailing finished.frontier
      (.var (functionResult.complete.successor.nextTy + 1))
      (Subst.seq finished.delta
        (Subst.seq argumentResult.complete.suffix prepared.retainedSuffix))) := by
  let checked : DemandCheck signature prepared.supply prepared.prevailing
      rawContext argument (.var functionResult.complete.successor.nextTy)
      argumentResult.complete.successor finished.prevailing :=
    DemandCheck.mk argumentResult.complete.derived finished.aligned.erase
  let checkedOrigin : DemandCheckOrigin signature checked [] [] :=
    DemandCheckOrigin.mk argumentResult.complete.origin finished.aligned
  let checkedPlan : WCheckAuditPlan signature (origin := checkedOrigin) :=
    WSynthAuditPlan.check (aligned := finished.aligned)
      argumentResult.complete.auditPlan
  let derived : DemandSynth signature supply initial rawContext
      (.app function argument)
      (.var (functionResult.complete.successor.nextTy + 1))
      argumentResult.complete.successor finished.prevailing :=
    DemandSynth.app functionResult.complete.derived
      functionAligned.erase checked
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.app functionResult.complete.origin functionAligned
      checkedOrigin
  let plan : WSynthAuditPlan signature (origin := origin) :=
    WSynthAuditPlan.app (aligned := functionAligned)
      functionResult.complete.auditPlan checkedPlan
  let planned : PlannedSynth signature supply initial rawContext
      (.app function argument)
      (.var (functionResult.complete.successor.nextTy + 1))
      argumentResult.complete.successor finished.prevailing :=
    ⟨derived, origin, plan⟩
  have finalAdmissible : AdmissiblePost []
      (SSubst.paired argumentResult.residual) := by
    have admissible := argumentResult.complete.postAdmissible
    rw [argumentResult.post_eq] at admissible
    exact admissible
  have retains : ∀ cut, cut ∈ inputPending →
      cut ∈ argumentResult.complete.pending := by
    intro cut member
    exact argumentResult.complete.retains cut
      (functionResult.complete.retains cut member)
  have auditCuts : ∀ cut, cut ∈ plan.cuts →
      cut ∈ argumentResult.complete.pending := by
    intro cut member
    change cut ∈ functionResult.complete.auditPlan.cuts ++
      argumentResult.complete.auditPlan.cuts at member
    rcases List.mem_append.mp member with functionCut | argumentCut
    · exact argumentResult.complete.retains cut
        (functionResult.complete.auditCuts cut functionCut)
    · exact argumentResult.complete.auditCuts cut argumentCut
  let suffix := Subst.seq finished.delta
    (Subst.seq argumentResult.complete.suffix
      (Subst.seq prepared.suffix functionResult.complete.suffix))
  have prevailingEq : finished.prevailing = Subst.seq suffix initial := by
    calc
      finished.prevailing = Subst.seq finished.delta
          argumentResult.complete.prevailing' := finished.prevailing_eq
      _ = Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix prepared.prevailing) :=
        congrArg (Subst.seq finished.delta)
          argumentResult.complete.prevailing_eq
      _ = Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix
            (Subst.seq prepared.suffix
              functionResult.complete.prevailing')) :=
        congrArg (fun current => Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix current))
          prepared.prevailing_eq
      _ = Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix
            (Subst.seq prepared.suffix
              (Subst.seq functionResult.complete.suffix initial))) :=
        congrArg (fun current => Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix
            (Subst.seq prepared.suffix current)))
          functionResult.complete.prevailing_eq
      _ = Subst.seq suffix initial := by
        simp only [suffix, PhasedPost.seq_assoc]
  have frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ finished.frontier := by
    intro algorithm selected member
    have inFunction := functionResult.complete.frontierRetains _ _ member
    have inPrepared := prepared.frontierRetains _ _ inFunction
    have inArgument := argumentResult.complete.frontierRetains _ _ inPrepared
    rw [finished.frontier_eq]
    apply List.mem_map.mpr
    refine ⟨(argumentResult.complete.suffix.apply
      (prepared.suffix.apply
        (functionResult.complete.suffix.apply algorithm)), selected),
      inArgument, ?_⟩
    simp only [suffix, Subst.seq_apply]
  have retainedSuffixEq :
      Subst.seq finished.delta
        (Subst.seq argumentResult.complete.suffix prepared.retainedSuffix) =
        suffix := by
    calc
      _ = Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix
            (Subst.seq prepared.suffix functionResult.complete.suffix)) :=
        congrArg (fun current => Subst.seq finished.delta
          (Subst.seq argumentResult.complete.suffix current))
          prepared.retainedSuffix_eq
      _ = suffix := rfl
  have finalRetained : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing) suffix
      provenanceFrontier := by
    rw [← retainedSuffixEq]
    exact finished.retainedOuter
  have finalProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ finished.frontier := by
    rw [← retainedSuffixEq]
    exact finished.provenanceRetains
  have core := w_normalized_complete_core
    (algorithmContext := functionResult.algorithmContext)
    planned finished.state rfl finished.context finished.scope
    finished.protectedScopes
    suffix
    finished.target provenanceFloor provenanceContext provenanceFrames
    functionResult.floorCaps
    functionResult.floorTargets finished.contextOld
    functionResult.contextProvenanceSuffix
    finished.provenanceIncluded finished.protectedOld
    functionResult.provenanceSuffix finished.provenanceCovered
    finalRetained finalProvenanceRetains finished.generativity
    finished.generativityContexts functionResult.generativityValid
    functionResult.currentObligation finished.targetGenerative
    (finished.targetGenerative _ functionResult.currentObligation)
    finished.protectedCovered functionResult.contextSuffix
    finished.pendingCapFree finalAdmissible finished.prevailingBounded
    finished.prevailingIdempotent retains auditCuts prevailingEq
    frontierRetains finished.targetMember
  simpa only [retainedSuffixEq] using core

/-- Oracle-free chronological application constructor.  The continuation is
exactly the recursive argument completeness result at the state produced by
the function cut; both solver cuts and the final origin/audit package are
constructed internally. -/
theorem Typing.w_normalized_app
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {initial : Subst} {rawContext : Context} {function argument : Expr}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (functionResult : WNormalizedCompleteWitness signature supply initial
      rawContext function selectedContext (.fn domain codomain)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (active : (rawContext, selectedContext) ∈ frames)
    (signatureClosed : signature.SchemesClosed)
    (argumentContinuation : ∀
      (prepared : WAppArgumentPrepared signature rawContext selectedContext
        domain codomain provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations frames
        functionResult.complete.successor
        functionResult.complete.prevailing' functionResult.complete.suffix
        functionResult.complete.frontier functionResult.complete.pending),
      DemandAlignTypesWithLedger [] functionResult.complete.prevailing'
        functionResult.complete.rawTarget
        (.fn (.var functionResult.complete.successor.nextTy)
          (.var (functionResult.complete.successor.nextTy + 1)))
        prepared.prevailing →
      WNormalizedCompleteResult signature prepared.supply prepared.prevailing
        rawContext argument selectedContext domain provenanceFloor
        provenanceContext provenanceFrames
        (provenanceFrontier.map fun pair =>
          (prepared.retainedSuffix.apply pair.1, pair.2))
        (GenerativitySurfaceObligation.current prepared.supply rawContext ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var (functionResult.complete.successor.nextTy + 1))
              generativityObligations)) frames
        prepared.frontier functionResult.complete.pending) :
    WNormalizedCompleteResult signature supply initial rawContext
      (.app function argument) selectedContext codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending := by
  obtain ⟨prepared, functionAligned, _functionTargetEq⟩ :=
    functionResult.prepareAppArgument active signatureClosed
  obtain ⟨argumentResult⟩ := argumentContinuation prepared functionAligned
  obtain ⟨finished⟩ :=
    argumentResult.finishAppArgument prepared active signatureClosed
  obtain ⟨completed⟩ := w_app_complete_of_finished functionResult prepared
    functionAligned argumentResult finished
  exact completed.toResult

/-- Paired-surface application constructor.  The recursive argument receives
the exact current continuation as its paired entry; on return that local
entry is discarded before the second cut, while every outer paired surface
is transported through both exact cuts. -/
theorem Typing.w_paired_normalized_app
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {initial : Subst} {rawContext : Context} {function argument : Expr}
    {selectedContext : SCtx} {domain codomain : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)} {inputPending : List PendingLetCut}
    (functionResult : WPairedNormalizedCompleteWitness signature supply initial
      rawContext function selectedContext (.fn domain codomain)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (active : (rawContext, selectedContext) ∈ frames)
    (signatureClosed : signature.SchemesClosed)
    (argumentContinuation : ∀
      (prepared : WAppArgumentPrepared signature rawContext selectedContext
        domain codomain InferenceBase.FreshSupply.empty [] [] []
        generativityObligations frames
        functionResult.normalized.complete.successor
        functionResult.normalized.complete.prevailing'
        functionResult.normalized.complete.suffix
        functionResult.normalized.complete.frontier
        functionResult.normalized.complete.pending),
      DemandAlignTypesWithLedger []
        functionResult.normalized.complete.prevailing'
        functionResult.normalized.complete.rawTarget
        (.fn (.var functionResult.normalized.complete.successor.nextTy)
          (.var (functionResult.normalized.complete.successor.nextTy + 1)))
        prepared.prevailing →
      (rawContext.applySubst prepared.prevailing).fcv = [] →
      GenerativitySurfaceFrameAt
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations)) prepared.prevailing →
      GenerativitySurfaceContextsAt
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations)) prepared.prevailing
        (rawContext.applySubst prepared.prevailing) →
      GenerativitySurfaceValid prepared.supply rawContext
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations)) →
      GenerativitySurfaceRetainedAt
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations)) prepared.prevailing →
      GenerativitySurfaceMembersAt
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations)) prepared.prevailing prepared.frontier →
      WPairedNormalizedCompleteResult signature prepared.supply
        prepared.prevailing rawContext argument selectedContext domain
        InferenceBase.FreshSupply.empty [] [] []
        (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
            prepared.frontier ::
          GenerativitySurfaceObligation.current prepared.supply rawContext ::
          provenanceApplicationObligation provenanceFloor provenanceContext
            functionResult.normalized.complete.successor.nextTy
            prepared.retainedSuffix provenanceFrontier ::
          GenerativitySurfaceObligations.protectToken
            (.var functionResult.normalized.complete.successor.nextTy)
            (GenerativitySurfaceObligations.protectToken
              (.var
                (functionResult.normalized.complete.successor.nextTy + 1))
              generativityObligations))
        frames prepared.frontier functionResult.normalized.complete.pending) :
    WPairedNormalizedCompleteResult signature supply initial rawContext
      (.app function argument) selectedContext codomain provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending := by
  obtain ⟨prepared, functionAligned, functionTargetEq⟩ :=
    functionResult.normalized.prepareAppArgument active signatureClosed
  let outerProtected := GenerativitySurfaceObligations.protectToken
    (.var functionResult.normalized.complete.successor.nextTy)
    (GenerativitySurfaceObligations.protectToken
      (.var (functionResult.normalized.complete.successor.nextTy + 1))
      generativityObligations)
  have outerPaired₁ : GenerativityPairedStateAt generativityObligations
      prepared.prevailing prepared.frontier :=
    prepared.pairedTransport ⟨functionResult.surfacesRetained,
      functionResult.surfacesMembers⟩
  have outerRetained₁ : GenerativitySurfaceRetainedAt outerProtected
      prepared.prevailing := outerPaired₁.retained.protectToken.protectToken
  have outerMembers₁ : GenerativitySurfaceMembersAt outerProtected
      prepared.prevailing prepared.frontier :=
    outerPaired₁.members.protectToken.protectToken
  have currentRetained : RetainedOldOrContextAt prepared.supply
      (rawContext.applySubst prepared.prevailing) prepared.prevailing
      prepared.frontier := by
    constructor
    · intro pair member varId free
      exact Or.inl
        ((prepared.prevailingBounded.apply
          (prepared.state.stable.frame.frontierBounded pair member)).caps
          varId free)
    · intro pair member varId free
      exact Or.inl
        ((prepared.prevailingBounded.apply
          (prepared.state.stable.frame.frontierBounded pair member)).targets
          varId free)
  have currentMembers : ∀ pair ∈ prepared.frontier,
      (prepared.prevailing.apply pair.1, pair.2) ∈ prepared.frontier := by
    intro pair member
    rw [prepared.frontierNormalizationTransport
      functionResult.frontierNormalized pair member]
    exact member
  have emptyRetained := GenerativitySurfaceRetainedAt.registerCurrent
    (supply := prepared.supply) (owner := rawContext)
    (surface := [])
    (RetainedOldOrContextAt.nil prepared.supply
      (rawContext.applySubst prepared.prevailing) prepared.prevailing)
    outerRetained₁
  have emptyMembers := GenerativitySurfaceMembersAt.registerCurrent
    (supply := prepared.supply) (owner := rawContext)
    (surface := []) (frontier := prepared.frontier)
    (fun (pair : Ty × STy) (member : pair ∈ ([] : List (Ty × STy))) => by
      simp at member)
    outerMembers₁
  have childRetained := GenerativitySurfaceRetainedAt.registerCurrent
    (supply := prepared.supply) (owner := rawContext)
    (surface := prepared.frontier)
    currentRetained emptyRetained
  have childMembers := GenerativitySurfaceMembersAt.registerCurrent
    (supply := prepared.supply) (owner := rawContext)
    (surface := prepared.frontier) (frontier := prepared.frontier)
    currentMembers emptyMembers
  have childGenerativity := prepared.childGenerativity.registerPaired
    prepared.supply rawContext prepared.frontier
  have childContexts := prepared.childGenerativityContexts.registerCurrentPaired
    prepared.supply prepared.frontier
  have childValid := prepared.childGenerativityValid.registerCurrentPaired
    prepared.frontier
  have preparedContextCapFree :
      (rawContext.applySubst prepared.prevailing).fcv = [] := by
    rw [prepared.solverPrevailing]
    exact ContextCapFree.applyLetStableExactPairedCut
      functionResult.contextCapFree prepared.solverCut
  let shadow := provenanceApplicationObligation provenanceFloor provenanceContext
    functionResult.normalized.complete.successor.nextTy
    prepared.retainedSuffix provenanceFrontier
  have floorLe : provenanceFloor.nextTy ≤
      functionResult.normalized.complete.successor.nextTy :=
    Nat.le_trans functionResult.floorTargets
      functionResult.normalized.complete.derived.supplyExtends.2
  have domainOldBefore : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst
        functionResult.normalized.complete.prevailing')
      (.var functionResult.normalized.complete.successor.nextTy) :=
    OldFreeInContextAt.var _ _ _ floorLe
  have codomainOldBefore : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst
        functionResult.normalized.complete.prevailing')
      (.var (functionResult.normalized.complete.successor.nextTy + 1)) :=
    OldFreeInContextAt.var _ _ _ (Nat.le_trans floorLe (Nat.le_succ _))
  have shadowBefore : GenerativitySurfaceFrameAt [shadow]
      functionResult.normalized.complete.prevailing' := by
    intro obligation member raw rawMember
    have obligationEq : obligation = shadow := List.mem_singleton.mp member
    subst obligation
    change OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst
        functionResult.normalized.complete.prevailing')
      (functionResult.normalized.complete.prevailing'.apply raw)
    change raw ∈ [.var functionResult.normalized.complete.successor.nextTy,
      .var (functionResult.normalized.complete.successor.nextTy + 1)] at rawMember
    rcases List.mem_cons.mp rawMember with rfl | rawMember
    · simpa [DM.Subst.BoundedBy.apply_freshTarget
        functionResult.normalized.complete.prevailingBounded] using domainOldBefore
    rcases List.mem_singleton.mp rawMember with rfl
    have fixed := DM.Subst.BoundedBy.apply_targetAbove
      functionResult.normalized.complete.prevailingBounded
        (Nat.le_succ functionResult.normalized.complete.successor.nextTy)
    simpa [fixed] using codomainOldBefore
  have skeletonOldBefore := OldFreeInContextAt.fn domainOldBefore codomainOldBefore
  have shadowFrame : GenerativitySurfaceFrameAt [shadow] prepared.prevailing := by
    rw [prepared.solverPrevailing]
    exact shadowBefore.applyOriginSafeExactPairedMGU
      (fun obligation member => by
        have obligationEq : obligation = shadow := List.mem_singleton.mp member
        subst obligation
        change OldFreeInContextAt provenanceFloor
          (provenanceContext.applySubst
            functionResult.normalized.complete.prevailing')
          (functionResult.normalized.complete.prevailing'.apply
            prepared.functionTarget)
        rw [functionTargetEq]
        exact functionResult.targetOld)
      (fun obligation member => by
        have obligationEq : obligation = shadow := List.mem_singleton.mp member
        subst obligation
        change OldFreeInContextAt provenanceFloor
          (provenanceContext.applySubst
            functionResult.normalized.complete.prevailing')
          (functionResult.normalized.complete.prevailing'.apply
            (.fn (.var functionResult.normalized.complete.successor.nextTy)
              (.var (functionResult.normalized.complete.successor.nextTy + 1))))
        simpa [DM.Subst.BoundedBy.apply_freshTarget
          functionResult.normalized.complete.prevailingBounded,
          DM.Subst.BoundedBy.apply_targetAbove
            functionResult.normalized.complete.prevailingBounded
              (Nat.le_succ functionResult.normalized.complete.successor.nextTy)]
          using skeletonOldBefore)
      prepared.solverCut.exact prepared.solverCut.leftCapFree
      prepared.solverCut.rightCapFree
  have shadowContext : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prepared.prevailing)
      (rawContext.applySubst prepared.prevailing) := by
    obtain ⟨transported, _⟩ :=
      functionResult.contextOld.applyOriginSafeExactPairedMGU_and_protected
        (ProtectedOldFreeAt.nil provenanceFloor
          (rawContext.applySubst functionResult.normalized.complete.prevailing'))
        (by rw [functionTargetEq]; exact functionResult.targetOld)
        (by
          rw [Subst.apply_fn, DM.Subst.BoundedBy.apply_freshTarget
            functionResult.normalized.complete.prevailingBounded,
            DM.Subst.BoundedBy.apply_targetAbove
              functionResult.normalized.complete.prevailingBounded
                (Nat.le_succ functionResult.normalized.complete.successor.nextTy)]
          exact skeletonOldBefore)
        prepared.solverCut.exact
        prepared.solverCut.leftCapFree prepared.solverCut.rightCapFree
    rw [prepared.solverPrevailing, Context.applySubst_seq,
      Context.applySubst_seq]
    exact transported
  have shadowRetained : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prepared.prevailing) prepared.prevailing
      shadow.continuation := by
    have transported := functionResult.retainedOuter
      |>.applyOriginSafeExactPairedMGU_of_endpointsOld
        (by rw [functionTargetEq]; exact functionResult.targetOld)
        (by
          rw [Subst.apply_fn, DM.Subst.BoundedBy.apply_freshTarget
            functionResult.normalized.complete.prevailingBounded,
            DM.Subst.BoundedBy.apply_targetAbove
              functionResult.normalized.complete.prevailingBounded
                (Nat.le_succ functionResult.normalized.complete.successor.nextTy)]
          exact skeletonOldBefore)
        prepared.solverCut.exact prepared.solverCut.leftCapFree
        prepared.solverCut.rightCapFree
    constructor <;> intro pair pairMember varId free
    · rcases List.mem_map.mp pairMember with ⟨source, sourceMember, rfl⟩
      have functionMember := functionResult.provenanceRetains _ _ sourceMember
      have functionFixed := functionResult.frontierNormalized _ functionMember
      have retainedMember := prepared.frontierRetains _ _ functionMember
      have fixed := prepared.frontierNormalizationTransport
        functionResult.frontierNormalized _ retainedMember
      have retainedRawEq : prepared.retainedSuffix.apply source.1 =
          prepared.solverDelta.apply
            (functionResult.normalized.complete.suffix.apply source.1) := by
        rw [prepared.retainedSuffix_eq, Subst.seq_apply]
        calc
          prepared.suffix.apply
                (functionResult.normalized.complete.suffix.apply source.1) =
              prepared.prevailing.apply
                (functionResult.normalized.complete.suffix.apply source.1) := by
            rw [prepared.prevailing_eq, Subst.seq_apply, functionFixed]
          _ = prepared.solverDelta.apply
                (functionResult.normalized.complete.suffix.apply source.1) := by
            rw [prepared.solverPrevailing, Subst.seq_apply, functionFixed]
      have fixed' : prepared.prevailing.apply
            (prepared.retainedSuffix.apply source.1) =
          prepared.retainedSuffix.apply source.1 := by
        simpa only [prepared.retainedSuffix_eq, Subst.seq_apply] using fixed
      have free' : varId ∈ (prepared.retainedSuffix.apply source.1).fcv := by
        rw [← fixed']
        exact free
      have retained := transported.caps source sourceMember varId (by
        rw [Subst.seq_apply, ← retainedRawEq]
        exact free')
      simpa [prepared.solverPrevailing, Context.applySubst_seq] using retained
    · rcases List.mem_map.mp pairMember with ⟨source, sourceMember, rfl⟩
      have functionMember := functionResult.provenanceRetains _ _ sourceMember
      have functionFixed := functionResult.frontierNormalized _ functionMember
      have retainedMember := prepared.frontierRetains _ _ functionMember
      have fixed := prepared.frontierNormalizationTransport
        functionResult.frontierNormalized _ retainedMember
      have retainedRawEq : prepared.retainedSuffix.apply source.1 =
          prepared.solverDelta.apply
            (functionResult.normalized.complete.suffix.apply source.1) := by
        rw [prepared.retainedSuffix_eq, Subst.seq_apply]
        calc
          prepared.suffix.apply
                (functionResult.normalized.complete.suffix.apply source.1) =
              prepared.prevailing.apply
                (functionResult.normalized.complete.suffix.apply source.1) := by
            rw [prepared.prevailing_eq, Subst.seq_apply, functionFixed]
          _ = prepared.solverDelta.apply
                (functionResult.normalized.complete.suffix.apply source.1) := by
            rw [prepared.solverPrevailing, Subst.seq_apply, functionFixed]
      have fixed' : prepared.prevailing.apply
            (prepared.retainedSuffix.apply source.1) =
          prepared.retainedSuffix.apply source.1 := by
        simpa only [prepared.retainedSuffix_eq, Subst.seq_apply] using fixed
      have free' : varId ∈ (prepared.retainedSuffix.apply source.1).ftv := by
        rw [← fixed']
        exact free
      have retained := transported.targets source sourceMember varId (by
        rw [Subst.seq_apply, ← retainedRawEq]
        exact free')
      simpa [prepared.solverPrevailing, Context.applySubst_seq] using retained
  have withShadowFrame : GenerativitySurfaceFrameAt
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) prepared.prevailing := by
    intro obligation member raw rawMember
    rcases List.mem_cons.mp member with rfl | member
    · exact prepared.childGenerativity _ List.mem_cons_self raw rawMember
    rcases List.mem_cons.mp member with rfl | member
    · exact shadowFrame shadow List.mem_cons_self raw rawMember
    · exact prepared.childGenerativity obligation
        (List.mem_cons_of_mem _ member) raw rawMember
  have withShadowContexts : GenerativitySurfaceContextsAt
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) prepared.prevailing
      (rawContext.applySubst prepared.prevailing) := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | member
    · exact prepared.childGenerativityContexts _ List.mem_cons_self
    rcases List.mem_cons.mp member with rfl | member
    · exact shadowContext
    · exact prepared.childGenerativityContexts obligation
        (List.mem_cons_of_mem _ member)
  have withShadowValid : GenerativitySurfaceValid prepared.supply rawContext
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | member
    · exact prepared.childGenerativityValid _ List.mem_cons_self
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨Nat.le_trans functionResult.floorCaps
            functionResult.normalized.complete.derived.supplyExtends.1,
          Nat.le_trans functionResult.floorTargets
            (Nat.le_trans functionResult.normalized.complete.derived.supplyExtends.2
              (Nat.le_add_right _ _))⟩,
        functionResult.contextProvenanceSuffix⟩
    · exact prepared.childGenerativityValid obligation
        (List.mem_cons_of_mem _ member)
  have withShadowRetained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
          prepared.frontier ::
        GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) prepared.prevailing := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | member
    · exact currentRetained
    rcases List.mem_cons.mp member with rfl | member
    · exact RetainedOldOrContextAt.nil prepared.supply
        (rawContext.applySubst prepared.prevailing) prepared.prevailing
    rcases List.mem_cons.mp member with rfl | member
    · exact shadowRetained
    · exact outerRetained₁ obligation member
  have withShadowMembers : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
          prepared.frontier ::
        GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) prepared.prevailing prepared.frontier := by
    intro obligation member pair pairMember
    rcases List.mem_cons.mp member with rfl | member
    · exact currentMembers pair pairMember
    rcases List.mem_cons.mp member with rfl | member
    · simp [GenerativitySurfaceObligation.current] at pairMember
    rcases List.mem_cons.mp member with rfl | member
    · rcases List.mem_map.mp pairMember with ⟨source, sourceMember, rfl⟩
      have retained := prepared.frontierRetains _ _
        (functionResult.provenanceRetains _ _ sourceMember)
      have retained' :
          (prepared.retainedSuffix.apply source.1, source.2) ∈
            prepared.frontier := by
        simpa only [prepared.retainedSuffix_eq, Subst.seq_apply] using retained
      exact currentMembers _ retained'
    · exact outerMembers₁ obligation member pair pairMember
  obtain ⟨argumentResult⟩ := argumentContinuation prepared functionAligned
    preparedContextCapFree
    (withShadowFrame.registerPaired prepared.supply rawContext prepared.frontier)
    (withShadowContexts.registerCurrentPaired prepared.supply prepared.frontier)
    (withShadowValid.registerCurrentPaired prepared.frontier)
    withShadowRetained withShadowMembers
  have trimMember : ∀ {obligation}, obligation ∈
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        outerProtected) → obligation ∈
      (GenerativitySurfaceObligation.currentPaired prepared.supply rawContext
          prepared.frontier ::
        GenerativitySurfaceObligation.current prepared.supply rawContext ::
        shadow :: outerProtected) := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member))
  let argumentNormalized : WNormalizedCompleteWitness signature
      prepared.supply prepared.prevailing rawContext argument selectedContext
      domain InferenceBase.FreshSupply.empty [] [] []
      (GenerativitySurfaceObligation.current prepared.supply rawContext ::
        outerProtected) frames prepared.frontier
      functionResult.normalized.complete.pending :=
    { complete := argumentResult.normalized.complete
      algorithmContext := argumentResult.normalized.algorithmContext
      algorithmTarget := argumentResult.normalized.algorithmTarget
      residual := argumentResult.normalized.residual
      post_eq := argumentResult.normalized.post_eq
      context := argumentResult.normalized.context
      scope := argumentResult.normalized.scope
      protectedScopes := argumentResult.normalized.protectedScopes
      target := argumentResult.normalized.target
      floorCaps := argumentResult.normalized.floorCaps
      floorTargets := argumentResult.normalized.floorTargets
      contextOld := argumentResult.normalized.contextOld
      contextProvenanceSuffix := argumentResult.normalized.contextProvenanceSuffix
      provenanceIncluded := argumentResult.normalized.provenanceIncluded
      protectedOld := argumentResult.normalized.protectedOld
      provenanceSuffix := argumentResult.normalized.provenanceSuffix
      provenanceCovered := argumentResult.normalized.provenanceCovered
      retainedOuter := argumentResult.normalized.retainedOuter
      provenanceRetains := argumentResult.normalized.provenanceRetains
      generativity := argumentResult.normalized.generativity.of_obligations_subset
        (fun _ member => trimMember member)
      generativityContexts := by
        intro obligation member
        exact argumentResult.normalized.generativityContexts obligation
          (trimMember member)
      generativityValid := by
        intro obligation member
        exact argumentResult.normalized.generativityValid obligation
          (trimMember member)
      currentObligation := List.mem_cons_self
      targetGenerative := by
        intro obligation member
        exact argumentResult.normalized.targetGenerative obligation
          (trimMember member)
      localOldFree := argumentResult.normalized.localOldFree
      protectedCovered := argumentResult.normalized.protectedCovered
      contextSuffix := argumentResult.normalized.contextSuffix
      pendingCapFree := argumentResult.normalized.pendingCapFree }
  obtain ⟨finished⟩ := argumentNormalized.finishAppArgument prepared
    active signatureClosed
  obtain ⟨completed⟩ := w_app_complete_of_finished
    functionResult.normalized prepared functionAligned argumentNormalized
      finished
  let normalizedResult := completed.result
  have outerRetained₂ : GenerativitySurfaceRetainedAt generativityObligations
      finished.prevailing := by
    have protectedBefore : GenerativitySurfaceRetainedAt outerProtected
        argumentResult.normalized.complete.prevailing' :=
      argumentResult.surfacesRetained.of_obligations_subset (by
        intro obligation member
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ member)))
    have protectedAfter := protectedBefore.applyOriginSafeExactPairedMGU
        (fun obligation member => argumentResult.normalized.targetGenerative
          obligation (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ member))))
        (fun obligation member => argumentResult.normalized.generativity
          obligation (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ member)))
          (.var functionResult.normalized.complete.successor.nextTy)
          (by
            rcases List.mem_map.mp member with ⟨codomainProtected, _, rfl⟩
            simp [GenerativitySurfaceObligation.protectToken]))
        finished.solverCut.exact finished.solverCut.leftCapFree
        finished.solverCut.rightCapFree
    simpa only [finished.prevailing_eq] using
      protectedAfter.unprotectToken.unprotectToken
  have outerMembers₂ : GenerativitySurfaceMembersAt generativityObligations
      finished.prevailing finished.frontier := by
    have outerBefore : GenerativitySurfaceMembersAt outerProtected
        argumentResult.normalized.complete.prevailing'
        argumentResult.normalized.complete.frontier :=
      argumentResult.surfacesMembers.of_obligations_subset (by
        intro obligation member
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ member)))
    simpa only [finished.prevailing_eq, finished.frontier_eq] using
      outerBefore.applyOriginSafeExactPairedMGU.unprotectToken.unprotectToken
  have finishedFrontierNormalized : ∀ pair ∈ finished.frontier,
      finished.prevailing.apply pair.1 = pair.1 := by
    intro pair member
    rw [finished.frontier_eq] at member
    rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    have sourceFixed := argumentResult.frontierNormalized source sourceMember
    have prevailingSource : finished.prevailing.apply source.1 =
        finished.delta.apply source.1 := by
      rw [finished.prevailing_eq, Subst.seq_apply, sourceFixed]
    calc
      finished.prevailing.apply (finished.delta.apply source.1) =
          finished.prevailing.apply (finished.prevailing.apply source.1) := by
        rw [prevailingSource]
      _ = finished.prevailing.apply source.1 :=
        finished.prevailingIdempotent source.1
      _ = finished.delta.apply source.1 := prevailingSource
  have completedPrevailing : normalizedResult.complete.prevailing' =
      finished.prevailing := completed.prevailing_eq
  have completedFrontier : normalizedResult.complete.frontier =
      finished.frontier := completed.frontier_eq
  have finishedContextCapFree :
      (rawContext.applySubst finished.prevailing).fcv = [] := by
    rw [finished.prevailing_eq]
    exact ContextCapFree.applyLetStableExactPairedCut
      argumentResult.contextCapFree finished.solverCut
  have argumentOuterTargetOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst argumentResult.normalized.complete.prevailing')
      (argumentResult.normalized.complete.prevailing'.apply
        argumentResult.normalized.complete.rawTarget) := by
    exact argumentResult.normalized.targetGenerative shadow
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have argumentOuterDomainOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst argumentResult.normalized.complete.prevailing')
      (argumentResult.normalized.complete.prevailing'.apply
        (.var functionResult.normalized.complete.successor.nextTy)) := by
    exact argumentResult.normalized.generativity
      shadow
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _
      (by simp [shadow, provenanceApplicationObligation])
  have finalOuterTargetOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing)
      (finished.prevailing.apply
        (.var (functionResult.normalized.complete.successor.nextTy + 1))) := by
    let finalShadow := shadow
    have before : GenerativitySurfaceFrameAt [finalShadow]
        argumentResult.normalized.complete.prevailing' := by
      intro obligation member raw rawMember
      have eq : obligation = finalShadow := List.mem_singleton.mp member
      subst obligation
      exact argumentResult.normalized.generativity _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        raw rawMember
    have after := before.applyOriginSafeExactPairedMGU
      (fun obligation member => by
        have eq : obligation = finalShadow := List.mem_singleton.mp member
        subst obligation
        exact argumentOuterTargetOld)
      (fun obligation member => by
        have eq : obligation = finalShadow := List.mem_singleton.mp member
        subst obligation
        exact argumentOuterDomainOld) finished.solverCut.exact
      finished.solverCut.leftCapFree finished.solverCut.rightCapFree
    rw [finished.prevailing_eq]
    exact after finalShadow List.mem_cons_self _ (by
      change (Ty.var (functionResult.normalized.complete.successor.nextTy + 1)) ∈
        [Ty.var functionResult.normalized.complete.successor.nextTy,
          Ty.var (functionResult.normalized.complete.successor.nextTy + 1)]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
  have finalOuterContextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing)
      (rawContext.applySubst finished.prevailing) := by
    obtain ⟨transported, _⟩ :=
      (argumentResult.normalized.generativityContexts shadow
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        |>.applyOriginSafeExactPairedMGU_and_protected
        (ProtectedOldFreeAt.nil provenanceFloor
          (rawContext.applySubst argumentResult.normalized.complete.prevailing'))
        argumentOuterTargetOld argumentOuterDomainOld finished.solverCut.exact
        finished.solverCut.leftCapFree finished.solverCut.rightCapFree
    rw [finished.prevailing_eq, Context.applySubst_seq,
      Context.applySubst_seq]
    exact transported
  have finalOuterRetained : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing)
      (Subst.seq finished.delta
        argumentResult.normalized.complete.prevailing')
      (provenanceFrontier.map fun candidate =>
        (prepared.retainedSuffix.apply candidate.1, candidate.2)) := by
    have transported := (argumentResult.surfacesRetained shadow
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      |>.applyOriginSafeExactPairedMGU_of_endpointsOld
        argumentOuterTargetOld argumentOuterDomainOld finished.solverCut.exact
        finished.solverCut.leftCapFree finished.solverCut.rightCapFree
    simpa only [shadow, provenanceApplicationObligation,
      finished.prevailing_eq, Context.applySubst_seq] using transported
  have argumentSuffixOnRetained : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
      argumentResult.normalized.complete.prevailing'.apply
          (prepared.retainedSuffix.apply algorithm) =
        argumentResult.normalized.complete.suffix.apply
          (prepared.retainedSuffix.apply algorithm) := by
    intro algorithm selected member
    have retained := prepared.frontierRetains _ _
      (functionResult.provenanceRetains _ _ member)
    have preparedFixed := prepared.frontierNormalizationTransport
      functionResult.frontierNormalized _ retained
    have preparedRetainedFixed : prepared.prevailing.apply
          (prepared.retainedSuffix.apply algorithm) =
        prepared.retainedSuffix.apply algorithm := by
      simpa only [prepared.retainedSuffix_eq, Subst.seq_apply] using preparedFixed
    rw [argumentResult.normalized.complete.prevailing_eq, Subst.seq_apply,
      preparedRetainedFixed]
  have finalOuterProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
      ((Subst.seq finished.delta
        (Subst.seq argumentResult.normalized.complete.suffix
          prepared.retainedSuffix)).apply algorithm, selected) ∈
        finished.frontier := by
    intro algorithm selected member
    rw [finished.frontier_eq]
    apply List.mem_map.mpr
    have shadowMember := argumentResult.surfacesMembers shadow
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (prepared.retainedSuffix.apply algorithm, selected)
      (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨_, shadowMember, by
      simp only [Subst.seq_apply]
      rw [argumentSuffixOnRetained algorithm selected member]⟩
  have normalizedRawTargetEq : normalizedResult.complete.rawTarget =
      Ty.var (functionResult.normalized.complete.successor.nextTy + 1) :=
    completed.rawTarget_eq
  have normalizedSuffixEq : normalizedResult.complete.suffix =
      Subst.seq finished.delta
        (Subst.seq argumentResult.normalized.complete.suffix
          prepared.retainedSuffix) := completed.suffix_eq
  exact ⟨
    { normalized := normalizedResult
      contextCapFree := by
        rw [completedPrevailing]
        exact finishedContextCapFree
      floorCaps := functionResult.floorCaps
      floorTargets := functionResult.floorTargets
      contextOld := by rw [completedPrevailing]; exact finalOuterContextOld
      contextProvenanceSuffix := functionResult.contextProvenanceSuffix
      provenanceIncluded := by
        rw [completedPrevailing]
        exact functionResult.contextProvenanceSuffix.toIncluded _
      targetOld := by
        rw [completedPrevailing, normalizedRawTargetEq]
        exact finalOuterTargetOld
      provenanceSuffix := functionResult.provenanceSuffix
      provenanceCovered := by
        rw [completedPrevailing]
        exact functionResult.provenanceSuffix.toProtectedFreeCovered _
      retainedOuter := by
        rw [completedPrevailing, normalizedSuffixEq]
        constructor
        · intro pair member varId free
          have mapped : (prepared.retainedSuffix.apply pair.1, pair.2) ∈
              provenanceFrontier.map (fun candidate =>
                (prepared.retainedSuffix.apply candidate.1, candidate.2)) :=
            List.mem_map.mpr ⟨pair, member, rfl⟩
          have free' : varId ∈ ((Subst.seq finished.delta
              argumentResult.normalized.complete.prevailing').apply
                (prepared.retainedSuffix.apply pair.1)).fcv := by
            rw [Subst.seq_apply,
              argumentSuffixOnRetained pair.1 pair.2 member]
            simpa only [Subst.seq_apply] using free
          exact finalOuterRetained.caps _ mapped varId free'
        · intro pair member varId free
          have mapped : (prepared.retainedSuffix.apply pair.1, pair.2) ∈
              provenanceFrontier.map (fun candidate =>
                (prepared.retainedSuffix.apply candidate.1, candidate.2)) :=
            List.mem_map.mpr ⟨pair, member, rfl⟩
          have free' : varId ∈ ((Subst.seq finished.delta
              argumentResult.normalized.complete.prevailing').apply
                (prepared.retainedSuffix.apply pair.1)).ftv := by
            rw [Subst.seq_apply,
              argumentSuffixOnRetained pair.1 pair.2 member]
            simpa only [Subst.seq_apply] using free
          exact finalOuterRetained.targets _ mapped varId free'
      provenanceRetains := by
        rw [completedFrontier, normalizedSuffixEq]
        exact finalOuterProvenanceRetains
      inputFrontierNormalized := functionResult.inputFrontierNormalized
      surfacesRetained := by
        rw [completedPrevailing]
        exact outerRetained₂
      surfacesMembers := by
        rw [completedPrevailing, completedFrontier]
        exact outerMembers₂
      frontierNormalized := by
        rw [completedPrevailing, completedFrontier]
        exact finishedFrontierNormalized
      currentPaired := functionResult.currentPaired }⟩

/-! ## Direct-self fix preparation -/

/-- State exposed to the recursive body of a direct-self fix.  The two
control metavariables are protected only on the already-existing
generativity surfaces; the body itself receives a fresh empty current
surface at its actual entry supply. -/
structure WFixBodyPrepared
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (self argument : String)
    (selectedContext : SCtx) (domain codomain : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Type where
  residual : SSubst
  state : WRetiredStableFrameAt signature
    { supply with nextTy := supply.nextTy + 2 }
    (SSubst.paired residual) prevailing
    (((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
      (argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) ::
      frames)
    ((.var supply.nextTy, domain) ::
      (.var (supply.nextTy + 1), codomain) :: frontier) pending
  context : ErasedDMContextView residual
    ((argument, SScheme.mono domain) ::
      (self, SScheme.mono (.fn domain codomain)) :: selectedContext)
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
  scope : ResidualContextScope residual
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
    ((argument, SScheme.mono domain) ::
      (self, SScheme.mono (.fn domain codomain)) :: selectedContext)
  protectedScopes : ProtectedResidualScopes residual prevailing
    (((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
      (argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) :: frames)
  postAdmissible : AdmissiblePost [] (SSubst.paired residual)
  prevailingBounded : prevailing.BoundedBy
    { supply with nextTy := supply.nextTy + 2 }
  prevailingIdempotent : prevailing.Idempotent
  pendingCapFree : PendingLetsCapFree prevailing pending
  contextCapFree :
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext)).fcv = []
  floorCaps : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ supply.nextTy + 2
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst prevailing)
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
    ((argument, Scheme.mono (.var supply.nextTy)) ::
      (self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst prevailing)
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst prevailing) provenanceFrames prevailing
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (algorithm, selected) ∈
        ((.var supply.nextTy, domain) ::
          (.var (supply.nextTy + 1), codomain) :: frontier)
  childObligations : List GenerativitySurfaceObligation :=
    GenerativitySurfaceObligation.currentPaired
        { supply with nextTy := supply.nextTy + 2 }
        ((argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
        ((.var supply.nextTy, domain) ::
          (.var (supply.nextTy + 1), codomain) :: frontier) ::
      GenerativitySurfaceObligation.current
        { supply with nextTy := supply.nextTy + 2 }
        ((argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext) ::
      provenanceControlObligation provenanceFloor provenanceContext
        supply.nextTy ::
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (supply.nextTy + 1)) generativityObligations)
  outerMember : ∀ obligation ∈
      GenerativitySurfaceObligations.protectToken (.var supply.nextTy)
        (GenerativitySurfaceObligations.protectToken
          (.var (supply.nextTy + 1)) generativityObligations),
    obligation ∈ childObligations
  shadowMember : provenanceControlObligation provenanceFloor provenanceContext
      supply.nextTy ∈ childObligations
  childGenerativity : GenerativitySurfaceFrameAt childObligations prevailing
  childGenerativityContexts : GenerativitySurfaceContextsAt childObligations
    prevailing
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
  childGenerativityValid : GenerativitySurfaceValid
    { supply with nextTy := supply.nextTy + 2 }
    ((argument, Scheme.mono (.var supply.nextTy)) ::
      (self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
    childObligations
  childCurrentObligation : GenerativitySurfaceObligation.current
      { supply with nextTy := supply.nextTy + 2 }
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext) ∈
    childObligations
  childCurrentPaired : GenerativitySurfaceObligation.currentPaired
      { supply with nextTy := supply.nextTy + 2 }
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) ∈ childObligations
  childRetained : GenerativitySurfaceRetainedAt childObligations prevailing
  childMembers : GenerativitySurfaceMembersAt childObligations prevailing
    ((.var supply.nextTy, domain) ::
      (.var (supply.nextTy + 1), codomain) :: frontier)
  frontierNormalized : ∀ pair ∈
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier),
    prevailing.apply pair.1 = pair.1
  protectedCovered : ProtectedFreeCovered
    (Context.applySubst prevailing
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext))
    (((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
      (argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) :: frames)
    prevailing
  contextSuffix : ProtectedContextsSuffix
    ((argument, Scheme.mono (.var supply.nextTy)) ::
      (self, Scheme.mono
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext)
    (((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext,
      (argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) :: frames)
  domainMember : (prevailing.apply (.var supply.nextTy), domain) ∈
    ((.var supply.nextTy, domain) ::
      (.var (supply.nextTy + 1), codomain) :: frontier)
  codomainMember : (prevailing.apply (.var (supply.nextTy + 1)), codomain) ∈
    ((.var supply.nextTy, domain) ::
      (.var (supply.nextTy + 1), codomain) :: frontier)

/-- Package a completed constructor step once its raw plan, protected state,
one-sort normalized view, and chronological transport facts are available. -/
theorem w_normalized_complete_of_planned
    {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' : Subst}
    {rawContext : Context} {expression : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {frames : List (Context × SCtx)}
    {provenanceFrontier inputFrontier frontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputPending pending : List PendingLetCut}
    {rawTarget : Ty} {post : Subst}
    {algorithmContext : SCtx} {algorithmTarget : STy}
    {residual : SSubst}
    (planned : PlannedSynth signature supply prevailing rawContext expression
      rawTarget successor prevailing')
    (state : WRetiredStableFrameAt signature successor post prevailing'
      frames frontier pending)
    (postEq : post = SSubst.paired residual)
    (context : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing'))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing') selectedContext)
    (protectedScopes : ∀ pair ∈ frames,
      ResidualContextScope residual (pair.1.applySubst prevailing') pair.2)
    (suffix : Subst)
    (target : NormalizedDMTargetView residual algorithmTarget selectedTarget
      (prevailing'.apply rawTarget))
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing') frontier)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing') provenanceFrames prevailing')
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing') suffix provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing')
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing' (rawContext.applySubst prevailing'))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing') (prevailing'.apply rawTarget))
    (localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing') (prevailing'.apply rawTarget))
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing') frames prevailing')
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (pendingCapFree : PendingLetsCapFree prevailing' pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing'.BoundedBy successor)
    (prevailingIdempotent : prevailing'.Idempotent)
    (retains : ∀ cut, cut ∈ inputPending → cut ∈ pending)
    (auditCuts : ∀ cut, cut ∈ planned.plan.cuts → cut ∈ pending)
    (prevailingEq : prevailing' = Subst.seq suffix prevailing)
    (frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (targetMember : (prevailing'.apply rawTarget, selectedTarget) ∈ frontier) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      expression selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending := by
  let complete : WCompleteWitness signature supply prevailing rawContext
      expression selectedTarget frames inputFrontier inputPending :=
    { successor := successor
      prevailing' := prevailing'
      rawTarget := rawTarget
      post := post
      frontier := frontier
      derived := planned.derived
      origin := planned.origin
      auditPlan := planned.plan
      pending := pending
      stability := state.stable.lets
      retains := retains
      auditCuts := auditCuts
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := state.stable.frame
      retired := state.retired
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := suffix
      prevailing_eq := prevailingEq
      frontierRetains := frontierRetains
      targetMember := targetMember }
  exact ⟨
    { complete := complete
      algorithmContext := algorithmContext
      algorithmTarget := algorithmTarget
      residual := residual
      post_eq := postEq
      context := context
      scope := scope
      protectedScopes := protectedScopes
      target := target
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := contextOld
      contextProvenanceSuffix := contextProvenanceSuffix
      provenanceIncluded := provenanceIncluded
      protectedOld := protectedOld
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := provenanceRetains
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetGenerative := targetGenerative
      localOldFree := localOldFree
      protectedCovered := protectedCovered
      contextSuffix := contextSuffix
      pendingCapFree := pendingCapFree }⟩

/-- Application spelling of the common final packager. -/
theorem w_app_normalized_complete_of_planned
    {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' : Subst}
    {rawContext : Context} {function argument : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {frames : List (Context × SCtx)}
    {inputFrontier frontier : List (Ty × STy)}
    {inputPending pending : List PendingLetCut}
    {rawTarget : Ty} {post : Subst}
    {algorithmContext : SCtx} {algorithmTarget : STy} {residual : SSubst}
    (planned : PlannedSynth signature supply prevailing rawContext
      (.app function argument) rawTarget successor prevailing')
    (state : WRetiredStableFrameAt signature successor post prevailing'
      frames frontier pending)
    (postEq : post = SSubst.paired residual)
    (context : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing'))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing') selectedContext)
    (protectedScopes : ∀ pair ∈ frames,
      ResidualContextScope residual (pair.1.applySubst prevailing') pair.2)
    (suffix : Subst)
    (target : NormalizedDMTargetView residual algorithmTarget selectedTarget
      (prevailing'.apply rawTarget))
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing') frontier)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing') provenanceFrames prevailing')
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing') suffix provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing')
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing' (rawContext.applySubst prevailing'))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing') (prevailing'.apply rawTarget))
    (localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing') (prevailing'.apply rawTarget))
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing') frames prevailing')
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (pendingCapFree : PendingLetsCapFree prevailing' pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing'.BoundedBy successor)
    (prevailingIdempotent : prevailing'.Idempotent)
    (retains : ∀ cut, cut ∈ inputPending → cut ∈ pending)
    (auditCuts : ∀ cut, cut ∈ planned.plan.cuts → cut ∈ pending)
    (prevailingEq : prevailing' = Subst.seq suffix prevailing)
    (frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (targetMember : (prevailing'.apply rawTarget, selectedTarget) ∈ frontier) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.app function argument) selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending :=
  w_normalized_complete_of_planned (algorithmContext := algorithmContext)
    planned state postEq context scope protectedScopes suffix target provenanceFloor
    provenanceContext provenanceFrames floorCaps floorTargets
    contextOld contextProvenanceSuffix
    provenanceIncluded protectedOld provenanceSuffix provenanceCovered
    retainedOuter provenanceRetains generativity generativityContexts
    generativityValid currentObligation targetGenerative localOldFree
    protectedCovered contextSuffix
    pendingCapFree postAdmissible prevailingBounded prevailingIdempotent
    retains auditCuts prevailingEq frontierRetains targetMember

/-- Direct-self fix spelling of the common final packager. -/
theorem w_fix_normalized_complete_of_planned
    {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' : Subst}
    {rawContext : Context} {self argument : String} {body : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {frames : List (Context × SCtx)}
    {inputFrontier frontier : List (Ty × STy)}
    {inputPending pending : List PendingLetCut}
    {rawTarget : Ty} {post : Subst}
    {algorithmContext : SCtx} {algorithmTarget : STy} {residual : SSubst}
    (planned : PlannedSynth signature supply prevailing rawContext
      (.fix self argument body) rawTarget successor prevailing')
    (state : WRetiredStableFrameAt signature successor post prevailing'
      frames frontier pending)
    (postEq : post = SSubst.paired residual)
    (context : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing'))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing') selectedContext)
    (protectedScopes : ∀ pair ∈ frames,
      ResidualContextScope residual (pair.1.applySubst prevailing') pair.2)
    (suffix : Subst)
    (target : NormalizedDMTargetView residual algorithmTarget selectedTarget
      (prevailing'.apply rawTarget))
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing') frontier)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing') provenanceFrames prevailing')
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing') suffix provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing')
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing' (rawContext.applySubst prevailing'))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing') (prevailing'.apply rawTarget))
    (localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing') (prevailing'.apply rawTarget))
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing') frames prevailing')
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (pendingCapFree : PendingLetsCapFree prevailing' pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing'.BoundedBy successor)
    (prevailingIdempotent : prevailing'.Idempotent)
    (retains : ∀ cut, cut ∈ inputPending → cut ∈ pending)
    (auditCuts : ∀ cut, cut ∈ planned.plan.cuts → cut ∈ pending)
    (prevailingEq : prevailing' = Subst.seq suffix prevailing)
    (frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (targetMember : (prevailing'.apply rawTarget, selectedTarget) ∈ frontier) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.fix self argument body) selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending :=
  w_normalized_complete_of_planned (algorithmContext := algorithmContext)
    planned state postEq context scope protectedScopes suffix target provenanceFloor
    provenanceContext provenanceFrames floorCaps floorTargets
    contextOld contextProvenanceSuffix
    provenanceIncluded protectedOld provenanceSuffix provenanceCovered
    retainedOuter provenanceRetains generativity generativityContexts
    generativityValid currentObligation targetGenerative localOldFree
    protectedCovered contextSuffix
    pendingCapFree postAdmissible prevailingBounded prevailingIdempotent
    retains auditCuts prevailingEq frontierRetains targetMember

/-- Let spelling of the common final packager. -/
theorem w_let_normalized_complete_of_planned
    {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' : Subst}
    {rawContext : Context} {name : String} {value body : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {frames : List (Context × SCtx)}
    {inputFrontier frontier : List (Ty × STy)}
    {inputPending pending : List PendingLetCut}
    {rawTarget : Ty} {post : Subst}
    {algorithmContext : SCtx} {algorithmTarget : STy} {residual : SSubst}
    (planned : PlannedSynth signature supply prevailing rawContext
      (.letE name value body) rawTarget successor prevailing')
    (state : WRetiredStableFrameAt signature successor post prevailing'
      frames frontier pending)
    (postEq : post = SSubst.paired residual)
    (context : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing'))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing') selectedContext)
    (protectedScopes : ∀ pair ∈ frames,
      ResidualContextScope residual (pair.1.applySubst prevailing') pair.2)
    (suffix : Subst)
    (target : NormalizedDMTargetView residual algorithmTarget selectedTarget
      (prevailing'.apply rawTarget))
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing')
      (rawContext.applySubst prevailing'))
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing') frontier)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing') provenanceFrames prevailing')
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing') suffix provenanceFrontier)
    (provenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing')
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing' (rawContext.applySubst prevailing'))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing') (prevailing'.apply rawTarget))
    (localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing') (prevailing'.apply rawTarget))
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing') frames prevailing')
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (pendingCapFree : PendingLetsCapFree prevailing' pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing'.BoundedBy successor)
    (prevailingIdempotent : prevailing'.Idempotent)
    (retains : ∀ cut, cut ∈ inputPending → cut ∈ pending)
    (auditCuts : ∀ cut, cut ∈ planned.plan.cuts → cut ∈ pending)
    (prevailingEq : prevailing' = Subst.seq suffix prevailing)
    (frontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (suffix.apply algorithm, selected) ∈ frontier)
    (targetMember : (prevailing'.apply rawTarget, selectedTarget) ∈ frontier) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.letE name value body) selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending :=
  w_normalized_complete_of_planned (algorithmContext := algorithmContext)
    planned state postEq context scope protectedScopes suffix target provenanceFloor
    provenanceContext provenanceFrames floorCaps floorTargets
    contextOld contextProvenanceSuffix
    provenanceIncluded protectedOld provenanceSuffix provenanceCovered
    retainedOuter provenanceRetains generativity generativityContexts
    generativityValid currentObligation targetGenerative localOldFree
    protectedCovered contextSuffix
    pendingCapFree postAdmissible prevailingBounded prevailingIdempotent
    retains auditCuts prevailingEq frontierRetains targetMember

end DM
end TypePM
