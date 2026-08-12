import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerAcceptanceBridge

/-!
# Mutual Damas--Milner Algorithm W completeness

This module sits above the constructor packages.  It exposes the normalized
mutual result used by the final induction and the public acceptance root.
-/

namespace TypePM
namespace DM

/-- Exact normalized empty chronological traversal. -/
theorem Typings.w_paired_normalized_nil
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext algorithmContext : SCtx} {residual : SSubst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply (SSubst.paired residual)
      prevailing frames frontier pending)
    (contextView : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes residual prevailing frames)
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing) frames prevailing)
    (contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing)
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing (rawContext.applySubst prevailing))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (surfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations prevailing)
    (surfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations prevailing frontier)
    (frontierNormalized : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1)
    (currentPaired : GenerativitySurfaceObligation.currentPaired supply
      rawContext frontier ∈ generativityObligations)
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier)
    (provenanceMembers : ∀ pair, pair ∈ provenanceFrontier → pair ∈ frontier)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing) provenanceFrames prevailing)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (postAdmissible : AdmissiblePost [] (SSubst.paired residual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    WPairedNormalizedTypingsResult signature supply prevailing rawContext []
      selectedContext [] provenanceFloor provenanceContext provenanceFrames
      provenanceFrontier generativityObligations frames frontier pending := by
  let complete : WTypingsFinalWitness signature supply prevailing rawContext
      [] [] frames frontier pending :=
    { successor := supply
      prevailing' := prevailing
      rawTargets := []
      post := SSubst.paired residual
      frontier := frontier
      derived := DemandSynths.nil
      origin := DemandSynthsOrigin.nil
      auditPlan := WSynthsAuditPlan.nil
      pending := pending
      stability := state.stable.lets
      retains := fun _ member => member
      auditCuts := by simp [WSynthsAuditPlan.nil]
      equations := WTargetListRel.nil
      targetsFresh := by simp
      targetsBounded := by simp
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := state.stable.frame
      retired := state.retired
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        simpa only [Subst.apply_id] using member }
  let normalizedWitness : WNormalizedTypingsWitness signature supply
      prevailing rawContext [] selectedContext [] InferenceBase.FreshSupply.empty
      [] [] []
      generativityObligations frames frontier pending :=
    { complete := complete
      algorithmContext := algorithmContext
      algorithmTargets := []
      residual := residual
      post_eq := rfl
      context := contextView
      scope := scope
      protectedScopes := protectedScopes
      targets := NormalizedDMTargetsView.nil
      floorCaps := by simp [InferenceBase.FreshSupply.empty]
      floorTargets := by simp [InferenceBase.FreshSupply.empty]
      contextOld := by
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      contextProvenanceSuffix := by
        exact ⟨rawContext, List.append_nil rawContext⟩
      protectedOld := by
        intro pair member
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      provenanceCovered := by
        constructor <;> intro pair member <;> simp at member
      provenanceIncluded := by
        constructor <;> intro varId free <;>
          simp [Context.applySubst, Context.fcv, Context.ftv] at free
      provenanceSuffix := by simp [ProtectedContextsSuffix]
      retainedOuter := RetainedOldOrContextAt.nil
        InferenceBase.FreshSupply.empty [] Subst.id
      provenanceRetains := by
        intro algorithm selected member
        exact nomatch member
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetsLocalOldFree := by
        intro raw member
        exact nomatch member
      targetsGenerative := by
        intro obligation obligationMember raw rawMember
        exact nomatch rawMember
      protectedCovered := protectedCovered
      contextSuffix := contextSuffix }
  exact ⟨
    { normalized := normalizedWitness
      contextCapFree := contextCapFree
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := contextOld
      contextProvenanceSuffix := contextProvenanceSuffix
      provenanceIncluded := provenanceIncluded
      targetsOld := by intro raw member; exact nomatch member
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := by
        intro algorithm selected member
        rw [Subst.apply_id]
        exact provenanceMembers (algorithm, selected) member
      surfacesRetained := surfacesRetained
      surfacesMembers := surfacesMembers
      inputFrontierNormalized := frontierNormalized
      frontierNormalized := frontierNormalized
      currentPaired := currentPaired }
    ⟩

/-- Exact normalized literal branch. -/
theorem Typing.w_paired_normalized_lit
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext algorithmContext : SCtx} {residual : SSubst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {value : Int} {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply (SSubst.paired residual)
      prevailing frames frontier pending)
    (contextView : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing))
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes residual prevailing frames)
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing) frames prevailing)
    (contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing)
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing (rawContext.applySubst prevailing))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (surfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations prevailing)
    (surfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations prevailing frontier)
    (frontierNormalized : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1)
    (currentPaired : GenerativitySurfaceObligation.currentPaired supply
      rawContext frontier ∈ generativityObligations)
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier)
    (provenanceMembers : ∀ pair, pair ∈ provenanceFrontier → pair ∈ frontier)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (provenanceCovered : ProtectedFreeCovered
      (provenanceContext.applySubst prevailing) provenanceFrames prevailing)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceSuffix : ProtectedContextsSuffix provenanceContext
      provenanceFrames)
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (postAdmissible : AdmissiblePost [] (SSubst.paired residual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.lit value) selectedContext .int provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames frontier pending := by
  let derived : DemandSynth signature supply prevailing rawContext
      (.lit value) .int supply prevailing := DemandSynth.lit
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.lit
  have resultFrame : WProtectedFrameAt supply (SSubst.paired residual)
      prevailing frames ((prevailing.apply .int, STy.int) :: frontier) := by
    refine
      { contexts := state.stable.frame.contexts
        types := WTypeFrame.cons (by rfl) state.stable.frame.types
        contextsBounded := state.stable.frame.contextsBounded
        frontierBounded := ?_ }
    intro pair member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact Ty.BoundedBy.int
    · exact state.stable.frame.frontierBounded pair oldMember
  let complete : WCompleteWitness signature supply prevailing rawContext
      (.lit value) .int frames frontier pending :=
    { successor := supply
      prevailing' := prevailing
      rawTarget := .int
      post := SSubst.paired residual
      frontier := (prevailing.apply .int, STy.int) :: frontier
      derived := derived
      origin := origin
      auditPlan := WSynthAuditPlan.lit
      pending := pending
      stability := state.stable.lets
      retains := fun _ member => member
      auditCuts := by simp [WSynthAuditPlan.lit]
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := resultFrame
      retired := RetiredFrontierFresh.cons
        (fun cut _ => PendingLetCut.AvoidsTy.int signature prevailing cut)
        state.retired
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (by simpa only [Subst.apply_id] using member)
      targetMember := List.mem_cons_self }
  let normalizedWitness : WNormalizedCompleteWitness signature supply
      prevailing rawContext (.lit value) selectedContext .int
      InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames frontier pending :=
    { complete := complete
      algorithmContext := algorithmContext
      algorithmTarget := .int
      residual := residual
      post_eq := rfl
      context := contextView
      scope := scope
      protectedScopes := protectedScopes
      target := NormalizedDMTargetView.lit residual
      floorCaps := by simp [InferenceBase.FreshSupply.empty]
      floorTargets := by simp [InferenceBase.FreshSupply.empty]
      contextOld := by
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      contextProvenanceSuffix := by
        exact ⟨rawContext, List.append_nil rawContext⟩
      protectedOld := by
        intro pair member
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below
      provenanceCovered := by
        constructor <;> intro pair member <;> simp at member
      provenanceIncluded := by
        constructor <;> intro varId free <;>
          simp [Context.applySubst, Context.fcv, Context.ftv] at free
      provenanceSuffix := by simp [ProtectedContextsSuffix]
      retainedOuter := RetainedOldOrContextAt.nil
        InferenceBase.FreshSupply.empty [] Subst.id
      provenanceRetains := by
        intro algorithm selected member
        exact nomatch member
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetGenerative := by
        intro obligation member
        exact OldFreeInContextAt.int obligation.floor _
      localOldFree := OldFreeInContextAt.int supply _
      protectedCovered := protectedCovered
      contextSuffix := contextSuffix
      pendingCapFree := pendingCapFree }
  exact ⟨
    { normalized := normalizedWitness
      contextCapFree := contextCapFree
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := contextOld
      contextProvenanceSuffix := contextProvenanceSuffix
      provenanceIncluded := provenanceIncluded
      targetOld := OldFreeInContextAt.int provenanceFloor _
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := by
        intro algorithm selected member
        rw [Subst.apply_id]
        exact List.mem_cons_of_mem _
          (provenanceMembers (algorithm, selected) member)
      surfacesRetained := surfacesRetained
      surfacesMembers := by
        intro obligation obligationMember pair pairMember
        exact List.mem_cons_of_mem _
          (surfacesMembers obligation obligationMember pair pairMember)
      inputFrontierNormalized := frontierNormalized
      frontierNormalized := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | oldMember
        · exact prevailingIdempotent _
        · exact frontierNormalized pair oldMember
      currentPaired := currentPaired }
    ⟩

/-- Fold a normalized chronological component traversal into a normalized
tuple branch without adding a solver cut. -/
theorem Typing.w_paired_normalized_tuple_of_children
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
    (childrenResult : WPairedNormalizedTypingsResult signature supply prevailing
      rawContext expressions selectedContext selectedTargets provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.tuple expressions) selectedContext (.prod selectedTargets)
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  rcases childrenResult with ⟨childrenPackage⟩
  let children := childrenPackage.normalized
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
  have normalizedTuple : NormalizedDMTargetView children.residual
      (.prod children.algorithmTargets) (.prod selectedTargets)
      (finished.prevailing'.apply (.prod finished.rawTargets)) := by
    simpa only [Subst.apply_prod] using
      (NormalizedDMTargetsView.prod children.targets)
  have productOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst finished.prevailing')
      (finished.prevailing'.apply (.prod finished.rawTargets)) := by
    rw [Subst.apply_prod]
    exact OldFreeInContextAt.prod (by
      intro component componentMember
      obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
      exact childrenPackage.targetsOld raw rawMember)
  let normalizedWitness : WNormalizedCompleteWitness signature supply
      prevailing rawContext (.tuple expressions) selectedContext
      (.prod selectedTargets) InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames frontier pending :=
    { complete := complete
      algorithmContext := children.algorithmContext
      algorithmTarget := .prod children.algorithmTargets
      residual := children.residual
      post_eq := children.post_eq
      context := children.context
      scope := children.scope
      protectedScopes := children.protectedScopes
      target := normalizedTuple
      floorCaps := children.floorCaps
      floorTargets := children.floorTargets
      contextOld := children.contextOld
      contextProvenanceSuffix := children.contextProvenanceSuffix
      protectedOld := children.protectedOld.cons (by
        constructor <;> intro varId free below <;>
          simp [InferenceBase.FreshSupply.empty] at below)
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
  exact ⟨
    { normalized := normalizedWitness
      contextCapFree := childrenPackage.contextCapFree
      floorCaps := childrenPackage.floorCaps
      floorTargets := childrenPackage.floorTargets
      contextOld := childrenPackage.contextOld
      contextProvenanceSuffix := childrenPackage.contextProvenanceSuffix
      provenanceIncluded := childrenPackage.provenanceIncluded
      targetOld := productOld
      provenanceSuffix := childrenPackage.provenanceSuffix
      provenanceCovered := childrenPackage.provenanceCovered
      retainedOuter := childrenPackage.retainedOuter
      provenanceRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (childrenPackage.provenanceRetains algorithm selected member)
      surfacesRetained := childrenPackage.surfacesRetained
      surfacesMembers := by
        intro obligation obligationMember pair pairMember
        exact List.mem_cons_of_mem _
          (childrenPackage.surfacesMembers obligation obligationMember pair
            pairMember)
      inputFrontierNormalized := childrenPackage.inputFrontierNormalized
      frontierNormalized := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | oldMember
        · exact finished.prevailingIdempotent _
        · exact childrenPackage.frontierNormalized pair oldMember
      currentPaired := childrenPackage.currentPaired }
    ⟩

/-! ## Public root -/

/-- Any completed normalized root run is accepted by the public executable
inference function. -/
theorem inferenceSucceeds_of_normalized_complete
    {signature : FrozenSig} {context : SCtx} {expression : Expr}
    {selectedTarget : STy}
    (signatureWF : FrozenSigWF signature)
    (result : WNormalizedCompleteResult signature
      (Inference.initialSupply signature context.emb) Subst.id context.emb
      expression context selectedTarget
      (Inference.initialSupply signature context.emb) context.emb
      [(context.emb, context)] []
      [GenerativitySurfaceObligation.current
        (Inference.initialSupply signature context.emb) context.emb]
      [(context.emb, context)] [] []) :
    Inference.inferenceSucceeds signature context.emb expression = true := by
  rcases result with ⟨normalized⟩
  obtain ⟨audit⟩ := normalized.complete.audit
  exact inferenceSucceeds_of_auditedWRun signatureWF audit

end DM
end TypePM
