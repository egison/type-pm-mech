import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerWNormalizedOpening
import TypePM.DamasMilnerWNormalizedVarFresh

/-!
# Erasure-stable normalized variable completeness

The algorithm context may contain an arbitrary capability-free core scheme.
Its semantic realization is sufficient; no syntactic reification of the
whole context as an embedded simple context is assumed.
-/

namespace TypePM
namespace DM

/-- A generic core-scheme opening is invisible below its fresh allocation
interval, hence preserves an existing residual context scope. -/
theorem ResidualContextScope.extendCoreSchemeOpening
    {base : SSubst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx} {scheme : Scheme}
    (opening : (scheme.applyMeta (SSubst.paired base)).ValueOpening)
    (scope : ResidualContextScope base algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply) :
    ResidualContextScope
      (fun varId => eraseTy
        ((DM.extendSchemeOpening (SSubst.paired base) supply scheme opening)
          |>.target varId))
      algorithmContext selectedContext := by
  intro algorithmVar selectedVar algorithmFree imageFree
  have below : algorithmVar < supply.nextTy := by
    rw [Context.ftv] at algorithmFree
    rcases List.mem_flatMap.mp algorithmFree with
      ⟨entry, entryMember, free⟩
    exact (bounded entry entryMember).targets algorithmVar free
  have imageEq := DM.extendSchemeOpening_target_below
    (SSubst.paired base) supply scheme opening algorithmVar below
  change selectedVar ∈
    (eraseTy ((DM.extendSchemeOpening (SSubst.paired base) supply scheme
      opening).target algorithmVar)).ftv at imageFree
  rw [imageEq] at imageFree
  have imageFree' : selectedVar ∈ (base algorithmVar).ftv := by
    simpa [SSubst.paired, SSubst.emb, eraseTy_emb] using imageFree
  exact scope algorithmFree imageFree'

/-- Variable completeness from an erased context relation.  Lookup exposes
the actual core algorithm scheme, while `RealizedBy` and the normalized
opening theorem construct the paired residual extension. -/
theorem Typing.w_paired_erased_normalized_var
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {name : String}
    {selectedScheme : SScheme} {selectedTarget : STy}
    {pending : List PendingLetCut} {contextResidual : SSubst}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired contextResidual) prevailing frames frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (contextView : ErasedDMContextView contextResidual selectedContext
      (rawContext.applySubst prevailing))
    (contextScope : ResidualContextScope contextResidual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes contextResidual prevailing
      frames)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (contextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
    (contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext
      rawContext)
    (provenanceIncluded : ProvenanceContextIncluded
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing))
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
    (generativityContexts : GenerativitySurfaceContextsAt
      generativityObligations prevailing (rawContext.applySubst prevailing))
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈
      generativityObligations)
    (surfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations prevailing)
    (surfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations prevailing frontier)
    (frontierNormalized : ∀ pair ∈ frontier,
      prevailing.apply pair.1 = pair.1)
    (currentPaired : GenerativitySurfaceObligation.currentPaired supply
      rawContext frontier ∈ generativityObligations)
    (coverage : ProtectedFreeCovered
      (rawContext.applySubst prevailing) frames prevailing)
    (contextCapFree : (rawContext.applySubst prevailing).fcv = [])
    (contextSuffix : ProtectedContextsSuffix rawContext frames)
    (postAdmissible : AdmissiblePost [] (SSubst.paired contextResidual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.var name) selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  let frame := state.stable.frame
  let activeFrame := frame.project active
  obtain ⟨scheme, lookup, schemeCapArity, realizes⟩ :=
    activeFrame.contexts found
  have selectedUse := realizes instantiation
  obtain ⟨opening, residual, opened, _images, postEq⟩ :=
    Scheme.normalized_valueFlowInst_pairedExtension_of_capArity_zero
      scheme contextResidual supply schemeCapArity selectedUse
  let post' := extendSchemeOpening (SSubst.paired contextResidual) supply
    scheme opening
  let rawTarget := (InferenceBase.instantiateScheme supply scheme).value
  let successor := (InferenceBase.instantiateScheme supply scheme).supply
  have schemeBounded := activeFrame.contextBounded.find? lookup
  have normalizedFixed :
      (rawContext.applySubst prevailing).applySubst prevailing =
        rawContext.applySubst prevailing := by
    rw [← Context.applySubst_seq,
      DemandTypingInferenceCompletenessTraversal.subst_seq_self_eq_of_idempotent
        prevailingIdempotent]
  have schemeFixed : scheme.applyMeta prevailing = scheme := by
    have lookupAfter := congrArg (Context.find? · name) normalizedFixed
    rw [Context.find?_applySubst, lookup] at lookupAfter
    exact Option.some.inj (by simpa using lookupAfter)
  have rawFixed : prevailing.apply rawTarget = rawTarget := by
    have transported :=
      DemandTypingInferenceCompletenessContext.instantiateScheme_applyMeta_bounded
        supply scheme prevailing prevailingBounded
    rw [schemeFixed] at transported
    exact transported.symm
  have targetEquation : post'.apply (prevailing.apply rawTarget) =
      selectedTarget.emb := by
    rw [rawFixed]
    exact canonicalSchemeOpening_relative_of_opened
      (SSubst.paired contextResidual) supply scheme schemeBounded opening opened
  have oldFrame : WProtectedFrameAt supply post' prevailing frames frontier :=
    frame.extendSchemeOpening opening
  have supplyExtends : SupplyExtends supply successor :=
    SupplyExtends.instantiateScheme supply scheme
  have rawBounded : rawTarget.BoundedBy successor :=
    Scheme.freshInstantiate_value_boundedBy schemeBounded
  have rawRetired : ∀ cut ∈ pending,
      cut.AvoidsTy signature prevailing (prevailing.apply rawTarget) := by
    intro cut cutMember
    rw [rawFixed]
    exact Scheme.freshInstantiate_value_avoids_of_lookup schemeCapArity lookup
      state.pendingBelow
      (fun retired retiredMember => state.contextsRetired retired retiredMember
        (rawContext, selectedContext) active) cut cutMember
  let derived : DemandSynth signature supply prevailing rawContext (.var name)
      rawTarget successor prevailing := DemandSynth.var lookup
  have resultFrame : WProtectedFrameAt successor post' prevailing frames
      ((prevailing.apply rawTarget, selectedTarget) :: frontier) := by
    refine
      { contexts := oldFrame.contexts
        types := WTypeFrame.cons targetEquation oldFrame.types
        contextsBounded := fun member =>
          (oldFrame.contextsBounded member).mono supplyExtends
        frontierBounded := ?_ }
    intro pair member
    rcases List.mem_cons.mp member with rfl | oldMember
    · rw [rawFixed]
      exact rawBounded
    · exact (oldFrame.frontierBounded pair oldMember).mono supplyExtends
  have postAdmissible' : AdmissiblePost [] post' :=
    AdmissiblePost.extendSchemeOpening_of_capArity_zero opening postAdmissible
      schemeCapArity
  have ledgerEq : DDLedger.markSchemeInstance [] supply scheme = [] :=
    DDLedger.markSchemeInstance_eq_self_of_capArity_zero [] supply scheme
      schemeCapArity
  let originMarked := DemandSynthOrigin.var (signature := signature)
    (q := supply) (S := prevailing) (context := rawContext)
    (ledger := []) lookup
  let OriginAudit := fun (ledger : CapabilityOriginLedger) =>
    ∃ origin : DemandSynthOrigin signature derived [] ledger,
      ∀ terminal, Nonempty (DemandSynthTerminalAudit terminal signature origin)
  let pkgMarked : OriginAudit (DDLedger.markSchemeInstance [] supply scheme) :=
    ⟨originMarked, fun _ =>
      ⟨DemandSynthTerminalAudit.var (lookup := lookup)⟩⟩
  let pkg : OriginAudit [] := ledgerEq ▸ pkgMarked
  obtain ⟨origin, audit⟩ := pkg
  let auditPlan : WSynthAuditPlan signature (origin := origin) :=
    WSynthAuditPlan.noCuts audit
  have related' : WContextRel post'
      (rawContext.applySubst prevailing) selectedContext :=
    WContextRel.extendSchemeOpening opening contextView.related
      (state.stable.frame.contextsBounded active)
  have finalContext : ErasedDMContextView residual selectedContext
      (rawContext.applySubst prevailing) := by
    refine ⟨?_⟩
    rw [← postEq]
    exact related'
  obtain ⟨algorithmTarget, targetView⟩ :=
    NormalizedDMTargetView.ofPairedEquation
      (residual := residual) (selectedTarget := selectedTarget)
      (coreTarget := prevailing.apply rawTarget) (by
        rw [← postEq]
        exact targetEquation)
  have extendedScope : ResidualContextScope
      (fun varId => eraseTy (post'.target varId))
      (rawContext.applySubst prevailing) selectedContext :=
    ResidualContextScope.extendCoreSchemeOpening opening contextScope
      (state.stable.frame.contextsBounded active)
  have finalScope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext := by
    intro algorithmVar selectedVar algorithmFree imageFree
    apply extendedScope algorithmFree
    have pointEq := congrFun (congrArg Subst.target postEq) algorithmVar
    change selectedVar ∈ (eraseTy (post'.target algorithmVar)).ftv
    rw [pointEq]
    simpa [SSubst.paired, SSubst.emb, eraseTy_emb] using imageFree
  have finalProtectedScopes : ProtectedResidualScopes residual prevailing
      frames := by
    intro pair member algorithmVar selectedVar algorithmFree imageFree
    have extended : ResidualContextScope
        (fun varId => eraseTy (post'.target varId))
        (pair.1.applySubst prevailing) pair.2 :=
      ResidualContextScope.extendCoreSchemeOpening opening
        (protectedScopes pair member)
        (state.stable.frame.contextsBounded member)
    apply extended algorithmFree
    have pointEq := congrFun (congrArg Subst.target postEq) algorithmVar
    change selectedVar ∈ (eraseTy (post'.target algorithmVar)).ftv
    rw [pointEq]
    simpa [SSubst.paired, SSubst.emb, eraseTy_emb] using imageFree
  have rawProtected : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (prevailing.apply rawTarget) := by
    rw [rawFixed]
    exact Scheme.freshInstantiate_value_oldFree_of_lookup_owner
      schemeCapArity lookup contextOld floorCaps floorTargets
  have targetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst prevailing)
        (prevailing.apply rawTarget) := by
    intro obligation obligationMember
    rw [rawFixed]
    exact Scheme.freshInstantiate_value_oldFree_of_lookup_owner
      schemeCapArity lookup (generativityContexts obligation obligationMember)
      (generativityValid obligation obligationMember).1.1
      (generativityValid obligation obligationMember).1.2
  have localOldFree : OldFreeInContextAt supply
      (rawContext.applySubst prevailing) (prevailing.apply rawTarget) :=
    targetGenerative _ currentObligation
  let complete : WCompleteWitness signature supply prevailing rawContext
      (.var name) selectedTarget frames frontier pending :=
    { successor := successor
      prevailing' := prevailing
      rawTarget := rawTarget
      post := post'
      frontier := (prevailing.apply rawTarget, selectedTarget) :: frontier
      derived := derived
      origin := origin
      auditPlan := auditPlan
      pending := pending
      stability := state.stable.lets
      retains := fun _ member => member
      auditCuts := by simp [auditPlan, WSynthAuditPlan.noCuts]
      postAdmissible := postAdmissible'
      prevailingBounded := prevailingBounded.mono supplyExtends
      prevailingIdempotent := prevailingIdempotent
      frame := resultFrame
      retired := by
        intro cut cutMember pair pairMember
        rcases List.mem_cons.mp pairMember with rfl | oldMember
        · exact rawRetired cut cutMember
        · exact state.retired cut cutMember pair oldMember
      contextsRetired := state.contextsRetired
      pendingBelow := PendingLetsBelow.mono state.pendingBelow supplyExtends
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (by simpa only [Subst.apply_id] using member)
      targetMember := List.mem_cons_self }
  let normalizedWitness : WNormalizedCompleteWitness signature supply
      prevailing rawContext (.var name) selectedContext selectedTarget
      InferenceBase.FreshSupply.empty [] [] []
      generativityObligations frames frontier pending :=
    { complete := complete
      algorithmContext := []
      algorithmTarget := algorithmTarget
      residual := residual
      post_eq := postEq
      context := finalContext
      scope := finalScope
      protectedScopes := finalProtectedScopes
      target := targetView
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
        InferenceBase.FreshSupply.empty [] Subst.id
      provenanceRetains := by intro algorithm selected member; cases member
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetGenerative := targetGenerative
      localOldFree := localOldFree
      protectedCovered := coverage
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
      targetOld := rawProtected
      provenanceSuffix := provenanceSuffix
      provenanceCovered := provenanceCovered
      retainedOuter := retainedOuter
      provenanceRetains := fun algorithm selected member =>
        List.mem_cons_of_mem _ (by
          change (Subst.id.apply algorithm, selected) ∈ frontier
          rw [Subst.apply_id]
          exact provenanceRetains algorithm selected member)
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

end DM
end TypePM
