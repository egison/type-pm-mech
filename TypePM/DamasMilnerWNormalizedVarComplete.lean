import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerWNormalizedOpening
import TypePM.DamasMilnerWNormalizedVarFresh

/-!
# Normalized variable completeness

This module refines the variable base case with a one-sort-normalized scheme
opening.  Keeping it separate avoids making the raw completeness theorem
depend on the stronger Damas--Milner invariant.
-/

namespace TypePM
namespace DM

/-- Variable base case whose final post is definitionally represented by a
one-sort residual. -/
theorem Typing.w_normalized_var
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {name : String}
    {selectedScheme : SScheme} {selectedTarget : STy}
    {pending : List PendingLetCut}
    {algorithmContext : SCtx} {contextResidual : SSubst}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired contextResidual) prevailing frames frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (contextView : NormalizedDMContextView contextResidual algorithmContext
      selectedContext (rawContext.applySubst prevailing))
    (contextScope : ResidualContextScope contextResidual
      (rawContext.applySubst prevailing) selectedContext)
    (protectedScopes : ProtectedResidualScopes contextResidual prevailing frames)
    (protectedCovered : ProtectedFreeCovered
      (rawContext.applySubst prevailing) frames prevailing)
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    (generativity : GenerativitySurfaceFrameAt generativityObligations prevailing)
    (generativityValid : GenerativitySurfaceValid supply rawContext
      generativityObligations)
    (generativityContexts : GenerativitySurfaceContextsAt generativityObligations
      prevailing (rawContext.applySubst prevailing))
    (currentObligation : GenerativitySurfaceObligation.current supply
      rawContext ∈ generativityObligations)
    (retainedOuter : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id provenanceFrontier)
    (provenanceMembers : ∀ pair, pair ∈ provenanceFrontier → pair ∈ frontier)
    (floorCaps : provenanceFloor.nextCap ≤ supply.nextCap)
    (floorTargets : provenanceFloor.nextTy ≤ supply.nextTy)
    (protectedOld : ProtectedOldFreeAt provenanceFloor
      (provenanceContext.applySubst prevailing) frontier)
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
    (postAdmissible : AdmissiblePost [] (SSubst.paired contextResidual))
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget) :
    WNormalizedCompleteResult signature supply prevailing rawContext
      (.var name) selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending := by
  let frame := state.stable.frame
  let activeFrame := frame.project active
  obtain ⟨scheme, lookup, schemeCapArity, realizes⟩ :=
    activeFrame.contexts found
  have algorithmLookup : ∃ algorithmScheme,
      algorithmContext.find? name = some algorithmScheme ∧
        scheme = algorithmScheme.emb := by
    rw [contextView.normalized_eq] at lookup
    rw [SCtx.find?_emb_eq] at lookup
    cases foundAlgorithm : algorithmContext.find? name with
    | none => simp [foundAlgorithm] at lookup
    | some algorithmScheme =>
        exact ⟨algorithmScheme, rfl,
          (Option.some.inj (by simpa [foundAlgorithm] using lookup)).symm⟩
  obtain ⟨algorithmScheme, algorithmFound, schemeEq⟩ := algorithmLookup
  have selectedUse := realizes instantiation
  rw [schemeEq] at selectedUse
  obtain ⟨opening, residual, opened, images, postEq⟩ :=
    algorithmScheme.normalized_valueFlowInst_pairedExtension
      contextResidual supply selectedUse
  let post' := extendSchemeOpening (SSubst.paired contextResidual) supply
    algorithmScheme.emb opening
  let rawTarget :=
    (InferenceBase.instantiateScheme supply algorithmScheme.emb).value
  let successor :=
    (InferenceBase.instantiateScheme supply algorithmScheme.emb).supply
  have schemeBounded := activeFrame.contextBounded.find? lookup
  rw [schemeEq] at schemeBounded
  have normalizedFixed :
      (rawContext.applySubst prevailing).applySubst prevailing =
        rawContext.applySubst prevailing := by
    rw [← Context.applySubst_seq,
      DemandTypingInferenceCompletenessTraversal.subst_seq_self_eq_of_idempotent
        prevailingIdempotent]
  have schemeFixed : algorithmScheme.emb.applyMeta prevailing =
      algorithmScheme.emb := by
    have lookupAfter := congrArg (Context.find? · name) normalizedFixed
    rw [Context.find?_applySubst, lookup, schemeEq] at lookupAfter
    exact Option.some.inj (by simpa using lookupAfter)
  have rawFixed : prevailing.apply rawTarget = rawTarget := by
    have transported :=
      DemandTypingInferenceCompletenessContext.instantiateScheme_applyMeta_bounded
        supply algorithmScheme.emb prevailing prevailingBounded
    rw [schemeFixed] at transported
    exact transported.symm
  have normalizedLookup :
      (rawContext.applySubst prevailing).find? name =
        some algorithmScheme.emb := by
    rw [contextView.normalized_eq]
    exact SCtx.find?_emb algorithmFound
  have rawOld : OldFreeInContextAt supply
      (rawContext.applySubst prevailing) (prevailing.apply rawTarget) := by
    rw [rawFixed]
    exact Scheme.freshInstantiate_value_oldFree_of_lookup
      (scheme := algorithmScheme.emb)
      (by simpa [schemeEq] using schemeCapArity) normalizedLookup
  have ownerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (prevailing.apply rawTarget) := by
    constructor
    · intro varId free below
      exact contextOld.caps varId
        (rawOld.caps varId free (Nat.lt_of_lt_of_le below floorCaps)) below
    · intro varId free below
      exact contextOld.targets varId
        (rawOld.targets varId free
          (Nat.lt_of_lt_of_le below floorTargets)) below
  have rawRetired : ∀ cut ∈ pending,
      cut.AvoidsTy signature prevailing (prevailing.apply rawTarget) := by
    have canonicalFresh :=
      algorithmScheme.canonicalTarget_avoids_of_lookup normalizedLookup
        state.pendingBelow
        (fun cut member => state.contextsRetired cut member
          (rawContext, selectedContext) active)
    intro cut cutMember
    rw [rawFixed]
    change cut.AvoidsTy signature prevailing
      (InferenceBase.instantiateScheme supply algorithmScheme.emb).value
    rw [algorithmScheme.canonicalTarget_emb]
    exact canonicalFresh cut cutMember
  have targetEquation : post'.apply (prevailing.apply rawTarget) =
      selectedTarget.emb := by
    rw [rawFixed]
    exact canonicalSchemeOpening_relative_of_opened
      (SSubst.paired contextResidual) supply algorithmScheme.emb
      schemeBounded opening opened
  have oldFrame : WProtectedFrameAt supply post' prevailing frames frontier :=
    frame.extendSchemeOpening opening
  have supplyExtends : SupplyExtends supply successor :=
    SupplyExtends.instantiateScheme supply algorithmScheme.emb
  have rawBounded : rawTarget.BoundedBy successor :=
    Scheme.freshInstantiate_value_boundedBy schemeBounded
  let derived : DemandSynth signature supply prevailing rawContext (.var name)
      rawTarget successor prevailing := DemandSynth.var (schemeEq ▸ lookup)
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
  have postAdmissible' : AdmissiblePost [] post' := by
    exact AdmissiblePost.extendSchemeOpening_of_capArity_zero opening
      postAdmissible (by simpa [schemeEq] using schemeCapArity)
  have ledgerEq :
      DDLedger.markSchemeInstance [] supply algorithmScheme.emb = [] :=
    DDLedger.markSchemeInstance_eq_self_of_capArity_zero
      [] supply algorithmScheme.emb (by simp [SScheme.emb, Scheme.close])
  let originMarked := DemandSynthOrigin.var (signature := signature)
    (q := supply) (S := prevailing) (context := rawContext)
    (ledger := []) (schemeEq ▸ lookup)
  let OriginAudit := fun (ledger : CapabilityOriginLedger) =>
    ∃ origin : DemandSynthOrigin signature derived [] ledger,
      ∀ terminal,
        Nonempty (DemandSynthTerminalAudit terminal signature origin)
  let pkgMarked : OriginAudit
      (DDLedger.markSchemeInstance [] supply algorithmScheme.emb) :=
    ⟨originMarked, fun _ =>
      ⟨DemandSynthTerminalAudit.var (lookup := schemeEq ▸ lookup)⟩⟩
  let pkg : OriginAudit [] := ledgerEq ▸ pkgMarked
  obtain ⟨origin, audit⟩ := pkg
  let auditPlan : WSynthAuditPlan signature (origin := origin) :=
    WSynthAuditPlan.noCuts audit
  have algorithmContextBounded : algorithmContext.emb.BoundedBy supply := by
    rw [← contextView.normalized_eq]
    exact activeFrame.contextBounded
  have relatedBase : WContextRel (SSubst.paired contextResidual)
      algorithmContext.emb selectedContext := by
    rw [← contextView.normalized_eq]
    exact contextView.related
  have related' : WContextRel post' algorithmContext.emb selectedContext :=
    WContextRel.extendSchemeOpening opening relatedBase algorithmContextBounded
  have normalizedContext' : NormalizedDMContextView residual algorithmContext
      selectedContext (rawContext.applySubst prevailing) := by
    refine ⟨contextView.normalized_eq, ?_⟩
    rw [contextView.normalized_eq]
    rw [← postEq]
    exact related'
  have normalizedTarget' : NormalizedDMTargetView residual
      (algorithmScheme.canonicalTarget supply.nextTy) selectedTarget
      (prevailing.apply rawTarget) := by
    have normalizedEq : prevailing.apply rawTarget =
        (algorithmScheme.canonicalTarget supply.nextTy).emb := by
      rw [rawFixed]
      exact algorithmScheme.canonicalTarget_emb supply
    refine ⟨normalizedEq, ?_⟩
    · have embedded : (SSubst.paired residual).apply
          (algorithmScheme.canonicalTarget supply.nextTy).emb =
            selectedTarget.emb := by
        rw [← postEq, ← normalizedEq]
        exact targetEquation
      rw [SSubst.paired_apply_emb] at embedded
      exact STy.emb_injective embedded
  have extendedScope : ResidualContextScope
      (fun varId => eraseTy
        ((extendSchemeOpening (SSubst.paired contextResidual) supply
          algorithmScheme.emb opening).target varId))
      (rawContext.applySubst prevailing) selectedContext :=
    ResidualContextScope.extendSchemeOpening
      (base := contextResidual) opening contextScope
      (state.stable.frame.contextsBounded active)
  have finalScope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext := by
    intro algorithmVar selectedVar algorithmFree imageFree
    apply extendedScope algorithmFree
    have targetEq := congrArg Subst.target postEq
    have pointEq := congrFun targetEq algorithmVar
    have erasedEq : eraseTy
        ((extendSchemeOpening (SSubst.paired contextResidual) supply
          algorithmScheme.emb opening).target algorithmVar) =
        residual algorithmVar := by
      rw [pointEq]
      simp [SSubst.paired, SSubst.emb, eraseTy_emb]
    change selectedVar ∈
      (eraseTy ((extendSchemeOpening (SSubst.paired contextResidual) supply
        algorithmScheme.emb opening).target algorithmVar)).ftv
    rw [erasedEq]
    exact imageFree
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
  exact ⟨
    { complete := complete
      algorithmContext := algorithmContext
      algorithmTarget := algorithmScheme.canonicalTarget supply.nextTy
      residual := residual
      post_eq := postEq
      context := ⟨normalizedContext'.related⟩
      scope := finalScope
      protectedScopes := by
        intro pair member
        have extended : ResidualContextScope
            (fun varId => eraseTy
              ((extendSchemeOpening (SSubst.paired contextResidual) supply
                algorithmScheme.emb opening).target varId))
            (pair.1.applySubst prevailing) pair.2 :=
          ResidualContextScope.extendSchemeOpening
            (base := contextResidual) opening (protectedScopes pair member)
            (state.stable.frame.contextsBounded member)
        intro algorithmVar selectedVar algorithmFree imageFree
        apply extended algorithmFree
        have targetEq := congrArg Subst.target postEq
        have pointEq := congrFun targetEq algorithmVar
        have erasedEq : eraseTy
            ((extendSchemeOpening (SSubst.paired contextResidual) supply
              algorithmScheme.emb opening).target algorithmVar) =
            residual algorithmVar := by
          rw [pointEq]
          simp [SSubst.paired, SSubst.emb, eraseTy_emb]
        change selectedVar ∈
          (eraseTy ((extendSchemeOpening (SSubst.paired contextResidual) supply
            algorithmScheme.emb opening).target algorithmVar)).ftv
        rw [erasedEq]
        exact imageFree
      target := normalizedTarget'
      floorCaps := floorCaps
      floorTargets := floorTargets
      contextOld := contextOld
      contextProvenanceSuffix := contextProvenanceSuffix
      protectedOld := protectedOld.cons ownerOld
      provenanceCovered := provenanceCovered
      provenanceIncluded := provenanceIncluded
      provenanceSuffix := provenanceSuffix
      retainedOuter := retainedOuter
      provenanceRetains := by
        intro algorithm selected member
        dsimp [complete]
        rw [Subst.apply_id]
        exact List.mem_cons_of_mem _
          (provenanceMembers (algorithm, selected) member)
      generativity := generativity
      generativityContexts := generativityContexts
      generativityValid := generativityValid
      currentObligation := currentObligation
      targetGenerative := by
        intro obligation obligationMember
        rw [rawFixed]
        exact Scheme.freshInstantiate_value_oldFree_of_lookup_owner
          (scheme := algorithmScheme.emb)
          (by simpa [schemeEq] using schemeCapArity) normalizedLookup
          (generativityContexts obligation obligationMember)
          (generativityValid obligation obligationMember).1.1
          (generativityValid obligation obligationMember).1.2
      localOldFree := by
        rw [rawFixed]
        exact Scheme.freshInstantiate_value_oldFree_of_lookup
          (scheme := algorithmScheme.emb)
          (by simpa [schemeEq] using schemeCapArity) normalizedLookup
      protectedCovered := protectedCovered
      contextSuffix := contextSuffix
      pendingCapFree := pendingCapFree }
    ⟩

end DM
end TypePM
