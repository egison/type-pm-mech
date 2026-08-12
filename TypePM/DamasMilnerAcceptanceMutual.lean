import TypePM.DamasMilnerAcceptanceCompleteness
import TypePM.DamasMilnerWNormalizedStructuralComplete
import TypePM.DamasMilnerWNormalizedErasedVarComplete
import TypePM.DamasMilnerWNormalizedErasedLamComplete
import TypePM.DamasMilnerWConstructorCompletion
import TypePM.DamasMilnerWLetRegistration
import TypePM.DamasMilnerWPairedFixCompletion

/-!
# Mutual normalized Algorithm W driver

Every expression and list constructor is closed here by mutual induction,
including application, generalized let, and direct-self fix. Context state is
carried by the cut-stable erased view, with no syntactic context reification
premise and no constructor callback.
-/

namespace TypePM
namespace DM

def NormalizedWComplete (selectedContext : SCtx) (expression : Expr)
    (selectedTarget : STy) : Prop :=
  ∀ {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {residual : SSubst}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation},
    signature.SchemesClosed →
    WRetiredStableFrameAt signature supply (SSubst.paired residual)
        prevailing frames frontier pending →
    (rawContext, selectedContext) ∈ frames →
    ErasedDMContextView residual selectedContext
        (rawContext.applySubst prevailing) →
    ResidualContextScope residual (rawContext.applySubst prevailing)
        selectedContext →
    ProtectedResidualScopes residual prevailing frames →
    (rawContext.applySubst prevailing).fcv = [] →
    provenanceFloor.nextCap ≤ supply.nextCap →
    provenanceFloor.nextTy ≤ supply.nextTy →
    OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) →
    ProvenanceContextSuffix provenanceContext rawContext →
    ProvenanceContextIncluded (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) →
    ProtectedContextsSuffix provenanceContext provenanceFrames →
    ProtectedFreeCovered (provenanceContext.applySubst prevailing)
      provenanceFrames prevailing →
    RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id
      provenanceFrontier →
    (∀ algorithm selected, (algorithm, selected) ∈ provenanceFrontier →
      (algorithm, selected) ∈ frontier) →
    GenerativitySurfaceFrameAt generativityObligations prevailing →
    GenerativitySurfaceRetainedAt generativityObligations prevailing →
    GenerativitySurfaceMembersAt generativityObligations prevailing frontier →
    (∀ pair ∈ frontier, prevailing.apply pair.1 = pair.1) →
    GenerativitySurfaceContextsAt generativityObligations prevailing
      (rawContext.applySubst prevailing) →
    GenerativitySurfaceValid supply rawContext generativityObligations →
    GenerativitySurfaceObligation.current supply rawContext ∈
      generativityObligations →
    GenerativitySurfaceObligation.currentPaired supply rawContext frontier ∈
      generativityObligations →
    ProtectedFreeCovered (rawContext.applySubst prevailing) frames
        prevailing →
    ProtectedContextsSuffix rawContext frames →
    AdmissiblePost [] (SSubst.paired residual) →
    prevailing.BoundedBy supply → prevailing.Idempotent →
    PendingLetsCapFree prevailing pending →
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      expression selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending

def NormalizedWCompletes (selectedContext : SCtx)
    (expressions : List Expr) (selectedTargets : List STy) : Prop :=
  ∀ {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {residual : SSubst}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation},
    signature.SchemesClosed →
    WRetiredStableFrameAt signature supply (SSubst.paired residual)
        prevailing frames frontier pending →
    (rawContext, selectedContext) ∈ frames →
    ErasedDMContextView residual selectedContext
        (rawContext.applySubst prevailing) →
    ResidualContextScope residual (rawContext.applySubst prevailing)
        selectedContext →
    ProtectedResidualScopes residual prevailing frames →
    (rawContext.applySubst prevailing).fcv = [] →
    provenanceFloor.nextCap ≤ supply.nextCap →
    provenanceFloor.nextTy ≤ supply.nextTy →
    OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) →
    ProvenanceContextSuffix provenanceContext rawContext →
    ProvenanceContextIncluded (provenanceContext.applySubst prevailing)
      (rawContext.applySubst prevailing) →
    ProtectedContextsSuffix provenanceContext provenanceFrames →
    ProtectedFreeCovered (provenanceContext.applySubst prevailing)
      provenanceFrames prevailing →
    RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst prevailing) Subst.id
      provenanceFrontier →
    (∀ algorithm selected, (algorithm, selected) ∈ provenanceFrontier →
      (algorithm, selected) ∈ frontier) →
    GenerativitySurfaceFrameAt generativityObligations prevailing →
    GenerativitySurfaceRetainedAt generativityObligations prevailing →
    GenerativitySurfaceMembersAt generativityObligations prevailing frontier →
    (∀ pair ∈ frontier, prevailing.apply pair.1 = pair.1) →
    GenerativitySurfaceContextsAt generativityObligations prevailing
      (rawContext.applySubst prevailing) →
    GenerativitySurfaceValid supply rawContext generativityObligations →
    GenerativitySurfaceObligation.current supply rawContext ∈
      generativityObligations →
    GenerativitySurfaceObligation.currentPaired supply rawContext frontier ∈
      generativityObligations →
    ProtectedFreeCovered (rawContext.applySubst prevailing) frames
        prevailing →
    ProtectedContextsSuffix rawContext frames →
    AdmissiblePost [] (SSubst.paired residual) →
    prevailing.BoundedBy supply → prevailing.Idempotent →
    PendingLetsCapFree prevailing pending →
    WPairedNormalizedTypingsResult signature supply prevailing rawContext
      expressions selectedContext selectedTargets provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames frontier pending

mutual

theorem Typing.w_paired_normalized_mutual :
    ∀ {context expression target}, Typing context expression target →
      NormalizedWComplete context expression target
  | _, _, _, .var found instantiation => by
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      exact Typing.w_paired_erased_normalized_var state active erased scope
        protectedScopes floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter
        provenanceRetains generativity generativityContexts generativityValid
        currentObligation surfacesRetained surfacesMembers frontierNormalized
        currentPaired coverage contextCapFree contextSuffix admissible bounded idempotent
        capFree found instantiation
  | context, .lam name body, .fn domain codomain, .lam bodyTyping => by
      rename_i signature supply prevailing rawContext frames frontier pending
        residual provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      have bodyIH : NormalizedWComplete
          ((name, SScheme.mono domain) :: context) body codomain :=
        Typing.w_paired_normalized_mutual bodyTyping
      apply Typing.w_paired_erased_normalized_lam state active erased scope
        contextCapFree admissible bounded capFree
      intro prepared preparedView preparedAdmissible preparedCapFree
        preparedScope
      have freshFixed : prevailing.apply (.var supply.nextTy) =
          .var supply.nextTy := Subst.BoundedBy.apply_freshTarget bounded
      let extendedRaw :=
        (name, Scheme.mono (.var supply.nextTy)) :: rawContext
      let childSupply := { supply with nextTy := supply.nextTy + 1 }
      let preparedFrontier := (.var supply.nextTy, domain) :: frontier
      let protectedObligations :=
        GenerativitySurfaceObligations.protectToken
          (.var supply.nextTy) generativityObligations
      let shadowObligation := lambdaShadowObligation provenanceFloor
        provenanceContext provenanceFrontier (.var supply.nextTy)
      let shadowedObligations := shadowObligation :: protectedObligations
      let rawObligations :=
        GenerativitySurfaceObligation.current childSupply extendedRaw ::
          shadowedObligations
      let childObligations :=
        GenerativitySurfaceObligation.currentPaired childSupply extendedRaw
            preparedFrontier :: rawObligations
      have preparedProtectedScopes : ProtectedResidualScopes
          (SSubst.extendFreshTarget residual supply.nextTy domain) prevailing
          ((extendedRaw, (name, SScheme.mono domain) :: context) :: frames) := by
        apply ProtectedResidualScopes.cons preparedScope
        intro pair member
        exact ResidualContextScope.extendFreshTarget
          (protectedScopes pair member)
          (state.stable.frame.contextsBounded member) domain
      have preparedContextSuffix : ProtectedContextsSuffix extendedRaw
          ((extendedRaw, (name, SScheme.mono domain) :: context) :: frames) :=
        contextSuffix.consActive name (Scheme.mono (.var supply.nextTy))
          ((name, SScheme.mono domain) :: context)
      have preparedCoverage : ProtectedFreeCovered
          (Context.applySubst prevailing extendedRaw)
          ((extendedRaw, (name, SScheme.mono domain) :: context) :: frames)
          prevailing := preparedContextSuffix.toProtectedFreeCovered prevailing
      have freshForObligations : ∀ obligation ∈ generativityObligations,
          OldFreeInContextAt obligation.floor
            (obligation.owner.applySubst prevailing)
            (prevailing.apply (.var supply.nextTy)) := by
        intro obligation member
        rw [freshFixed]
        exact OldFreeInContextAt.var obligation.floor _ supply.nextTy
          (generativityValid obligation member).1.2
      have shadowGenerativity : GenerativitySurfaceFrameAt
          shadowedObligations prevailing := by
        intro obligation member raw rawMember
        rcases List.mem_cons.mp member with rfl | old
        · simp [shadowObligation, lambdaShadowObligation] at rawMember
          subst raw
          rw [freshFixed]
          exact OldFreeInContextAt.var provenanceFloor _ supply.nextTy
            floorTargets
        · exact (generativity.protectToken freshForObligations)
            obligation old raw rawMember
      have childGenerativityRaw : GenerativitySurfaceFrameAt rawObligations
          prevailing := shadowGenerativity.registerEmpty childSupply extendedRaw
      have childGenerativity : GenerativitySurfaceFrameAt childObligations
          prevailing := childGenerativityRaw.registerPaired childSupply
            extendedRaw preparedFrontier
      have shadowContexts : GenerativitySurfaceContextsAt shadowedObligations
          prevailing (Context.applySubst prevailing extendedRaw) := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | old
        · simpa [shadowObligation, lambdaShadowObligation, extendedRaw,
            Context.applySubst, freshFixed] using
            contextOld.consFreshTargetAbove floorTargets
        · obtain ⟨oldObligation, oldMember, rfl⟩ := List.mem_map.mp old
          simpa [GenerativitySurfaceObligation.protectToken, extendedRaw,
            Context.applySubst, freshFixed] using
            (generativityContexts oldObligation oldMember).consFreshTargetAbove
              (generativityValid oldObligation oldMember).1.2
      have childContextsRaw : GenerativitySurfaceContextsAt rawObligations
          prevailing (Context.applySubst prevailing extendedRaw) :=
        shadowContexts.registerCurrent childSupply
      have childContexts : GenerativitySurfaceContextsAt childObligations
          prevailing (Context.applySubst prevailing extendedRaw) :=
        childContextsRaw.registerCurrentPaired childSupply preparedFrontier
      have shadowValid : GenerativitySurfaceValid childSupply extendedRaw
          shadowedObligations := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | old
        · exact ⟨⟨Nat.le_trans floorCaps (by simp [childSupply]),
              Nat.le_trans floorTargets (by simp [childSupply])⟩,
            rawSuffix.consActive name (Scheme.mono (.var supply.nextTy))⟩
        · obtain ⟨oldObligation, oldMember, rfl⟩ := List.mem_map.mp old
          exact ⟨(generativityValid oldObligation oldMember).1.trans
              (SupplyExtends.bumpTy supply 1),
            (generativityValid oldObligation oldMember).2.consActive name
              (Scheme.mono (.var supply.nextTy))⟩
      have childValidRaw : GenerativitySurfaceValid childSupply extendedRaw
          rawObligations := shadowValid.registerCurrent
      have childValid : GenerativitySurfaceValid childSupply extendedRaw
          childObligations := childValidRaw.registerCurrentPaired
            preparedFrontier
      have preparedFrontierNormalized : ∀ pair ∈ preparedFrontier,
          prevailing.apply pair.1 = pair.1 := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | oldMember
        · exact freshFixed
        · exact frontierNormalized pair oldMember
      have protectedRetained : GenerativitySurfaceRetainedAt
          protectedObligations prevailing := surfacesRetained.protectToken
      have protectedMembers : GenerativitySurfaceMembersAt
          protectedObligations prevailing preparedFrontier := by
        apply GenerativitySurfaceMembersAt.protectToken
        intro obligation member pair pairMember
        exact List.mem_cons_of_mem _
          (surfacesMembers obligation member pair pairMember)
      have shadowRetained : GenerativitySurfaceRetainedAt shadowedObligations
          prevailing := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | old
        · constructor
          · intro pair pairMember varId free
            have surfaceMember := provenanceRetains pair.1 pair.2 pairMember
            have fixed := frontierNormalized pair surfaceMember
            exact retainedOuter.caps pair pairMember varId (by
              rw [Subst.apply_id]
              simpa [fixed] using free)
          · intro pair pairMember varId free
            have surfaceMember := provenanceRetains pair.1 pair.2 pairMember
            have fixed := frontierNormalized pair surfaceMember
            exact retainedOuter.targets pair pairMember varId (by
              rw [Subst.apply_id]
              simpa [fixed] using free)
        · exact protectedRetained obligation old
      have rawRetained : GenerativitySurfaceRetainedAt rawObligations
          prevailing :=
        GenerativitySurfaceRetainedAt.registerCurrent
          (RetainedOldOrContextAt.nil childSupply
            (Context.applySubst prevailing extendedRaw) prevailing)
          shadowRetained
      have shadowMembers : GenerativitySurfaceMembersAt shadowedObligations
          prevailing preparedFrontier := by
        intro obligation member pair pairMember
        rcases List.mem_cons.mp member with rfl | old
        · have member := provenanceRetains pair.1 pair.2 pairMember
          have fixed := frontierNormalized pair member
          simpa [preparedFrontier, fixed] using List.mem_cons_of_mem
            ((.var supply.nextTy), domain) member
        · exact protectedMembers obligation old pair pairMember
      have rawMembers : GenerativitySurfaceMembersAt rawObligations prevailing
          preparedFrontier :=
        GenerativitySurfaceMembersAt.registerCurrent
          (fun pair member => by simp at member) shadowMembers
      have childRetained : GenerativitySurfaceRetainedAt childObligations
          prevailing := by
        apply GenerativitySurfaceRetainedAt.registerCurrentOfBounded
          (tail := rawRetained)
        intro pair member
        exact (bounded.mono (SupplyExtends.bumpTy supply 1)).apply
          (prepared.stable.frame.frontierBounded pair member)
      have childMembers : GenerativitySurfaceMembersAt childObligations
          prevailing preparedFrontier :=
        GenerativitySurfaceMembersAt.registerCurrent
          (fun pair member => by
            rw [preparedFrontierNormalized pair member]
            exact member)
          rawMembers
      have bodyResult := bodyIH signatureClosed prepared List.mem_cons_self
        preparedView preparedScope preparedProtectedScopes
        (by
          rw [show Context.applySubst prevailing extendedRaw =
            (name, (Scheme.mono (.var supply.nextTy)).applyMeta prevailing) ::
              rawContext.applySubst prevailing by
            simp [extendedRaw, Context.applySubst]]
          rw [Context.fcv, List.flatMap_cons, List.append_eq_nil_iff]
          exact ⟨by
            rw [Scheme.applyMeta_mono, freshFixed, Scheme.mono]
            simp [Scheme.fcv, PolyTy.fcv_lift, Ty.fcv], contextCapFree⟩)
        floorCaps
        (Nat.le_trans floorTargets (Nat.le_succ _))
        (by simpa [extendedRaw, Context.applySubst, freshFixed] using
          contextOld.consFreshTargetAbove floorTargets)
        (rawSuffix.consActive name (Scheme.mono (.var supply.nextTy)))
        (by simpa [extendedRaw, Context.applySubst, freshFixed] using
          included.consActive name (Scheme.mono (.var supply.nextTy)))
        provenanceSuffix provenanceCovered retainedOuter
        (fun algorithm selected member =>
          List.mem_cons_of_mem _ (provenanceRetains algorithm selected member))
        childGenerativity childRetained childMembers
        preparedFrontierNormalized childContexts childValid
        (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
        preparedCoverage preparedContextSuffix preparedAdmissible
        (bounded.mono (SupplyExtends.bumpTy supply 1)) idempotent
        preparedCapFree
      rcases bodyResult with ⟨bodyWitness⟩
      have domainMemberFinal :
          (bodyWitness.normalized.complete.prevailing'.apply
              (.var supply.nextTy), domain) ∈
            bodyWitness.normalized.complete.frontier := by
        have retained := bodyWitness.normalized.complete.frontierRetains _ _
          List.mem_cons_self
        rw [bodyWitness.normalized.complete.prevailing_eq, Subst.seq_apply,
          freshFixed]
        exact retained
      obtain ⟨algorithmDomain, domainView⟩ :=
        NormalizedDMTargetView.ofPairedEquation (by
          rw [← bodyWitness.normalized.post_eq]
          exact bodyWitness.normalized.complete.frame.types domainMemberFinal)
      let protectedCurrent :=
        (GenerativitySurfaceObligation.current supply rawContext).protectToken
          (.var supply.nextTy)
      have protectedCurrentMember : protectedCurrent ∈ childObligations := by
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨_, currentObligation, rfl⟩
      have functionLocalOld : OldFreeInContextAt supply
          (rawContext.applySubst bodyWitness.normalized.complete.prevailing')
          (bodyWitness.normalized.complete.prevailing'.apply
            (.fn (.var supply.nextTy)
              bodyWitness.normalized.complete.rawTarget)) := by
        rw [Subst.apply_fn]
        apply OldFreeInContextAt.fn
        · exact bodyWitness.normalized.generativity.token protectedCurrentMember
            List.mem_cons_self
        · exact bodyWitness.normalized.targetGenerative protectedCurrent
            protectedCurrentMember
      exact ⟨
        { body :=
            { result := bodyWitness.normalized
              algorithmDomain := algorithmDomain
              outer := ⟨by
                rw [← bodyWitness.normalized.post_eq]
                exact bodyWitness.normalized.complete.frame.contexts
                  (List.mem_cons_of_mem _ active)⟩
              domainView := domainView
              outerScope := bodyWitness.normalized.protectedScopes _
                (List.mem_cons_of_mem _ active)
              floorCapsOuter := floorCaps
              floorTargetsOuter := floorTargets
              contextOldOuter := by
                simpa [extendedRaw, Context.applySubst] using
                  bodyWitness.contextOld.dropActiveHead
              contextProvenanceSuffixOuter := rawSuffix
              provenanceIncludedOuter := rawSuffix.toIncluded _
              protectedCoveredOuter := contextSuffix.toProtectedFreeCovered _
              contextSuffixOuter := contextSuffix
              contextCapFreeOuter := by
                have bodyCapFree := bodyWitness.contextCapFree
                rw [show Context.applySubst
                    bodyWitness.normalized.complete.prevailing' extendedRaw =
                  (name, (Scheme.mono (.var supply.nextTy)).applyMeta
                    bodyWitness.normalized.complete.prevailing') ::
                    rawContext.applySubst
                      bodyWitness.normalized.complete.prevailing' by
                  simp [extendedRaw, Context.applySubst]] at bodyCapFree
                simp only [Context.fcv, List.flatMap_cons,
                  List.append_eq_nil_iff] at bodyCapFree
                exact bodyCapFree.2
              provenanceSuffixOuter := bodyWitness.provenanceSuffix
              provenanceFrontierNormalizedOuter := by
                intro pair member
                exact frontierNormalized pair
                  (provenanceRetains pair.1 pair.2 member)
              generativityValidOuter := generativityValid
              currentObligationOuter := currentObligation
              localOldFreeOuter := functionLocalOld }
          surfacesRetained := bodyWitness.surfacesRetained
          surfacesMembers := bodyWitness.surfacesMembers
          frontierNormalized := bodyWitness.frontierNormalized
          currentPairedOuter := currentPaired
          inputFrontierNormalizedOuter := frontierNormalized } ⟩
  | context, .app function argument, codomain,
      .app (domain := domain) functionTyping argumentTyping => by
      rename_i signature supply prevailing rawContext frames frontier pending
        residual provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      have functionResult := Typing.w_paired_normalized_mutual
        functionTyping signatureClosed state active erased scope protectedScopes
        contextCapFree floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      rcases functionResult with ⟨functionResult⟩
      apply Typing.w_paired_normalized_app functionResult active signatureClosed
      intro prepared _functionAligned childContextCapFree childGenerativity
        childContexts childValid childRetained childMembers
      apply Typing.w_paired_normalized_mutual argumentTyping
        (provenanceFloor := InferenceBase.FreshSupply.empty)
        (provenanceContext := []) (provenanceFrames := [])
        (provenanceFrontier := [])
        signatureClosed prepared.state active prepared.context prepared.scope
        prepared.protectedScopes childContextCapFree
        (by simp [InferenceBase.FreshSupply.empty])
        (by simp [InferenceBase.FreshSupply.empty])
        (by
          constructor <;> intro varId member below
          · exact (Nat.not_lt_zero _ below).elim
          · exact (Nat.not_lt_zero _ below).elim)
        (⟨rawContext, List.append_nil rawContext⟩)
        (by
          constructor <;> intro varId member <;>
            simp [Context.applySubst, Context.fcv, Context.ftv] at member)
        (by intro pair member; simp at member)
        (by constructor <;> intro pair member <;> simp at member)
        (RetainedOldOrContextAt.nil InferenceBase.FreshSupply.empty [] Subst.id)
        (fun algorithm selected member => by cases member) childGenerativity
        childRetained childMembers
        (prepared.frontierNormalizationTransport
          functionResult.frontierNormalized)
        childContexts childValid
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
      · exact prepared.protectedCovered
      · exact prepared.contextSuffix
      · exact prepared.postAdmissible
      · exact prepared.prevailingBounded
      · exact prepared.prevailingIdempotent
      · exact prepared.pendingCapFree
  | context, .letE name value body, bodyTy,
      .letE (valueTy := valueTy) valueTyping bodyTyping => by
      rename_i signature supply prevailing rawContext frames frontier pending
        residual provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      have valueResult := Typing.w_paired_normalized_mutual valueTyping
        signatureClosed state active erased scope protectedScopes contextCapFree
        floorCaps
        floorTargets contextOld rawSuffix included provenanceSuffix
        provenanceCovered retainedOuter provenanceRetains generativity
        surfacesRetained surfacesMembers frontierNormalized generativityContexts
        generativityValid currentObligation currentPaired coverage contextSuffix
        admissible bounded idempotent capFree
      rcases valueResult with ⟨valuePackage⟩
      let valueWitness := valuePackage.normalized
      let finished := valueWitness.complete
      let algorithmScheme := signature.generalize
        (rawContext.applySubst finished.prevailing')
        (finished.prevailing'.apply finished.rawTarget)
      let selectedScheme := SCtx.generalize context valueTy
      let bodyRawContext := (name, algorithmScheme) :: rawContext
      let bodySelectedContext := (name, selectedScheme) :: context
      let bodyFrontier := letBodyContinuationFrontier provenanceFrontier
        generativityObligations finished.suffix finished.prevailing'
      let shadow := letShadowObligation provenanceFloor provenanceContext
        (provenanceFrontier.map fun pair =>
          (finished.suffix.apply pair.1, pair.2))
      let bodyObligations :=
        GenerativitySurfaceObligation.currentPaired finished.successor
            bodyRawContext bodyFrontier ::
          GenerativitySurfaceObligation.current finished.successor
              bodyRawContext :: shadow :: generativityObligations
      obtain ⟨_binding, preparedState, preparedScope⟩ :=
        valuePackage.prepareErasedLetBody signatureClosed active
      obtain ⟨bodyRetained, bodyMembers, bodyCurrentPaired⟩ :=
        valuePackage.prepareErasedLetBodySurfaces (name := name)
      have bodyMember : ∀ pair, pair ∈ bodyFrontier →
          pair ∈ finished.frontier := by
        intro pair member
        rcases List.mem_append.mp member with provenanceMember | surfaceMember
        · rcases List.mem_map.mp provenanceMember with ⟨old, oldMember, rfl⟩
          exact valuePackage.provenanceRetains old.1 old.2 oldMember
        · rcases List.mem_flatMap.mp surfaceMember with
            ⟨obligation, obligationMember, pairMember⟩
          rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
          exact valuePackage.surfacesMembers obligation obligationMember old
            oldMember
      have bodyFrontierNormalized : ∀ pair ∈ bodyFrontier,
          finished.prevailing'.apply pair.1 = pair.1 := by
        intro pair member
        exact valuePackage.frontierNormalized pair (bodyMember pair member)
      have shadowFrame : GenerativitySurfaceFrameAt
          (shadow :: generativityObligations) finished.prevailing' := by
        intro obligation member raw rawMember
        rcases List.mem_cons.mp member with rfl | old
        · simp [shadow, letShadowObligation] at rawMember
        · exact valueWitness.generativity obligation old raw rawMember
      have bodyGenerativity : GenerativitySurfaceFrameAt bodyObligations
          finished.prevailing' :=
        (shadowFrame.registerEmpty finished.successor bodyRawContext)
          |>.registerPaired finished.successor bodyRawContext bodyFrontier
      have schemeFixed : algorithmScheme.applyMeta finished.prevailing' =
          algorithmScheme := by
        exact letGeneralizedScheme_fixed signature rawContext
          finished.rawTarget finished.prevailing'
            finished.prevailingIdempotent
      have extendCovered : ∀
          {floor : InferenceBase.FreshSupply} {owner : Context},
          OldContextCoveredAt floor
              (owner.applySubst finished.prevailing')
              (rawContext.applySubst finished.prevailing') →
          OldFreeInContextAt floor (owner.applySubst finished.prevailing')
              (finished.prevailing'.apply finished.rawTarget) →
          OldContextCoveredAt floor
              (owner.applySubst finished.prevailing')
              (Context.applySubst finished.prevailing' bodyRawContext) := by
        intro floor owner covered targetOld
        change OldContextCoveredAt floor
          (owner.applySubst finished.prevailing')
          (Context.applySubst finished.prevailing'
            ((name, algorithmScheme) :: rawContext))
        rw [show Context.applySubst finished.prevailing'
              ((name, algorithmScheme) :: rawContext) =
            (name, algorithmScheme) ::
              rawContext.applySubst finished.prevailing' by
          simp [Context.applySubst, schemeFixed]]
        constructor
        · intro varId free below
          rw [Context.fcv, List.flatMap_cons, List.mem_append] at free
          rcases free with head | outer
          · apply targetOld.caps varId _ below
            unfold algorithmScheme FrozenSig.generalize Scheme.generalize
              Scheme.close Scheme.fcv at head
            exact (PolyTy.abstract_free_subset _ _
              (finished.prevailing'.apply finished.rawTarget)).1 varId head
          · exact covered.caps varId outer below
        · intro varId free below
          rw [Context.ftv, List.flatMap_cons, List.mem_append] at free
          rcases free with head | outer
          · apply targetOld.targets varId _ below
            unfold algorithmScheme FrozenSig.generalize Scheme.generalize
              Scheme.close Scheme.ftv at head
            exact (PolyTy.abstract_free_subset _ _
              (finished.prevailing'.apply finished.rawTarget)).2 varId head
          · exact covered.targets varId outer below
      have bodyContexts : GenerativitySurfaceContextsAt bodyObligations
          finished.prevailing'
          (Context.applySubst finished.prevailing' bodyRawContext) := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | member
        · exact OldContextCoveredAt.refl finished.successor _
        rcases List.mem_cons.mp member with rfl | member
        · exact OldContextCoveredAt.refl finished.successor _
        rcases List.mem_cons.mp member with rfl | old
        · exact extendCovered valuePackage.contextOld valuePackage.targetOld
        · exact extendCovered
            (valueWitness.generativityContexts obligation old)
            (valueWitness.targetGenerative obligation old)
      have bodyValid : GenerativitySurfaceValid finished.successor
          bodyRawContext bodyObligations := by
        intro obligation member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩
        rcases List.mem_cons.mp member with rfl | old
        · exact ⟨⟨Nat.le_trans floorCaps
                  finished.derived.supplyExtends.1,
                Nat.le_trans floorTargets finished.derived.supplyExtends.2⟩,
              rawSuffix.consActive name algorithmScheme⟩
        · exact ⟨(generativityValid obligation old).1.trans
                finished.derived.supplyExtends,
              (generativityValid obligation old).2.consActive name
                algorithmScheme⟩
      have bodyResult := Typing.w_paired_normalized_mutual bodyTyping
        (signature := signature) (supply := finished.successor)
        (prevailing := finished.prevailing') (rawContext := bodyRawContext)
        (frames := (bodyRawContext, bodySelectedContext) :: frames)
        (frontier := bodyFrontier)
        (pending := PendingLetCut.mk rawContext finished.rawTarget
          finished.prevailing' :: finished.pending)
        (residual := valueWitness.residual)
        (provenanceFloor := InferenceBase.FreshSupply.empty)
        (provenanceContext := []) (provenanceFrames := [])
        (provenanceFrontier := [])
        (generativityObligations := bodyObligations)
        signatureClosed (by
          rw [← valueWitness.post_eq]
          exact preparedState) List.mem_cons_self
        ⟨by
          rw [← valueWitness.post_eq]
          exact preparedState.stable.frame.contexts List.mem_cons_self⟩
        preparedScope
        (by
          intro pair member
          rcases List.mem_cons.mp member with rfl | old
          · exact preparedScope
          · exact valueWitness.protectedScopes pair old)
        (by
          rw [show Context.applySubst finished.prevailing' bodyRawContext =
            (name, algorithmScheme) ::
              rawContext.applySubst finished.prevailing' by
            simp [bodyRawContext, Context.applySubst, schemeFixed]]
          rw [Context.fcv, List.flatMap_cons, List.append_eq_nil_iff]
          exact ⟨by
            change (signature.generalize
              (rawContext.applySubst finished.prevailing')
              (finished.prevailing'.apply finished.rawTarget)).fcv = []
            unfold FrozenSig.generalize Scheme.generalize Scheme.fcv
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro varId free
            have source := (PolyTy.abstract_free_subset _ _
              (finished.prevailing'.apply finished.rawTarget)).1 varId free
            rw [valueWitness.target.normalized_eq, STy.emb_fcv] at source
            simp at source,
            valuePackage.contextCapFree⟩)
        (by simp [InferenceBase.FreshSupply.empty])
        (by simp [InferenceBase.FreshSupply.empty])
        (by
          constructor <;> intro varId member below <;>
            exact (Nat.not_lt_zero _ below).elim)
        ⟨bodyRawContext, List.append_nil bodyRawContext⟩
        (by
          constructor <;> intro varId member <;>
            simp [Context.applySubst, Context.fcv, Context.ftv] at member)
        (by intro pair member; simp at member)
        (by constructor <;> intro pair member <;> simp at member)
        (RetainedOldOrContextAt.nil InferenceBase.FreshSupply.empty [] Subst.id)
        (fun algorithm selected member => by cases member)
        bodyGenerativity bodyRetained bodyMembers bodyFrontierNormalized
        bodyContexts bodyValid (List.mem_cons_of_mem _ List.mem_cons_self)
        bodyCurrentPaired
        (by exact (contextSuffix.consActive name algorithmScheme
          bodySelectedContext).toProtectedFreeCovered finished.prevailing')
        (contextSuffix.consActive name algorithmScheme bodySelectedContext)
        (by rw [← valueWitness.post_eq]; exact finished.postAdmissible)
        finished.prevailingBounded finished.prevailingIdempotent
        (PendingLetsCapFree.cons (cut := PendingLetCut.mk rawContext
          finished.rawTarget finished.prevailing') finished.pendingCapFree
          valuePackage.contextCapFree (by
          rw [valueWitness.target.normalized_eq, STy.emb_fcv]))
      rcases bodyResult with ⟨bodyPackage⟩
      exact Typing.w_paired_normalized_let_of_body active valuePackage
        ⟨bodyPackage⟩
  | context, .fix self argument body, .fn domain codomain,
      .fixE distinct direct bodyTyping => by
      rename_i signature supply prevailing rawContext frames frontier pending
        residual provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceRetains
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      let bodyRawContext :=
        (argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) :: rawContext
      let bodySelectedContext :=
        (argument, SScheme.mono domain) ::
          (self, SScheme.mono (.fn domain codomain)) :: context
      let bodyFrames := (bodyRawContext, bodySelectedContext) :: frames
      let bodyFrontier := (.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier
      apply Typing.w_paired_normalized_fix (self := self)
        (argument := argument) (body := body) distinct direct
        (Typing.inDMFragment bodyTyping).nonMatcherBody
        signatureClosed state active scope protectedScopes floorCaps floorTargets
        contextOld rawSuffix provenanceSuffix provenanceCovered
        retainedOuter provenanceRetains generativity surfacesRetained
        surfacesMembers frontierNormalized generativityContexts generativityValid
        currentObligation currentPaired coverage contextSuffix contextCapFree
        admissible bounded idempotent capFree
      intro prepared
      let preparedBody : WFixBodyPrepared signature supply prevailing
          rawContext self argument context domain codomain provenanceFloor
          provenanceContext provenanceFrames provenanceFrontier
          generativityObligations frames frontier pending := prepared
      exact Typing.w_paired_normalized_mutual bodyTyping
        (signature := signature)
        (supply := { supply with nextTy := supply.nextTy + 2 })
        (prevailing := prevailing)
        (rawContext := bodyRawContext) (frames := bodyFrames)
        (frontier := bodyFrontier)
        (pending := pending)
        (residual := WFixBodyPrepared.residual (self := self)
          (argument := argument) preparedBody)
        (provenanceFloor := provenanceFloor)
        (provenanceContext := provenanceContext)
        (provenanceFrames := provenanceFrames)
        (provenanceFrontier := provenanceFrontier)
        (generativityObligations := WFixBodyPrepared.childObligations
          (self := self) (argument := argument) preparedBody)
        signatureClosed
        (WFixBodyPrepared.state (self := self) (argument := argument) preparedBody)
        List.mem_cons_self
        (WFixBodyPrepared.context (self := self) (argument := argument) preparedBody)
        (WFixBodyPrepared.scope (self := self) (argument := argument) preparedBody)
        (WFixBodyPrepared.protectedScopes (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.contextCapFree (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.floorCaps (signature := signature) (supply := supply)
          (prevailing := prevailing) (rawContext := rawContext)
          (self := self) (argument := argument) preparedBody)
        (WFixBodyPrepared.floorTargets (self := self) (argument := argument)
          prepared)
        (WFixBodyPrepared.contextOld (self := self) (argument := argument)
          prepared)
        (WFixBodyPrepared.contextProvenanceSuffix (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.provenanceIncluded (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.provenanceSuffix (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.provenanceCovered (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.retainedOuter (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.provenanceRetains (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childGenerativity (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childRetained (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childMembers (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.frontierNormalized (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childGenerativityContexts (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childGenerativityValid (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childCurrentObligation (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.childCurrentPaired (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.protectedCovered (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.contextSuffix (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.postAdmissible (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.prevailingBounded (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.prevailingIdempotent (self := self)
          (argument := argument) preparedBody)
        (WFixBodyPrepared.pendingCapFree (self := self)
          (argument := argument) preparedBody)
  | _, _, _, .lit => by
      intro _signatureClosed state _active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceMembers
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      exact Typing.w_paired_normalized_lit (algorithmContext := []) state erased
        scope protectedScopes coverage contextCapFree generativity generativityContexts
        generativityValid currentObligation surfacesRetained surfacesMembers
        frontierNormalized currentPaired retainedOuter
        (fun pair member => provenanceMembers pair.1 pair.2 member)
        floorCaps floorTargets provenanceCovered included rawSuffix
        provenanceSuffix contextSuffix contextOld admissible bounded idempotent
        capFree
  | _, _, _, .tuple typings => by
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceMembers
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      apply Typing.w_paired_normalized_tuple_of_children
      exact Typings.w_paired_normalized_mutual typings signatureClosed
        state active erased scope protectedScopes contextCapFree floorCaps floorTargets
        contextOld rawSuffix included provenanceSuffix
        provenanceCovered retainedOuter provenanceMembers generativity
        surfacesRetained surfacesMembers frontierNormalized generativityContexts
        generativityValid currentObligation currentPaired coverage contextSuffix
        admissible bounded idempotent capFree

theorem Typings.w_paired_normalized_mutual :
    ∀ {context expressions targets}, Typings context expressions targets →
      NormalizedWCompletes context expressions targets
  | _, _, _, .nil => by
      intro _signatureClosed state _active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceMembers
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      exact Typings.w_paired_normalized_nil (algorithmContext := []) state erased
        scope protectedScopes coverage contextCapFree generativity generativityContexts
        generativityValid currentObligation surfacesRetained surfacesMembers
        frontierNormalized currentPaired retainedOuter
        (fun pair member => provenanceMembers pair.1 pair.2 member)
        floorCaps floorTargets provenanceCovered included rawSuffix
        provenanceSuffix contextSuffix contextOld admissible bounded idempotent
        capFree
  | context, expression :: expressions, target :: targets, .cons head tail => by
      rename_i signature supply prevailing rawContext frames frontier pending
        residual provenanceFloor provenanceContext provenanceFrames
        provenanceFrontier generativityObligations
      intro signatureClosed state active erased scope protectedScopes
        contextCapFree
        floorCaps floorTargets contextOld rawSuffix included
        provenanceSuffix provenanceCovered retainedOuter provenanceMembers
        generativity surfacesRetained surfacesMembers frontierNormalized
        generativityContexts generativityValid currentObligation currentPaired
        coverage contextSuffix admissible bounded idempotent capFree
      have headResult := Typing.w_paired_normalized_mutual head
        signatureClosed state active erased scope protectedScopes contextCapFree
        floorCaps
        floorTargets contextOld rawSuffix included provenanceSuffix
        provenanceCovered retainedOuter provenanceMembers generativity
        surfacesRetained surfacesMembers frontierNormalized generativityContexts
        generativityValid currentObligation currentPaired coverage contextSuffix
        admissible bounded idempotent capFree
      rcases headResult with ⟨headPackage⟩
      apply Typings.w_paired_normalized_cons_of_results headPackage
      let headWitness := headPackage.normalized
      let finished := headWitness.complete
      let mappedProvenance := provenanceFrontier.map fun pair =>
        (finished.suffix.apply pair.1, pair.2)
      let protectedObligations :=
        GenerativitySurfaceObligations.protectToken finished.rawTarget
          generativityObligations
      let rawObligations :=
        GenerativitySurfaceObligation.current finished.successor rawContext ::
          protectedObligations
      let tailObligations :=
        GenerativitySurfaceObligation.currentPaired finished.successor
            rawContext finished.frontier :: rawObligations
      have mappedMembers : ∀ algorithm selected,
          (algorithm, selected) ∈ mappedProvenance →
            (algorithm, selected) ∈ finished.frontier := by
        intro algorithm selected member
        rcases List.mem_map.mp member with ⟨pair, oldMember, equality⟩
        rw [← equality]
        exact headPackage.provenanceRetains pair.1 pair.2 oldMember
      have mappedRetained : RetainedOldOrContextAt provenanceFloor
          (provenanceContext.applySubst finished.prevailing') Subst.id
          mappedProvenance := by
        constructor
        · intro pair member varId free
          rw [Subst.apply_id] at free
          rcases List.mem_map.mp member with ⟨oldPair, oldMember, equality⟩
          rw [← equality] at free
          exact headPackage.retainedOuter.caps oldPair oldMember varId free
        · intro pair member varId free
          rw [Subst.apply_id] at free
          rcases List.mem_map.mp member with ⟨oldPair, oldMember, equality⟩
          rw [← equality] at free
          exact headPackage.retainedOuter.targets oldPair oldMember varId free
      have protectedGenerativity : GenerativitySurfaceFrameAt
          protectedObligations finished.prevailing' :=
        headWitness.generativity.protectToken (by
          intro obligation member
          exact headWitness.targetGenerative obligation member)
      have rawGenerativity : GenerativitySurfaceFrameAt rawObligations
          finished.prevailing' := protectedGenerativity.registerEmpty
            finished.successor rawContext
      have tailGenerativity : GenerativitySurfaceFrameAt tailObligations
          finished.prevailing' := rawGenerativity.registerPaired
            finished.successor rawContext finished.frontier
      have rawContexts : GenerativitySurfaceContextsAt rawObligations
          finished.prevailing' (rawContext.applySubst finished.prevailing') :=
        headWitness.generativityContexts.protectToken.registerCurrent _
      have tailContexts : GenerativitySurfaceContextsAt tailObligations
          finished.prevailing' (rawContext.applySubst finished.prevailing') :=
        rawContexts.registerCurrentPaired finished.successor finished.frontier
      have rawValid : GenerativitySurfaceValid finished.successor rawContext
          rawObligations := by
        apply GenerativitySurfaceValid.registerCurrent
        exact headWitness.generativityValid.protectToken.monoSupply
          finished.derived.supplyExtends
      have tailValid : GenerativitySurfaceValid finished.successor rawContext
          tailObligations := rawValid.registerCurrentPaired finished.frontier
      have protectedRetained : GenerativitySurfaceRetainedAt
          protectedObligations finished.prevailing' :=
        headPackage.surfacesRetained.protectToken
      have rawRetained : GenerativitySurfaceRetainedAt rawObligations
          finished.prevailing' :=
        GenerativitySurfaceRetainedAt.registerCurrent
          (RetainedOldOrContextAt.nil finished.successor
            (rawContext.applySubst finished.prevailing') finished.prevailing')
          protectedRetained
      have tailRetained : GenerativitySurfaceRetainedAt tailObligations
          finished.prevailing' := by
        apply GenerativitySurfaceRetainedAt.registerCurrentOfBounded
          (tail := rawRetained)
        intro pair member
        exact finished.prevailingBounded.apply
          (finished.frame.frontierBounded pair member)
      have protectedMembers : GenerativitySurfaceMembersAt
          protectedObligations finished.prevailing' finished.frontier :=
        headPackage.surfacesMembers.protectToken
      have rawMembers : GenerativitySurfaceMembersAt rawObligations
          finished.prevailing' finished.frontier :=
        GenerativitySurfaceMembersAt.registerCurrent
          (fun pair member => by simp at member) protectedMembers
      have tailMembers : GenerativitySurfaceMembersAt tailObligations
          finished.prevailing' finished.frontier :=
        GenerativitySurfaceMembersAt.registerCurrent
          (fun pair member => by
            rw [headPackage.frontierNormalized pair member]
            exact member)
          rawMembers
      have tailResult := Typings.w_paired_normalized_mutual tail
        (signature := signature)
        (supply := finished.successor)
        (prevailing := finished.prevailing') (rawContext := rawContext)
        (frames := frames) (frontier := finished.frontier)
        (pending := finished.pending) (residual := headWitness.residual)
        (provenanceFloor := provenanceFloor)
        (provenanceContext := provenanceContext)
        (provenanceFrames := provenanceFrames)
        (provenanceFrontier := mappedProvenance)
        (generativityObligations := tailObligations)
        signatureClosed (by
          rw [← headWitness.post_eq]
          exact finished.retiredState) active headWitness.context
        headWitness.scope headWitness.protectedScopes headPackage.contextCapFree
        (Nat.le_trans headPackage.floorCaps
          finished.derived.supplyExtends.1)
        (Nat.le_trans headPackage.floorTargets
          finished.derived.supplyExtends.2) headPackage.contextOld
        headPackage.contextProvenanceSuffix headPackage.provenanceIncluded
        headPackage.provenanceSuffix
        headPackage.provenanceCovered mappedRetained mappedMembers
        tailGenerativity tailRetained tailMembers headPackage.frontierNormalized
        tailContexts tailValid (List.mem_cons_of_mem _ List.mem_cons_self)
        List.mem_cons_self headWitness.protectedCovered
        headWitness.contextSuffix (by
          rw [← headWitness.post_eq]
          exact finished.postAdmissible)
        finished.prevailingBounded finished.prevailingIdempotent
        finished.pendingCapFree
      rcases tailResult with ⟨tailPackage⟩
      exact ⟨
        { result := tailPackage
          surfacesRetained := tailPackage.surfacesRetained
          surfacesMembers := tailPackage.surfacesMembers
          frontierNormalized := tailPackage.frontierNormalized
          currentPairedOuter := currentPaired
          inputFrontierNormalizedOuter := frontierNormalized } ⟩

end

/-! ## Public root -/

/-- Every Damas--Milner typing derivation is accepted by executable
inference.  All continuation certificates are initialized here; the mutual
driver itself has no constructor callbacks or proof oracles. -/
theorem Typing.inferenceSucceeds
    {signature : FrozenSig} {context : SCtx} {expression : Expr}
    {target : STy} (signatureWF : FrozenSigWF signature)
    (typing : Typing context expression target) :
    Inference.inferenceSucceeds signature context.emb expression = true := by
  let supply := Inference.initialSupply signature context.emb
  let rawCurrent := GenerativitySurfaceObligation.current supply context.emb
  let obligations := [rawCurrent]
  have pairedId : SSubst.paired SSubst.id = Subst.id := by
    apply congrArg (fun target => Subst.mk CapSubst.id target)
    funext varId
    rfl
  have result := Typing.w_paired_normalized_mutual typing
    (signature := signature) (supply := supply) (prevailing := Subst.id)
    (rawContext := context.emb) (frames := [(context.emb, context)])
    (frontier := []) (pending := []) (residual := SSubst.id)
    (provenanceFloor := InferenceBase.FreshSupply.empty)
    (provenanceContext := []) (provenanceFrames := [])
    (provenanceFrontier := [])
    (generativityObligations := obligations)
    signatureWF.schemesClosed
    (by rw [pairedId]; exact
      WRetiredStableFrameAt.initial signature context)
    List.mem_cons_self
    (by
      constructor
      rw [Context.applySubst_id, pairedId]
      exact WContextRel.emb_id context)
    (by
      intro algorithmVar selectedVar algorithmFree imageFree
      exact ResidualContextScope.initial context (by
        simpa [Context.applySubst_id] using algorithmFree) (by
        simpa [SSubst.id] using imageFree))
    (by
      intro pair member
      rcases List.mem_singleton.mp member with rfl
      intro algorithmVar selectedVar algorithmFree imageFree
      exact ResidualContextScope.initial context (by
        simpa [Context.applySubst_id] using algorithmFree) (by
        simpa [SSubst.id] using imageFree))
    (by simpa [Context.applySubst_id] using SCtx.emb_fcv context)
    (by simp [InferenceBase.FreshSupply.empty])
    (by simp [InferenceBase.FreshSupply.empty])
    (by
      constructor <;> intro varId member below <;>
        exact (Nat.not_lt_zero _ below).elim)
    ⟨context.emb, by simp⟩
    (by
      constructor <;> intro varId member <;>
        simp [Context.fcv, Context.ftv] at member)
    (by intro pair member; simp at member)
    (by constructor <;> intro pair member <;> simp at member)
    (RetainedOldOrContextAt.nil InferenceBase.FreshSupply.empty [] Subst.id)
    (by intro algorithm selected member; simp at member)
    (by
      intro obligation member raw rawMember
      rcases List.mem_singleton.mp member with rfl
      simp [rawCurrent, GenerativitySurfaceObligation.current] at rawMember)
    (by
      intro obligation member
      rcases List.mem_singleton.mp member with rfl
      dsimp [rawCurrent, GenerativitySurfaceObligation.current]
      simpa [Context.applySubst_id] using
        RetainedOldOrContextAt.nil supply context.emb Subst.id)
    (by
      intro obligation member pair pairMember
      rcases List.mem_singleton.mp member with rfl
      simp [rawCurrent, GenerativitySurfaceObligation.current] at pairMember)
    (by intro pair member; simp at member)
    (by
      intro obligation member
      rcases List.mem_singleton.mp member with rfl
      dsimp [rawCurrent, GenerativitySurfaceObligation.current]
      simpa [Context.applySubst_id] using
        OldContextCoveredAt.refl supply context.emb)
    (by
      intro obligation member
      rcases List.mem_singleton.mp member with rfl
      exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩)
    (by simp [obligations, rawCurrent])
    (by simp [obligations, rawCurrent,
      GenerativitySurfaceObligation.current,
      GenerativitySurfaceObligation.currentPaired])
    (by simpa [Context.applySubst_id] using
      ProtectedFreeCovered.initial context)
    (ProtectedContextsSuffix.singleton context.emb context)
    (by rw [pairedId]; exact AdmissiblePost.id [])
    (Subst.boundedBy_id supply)
    Subst.id_idempotent (PendingLetsCapFree.nil Subst.id)
  rcases result with ⟨package⟩
  obtain ⟨audit⟩ := package.normalized.complete.audit
  exact inferenceSucceeds_of_auditedWRun signatureWF audit

end DM
end TypePM
