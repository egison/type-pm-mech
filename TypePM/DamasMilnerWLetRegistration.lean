import TypePM.DamasMilnerAcceptanceTheorem
import TypePM.DamasMilnerWLetDerived
import TypePM.DamasMilnerWLetGenerative
import TypePM.DamasMilnerWConstructorCompletion

/-!
# Oracle-free let registration from a normalized W value

This post-Acceptance bridge derives every premise of
`w_prepareErasedLetBindingAndRetire` from the indexed generative invariants
carried by a completed value result.
-/

namespace TypePM
namespace DM

/-- The let-body continuation consists of the fixed provenance surface and
all constructor-local paired surfaces, each evaluated at the completed value
substitution. -/
def letBodyContinuationFrontier
    (provenance : List (Ty × STy))
    (obligations : List GenerativitySurfaceObligation)
    (provenanceSuffix : Subst)
    (current : Subst) : List (Ty × STy) :=
  provenance.map (fun pair => (provenanceSuffix.apply pair.1, pair.2)) ++
    obligations.flatMap fun obligation =>
      obligation.continuation.map fun pair => (current.apply pair.1, pair.2)

/-- Real outer provenance carried through the let body without imposing its
old-free polarity on the body's executable continuation frontier. -/
def letShadowObligation (floor : InferenceBase.FreshSupply) (owner : Context)
    (frontier : List (Ty × STy)) : GenerativitySurfaceObligation :=
  ⟨floor, owner, frontier, []⟩

/-- Free variables left by generalization over a closed signature come from
the environment. -/
theorem FrozenSig.generalize_ftv_mem_context
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {context : Context} {target : Ty} {varId : TypePM.TyVar}
    (free : varId ∈ (signature.generalize context target).ftv) :
    varId ∈ context.ftv := by
  let binders := signature.generalizedTyVars context target
  have sourceFree : varId ∈ target.ftv :=
    (PolyTy.abstract_free_subset
      (fun candidate =>
        (signature.generalizedCapVars context target).finIdxOf? candidate)
      (fun candidate => binders.finIdxOf? candidate) target).2 varId free
  have closingNone : binders.finIdxOf? varId = none :=
    (PolyTy.closing_none_of_abstract_free
      (fun candidate =>
        (signature.generalizedCapVars context target).finIdxOf? candidate)
      (fun candidate => binders.finIdxOf? candidate) target).2 varId free
  have outside : varId ∉ binders :=
    List.finIdxOf?_eq_none_iff.mp closingNone
  by_cases inEnvironment : varId ∈ context.ftv
  · exact inEnvironment
  · exact (outside (by
      unfold binders FrozenSig.generalizedTyVars
      apply mem_generalizedTyVars sourceFree
      simpa [signatureClosed] using inEnvironment)).elim

/-- Generalizing a let value adds no new free residual image to the selected
environment: all free algorithmic scheme variables already came from the
outer context. -/
theorem ResidualContextScope.consGeneralized
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {residual : SSubst} {current : Subst}
    {rawContext : Context} {selectedContext : SCtx}
    {rawTarget : Ty} {selectedScheme : SScheme} {name : String}
    (scope : ResidualContextScope residual
      (rawContext.applySubst current) selectedContext)
    (fixed : (signature.generalize (rawContext.applySubst current)
      (current.apply rawTarget)).applyMeta current =
        signature.generalize (rawContext.applySubst current)
          (current.apply rawTarget)) :
    ResidualContextScope residual
      (Context.applySubst current
        ((name, signature.generalize (rawContext.applySubst current)
          (current.apply rawTarget)) :: rawContext))
      ((name, selectedScheme) :: selectedContext) := by
  intro source image sourceFree imageFree
  change source ∈
    ((signature.generalize (rawContext.applySubst current)
      (current.apply rawTarget)).applyMeta current).ftv ++
      (rawContext.applySubst current).ftv at sourceFree
  change image ∈ selectedScheme.ftv ++ selectedContext.ftv
  simp only [List.mem_append] at sourceFree ⊢
  rcases sourceFree with headFree | outerFree
  · rw [fixed] at headFree
    right
    exact scope
      (FrozenSig.generalize_ftv_mem_context signatureClosed headFree) imageFree
  · right
    exact scope outerFree imageFree

/-- Sound paired-surface version of let registration.  Every retained pair is
either fixed provenance or belongs to an explicitly paired generativity
surface; no ambient frontier entry is silently discarded. -/
theorem WPairedNormalizedCompleteWitness.prepareErasedLetBindingAndRetire
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {value : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (result : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext value selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (signatureClosed : signature.SchemesClosed) :
    WLetBindingRel result.normalized.complete.post
        result.normalized.complete.prevailing'
        (signature.generalize
          (rawContext.applySubst result.normalized.complete.prevailing')
          (result.normalized.complete.prevailing'.apply
            result.normalized.complete.rawTarget))
        (SCtx.generalize selectedContext selectedTarget) ∧
      WRetiredStableFrameAt signature result.normalized.complete.successor
        result.normalized.complete.post
        result.normalized.complete.prevailing' frames
        (letBodyContinuationFrontier provenanceFrontier
          generativityObligations result.normalized.complete.suffix
          result.normalized.complete.prevailing')
        (PendingLetCut.mk rawContext result.normalized.complete.rawTarget
          result.normalized.complete.prevailing' ::
            result.normalized.complete.pending) := by
  let normalized := result.normalized
  let complete := normalized.complete
  let smaller := letBodyContinuationFrontier provenanceFrontier
    generativityObligations complete.suffix complete.prevailing'
  have subset : ∀ pair, pair ∈ smaller → pair ∈ complete.frontier := by
    intro pair member
    rcases List.mem_append.mp member with provenanceMember | surfaceMember
    · rcases List.mem_map.mp provenanceMember with ⟨old, oldMember, rfl⟩
      exact result.provenanceRetains old.1 old.2 oldMember
    · rcases List.mem_flatMap.mp surfaceMember with
        ⟨obligation, obligationMember, pairMember⟩
      rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
      exact result.surfacesMembers obligation obligationMember old oldMember
  have ownerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget) :=
    result.targetOld
  have newFresh : ∀ pair ∈ smaller,
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing')
        |>.AvoidsTy signature complete.prevailing' pair.1 := by
    intro pair member
    rcases List.mem_append.mp member with provenanceMember | surfaceMember
    · rcases List.mem_map.mp provenanceMember with ⟨old, oldMember, rfl⟩
      exact result.retainedOuter.avoidsGeneralized_of_included result.targetOld
        result.provenanceIncluded rfl rfl old oldMember
    · rcases List.mem_flatMap.mp surfaceMember with
        ⟨obligation, obligationMember, pairMember⟩
      rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
      have included :=
        (normalized.generativityValid obligation obligationMember).2.toIncluded
          complete.prevailing'
      exact (result.surfacesRetained obligation obligationMember)
        |>.avoidsGeneralized_of_included
          (normalized.targetGenerative obligation obligationMember) included
          rfl rfl old oldMember
  have newContextsFresh : ∀ pair ∈ frames,
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing')
        |>.AvoidsContext signature complete.prevailing'
          (pair.1.applySubst complete.prevailing') :=
    normalized.protectedCovered.avoidsContexts
      (PendingLetCut.avoidsOwnContext (signature := signature))
  have targetBounded := complete.frame.frontierBounded _ complete.targetMember
  have newBelow := letGeneralizedVarsBelow_of_targetBounded signature
    (rawContext.applySubst complete.prevailing')
    (complete.prevailing'.apply complete.rawTarget) complete.successor
    targetBounded
  have schemeFixed := letGeneralizedScheme_fixed signature rawContext
    complete.rawTarget complete.prevailing' complete.prevailingIdempotent
  have erasedView : ErasedDMView normalized.residual selectedContext
      selectedTarget (rawContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget) :=
    ⟨normalized.context, ⟨by
      rw [normalized.target.normalized_eq, SSubst.paired_apply_emb,
        normalized.target.residual_eq]⟩⟩
  have retiredState : WRetiredStableFrameAt signature complete.successor
      (SSubst.paired normalized.residual) complete.prevailing' frames
      complete.frontier complete.pending := by
    rw [← normalized.post_eq]
    exact complete.retiredState
  have prepared := w_prepareErasedLetBindingAndRetire retiredState
    signatureClosed erasedView normalized.scope schemeFixed subset newFresh
    newContextsFresh newBelow complete.prevailingIdempotent
  rw [normalized.post_eq]
  exact prepared

/-- Install the paired-surface let continuation as the active generalized
body context, including the residual scope needed by the recursive body. -/
theorem WPairedNormalizedCompleteWitness.prepareErasedLetBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {value : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut} {name : String}
    (result : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext value selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (signatureClosed : signature.SchemesClosed)
    (active : (rawContext, selectedContext) ∈ frames) :
    let complete := result.normalized.complete
    let algorithmScheme := signature.generalize
      (rawContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget)
    let selectedScheme := SCtx.generalize selectedContext selectedTarget
    let bodyFrontier := letBodyContinuationFrontier provenanceFrontier
      generativityObligations complete.suffix complete.prevailing'
    let bodyPending := PendingLetCut.mk rawContext complete.rawTarget
      complete.prevailing' :: complete.pending
    WLetBindingRel complete.post complete.prevailing' algorithmScheme
        selectedScheme ∧
      WRetiredStableFrameAt signature complete.successor complete.post
        complete.prevailing'
        (((((name, algorithmScheme) :: rawContext),
          (name, selectedScheme) :: selectedContext)) :: frames)
        bodyFrontier bodyPending ∧
      ResidualContextScope result.normalized.residual
        (Context.applySubst complete.prevailing'
          ((name, algorithmScheme) :: rawContext))
        ((name, selectedScheme) :: selectedContext) := by
  dsimp only
  obtain ⟨binding, registered⟩ :=
    result.prepareErasedLetBindingAndRetire signatureClosed
  let normalized := result.normalized
  let complete := normalized.complete
  let algorithmScheme := signature.generalize
    (rawContext.applySubst complete.prevailing')
    (complete.prevailing'.apply complete.rawTarget)
  let selectedScheme := SCtx.generalize selectedContext selectedTarget
  have targetBounded := complete.frame.frontierBounded _ complete.targetMember
  have outerBounded := complete.frame.contextsBounded active
  have schemeFixed : algorithmScheme.applyMeta complete.prevailing' =
      algorithmScheme :=
    letGeneralizedScheme_fixed signature rawContext complete.rawTarget
      complete.prevailing' complete.prevailingIdempotent
  have bodyBounded : Context.BoundedBy complete.successor
      (Context.applySubst complete.prevailing'
        ((name, algorithmScheme) :: rawContext)) := by
    simp only [Context.applySubst, List.map_cons, schemeFixed]
    exact Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy targetBounded) outerBounded
  have bodyFresh : ∀ cut ∈
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing' ::
        complete.pending),
      cut.AvoidsContext signature complete.prevailing'
        (Context.applySubst complete.prevailing'
          ((name, algorithmScheme) :: rawContext)) := by
    intro cut cutMember
    rcases List.mem_cons.mp cutMember with rfl | oldMember
    · change (PendingLetCut.mk rawContext complete.rawTarget
        complete.prevailing').AvoidsContext signature complete.prevailing'
        ((name, algorithmScheme.applyMeta complete.prevailing') ::
          rawContext.applySubst complete.prevailing')
      rw [schemeFixed]
      exact PendingLetCut.avoidsOwnGeneralizedContext
        (signature := signature) (current := complete.prevailing')
        (rawContext := rawContext) (rawTarget := complete.rawTarget)
        (name := name)
    · have contextFresh := complete.contextsRetired cut oldMember
        (rawContext, selectedContext) active
      have targetFresh := complete.retired cut oldMember
        (complete.prevailing'.apply complete.rawTarget, selectedTarget)
        complete.targetMember
      change cut.AvoidsContext signature complete.prevailing'
        ((name, algorithmScheme.applyMeta complete.prevailing') ::
          rawContext.applySubst complete.prevailing')
      rw [schemeFixed]
      exact contextFresh.consGeneralized (name := name) targetFresh
  have outer : WContextRel complete.post
      (rawContext.applySubst complete.prevailing') selectedContext := by
    rw [normalized.post_eq]
    exact normalized.context.related
  have bodyScope : ResidualContextScope normalized.residual
      (Context.applySubst complete.prevailing'
        ((name, algorithmScheme) :: rawContext))
      ((name, selectedScheme) :: selectedContext) :=
    ResidualContextScope.consGeneralized
      signatureClosed.signatureTargets normalized.scope schemeFixed
  exact ⟨binding,
    registered.protectLetBody outer binding bodyBounded bodyFresh, bodyScope⟩

/-- The paired generativity package supplied to the recursive let body. -/
theorem WPairedNormalizedCompleteWitness.prepareErasedLetBodySurfaces
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {value : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut} {name : String}
    (result : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext value selectedContext selectedTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending) :
    let complete := result.normalized.complete
    let bodyFrontier := letBodyContinuationFrontier provenanceFrontier
      generativityObligations complete.suffix complete.prevailing'
    let algorithmScheme := signature.generalize
      (rawContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget)
    let bodyContext := (name, algorithmScheme) :: rawContext
    let bodyObligations :=
      GenerativitySurfaceObligation.currentPaired complete.successor
        bodyContext bodyFrontier ::
      GenerativitySurfaceObligation.current complete.successor bodyContext ::
      letShadowObligation provenanceFloor provenanceContext
        (provenanceFrontier.map fun pair =>
          (complete.suffix.apply pair.1, pair.2)) ::
        generativityObligations
    GenerativitySurfaceRetainedAt bodyObligations complete.prevailing' ∧
      GenerativitySurfaceMembersAt bodyObligations complete.prevailing'
        bodyFrontier ∧
      GenerativitySurfaceObligation.currentPaired complete.successor
        bodyContext bodyFrontier ∈ bodyObligations := by
  dsimp only
  let normalized := result.normalized
  let complete := normalized.complete
  let bodyFrontier := letBodyContinuationFrontier provenanceFrontier
    generativityObligations complete.suffix complete.prevailing'
  have outerMembers : GenerativitySurfaceMembersAt generativityObligations
      complete.prevailing' bodyFrontier := by
    intro obligation obligationMember pair pairMember
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨obligation, obligationMember,
      List.mem_map.mpr ⟨pair, pairMember, rfl⟩⟩
  have bodyMember : ∀ pair, pair ∈ bodyFrontier → pair ∈ complete.frontier := by
    intro pair member
    rcases List.mem_append.mp member with provenanceMember | surfaceMember
    · rcases List.mem_map.mp provenanceMember with ⟨old, oldMember, rfl⟩
      exact result.provenanceRetains old.1 old.2 oldMember
    · rcases List.mem_flatMap.mp surfaceMember with
        ⟨obligation, obligationMember, pairMember⟩
      rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
      exact result.surfacesMembers obligation obligationMember old oldMember
  have bodyBounded : ∀ pair ∈ bodyFrontier,
      pair.1.BoundedBy complete.successor := by
    intro pair member
    exact complete.frame.frontierBounded pair (bodyMember pair member)
  have retainedWithShadow : GenerativitySurfaceRetainedAt
      (letShadowObligation provenanceFloor provenanceContext
        (provenanceFrontier.map fun pair =>
          (complete.suffix.apply pair.1, pair.2)) ::
        generativityObligations) complete.prevailing' := by
    intro obligation member
    rcases List.mem_cons.mp member with rfl | outerMember
    · constructor
      · intro pair pairMember varId free
        rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
        have fixed := result.frontierNormalized _
          (result.provenanceRetains old.1 old.2 oldMember)
        rw [fixed] at free
        exact result.retainedOuter.caps old oldMember varId free
      · intro pair pairMember varId free
        rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
        have fixed := result.frontierNormalized _
          (result.provenanceRetains old.1 old.2 oldMember)
        rw [fixed] at free
        exact result.retainedOuter.targets old oldMember varId free
    · exact result.surfacesRetained obligation outerMember
  have membersWithShadow : GenerativitySurfaceMembersAt
      (letShadowObligation provenanceFloor provenanceContext
        (provenanceFrontier.map fun pair =>
          (complete.suffix.apply pair.1, pair.2)) ::
        generativityObligations) complete.prevailing'
      bodyFrontier := by
    intro obligation obligationMember pair pairMember
    rcases List.mem_cons.mp obligationMember with rfl | outerMember
    · rcases List.mem_map.mp pairMember with ⟨old, oldMember, rfl⟩
      have fixed := result.frontierNormalized _
        (result.provenanceRetains old.1 old.2 oldMember)
      rw [fixed]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨old, oldMember, rfl⟩
    · exact outerMembers obligation outerMember pair pairMember
  have retainedWithRaw : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligation.current complete.successor
        ((name, signature.generalize
          (rawContext.applySubst complete.prevailing')
          (complete.prevailing'.apply complete.rawTarget)) :: rawContext) ::
        letShadowObligation provenanceFloor provenanceContext
          (provenanceFrontier.map fun pair =>
            (complete.suffix.apply pair.1, pair.2)) ::
          generativityObligations) complete.prevailing' := by
    simpa [GenerativitySurfaceObligation.current,
      GenerativitySurfaceObligation.currentPaired] using
      (GenerativitySurfaceRetainedAt.registerCurrentOfBounded
        (surface := ([] : List (Ty × STy))) (by simp)
        retainedWithShadow)
  have membersWithRaw : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligation.current complete.successor
        ((name, signature.generalize
          (rawContext.applySubst complete.prevailing')
          (complete.prevailing'.apply complete.rawTarget)) :: rawContext) ::
        letShadowObligation provenanceFloor provenanceContext
          (provenanceFrontier.map fun pair =>
            (complete.suffix.apply pair.1, pair.2)) ::
          generativityObligations) complete.prevailing'
      bodyFrontier := by
    simpa [GenerativitySurfaceObligation.current,
      GenerativitySurfaceObligation.currentPaired] using
      (GenerativitySurfaceMembersAt.registerCurrent
        (supply := complete.successor)
        (owner := ((name, signature.generalize
          (rawContext.applySubst complete.prevailing')
          (complete.prevailing'.apply complete.rawTarget)) :: rawContext))
        (surface := ([] : List (Ty × STy))) (by simp) membersWithShadow)
  refine ⟨GenerativitySurfaceRetainedAt.registerCurrentOfBounded
      (fun pair member => by
        rw [result.frontierNormalized pair (bodyMember pair member)]
        exact bodyBounded pair member)
      retainedWithRaw, ?_, List.mem_cons_self⟩
  apply GenerativitySurfaceMembersAt.registerCurrent
  · intro pair member
    rw [result.frontierNormalized pair (bodyMember pair member)]
    exact member
  · exact membersWithRaw

/-- Recursive let-body output together with the outer certificates deliberately
kept alive by the shadow surface obligation.  The body itself uses dummy
provenance; these projections are proof outputs of the recursive motive, not
premises asserted about an arbitrary result. -/
structure WPairedNormalizedLetBody
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (name : String)
    (value body : Expr) (selectedContext : SCtx) (valueTarget bodyTarget : STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx)) (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut)
    (valueResult : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext value selectedContext valueTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending) : Type where
  bodyResult : WPairedNormalizedCompleteWitness signature
    valueResult.normalized.complete.successor
    valueResult.normalized.complete.prevailing'
    ((name, signature.generalize
      (rawContext.applySubst valueResult.normalized.complete.prevailing')
      (valueResult.normalized.complete.prevailing'.apply
        valueResult.normalized.complete.rawTarget)) :: rawContext)
    body ((name, SCtx.generalize selectedContext valueTarget) :: selectedContext)
    bodyTarget InferenceBase.FreshSupply.empty [] [] []
    (GenerativitySurfaceObligation.currentPaired
        valueResult.normalized.complete.successor
        ((name, signature.generalize
          (rawContext.applySubst valueResult.normalized.complete.prevailing')
          (valueResult.normalized.complete.prevailing'.apply
            valueResult.normalized.complete.rawTarget)) :: rawContext)
        (letBodyContinuationFrontier provenanceFrontier
          generativityObligations valueResult.normalized.complete.suffix
          valueResult.normalized.complete.prevailing') ::
      GenerativitySurfaceObligation.current
        valueResult.normalized.complete.successor
        ((name, signature.generalize
          (rawContext.applySubst valueResult.normalized.complete.prevailing')
          (valueResult.normalized.complete.prevailing'.apply
            valueResult.normalized.complete.rawTarget)) :: rawContext) ::
      letShadowObligation provenanceFloor provenanceContext
        (provenanceFrontier.map fun pair =>
          (valueResult.normalized.complete.suffix.apply pair.1, pair.2)) ::
      generativityObligations)
    (((((name, signature.generalize
      (rawContext.applySubst valueResult.normalized.complete.prevailing')
      (valueResult.normalized.complete.prevailing'.apply
        valueResult.normalized.complete.rawTarget)) :: rawContext),
      (name, SCtx.generalize selectedContext valueTarget) :: selectedContext)) ::
      frames)
    (letBodyContinuationFrontier provenanceFrontier generativityObligations
      valueResult.normalized.complete.suffix
      valueResult.normalized.complete.prevailing')
    (PendingLetCut.mk rawContext valueResult.normalized.complete.rawTarget
      valueResult.normalized.complete.prevailing' ::
      valueResult.normalized.complete.pending)

/-- Genuine paired normalized let completion.  The value theorem installs the
generalized body state; the recursive continuation returns
`WPairedNormalizedLetBody`, whose outer fields are the shadow-obligation
projections preserved by that recursion. -/
theorem Typing.w_paired_normalized_let_of_body
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {name : String}
    {value body : Expr} {selectedContext : SCtx} {valueTarget bodyTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)} {inputPending : List PendingLetCut}
    (active : (rawContext, selectedContext) ∈ frames)
    (valueResult : WPairedNormalizedCompleteWitness signature supply prevailing
      rawContext value selectedContext valueTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending)
    (bodyPackage : WPairedNormalizedLetBody signature supply prevailing
      rawContext name value body selectedContext valueTarget bodyTarget
      provenanceFloor provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending valueResult) :
    WPairedNormalizedCompleteResult signature supply prevailing rawContext
      (.letE name value body) selectedContext bodyTarget provenanceFloor
      provenanceContext provenanceFrames provenanceFrontier
      generativityObligations frames inputFrontier inputPending := by
  let valueWitness := valueResult.normalized
  let valueComplete := valueWitness.complete
  let bodyResult := bodyPackage.bodyResult
  let bodyWitness := bodyResult.normalized
  let bodyComplete := bodyWitness.complete
  let shadow := letShadowObligation provenanceFloor provenanceContext
    (provenanceFrontier.map fun pair =>
      (valueComplete.suffix.apply pair.1, pair.2))
  have shadowMember : shadow ∈
      (GenerativitySurfaceObligation.currentPaired valueComplete.successor
          ((name, signature.generalize
            (rawContext.applySubst valueComplete.prevailing')
            (valueComplete.prevailing'.apply valueComplete.rawTarget)) :: rawContext)
          (letBodyContinuationFrontier provenanceFrontier
            generativityObligations valueComplete.suffix
            valueComplete.prevailing') ::
        GenerativitySurfaceObligation.current valueComplete.successor
          ((name, signature.generalize
            (rawContext.applySubst valueComplete.prevailing')
            (valueComplete.prevailing'.apply valueComplete.rawTarget)) :: rawContext) ::
        shadow :: generativityObligations) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have outerObligationMember : ∀ obligation ∈ generativityObligations,
      obligation ∈
        (GenerativitySurfaceObligation.currentPaired valueComplete.successor
            ((name, signature.generalize
              (rawContext.applySubst valueComplete.prevailing')
              (valueComplete.prevailing'.apply valueComplete.rawTarget)) :: rawContext)
            (letBodyContinuationFrontier provenanceFrontier
              generativityObligations valueComplete.suffix
              valueComplete.prevailing') ::
          GenerativitySurfaceObligation.current valueComplete.successor
            ((name, signature.generalize
              (rawContext.applySubst valueComplete.prevailing')
              (valueComplete.prevailing'.apply valueComplete.rawTarget)) :: rawContext) ::
          shadow :: generativityObligations) := by
    intro obligation member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ member))
  let letDerived : DemandSynth signature supply prevailing rawContext
      (.letE name value body) bodyComplete.rawTarget bodyComplete.successor
      bodyComplete.prevailing' :=
    DemandSynth.letE valueComplete.derived bodyComplete.derived
  let letOrigin : DemandSynthOrigin signature letDerived [] [] :=
    DemandSynthOrigin.letE valueComplete.origin bodyComplete.origin
  let planned : PlannedSynth signature supply prevailing rawContext
      (.letE name value body) bodyComplete.rawTarget bodyComplete.successor
      bodyComplete.prevailing' :=
    ⟨letDerived, letOrigin,
      WSynthAuditPlan.letE valueComplete.auditPlan bodyComplete.auditPlan⟩
  have finalState : WRetiredStableFrameAt signature bodyComplete.successor
      bodyComplete.post bodyComplete.prevailing' frames bodyComplete.frontier
      bodyComplete.pending := bodyComplete.retiredState.dropContextHead
  have outerContext : ErasedDMContextView bodyWitness.residual selectedContext
      (rawContext.applySubst bodyComplete.prevailing') := by
    refine ⟨?_⟩
    rw [← bodyWitness.post_eq]
    exact bodyComplete.frame.contexts (List.mem_cons_of_mem _ active)
  have outerScope : ResidualContextScope bodyWitness.residual
      (rawContext.applySubst bodyComplete.prevailing') selectedContext :=
    bodyWitness.protectedScopes _ (List.mem_cons_of_mem _ active)
  have outerProtectedScopes : ∀ pair ∈ frames,
      ResidualContextScope bodyWitness.residual
        (pair.1.applySubst bodyComplete.prevailing') pair.2 := by
    intro pair member
    exact bodyWitness.protectedScopes pair (List.mem_cons_of_mem _ member)
  let finalSuffix := Subst.seq bodyComplete.suffix valueComplete.suffix
  have finalPrevailing : bodyComplete.prevailing' =
      Subst.seq finalSuffix prevailing := by
    calc
      bodyComplete.prevailing' =
          Subst.seq bodyComplete.suffix valueComplete.prevailing' :=
        bodyComplete.prevailing_eq
      _ = Subst.seq bodyComplete.suffix
          (Subst.seq valueComplete.suffix prevailing) := by
        exact congrArg (Subst.seq bodyComplete.suffix)
          valueComplete.prevailing_eq
      _ = Subst.seq finalSuffix prevailing :=
        PhasedPost.seq_assoc bodyComplete.suffix valueComplete.suffix prevailing
  have finalFrontierRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ inputFrontier →
        (finalSuffix.apply algorithm, selected) ∈ bodyComplete.frontier := by
    intro algorithm selected member
    have bodyInput : (valueComplete.prevailing'.apply algorithm, selected) ∈
        letBodyContinuationFrontier provenanceFrontier
          generativityObligations valueComplete.suffix
          valueComplete.prevailing' := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨GenerativitySurfaceObligation.currentPaired supply rawContext
        inputFrontier, valueResult.currentPaired, ?_⟩
      exact List.mem_map.mpr ⟨(algorithm, selected), member, rfl⟩
    have afterBody := bodyComplete.frontierRetains _ _ bodyInput
    have inputFixed := valueResult.inputFrontierNormalized
      (algorithm, selected) member
    have coordinateEq : finalSuffix.apply algorithm =
        bodyComplete.suffix.apply (valueComplete.prevailing'.apply algorithm) := by
      dsimp [finalSuffix]
      rw [Subst.seq_apply]
      have evolved := congrArg (fun subst => subst.apply algorithm)
        valueComplete.prevailing_eq
      rw [Subst.seq_apply, inputFixed] at evolved
      rw [evolved]
    rw [coordinateEq]
    exact afterBody
  have finalRetains : ∀ cut, cut ∈ inputPending → cut ∈ bodyComplete.pending := by
    intro cut member
    exact bodyComplete.retains cut
      (List.mem_cons_of_mem _ (valueComplete.retains cut member))
  have finalAuditCuts : ∀ cut, cut ∈ planned.plan.cuts →
      cut ∈ bodyComplete.pending := by
    intro cut member
    have cutsEq : planned.plan.cuts = valueComplete.auditPlan.cuts ++
        PendingLetCut.mk rawContext valueComplete.rawTarget
          valueComplete.prevailing' :: bodyComplete.auditPlan.cuts := by
      rfl
    rw [cutsEq] at member
    rcases List.mem_append.mp member with
      valueMember | bodyOrCurrent
    · exact bodyComplete.retains cut
        (List.mem_cons_of_mem _ (valueComplete.auditCuts cut valueMember))
    · rcases List.mem_cons.mp bodyOrCurrent with rfl | bodyMember
      · exact bodyComplete.retains _ List.mem_cons_self
      · exact bodyComplete.auditCuts cut bodyMember
  have finalContextOld : OldContextCoveredAt provenanceFloor
      (provenanceContext.applySubst bodyComplete.prevailing')
      (rawContext.applySubst bodyComplete.prevailing') := by
    have covered := bodyWitness.generativityContexts shadow shadowMember
    simpa [shadow, letShadowObligation, Context.applySubst] using
      covered.dropActiveHead
  have finalTargetOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst bodyComplete.prevailing')
      (bodyComplete.prevailing'.apply bodyComplete.rawTarget) :=
    bodyWitness.targetGenerative shadow shadowMember
  have finalGenerativity : GenerativitySurfaceFrameAt generativityObligations
      bodyComplete.prevailing' :=
    bodyWitness.generativity.of_obligations_subset outerObligationMember
  have finalContexts : GenerativitySurfaceContextsAt generativityObligations
      bodyComplete.prevailing' (rawContext.applySubst bodyComplete.prevailing') := by
    intro obligation member
    have covered := bodyWitness.generativityContexts obligation
      (outerObligationMember obligation member)
    simpa [Context.applySubst] using covered.dropActiveHead
  have finalTargetGenerative : ∀ obligation ∈ generativityObligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst bodyComplete.prevailing')
        (bodyComplete.prevailing'.apply bodyComplete.rawTarget) := by
    intro obligation member
    exact bodyWitness.targetGenerative obligation
      (outerObligationMember obligation member)
  have finalLocalOld : OldFreeInContextAt supply
      (rawContext.applySubst bodyComplete.prevailing')
      (bodyComplete.prevailing'.apply bodyComplete.rawTarget) :=
    finalTargetGenerative _ valueWitness.currentObligation
  have finalSurfacesRetained : GenerativitySurfaceRetainedAt
      generativityObligations bodyComplete.prevailing' :=
    bodyResult.surfacesRetained.of_obligations_subset outerObligationMember
  have finalSurfacesMembers : GenerativitySurfaceMembersAt
      generativityObligations bodyComplete.prevailing' bodyComplete.frontier :=
    bodyResult.surfacesMembers.of_obligations_subset outerObligationMember
  have finalOuterRetained : RetainedOldOrContextAt provenanceFloor
      (provenanceContext.applySubst bodyComplete.prevailing') finalSuffix
      provenanceFrontier := by
    have retained := bodyResult.surfacesRetained shadow shadowMember
    have evolvedEq : ∀ pair ∈ provenanceFrontier,
        bodyComplete.prevailing'.apply (valueComplete.suffix.apply pair.1) =
          finalSuffix.apply pair.1 := by
      intro pair member
      have fixed := valueResult.frontierNormalized _
        (valueResult.provenanceRetains pair.1 pair.2 member)
      calc
        bodyComplete.prevailing'.apply (valueComplete.suffix.apply pair.1) =
            bodyComplete.suffix.apply
              (valueComplete.prevailing'.apply
                (valueComplete.suffix.apply pair.1)) := by
          rw [bodyComplete.prevailing_eq, Subst.seq_apply]
        _ = bodyComplete.suffix.apply (valueComplete.suffix.apply pair.1) :=
          congrArg bodyComplete.suffix.apply fixed
        _ = finalSuffix.apply pair.1 := by
          rw [Subst.seq_apply]
    constructor
    · intro pair member varId free
      exact retained.caps (valueComplete.suffix.apply pair.1, pair.2)
        (List.mem_map.mpr ⟨pair, member, rfl⟩) varId
        (by rw [evolvedEq pair member]; exact free)
    · intro pair member varId free
      exact retained.targets (valueComplete.suffix.apply pair.1, pair.2)
        (List.mem_map.mpr ⟨pair, member, rfl⟩) varId
        (by rw [evolvedEq pair member]; exact free)
  have finalProvenanceRetains : ∀ algorithm selected,
      (algorithm, selected) ∈ provenanceFrontier →
        (finalSuffix.apply algorithm, selected) ∈ bodyComplete.frontier := by
    intro algorithm selected member
    have onShadow := bodyResult.surfacesMembers shadow shadowMember
      (valueComplete.suffix.apply algorithm, selected)
      (List.mem_map.mpr ⟨(algorithm, selected), member, rfl⟩)
    have fixed := valueResult.frontierNormalized _
      (valueResult.provenanceRetains algorithm selected member)
    have evolvedEq : bodyComplete.prevailing'.apply
        (valueComplete.suffix.apply algorithm) = finalSuffix.apply algorithm := by
      calc
        _ = bodyComplete.suffix.apply
            (valueComplete.prevailing'.apply
              (valueComplete.suffix.apply algorithm)) := by
          rw [bodyComplete.prevailing_eq, Subst.seq_apply]
        _ = bodyComplete.suffix.apply (valueComplete.suffix.apply algorithm) :=
          congrArg bodyComplete.suffix.apply fixed
        _ = _ := by rw [Subst.seq_apply]
    rw [evolvedEq] at onShadow
    exact onShadow
  let complete : WCompleteWitness signature supply prevailing rawContext
      (.letE name value body) bodyTarget frames inputFrontier inputPending :=
    { successor := bodyComplete.successor
      prevailing' := bodyComplete.prevailing'
      rawTarget := bodyComplete.rawTarget
      post := bodyComplete.post
      frontier := bodyComplete.frontier
      derived := planned.derived
      origin := planned.origin
      auditPlan := planned.plan
      pending := bodyComplete.pending
      stability := finalState.stable.lets
      retains := finalRetains
      auditCuts := finalAuditCuts
      postAdmissible := bodyComplete.postAdmissible
      prevailingBounded := bodyComplete.prevailingBounded
      prevailingIdempotent := bodyComplete.prevailingIdempotent
      frame := finalState.stable.frame
      retired := finalState.retired
      contextsRetired := finalState.contextsRetired
      pendingBelow := finalState.pendingBelow
      pendingCapFree := bodyComplete.pendingCapFree
      suffix := finalSuffix
      prevailing_eq := finalPrevailing
      frontierRetains := finalFrontierRetains
      targetMember := bodyComplete.targetMember }
  let normalized : WNormalizedCompleteWitness signature supply prevailing
      rawContext (.letE name value body) selectedContext bodyTarget
      InferenceBase.FreshSupply.empty [] [] [] generativityObligations frames
      inputFrontier inputPending :=
    { complete := complete
      algorithmContext := bodyWitness.algorithmContext
      algorithmTarget := bodyWitness.algorithmTarget
      residual := bodyWitness.residual
      post_eq := bodyWitness.post_eq
      context := outerContext
      scope := outerScope
      protectedScopes := outerProtectedScopes
      target := bodyWitness.target
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
        InferenceBase.FreshSupply.empty [] finalSuffix
      provenanceRetains := by intro algorithm selected member; cases member
      generativity := finalGenerativity
      generativityContexts := finalContexts
      generativityValid := valueWitness.generativityValid
      currentObligation := valueWitness.currentObligation
      targetGenerative := finalTargetGenerative
      localOldFree := finalLocalOld
      protectedCovered := valueWitness.contextSuffix.toProtectedFreeCovered _
      contextSuffix := valueWitness.contextSuffix
      pendingCapFree := bodyComplete.pendingCapFree }
  exact ⟨
    { normalized := normalized
      contextCapFree := by
        have bodyCapFree := bodyResult.contextCapFree
        simp only [Context.applySubst, List.map_cons, Context.fcv,
          List.flatMap_cons, List.append_eq_nil_iff] at bodyCapFree
        exact bodyCapFree.2
      floorCaps := valueResult.floorCaps
      floorTargets := valueResult.floorTargets
      contextOld := finalContextOld
      contextProvenanceSuffix := valueResult.contextProvenanceSuffix
      provenanceIncluded := valueResult.contextProvenanceSuffix.toIncluded _
      targetOld := finalTargetOld
      provenanceSuffix := valueResult.provenanceSuffix
      provenanceCovered := valueResult.provenanceSuffix.toProtectedFreeCovered _
      retainedOuter := finalOuterRetained
      provenanceRetains := finalProvenanceRetains
      inputFrontierNormalized := valueResult.inputFrontierNormalized
      surfacesRetained := finalSurfacesRetained
      surfacesMembers := finalSurfacesMembers
      frontierNormalized := bodyResult.frontierNormalized
      currentPaired := valueResult.currentPaired }
    ⟩

/-- Retire the generalized variables of a completed normalized value after
dropping its protected value head.  No freshness premise is supplied by the
caller: frontier freshness, context freshness, boundedness, and scheme
stability are all consequences of the result certificate. -/
theorem WNormalizedCompleteWitness.prepareErasedLetBindingAndRetire
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {value : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (result : WNormalizedCompleteWitness signature supply prevailing rawContext
      value selectedContext selectedTarget provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames
      inputFrontier inputPending)
    (signatureClosed : signature.SchemesClosed) :
    WLetBindingRel result.complete.post result.complete.prevailing'
        (signature.generalize
          (rawContext.applySubst result.complete.prevailing')
          (result.complete.prevailing'.apply result.complete.rawTarget))
        (SCtx.generalize selectedContext selectedTarget) ∧
      WRetiredStableFrameAt signature result.complete.successor
        result.complete.post result.complete.prevailing' frames
        (provenanceFrontier.map fun pair =>
          (result.complete.suffix.apply pair.1, pair.2))
        (PendingLetCut.mk rawContext result.complete.rawTarget
          result.complete.prevailing' :: result.complete.pending) := by
  let complete := result.complete
  let smaller := provenanceFrontier.map fun pair =>
    (complete.suffix.apply pair.1, pair.2)
  have subset : ∀ pair, pair ∈ smaller → pair ∈ complete.frontier := by
    intro pair member
    rcases List.mem_map.mp member with ⟨oldPair, oldMember, rfl⟩
    exact result.provenanceRetains oldPair.1 oldPair.2 oldMember
  have ownerOld : OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget) := by
    constructor
    · intro varId free below
      exact result.contextOld.caps varId
        (result.localOldFree.caps varId free
          (Nat.lt_of_lt_of_le below result.floorCaps)) below
    · intro varId free below
      exact result.contextOld.targets varId
        (result.localOldFree.targets varId free
          (Nat.lt_of_lt_of_le below result.floorTargets)) below
  have newFresh : ∀ pair ∈ smaller,
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing').AvoidsTy
        signature complete.prevailing' pair.1 := by
    intro pair member
    rcases List.mem_map.mp member with ⟨oldPair, oldMember, rfl⟩
    exact result.retainedOuter.avoidsGeneralized_of_included
      ownerOld result.provenanceIncluded rfl rfl oldPair oldMember
  have newContextsFresh : ∀ pair ∈ frames,
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing').AvoidsContext
        signature complete.prevailing' (pair.1.applySubst complete.prevailing') :=
    result.protectedCovered.avoidsContexts
      (PendingLetCut.avoidsOwnContext (signature := signature))
  have targetBounded :
      (complete.prevailing'.apply complete.rawTarget).BoundedBy
        complete.successor :=
    complete.frame.frontierBounded _ complete.targetMember
  have newBelow := letGeneralizedVarsBelow_of_targetBounded signature
    (rawContext.applySubst complete.prevailing')
    (complete.prevailing'.apply complete.rawTarget) complete.successor
    targetBounded
  have schemeFixed := letGeneralizedScheme_fixed signature rawContext
    complete.rawTarget complete.prevailing' complete.prevailingIdempotent
  have erasedView : ErasedDMView result.residual selectedContext selectedTarget
      (rawContext.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget) :=
    ⟨result.context, ⟨by
      rw [result.target.normalized_eq, SSubst.paired_apply_emb,
        result.target.residual_eq]⟩⟩
  have retiredState : WRetiredStableFrameAt signature complete.successor
      (SSubst.paired result.residual) complete.prevailing' frames
      complete.frontier complete.pending := by
    rw [← result.post_eq]
    exact complete.retiredState
  have prepared := w_prepareErasedLetBindingAndRetire retiredState
    signatureClosed erasedView result.scope schemeFixed subset newFresh
    newContextsFresh newBelow complete.prevailingIdempotent
  simpa only [result.post_eq] using prepared

/-- Register a completed value and install its generalized binding as the
active protected frame for the recursive let body.  The new cut's own body
freshness follows from closing; older cuts use the value target and outer
context freshness already stored in the completed result. -/
theorem WNormalizedCompleteWitness.prepareErasedLetBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {value : Expr}
    {selectedContext : SCtx} {selectedTarget : STy}
    {provenanceFloor : InferenceBase.FreshSupply}
    {provenanceContext : Context}
    {provenanceFrames frames : List (Context × SCtx)}
    {provenanceFrontier : List (Ty × STy)}
    {generativityObligations : List GenerativitySurfaceObligation}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut} {name : String}
    (result : WNormalizedCompleteWitness signature supply prevailing rawContext
      value selectedContext selectedTarget provenanceFloor provenanceContext
      provenanceFrames provenanceFrontier generativityObligations frames
      inputFrontier inputPending)
    (signatureClosed : signature.SchemesClosed)
    (active : (rawContext, selectedContext) ∈ frames) :
    let algorithmScheme := signature.generalize
      (rawContext.applySubst result.complete.prevailing')
      (result.complete.prevailing'.apply result.complete.rawTarget)
    let selectedScheme := SCtx.generalize selectedContext selectedTarget
    let bodyFrontier := provenanceFrontier.map fun pair =>
      (result.complete.suffix.apply pair.1, pair.2)
    let bodyPending := PendingLetCut.mk rawContext result.complete.rawTarget
      result.complete.prevailing' :: result.complete.pending
    WLetBindingRel result.complete.post result.complete.prevailing'
        algorithmScheme selectedScheme ∧
      WRetiredStableFrameAt signature result.complete.successor
        result.complete.post result.complete.prevailing'
        (((((name, algorithmScheme) :: rawContext),
          (name, selectedScheme) :: selectedContext)) :: frames)
        bodyFrontier bodyPending := by
  dsimp only
  obtain ⟨binding, registered⟩ :=
    result.prepareErasedLetBindingAndRetire signatureClosed
  let complete := result.complete
  let algorithmScheme := signature.generalize
    (rawContext.applySubst complete.prevailing')
    (complete.prevailing'.apply complete.rawTarget)
  have targetBounded :
      (complete.prevailing'.apply complete.rawTarget).BoundedBy
        complete.successor :=
    complete.frame.frontierBounded _ complete.targetMember
  have outerBounded :
      (rawContext.applySubst complete.prevailing').BoundedBy
        complete.successor :=
    complete.frame.contextsBounded active
  have schemeFixed : algorithmScheme.applyMeta complete.prevailing' =
      algorithmScheme := by
    exact letGeneralizedScheme_fixed signature rawContext complete.rawTarget
      complete.prevailing' complete.prevailingIdempotent
  have bodyBounded : Context.BoundedBy complete.successor
      (Context.applySubst complete.prevailing'
        ((name, algorithmScheme) :: rawContext)) := by
    simp only [Context.applySubst, List.map_cons, schemeFixed]
    exact Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy targetBounded) outerBounded
  have bodyFresh : ∀ cut ∈
      (PendingLetCut.mk rawContext complete.rawTarget complete.prevailing' ::
        complete.pending),
      cut.AvoidsContext signature complete.prevailing'
        (Context.applySubst complete.prevailing'
          ((name, algorithmScheme) :: rawContext)) := by
    intro cut cutMember
    rcases List.mem_cons.mp cutMember with rfl | oldMember
    · have own := PendingLetCut.avoidsOwnGeneralizedContext
        (signature := signature) (current := complete.prevailing')
        (rawContext := rawContext) (rawTarget := complete.rawTarget)
        (name := name)
      change (PendingLetCut.mk rawContext complete.rawTarget
        complete.prevailing').AvoidsContext signature complete.prevailing'
        ((name, algorithmScheme.applyMeta complete.prevailing') ::
          rawContext.applySubst complete.prevailing')
      rw [schemeFixed]
      exact own
    · have contextFresh := complete.contextsRetired cut oldMember
        (rawContext, selectedContext) active
      have targetFresh := complete.retired cut oldMember
        (complete.prevailing'.apply complete.rawTarget, selectedTarget)
        complete.targetMember
      have generalizedFresh := contextFresh.consGeneralized
        (name := name) targetFresh
      change cut.AvoidsContext signature complete.prevailing'
        ((name, algorithmScheme.applyMeta complete.prevailing') ::
          rawContext.applySubst complete.prevailing')
      rw [schemeFixed]
      exact generalizedFresh
  refine ⟨binding, ?_⟩
  have outer : WContextRel complete.post
      (rawContext.applySubst complete.prevailing') selectedContext := by
    rw [result.post_eq]
    exact result.context.related
  exact registered.protectLetBody outer binding bodyBounded bodyFresh

end DM
end TypePM
