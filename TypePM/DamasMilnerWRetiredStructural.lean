import TypePM.DamasMilnerWRetired
import TypePM.DamasMilnerWFix
import TypePM.DamasMilnerWTuple

/-!
# Structural transport of retired Damas--Milner variables

Fresh lambda/fix metavariables are allocated at or above the current supply.
Pending generalized variables are older and lie strictly below that supply.
This module records that boundary and lifts it through the structural W
frontier operations which perform no solver cut.
-/

namespace TypePM
namespace DM

/-- Every metavariable generalized by a pending let lies below the current
fresh supply. -/
abbrev PendingBelow := PendingLetsBelow

theorem PendingBelow.monoSupply
    {signature : FrozenSig} {supply successor : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    (below : PendingBelow signature supply current pending)
    (extension : SupplyExtends supply successor) :
    PendingBelow signature successor current pending := by
  intro cut member
  obtain ⟨caps, targets⟩ := below cut member
  exact ⟨
    fun varId generalized => Nat.lt_of_lt_of_le (caps varId generalized)
      extension.1,
    fun varId generalized => Nat.lt_of_lt_of_le (targets varId generalized)
      extension.2⟩

/-- A fresh target variable avoids every older pending generalized set. -/
theorem PendingBelow.freshTarget_avoids
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    (below : PendingBelow signature supply current pending)
    {cut : PendingLetCut} (member : cut ∈ pending) :
    cut.AvoidsTy signature current (.var supply.nextTy) := by
  obtain ⟨caps, targets⟩ := below cut member
  constructor
  · intro varId generalized free
    simp [Ty.fcv] at free
  · intro varId generalized free
    simp only [Ty.ftv, List.mem_singleton] at free
    subst varId
    exact Nat.lt_irrefl _ (targets supply.nextTy generalized)

/-- The two-variable fix/application placeholder avoids every older pending
generalized set. -/
theorem PendingBelow.freshFunction_avoids
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    (below : PendingBelow signature supply current pending)
    {cut : PendingLetCut} (member : cut ∈ pending) :
    cut.AvoidsTy signature current
      (.fn (.var supply.nextTy) (.var (supply.nextTy + 1))) := by
  obtain ⟨caps, targets⟩ := below cut member
  constructor
  · intro varId generalized free
    simp [Ty.fcv] at free
  · intro varId generalized free
    simp only [Ty.ftv, List.mem_append, List.mem_singleton] at free
    rcases free with rfl | rfl
    · exact Nat.lt_irrefl _ (targets supply.nextTy generalized)
    · exact (Nat.not_lt_of_ge (Nat.le_succ supply.nextTy))
        (targets (supply.nextTy + 1) generalized)

/-- Add the fresh lambda-domain pair to a retired frontier. -/
theorem RetiredFrontierFresh.consFreshTarget
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    {frontier : List (Ty × STy)} {selected : STy}
    (fresh : RetiredFrontierFresh signature current pending frontier)
    (below : PendingBelow signature supply current pending) :
    RetiredFrontierFresh signature current pending
      ((.var supply.nextTy, selected) :: frontier) := by
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · exact below.freshTarget_avoids cutMember
  · exact fresh cut cutMember pair oldMember

/-- Add the fresh fix domain/codomain pairs to a retired frontier. -/
theorem RetiredFrontierFresh.consFixTargets
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    {frontier : List (Ty × STy)} {domain codomain : STy}
    (fresh : RetiredFrontierFresh signature current pending frontier)
    (below : PendingBelow signature supply current pending) :
    RetiredFrontierFresh signature current pending
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) := by
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | pairMember
  · exact below.freshTarget_avoids cutMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · obtain ⟨caps, targets⟩ := below cut cutMember
    constructor
    · intro varId generalized free
      simp [Ty.fcv] at free
    · intro varId generalized free
      simp only [Ty.ftv, List.mem_singleton] at free
      subst varId
      exact (Nat.not_lt_of_ge (Nat.le_succ supply.nextTy))
        (targets (supply.nextTy + 1) generalized)
  · exact fresh cut cutMember pair oldMember

/-- Lift the lambda preparation frame together with retired freshness. -/
theorem WRetiredStableFrameAt.prepareLamBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {rawContext : Context} {selectedContext : SCtx} {name : String}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (prevailingBounded : prevailing.BoundedBy supply)
    (below : PendingBelow signature supply prevailing pending)
    (domain : STy) :
    WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 1 }
      (DM.extendFreshTarget post supply.nextTy domain) prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      ((.var supply.nextTy, domain) :: frontier) pending := by
  have frame := state.stable.frame
  have outer : WContextRel post (rawContext.applySubst prevailing)
      selectedContext := frame.contexts active
  have outerBounded : (rawContext.applySubst prevailing).BoundedBy supply :=
    frame.contextsBounded active
  refine
    { stable :=
        { frame := frame.prepareLamBody outer outerBounded prevailingBounded
            domain
          lets := state.stable.lets }
      retired := state.retired.consFreshTarget below
      contextsRetired := ?_
      pendingBelow := below.monoSupply (SupplyExtends.bumpTy supply 1) }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · have outer := state.contextsRetired cut cutMember
        (rawContext, selectedContext) active
    have domainFixed : prevailing.apply (.var supply.nextTy) =
        .var supply.nextTy := by
      simp [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        prevailingBounded.targetFixedAbove supply.nextTy (Nat.le_refl _)]
    have freshDomain := below.freshTarget_avoids cutMember
    have contextEq : Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext) =
      (name, Scheme.mono (.var supply.nextTy)) ::
        rawContext.applySubst prevailing := by
      simp [Context.applySubst, domainFixed]
    rw [contextEq]
    constructor
    · intro varId generalized member
      simp only [Context.fcv, List.flatMap_cons, Scheme.fcv, Scheme.mono,
        PolyTy.fcv_lift, List.mem_append] at member
      rcases member with inDomain | inOuter
      · exact freshDomain.caps varId generalized inDomain
      · exact outer.caps varId generalized inOuter
    · intro varId generalized member
      simp only [Context.ftv, List.flatMap_cons, Scheme.ftv, Scheme.mono,
        PolyTy.ftv_lift, List.mem_append] at member
      rcases member with inDomain | inOuter
      · exact freshDomain.targets varId generalized inDomain
      · exact outer.targets varId generalized inOuter
  · exact state.contextsRetired cut cutMember pair oldMember

/-- Lift direct-self fix preparation together with the two fresh retired-safe
target variables. -/
theorem WRetiredStableFrameAt.prepareFixBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {rawContext : Context} {selectedContext : SCtx}
    {self argument : String}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (prevailingBounded : prevailing.BoundedBy supply)
    (below : PendingBelow signature supply prevailing pending)
    (domain codomain : STy) :
    WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 2 }
      (DM.extendAppTargets post supply domain codomain) prevailing
      (((
        (argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
          rawContext,
        (argument, SScheme.mono domain) ::
          (self, SScheme.mono (.fn domain codomain)) :: selectedContext)) ::
        frames)
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) pending := by
  have frame := state.stable.frame
  have outer : WContextRel post (rawContext.applySubst prevailing)
      selectedContext := frame.contexts active
  have outerBounded : (rawContext.applySubst prevailing).BoundedBy supply :=
    frame.contextsBounded active
  refine
    { stable :=
        { frame := frame.prepareFixBody outer outerBounded prevailingBounded
            domain codomain
          lets := state.stable.lets }
      retired := state.retired.consFixTargets below
      contextsRetired := ?_
      pendingBelow := below.monoSupply (SupplyExtends.bumpTy supply 2) }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · have outer := state.contextsRetired cut cutMember
        (rawContext, selectedContext) active
    have domainFixed : prevailing.apply (.var supply.nextTy) =
        .var supply.nextTy := by
      simp [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        prevailingBounded.targetFixedAbove supply.nextTy (Nat.le_refl _)]
    have codomainFixed : prevailing.apply (.var (supply.nextTy + 1)) =
        .var (supply.nextTy + 1) := by
      simp [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        prevailingBounded.targetFixedAbove _ (Nat.le_succ supply.nextTy)]
    have functionFixed : prevailing.apply
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1))) =
          .fn (.var supply.nextTy) (.var (supply.nextTy + 1)) := by
      simp only [Subst.apply_fn, domainFixed, codomainFixed]
    have freshDomain := below.freshTarget_avoids cutMember
    have freshCodomain : cut.AvoidsTy signature prevailing
        (.var (supply.nextTy + 1)) := by
      constructor
      · intro _ _ member
        simp [Ty.fcv] at member
      · intro varId generalized member
        simp only [Ty.ftv, List.mem_singleton] at member
        subst varId
        have older := (below cut cutMember).2 _ generalized
        exact (Nat.not_lt_of_ge (Nat.le_succ supply.nextTy)) older
    have freshFunction := freshDomain.fn freshCodomain
    have contextEq : Context.applySubst prevailing
        ((argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
          rawContext) =
      (argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext.applySubst prevailing := by
      simp [Context.applySubst, domainFixed, functionFixed]
    rw [contextEq]
    constructor
    · intro varId generalized member
      simp only [Context.fcv, List.flatMap_cons, Scheme.fcv, Scheme.mono,
        PolyTy.fcv_lift, List.mem_append] at member
      rcases member with inDomain | inFunction | inOuter
      · exact freshDomain.caps varId generalized inDomain
      · exact freshFunction.caps varId generalized inFunction
      · exact outer.caps varId generalized inOuter
    · intro varId generalized member
      simp only [Context.ftv, List.flatMap_cons, Scheme.ftv, Scheme.mono,
        PolyTy.ftv_lift, List.mem_append] at member
      rcases member with inDomain | inFunction | inOuter
      · exact freshDomain.targets varId generalized inDomain
      · exact freshFunction.targets varId generalized inFunction
      · exact outer.targets varId generalized inOuter
  · exact state.contextsRetired cut cutMember pair oldMember

/-- Forget the innermost protected binder context without changing the
frontier or any retired-variable fact. -/
theorem WRetiredStableFrameAt.dropContextHead
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply post prevailing
      ((rawContext, selectedContext) :: frames) frontier pending) :
    WRetiredStableFrameAt signature supply post prevailing frames frontier
      pending :=
  { stable :=
      { frame := state.stable.frame.dropContextHead
        lets := state.stable.lets }
    retired := state.retired
    contextsRetired := by
      intro cut cutMember pair pairMember
      exact state.contextsRetired cut cutMember pair
        (List.mem_cons_of_mem _ pairMember)
    pendingBelow := state.pendingBelow }

/-- Collapse the leading body/domain frontier pairs to the lambda function
pair while preserving retired freshness. -/
theorem WRetiredStableFrameAt.finishLamTarget
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {bodyRaw domainRaw : Ty} {codomain domain : STy}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      ((bodyRaw, codomain) :: (domainRaw, domain) :: frontier) pending) :
    WRetiredStableFrameAt signature supply post prevailing frames
      ((.fn domainRaw bodyRaw, .fn domain codomain) :: frontier) pending := by
  refine
    { stable :=
        { frame := state.stable.frame.finishLamTarget
          lets := state.stable.lets }
      retired := ?_
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · apply PendingLetCut.AvoidsTy.fn
    · exact state.retired cut cutMember (domainRaw, domain) (by simp)
    · exact state.retired cut cutMember (bodyRaw, codomain) (by simp)
  · exact state.retired cut cutMember pair (by simp [oldMember])

/-- Structural tuple target protection preserves retired freshness when the
new product target itself avoids all pending generalized sets. -/
theorem WRetiredStableFrameAt.protectTupleTarget
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {rawTargets : List Ty} {selectedTargets : List STy}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (relation : WTargetListRel post prevailing rawTargets selectedTargets)
    (bounded : ∀ raw ∈ rawTargets,
      (prevailing.apply raw).BoundedBy supply)
    (avoids : ∀ cut ∈ pending,
      cut.AvoidsTy signature prevailing
        (prevailing.apply (.prod rawTargets))) :
    WRetiredStableFrameAt signature supply post prevailing frames
      ((prevailing.apply (.prod rawTargets), .prod selectedTargets) ::
        frontier) pending := by
  refine
    { stable :=
        { frame := state.stable.frame.protectTupleTarget relation bounded
          lets := state.stable.lets }
      retired := ?_
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · exact avoids cut cutMember
  · exact state.retired cut cutMember pair oldMember

end DM
end TypePM
