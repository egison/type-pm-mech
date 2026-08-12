import TypePM.DamasMilnerWLetStability
import TypePM.DamasMilnerWApp

/-!
# Retired generalized variables in the Damas--Milner W simulation

Once a `let` closes its locally inferred variables, subsequent ordinary
solver constraints must not mention those names.  This invariant is stronger
than boundedness and is exactly what turns exact-MGU support confinement into
the `LetCutConstraintSeparated` premise used by terminal stability.
-/

namespace TypePM
namespace DM

/-- No variable selected by one pending generalization occurs in a type at
the displayed current substitution. -/
structure PendingLetCut.AvoidsTy (signature : FrozenSig)
    (current : Subst) (cut : PendingLetCut) (target : Ty) : Prop where
  caps : ∀ varId,
    varId ∈ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ target.fcv
  targets : ∀ varId,
    varId ∈ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ target.ftv

theorem PendingLetCut.AvoidsTy.int
    (signature : FrozenSig) (current : Subst) (cut : PendingLetCut) :
    cut.AvoidsTy signature current .int := by
  constructor <;> intros <;> simp_all [Ty.fcv, Ty.ftv]

theorem PendingLetCut.AvoidsTy.fn
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {domain codomain : Ty}
    (domainFresh : cut.AvoidsTy signature current domain)
    (codomainFresh : cut.AvoidsTy signature current codomain) :
    cut.AvoidsTy signature current (.fn domain codomain) := by
  constructor
  · intro varId generalized member
    rcases List.mem_append.mp member with member | member
    · exact domainFresh.caps varId generalized member
    · exact codomainFresh.caps varId generalized member
  · intro varId generalized member
    rcases List.mem_append.mp member with member | member
    · exact domainFresh.targets varId generalized member
    · exact codomainFresh.targets varId generalized member

theorem PendingLetCut.AvoidsTy.prod
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {components : List Ty}
    (fresh : ∀ component ∈ components,
      cut.AvoidsTy signature current component) :
    cut.AvoidsTy signature current (.prod components) := by
  constructor
  · intro varId generalized member
    rw [Ty.fcv] at member
    obtain ⟨component, componentMember, free⟩ :=
      Ty.mem_fcvList_split member
    exact (fresh component componentMember).caps varId generalized free
  · intro varId generalized member
    rw [Ty.ftv] at member
    obtain ⟨component, componentMember, free⟩ :=
      Ty.mem_ftvList_split member
    exact (fresh component componentMember).targets varId generalized free

/-- Exact-MGU support and range confinement transports avoidance of one
retired generalized set through an ordinary solver cut.  The statement is
kept relative to the generalized set before the cut; generalization
naturality rewrites that set at the coupled-frame boundary below. -/
theorem PendingLetCut.AvoidsTy.applyOriginSafeExactPairedMGU
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {left right target : Ty} {delta : Subst}
    (fresh : cut.AvoidsTy signature current target)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : LetCutConstraintSeparated signature current cut left right) :
    cut.AvoidsTy signature current (delta.apply target) := by
  constructor
  · intro image generalized imageIn
    unfold Subst.apply at imageIn
    rcases Unification.Ty.mem_fcv_applyTarget _ _ _ imageIn with own | introduced
    · rw [Unification.Ty.fcv_applyCapability] at own
      rcases List.mem_flatMap.mp own with ⟨source, sourceIn, imageInSource⟩
      by_cases sourceConstraint : source ∈ left.fcv ++ right.fcv
      · exact separated.caps image generalized
          (exact.exact.2.2.2.1 source sourceConstraint image imageInSource)
      · rw [exact.exact.2.1 source sourceConstraint] at imageInSource
        have imageEq : image = source := by
          simpa [Cap.fcv] using imageInSource
        subst image
        exact fresh.caps source generalized sourceIn
    · rcases introduced with ⟨source, sourceIn, imageInSource⟩
      rw [Unification.Ty.ftv_applyCapability] at sourceIn
      by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
      · exact separated.caps image generalized
          (exact.exact.2.2.2.2.2.1 source sourceConstraint image imageInSource)
      · rw [exact.exact.2.2.1 source sourceConstraint] at imageInSource
        simp [Ty.fcv] at imageInSource
  · intro image generalized imageIn
    unfold Subst.apply at imageIn
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability] at imageIn
    rcases List.mem_flatMap.mp imageIn with
      ⟨source, sourceIn, imageInSource⟩
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact separated.targets image generalized
        (exact.exact.2.2.2.2.1 source sourceConstraint image imageInSource)
    · rw [exact.exact.2.2.1 source sourceConstraint] at imageInSource
      have imageEq : image = source := by
        simpa [Ty.ftv] using imageInSource
      subst image
      exact fresh.targets source generalized sourceIn

/-- Every pending generalized set avoids all normalized solver-visible types
in the protected frontier.  The frontier is the finite continuation surface
of the W induction. -/
def RetiredFrontierFresh (signature : FrozenSig) (current : Subst)
    (pending : List PendingLetCut) (frontier : List (Ty × STy)) : Prop :=
  ∀ cut ∈ pending, ∀ pair ∈ frontier,
    cut.AvoidsTy signature current pair.1

/-- A normalized protected context does not expose any metavariable retired
at a pending let boundary. -/
structure PendingLetCut.AvoidsContext (signature : FrozenSig)
    (current : Subst) (cut : PendingLetCut) (context : Context) : Prop where
  caps : ∀ varId,
    varId ∈ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ context.fcv
  targets : ∀ varId,
    varId ∈ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target) →
    varId ∉ context.ftv

/-- Every raw context protected by W is fresh for every retired set after the
displayed prevailing substitution has normalized it. -/
def RetiredContextsFresh (signature : FrozenSig) (current : Subst)
    (pending : List PendingLetCut) (frames : List (Context × SCtx)) : Prop :=
  ∀ cut ∈ pending, ∀ pair ∈ frames,
    cut.AvoidsContext signature current (pair.1.applySubst current)

/-- Every variable selected by a pending generalization is below the current
fresh supply.  Later binder allocation therefore cannot accidentally reuse a
retired name. -/
def PendingLetsBelow (signature : FrozenSig)
    (supply : InferenceBase.FreshSupply) (current : Subst)
    (pending : List PendingLetCut) : Prop :=
  ∀ cut ∈ pending,
    (∀ varId, varId ∈ signature.generalizedCapVars
      (cut.context.applySubst current) (current.apply cut.target) →
      varId.id < supply.nextCap) ∧
    (∀ varId, varId ∈ signature.generalizedTyVars
      (cut.context.applySubst current) (current.apply cut.target) →
      varId < supply.nextTy)

/-- Two frontier operands automatically satisfy the exact solver's pending
let separation requirement. -/
theorem RetiredFrontierFresh.separated
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {frontier : List (Ty × STy)}
    (fresh : RetiredFrontierFresh signature current pending frontier)
    {left right : Ty} {leftSelected rightSelected : STy}
    (leftMember : (left, leftSelected) ∈ frontier)
    (rightMember : (right, rightSelected) ∈ frontier) :
    ∀ cut ∈ pending,
      LetCutConstraintSeparated signature current cut left right := by
  intro cut cutMember
  have leftFresh := fresh cut cutMember (left, leftSelected) leftMember
  have rightFresh := fresh cut cutMember (right, rightSelected) rightMember
  constructor
  · intro varId generalized member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact leftFresh.caps varId generalized inLeft
    · exact rightFresh.caps varId generalized inRight
  · intro varId generalized member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact leftFresh.targets varId generalized inLeft
    · exact rightFresh.targets varId generalized inRight

/-- Weakening to a sub-frontier. -/
theorem RetiredFrontierFresh.of_subset
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {larger smaller : List (Ty × STy)}
    (fresh : RetiredFrontierFresh signature current pending larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    RetiredFrontierFresh signature current pending smaller := by
  intro cut cutMember pair pairMember
  exact fresh cut cutMember pair (subset pair pairMember)

theorem RetiredFrontierFresh.cons
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {frontier : List (Ty × STy)}
    {algorithm : Ty} {selected : STy}
    (head : ∀ cut ∈ pending, cut.AvoidsTy signature current algorithm)
    (tail : RetiredFrontierFresh signature current pending frontier) :
    RetiredFrontierFresh signature current pending
      ((algorithm, selected) :: frontier) := by
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · exact head cut cutMember
  · exact tail cut cutMember pair oldMember

/-- Registering a new let cut requires dropping its value target from the
continuation frontier.  The caller supplies precisely the fact that every
remaining continuation type avoids the just-closed generalized variables;
older retired cuts are inherited by subset weakening. -/
theorem RetiredFrontierFresh.register
    {signature : FrozenSig} {current : Subst}
    {pending : List PendingLetCut} {larger smaller : List (Ty × STy)}
    {newCut : PendingLetCut}
    (older : RetiredFrontierFresh signature current pending larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (newFresh : ∀ pair ∈ smaller,
      newCut.AvoidsTy signature current pair.1) :
    RetiredFrontierFresh signature current (newCut :: pending) smaller := by
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp cutMember with rfl | oldMember
  · exact newFresh pair pairMember
  · exact older cut oldMember pair (subset pair pairMember)

/-- Transport the retired-variable side condition through an exact cut once
the generalization-naturality layer has identified the binder lists before
and after the cut. -/
theorem RetiredFrontierFresh.applyOriginSafeExactPairedMGU
    {signature : FrozenSig} {current delta : Subst}
    {pending : List PendingLetCut} {frontier : List (Ty × STy)}
    {left right : Ty}
    (fresh : RetiredFrontierFresh signature current pending frontier)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (separated : ∀ cut ∈ pending,
      LetCutConstraintSeparated signature current cut left right)
    (capBinders : ∀ cut ∈ pending,
      signature.generalizedCapVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedCapVars
          (cut.context.applySubst current) (current.apply cut.target))
    (targetBinders : ∀ cut ∈ pending,
      signature.generalizedTyVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target)) :
    RetiredFrontierFresh signature (Subst.seq delta current) pending
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  intro cut cutMember pair pairMember
  rcases List.mem_map.mp pairMember with ⟨oldPair, oldMember, rfl⟩
  have transported :=
    (fresh cut cutMember oldPair oldMember).applyOriginSafeExactPairedMGU
      exact (separated cut cutMember)
  constructor
  · intro varId generalized
    apply transported.caps varId
    rw [← capBinders cut cutMember]
    exact generalized
  · intro varId generalized
    apply transported.targets varId
    rw [← targetBinders cut cutMember]
    exact generalized

/-- Exact target-only solver transport for one protected normalized context. -/
theorem PendingLetCut.AvoidsContext.applyLetStableExactPairedCut
    {signature : FrozenSig} {current delta : Subst} {cut : PendingLetCut}
    {pending : List PendingLetCut} {context : Context} {left right : Ty}
    (fresh : cut.AvoidsContext signature current context)
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta)
    (signatureClosed : signature.SchemesClosed)
    (member : cut ∈ pending) :
    cut.AvoidsContext signature (Subst.seq delta current)
      (context.applySubst delta) := by
  have capEq : delta.cap = CapSubst.id :=
    TypePM.DM.OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
      solverCut.exact
      solverCut.leftCapFree solverCut.rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    TypePM.DM.OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree
      solverCut.exact
      solverCut.leftCapFree solverCut.rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  constructor
  · intro varId generalized imageIn
    rw [solverCut.generalizedCapVars signatureClosed member] at generalized
    rw [deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree] at imageIn
    exact fresh.caps varId generalized imageIn
  · intro image generalized imageIn
    rw [solverCut.generalizedTyVars signatureClosed member] at generalized
    rw [Context.ftv_applySubst_flatMap] at imageIn
    rcases List.mem_flatMap.mp imageIn with
      ⟨source, sourceIn, imageInSource⟩
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact (solverCut.separated cut member).targets image generalized
        (solverCut.exact.exact.2.2.2.2.1 source sourceConstraint image
          imageInSource)
    · rw [solverCut.exact.exact.2.2.1 source sourceConstraint] at imageInSource
      have imageEq : image = source := by simpa [Ty.ftv] using imageInSource
      subst image
      exact fresh.targets source generalized sourceIn

/-- Pointwise context transport through one stable exact cut. -/
theorem RetiredContextsFresh.applyLetStableExactPairedCut
    {signature : FrozenSig} {current delta : Subst}
    {pending : List PendingLetCut} {frames : List (Context × SCtx)}
    {left right : Ty}
    (fresh : RetiredContextsFresh signature current pending frames)
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta)
    (signatureClosed : signature.SchemesClosed) :
    RetiredContextsFresh signature (Subst.seq delta current) pending frames := by
  intro cut cutMember pair pairMember
  rw [Context.applySubst_seq]
  exact (fresh cut cutMember pair pairMember).applyLetStableExactPairedCut
    solverCut signatureClosed cutMember

theorem PendingLetsBelow.mono
    {signature : FrozenSig} {supply successor : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    (below : PendingLetsBelow signature supply current pending)
    (extension : SupplyExtends supply successor) :
    PendingLetsBelow signature successor current pending := by
  intro cut member
  obtain ⟨caps, targets⟩ := below cut member
  exact ⟨
    fun varId generalized => Nat.lt_of_lt_of_le (caps varId generalized)
      extension.1,
    fun varId generalized => Nat.lt_of_lt_of_le (targets varId generalized)
      extension.2⟩

/-- Binder-list naturality also transports the below-supply fact; the solver
cut does not allocate any fresh names. -/
theorem PendingLetsBelow.applyOfBinderEqualities
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current delta : Subst} {pending : List PendingLetCut}
    (below : PendingLetsBelow signature supply current pending)
    (capBinders : ∀ cut ∈ pending,
      signature.generalizedCapVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedCapVars
          (cut.context.applySubst current) (current.apply cut.target))
    (targetBinders : ∀ cut ∈ pending,
      signature.generalizedTyVars
          (cut.context.applySubst (Subst.seq delta current))
          ((Subst.seq delta current).apply cut.target) =
        signature.generalizedTyVars
          (cut.context.applySubst current) (current.apply cut.target)) :
    PendingLetsBelow signature supply (Subst.seq delta current) pending := by
  intro cut cutMember
  constructor
  · intro varId generalized
    apply (below cut cutMember).1 varId
    rw [← capBinders cut cutMember]
    exact generalized
  · intro varId generalized
    apply (below cut cutMember).2 varId
    rw [← targetBinders cut cutMember]
    exact generalized

/-- A terminally stable W frame together with the missing retired-variable
freshness invariant. -/
structure WRetiredStableFrameAt (signature : FrozenSig)
    (supply : InferenceBase.FreshSupply) (post prevailing : Subst)
    (frames : List (Context × SCtx)) (frontier : List (Ty × STy))
    (pending : List PendingLetCut) : Prop where
  stable : WLetStableFrameAt signature supply post prevailing frames frontier
    pending
  retired : RetiredFrontierFresh signature prevailing pending frontier
  contextsRetired : RetiredContextsFresh signature prevailing pending frames
  pendingBelow : PendingLetsBelow signature supply prevailing pending

/-- Coupled exact-cut transport.  Frontier membership supplies solver
separation, exact-MGU support/range transports avoidance, and the syntactic
generalization theorem supplies both the audit step and binder equalities. -/
theorem WRetiredStableFrameAt.applyOriginSafeExactPairedMGU
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {left right : Ty}
    {leftSelected rightSelected : STy}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftMember : (left, leftSelected) ∈ frontier)
    (rightMember : (right, rightSelected) ∈ frontier)
    (factor : post = Subst.seq residual delta)
    (stepSafe : PendingLetStepsSafe signature prevailing delta pending)
    (capBinders : ∀ cut ∈ pending,
      signature.generalizedCapVars
          (cut.context.applySubst (Subst.seq delta prevailing))
          ((Subst.seq delta prevailing).apply cut.target) =
        signature.generalizedCapVars
          (cut.context.applySubst prevailing) (prevailing.apply cut.target))
    (targetBinders : ∀ cut ∈ pending,
      signature.generalizedTyVars
          (cut.context.applySubst (Subst.seq delta prevailing))
          ((Subst.seq delta prevailing).apply cut.target) =
        signature.generalizedTyVars
          (cut.context.applySubst prevailing) (prevailing.apply cut.target))
    (contextsFresh : RetiredContextsFresh signature
      (Subst.seq delta prevailing) pending frames) :
    WRetiredStableFrameAt signature supply residual
      (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  have separated := state.retired.separated leftMember rightMember
  exact
    { stable := state.stable.applyOriginSafeExactPairedMGU exact
        (state.stable.frame.frontierBounded (left, leftSelected) leftMember)
        (state.stable.frame.frontierBounded (right, rightSelected) rightMember)
        factor stepSafe
      retired := state.retired.applyOriginSafeExactPairedMGU exact separated
        capBinders targetBinders
      contextsRetired := contextsFresh
      pendingBelow := state.pendingBelow.applyOfBinderEqualities
        capBinders targetBinders }

/-- Oracle-free exact-cut boundary used by the DM W constructors.  Every
terminal-generalization and binder-preservation fact is projected from the
capability-inert exact solver certificate. -/
theorem WRetiredStableFrameAt.applyLetStableExactPairedCut
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut} {left right : Ty}
    {leftSelected rightSelected : STy}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (solverCut : LetStableExactPairedCut signature prevailing pending
      left right delta)
    (signatureClosed : signature.SchemesClosed)
    (leftMember : (left, leftSelected) ∈ frontier)
    (rightMember : (right, rightSelected) ∈ frontier)
    (factor : post = Subst.seq residual delta) :
    WRetiredStableFrameAt signature supply residual
      (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  exact state.applyOriginSafeExactPairedMGU solverCut.exact leftMember
    rightMember factor (solverCut.generalizations signatureClosed)
    (fun cut member => solverCut.generalizedCapVars signatureClosed member)
    (fun cut member => solverCut.generalizedTyVars signatureClosed member)
    (state.contextsRetired.applyLetStableExactPairedCut solverCut
      signatureClosed)

/-- Dropping a frontier prefix preserves the protected frame and all retired
freshness facts.  Let uses this after consuming the value target relation into
its generalized binding witness. -/
theorem WRetiredStableFrameAt.dropFrontier
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {larger smaller : List (Ty × STy)} {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      larger pending)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    WRetiredStableFrameAt signature supply post prevailing frames smaller
      pending := by
  refine
    { stable :=
        { frame :=
            { contexts := state.stable.frame.contexts
              types := fun {algorithm} {selected} member =>
                state.stable.frame.types (subset (algorithm, selected) member)
              contextsBounded := state.stable.frame.contextsBounded
              frontierBounded := fun pair member =>
                state.stable.frame.frontierBounded pair (subset pair member) }
          lets := state.stable.lets }
      retired := state.retired.of_subset subset
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow }

/-- Consume the just-inferred value pair, weaken to the let-body continuation
frontier, and register its newly closed variables as retired in one step. -/
theorem WRetiredStableFrameAt.registerLetAfterDrop
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {larger smaller : List (Ty × STy)} {pending : List PendingLetCut}
    {context : Context} {target : Ty}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      larger pending)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (newFresh : ∀ pair ∈ smaller,
      (PendingLetCut.mk context target prevailing).AvoidsTy
        signature prevailing pair.1)
    (newContextsFresh : ∀ pair ∈ frames,
      (PendingLetCut.mk context target prevailing).AvoidsContext
        signature prevailing (pair.1.applySubst prevailing))
    (newBelow :
      (∀ varId, varId ∈ signature.generalizedCapVars
          (context.applySubst prevailing) (prevailing.apply target) →
        varId.id < supply.nextCap) ∧
      (∀ varId, varId ∈ signature.generalizedTyVars
          (context.applySubst prevailing) (prevailing.apply target) →
        varId < supply.nextTy))
    (idempotent : prevailing.Idempotent) :
    WRetiredStableFrameAt signature supply post prevailing frames smaller
      (PendingLetCut.mk context target prevailing :: pending) := by
  let dropped := state.dropFrontier subset
  refine
    { stable := dropped.stable.registerLet idempotent
      retired := state.retired.register subset newFresh
      contextsRetired := by
        intro cut cutMember pair pairMember
        rcases List.mem_cons.mp cutMember with rfl | oldMember
        · exact newContextsFresh pair pairMember
        · exact state.contextsRetired cut oldMember pair pairMember
      pendingBelow := ?_ }
  intro cut cutMember
  rcases List.mem_cons.mp cutMember with rfl | oldMember
  · exact newBelow
  · exact state.pendingBelow cut oldMember

/-- Canonical scheme opening changes only the residual post and hence leaves
all retired-variable facts unchanged. -/
theorem WRetiredStableFrameAt.extendSchemeOpening
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {base prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {scheme : Scheme}
    (state : WRetiredStableFrameAt signature supply base prevailing frames
      frontier pending)
    (opening : (scheme.applyMeta base).ValueOpening) :
    WRetiredStableFrameAt signature supply
      (DM.extendSchemeOpening base supply scheme opening) prevailing
      frames frontier pending :=
  { stable := state.stable.extendSchemeOpening opening
    retired := state.retired
    contextsRetired := state.contextsRetired
    pendingBelow := state.pendingBelow }

/-- Allocating one fresh monomorphic target preserves retirement: every
pending generalized target variable is strictly below the fresh identifier. -/
theorem WRetiredStableFrameAt.extendFreshTarget
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {base prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply base prevailing frames
      frontier pending)
    (selected : STy) :
    WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 1 }
      (DM.extendFreshTarget base supply.nextTy selected) prevailing frames
      ((.var supply.nextTy, selected) :: frontier) pending := by
  refine
    { stable :=
        { frame := state.stable.frame.extendFreshTarget selected
          lets := state.stable.lets }
      retired := ?_
      contextsRetired := state.contextsRetired
      pendingBelow := PendingLetsBelow.mono state.pendingBelow
        (SupplyExtends.bumpTy supply 1) }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · constructor
    · intro _ _
      simp [Ty.fcv]
    · intro varId generalized member
      simp only [Ty.ftv, List.mem_singleton] at member
      subst varId
      have below := (state.pendingBelow cut cutMember).2 _ generalized
      exact (Nat.lt_irrefl _ below)
  · exact state.retired cut cutMember pair oldMember

/-- Allocate the fresh application/fix domain and codomain pair. -/
theorem WRetiredStableFrameAt.protectAppTargets
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {base prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    (state : WRetiredStableFrameAt signature supply base prevailing frames
      frontier pending)
    (domain codomain : STy) :
    WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 2 }
      (DM.extendAppTargets base supply domain codomain) prevailing frames
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) pending := by
  refine
    { stable :=
        { frame := state.stable.frame.protectAppTargets domain codomain
          lets := state.stable.lets }
      retired := ?_
      contextsRetired := state.contextsRetired
      pendingBelow := PendingLetsBelow.mono state.pendingBelow
        (SupplyExtends.bumpTy supply 2) }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | pairMember
  · constructor
    · intro _ _
      simp [Ty.fcv]
    · intro varId generalized member
      simp only [Ty.ftv, List.mem_singleton] at member
      subst varId
      exact Nat.lt_irrefl _ ((state.pendingBelow cut cutMember).2 _ generalized)
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · constructor
    · intro _ _
      simp [Ty.fcv]
    · intro varId generalized member
      simp only [Ty.ftv, List.mem_singleton] at member
      subst varId
      have below := (state.pendingBelow cut cutMember).2 _ generalized
      exact (Nat.not_lt_of_ge (Nat.le_succ _) below)
  · exact state.retired cut cutMember pair oldMember

/-- Canonical empty-prefix frame used at the public DM root. -/
theorem WRetiredStableFrameAt.initial
    (signature : FrozenSig) (context : SCtx) :
    WRetiredStableFrameAt signature
      (Inference.initialSupply signature context.emb) Subst.id Subst.id
      [(context.emb, context)] [] [] := by
  refine
    { stable :=
        { frame :=
            { contexts := ?_
              types := WTypeFrame.nil Subst.id
              contextsBounded := ?_
              frontierBounded := by simp }
          lets := by simp [PendingLetStability] }
      retired := by simp [RetiredFrontierFresh]
      contextsRetired := by simp [RetiredContextsFresh]
      pendingBelow := by simp [PendingLetsBelow] }
  · intro rawContext selectedContext member
    simp only [List.mem_singleton] at member
    cases member
    change WContextRel Subst.id (context.emb.applySubst Subst.id) context
    rw [Context.applySubst_id]
    exact WContextRel.emb_id context
  · intro rawContext selectedContext member
    simp only [List.mem_singleton] at member
    cases member
    simpa using initialSupply_context_boundedBy signature context.emb

end DM
end TypePM
