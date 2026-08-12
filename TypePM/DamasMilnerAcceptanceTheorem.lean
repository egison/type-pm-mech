import TypePM.DamasMilnerWApp
import TypePM.DamasMilnerWTuple
import TypePM.DamasMilnerWLet
import TypePM.DamasMilnerWLetStability
import TypePM.DamasMilnerWAuditPlan
import TypePM.DamasMilnerWFix
import TypePM.DamasMilnerWNormalized
import TypePM.DamasMilnerWNormalizedVar
import TypePM.DamasMilnerWRetiredStructural
import TypePM.DamasMilnerWCompleteSteps
import TypePM.DamasMilnerWCutNormalization
import TypePM.DamasMilnerWErasedLetBridge
import TypePM.DamasMilnerWLetGenerative
import TypePM.DamasMilnerWGenerativeTransport
import TypePM.DamasMilnerWGenerativity

/-!
# Public Algorithm W acceptance for the Damas--Milner fragment

This module carries the final mutual completeness induction.  Its result
packages keep the executable demand synthesis, empty-ledger origin, and audit
at the same existential terminal substitution.  Protected contexts and type
equations are threaded independently of the proof-relevant audit tree.
-/

namespace TypePM
namespace DM

/-- An exact target-only solver cut preserves capability-inertness of the
active algorithm context. -/
theorem ContextCapFree.applyLetStableExactPairedCut
    {signature : FrozenSig} {rawContext : Context} {current delta : Subst}
    {pending : List PendingLetCut} {left right : Ty}
    (free : (rawContext.applySubst current).fcv = [])
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta) :
    (rawContext.applySubst (Subst.seq delta current)).fcv = [] := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
      solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree
      solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  rw [Context.applySubst_seq, deltaEq,
    Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree, free]

@[simp] theorem Subst.seq_id_left (earlier : Subst) :
    Subst.seq Subst.id earlier = earlier := by
  cases earlier with
  | mk cap target =>
      have capEq : CapSubst.id.comp cap = cap := by
        funext varId
        exact Cap.apply_id (cap varId)
      have targetEq :
          (fun varId => Subst.id.apply (target varId)) = target := by
        funext varId
        exact Subst.apply_id (target varId)
      unfold Subst.seq Subst.id
      change Subst.mk (CapSubst.id.comp cap)
          (fun varId => Subst.id.apply (target varId)) = Subst.mk cap target
      rw [capEq, targetEq]

/-- Complete output of one expression branch of the DM Algorithm W
simulation.  The selected DM target is related to the normalized raw target;
it is not required to be the syntactic target eventually published by
inference. -/
structure WCompleteWitness
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (expression : Expr)
    (selectedTarget : STy) (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) where
  successor : InferenceBase.FreshSupply
  prevailing' : Subst
  rawTarget : Ty
  post : Subst
  frontier : List (Ty × STy)
  derived : DemandSynth signature supply prevailing rawContext expression
    rawTarget successor prevailing'
  origin : DemandSynthOrigin signature derived [] []
  auditPlan : WSynthAuditPlan signature (origin := origin)
  pending : List PendingLetCut
  stability : PendingLetStability signature prevailing' pending
  retains : ∀ cut, cut ∈ inputPending → cut ∈ pending
  auditCuts : ∀ cut, cut ∈ auditPlan.cuts → cut ∈ pending
  postAdmissible : AdmissiblePost [] post
  prevailingBounded : prevailing'.BoundedBy successor
  prevailingIdempotent : prevailing'.Idempotent
  frame : WProtectedFrameAt successor post prevailing' frames frontier
  retired : RetiredFrontierFresh signature prevailing' pending frontier
  contextsRetired : RetiredContextsFresh signature prevailing' pending frames
  pendingBelow : PendingLetsBelow signature successor prevailing' pending
  pendingCapFree : PendingLetsCapFree prevailing' pending
  suffix : Subst
  prevailing_eq : prevailing' = Subst.seq suffix prevailing
  frontierRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ inputFrontier →
      (suffix.apply algorithm, selected) ∈ frontier
  targetMember :
    (prevailing'.apply rawTarget, selectedTarget) ∈ frontier

/-- Propositional closure of the proof-relevant W result.  `Nonempty` keeps
the public theorem in `Prop` while allowing the witness to carry executable
supplies, substitutions, and dependent derivations. -/
def WCompleteResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context) (expression : Expr)
    (selectedTarget : STy) (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WCompleteWitness signature supply prevailing rawContext expression
    selectedTarget frames inputFrontier inputPending)

/-- A complete W result whose final normalized context and target are both
decoded by one shared one-sort residual.  The algorithm context and target
are genuine outputs because ordinary solver cuts can refine them. -/
structure WNormalizedCompleteWitness
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
    (inputPending : List PendingLetCut) : Type where
  complete : WCompleteWitness signature supply prevailing rawContext expression
    selectedTarget frames inputFrontier inputPending
  algorithmContext : SCtx
  algorithmTarget : STy
  residual : SSubst
  post_eq : complete.post = SSubst.paired residual
  context : ErasedDMContextView residual selectedContext
    (rawContext.applySubst complete.prevailing')
  scope : ResidualContextScope residual
    (rawContext.applySubst complete.prevailing') selectedContext
  protectedScopes : ∀ pair ∈ frames,
    ResidualContextScope residual
      (pair.1.applySubst complete.prevailing') pair.2
  target : NormalizedDMTargetView residual algorithmTarget selectedTarget
    (complete.prevailing'.apply complete.rawTarget)
  floorCaps : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ supply.nextTy
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing')
    (rawContext.applySubst complete.prevailing')
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext rawContext
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst complete.prevailing')
    (rawContext.applySubst complete.prevailing')
  protectedOld : ProtectedOldFreeAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing') complete.frontier
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst complete.prevailing') provenanceFrames
    complete.prevailing'
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing') complete.suffix
    provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (complete.suffix.apply algorithm, selected) ∈ complete.frontier
  generativity : GenerativitySurfaceFrameAt generativityObligations
    complete.prevailing'
  generativityContexts : GenerativitySurfaceContextsAt generativityObligations
    complete.prevailing' (rawContext.applySubst complete.prevailing')
  generativityValid : GenerativitySurfaceValid supply rawContext
    generativityObligations
  currentObligation : GenerativitySurfaceObligation.current supply rawContext ∈
    generativityObligations
  targetGenerative : ∀ obligation ∈ generativityObligations,
    OldFreeInContextAt obligation.floor
      (obligation.owner.applySubst complete.prevailing')
      (complete.prevailing'.apply complete.rawTarget)
  localOldFree : OldFreeInContextAt supply
    (rawContext.applySubst complete.prevailing')
    (complete.prevailing'.apply complete.rawTarget)
  protectedCovered : ProtectedFreeCovered
    (rawContext.applySubst complete.prevailing') frames complete.prevailing'
  contextSuffix : ProtectedContextsSuffix rawContext frames

  pendingCapFree : PendingLetsCapFree complete.prevailing' complete.pending

def WNormalizedCompleteResult
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
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WNormalizedCompleteWitness signature supply prevailing rawContext
    expression selectedContext selectedTarget provenanceFloor provenanceContext
    provenanceFrames provenanceFrontier generativityObligations frames
    inputFrontier inputPending)

/-- Sound paired-continuation strengthening of a normalized W witness.  The
constructor-control old-free surface is intentionally separate: a full continuation
frontier satisfies the retained disjunction and membership invariant, but
need not be old-free. -/
structure WPairedNormalizedCompleteWitness
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
    (inputPending : List PendingLetCut) : Type where
  normalized : WNormalizedCompleteWitness signature supply prevailing
    rawContext expression selectedContext selectedTarget
    InferenceBase.FreshSupply.empty [] [] []
    generativityObligations frames inputFrontier inputPending
  /-- The active normalized DM context remains capability-inert.  This is
  the constructor-threaded fact used when a completed value is registered as
  a pending let cut; it is not reconstructed from the selected view. -/
  contextCapFree :
    (rawContext.applySubst normalized.complete.prevailing').fcv = []
  floorCaps : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ supply.nextTy
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst normalized.complete.prevailing')
    (rawContext.applySubst normalized.complete.prevailing')
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext rawContext
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst normalized.complete.prevailing')
    (rawContext.applySubst normalized.complete.prevailing')
  targetOld : OldFreeInContextAt provenanceFloor
    (provenanceContext.applySubst normalized.complete.prevailing')
    (normalized.complete.prevailing'.apply normalized.complete.rawTarget)
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst normalized.complete.prevailing')
    provenanceFrames normalized.complete.prevailing'
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst normalized.complete.prevailing')
    normalized.complete.suffix provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (normalized.complete.suffix.apply algorithm, selected) ∈
        normalized.complete.frontier
  inputFrontierNormalized : ∀ pair ∈ inputFrontier,
    prevailing.apply pair.1 = pair.1
  surfacesRetained : GenerativitySurfaceRetainedAt generativityObligations
    normalized.complete.prevailing'
  surfacesMembers : GenerativitySurfaceMembersAt generativityObligations
    normalized.complete.prevailing' normalized.complete.frontier
  frontierNormalized : ∀ pair ∈ normalized.complete.frontier,
    normalized.complete.prevailing'.apply pair.1 = pair.1
  currentPaired : GenerativitySurfaceObligation.currentPaired supply rawContext
    inputFrontier ∈ generativityObligations

def WPairedNormalizedCompleteResult
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
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WPairedNormalizedCompleteWitness signature supply prevailing
    rawContext expression selectedContext selectedTarget provenanceFloor
    provenanceContext provenanceFrames provenanceFrontier
    generativityObligations frames inputFrontier inputPending)

/-- Build the proof-relevant audit only at the final terminal. -/
theorem WCompleteWitness.audit
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {expression : Expr}
    {selectedTarget : STy} {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (result : WCompleteWitness signature supply prevailing rawContext
      expression selectedTarget frames inputFrontier inputPending) :
    Nonempty (DemandSynthTerminalAudit result.prevailing' signature
      result.origin) :=
  result.auditPlan.build result.prevailing'
    (result.stability.of_subset result.auditCuts)

/-- Reassemble the coupled retired-state package carried fieldwise by a
complete result. -/
theorem WCompleteWitness.retiredState
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context} {expression : Expr}
    {selectedTarget : STy} {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (result : WCompleteWitness signature supply prevailing rawContext
      expression selectedTarget frames inputFrontier inputPending) :
    WRetiredStableFrameAt signature result.successor result.post
      result.prevailing' frames result.frontier result.pending :=
  { stable := ⟨result.frame, result.stability⟩
    retired := result.retired
    contextsRetired := result.contextsRetired
    pendingBelow := result.pendingBelow }

/-! ## Chronological list results -/

structure WTypingsFinalWitness
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedTargets : List STy)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) where
  successor : InferenceBase.FreshSupply
  prevailing' : Subst
  rawTargets : List Ty
  post : Subst
  frontier : List (Ty × STy)
  derived : DemandSynths signature supply prevailing rawContext expressions
    rawTargets successor prevailing'
  origin : DemandSynthsOrigin signature derived [] []
  auditPlan : WSynthsAuditPlan signature (origin := origin)
  pending : List PendingLetCut
  stability : PendingLetStability signature prevailing' pending
  retains : ∀ cut, cut ∈ inputPending → cut ∈ pending
  auditCuts : ∀ cut, cut ∈ auditPlan.cuts → cut ∈ pending
  equations : WTargetListRel post prevailing' rawTargets selectedTargets
  targetsFresh : ∀ cut ∈ pending, ∀ raw ∈ rawTargets,
    cut.AvoidsTy signature prevailing' (prevailing'.apply raw)
  targetsBounded : ∀ raw ∈ rawTargets,
    (prevailing'.apply raw).BoundedBy successor
  postAdmissible : AdmissiblePost [] post
  prevailingBounded : prevailing'.BoundedBy successor
  prevailingIdempotent : prevailing'.Idempotent
  frame : WProtectedFrameAt successor post prevailing' frames frontier
  retired : RetiredFrontierFresh signature prevailing' pending frontier
  contextsRetired : RetiredContextsFresh signature prevailing' pending frames
  pendingBelow : PendingLetsBelow signature successor prevailing' pending
  pendingCapFree : PendingLetsCapFree prevailing' pending
  suffix : Subst
  prevailing_eq : prevailing' = Subst.seq suffix prevailing
  frontierRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ inputFrontier →
      (suffix.apply algorithm, selected) ∈ frontier

def WTypingsFinalResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedTargets : List STy)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WTypingsFinalWitness signature supply prevailing rawContext
    expressions selectedTargets frames inputFrontier inputPending)

/-- Normalized chronological list output under one shared residual. -/
structure WNormalizedTypingsWitness
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedContext : SCtx)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Type where
  complete : WTypingsFinalWitness signature supply prevailing rawContext
    expressions selectedTargets frames inputFrontier inputPending
  algorithmContext : SCtx
  algorithmTargets : List STy
  residual : SSubst
  post_eq : complete.post = SSubst.paired residual
  context : ErasedDMContextView residual selectedContext
    (rawContext.applySubst complete.prevailing')
  scope : ResidualContextScope residual
    (rawContext.applySubst complete.prevailing') selectedContext
  protectedScopes : ∀ pair ∈ frames,
    ResidualContextScope residual
      (pair.1.applySubst complete.prevailing') pair.2
  targets : NormalizedDMTargetsView residual algorithmTargets selectedTargets
    (complete.rawTargets.map complete.prevailing'.apply)
  floorCaps : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ supply.nextTy
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing')
    (rawContext.applySubst complete.prevailing')
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext rawContext
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst complete.prevailing')
    (rawContext.applySubst complete.prevailing')
  protectedOld : ProtectedOldFreeAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing') complete.frontier
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst complete.prevailing') provenanceFrames
    complete.prevailing'
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst complete.prevailing') complete.suffix
    provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (complete.suffix.apply algorithm, selected) ∈ complete.frontier
  generativity : GenerativitySurfaceFrameAt generativityObligations
    complete.prevailing'
  generativityContexts : GenerativitySurfaceContextsAt generativityObligations
    complete.prevailing' (rawContext.applySubst complete.prevailing')
  targetsLocalOldFree : ∀ raw ∈ complete.rawTargets,
    OldFreeInContextAt supply
      (rawContext.applySubst complete.prevailing')
      (complete.prevailing'.apply raw)
  targetsGenerative : ∀ obligation ∈ generativityObligations,
    ∀ raw ∈ complete.rawTargets,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst complete.prevailing')
        (complete.prevailing'.apply raw)
  generativityValid : GenerativitySurfaceValid supply rawContext
    generativityObligations
  currentObligation : GenerativitySurfaceObligation.current supply rawContext ∈
    generativityObligations
  protectedCovered : ProtectedFreeCovered
    (rawContext.applySubst complete.prevailing') frames complete.prevailing'
  contextSuffix : ProtectedContextsSuffix rawContext frames

def WNormalizedTypingsResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedContext : SCtx)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WNormalizedTypingsWitness signature supply prevailing rawContext
    expressions selectedContext selectedTargets provenanceFloor
    provenanceContext provenanceFrames provenanceFrontier
    generativityObligations frames inputFrontier inputPending)

/-- Paired-surface strengthening of a chronological normalized traversal. -/
structure WPairedNormalizedTypingsWitness
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedContext : SCtx)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Type where
  normalized : WNormalizedTypingsWitness signature supply prevailing rawContext
    expressions selectedContext selectedTargets InferenceBase.FreshSupply.empty
    [] [] []
    generativityObligations frames inputFrontier inputPending
  /-- Capability-inertness of the active context after the chronological
  traversal, used by enclosing let registration just as in the expression
  witness. -/
  contextCapFree :
    (rawContext.applySubst normalized.complete.prevailing').fcv = []
  floorCaps : provenanceFloor.nextCap ≤ supply.nextCap
  floorTargets : provenanceFloor.nextTy ≤ supply.nextTy
  contextOld : OldContextCoveredAt provenanceFloor
    (provenanceContext.applySubst normalized.complete.prevailing')
    (rawContext.applySubst normalized.complete.prevailing')
  contextProvenanceSuffix : ProvenanceContextSuffix provenanceContext rawContext
  provenanceIncluded : ProvenanceContextIncluded
    (provenanceContext.applySubst normalized.complete.prevailing')
    (rawContext.applySubst normalized.complete.prevailing')
  targetsOld : ∀ raw ∈ normalized.complete.rawTargets,
    OldFreeInContextAt provenanceFloor
      (provenanceContext.applySubst normalized.complete.prevailing')
      (normalized.complete.prevailing'.apply raw)
  provenanceSuffix : ProtectedContextsSuffix provenanceContext provenanceFrames
  provenanceCovered : ProtectedFreeCovered
    (provenanceContext.applySubst normalized.complete.prevailing')
    provenanceFrames normalized.complete.prevailing'
  retainedOuter : RetainedOldOrContextAt provenanceFloor
    (provenanceContext.applySubst normalized.complete.prevailing')
    normalized.complete.suffix provenanceFrontier
  provenanceRetains : ∀ algorithm selected,
    (algorithm, selected) ∈ provenanceFrontier →
      (normalized.complete.suffix.apply algorithm, selected) ∈
        normalized.complete.frontier
  inputFrontierNormalized : ∀ pair ∈ inputFrontier,
    prevailing.apply pair.1 = pair.1
  surfacesRetained : GenerativitySurfaceRetainedAt generativityObligations
    normalized.complete.prevailing'
  surfacesMembers : GenerativitySurfaceMembersAt generativityObligations
    normalized.complete.prevailing' normalized.complete.frontier
  frontierNormalized : ∀ pair ∈ normalized.complete.frontier,
    normalized.complete.prevailing'.apply pair.1 = pair.1
  currentPaired : GenerativitySurfaceObligation.currentPaired supply rawContext
    inputFrontier ∈ generativityObligations

def WPairedNormalizedTypingsResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedContext : SCtx)
    (selectedTargets : List STy)
    (provenanceFloor : InferenceBase.FreshSupply)
    (provenanceContext : Context)
    (provenanceFrames : List (Context × SCtx))
    (provenanceFrontier : List (Ty × STy))
    (generativityObligations : List GenerativitySurfaceObligation)
    (frames : List (Context × SCtx))
    (inputFrontier : List (Ty × STy))
    (inputPending : List PendingLetCut) : Prop :=
  Nonempty (WPairedNormalizedTypingsWitness signature supply prevailing
    rawContext expressions selectedContext selectedTargets provenanceFloor
    provenanceContext provenanceFrames provenanceFrontier
    generativityObligations frames inputFrontier inputPending)

/-- Reassemble the coupled state after a chronological list traversal. -/
theorem WTypingsFinalWitness.retiredState
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {expressions : List Expr} {selectedTargets : List STy}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (result : WTypingsFinalWitness signature supply prevailing rawContext
      expressions selectedTargets frames inputFrontier inputPending) :
    WRetiredStableFrameAt signature result.successor result.post
      result.prevailing' frames result.frontier result.pending :=
  { stable := ⟨result.frame, result.stability⟩
    retired := result.retired
    contextsRetired := result.contextsRetired
    pendingBelow := result.pendingBelow }

/-- Empty chronological traversal. -/
theorem Typings.w_complete_nil
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    (stableFrame : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    WTypingsFinalResult signature supply prevailing rawContext [] [] frames
      frontier pending := by
  exact ⟨
    { successor := supply
      prevailing' := prevailing
      rawTargets := []
      post := post
      frontier := frontier
      derived := DemandSynths.nil
      origin := DemandSynthsOrigin.nil
      auditPlan := WSynthsAuditPlan.nil
      pending := pending
      stability := stableFrame.stable.lets
      retains := fun _ member => member
      auditCuts := by simp [WSynthsAuditPlan.nil]
      equations := WTargetListRel.nil
      targetsFresh := by simp
      targetsBounded := by simp
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := stableFrame.stable.frame
      retired := stableFrame.retired
      contextsRetired := stableFrame.contextsRetired
      pendingBelow := stableFrame.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        simpa only [Subst.apply_id] using member }
    ⟩

/-- Chronological cons packaging after the tail has transported the head's
target equation to its final residual.  The mutual induction obtains the two
displayed head facts from the protected pair supplied to the tail call. -/
theorem Typings.w_complete_cons_of_results
    {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    {rawContext : Context} {expression : Expr} {expressions : List Expr}
    {selected : STy} {selectedTargets : List STy}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (headResult : WCompleteResult signature supply prevailing rawContext
      expression selected frames inputFrontier inputPending)
    (tailResult : ∀ head : WCompleteWitness signature supply prevailing
        rawContext expression selected frames inputFrontier inputPending,
      WTypingsFinalResult signature head.successor head.prevailing'
        rawContext expressions selectedTargets frames head.frontier
        head.pending) :
    WTypingsFinalResult signature supply prevailing rawContext
      (expression :: expressions) (selected :: selectedTargets) frames
      inputFrontier inputPending := by
  rcases headResult with ⟨head⟩
  rcases tailResult head with ⟨tail⟩
  let derived : DemandSynths signature supply prevailing rawContext
      (expression :: expressions) (head.rawTarget :: tail.rawTargets)
      tail.successor tail.prevailing' :=
    DemandSynths.cons head.derived tail.derived
  let origin : DemandSynthsOrigin signature derived [] [] :=
    DemandSynthsOrigin.cons head.origin tail.origin
  let auditPlan : WSynthsAuditPlan signature (origin := origin) :=
    WSynthsAuditPlan.cons head.auditPlan tail.auditPlan
  have headFinalMember :
      (tail.prevailing'.apply head.rawTarget, selected) ∈ tail.frontier := by
    have retained := tail.frontierRetains _ _ head.targetMember
    rw [tail.prevailing_eq, Subst.seq_apply]
    exact retained
  have headEquation :
      tail.post.apply (tail.prevailing'.apply head.rawTarget) = selected.emb :=
    tail.frame.types headFinalMember
  have headFinalBounded :
      (tail.prevailing'.apply head.rawTarget).BoundedBy tail.successor :=
    tail.frame.frontierBounded _ headFinalMember
  exact ⟨
    { successor := tail.successor
      prevailing' := tail.prevailing'
      rawTargets := head.rawTarget :: tail.rawTargets
      post := tail.post
      frontier := tail.frontier
      derived := derived
      origin := origin
      auditPlan := auditPlan
      pending := tail.pending
      stability := tail.stability
      retains := fun cut member =>
        tail.retains cut (head.retains cut member)
      auditCuts := by
        intro cut member
        rcases List.mem_append.mp member with headMember | tailMember
        · exact tail.retains cut (head.auditCuts cut headMember)
        · exact tail.auditCuts cut tailMember
      equations := WTargetListRel.cons headEquation tail.equations
      targetsFresh := by
        intro cut cutMember raw member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact tail.retired cut cutMember _ headFinalMember
        · exact tail.targetsFresh cut cutMember raw tailMember
      targetsBounded := by
        intro raw member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headFinalBounded
        · exact tail.targetsBounded raw tailMember
      postAdmissible := tail.postAdmissible
      prevailingBounded := tail.prevailingBounded
      prevailingIdempotent := tail.prevailingIdempotent
      frame := tail.frame
      retired := tail.retired
      contextsRetired := tail.contextsRetired
      pendingBelow := tail.pendingBelow
      pendingCapFree := tail.pendingCapFree
      suffix := Subst.seq tail.suffix head.suffix
      prevailing_eq := by
        calc
          tail.prevailing' = Subst.seq tail.suffix head.prevailing' :=
            tail.prevailing_eq
          _ = Subst.seq tail.suffix
              (Subst.seq head.suffix prevailing) :=
            congrArg (Subst.seq tail.suffix) head.prevailing_eq
          _ = Subst.seq (Subst.seq tail.suffix head.suffix) prevailing :=
            PhasedPost.seq_assoc tail.suffix head.suffix prevailing
      frontierRetains := by
        intro algorithm selected member
        have first := head.frontierRetains algorithm selected member
        have second := tail.frontierRetains _ _ first
        simpa only [Subst.seq_apply] using second }
    ⟩

/-- Finalize a chronologically complete component traversal as one tuple
result.  No solver step occurs at this boundary. -/
theorem Typing.w_complete_tuple_of_children
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {expressions : List Expr} {selectedTargets : List STy}
    {frames : List (Context × SCtx)}
    {inputFrontier : List (Ty × STy)}
    {inputPending : List PendingLetCut}
    (childrenResult : WTypingsFinalResult signature supply prevailing
      rawContext expressions selectedTargets frames inputFrontier inputPending) :
    WCompleteResult signature supply prevailing rawContext
      (.tuple expressions) (.prod selectedTargets) frames inputFrontier
      inputPending := by
  rcases childrenResult with ⟨children⟩
  let derived : DemandSynth signature supply prevailing rawContext
      (.tuple expressions) (.prod children.rawTargets)
      children.successor children.prevailing' :=
    DemandSynth.tuple children.derived
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.tuple children.origin
  have finalFrame := children.frame.protectTupleTarget
    children.equations children.targetsBounded
  have productFresh : ∀ cut ∈ children.pending,
      cut.AvoidsTy signature children.prevailing'
        (children.prevailing'.apply (.prod children.rawTargets)) := by
    intro cut cutMember
    simp only [Subst.apply_prod]
    apply PendingLetCut.AvoidsTy.prod
    intro component componentMember
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp componentMember
    exact children.targetsFresh cut cutMember raw rawMember
  exact ⟨
    { successor := children.successor
      prevailing' := children.prevailing'
      rawTarget := .prod children.rawTargets
      post := children.post
      frontier :=
        (children.prevailing'.apply (.prod children.rawTargets),
          .prod selectedTargets) :: children.frontier
      derived := derived
      origin := origin
      auditPlan := WSynthAuditPlan.tuple children.auditPlan
      pending := children.pending
      stability := children.stability
      retains := children.retains
      auditCuts := children.auditCuts
      postAdmissible := children.postAdmissible
      prevailingBounded := children.prevailingBounded
      prevailingIdempotent := children.prevailingIdempotent
      frame := finalFrame
      retired := RetiredFrontierFresh.cons productFresh children.retired
      contextsRetired := children.contextsRetired
      pendingBelow := children.pendingBelow
      pendingCapFree := children.pendingCapFree
      suffix := children.suffix
      prevailing_eq := children.prevailing_eq
      frontierRetains := fun algorithm selected member =>
        List.mem_cons_of_mem _ (children.frontierRetains algorithm selected member)
      targetMember := List.mem_cons_self }
    ⟩

theorem extendSchemeOpening_cap_eq_of_capArity_zero
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening)
    (empty : scheme.capArity = 0) :
    (extendSchemeOpening base supply scheme opening).cap = base.cap := by
  funext varId
  simp [extendSchemeOpening, empty]

theorem AdmissiblePost.extendSchemeOpening_of_capArity_zero
    {base : Subst} {supply : InferenceBase.FreshSupply} {scheme : Scheme}
    (opening : (scheme.applyMeta base).ValueOpening)
    (admissible : AdmissiblePost [] base)
    (empty : scheme.capArity = 0) :
    AdmissiblePost [] (extendSchemeOpening base supply scheme opening) := by
  refine ⟨?_⟩
  rw [extendSchemeOpening_cap_eq_of_capArity_zero base supply scheme opening
    empty]
  exact admissible.cap

/-- Variable base case of the final mutual completeness induction. -/
theorem Typing.w_complete_var
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {name : String}
    {selectedScheme : SScheme} {selectedTarget : STy}
    {pending : List PendingLetCut}
    (stableFrame : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (active : (rawContext, selectedContext) ∈ frames)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget)
    {algorithmContext : SCtx} {contextResidual : SSubst}
    (normalizedContext : NormalizedDMContextView contextResidual
      algorithmContext selectedContext (rawContext.applySubst prevailing))
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    WCompleteResult signature supply prevailing rawContext (.var name)
      selectedTarget frames frontier pending := by
  let frame := stableFrame.stable.frame
  let activeFrame := frame.project active
  obtain ⟨scheme, lookup, schemeCapArity, realizes⟩ :=
    activeFrame.contexts found
  have algorithmLookup : ∃ algorithmScheme,
      algorithmContext.find? name = some algorithmScheme ∧
        scheme = algorithmScheme.emb := by
    rw [normalizedContext.normalized_eq] at lookup
    rw [SCtx.find?_emb_eq] at lookup
    cases foundAlgorithm : algorithmContext.find? name with
    | none => simp [foundAlgorithm] at lookup
    | some algorithmScheme =>
        exact ⟨algorithmScheme, rfl,
          (Option.some.inj (by simpa [foundAlgorithm] using lookup)).symm⟩
  obtain ⟨algorithmScheme, algorithmFound, schemeEq⟩ := algorithmLookup
  have selectedUse := realizes instantiation
  let opening := Classical.choose selectedUse
  let post' := extendSchemeOpening post supply scheme opening
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
  have rawRetired : ∀ cut ∈ pending,
      cut.AvoidsTy signature prevailing (prevailing.apply rawTarget) := by
    have normalizedLookup :
        (rawContext.applySubst prevailing).find? name =
          some algorithmScheme.emb := by
      rw [normalizedContext.normalized_eq]
      exact SCtx.find?_emb algorithmFound
    have canonicalFresh :=
      algorithmScheme.canonicalTarget_avoids_of_lookup normalizedLookup
        stableFrame.pendingBelow
        (fun cut member => stableFrame.contextsRetired cut member
          (rawContext, selectedContext) active)
    intro cut cutMember
    rw [rawFixed]
    change cut.AvoidsTy signature prevailing
      (InferenceBase.instantiateScheme supply scheme).value
    rw [schemeEq, algorithmScheme.canonicalTarget_emb]
    exact canonicalFresh cut cutMember
  have targetEquation : post'.apply (prevailing.apply rawTarget) =
      selectedTarget.emb := by
    rw [rawFixed]
    exact canonicalSchemeOpening_principal_relative post supply scheme
      schemeBounded selectedUse
  have oldFrame : WProtectedFrameAt supply post' prevailing frames frontier :=
    frame.extendSchemeOpening opening
  have supplyExtends : SupplyExtends supply successor :=
    SupplyExtends.instantiateScheme supply scheme
  have rawBounded : rawTarget.BoundedBy successor :=
    Scheme.freshInstantiate_value_boundedBy schemeBounded
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
  have postAdmissible' : AdmissiblePost [] post' := by
    exact AdmissiblePost.extendSchemeOpening_of_capArity_zero opening
      postAdmissible
      schemeCapArity
  have ledgerEq : DDLedger.markSchemeInstance [] supply scheme = [] :=
    DDLedger.markSchemeInstance_eq_self_of_capArity_zero
      [] supply scheme schemeCapArity
  let originMarked := DemandSynthOrigin.var (signature := signature)
    (q := supply) (S := prevailing) (context := rawContext)
    (ledger := []) lookup
  let OriginAudit := fun (ledger : CapabilityOriginLedger) =>
    ∃ origin : DemandSynthOrigin signature derived [] ledger,
      ∀ terminal,
        Nonempty (DemandSynthTerminalAudit terminal signature origin)
  let pkgMarked : OriginAudit
      (DDLedger.markSchemeInstance [] supply scheme) :=
    ⟨originMarked, fun _ =>
      ⟨DemandSynthTerminalAudit.var (lookup := lookup)⟩⟩
  let pkg : OriginAudit [] := ledgerEq ▸ pkgMarked
  obtain ⟨origin, audit⟩ := pkg
  let auditPlan : WSynthAuditPlan signature (origin := origin) :=
    WSynthAuditPlan.noCuts audit
  exact ⟨
    { successor := successor
      prevailing' := prevailing
      rawTarget := rawTarget
      post := post'
      frontier := (prevailing.apply rawTarget, selectedTarget) :: frontier
      derived := derived
      origin := origin
      auditPlan := auditPlan
      pending := pending
      stability := stableFrame.stable.lets
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
        · exact stableFrame.retired cut cutMember pair oldMember
      contextsRetired := stableFrame.contextsRetired
      pendingBelow := PendingLetsBelow.mono stableFrame.pendingBelow
        supplyExtends
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (by simpa only [Subst.apply_id] using member)
      targetMember := List.mem_cons_self }
    ⟩

/-- Literal base case of the final mutual completeness induction. -/
theorem Typing.w_complete_lit
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {value : Int}
    {pending : List PendingLetCut}
    (stableFrame : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    WCompleteResult signature supply prevailing rawContext (.lit value)
      .int frames frontier pending := by
  let frame := stableFrame.stable.frame
  let derived : DemandSynth signature supply prevailing rawContext
      (.lit value) .int supply prevailing := DemandSynth.lit
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.lit
  have resultFrame : WProtectedFrameAt supply post prevailing frames
      ((prevailing.apply .int, STy.int) :: frontier) := by
    refine
      { contexts := frame.contexts
        types := WTypeFrame.cons (by rfl) frame.types
        contextsBounded := frame.contextsBounded
        frontierBounded := ?_ }
    intro pair member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact Ty.BoundedBy.int
    · exact frame.frontierBounded pair oldMember
  exact ⟨
    { successor := supply
      prevailing' := prevailing
      rawTarget := .int
      post := post
      frontier := (prevailing.apply .int, STy.int) :: frontier
      derived := derived
      origin := origin
      auditPlan := WSynthAuditPlan.lit
      pending := pending
      stability := stableFrame.stable.lets
      retains := fun _ member => member
      auditCuts := by simp [WSynthAuditPlan.lit]
      postAdmissible := postAdmissible
      prevailingBounded := prevailingBounded
      prevailingIdempotent := prevailingIdempotent
      frame := resultFrame
      retired := RetiredFrontierFresh.cons
        (fun cut cutMember => PendingLetCut.AvoidsTy.int signature prevailing cut)
        stableFrame.retired
      contextsRetired := stableFrame.contextsRetired
      pendingBelow := stableFrame.pendingBelow
      pendingCapFree := pendingCapFree
      suffix := Subst.id
      prevailing_eq := (Subst.seq_id_left prevailing).symm
      frontierRetains := by
        intro algorithm selected member
        exact List.mem_cons_of_mem _
          (by simpa only [Subst.apply_id] using member)
      targetMember := List.mem_cons_self }
    ⟩

/-! ## Structural composition lemmas -/

/-- Recover the residual equation of the newest monomorphic binder from the
context component of a protected W frame. -/
theorem WContextRel.consMono_head_equation
    {post prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx} {name : String} {raw : Ty} {selected : STy}
    (related : WContextRel post
      (Context.applySubst prevailing
        ((name, Scheme.mono raw) :: rawContext))
      ((name, SScheme.mono selected) :: selectedContext)) :
    post.apply (prevailing.apply raw) = selected.emb := by
  have selectedFound :
      SCtx.find? ((name, SScheme.mono selected) :: selectedContext) name =
        some (SScheme.mono selected) := by
    simp [SCtx.find?]
  obtain ⟨general, generalFound, _capArity, realizes⟩ :=
    related selectedFound
  have expectedFound :
      (Context.applySubst prevailing
        ((name, Scheme.mono raw) :: rawContext)).find? name =
        some (Scheme.mono (prevailing.apply raw)) := by
    simp [Context.applySubst, Context.find?]
  have generalEq : general = Scheme.mono (prevailing.apply raw) :=
    Option.some.inj (generalFound.symm.trans expectedFound)
  subst general
  have selectedInst : (SScheme.mono selected).Inst selected :=
    ⟨SSubst.id, SSubst.id_supportWithin [], STy.applySubst_id selected⟩
  have use := realizes selectedInst
  rw [Scheme.applyMeta_mono] at use
  exact (Scheme.ValueFlowInst.mono_eq use).symm

/-- Package a recursively complete lambda body as a complete lambda result.
The body context itself recovers the final domain equation, so no positional
assumption about the child's evolving frontier is needed. -/
theorem Typing.w_complete_lam_of_body
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {name : String} {body : Expr}
    {domain codomain : STy}
    (_prepared : WRetiredStableFrameAt signature
      { supply with nextTy := supply.nextTy + 1 }
      post prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      frontier inputPending)
    (domainMember : (prevailing.apply (.var supply.nextTy), domain) ∈
      frontier)
    (bodyResult : WCompleteResult signature
      { supply with nextTy := supply.nextTy + 1 } prevailing
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
      body codomain
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      frontier inputPending) :
    WCompleteResult signature supply prevailing rawContext (.lam name body)
      (.fn domain codomain) frames frontier inputPending := by
  rcases bodyResult with ⟨result⟩
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
  exact ⟨
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
          (result.frontierRetains algorithm selected member)
      targetMember := List.mem_cons_self }
    ⟩

end DM
end TypePM
