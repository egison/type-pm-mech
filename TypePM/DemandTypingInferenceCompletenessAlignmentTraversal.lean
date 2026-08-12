import TypePM.DemandTypingInferenceCompletenessTraversal
import TypePM.DemandTypingInferenceCompletenessOneWayTransport

/-!
# Alignment traversal completeness

This module connects the solver-independent DD alignment relations to the
executable alignment traversals.  It is kept separate from the main mutual
expression traversal so branch-local solver transport can stabilize without
expanding that recursion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessAlignmentTraversal

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessOneWayTransport
open DemandTypingInferenceCompletenessSolver
open DemandTypingInferenceCompletenessLedgerBisimulation

private def capOnly (substitution : CapSubst) : Subst :=
  ⟨substitution, TySubst.id⟩

/-- Capability components exposed from two bisimilar resolved annotated
types.  Unlike two unrelated existential renamings, the shared residuals
preserve repeated capability variables across the cut. -/
structure ResolvedCapComponents
    (forward reverse : Subst)
    (declarativeLeft executableLeft declarativeRight executableRight : Cap) :
    Prop where
  leftForward : declarativeLeft = executableLeft.apply forward.cap
  leftReverse : executableLeft = declarativeLeft.apply reverse.cap
  rightForward : declarativeRight = executableRight.apply forward.cap
  rightReverse : executableRight = declarativeRight.apply reverse.cap

/-- A capability-only exact cut mutually transports through the residuals
already relating the DD and executable states. -/
noncomputable def capabilityDeltaBisimulation
    {declarativeLedger executableLedger : CapabilityOriginLedger}
    {forward reverse : Subst}
    {declarativeLeft executableLeft declarativeRight executableRight : Cap}
    {declarativeDelta : CapSubst}
    (ledgers :
      DemandTypingInferenceCompletenessLedgerBisimulation.LedgerBisimulation
        declarativeLedger executableLedger forward reverse)
    (resolved : ResolvedCapComponents forward reverse declarativeLeft
      executableLeft declarativeRight executableRight)
    (dd : OriginSafeExactCapMGU declarativeLedger declarativeLeft
      declarativeRight declarativeDelta)
    (result : PairedUnification.OrientedCapResult executableLedger
      executableLeft executableRight) :
    OneWayDeltaBisimulation declarativeLedger executableLedger forward reverse
      (capOnly declarativeDelta) (capOnly result.subst) := by
  let combined := Subst.seq (capOnly declarativeDelta) forward
  have combinedBetween : AdmissiblePostBetween executableLedger
      declarativeLedger combined :=
    (AdmissiblePostBetween.ofAdmissible { cap := dd.admissible }).seq
      ledgers.forwardBetween
  have combinedSound : executableLeft.apply combined.cap =
      executableRight.apply combined.cap := by
    calc
      executableLeft.apply combined.cap =
          (executableLeft.apply forward.cap).apply declarativeDelta := by
        exact Cap.apply_comp declarativeDelta forward.cap executableLeft
      _ = declarativeLeft.apply declarativeDelta := by
        rw [← resolved.leftForward]
      _ = declarativeRight.apply declarativeDelta := dd.exact.1.1
      _ = (executableRight.apply forward.cap).apply declarativeDelta := by
        rw [resolved.rightForward]
      _ = executableRight.apply combined.cap := by
        exact (Cap.apply_comp declarativeDelta forward.cap executableRight).symm
  have capForwardAbsorbs : combined.cap =
      CapSubst.comp combined.cap result.subst :=
    result.exactCapMGU.absorbs combinedSound
  have forwardAbsorbs : combined =
      Subst.seq combined (capOnly result.subst) := by
    apply PhasedPost.subst_ext
    · exact capForwardAbsorbs
    · funext varId
      change combined.target varId = combined.apply (TySubst.id varId)
      rfl
  let reverseCompetitor := Subst.seq (capOnly result.subst) reverse
  have reverseBetween : AdmissiblePostBetween declarativeLedger
      executableLedger reverseCompetitor :=
    (AdmissiblePostBetween.ofAdmissible { cap := result.admissible }).seq
      ledgers.reverseBetween
  have reverseSound : declarativeLeft.apply reverseCompetitor.cap =
      declarativeRight.apply reverseCompetitor.cap := by
    calc
      declarativeLeft.apply reverseCompetitor.cap =
          (declarativeLeft.apply reverse.cap).apply result.subst := by
        exact Cap.apply_comp result.subst reverse.cap declarativeLeft
      _ = executableLeft.apply result.subst := by
        exact congrArg (Cap.apply result.subst) resolved.leftReverse |>.symm
      _ = executableRight.apply result.subst := result.sound
      _ = (declarativeRight.apply reverse.cap).apply result.subst := by
        exact congrArg (Cap.apply result.subst) resolved.rightReverse
      _ = declarativeRight.apply reverseCompetitor.cap := by
        exact (Cap.apply_comp result.subst reverse.cap declarativeRight).symm
  have capReverseAbsorbs : reverseCompetitor.cap =
      CapSubst.comp reverseCompetitor.cap declarativeDelta :=
    dd.exact.absorbs reverseSound
  have reverseAbsorbs : reverseCompetitor =
      Subst.seq reverseCompetitor (capOnly declarativeDelta) := by
    apply PhasedPost.subst_ext
    · exact capReverseAbsorbs
    · funext varId
      change reverseCompetitor.target varId =
        reverseCompetitor.apply (TySubst.id varId)
      rfl
  exact
    { forwardAfter := combined
      forwardEquation := forwardAbsorbs
      forwardAdmissible := combinedBetween
      reverseAfter := reverseCompetitor
      reverseEquation := reverseAbsorbs
      reverseAdmissible := reverseBetween }

/-- Solved-form preservation for a capability-only exact cut.  This is the
local two-sort form needed between the capability and target stages of an
annotated alignment. -/
private theorem capOnly_seq_idempotent_of_fixed
    {S : Subst} {left right : Cap} {delta : CapSubst}
    (idem : S.Idempotent) (exact : ExactCapMGU left right delta)
    (leftFixed : left.apply S.cap = left)
    (rightFixed : right.apply S.cap = right) :
    (Subst.seq (capOnly delta) S).Idempotent := by
  apply Subst.seq_idempotent
  · exact Subst.idempotent_of_targetId exact.2.2.2
  · intro target
    apply Subst.apply_eq_self_of_fixed
    · intro varId mem
      have mem' : varId ∈ (S.apply target).ftv := by
        simpa [capOnly, Subst.apply, Ty.applyTarget_id,
          Unification.Ty.ftv_applyCapability] using mem
      exact idem.image_target_fixed target varId mem'
    · intro varId mem
      have mem' : varId ∈ ((S.apply target).applyCapability delta).fcv := by
        simpa [capOnly, Subst.apply, Ty.applyTarget_id] using mem
      rw [Unification.Ty.fcv_applyCapability] at mem'
      obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp mem'
      by_cases inConstraint : source ∈ left.fcv ++ right.fcv
      · have imageIn : varId ∈ left.fcv ++ right.fcv :=
          exact.2.2.1 source inConstraint varId imageMem
        rcases List.mem_append.mp imageIn with inLeft | inRight
        · exact Cap.fixed_of_apply_self left leftFixed varId inLeft
        · exact Cap.fixed_of_apply_self right rightFixed varId inRight
      · rw [exact.2.1 source inConstraint] at imageMem
        have equality : varId = source := by
          simpa [Cap.fcv] using imageMem
        subst varId
        exact idem.image_cap_fixed target source sourceMem

/-- Change only the executable operation named by a state-run package. -/
def StateRunCompletion.congrOperation
    {q q' : InferenceBase.FreshSupply} {S declarative : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {first second : Option InferState}
    (run : StateRunCompletion before first q' declarative ledger)
    (operationEq : second = first) :
    StateRunCompletion before second q' declarative ledger :=
  { run with success := operationEq.trans run.success }

/-- Chronologically compose two state-only traversal packages. -/
def StateRunCompletion.seq
    {q q' q'' : InferenceBase.FreshSupply}
    {S S' S'' : Subst}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {firstOperation : Option InferState}
    (first : StateRunCompletion before firstOperation q' S' ledger₁)
    {secondOperation : InferState → Option InferState}
    (second : StateRunCompletion first.completion
      (secondOperation first.result) q'' S'' ledger₂) :
    StateRunCompletion before
      (do
        let middle ← firstOperation
        secondOperation middle)
      q'' S'' ledger₂ := by
  refine
    { result := second.result
      success := ?_
      supply_eq := second.supply_eq
      transition := first.transition.seq second.transition
      declarative_bounded := second.declarative_bounded
      executable_bounded := second.executable_bounded
      forward_bounded := second.forward_bounded
      reverse_bounded := second.reverse_bounded
      ledger_below := second.ledger_below
      executable_ledger_below := second.executable_ledger_below
      protected_origins := second.protected_origins
      protected_below := second.protected_below
      allocated_recorded := second.allocated_recorded }
  calc
    (do
      let middle ← firstOperation
      secondOperation middle) =
        (do
          let middle ← some first.result
          secondOperation middle) :=
      congrArg (fun operation => operation.bind secondOperation) first.success
    _ = secondOperation first.result := rfl
    _ = some second.result := second.success

/-- Complete one already-resolved capability equality.  The DD capability
MGU is transported through the incoming state bisimulation to obtain an
executable solver competitor; neither solver success nor an orientation is a
caller premise. -/
noncomputable def runResolvedCapEq_complete
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft executableLeft declarativeRight executableRight : Cap}
    {declarativeDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolved : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeLeft executableLeft
      declarativeRight executableRight)
    (dd : OriginSafeExactCapMGU ledger declarativeLeft declarativeRight
      declarativeDelta)
    (declarativeLeftFixed : declarativeLeft.apply S.cap = declarativeLeft)
    (declarativeRightFixed : declarativeRight.apply S.cap = declarativeRight)
    (executableLeftFixed : executableLeft.apply initial.prevailing.cap =
      executableLeft)
    (executableRightFixed : executableRight.apply initial.prevailing.cap =
      executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.capEq executableLeft executableRight)) q
      (Subst.seq (capOnly declarativeDelta) S) ledger := by
  let combined := Subst.seq (capOnly declarativeDelta)
    relation.prevailing.forward
  let transported := Subst.seq relation.prevailing.reverse combined
  have transportedAdmissible : AdmissibleCapPost initial.capabilityOrigins
      transported.cap := by
    exact (relation.prevailing.ledgerBisimulation.transportAdmissible
      { cap := dd.admissible }).cap
  have combinedSound : executableLeft.apply combined.cap =
      executableRight.apply combined.cap := by
    calc
      executableLeft.apply combined.cap =
          (executableLeft.apply relation.prevailing.forward.cap).apply
            declarativeDelta := by
        exact Cap.apply_comp declarativeDelta relation.prevailing.forward.cap
          executableLeft
      _ = declarativeLeft.apply declarativeDelta := by
        rw [← resolved.leftForward]
      _ = declarativeRight.apply declarativeDelta := dd.exact.1.1
      _ = (executableRight.apply relation.prevailing.forward.cap).apply
            declarativeDelta := by
        rw [resolved.rightForward]
      _ = executableRight.apply combined.cap := by
        exact (Cap.apply_comp declarativeDelta
          relation.prevailing.forward.cap executableRight).symm
  have transportedSound : executableLeft.apply transported.cap =
      executableRight.apply transported.cap := by
    calc
      executableLeft.apply transported.cap =
          (executableLeft.apply combined.cap).apply
            relation.prevailing.reverse.cap := by
        exact Cap.apply_comp relation.prevailing.reverse.cap combined.cap
          executableLeft
      _ = (executableRight.apply combined.cap).apply
            relation.prevailing.reverse.cap :=
        congrArg (Cap.apply relation.prevailing.reverse.cap) combinedSound
      _ = executableRight.apply transported.cap := by
        exact (Cap.apply_comp relation.prevailing.reverse.cap combined.cap
          executableRight).symm
  let solverExists := solveCapEqWithLedger_complete_of_admissible
    transportedAdmissible transportedSound initial.trace.solves.length origin
  let solver := Classical.choose solverExists
  have stepExists := Classical.choose_spec solverExists
  let step := Classical.choose stepExists
  have stepFacts := Classical.choose_spec stepExists
  have solverSuccess := stepFacts.1
  have stepDelta := stepFacts.2
  let deltaRelation := capabilityDeltaBisimulation
    relation.prevailing.ledgerBisimulation resolved dd solver
  have declarativeAfterIdempotent :
      (Subst.seq (capOnly declarativeDelta) S).Idempotent :=
    capOnly_seq_idempotent_of_fixed relation.prevailing.declarativeIdempotent
      dd.exact declarativeLeftFixed declarativeRightFixed
  have executableAfterIdempotent :
      (Subst.seq (capOnly solver.subst) initial.prevailing).Idempotent :=
    capOnly_seq_idempotent_of_fixed relation.prevailing.executableIdempotent
      solver.exactCapMGU executableLeftFixed executableRightFixed
  let transition :=
    DemandTypingInferenceCompletenessOneWayTransport.StateBisimulation.oneWayCut_recordSolve
      relation.prevailing deltaRelation declarativeAfterIdempotent
      executableAfterIdempotent stepDelta
  have declarativeDeltaBounded : (capOnly declarativeDelta).BoundedBy q :=
    dd.exact.boundedBy_pair declarativeLeftBounded declarativeRightBounded
  have executableDeltaBounded : (capOnly solver.subst).BoundedBy q :=
    solver.exactCapMGU.boundedBy_pair executableLeftBounded
      executableRightBounded
  refine
    { result := initial.recordSolve step
      success := ?_
      supply_eq := relation.supply_eq
      transition := transition
      declarative_bounded := declarativeDeltaBounded.seq
        relation.declarative_bounded
      executable_bounded := ?_
      forward_bounded := ?_
      reverse_bounded := ?_
      ledger_below := relation.ledger_below
      executable_ledger_below := relation.executable_ledger_below
      protected_origins := relation.protected_origins.recordSolve step
      protected_below := relation.protected_below.recordSolve step
      allocated_recorded := relation.allocated_recorded.recordSolve step }
  · unfold runResolvedConstraint
    change (do
      let emitted ← solveCapEqWithLedger initial.capabilityOrigins
        initial.trace.solves.length origin executableLeft executableRight
      pure (initial.recordSolve emitted)) = some (initial.recordSolve step)
    rw [solverSuccess]
    rfl
  · rw [InferState.prevailing_recordSolve, stepDelta]
    exact executableDeltaBounded.seq relation.executable_bounded
  · change combined.BoundedBy q
    exact declarativeDeltaBounded.seq relation.forward_bounded
  · change (Subst.seq (capOnly solver.subst)
      relation.prevailing.reverse).BoundedBy q
    exact executableDeltaBounded.seq relation.reverse_bounded

/-- Complete the common annotated-type protocol: capability equality first,
then equality of the capability-adjusted target components. -/
noncomputable def runResolvedAnnotatedPair_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeftCap executableLeftCap declarativeRightCap
      executableRightCap : Cap}
    {declarativeLeftTarget executableLeftTarget declarativeRightTarget
      executableRightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeLeftCap executableLeftCap
      declarativeRightCap executableRightCap)
    (leftTarget : TyBisimulation relation.prevailing declarativeLeftTarget
      executableLeftTarget)
    (rightTarget : TyBisimulation relation.prevailing declarativeRightTarget
      executableRightTarget)
    (capDD : OriginSafeExactCapMGU ledger declarativeLeftCap
      declarativeRightCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (declarativeLeftTarget.applyCapability capDelta)
      (declarativeRightTarget.applyCapability capDelta) targetDelta)
    (declarativeLeftCapFixed : declarativeLeftCap.apply S.cap =
      declarativeLeftCap)
    (declarativeRightCapFixed : declarativeRightCap.apply S.cap =
      declarativeRightCap)
    (executableLeftCapFixed : executableLeftCap.apply initial.prevailing.cap =
      executableLeftCap)
    (executableRightCapFixed : executableRightCap.apply
      initial.prevailing.cap = executableRightCap)
    (declarativeLeftTargetFixed : S.apply declarativeLeftTarget =
      declarativeLeftTarget)
    (declarativeRightTargetFixed : S.apply declarativeRightTarget =
      declarativeRightTarget)
    (declarativeLeftCapBounded : declarativeLeftCap.BoundedBy q)
    (declarativeRightCapBounded : declarativeRightCap.BoundedBy q)
    (executableLeftCapBounded : executableLeftCap.BoundedBy q)
    (executableRightCapBounded : executableRightCap.BoundedBy q)
    (declarativeLeftTargetBounded : declarativeLeftTarget.BoundedBy q)
    (declarativeRightTargetBounded : declarativeRightTarget.BoundedBy q)
    (executableLeftTargetBounded : executableLeftTarget.BoundedBy q)
    (executableRightTargetBounded : executableRightTarget.BoundedBy q) :
    StateRunCompletion relation
      (do
        let middle ← runResolvedConstraint initial origin
          (.capEq executableLeftCap executableRightCap)
        runResolvedConstraint middle origin
          (.targetEq (middle.prevailing.apply executableLeftTarget)
            (middle.prevailing.apply executableRightTarget))) q
      (Subst.seq targetDelta
        (Subst.seq (capOnly capDelta) S)) ledger := by
  let capRun := runResolvedCapEq_complete (origin := origin) relation
    resolvedCaps capDD declarativeLeftCapFixed declarativeRightCapFixed
    executableLeftCapFixed executableRightCapFixed declarativeLeftCapBounded
    declarativeRightCapBounded executableLeftCapBounded
    executableRightCapBounded
  have adjustedTargetDD : OriginSafeExactPairedMGU ledger
      ((Subst.seq (capOnly capDelta) S).apply declarativeLeftTarget)
      ((Subst.seq (capOnly capDelta) S).apply declarativeRightTarget)
      targetDelta := by
    have leftEq :
        (Subst.seq (capOnly capDelta) S).apply declarativeLeftTarget =
          declarativeLeftTarget.applyCapability capDelta := by
      rw [Subst.seq_apply, declarativeLeftTargetFixed]
      simp [capOnly, Subst.apply, Ty.applyTarget_id]
    have rightEq :
        (Subst.seq (capOnly capDelta) S).apply declarativeRightTarget =
          declarativeRightTarget.applyCapability capDelta := by
      rw [Subst.seq_apply, declarativeRightTargetFixed]
      simp [capOnly, Subst.apply, Ty.applyTarget_id]
    rw [leftEq, rightEq]
    exact targetDD
  have declarativeLeftAdjustedBounded :
      (declarativeLeftTarget.applyCapability capDelta).BoundedBy q := by
    have deltaBounded := capDD.exact.boundedBy_pair
      declarativeLeftCapBounded declarativeRightCapBounded
    simpa [capOnly, Subst.apply, Ty.applyTarget_id] using
      deltaBounded.apply declarativeLeftTargetBounded
  have declarativeRightAdjustedBounded :
      (declarativeRightTarget.applyCapability capDelta).BoundedBy q := by
    have deltaBounded := capDD.exact.boundedBy_pair
      declarativeLeftCapBounded declarativeRightCapBounded
    simpa [capOnly, Subst.apply, Ty.applyTarget_id] using
      deltaBounded.apply declarativeRightTargetBounded
  have declarativeLeftAfterBounded :
      declarativeLeftTarget.BoundedBy q := declarativeLeftTargetBounded
  have declarativeRightAfterBounded :
      declarativeRightTarget.BoundedBy q := declarativeRightTargetBounded
  let targetRun := runResolvedTargetEq_complete (origin := origin)
    capRun.completion
    (capRun.transition.transportTy leftTarget)
    (capRun.transition.transportTy rightTarget)
    declarativeLeftAfterBounded declarativeRightAfterBounded
    executableLeftTargetBounded executableRightTargetBounded adjustedTargetDD
  exact StateRunCompletion.seq capRun targetRun

/-- The matcher/matcher branch of `alignTypesCore` on its already-resolved
annotated operands. -/
noncomputable def alignTypesCore_matcherPair_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeftCap executableLeftCap declarativeRightCap
      executableRightCap : Cap}
    {declarativeLeftTarget executableLeftTarget declarativeRightTarget
      executableRightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeLeftCap executableLeftCap
      declarativeRightCap executableRightCap)
    (leftTarget : TyBisimulation relation.prevailing declarativeLeftTarget
      executableLeftTarget)
    (rightTarget : TyBisimulation relation.prevailing declarativeRightTarget
      executableRightTarget)
    (capDD : OriginSafeExactCapMGU ledger declarativeLeftCap
      declarativeRightCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (declarativeLeftTarget.applyCapability capDelta)
      (declarativeRightTarget.applyCapability capDelta) targetDelta)
    (declarativeLeftCapFixed : declarativeLeftCap.apply S.cap =
      declarativeLeftCap)
    (declarativeRightCapFixed : declarativeRightCap.apply S.cap =
      declarativeRightCap)
    (executableLeftCapFixed : executableLeftCap.apply initial.prevailing.cap =
      executableLeftCap)
    (executableRightCapFixed : executableRightCap.apply
      initial.prevailing.cap = executableRightCap)
    (declarativeLeftTargetFixed : S.apply declarativeLeftTarget =
      declarativeLeftTarget)
    (declarativeRightTargetFixed : S.apply declarativeRightTarget =
      declarativeRightTarget)
    (executableLeftTargetFixed : initial.prevailing.apply
      executableLeftTarget = executableLeftTarget)
    (executableRightTargetFixed : initial.prevailing.apply
      executableRightTarget = executableRightTarget)
    (declarativeLeftCapBounded : declarativeLeftCap.BoundedBy q)
    (declarativeRightCapBounded : declarativeRightCap.BoundedBy q)
    (executableLeftCapBounded : executableLeftCap.BoundedBy q)
    (executableRightCapBounded : executableRightCap.BoundedBy q)
    (declarativeLeftTargetBounded : declarativeLeftTarget.BoundedBy q)
    (declarativeRightTargetBounded : declarativeRightTarget.BoundedBy q)
    (executableLeftTargetBounded : executableLeftTarget.BoundedBy q)
    (executableRightTargetBounded : executableRightTarget.BoundedBy q) :
    StateRunCompletion relation
      (alignTypesCore initial origin
        (.matcher executableLeftCap executableLeftTarget)
        (.matcher executableRightCap executableRightTarget)) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  let run := runResolvedAnnotatedPair_complete (origin := origin) relation
    resolvedCaps leftTarget rightTarget capDD targetDD
    declarativeLeftCapFixed declarativeRightCapFixed executableLeftCapFixed
    executableRightCapFixed declarativeLeftTargetFixed
    declarativeRightTargetFixed declarativeLeftCapBounded
    declarativeRightCapBounded executableLeftCapBounded
    executableRightCapBounded declarativeLeftTargetBounded
    declarativeRightTargetBounded executableLeftTargetBounded
    executableRightTargetBounded
  apply StateRunCompletion.congrOperation run
  unfold alignTypesCore
  simp only [Subst.apply_matcher, executableLeftCapFixed,
    executableRightCapFixed, executableLeftTargetFixed,
    executableRightTargetFixed]

/-- Slot/slot checking uses the same two-stage protocol as ordinary
slot-pair alignment, but is selected by `alignAtSlot`. -/
noncomputable def alignAtSlot_slotToSlot_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeftCap executableLeftCap declarativeRightCap
      executableRightCap : Cap}
    {declarativeLeftTarget executableLeftTarget declarativeRightTarget
      executableRightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeLeftCap executableLeftCap
      declarativeRightCap executableRightCap)
    (leftTarget : TyBisimulation relation.prevailing declarativeLeftTarget
      executableLeftTarget)
    (rightTarget : TyBisimulation relation.prevailing declarativeRightTarget
      executableRightTarget)
    (capDD : OriginSafeExactCapMGU ledger declarativeLeftCap
      declarativeRightCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (declarativeLeftTarget.applyCapability capDelta)
      (declarativeRightTarget.applyCapability capDelta) targetDelta)
    (declarativeLeftCapFixed : declarativeLeftCap.apply S.cap =
      declarativeLeftCap)
    (declarativeRightCapFixed : declarativeRightCap.apply S.cap =
      declarativeRightCap)
    (executableLeftCapFixed : executableLeftCap.apply initial.prevailing.cap =
      executableLeftCap)
    (executableRightCapFixed : executableRightCap.apply
      initial.prevailing.cap = executableRightCap)
    (declarativeLeftTargetFixed : S.apply declarativeLeftTarget =
      declarativeLeftTarget)
    (declarativeRightTargetFixed : S.apply declarativeRightTarget =
      declarativeRightTarget)
    (executableLeftTargetFixed : initial.prevailing.apply
      executableLeftTarget = executableLeftTarget)
    (executableRightTargetFixed : initial.prevailing.apply
      executableRightTarget = executableRightTarget)
    (declarativeLeftCapBounded : declarativeLeftCap.BoundedBy q)
    (declarativeRightCapBounded : declarativeRightCap.BoundedBy q)
    (executableLeftCapBounded : executableLeftCap.BoundedBy q)
    (executableRightCapBounded : executableRightCap.BoundedBy q)
    (declarativeLeftTargetBounded : declarativeLeftTarget.BoundedBy q)
    (declarativeRightTargetBounded : declarativeRightTarget.BoundedBy q)
    (executableLeftTargetBounded : executableLeftTarget.BoundedBy q)
    (executableRightTargetBounded : executableRightTarget.BoundedBy q) :
    StateRunCompletion relation
      (alignAtSlot initial origin
        (.slot executableLeftCap executableLeftTarget)
        (.slot executableRightCap executableRightTarget)) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  let run := runResolvedAnnotatedPair_complete (origin := origin) relation
    resolvedCaps leftTarget rightTarget capDD targetDD
    declarativeLeftCapFixed declarativeRightCapFixed executableLeftCapFixed
    executableRightCapFixed declarativeLeftTargetFixed
    declarativeRightTargetFixed declarativeLeftCapBounded
    declarativeRightCapBounded executableLeftCapBounded
    executableRightCapBounded declarativeLeftTargetBounded
    declarativeRightTargetBounded executableLeftTargetBounded
    executableRightTargetBounded
  apply StateRunCompletion.congrOperation run
  unfold alignAtSlot
  simp only [Subst.apply_slot, executableLeftCapFixed,
    executableRightCapFixed, executableLeftTargetFixed,
    executableRightTargetFixed]

/-- The slot/slot branch of `alignTypesCore` is extensionally the same
two-stage run as slot-to-slot checking. -/
noncomputable def alignTypesCore_slotPair_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {executableLeftCap executableRightCap : Cap}
    {executableLeftTarget executableRightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (run : StateRunCompletion relation
      (alignAtSlot initial origin
        (.slot executableLeftCap executableLeftTarget)
        (.slot executableRightCap executableRightTarget)) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger) :
    StateRunCompletion relation
      (alignTypesCore initial origin
        (.slot executableLeftCap executableLeftTarget)
        (.slot executableRightCap executableRightTarget)) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  apply StateRunCompletion.congrOperation run
  unfold alignTypesCore alignAtSlot
  rfl

/-- Add the public `typeAlignment` event around a completed core run. -/
def StateRunCompletion.finishAlignTypes
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {origin : ConstraintOrigin} {left right : Ty}
    (core : StateRunCompletion before
      (alignTypesCore initial origin left right) q S' ledger) :
    StateRunCompletion before (alignTypes initial origin left right) q S'
      ledger := by
  let event := TraceEvent.typeAlignment initial.trace.solves.length
    core.result.trace.solves.length left right
    (initial.prevailing.apply left) (initial.prevailing.apply right)
  let finishExtension := core.transition.after.recordEventExtension event
  refine
    { result := core.result.recordEvent event
      success := ?_
      supply_eq := core.supply_eq
      transition := core.transition.seq finishExtension
      declarative_bounded := core.declarative_bounded
      executable_bounded := core.executable_bounded
      forward_bounded := core.forward_bounded
      reverse_bounded := core.reverse_bounded
      ledger_below := core.ledger_below
      executable_ledger_below := core.executable_ledger_below
      protected_origins := core.protected_origins.recordEvent event
      protected_below := core.protected_below.recordEvent_of_allocated event
      allocated_recorded := core.allocated_recorded.recordEvent event (by
        simp [event, TraceEvent.allocatedCapVars]) }
  unfold alignTypes
  let finishState := fun aligned : InferState =>
    some (aligned.recordEvent (.typeAlignment initial.trace.solves.length
      aligned.trace.solves.length left right
      (initial.prevailing.apply left) (initial.prevailing.apply right)))
  change (alignTypesCore initial origin left right).bind finishState =
    some (core.result.recordEvent event)
  calc
    (alignTypesCore initial origin left right).bind finishState =
        (some core.result).bind finishState :=
      congrArg (fun operation => operation.bind finishState) core.success
    _ = some (core.result.recordEvent event) := rfl

/-- Once the initial matcher heads are exposed, `alignTypesCore` is exactly
the common capability-then-target protocol on their components. -/
theorem alignTypesCore_matcherViews
    {state : InferState} {origin : ConstraintOrigin} {left right : Ty}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    (leftView : state.prevailing.apply left = .matcher leftCap leftTarget)
    (rightView : state.prevailing.apply right = .matcher rightCap rightTarget)
    (leftTargetFixed : state.prevailing.apply leftTarget = leftTarget)
    (rightTargetFixed : state.prevailing.apply rightTarget = rightTarget) :
    alignTypesCore state origin left right = (do
      let middle ← runResolvedConstraint state origin (.capEq leftCap rightCap)
      runResolvedConstraint middle origin
        (.targetEq (middle.prevailing.apply leftTarget)
          (middle.prevailing.apply rightTarget))) := by
  unfold alignTypesCore
  rw [leftView, rightView]
  unfold runResolvedConstraint solveResolvedWithLedger
  cases solved : solveCapEqWithLedger state.capabilityOrigins
      state.trace.solves.length origin leftCap rightCap with
  | none => simp [solved]
  | some step =>
      have targetId :=
        (solveCapEqWithLedger_originSafeExactCapMGU solved).1
      have afterLeft :
          (step.delta.seq state.prevailing).apply left =
            .matcher (leftCap.apply step.delta.cap)
              (step.delta.apply leftTarget) := by
        rw [Subst.seq_apply, leftView]
        simp [Subst.apply, targetId, Ty.applyTarget_id]
        rfl
      have afterRight :
          (step.delta.seq state.prevailing).apply right =
            .matcher (rightCap.apply step.delta.cap)
              (step.delta.apply rightTarget) := by
        rw [Subst.seq_apply, rightView]
        simp [Subst.apply, targetId, Ty.applyTarget_id]
        rfl
      simp [solved, InferState.prevailing_recordSolve, afterLeft, afterRight,
        Subst.seq_apply, leftTargetFixed, rightTargetFixed]

/-- Slot heads obey the same two-stage core protocol. -/
theorem alignTypesCore_slotViews
    {state : InferState} {origin : ConstraintOrigin} {left right : Ty}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    (leftView : state.prevailing.apply left = .slot leftCap leftTarget)
    (rightView : state.prevailing.apply right = .slot rightCap rightTarget)
    (leftTargetFixed : state.prevailing.apply leftTarget = leftTarget)
    (rightTargetFixed : state.prevailing.apply rightTarget = rightTarget) :
    alignTypesCore state origin left right = (do
      let middle ← runResolvedConstraint state origin (.capEq leftCap rightCap)
      runResolvedConstraint middle origin
        (.targetEq (middle.prevailing.apply leftTarget)
          (middle.prevailing.apply rightTarget))) := by
  unfold alignTypesCore
  rw [leftView, rightView]
  unfold runResolvedConstraint solveResolvedWithLedger
  cases solved : solveCapEqWithLedger state.capabilityOrigins
      state.trace.solves.length origin leftCap rightCap with
  | none => simp [solved]
  | some step =>
      have targetId :=
        (solveCapEqWithLedger_originSafeExactCapMGU solved).1
      have afterLeft :
          (step.delta.seq state.prevailing).apply left =
            .slot (leftCap.apply step.delta.cap)
              (step.delta.apply leftTarget) := by
        rw [Subst.seq_apply, leftView]
        simp [Subst.apply, targetId, Ty.applyTarget_id]
        rfl
      have afterRight :
          (step.delta.seq state.prevailing).apply right =
            .slot (rightCap.apply step.delta.cap)
              (step.delta.apply rightTarget) := by
        rw [Subst.seq_apply, rightView]
        simp [Subst.apply, targetId, Ty.applyTarget_id]
        rfl
      simp [solved, InferState.prevailing_recordSolve, afterLeft, afterRight,
        Subst.seq_apply, leftTargetFixed, rightTargetFixed]

/-- Raw matcher/matcher DD alignment completes without identifying DD and
executable metavariable names. -/
noncomputable def alignTypes_matcherPair_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (leftView : S.apply declarativeLeft = .matcher leftCap leftTarget)
    (rightView : S.apply declarativeRight = .matcher rightCap rightTarget)
    (capDD : OriginSafeExactCapMGU ledger leftCap rightCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (leftTarget.applyCapability capDelta)
      (rightTarget.applyCapability capDelta) targetDelta)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q) :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  let executableLeftCap := leftCap.apply relation.prevailing.reverse.cap
  let executableLeftTarget := relation.prevailing.reverse.apply leftTarget
  let executableRightCap := rightCap.apply relation.prevailing.reverse.cap
  let executableRightTarget := relation.prevailing.reverse.apply rightTarget
  have executableLeftView : initial.prevailing.apply executableLeft =
      .matcher executableLeftCap executableLeftTarget := by
    rw [left.reverse, leftView]
    rfl
  have executableRightView : initial.prevailing.apply executableRight =
      .matcher executableRightCap executableRightTarget := by
    rw [right.reverse, rightView]
    rfl
  have leftForward := left.forward
  have rightForward := right.forward
  rw [leftView, executableLeftView] at leftForward
  rw [rightView, executableRightView] at rightForward
  have resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse leftCap executableLeftCap rightCap
      executableRightCap :=
    ⟨(Ty.matcher.inj leftForward).1, rfl,
      (Ty.matcher.inj rightForward).1, rfl⟩
  have declarativeLeftFixed :=
    relation.prevailing.declarativeIdempotent declarativeLeft
  have declarativeRightFixed :=
    relation.prevailing.declarativeIdempotent declarativeRight
  rw [leftView] at declarativeLeftFixed
  rw [rightView] at declarativeRightFixed
  have executableLeftFixed :=
    relation.prevailing.executableIdempotent executableLeft
  have executableRightFixed :=
    relation.prevailing.executableIdempotent executableRight
  rw [executableLeftView] at executableLeftFixed
  rw [executableRightView] at executableRightFixed
  have leftTargetRelated : TyBisimulation relation.prevailing leftTarget
      executableLeftTarget := by
    constructor
    · calc
        S.apply leftTarget = leftTarget :=
          (Ty.matcher.inj declarativeLeftFixed).2
        _ = relation.prevailing.forward.apply executableLeftTarget :=
          (Ty.matcher.inj leftForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableLeftTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.matcher.inj executableLeftFixed).2.symm
    · calc
        initial.prevailing.apply executableLeftTarget = executableLeftTarget :=
          (Ty.matcher.inj executableLeftFixed).2
        _ = relation.prevailing.reverse.apply leftTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply leftTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.matcher.inj declarativeLeftFixed).2.symm
  have rightTargetRelated : TyBisimulation relation.prevailing rightTarget
      executableRightTarget := by
    constructor
    · calc
        S.apply rightTarget = rightTarget :=
          (Ty.matcher.inj declarativeRightFixed).2
        _ = relation.prevailing.forward.apply executableRightTarget :=
          (Ty.matcher.inj rightForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableRightTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.matcher.inj executableRightFixed).2.symm
    · calc
        initial.prevailing.apply executableRightTarget = executableRightTarget :=
          (Ty.matcher.inj executableRightFixed).2
        _ = relation.prevailing.reverse.apply rightTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply rightTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.matcher.inj declarativeRightFixed).2.symm
  have declarativeLeftResolvedBounded :=
    relation.declarative_bounded.apply declarativeLeftBounded
  have declarativeRightResolvedBounded :=
    relation.declarative_bounded.apply declarativeRightBounded
  rw [leftView] at declarativeLeftResolvedBounded
  rw [rightView] at declarativeRightResolvedBounded
  have executableLeftResolvedBounded :=
    relation.executable_bounded.apply executableLeftBounded
  have executableRightResolvedBounded :=
    relation.executable_bounded.apply executableRightBounded
  rw [executableLeftView] at executableLeftResolvedBounded
  rw [executableRightView] at executableRightResolvedBounded
  let staged := runResolvedAnnotatedPair_complete (origin := origin) relation
    resolvedCaps leftTargetRelated rightTargetRelated capDD targetDD
    (Ty.matcher.inj declarativeLeftFixed).1
    (Ty.matcher.inj declarativeRightFixed).1
    (Ty.matcher.inj executableLeftFixed).1
    (Ty.matcher.inj executableRightFixed).1
    (Ty.matcher.inj declarativeLeftFixed).2
    (Ty.matcher.inj declarativeRightFixed).2
    declarativeLeftResolvedBounded.matcherParts.1
    declarativeRightResolvedBounded.matcherParts.1
    executableLeftResolvedBounded.matcherParts.1
    executableRightResolvedBounded.matcherParts.1
    declarativeLeftResolvedBounded.matcherParts.2
    declarativeRightResolvedBounded.matcherParts.2
    executableLeftResolvedBounded.matcherParts.2
    executableRightResolvedBounded.matcherParts.2
  have core : StateRunCompletion relation
      (alignTypesCore initial origin executableLeft executableRight) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
    apply StateRunCompletion.congrOperation staged
    exact alignTypesCore_matcherViews executableLeftView executableRightView
      (Ty.matcher.inj executableLeftFixed).2
      (Ty.matcher.inj executableRightFixed).2
  exact StateRunCompletion.finishAlignTypes core

/-- Mutual state factorization prevents an annotated homogeneous pair from
appearing only on the executable side.  Hence an ordinary DD pair selects the
ordinary executable branch as well. -/
theorem executableAlignPairClass_ordinary
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeClass :
      alignPairClass (S.apply declarativeLeft) (S.apply declarativeRight) =
        .ordinary) :
    alignPairClass (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight) = .ordinary := by
  generalize leftEq : initial.prevailing.apply executableLeft = leftResolved
  generalize rightEq : initial.prevailing.apply executableRight = rightResolved
  cases leftResolved <;> cases rightResolved <;> try rfl
  all_goals
    have leftForward := left.forward
    have rightForward := right.forward
    rw [leftEq] at leftForward
    rw [rightEq] at rightForward
    rw [leftForward, rightForward] at declarativeClass
    simp [alignPairClass] at declarativeClass

/-- Raw slot/slot DD alignment completes under the same mutual-state
invariant. -/
noncomputable def alignTypes_slotPair_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    {capDelta : CapSubst} {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (leftView : S.apply declarativeLeft = .slot leftCap leftTarget)
    (rightView : S.apply declarativeRight = .slot rightCap rightTarget)
    (capDD : OriginSafeExactCapMGU ledger leftCap rightCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (leftTarget.applyCapability capDelta)
      (rightTarget.applyCapability capDelta) targetDelta)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q) :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  let executableLeftCap := leftCap.apply relation.prevailing.reverse.cap
  let executableLeftTarget := relation.prevailing.reverse.apply leftTarget
  let executableRightCap := rightCap.apply relation.prevailing.reverse.cap
  let executableRightTarget := relation.prevailing.reverse.apply rightTarget
  have executableLeftView : initial.prevailing.apply executableLeft =
      .slot executableLeftCap executableLeftTarget := by
    rw [left.reverse, leftView]
    rfl
  have executableRightView : initial.prevailing.apply executableRight =
      .slot executableRightCap executableRightTarget := by
    rw [right.reverse, rightView]
    rfl
  have leftForward := left.forward
  have rightForward := right.forward
  rw [leftView, executableLeftView] at leftForward
  rw [rightView, executableRightView] at rightForward
  have resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse leftCap executableLeftCap rightCap
      executableRightCap :=
    ⟨(Ty.slot.inj leftForward).1, rfl,
      (Ty.slot.inj rightForward).1, rfl⟩
  have declarativeLeftFixed :=
    relation.prevailing.declarativeIdempotent declarativeLeft
  have declarativeRightFixed :=
    relation.prevailing.declarativeIdempotent declarativeRight
  rw [leftView] at declarativeLeftFixed
  rw [rightView] at declarativeRightFixed
  have executableLeftFixed :=
    relation.prevailing.executableIdempotent executableLeft
  have executableRightFixed :=
    relation.prevailing.executableIdempotent executableRight
  rw [executableLeftView] at executableLeftFixed
  rw [executableRightView] at executableRightFixed
  have leftTargetRelated : TyBisimulation relation.prevailing leftTarget
      executableLeftTarget := by
    constructor
    · calc
        S.apply leftTarget = leftTarget := (Ty.slot.inj declarativeLeftFixed).2
        _ = relation.prevailing.forward.apply executableLeftTarget :=
          (Ty.slot.inj leftForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableLeftTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.slot.inj executableLeftFixed).2.symm
    · calc
        initial.prevailing.apply executableLeftTarget = executableLeftTarget :=
          (Ty.slot.inj executableLeftFixed).2
        _ = relation.prevailing.reverse.apply leftTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply leftTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.slot.inj declarativeLeftFixed).2.symm
  have rightTargetRelated : TyBisimulation relation.prevailing rightTarget
      executableRightTarget := by
    constructor
    · calc
        S.apply rightTarget = rightTarget :=
          (Ty.slot.inj declarativeRightFixed).2
        _ = relation.prevailing.forward.apply executableRightTarget :=
          (Ty.slot.inj rightForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableRightTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.slot.inj executableRightFixed).2.symm
    · calc
        initial.prevailing.apply executableRightTarget = executableRightTarget :=
          (Ty.slot.inj executableRightFixed).2
        _ = relation.prevailing.reverse.apply rightTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply rightTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.slot.inj declarativeRightFixed).2.symm
  have declarativeLeftResolvedBounded :=
    relation.declarative_bounded.apply declarativeLeftBounded
  have declarativeRightResolvedBounded :=
    relation.declarative_bounded.apply declarativeRightBounded
  rw [leftView] at declarativeLeftResolvedBounded
  rw [rightView] at declarativeRightResolvedBounded
  have executableLeftResolvedBounded :=
    relation.executable_bounded.apply executableLeftBounded
  have executableRightResolvedBounded :=
    relation.executable_bounded.apply executableRightBounded
  rw [executableLeftView] at executableLeftResolvedBounded
  rw [executableRightView] at executableRightResolvedBounded
  let staged := runResolvedAnnotatedPair_complete (origin := origin) relation
    resolvedCaps leftTargetRelated rightTargetRelated capDD targetDD
    (Ty.slot.inj declarativeLeftFixed).1
    (Ty.slot.inj declarativeRightFixed).1
    (Ty.slot.inj executableLeftFixed).1
    (Ty.slot.inj executableRightFixed).1
    (Ty.slot.inj declarativeLeftFixed).2
    (Ty.slot.inj declarativeRightFixed).2
    declarativeLeftResolvedBounded.slotParts.1
    declarativeRightResolvedBounded.slotParts.1
    executableLeftResolvedBounded.slotParts.1
    executableRightResolvedBounded.slotParts.1
    declarativeLeftResolvedBounded.slotParts.2
    declarativeRightResolvedBounded.slotParts.2
    executableLeftResolvedBounded.slotParts.2
    executableRightResolvedBounded.slotParts.2
  have core : StateRunCompletion relation
      (alignTypesCore initial origin executableLeft executableRight) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
    apply StateRunCompletion.congrOperation staged
    exact alignTypesCore_slotViews executableLeftView executableRightView
      (Ty.slot.inj executableLeftFixed).2
      (Ty.slot.inj executableRightFixed).2
  exact StateRunCompletion.finishAlignTypes core

/-- Public raw completeness theorem for all three ordinary-alignment DD
constructors.  Solver success and MGU orientation are derived internally. -/
theorem ddAlignTypesWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S declarativeLeft
      declarativeRight S') :
    Nonempty (StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q S' ledger) := by
  cases aligned with
  | matcherPair leftView rightView capDD targetDD =>
      exact ⟨alignTypes_matcherPair_complete (origin := origin) relation left
        right leftView rightView capDD targetDD declarativeLeftBounded
        declarativeRightBounded executableLeftBounded executableRightBounded⟩
  | slotPair leftView rightView capDD targetDD =>
      exact ⟨alignTypes_slotPair_complete (origin := origin) relation left right
        leftView rightView capDD targetDD declarativeLeftBounded
        declarativeRightBounded executableLeftBounded executableRightBounded⟩
  | ordinary declarativeClass dd =>
      have executableClass := executableAlignPairClass_ordinary relation left
        right declarativeClass
      exact ⟨alignTypes_ordinary_complete (origin := origin) relation left right
        declarativeLeftBounded declarativeRightBounded executableLeftBounded
        executableRightBounded declarativeClass executableClass dd⟩

/-- Noncomputable package projection used by the main traversal recursion. -/
noncomputable def ddAlignTypesWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S declarativeLeft
      declarativeRight S') :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q S' ledger :=
  Classical.choice (ddAlignTypesWithLedger_complete_nonempty relation left right
    declarativeLeftBounded declarativeRightBounded executableLeftBounded
    executableRightBounded aligned)

/-- The dedicated slot-tuple executable is extensionally the slot/slot
two-stage protocol when its cut-local dual components are already normalized.
This lets the public selector branch reuse the capability/target completeness
proof instead of duplicating solver transport. -/
theorem alignResolvedSlotTupleAtSlot_eq_alignAtSlot
    {state : InferState} {origin : ConstraintOrigin} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (producerCapFixed :
      (Cap.prod (duals.map Dual.cap)).apply state.prevailing.cap =
        .prod (duals.map Dual.cap))
    (producerTargetFixed :
      state.prevailing.apply (.prod (duals.map Dual.target)) =
        .prod (duals.map Dual.target))
    (consumerCapFixed : consumerCap.apply state.prevailing.cap = consumerCap)
    (consumerTargetFixed : state.prevailing.apply consumerTarget =
      consumerTarget) :
    alignResolvedSlotTupleAtSlot state origin duals consumerCap
      consumerTarget =
    alignAtSlot state origin (.slot (.prod (duals.map Dual.cap))
      (.prod (duals.map Dual.target))) (.slot consumerCap consumerTarget) := by
  unfold alignResolvedSlotTupleAtSlot alignAtSlot
  simp only [Subst.apply_slot, producerCapFixed, producerTargetFixed,
    consumerCapFixed, consumerTargetFixed]
  unfold runResolvedConstraint
  unfold solveResolvedWithLedger
  cases solved : solveCapEqWithLedger state.capabilityOrigins
      state.trace.solves.length origin (.prod (duals.map Dual.cap))
      consumerCap with
  | none => simp [solved]
  | some step =>
      have targetEq :
          (step.delta.seq state.prevailing).apply
              (.prod (duals.map Dual.target)) =
            step.delta.apply (.prod (duals.map Dual.target)) := by
        rw [Subst.seq_apply, producerTargetFixed]
      have consumerEq :
          (step.delta.seq state.prevailing).apply consumerTarget =
            step.delta.apply consumerTarget := by
        rw [Subst.seq_apply, consumerTargetFixed]
      have targetMapEq :
          duals.map ((step.delta.seq state.prevailing).apply ∘ Dual.target) =
            duals.map (step.delta.apply ∘ Dual.target) := by
        apply Ty.prod.inj
        simpa only [Subst.apply_prod, List.map_map, Function.comp_apply] using
          targetEq
      simp [solved]
      rw [InferState.prevailing_recordSolve, targetMapEq, consumerEq]

/-- Complete the executable slot-tuple path by reusing the common annotated
pair protocol and the extensional equality above. -/
noncomputable def alignResolvedSlotTuple_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {executableProducerCap executableConsumerCap : Cap}
    {executableProducerTarget executableConsumerTarget : Ty}
    {executableDuals : List Dual} {capDelta : CapSubst}
    {origin : ConstraintOrigin}
    (producerCapEq : executableProducerCap =
      .prod (executableDuals.map Dual.cap))
    (producerTargetEq : executableProducerTarget =
      .prod (executableDuals.map Dual.target))
    (run : StateRunCompletion relation
      (alignAtSlot initial origin
        (.slot executableProducerCap executableProducerTarget)
        (.slot executableConsumerCap executableConsumerTarget)) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger)
    (producerCapFixed : executableProducerCap.apply initial.prevailing.cap =
      executableProducerCap)
    (producerTargetFixed : initial.prevailing.apply executableProducerTarget =
      executableProducerTarget)
    (consumerCapFixed : executableConsumerCap.apply initial.prevailing.cap =
      executableConsumerCap)
    (consumerTargetFixed : initial.prevailing.apply executableConsumerTarget =
      executableConsumerTarget) :
    StateRunCompletion relation
      (alignResolvedSlotTupleAtSlot initial origin executableDuals
        executableConsumerCap executableConsumerTarget) q
      (Subst.seq targetDelta (Subst.seq (capOnly capDelta) S)) ledger := by
  subst executableProducerCap
  subst executableProducerTarget
  apply StateRunCompletion.congrOperation run
  exact alignResolvedSlotTupleAtSlot_eq_alignAtSlot producerCapFixed
    producerTargetFixed consumerCapFixed consumerTargetFixed

/-- Traversal package for one already-resolved producer-to-slot cut.  Solver
success, the matcher transport, and both target-MGU orientations are derived
internally by `oneWayCut_complete_bounded`. -/
noncomputable def runResolvedOneWay_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeProducerCap executableProducerCap : Cap}
    {declarativeProducerTarget executableProducerTarget : Ty}
    {declarativeConsumerCap executableConsumerCap : Cap}
    {declarativeConsumerTarget executableConsumerTarget : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolved : ResolvedOneWayComponents relation.prevailing.forward
      relation.prevailing.reverse
      declarativeProducerCap executableProducerCap
      declarativeProducerTarget executableProducerTarget
      declarativeConsumerCap executableConsumerCap
      declarativeConsumerTarget executableConsumerTarget)
    (dd : OriginSafeOneWayDelta ledger declarativeProducerCap
      declarativeProducerTarget declarativeConsumerCap
      declarativeConsumerTarget delta)
    (declarativeProducerCapFixed :
      declarativeProducerCap.apply S.cap = declarativeProducerCap)
    (declarativeProducerTargetFixed :
      S.apply declarativeProducerTarget = declarativeProducerTarget)
    (declarativeConsumerTargetFixed :
      S.apply declarativeConsumerTarget = declarativeConsumerTarget)
    (executableProducerCapFixed :
      executableProducerCap.apply initial.prevailing.cap = executableProducerCap)
    (executableConsumerCapFixed :
      executableConsumerCap.apply initial.prevailing.cap = executableConsumerCap)
    (executableProducerTargetFixed :
      initial.prevailing.apply executableProducerTarget = executableProducerTarget)
    (executableConsumerTargetFixed :
      initial.prevailing.apply executableConsumerTarget = executableConsumerTarget)
    (declarativeProducerCapBounded : declarativeProducerCap.BoundedBy q)
    (declarativeProducerTargetBounded : declarativeProducerTarget.BoundedBy q)
    (declarativeConsumerCapBounded : declarativeConsumerCap.BoundedBy q)
    (declarativeConsumerTargetBounded : declarativeConsumerTarget.BoundedBy q)
    (executableProducerCapBounded : executableProducerCap.BoundedBy q)
    (executableProducerTargetBounded : executableProducerTarget.BoundedBy q)
    (executableConsumerCapBounded : executableConsumerCap.BoundedBy q)
    (executableConsumerTargetBounded : executableConsumerTarget.BoundedBy q) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.producerToSlot executableProducerCap executableProducerTarget
          executableConsumerCap executableConsumerTarget)) q
      (Subst.seq delta S) ledger := by
  let cut := oneWayCut_complete_bounded relation.prevailing resolved dd
    declarativeProducerCapFixed declarativeProducerTargetFixed
    declarativeConsumerTargetFixed executableProducerCapFixed
    executableConsumerCapFixed executableProducerTargetFixed
    executableConsumerTargetFixed declarativeProducerCapBounded
    declarativeProducerTargetBounded declarativeConsumerCapBounded
    declarativeConsumerTargetBounded executableProducerCapBounded
    executableProducerTargetBounded executableConsumerCapBounded
    executableConsumerTargetBounded relation.forward_bounded
    relation.reverse_bounded initial.trace.solves.length origin
  have protectedSafe : SafeCapVars initial.capabilityOrigins
      cut.step.delta.cap initial.protectedCaps :=
    safeCapVars_of_admissible (by
      rw [cut.stepDeltaEq]
      exact cut.safe.admissible.cap) relation.protected_origins
  have protectedCheck : capSubstSafeVarsCheck initial.capabilityOrigins
      cut.step.delta.cap initial.protectedCaps = true :=
    (capSubstSafeVarsCheck_eq_true _ _ _).2 protectedSafe
  refine
    { result := initial.recordSolve cut.step
      success := ?_
      supply_eq := relation.supply_eq
      transition := cut.transition
      declarative_bounded := cut.declarativeDeltaBounded.seq
        relation.declarative_bounded
      executable_bounded := ?_
      forward_bounded := cut.forwardBounded
      reverse_bounded := cut.reverseBounded
      ledger_below := relation.ledger_below
      executable_ledger_below := relation.executable_ledger_below
      protected_origins := relation.protected_origins.recordSolve cut.step
      protected_below := relation.protected_below.recordSolve cut.step
      allocated_recorded := relation.allocated_recorded.recordSolve cut.step }
  · unfold runResolvedConstraint
    change (do
      let step ← solveProducerToSlotWithLedger initial.capabilityOrigins
        initial.trace.solves.length origin executableProducerCap
        executableProducerTarget executableConsumerCap executableConsumerTarget
      if capSubstSafeVarsCheck initial.capabilityOrigins step.delta.cap
          initial.protectedCaps then
        pure (initial.recordSolve step)
      else none) = some (initial.recordSolve cut.step)
    rw [cut.success]
    simp [protectedCheck]
  · rw [InferState.prevailing_recordSolve]
    rw [cut.stepDeltaEq]
    exact cut.executableDeltaBounded.seq relation.executable_bounded

/-- Matcher-to-slot branch of `alignAtSlot`, with no caller-selected solver
result.  The explicit resolved component equations are precisely the local
head decomposition later supplied by the full DD-alignment induction. -/
noncomputable def alignAtSlot_matcherToSlot_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {declarativeProducerCap executableProducerCap : Cap}
    {declarativeProducerTarget executableProducerTarget : Ty}
    {declarativeConsumerCap executableConsumerCap : Cap}
    {declarativeConsumerTarget executableConsumerTarget : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolved : ResolvedOneWayComponents relation.prevailing.forward
      relation.prevailing.reverse
      declarativeProducerCap executableProducerCap
      declarativeProducerTarget executableProducerTarget
      declarativeConsumerCap executableConsumerCap
      declarativeConsumerTarget executableConsumerTarget)
    (dd : OriginSafeOneWayDelta ledger declarativeProducerCap
      declarativeProducerTarget declarativeConsumerCap
      declarativeConsumerTarget delta)
    (declarativeRawView : S.apply declarativeRaw =
      .matcher declarativeProducerCap declarativeProducerTarget)
    (declarativeExpectedView : S.apply declarativeExpected =
      .slot declarativeConsumerCap declarativeConsumerTarget)
    (executableRawView : initial.prevailing.apply executableRaw =
      .matcher executableProducerCap executableProducerTarget)
    (executableExpectedView : initial.prevailing.apply executableExpected =
      .slot executableConsumerCap executableConsumerTarget)
    (declarativeProducerCapBounded : declarativeProducerCap.BoundedBy q)
    (declarativeProducerTargetBounded : declarativeProducerTarget.BoundedBy q)
    (declarativeConsumerCapBounded : declarativeConsumerCap.BoundedBy q)
    (declarativeConsumerTargetBounded : declarativeConsumerTarget.BoundedBy q)
    (executableProducerCapBounded : executableProducerCap.BoundedBy q)
    (executableProducerTargetBounded : executableProducerTarget.BoundedBy q)
    (executableConsumerCapBounded : executableConsumerCap.BoundedBy q)
    (executableConsumerTargetBounded : executableConsumerTarget.BoundedBy q) :
    StateRunCompletion relation
      (alignAtSlot initial origin executableRaw executableExpected) q
      (Subst.seq delta S) ledger := by
  have declarativeRawFixed := relation.prevailing.declarativeIdempotent
    declarativeRaw
  have declarativeExpectedFixed := relation.prevailing.declarativeIdempotent
    declarativeExpected
  have executableRawFixed := relation.prevailing.executableIdempotent
    executableRaw
  have executableExpectedFixed := relation.prevailing.executableIdempotent
    executableExpected
  rw [declarativeRawView] at declarativeRawFixed
  rw [declarativeExpectedView] at declarativeExpectedFixed
  rw [executableRawView] at executableRawFixed
  rw [executableExpectedView] at executableExpectedFixed
  have localRun := runResolvedOneWay_complete (origin := origin)
    relation resolved dd
    (Ty.matcher.inj declarativeRawFixed).1
    (Ty.matcher.inj declarativeRawFixed).2
    (Ty.slot.inj declarativeExpectedFixed).2
    (Ty.matcher.inj executableRawFixed).1
    (Ty.slot.inj executableExpectedFixed).1
    (Ty.matcher.inj executableRawFixed).2
    (Ty.slot.inj executableExpectedFixed).2
    declarativeProducerCapBounded declarativeProducerTargetBounded
    declarativeConsumerCapBounded declarativeConsumerTargetBounded
    executableProducerCapBounded executableProducerTargetBounded
    executableConsumerCapBounded executableConsumerTargetBounded
  apply DemandTypingInferenceCompletenessAlignmentTraversal.StateRunCompletion.congrOperation
    localRun
  unfold alignAtSlot
  rw [executableRawView, executableExpectedView]

/-- Product-matcher lifting is the same one-way cut once recognition has
assembled the product capability and product target. -/
noncomputable def alignResolvedProductMatcher_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeProducerCap : Cap} {declarativeProducerTarget : Ty}
    {executableDuals : List Dual}
    {declarativeConsumerCap executableConsumerCap : Cap}
    {declarativeConsumerTarget executableConsumerTarget : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (resolved : ResolvedOneWayComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeProducerCap
      (.prod (executableDuals.map Dual.cap)) declarativeProducerTarget
      (.prod (executableDuals.map Dual.target)) declarativeConsumerCap
      executableConsumerCap declarativeConsumerTarget executableConsumerTarget)
    (dd : OriginSafeOneWayDelta ledger declarativeProducerCap
      declarativeProducerTarget declarativeConsumerCap
      declarativeConsumerTarget delta)
    (declarativeProducerCapFixed :
      declarativeProducerCap.apply S.cap = declarativeProducerCap)
    (declarativeProducerTargetFixed :
      S.apply declarativeProducerTarget = declarativeProducerTarget)
    (declarativeConsumerTargetFixed :
      S.apply declarativeConsumerTarget = declarativeConsumerTarget)
    (executableProducerCapFixed :
      (Cap.prod (executableDuals.map Dual.cap)).apply
        initial.prevailing.cap = .prod (executableDuals.map Dual.cap))
    (executableConsumerCapFixed :
      executableConsumerCap.apply initial.prevailing.cap =
        executableConsumerCap)
    (executableProducerTargetFixed :
      initial.prevailing.apply (.prod (executableDuals.map Dual.target)) =
        .prod (executableDuals.map Dual.target))
    (executableConsumerTargetFixed :
      initial.prevailing.apply executableConsumerTarget =
        executableConsumerTarget)
    (declarativeProducerCapBounded : declarativeProducerCap.BoundedBy q)
    (declarativeProducerTargetBounded : declarativeProducerTarget.BoundedBy q)
    (declarativeConsumerCapBounded : declarativeConsumerCap.BoundedBy q)
    (declarativeConsumerTargetBounded : declarativeConsumerTarget.BoundedBy q)
    (executableProducerCapBounded :
      (Cap.prod (executableDuals.map Dual.cap)).BoundedBy q)
    (executableProducerTargetBounded :
      (Ty.prod (executableDuals.map Dual.target)).BoundedBy q)
    (executableConsumerCapBounded : executableConsumerCap.BoundedBy q)
    (executableConsumerTargetBounded : executableConsumerTarget.BoundedBy q) :
    StateRunCompletion relation
      (alignResolvedProductMatcherAtSlot initial origin executableDuals
        executableConsumerCap executableConsumerTarget) q
      (Subst.seq delta S) ledger := by
  let run := runResolvedOneWay_complete (origin := origin) relation resolved dd
    declarativeProducerCapFixed declarativeProducerTargetFixed
    declarativeConsumerTargetFixed executableProducerCapFixed
    executableConsumerCapFixed executableProducerTargetFixed
    executableConsumerTargetFixed declarativeProducerCapBounded
    declarativeProducerTargetBounded declarativeConsumerCapBounded
    declarativeConsumerTargetBounded executableProducerCapBounded
    executableProducerTargetBounded executableConsumerCapBounded
    executableConsumerTargetBounded
  apply StateRunCompletion.congrOperation run
  rfl

end DemandTypingInferenceCompletenessAlignmentTraversal
end TypePM
