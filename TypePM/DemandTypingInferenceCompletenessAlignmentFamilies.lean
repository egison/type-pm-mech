import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal
import TypePM.DemandTypingInferenceCompletenessDataBisimulation

/-!
# Pattern alignment-family completeness

The ordinary type-alignment completeness theorem is the atomic cut used by
four pattern-layer executors.  This module lifts that theorem to duals,
dual lists, pattern-target lists, and monomorphic binding contexts.  The
wrappers derive every solver fact internally; callers provide only the DD
alignment, the paired traversal data, and the usual supply bounds.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessAlignmentFamilies

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessDataBisimulation

private def capOnly (substitution : CapSubst) : Subst :=
  ⟨substitution, TySubst.id⟩

/-- Empty alignment families leave the state boundary unchanged. -/
private def StateRunCompletion.refl
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial) :
    StateRunCompletion relation (some initial) q S ledger :=
  { result := initial
    success := rfl
    supply_eq := relation.supply_eq
    transition := BisimulationExtension.refl relation.prevailing
    declarative_bounded := relation.declarative_bounded
    executable_bounded := relation.executable_bounded
    forward_bounded := relation.forward_bounded
    reverse_bounded := relation.reverse_bounded
    ledger_below := relation.ledger_below
    executable_ledger_below := relation.executable_ledger_below
    protected_origins := relation.protected_origins
    protected_below := relation.protected_below
    allocated_recorded := relation.allocated_recorded
    protected_safe := relation.protected_safe }

private theorem MonoCtx.BoundedBy.head
    {q : InferenceBase.FreshSupply} {entry : String × Ty} {tail : MonoCtx}
    (bounded : MonoCtx.BoundedBy q (entry :: tail)) :
    Ty.BoundedBy q entry.2 :=
  bounded entry (by simp)

private theorem MonoCtx.BoundedBy.tail
    {q : InferenceBase.FreshSupply} {entry : String × Ty} {tail : MonoCtx}
    (bounded : MonoCtx.BoundedBy q (entry :: tail)) :
    MonoCtx.BoundedBy q tail :=
  fun candidate membership => bounded candidate (by simp [membership])

/-- Append the public dual-alignment event to an already completed capability
and target run. -/
private def StateRunCompletion.finishAlignDuals
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {origin : ConstraintOrigin} {left right : Dual}
    (core : StateRunCompletion before
      (do
        let state ← runResolvedConstraint initial origin
          (.capEq (left.cap.apply initial.prevailing.cap)
            (right.cap.apply initial.prevailing.cap))
        alignTypes state origin left.target right.target) q S' ledger) :
    StateRunCompletion before (alignDuals initial origin left right) q S'
      ledger := by
  let event := TraceEvent.dualAlignment initial.trace.solves.length
    core.result.trace.solves.length left right
    (left.applySubst initial.prevailing) (right.applySubst initial.prevailing)
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
        simp [event, TraceEvent.allocatedCapVars])
      protected_safe := core.protected_safe.recordEvent event }
  rcases Option.bind_eq_some_iff.mp core.success with
    ⟨middle, capSuccess, targetSuccess⟩
  rw [alignDuals.eq_1]
  conv =>
    lhs
    simp [capSuccess, targetSuccess]

/-- Completeness of one dual alignment.  Capability solver success and its
orientation are reconstructed from the ledger-aware DD MGU. -/
theorem ddAlignDualWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Dual}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : DualBisimulation relation.prevailing declarativeLeft
      executableLeft)
    (rightRelated : DualBisimulation relation.prevailing declarativeRight
      executableRight)
    (declarativeLeftBounded : Dual.BoundedBy q declarativeLeft)
    (declarativeRightBounded : Dual.BoundedBy q declarativeRight)
    (executableLeftBounded : Dual.BoundedBy q executableLeft)
    (executableRightBounded : Dual.BoundedBy q executableRight)
    (aligned : DDAlignDualWithLedger ledger S declarativeLeft declarativeRight
      S') :
    Nonempty (StateRunCompletion relation
      (alignDuals initial origin executableLeft executableRight) q S' ledger) := by
  cases aligned with
  | mk capDD targetsAligned =>
      let declarativeLeftCap := declarativeLeft.cap.apply S.cap
      let declarativeRightCap := declarativeRight.cap.apply S.cap
      let executableLeftCap := executableLeft.cap.apply initial.prevailing.cap
      let executableRightCap := executableRight.cap.apply initial.prevailing.cap
      have resolved : ResolvedCapComponents relation.prevailing.forward
          relation.prevailing.reverse declarativeLeftCap executableLeftCap
          declarativeRightCap executableRightCap := by
        exact ⟨(Ty.matcher.inj leftRelated.cap.forward).1,
          (Ty.matcher.inj leftRelated.cap.reverse).1,
          (Ty.matcher.inj rightRelated.cap.forward).1,
          (Ty.matcher.inj rightRelated.cap.reverse).1⟩
      have declarativeLeftFixed :
          declarativeLeftCap.apply S.cap = declarativeLeftCap := by
        exact (Ty.matcher.inj
          (relation.prevailing.declarativeIdempotent
            (.matcher declarativeLeft.cap .unit))).1
      have declarativeRightFixed :
          declarativeRightCap.apply S.cap = declarativeRightCap := by
        exact (Ty.matcher.inj
          (relation.prevailing.declarativeIdempotent
            (.matcher declarativeRight.cap .unit))).1
      have executableLeftFixed :
          executableLeftCap.apply initial.prevailing.cap =
            executableLeftCap := by
        exact (Ty.matcher.inj
          (relation.prevailing.executableIdempotent
            (.matcher executableLeft.cap .unit))).1
      have executableRightFixed :
          executableRightCap.apply initial.prevailing.cap =
            executableRightCap := by
        exact (Ty.matcher.inj
          (relation.prevailing.executableIdempotent
            (.matcher executableRight.cap .unit))).1
      have declarativeLeftCapBounded : declarativeLeftCap.BoundedBy q :=
        relation.declarative_bounded.applyCap declarativeLeftBounded.1
      have declarativeRightCapBounded : declarativeRightCap.BoundedBy q :=
        relation.declarative_bounded.applyCap declarativeRightBounded.1
      have executableLeftCapBounded : executableLeftCap.BoundedBy q :=
        relation.executable_bounded.applyCap executableLeftBounded.1
      have executableRightCapBounded : executableRightCap.BoundedBy q :=
        relation.executable_bounded.applyCap executableRightBounded.1
      let capRun := runResolvedCapEq_complete (origin := origin) relation
        resolved capDD declarativeLeftFixed declarativeRightFixed
        executableLeftFixed executableRightFixed declarativeLeftCapBounded
        declarativeRightCapBounded executableLeftCapBounded
        executableRightCapBounded
      let targetRun := ddAlignTypesWithLedger_complete (origin := origin)
        capRun.completion (capRun.transition.transportTy leftRelated.target)
        (capRun.transition.transportTy rightRelated.target)
        declarativeLeftBounded.2 declarativeRightBounded.2
        executableLeftBounded.2 executableRightBounded.2 targetsAligned
      exact ⟨StateRunCompletion.finishAlignDuals
        (StateRunCompletion.seq capRun targetRun)⟩

/-- Noncomputable package projection used by recursive pattern alignments. -/
noncomputable def ddAlignDualWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Dual}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : DualBisimulation relation.prevailing declarativeLeft
      executableLeft)
    (rightRelated : DualBisimulation relation.prevailing declarativeRight
      executableRight)
    (declarativeLeftBounded : Dual.BoundedBy q declarativeLeft)
    (declarativeRightBounded : Dual.BoundedBy q declarativeRight)
    (executableLeftBounded : Dual.BoundedBy q executableLeft)
    (executableRightBounded : Dual.BoundedBy q executableRight)
    (aligned : DDAlignDualWithLedger ledger S declarativeLeft declarativeRight
      S') :
    StateRunCompletion relation
      (alignDuals initial origin executableLeft executableRight) q S' ledger :=
  Classical.choice (ddAlignDualWithLedger_complete_nonempty relation
    leftRelated rightRelated declarativeLeftBounded declarativeRightBounded
    executableLeftBounded executableRightBounded aligned)

/-- Completeness of pointwise dual-list alignment. -/
theorem ddAlignDualListWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLefts declarativeRights executableLefts executableRights :
      List Dual}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : DualListBisimulation relation.prevailing declarativeLefts
      executableLefts)
    (rightRelated : DualListBisimulation relation.prevailing declarativeRights
      executableRights)
    (declarativeLeftsBounded : ∀ dual ∈ declarativeLefts,
      Dual.BoundedBy q dual)
    (declarativeRightsBounded : ∀ dual ∈ declarativeRights,
      Dual.BoundedBy q dual)
    (executableLeftsBounded : ∀ dual ∈ executableLefts,
      Dual.BoundedBy q dual)
    (executableRightsBounded : ∀ dual ∈ executableRights,
      Dual.BoundedBy q dual)
    (aligned : DDAlignDualListWithLedger ledger S declarativeLefts
      declarativeRights S') :
    Nonempty (StateRunCompletion relation
      (alignDualLists initial origin executableLefts executableRights) q S'
      ledger) := by
  induction aligned generalizing initial executableLefts executableRights with
  | nil =>
      cases leftRelated
      cases rightRelated
      exact ⟨StateRunCompletion.refl relation⟩
  | cons headAligned tailAligned induction =>
      cases leftRelated with
      | cons leftHead leftTail =>
          cases rightRelated with
          | cons rightHead rightTail =>
              let headRun := ddAlignDualWithLedger_complete (origin := origin)
                relation leftHead rightHead
                (declarativeLeftsBounded _ (by simp))
                (declarativeRightsBounded _ (by simp))
                (executableLeftsBounded _ (by simp))
                (executableRightsBounded _ (by simp)) headAligned
              let tailExists := induction headRun.completion
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
                  headRun.transition leftTail)
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
                  headRun.transition rightTail)
                (fun dual mem => declarativeLeftsBounded dual (by simp [mem]))
                (fun dual mem => declarativeRightsBounded dual (by simp [mem]))
                (fun dual mem => executableLeftsBounded dual (by simp [mem]))
                (fun dual mem => executableRightsBounded dual (by simp [mem]))
              let tailRun := Classical.choice tailExists
              exact ⟨StateRunCompletion.congrOperation
                (StateRunCompletion.seq headRun tailRun) (by rfl)⟩

/-- Noncomputable package projection for dual-list callers. -/
noncomputable def ddAlignDualListWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLefts declarativeRights executableLefts executableRights :
      List Dual}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : DualListBisimulation relation.prevailing declarativeLefts
      executableLefts)
    (rightRelated : DualListBisimulation relation.prevailing declarativeRights
      executableRights)
    (declarativeLeftsBounded : ∀ dual ∈ declarativeLefts,
      Dual.BoundedBy q dual)
    (declarativeRightsBounded : ∀ dual ∈ declarativeRights,
      Dual.BoundedBy q dual)
    (executableLeftsBounded : ∀ dual ∈ executableLefts,
      Dual.BoundedBy q dual)
    (executableRightsBounded : ∀ dual ∈ executableRights,
      Dual.BoundedBy q dual)
    (aligned : DDAlignDualListWithLedger ledger S declarativeLefts
      declarativeRights S') :
    StateRunCompletion relation
      (alignDualLists initial origin executableLefts executableRights) q S'
      ledger :=
  Classical.choice (ddAlignDualListWithLedger_complete_nonempty relation
    leftRelated rightRelated declarativeLeftsBounded declarativeRightsBounded
    executableLeftsBounded executableRightsBounded aligned)

/-- Completeness of pattern-result target alignment. -/
theorem ddAlignTargetListWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeDuals executableDuals : List Dual}
    {declarativeExpecteds executableExpecteds : List Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (dualsRelated : DualListBisimulation relation.prevailing declarativeDuals
      executableDuals)
    (expectedsRelated : TyListBisimulation relation.prevailing
      declarativeExpecteds executableExpecteds)
    (declarativeDualsBounded : ∀ dual ∈ declarativeDuals,
      Dual.BoundedBy q dual)
    (declarativeExpectedsBounded : ∀ target ∈ declarativeExpecteds,
      Ty.BoundedBy q target)
    (executableDualsBounded : ∀ dual ∈ executableDuals,
      Dual.BoundedBy q dual)
    (executableExpectedsBounded : ∀ target ∈ executableExpecteds,
      Ty.BoundedBy q target)
    (aligned : DDAlignTargetListWithLedger ledger S declarativeDuals
      declarativeExpecteds S') :
    Nonempty (StateRunCompletion relation
      (alignPatternTargets initial origin executableDuals executableExpecteds)
      q S' ledger) := by
  induction aligned generalizing initial executableDuals executableExpecteds with
  | nil =>
      cases dualsRelated
      cases expectedsRelated
      exact ⟨StateRunCompletion.refl relation⟩
  | cons headAligned tailAligned induction =>
      cases dualsRelated with
      | cons dualHead dualTail =>
          cases expectedsRelated with
          | cons expectedHead expectedTail =>
              let headRun := ddAlignTypesWithLedger_complete
                (origin := origin) relation dualHead.target expectedHead
                (declarativeDualsBounded _ (by simp)).2
                (declarativeExpectedsBounded _ (by simp))
                (executableDualsBounded _ (by simp)).2
                (executableExpectedsBounded _ (by simp)) headAligned
              let tailExists := induction headRun.completion
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
                  headRun.transition dualTail)
                (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
                  headRun.transition expectedTail)
                (fun dual mem => declarativeDualsBounded dual (by simp [mem]))
                (fun target mem => declarativeExpectedsBounded target
                  (by simp [mem]))
                (fun dual mem => executableDualsBounded dual (by simp [mem]))
                (fun target mem => executableExpectedsBounded target
                  (by simp [mem]))
              let tailRun := Classical.choice tailExists
              exact ⟨StateRunCompletion.congrOperation
                (StateRunCompletion.seq headRun tailRun) (by rfl)⟩

/-- Noncomputable package projection for pattern-target callers. -/
noncomputable def ddAlignTargetListWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeDuals executableDuals : List Dual}
    {declarativeExpecteds executableExpecteds : List Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (dualsRelated : DualListBisimulation relation.prevailing declarativeDuals
      executableDuals)
    (expectedsRelated : TyListBisimulation relation.prevailing
      declarativeExpecteds executableExpecteds)
    (declarativeDualsBounded : ∀ dual ∈ declarativeDuals,
      Dual.BoundedBy q dual)
    (declarativeExpectedsBounded : ∀ target ∈ declarativeExpecteds,
      Ty.BoundedBy q target)
    (executableDualsBounded : ∀ dual ∈ executableDuals,
      Dual.BoundedBy q dual)
    (executableExpectedsBounded : ∀ target ∈ executableExpecteds,
      Ty.BoundedBy q target)
    (aligned : DDAlignTargetListWithLedger ledger S declarativeDuals
      declarativeExpecteds S') :
    StateRunCompletion relation
      (alignPatternTargets initial origin executableDuals executableExpecteds)
      q S' ledger :=
  Classical.choice (ddAlignTargetListWithLedger_complete_nonempty relation
    dualsRelated expectedsRelated declarativeDualsBounded
    declarativeExpectedsBounded executableDualsBounded
    executableExpectedsBounded aligned)

/-- Completeness of entrywise or-pattern binding alignment. -/
theorem ddAlignBindingsWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLefts declarativeRights executableLefts executableRights :
      MonoCtx}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : MonoCtxBisimulation relation.prevailing declarativeLefts
      executableLefts)
    (rightRelated : MonoCtxBisimulation relation.prevailing declarativeRights
      executableRights)
    (declarativeLeftsBounded : MonoCtx.BoundedBy q declarativeLefts)
    (declarativeRightsBounded : MonoCtx.BoundedBy q declarativeRights)
    (executableLeftsBounded : MonoCtx.BoundedBy q executableLefts)
    (executableRightsBounded : MonoCtx.BoundedBy q executableRights)
    (aligned : DDAlignBindingsWithLedger ledger S declarativeLefts
      declarativeRights S') :
    Nonempty (StateRunCompletion relation
      (alignBindings initial origin executableLefts executableRights) q S'
      ledger) := by
  induction aligned generalizing initial executableLefts executableRights with
  | nil =>
      cases leftRelated
      cases rightRelated
      exact ⟨StateRunCompletion.refl relation⟩
  | cons namesEq headAligned tailAligned induction =>
      cases leftRelated with
      | cons leftHead leftTail =>
          cases rightRelated with
          | cons rightHead rightTail =>
              cases namesEq
              let headRun := ddAlignTypesWithLedger_complete
                (origin := origin) relation leftHead rightHead
                (MonoCtx.BoundedBy.head declarativeLeftsBounded)
                (MonoCtx.BoundedBy.head declarativeRightsBounded)
                (MonoCtx.BoundedBy.head executableLeftsBounded)
                (MonoCtx.BoundedBy.head executableRightsBounded)
                headAligned
              let tailExists := induction headRun.completion
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                  headRun.transition leftTail)
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                  headRun.transition rightTail)
                (MonoCtx.BoundedBy.tail declarativeLeftsBounded)
                (MonoCtx.BoundedBy.tail declarativeRightsBounded)
                (MonoCtx.BoundedBy.tail executableLeftsBounded)
                (MonoCtx.BoundedBy.tail executableRightsBounded)
              let tailRun := Classical.choice tailExists
              exact ⟨StateRunCompletion.congrOperation
                (StateRunCompletion.seq
                  (secondOperation := fun state => alignBindings state origin
                    _ _) headRun tailRun) (by
                  simp [alignBindings])⟩

/-- Noncomputable package projection for binding-alignment callers. -/
noncomputable def ddAlignBindingsWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLefts declarativeRights executableLefts executableRights :
      MonoCtx}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (leftRelated : MonoCtxBisimulation relation.prevailing declarativeLefts
      executableLefts)
    (rightRelated : MonoCtxBisimulation relation.prevailing declarativeRights
      executableRights)
    (declarativeLeftsBounded : MonoCtx.BoundedBy q declarativeLefts)
    (declarativeRightsBounded : MonoCtx.BoundedBy q declarativeRights)
    (executableLeftsBounded : MonoCtx.BoundedBy q executableLefts)
    (executableRightsBounded : MonoCtx.BoundedBy q executableRights)
    (aligned : DDAlignBindingsWithLedger ledger S declarativeLefts
      declarativeRights S') :
    StateRunCompletion relation
      (alignBindings initial origin executableLefts executableRights) q S'
      ledger :=
  Classical.choice (ddAlignBindingsWithLedger_complete_nonempty relation
    leftRelated rightRelated declarativeLeftsBounded declarativeRightsBounded
    executableLeftsBounded executableRightsBounded aligned)

end DemandTypingInferenceCompletenessAlignmentFamilies
end TypePM
