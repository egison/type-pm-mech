import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal

/-!
# Checking-cut alignment completeness

This module reconstructs the executable expected-type cut from one
`DDAlignWithLedger` derivation.  The solver choices stay internal to the
alignment traversal packages; the final helper also records the public
`slotAlignment` event produced by `alignExprResultAtExpected`.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessCheckingAlignment

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessOneWayTransport

/-! ## Final event -/

def StateRunCompletion.finishExpectedRaw
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {path : SyntaxPath} {inferred expected : Ty}
    (planRaw : expectedCoercionPlan initial inferred expected = .raw)
    (run : StateRunCompletion before
      (alignAtSlot initial (freshOrigin .expression path "expected-type")
        inferred expected) q S' ledger) :
    StateRunCompletion before
      (alignExprResultAtExpected path ⟨inferred, initial⟩ expected)
      q S' ledger := by
  let event := TraceEvent.slotAlignment initial.trace.solves.length
    run.result.trace.solves.length (initial.prevailing.apply inferred)
    (initial.prevailing.apply expected)
  let extension := run.transition.after.recordEventExtension event
  let final := run.completion.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  refine
    { result := run.result.recordEvent event
      success := ?_
      supply_eq := run.supply_eq
      transition := run.transition.seq extension
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded }
  unfold alignExprResultAtExpected
  rw [planRaw]
  simp only
  let finish : Option InferState → Option InferState := fun candidate =>
    match candidate with
    | none => none
    | some aligned => some (aligned.recordEvent (.slotAlignment
        initial.trace.solves.length aligned.trace.solves.length
        (initial.prevailing.apply inferred)
        (initial.prevailing.apply expected)))
  change finish (alignAtSlot initial
    (freshOrigin .expression path "expected-type") inferred expected) =
      some (run.result.recordEvent event)
  calc
    _ = finish (some run.result) := congrArg finish run.success
    _ = some (run.result.recordEvent event) := rfl

/-! ## Raw matcher to slot -/

noncomputable def matcherToSlot_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (rawView : S.apply declarativeRaw = .matcher producerCap producerTarget)
    (expectedView : S.apply declarativeExpected = .slot consumerCap
      consumerTarget)
    (dd : OriginSafeOneWayDelta ledger producerCap producerTarget consumerCap
      consumerTarget delta)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q) :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q (Subst.seq delta S) ledger := by
  let executableProducerCap := producerCap.apply relation.prevailing.reverse.cap
  let executableProducerTarget := relation.prevailing.reverse.apply producerTarget
  let executableConsumerCap := consumerCap.apply relation.prevailing.reverse.cap
  let executableConsumerTarget := relation.prevailing.reverse.apply consumerTarget
  have executableRawView : initial.prevailing.apply executableRaw =
      .matcher executableProducerCap executableProducerTarget := by
    rw [raw.reverse, rawView]
    rfl
  have executableExpectedView : initial.prevailing.apply executableExpected =
      .slot executableConsumerCap executableConsumerTarget := by
    rw [expected.reverse, expectedView]
    rfl
  have rawForward := raw.forward
  have expectedForward := expected.forward
  rw [rawView, executableRawView] at rawForward
  rw [expectedView, executableExpectedView] at expectedForward
  have resolved : ResolvedOneWayComponents relation.prevailing.forward
      relation.prevailing.reverse producerCap executableProducerCap
      producerTarget executableProducerTarget consumerCap executableConsumerCap
      consumerTarget executableConsumerTarget :=
    ⟨(Ty.matcher.inj rawForward).1, rfl,
      (Ty.matcher.inj rawForward).2, rfl,
      (Ty.slot.inj expectedForward).1, rfl,
      (Ty.slot.inj expectedForward).2, rfl⟩
  have declarativeRawFixed :=
    relation.prevailing.declarativeIdempotent declarativeRaw
  have declarativeExpectedFixed :=
    relation.prevailing.declarativeIdempotent declarativeExpected
  rw [rawView] at declarativeRawFixed
  rw [expectedView] at declarativeExpectedFixed
  have executableRawFixed :=
    relation.prevailing.executableIdempotent executableRaw
  have executableExpectedFixed :=
    relation.prevailing.executableIdempotent executableExpected
  rw [executableRawView] at executableRawFixed
  rw [executableExpectedView] at executableExpectedFixed
  have declarativeRawResolved :=
    relation.declarative_bounded.apply declarativeRawBounded
  have declarativeExpectedResolved :=
    relation.declarative_bounded.apply declarativeExpectedBounded
  rw [rawView] at declarativeRawResolved
  rw [expectedView] at declarativeExpectedResolved
  obtain ⟨producerCapBounded, producerTargetBounded⟩ :=
    declarativeRawResolved.matcherParts
  obtain ⟨consumerCapBounded, consumerTargetBounded⟩ :=
    declarativeExpectedResolved.slotParts
  have executableRawResolved :=
    relation.executable_bounded.apply executableRawBounded
  have executableExpectedResolved :=
    relation.executable_bounded.apply executableExpectedBounded
  rw [executableRawView] at executableRawResolved
  rw [executableExpectedView] at executableExpectedResolved
  obtain ⟨executableProducerCapBounded, executableProducerTargetBounded⟩ :=
    executableRawResolved.matcherParts
  obtain ⟨executableConsumerCapBounded, executableConsumerTargetBounded⟩ :=
    executableExpectedResolved.slotParts
  let run := alignAtSlot_matcherToSlot_complete
    (origin := freshOrigin .expression path "expected-type") relation resolved dd
    rawView expectedView executableRawView executableExpectedView
    producerCapBounded producerTargetBounded consumerCapBounded
    consumerTargetBounded executableProducerCapBounded
    executableProducerTargetBounded executableConsumerCapBounded
    executableConsumerTargetBounded
  have planRaw : expectedCoercionPlan initial executableRaw executableExpected =
      .raw := by
    unfold expectedCoercionPlan
    rw [executableRawView, executableExpectedView]
    rfl
  exact StateRunCompletion.finishExpectedRaw planRaw run

/-! ## Raw slot to slot -/

noncomputable def slotToSlot_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {sourceCap requestedCap : Cap} {sourceTarget requestedTarget : Ty}
    {capDelta : CapSubst} {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (rawView : S.apply declarativeRaw = .slot sourceCap sourceTarget)
    (expectedView : S.apply declarativeExpected = .slot requestedCap
      requestedTarget)
    (capDD : OriginSafeExactCapMGU ledger sourceCap requestedCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      (sourceTarget.applyCapability capDelta)
      (requestedTarget.applyCapability capDelta) targetDelta)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q) :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q
      (Subst.seq targetDelta
        (Subst.seq ⟨capDelta, TySubst.id⟩ S)) ledger := by
  let executableSourceCap := sourceCap.apply relation.prevailing.reverse.cap
  let executableSourceTarget := relation.prevailing.reverse.apply sourceTarget
  let executableRequestedCap := requestedCap.apply relation.prevailing.reverse.cap
  let executableRequestedTarget :=
    relation.prevailing.reverse.apply requestedTarget
  have executableRawView : initial.prevailing.apply executableRaw =
      .slot executableSourceCap executableSourceTarget := by
    rw [raw.reverse, rawView]
    rfl
  have executableExpectedView : initial.prevailing.apply executableExpected =
      .slot executableRequestedCap executableRequestedTarget := by
    rw [expected.reverse, expectedView]
    rfl
  have rawForward := raw.forward
  have expectedForward := expected.forward
  rw [rawView, executableRawView] at rawForward
  rw [expectedView, executableExpectedView] at expectedForward
  have resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse sourceCap executableSourceCap requestedCap
      executableRequestedCap :=
    ⟨(Ty.slot.inj rawForward).1, rfl,
      (Ty.slot.inj expectedForward).1, rfl⟩
  have declarativeRawFixed :=
    relation.prevailing.declarativeIdempotent declarativeRaw
  have declarativeExpectedFixed :=
    relation.prevailing.declarativeIdempotent declarativeExpected
  rw [rawView] at declarativeRawFixed
  rw [expectedView] at declarativeExpectedFixed
  have executableRawFixed :=
    relation.prevailing.executableIdempotent executableRaw
  have executableExpectedFixed :=
    relation.prevailing.executableIdempotent executableExpected
  rw [executableRawView] at executableRawFixed
  rw [executableExpectedView] at executableExpectedFixed
  have rawTargetRelated : TyBisimulation relation.prevailing sourceTarget
      executableSourceTarget := by
    constructor
    · calc
        S.apply sourceTarget = sourceTarget :=
          (Ty.slot.inj declarativeRawFixed).2
        _ = relation.prevailing.forward.apply executableSourceTarget :=
          (Ty.slot.inj rawForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableSourceTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.slot.inj executableRawFixed).2.symm
    · calc
        initial.prevailing.apply executableSourceTarget = executableSourceTarget :=
          (Ty.slot.inj executableRawFixed).2
        _ = relation.prevailing.reverse.apply sourceTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply sourceTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.slot.inj declarativeRawFixed).2.symm
  have expectedTargetRelated : TyBisimulation relation.prevailing
      requestedTarget executableRequestedTarget := by
    constructor
    · calc
        S.apply requestedTarget = requestedTarget :=
          (Ty.slot.inj declarativeExpectedFixed).2
        _ = relation.prevailing.forward.apply executableRequestedTarget :=
          (Ty.slot.inj expectedForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableRequestedTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.slot.inj executableExpectedFixed).2.symm
    · calc
        initial.prevailing.apply executableRequestedTarget =
            executableRequestedTarget :=
          (Ty.slot.inj executableExpectedFixed).2
        _ = relation.prevailing.reverse.apply requestedTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply requestedTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.slot.inj declarativeExpectedFixed).2.symm
  have declarativeRawResolved :=
    relation.declarative_bounded.apply declarativeRawBounded
  have declarativeExpectedResolved :=
    relation.declarative_bounded.apply declarativeExpectedBounded
  have executableRawResolved :=
    relation.executable_bounded.apply executableRawBounded
  have executableExpectedResolved :=
    relation.executable_bounded.apply executableExpectedBounded
  rw [rawView] at declarativeRawResolved
  rw [expectedView] at declarativeExpectedResolved
  rw [executableRawView] at executableRawResolved
  rw [executableExpectedView] at executableExpectedResolved
  let run := alignAtSlot_slotToSlot_complete
    (origin := freshOrigin .expression path "expected-type") relation
    resolvedCaps rawTargetRelated expectedTargetRelated capDD targetDD
    (Ty.slot.inj declarativeRawFixed).1
    (Ty.slot.inj declarativeExpectedFixed).1
    (Ty.slot.inj executableRawFixed).1
    (Ty.slot.inj executableExpectedFixed).1
    (Ty.slot.inj declarativeRawFixed).2
    (Ty.slot.inj declarativeExpectedFixed).2
    (Ty.slot.inj executableRawFixed).2
    (Ty.slot.inj executableExpectedFixed).2
    declarativeRawResolved.slotParts.1
    declarativeExpectedResolved.slotParts.1
    executableRawResolved.slotParts.1
    executableExpectedResolved.slotParts.1
    declarativeRawResolved.slotParts.2
    declarativeExpectedResolved.slotParts.2
    executableRawResolved.slotParts.2
    executableExpectedResolved.slotParts.2
  have planRaw : expectedCoercionPlan initial executableRaw executableExpected =
      .raw := by
    unfold expectedCoercionPlan
    rw [executableRawView, executableExpectedView]
    rfl
  have rawRun : StateRunCompletion relation
      (alignAtSlot initial (freshOrigin .expression path "expected-type")
        executableRaw executableExpected) q
      (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S)) ledger := by
    apply StateRunCompletion.congrOperation run
    unfold alignAtSlot
    rw [executableRawView, executableExpectedView,
      executableRawFixed, executableExpectedFixed]
    unfold runResolvedConstraint
    cases stepEq : solveResolvedWithLedger initial.capabilityOrigins
        initial.trace.solves.length
        (freshOrigin .expression path "expected-type")
        (.capEq executableSourceCap executableRequestedCap) with
    | none => simp [stepEq]
    | some step =>
        have afterRaw : (initial.recordSolve step).prevailing.apply
            executableRaw = (initial.recordSolve step).prevailing.apply
              (.slot executableSourceCap executableSourceTarget) := by
          rw [InferState.prevailing_recordSolve, Subst.seq_apply,
            Subst.seq_apply, executableRawView, executableRawFixed]
        have afterExpected : (initial.recordSolve step).prevailing.apply
            executableExpected = (initial.recordSolve step).prevailing.apply
              (.slot executableRequestedCap executableRequestedTarget) := by
          rw [InferState.prevailing_recordSolve, Subst.seq_apply,
            Subst.seq_apply, executableExpectedView, executableExpectedFixed]
        simp [stepEq]
        rw [afterRaw, afterExpected]
        simp only [Subst.apply_slot]
  exact StateRunCompletion.finishExpectedRaw planRaw rawRun

end DemandTypingInferenceCompletenessCheckingAlignment
end TypePM
