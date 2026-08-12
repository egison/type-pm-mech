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

def StateRunCompletion.finishExpectedProductMatcher
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {path : SyntaxPath} {inferred expected : Ty} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (plan : expectedCoercionPlan initial inferred expected =
      .productMatcherLift duals)
    (requested : initial.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (run : StateRunCompletion before
      (alignResolvedProductMatcherAtSlot initial
        (freshOrigin .expression path "expected-type") duals consumerCap
        consumerTarget) q S' ledger) :
    StateRunCompletion before
      (alignExprResultAtExpected path ⟨inferred, initial⟩ expected)
      q S' ledger := by
  let inferredResolved := productMatcherTarget duals
  let requestedResolved := Ty.slot consumerCap consumerTarget
  let event := TraceEvent.slotAlignment initial.trace.solves.length
    run.result.trace.solves.length inferredResolved requestedResolved
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
  rw [plan, requested]
  simp only
  let finish : Option InferState → Option InferState := fun candidate =>
    match candidate with
    | none => none
    | some aligned => some (aligned.recordEvent (.slotAlignment
        initial.trace.solves.length aligned.trace.solves.length
        inferredResolved requestedResolved))
  change finish (alignResolvedProductMatcherAtSlot initial
    (freshOrigin .expression path "expected-type") duals consumerCap
    consumerTarget) = some (run.result.recordEvent event)
  calc
    _ = finish (some run.result) := congrArg finish run.success
    _ = some (run.result.recordEvent event) := rfl

def StateRunCompletion.finishExpectedSlotTuple
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {path : SyntaxPath} {inferred expected : Ty} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (plan : expectedCoercionPlan initial inferred expected =
      .slotTupleLift duals)
    (requested : initial.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (run : StateRunCompletion before
      (alignResolvedSlotTupleAtSlot initial
        (freshOrigin .expression path "expected-type") duals consumerCap
        consumerTarget) q S' ledger) :
    StateRunCompletion before
      (alignExprResultAtExpected path ⟨inferred, initial⟩ expected)
      q S' ledger := by
  let inferredResolved := slotTupleTarget duals
  let requestedResolved := Ty.slot consumerCap consumerTarget
  let event := TraceEvent.slotAlignment initial.trace.solves.length
    run.result.trace.solves.length inferredResolved requestedResolved
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
  rw [plan, requested]
  simp only
  let finish : Option InferState → Option InferState := fun candidate =>
    match candidate with
    | none => none
    | some aligned => some (aligned.recordEvent (.slotAlignment
        initial.trace.solves.length aligned.trace.solves.length
        inferredResolved requestedResolved))
  change finish (alignResolvedSlotTupleAtSlot initial
    (freshOrigin .expression path "expected-type") duals consumerCap
    consumerTarget) = some (run.result.recordEvent event)
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

/-! ## Product matcher lifting -/

noncomputable def productMatcherLift_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (rawView : productMatcherDuals? (S.apply declarativeRaw) = some duals)
    (expectedView : S.apply declarativeExpected =
      .slot consumerCap consumerTarget)
    (dd : OriginSafeOneWayDelta ledger (.prod (duals.map Dual.cap))
      (.prod (duals.map Dual.target)) consumerCap consumerTarget delta)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q) :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q (Subst.seq delta S) ledger := by
  let executableDuals := duals.map
    (Dual.applySubst relation.prevailing.reverse)
  let declarativeProducerCap := Cap.prod (duals.map Dual.cap)
  let declarativeProducerTarget := Ty.prod (duals.map Dual.target)
  let executableProducerCap := Cap.prod (executableDuals.map Dual.cap)
  let executableProducerTarget := Ty.prod (executableDuals.map Dual.target)
  let executableConsumerCap := consumerCap.apply relation.prevailing.reverse.cap
  let executableConsumerTarget := relation.prevailing.reverse.apply consumerTarget
  have executableRawView : productMatcherDuals?
      (initial.prevailing.apply executableRaw) = some executableDuals := by
    rw [raw.reverse]
    exact productMatcherDuals?_apply rawView
  have executableExpectedView : initial.prevailing.apply executableExpected =
      .slot executableConsumerCap executableConsumerTarget := by
    rw [expected.reverse, expectedView]
    rfl
  have declarativeDualsFixed :
      duals.map (Dual.applySubst S) = duals := by
    have fixed := congrArg productMatcherDuals?
      (relation.prevailing.declarativeIdempotent declarativeRaw)
    rw [productMatcherDuals?_apply rawView, rawView] at fixed
    exact Option.some.inj fixed
  have declarativeProducerCapFixed : declarativeProducerCap.apply S.cap =
      declarativeProducerCap := by
    change (Cap.prod (duals.map Dual.cap)).apply S.cap =
      Cap.prod (duals.map Dual.cap)
    simpa only [Cap.apply, Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap))
        declarativeDualsFixed
  have declarativeProducerTargetFixed : S.apply declarativeProducerTarget =
      declarativeProducerTarget := by
    change S.apply (.prod (duals.map Dual.target)) =
      .prod (duals.map Dual.target)
    simpa only [Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target))
        declarativeDualsFixed
  have declarativeConsumerTargetFixed : S.apply consumerTarget =
      consumerTarget := by
    have fixed := relation.prevailing.declarativeIdempotent declarativeExpected
    rw [expectedView] at fixed
    exact (Ty.slot.inj fixed).2
  have dualsReverse : executableDuals =
      duals.map (Dual.applySubst relation.prevailing.reverse) := rfl
  have dualsForward : duals = executableDuals.map
      (Dual.applySubst relation.prevailing.forward) := by
    have moved := congrArg productMatcherDuals? raw.forward
    rw [rawView, productMatcherDuals?_apply executableRawView] at moved
    exact Option.some.inj moved
  have executableProducerCapReverse : executableProducerCap =
      declarativeProducerCap.apply relation.prevailing.reverse.cap := by
    simpa only [executableProducerCap, declarativeProducerCap, Cap.apply,
      Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap)) dualsReverse
  have executableProducerTargetReverse : executableProducerTarget =
      relation.prevailing.reverse.apply declarativeProducerTarget := by
    simpa only [executableProducerTarget, declarativeProducerTarget,
      Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target)) dualsReverse
  have executableProducerCapForward : declarativeProducerCap =
      executableProducerCap.apply relation.prevailing.forward.cap := by
    simpa only [executableProducerCap, declarativeProducerCap, Cap.apply,
      Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap)) dualsForward
  have executableProducerTargetForward : declarativeProducerTarget =
      relation.prevailing.forward.apply executableProducerTarget := by
    simpa only [executableProducerTarget, declarativeProducerTarget,
      Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target)) dualsForward
  have expectedForward := expected.forward
  rw [expectedView, executableExpectedView] at expectedForward
  have declarativeExpectedFixed :=
    relation.prevailing.declarativeIdempotent declarativeExpected
  have executableExpectedFixed :=
    relation.prevailing.executableIdempotent executableExpected
  rw [expectedView] at declarativeExpectedFixed
  rw [executableExpectedView] at executableExpectedFixed
  have resolved : ResolvedOneWayComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeProducerCap
      executableProducerCap declarativeProducerTarget executableProducerTarget
      consumerCap executableConsumerCap consumerTarget
      executableConsumerTarget :=
    ⟨executableProducerCapForward, executableProducerCapReverse,
      executableProducerTargetForward, executableProducerTargetReverse,
      (Ty.slot.inj expectedForward).1, rfl,
      (Ty.slot.inj expectedForward).2, rfl⟩
  have executableDualsFixed : executableDuals.map
      (Dual.applySubst initial.prevailing) = executableDuals := by
    have fixed := congrArg productMatcherDuals?
      (relation.prevailing.executableIdempotent executableRaw)
    rw [productMatcherDuals?_apply executableRawView,
      executableRawView] at fixed
    exact Option.some.inj fixed
  have executableProducerCapFixed : executableProducerCap.apply
      initial.prevailing.cap = executableProducerCap := by
    change (Cap.prod (executableDuals.map Dual.cap)).apply
      initial.prevailing.cap = Cap.prod (executableDuals.map Dual.cap)
    simpa only [Cap.apply, Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap))
        executableDualsFixed
  have executableProducerTargetFixed : initial.prevailing.apply
      executableProducerTarget = executableProducerTarget := by
    change initial.prevailing.apply (.prod (executableDuals.map Dual.target)) =
      .prod (executableDuals.map Dual.target)
    simpa only [Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target))
        executableDualsFixed
  have executableExpectedFixed :=
    relation.prevailing.executableIdempotent executableExpected
  rw [executableExpectedView] at executableExpectedFixed
  have declarativeRawResolved :=
    relation.declarative_bounded.apply declarativeRawBounded
  have declarativeExpectedResolved :=
    relation.declarative_bounded.apply declarativeExpectedBounded
  rw [productMatcherDuals?_sound rawView] at declarativeRawResolved
  rw [expectedView] at declarativeExpectedResolved
  have declarativeDualsBounded : ∀ dual ∈ duals,
      dual.cap.BoundedBy q ∧ dual.target.BoundedBy q := by
    intro dual member
    exact (declarativeRawResolved.of_mem_prod
      (List.mem_map.mpr ⟨dual, member, rfl⟩)).matcherParts
  have declarativeProducerCapBounded : declarativeProducerCap.BoundedBy q := by
    apply Cap.BoundedBy.prodOfForall
    intro cap member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (declarativeDualsBounded dual dualMem).1
  have declarativeProducerTargetBounded :
      declarativeProducerTarget.BoundedBy q := by
    apply Ty.BoundedBy.prodOfForall
    intro target member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (declarativeDualsBounded dual dualMem).2
  have executableRawResolved :=
    relation.executable_bounded.apply executableRawBounded
  have executableExpectedResolved :=
    relation.executable_bounded.apply executableExpectedBounded
  rw [productMatcherDuals?_sound executableRawView] at executableRawResolved
  rw [executableExpectedView] at executableExpectedResolved
  have executableDualsBounded : ∀ dual ∈ executableDuals,
      dual.cap.BoundedBy q ∧ dual.target.BoundedBy q := by
    intro dual member
    exact (executableRawResolved.of_mem_prod
      (List.mem_map.mpr ⟨dual, member, rfl⟩)).matcherParts
  have executableProducerCapBounded : executableProducerCap.BoundedBy q := by
    apply Cap.BoundedBy.prodOfForall
    intro cap member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (executableDualsBounded dual dualMem).1
  have executableProducerTargetBounded : executableProducerTarget.BoundedBy q := by
    apply Ty.BoundedBy.prodOfForall
    intro target member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (executableDualsBounded dual dualMem).2
  let run := alignResolvedProductMatcher_complete
    (origin := freshOrigin .expression path "expected-type") relation resolved dd
    declarativeProducerCapFixed declarativeProducerTargetFixed
    declarativeConsumerTargetFixed executableProducerCapFixed
    (Ty.slot.inj executableExpectedFixed).1 executableProducerTargetFixed
    (Ty.slot.inj executableExpectedFixed).2
    declarativeProducerCapBounded declarativeProducerTargetBounded
    declarativeExpectedResolved.slotParts.1
    declarativeExpectedResolved.slotParts.2 executableProducerCapBounded
    executableProducerTargetBounded executableExpectedResolved.slotParts.1
    executableExpectedResolved.slotParts.2
  have plan : expectedCoercionPlan initial executableRaw executableExpected =
      .productMatcherLift executableDuals := by
    unfold expectedCoercionPlan
    rw [executableRawView, executableExpectedView]
  exact StateRunCompletion.finishExpectedProductMatcher plan
    executableExpectedView run

/-! ## Slot-tuple lifting -/

noncomputable def slotTupleLift_complete
    {q : InferenceBase.FreshSupply} {S targetDelta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    {capDelta : CapSubst} {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (branch : demandClass (S.apply declarativeRaw)
      (S.apply declarativeExpected) = .slotTupleLift)
    (rawView : productSlotDuals? (S.apply declarativeRaw) = some duals)
    (expectedView : S.apply declarativeExpected =
      .slot consumerCap consumerTarget)
    (capDD : OriginSafeExactCapMGU ledger (.prod (duals.map Dual.cap))
      consumerCap capDelta)
    (targetDD : OriginSafeExactPairedMGU ledger
      ((Ty.prod (duals.map Dual.target)).applyCapability capDelta)
      (consumerTarget.applyCapability capDelta) targetDelta)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q) :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q
      (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S)) ledger := by
  let executableDuals := duals.map
    (Dual.applySubst relation.prevailing.reverse)
  let declarativeProducerCap := Cap.prod (duals.map Dual.cap)
  let declarativeProducerTarget := Ty.prod (duals.map Dual.target)
  let executableProducerCap := Cap.prod (executableDuals.map Dual.cap)
  let executableProducerTarget := Ty.prod (executableDuals.map Dual.target)
  let executableConsumerCap := consumerCap.apply relation.prevailing.reverse.cap
  let executableConsumerTarget := relation.prevailing.reverse.apply consumerTarget
  have executableRawView : productSlotDuals?
      (initial.prevailing.apply executableRaw) = some executableDuals := by
    rw [raw.reverse]
    exact productSlotDuals?_apply rawView
  have executableExpectedView : initial.prevailing.apply executableExpected =
      .slot executableConsumerCap executableConsumerTarget := by
    rw [expected.reverse, expectedView]
    rfl
  have declarativeDualsFixed :
      duals.map (Dual.applySubst S) = duals := by
    have fixed := congrArg productSlotDuals?
      (relation.prevailing.declarativeIdempotent declarativeRaw)
    rw [productSlotDuals?_apply rawView, rawView] at fixed
    exact Option.some.inj fixed
  have executableDualsFixed : executableDuals.map
      (Dual.applySubst initial.prevailing) = executableDuals := by
    have fixed := congrArg productSlotDuals?
      (relation.prevailing.executableIdempotent executableRaw)
    rw [productSlotDuals?_apply executableRawView,
      executableRawView] at fixed
    exact Option.some.inj fixed
  have declarativeProducerCapFixed : declarativeProducerCap.apply S.cap =
      declarativeProducerCap := by
    change (Cap.prod (duals.map Dual.cap)).apply S.cap =
      Cap.prod (duals.map Dual.cap)
    simpa only [Cap.apply, Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap))
        declarativeDualsFixed
  have declarativeProducerTargetFixed : S.apply declarativeProducerTarget =
      declarativeProducerTarget := by
    change S.apply (.prod (duals.map Dual.target)) =
      .prod (duals.map Dual.target)
    simpa only [Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target))
        declarativeDualsFixed
  have executableProducerCapFixed : executableProducerCap.apply
      initial.prevailing.cap = executableProducerCap := by
    change (Cap.prod (executableDuals.map Dual.cap)).apply
      initial.prevailing.cap = Cap.prod (executableDuals.map Dual.cap)
    simpa only [Cap.apply, Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap))
        executableDualsFixed
  have executableProducerTargetFixed : initial.prevailing.apply
      executableProducerTarget = executableProducerTarget := by
    change initial.prevailing.apply (.prod (executableDuals.map Dual.target)) =
      .prod (executableDuals.map Dual.target)
    simpa only [Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target))
        executableDualsFixed
  have dualsReverse : executableDuals =
      duals.map (Dual.applySubst relation.prevailing.reverse) := rfl
  have dualsForward : duals = executableDuals.map
      (Dual.applySubst relation.prevailing.forward) := by
    have moved := congrArg productSlotDuals? raw.forward
    rw [rawView, productSlotDuals?_apply executableRawView] at moved
    exact Option.some.inj moved
  have producerCapReverse : executableProducerCap =
      declarativeProducerCap.apply relation.prevailing.reverse.cap := by
    simpa only [executableProducerCap, declarativeProducerCap, Cap.apply,
      Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap)) dualsReverse
  have producerCapForward : declarativeProducerCap =
      executableProducerCap.apply relation.prevailing.forward.cap := by
    simpa only [executableProducerCap, declarativeProducerCap, Cap.apply,
      Dual.map_cap_applySubst] using
      congrArg (fun values => Cap.prod (values.map Dual.cap)) dualsForward
  have producerTargetReverse : executableProducerTarget =
      relation.prevailing.reverse.apply declarativeProducerTarget := by
    simpa only [executableProducerTarget, declarativeProducerTarget,
      Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target)) dualsReverse
  have producerTargetForward : declarativeProducerTarget =
      relation.prevailing.forward.apply executableProducerTarget := by
    simpa only [executableProducerTarget, declarativeProducerTarget,
      Subst.apply_prod, Dual.map_target_applySubst] using
      congrArg (fun values => Ty.prod (values.map Dual.target)) dualsForward
  have expectedForward := expected.forward
  rw [expectedView, executableExpectedView] at expectedForward
  have declarativeExpectedFixed :=
    relation.prevailing.declarativeIdempotent declarativeExpected
  have executableExpectedFixed :=
    relation.prevailing.executableIdempotent executableExpected
  rw [expectedView] at declarativeExpectedFixed
  rw [executableExpectedView] at executableExpectedFixed
  have resolvedCaps : ResolvedCapComponents relation.prevailing.forward
      relation.prevailing.reverse declarativeProducerCap executableProducerCap
      consumerCap executableConsumerCap :=
    ⟨producerCapForward, producerCapReverse,
      (Ty.slot.inj expectedForward).1, rfl⟩
  have producerTargetRelated : TyBisimulation relation.prevailing
      declarativeProducerTarget executableProducerTarget := by
    constructor
    · calc
        S.apply declarativeProducerTarget = declarativeProducerTarget :=
          declarativeProducerTargetFixed
        _ = relation.prevailing.forward.apply executableProducerTarget :=
          producerTargetForward
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableProducerTarget) := by
          rw [executableProducerTargetFixed]
    · calc
        initial.prevailing.apply executableProducerTarget =
            executableProducerTarget := executableProducerTargetFixed
        _ = relation.prevailing.reverse.apply declarativeProducerTarget :=
          producerTargetReverse
        _ = relation.prevailing.reverse.apply
            (S.apply declarativeProducerTarget) := by
          rw [declarativeProducerTargetFixed]
  have consumerTargetRelated : TyBisimulation relation.prevailing
      consumerTarget executableConsumerTarget := by
    constructor
    · calc
        S.apply consumerTarget = consumerTarget :=
          (Ty.slot.inj declarativeExpectedFixed).2
        _ = relation.prevailing.forward.apply executableConsumerTarget :=
          (Ty.slot.inj expectedForward).2
        _ = relation.prevailing.forward.apply
            (initial.prevailing.apply executableConsumerTarget) := by
          exact congrArg relation.prevailing.forward.apply
            (Ty.slot.inj executableExpectedFixed).2.symm
    · calc
        initial.prevailing.apply executableConsumerTarget =
            executableConsumerTarget :=
          (Ty.slot.inj executableExpectedFixed).2
        _ = relation.prevailing.reverse.apply consumerTarget := rfl
        _ = relation.prevailing.reverse.apply (S.apply consumerTarget) := by
          exact congrArg relation.prevailing.reverse.apply
            (Ty.slot.inj declarativeExpectedFixed).2.symm
  have declarativeRawResolved :=
    relation.declarative_bounded.apply declarativeRawBounded
  have declarativeExpectedResolved :=
    relation.declarative_bounded.apply declarativeExpectedBounded
  rw [productSlotDuals?_sound rawView] at declarativeRawResolved
  rw [expectedView] at declarativeExpectedResolved
  have declarativeDualsBounded : ∀ dual ∈ duals,
      dual.cap.BoundedBy q ∧ dual.target.BoundedBy q := by
    intro dual member
    exact (declarativeRawResolved.of_mem_prod
      (List.mem_map.mpr ⟨dual, member, rfl⟩)).slotParts
  have declarativeProducerCapBounded : declarativeProducerCap.BoundedBy q := by
    apply Cap.BoundedBy.prodOfForall
    intro cap member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (declarativeDualsBounded dual dualMem).1
  have declarativeProducerTargetBounded :
      declarativeProducerTarget.BoundedBy q := by
    apply Ty.BoundedBy.prodOfForall
    intro target member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (declarativeDualsBounded dual dualMem).2
  have executableRawResolved :=
    relation.executable_bounded.apply executableRawBounded
  have executableExpectedResolved :=
    relation.executable_bounded.apply executableExpectedBounded
  rw [productSlotDuals?_sound executableRawView] at executableRawResolved
  rw [executableExpectedView] at executableExpectedResolved
  have executableDualsBounded : ∀ dual ∈ executableDuals,
      dual.cap.BoundedBy q ∧ dual.target.BoundedBy q := by
    intro dual member
    exact (executableRawResolved.of_mem_prod
      (List.mem_map.mpr ⟨dual, member, rfl⟩)).slotParts
  have executableProducerCapBounded : executableProducerCap.BoundedBy q := by
    apply Cap.BoundedBy.prodOfForall
    intro cap member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (executableDualsBounded dual dualMem).1
  have executableProducerTargetBounded : executableProducerTarget.BoundedBy q := by
    apply Ty.BoundedBy.prodOfForall
    intro target member
    rcases List.mem_map.mp member with ⟨dual, dualMem, rfl⟩
    exact (executableDualsBounded dual dualMem).2
  let aggregateRun := alignAtSlot_slotToSlot_complete
    (origin := freshOrigin .expression path "expected-type") relation
    resolvedCaps producerTargetRelated consumerTargetRelated capDD targetDD
    declarativeProducerCapFixed (Ty.slot.inj declarativeExpectedFixed).1
    executableProducerCapFixed (Ty.slot.inj executableExpectedFixed).1
    declarativeProducerTargetFixed (Ty.slot.inj declarativeExpectedFixed).2
    executableProducerTargetFixed (Ty.slot.inj executableExpectedFixed).2
    declarativeProducerCapBounded declarativeExpectedResolved.slotParts.1
    executableProducerCapBounded executableExpectedResolved.slotParts.1
    declarativeProducerTargetBounded declarativeExpectedResolved.slotParts.2
    executableProducerTargetBounded executableExpectedResolved.slotParts.2
  let run := alignResolvedSlotTuple_complete (relation := relation) rfl rfl
    aggregateRun executableProducerCapFixed executableProducerTargetFixed
    (Ty.slot.inj executableExpectedFixed).1
    (Ty.slot.inj executableExpectedFixed).2
  have declarativeMatcherNone :
      productMatcherDuals? (S.apply declarativeRaw) = none := by
    unfold demandClass at branch
    cases matcherView : productMatcherDuals? (S.apply declarativeRaw) with
    | none => rfl
    | some matcherDuals =>
        simp [matcherView, expectedView] at branch
  have executableMatcherNone :
      productMatcherDuals? (initial.prevailing.apply executableRaw) = none := by
    rw [raw.reverse]
    exact productMatcherDuals?_apply_none_of_productSlot
      declarativeMatcherNone rawView
  have plan : expectedCoercionPlan initial executableRaw executableExpected =
      .slotTupleLift executableDuals := by
    unfold expectedCoercionPlan
    rw [executableMatcherNone, executableRawView, executableExpectedView]
  exact StateRunCompletion.finishExpectedSlotTuple plan
    executableExpectedView run

/-! ## Ordinary checking -/

theorem executableDemandClass_ordinary
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (ordinary : demandClass (S.apply declarativeRaw)
      (S.apply declarativeExpected) = .ordinary) :
    demandClass (initial.prevailing.apply executableRaw)
      (initial.prevailing.apply executableExpected) = .ordinary := by
  apply Classical.byContradiction
  intro nonOrdinary
  obtain ⟨executableConsumerCap, executableConsumerTarget,
      executableExpectedView⟩ := demandClass_slotDemand nonOrdinary
  have expectedHeads := slotHead_iff_of_mutualInstances expected.forward
    expected.reverse
  obtain ⟨declarativeConsumerCap, declarativeConsumerTarget,
      declarativeExpectedView⟩ := expectedHeads.mpr
        ⟨executableConsumerCap, executableConsumerTarget,
          executableExpectedView⟩
  have rawForward := raw.forward
  have rawReverse := raw.reverse
  have matcherViews := productMatcherView_iff_of_mutualInstances rawForward
    rawReverse
  have slotViews := productSlotView_iff_of_mutualInstances rawForward rawReverse
  cases executableMatcherView : productMatcherDuals?
      (initial.prevailing.apply executableRaw) with
  | some executableDuals =>
      obtain ⟨declarativeDuals, declarativeMatcherView⟩ := matcherViews.mpr
        ⟨executableDuals, executableMatcherView⟩
      unfold demandClass at ordinary
      rw [declarativeMatcherView, declarativeExpectedView] at ordinary
      contradiction
  | none =>
      cases executableSlotView : productSlotDuals?
          (initial.prevailing.apply executableRaw) with
      | some executableDuals =>
          obtain ⟨declarativeDuals, declarativeSlotView⟩ := slotViews.mpr
            ⟨executableDuals, executableSlotView⟩
          cases declarativeMatcherView : productMatcherDuals?
              (S.apply declarativeRaw) with
          | none =>
              simp [demandClass, declarativeMatcherView, declarativeSlotView,
                declarativeExpectedView] at ordinary
          | some declarativeMatcherDuals =>
              simp [demandClass, declarativeMatcherView,
                declarativeExpectedView] at ordinary
      | none =>
          unfold demandClass at nonOrdinary
          rw [executableMatcherView, executableSlotView,
            executableExpectedView] at nonOrdinary
          generalize sourceEq : initial.prevailing.apply executableRaw = source
            at nonOrdinary
          cases source with
          | matcher executableProducerCap executableProducerTarget =>
              have rawHeads := matcherHead_iff_of_mutualInstances rawForward
                rawReverse
              obtain ⟨declarativeProducerCap, declarativeProducerTarget,
                  declarativeRawView⟩ := rawHeads.mpr
                    ⟨executableProducerCap, executableProducerTarget,
                      sourceEq⟩
              simp [demandClass, declarativeExpectedView, declarativeRawView,
                productMatcherDuals?, productSlotDuals?] at ordinary
          | slot executableSourceCap executableSourceTarget =>
              have rawHeads := slotHead_iff_of_mutualInstances rawForward
                rawReverse
              obtain ⟨declarativeSourceCap, declarativeSourceTarget,
                  declarativeRawView⟩ := rawHeads.mpr
                    ⟨executableSourceCap, executableSourceTarget, sourceEq⟩
              simp [demandClass, declarativeExpectedView, declarativeRawView,
                productMatcherDuals?, productSlotDuals?] at ordinary
          | _ => simp at nonOrdinary

theorem expectedCoercionPlan_raw_of_demandClass_ordinary
    {state : InferState} {raw expected : Ty}
    (ordinary : demandClass (state.prevailing.apply raw)
      (state.prevailing.apply expected) = .ordinary) :
    expectedCoercionPlan state raw expected = .raw := by
  unfold demandClass at ordinary
  unfold expectedCoercionPlan
  split <;> simp_all

theorem alignAtSlot_eq_alignTypes_of_demandClass_ordinary
    {state : InferState} {origin : ConstraintOrigin} {raw expected : Ty}
    (ordinary : demandClass (state.prevailing.apply raw)
      (state.prevailing.apply expected) = .ordinary) :
    alignAtSlot state origin raw expected = alignTypes state origin raw expected := by
  unfold demandClass at ordinary
  unfold alignAtSlot
  generalize rawView : state.prevailing.apply raw = resolvedRaw at ordinary ⊢
  generalize expectedView : state.prevailing.apply expected = resolvedExpected
    at ordinary ⊢
  cases resolvedRaw <;> cases resolvedExpected <;>
    simp [productMatcherDuals?, productSlotDuals?] at ordinary ⊢

noncomputable def ordinary_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (ordinary : demandClass (S.apply declarativeRaw)
      (S.apply declarativeExpected) = .ordinary)
    (aligned : DDAlignTypesWithLedger ledger S declarativeRaw
      declarativeExpected S')
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q) :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q S' ledger := by
  have executableOrdinary := executableDemandClass_ordinary relation raw
    expected ordinary
  let alignedRun := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .expression path "expected-type") relation raw
    expected declarativeRawBounded declarativeExpectedBounded
    executableRawBounded executableExpectedBounded aligned
  have rawRun : StateRunCompletion relation
      (alignAtSlot initial (freshOrigin .expression path "expected-type")
        executableRaw executableExpected) q S' ledger := by
    apply StateRunCompletion.congrOperation alignedRun
    exact alignAtSlot_eq_alignTypes_of_demandClass_ordinary executableOrdinary
  exact StateRunCompletion.finishExpectedRaw
    (expectedCoercionPlan_raw_of_demandClass_ordinary executableOrdinary) rawRun

/-! ## Public checking-alignment package -/

theorem ddAlignWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q)
    (aligned : DDAlignWithLedger ledger S declarativeRaw
      declarativeExpected S') :
    Nonempty (StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q S' ledger) := by
  cases aligned with
  | productMatcherLift rawView expectedView dd =>
      exact ⟨productMatcherLift_complete relation raw expected rawView
        expectedView dd declarativeRawBounded declarativeExpectedBounded
        executableRawBounded executableExpectedBounded⟩
  | slotTupleLift branch rawView expectedView capDD targetDD =>
      exact ⟨slotTupleLift_complete relation raw expected branch rawView
        expectedView capDD targetDD declarativeRawBounded
        declarativeExpectedBounded executableRawBounded
        executableExpectedBounded⟩
  | matcherToSlot rawView expectedView dd =>
      exact ⟨matcherToSlot_complete relation raw expected rawView expectedView
        dd declarativeRawBounded declarativeExpectedBounded executableRawBounded
        executableExpectedBounded⟩
  | slotToSlot rawView expectedView capDD targetDD =>
      exact ⟨slotToSlot_complete relation raw expected rawView expectedView
        capDD targetDD declarativeRawBounded declarativeExpectedBounded
        executableRawBounded executableExpectedBounded⟩
  | ordinary branch dd =>
      exact ⟨ordinary_complete relation raw expected branch dd
        declarativeRawBounded declarativeExpectedBounded executableRawBounded
        executableExpectedBounded⟩

/-- Noncomputable projection used by the expression completeness recursion.
All executable solver choices and selector witnesses remain internal. -/
noncomputable def ddAlignWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeRaw executableRaw declarativeExpected executableExpected : Ty}
    {path : SyntaxPath}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (raw : TyBisimulation relation.prevailing declarativeRaw executableRaw)
    (expected : TyBisimulation relation.prevailing declarativeExpected
      executableExpected)
    (declarativeRawBounded : declarativeRaw.BoundedBy q)
    (declarativeExpectedBounded : declarativeExpected.BoundedBy q)
    (executableRawBounded : executableRaw.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q)
    (aligned : DDAlignWithLedger ledger S declarativeRaw
      declarativeExpected S') :
    StateRunCompletion relation
      (alignExprResultAtExpected path ⟨executableRaw, initial⟩
        executableExpected) q S' ledger :=
  Classical.choice (ddAlignWithLedger_complete_nonempty relation raw expected
    declarativeRawBounded declarativeExpectedBounded executableRawBounded
    executableExpectedBounded aligned)

end DemandTypingInferenceCompletenessCheckingAlignment
end TypePM
