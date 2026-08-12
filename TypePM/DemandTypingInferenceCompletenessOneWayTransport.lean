import TypePM.DemandTypingInferenceCompletenessStateMutual
import TypePM.DemandTypingInferenceCompletenessLocalRenaming
import TypePM.DemandTypingInferenceCompletenessOneWayCapability
import TypePM.DemandTypingInferenceCompletenessOneWayTarget
import TypePM.InferenceLocalFactorization

/-!
# Transport for heterogeneous producer-to-slot cuts

`TyBisimulation` relates resolved DD and executable operands by a common
forward/reverse pair, but the resolved capability and target syntax need not
be literally equal.  This file derives the corresponding executable
`matchCap` and target-MGU run from that ordinary state relation.

The boundary is real.  If the reverse residual is not ledger-admissible, two
collapsed solved states can relate a legal `renameOnly` match to an illegal
one whose image is `structuralFlexible`; the executable ledger check then
rejects.  `StateBisimulation.ledgerBisimulation` rules out that state-level
counterexample.  Scoped renaming extracted from the same state relation then
supplies the exact matcher and target-MGU equivariance facts.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessOneWayTransport

open Inference
open DemandTypingInferenceCompletenessOneWay
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessOneWayCapability
open DemandTypingInferenceCompletenessOneWayTarget

private def restrictCapPost (post : CapSubst) (scope : List CapVar) :
    CapSubst := fun varId =>
  if varId ∈ scope then post varId else .var varId

private theorem restrictCapPost_admissible
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (admissible : AdmissibleCapPost ledger post) (scope : List CapVar) :
    AdmissibleCapPost ledger (restrictCapPost post scope) := by
  intro varId
  by_cases member : varId ∈ scope
  · simpa [restrictCapPost, member] using admissible varId
  · simp only [restrictCapPost, member, ↓reduceIte]
    cases origin : ledger.originOf varId with
    | rigid => trivial
    | renameOnly => exact ⟨varId, rfl, by simp [origin]⟩
    | structuralFlexible => trivial

/-- Mutual component renaming transports declarative one-way acceptance to
executable `matchCap` success.  The conjugate post is restricted back to the
consumer support before invoking completeness, so no behavior of the state
residuals on unrelated variables enters the witness. -/
theorem matchCap_complete_of_components
    {forward reverse declarativeCap : CapSubst}
    {declarativeProducer executableProducer : Cap}
    {declarativeConsumer executableConsumer : Cap}
    (producerForward :
      declarativeProducer = executableProducer.apply forward)
    (producerReverse :
      executableProducer = declarativeProducer.apply reverse)
    (consumerForward :
      declarativeConsumer = executableConsumer.apply forward)
    (consumerReverse :
      executableConsumer = declarativeConsumer.apply reverse)
    (oneWay : OneWayAt declarativeCap declarativeProducer
      declarativeConsumer) :
    ∃ bindings, CapMatch.matchCap executableProducer executableConsumer =
      some bindings := by
  let forwardPost := CapSubst.comp declarativeCap forward
  let conjugate := CapSubst.comp reverse forwardPost
  have forwardDemand : DemandMatches forwardPost
      (executableProducer.apply forwardPost) executableConsumer :=
    oneWayAt_forward_postDemand producerForward consumerForward
      consumerReverse oneWay
  have conjugateDemand : DemandMatches conjugate executableProducer
      executableConsumer := by
    have transported := demandMatches_comp reverse forwardPost forwardDemand
    have producerEq : (executableProducer.apply forwardPost).apply reverse =
        executableProducer := by
      dsimp [forwardPost]
      rw [Cap.apply_comp]
      rw [← producerForward, oneWay.2.1, ← producerReverse]
    simpa only [conjugate, producerEq] using transported
  have conjugateStable : executableProducer.apply conjugate =
      executableProducer := by
    dsimp [conjugate, forwardPost]
    rw [Cap.apply_comp, Cap.apply_comp]
    rw [← producerForward, oneWay.2.1, ← producerReverse]
  let restricted := restrictCapPost conjugate executableConsumer.fcv
  have restrictedSupport : restricted.SupportWithin executableConsumer.fcv := by
    intro varId outside
    simp [restricted, restrictCapPost, outside]
  have restrictedDemand : DemandMatches restricted executableProducer
      executableConsumer := by
    apply CapMatch.demandMatches_congr_on_consumer conjugate restricted
      executableProducer executableConsumer conjugateDemand
    intro varId member
    simp [restricted, restrictCapPost, member]
  have restrictedStable : executableProducer.apply restricted =
      executableProducer := by
    calc
      executableProducer.apply restricted =
          executableProducer.apply CapSubst.id := by
        apply CapMatch.apply_congr_on_fcv
        intro varId producerMember
        have conjugateFixed : conjugate varId = .var varId := by
          have agrees := Cap.apply_eq_on_fcv conjugate CapSubst.id
            executableProducer (by
              rw [conjugateStable, Cap.apply_id]) varId producerMember
          simpa [CapSubst.id] using agrees
        by_cases consumerMember : varId ∈ executableConsumer.fcv
        · simp [restricted, restrictCapPost, consumerMember,
            conjugateFixed, CapSubst.id]
        · simp [restricted, restrictCapPost, consumerMember, CapSubst.id]
      _ = executableProducer := Cap.apply_id executableProducer
  exact CapMatch.matchCap_complete
    ⟨restricted, restrictedSupport, restrictedStable, restrictedDemand⟩

/-- The transported matcher result also passes the origin policy.  This is
the form needed to run the ledger-aware one-way solver rather than merely to
establish syntactic matchability. -/
theorem matchCap_complete_admissible_of_components
    {declarativeLedger executableLedger : CapabilityOriginLedger}
    {forward reverse declarativeCap : CapSubst}
    {declarativeProducer executableProducer : Cap}
    {declarativeConsumer executableConsumer : Cap}
    (forwardAdmissible : AdmissibleCapPostBetween executableLedger
      declarativeLedger forward)
    (reverseAdmissible : AdmissibleCapPostBetween declarativeLedger
      executableLedger reverse)
    (declarativeAdmissible : AdmissibleCapPost declarativeLedger
      declarativeCap)
    (producerForward :
      declarativeProducer = executableProducer.apply forward)
    (producerReverse :
      executableProducer = declarativeProducer.apply reverse)
    (consumerForward :
      declarativeConsumer = executableConsumer.apply forward)
    (consumerReverse :
      executableConsumer = declarativeConsumer.apply reverse)
    (oneWay : OneWayAt declarativeCap declarativeProducer
      declarativeConsumer) :
    ∃ bindings,
      CapMatch.matchCap executableProducer executableConsumer =
        some bindings ∧
      AdmissibleCapPost executableLedger
        (bindings.toSubstWithin executableConsumer.fcv) := by
  obtain ⟨bindings, matched⟩ := matchCap_complete_of_components
    producerForward producerReverse consumerForward consumerReverse oneWay
  let forwardPost := CapSubst.comp declarativeCap forward
  let conjugate := CapSubst.comp reverse forwardPost
  let restricted := restrictCapPost conjugate executableConsumer.fcv
  have forwardDemand : DemandMatches forwardPost
      (executableProducer.apply forwardPost) executableConsumer :=
    oneWayAt_forward_postDemand producerForward consumerForward
      consumerReverse oneWay
  have conjugateDemand : DemandMatches conjugate executableProducer
      executableConsumer := by
    have transported := demandMatches_comp reverse forwardPost forwardDemand
    have producerEq : (executableProducer.apply forwardPost).apply reverse =
        executableProducer := by
      dsimp [forwardPost]
      rw [Cap.apply_comp]
      rw [← producerForward, oneWay.2.1, ← producerReverse]
    simpa only [conjugate, producerEq] using transported
  have conjugateStable : executableProducer.apply conjugate =
      executableProducer := by
    dsimp [conjugate, forwardPost]
    rw [Cap.apply_comp, Cap.apply_comp]
    rw [← producerForward, oneWay.2.1, ← producerReverse]
  have restrictedSupport : restricted.SupportWithin executableConsumer.fcv := by
    intro varId outside
    simp [restricted, restrictCapPost, outside]
  have restrictedDemand : DemandMatches restricted executableProducer
      executableConsumer := by
    apply CapMatch.demandMatches_congr_on_consumer conjugate restricted
      executableProducer executableConsumer conjugateDemand
    intro varId member
    simp [restricted, restrictCapPost, member]
  have restrictedStable : executableProducer.apply restricted =
      executableProducer := by
    calc
      executableProducer.apply restricted =
          executableProducer.apply CapSubst.id := by
        apply CapMatch.apply_congr_on_fcv
        intro varId producerMember
        have conjugateFixed : conjugate varId = .var varId := by
          have agrees := Cap.apply_eq_on_fcv conjugate CapSubst.id
            executableProducer (by
              rw [conjugateStable, Cap.apply_id]) varId producerMember
          simpa [CapSubst.id] using agrees
        by_cases consumerMember : varId ∈ executableConsumer.fcv
        · simp [restricted, restrictCapPost, consumerMember,
            conjugateFixed, CapSubst.id]
        · simp [restricted, restrictCapPost, consumerMember, CapSubst.id]
      _ = executableProducer := Cap.apply_id executableProducer
  have restrictedOneWay : OneWayAt restricted executableProducer
      executableConsumer :=
    ⟨restrictedSupport, restrictedStable, restrictedDemand⟩
  have exactEq : bindings.toSubstWithin executableConsumer.fcv = restricted :=
    Inference.capMatchRestricted_eq_of_oneWayAt matched restrictedOneWay
  have conjugateAdmissible : AdmissibleCapPost executableLedger conjugate := by
    dsimp [conjugate, forwardPost]
    exact AdmissibleCapPostBetween.toAdmissible
      (AdmissibleCapPostBetween.comp reverseAdmissible
        (AdmissibleCapPostBetween.comp
          (AdmissibleCapPostBetween.ofAdmissible declarativeAdmissible)
          forwardAdmissible))
  refine ⟨bindings, matched, ?_⟩
  rw [exactEq]
  exact restrictCapPost_admissible conjugateAdmissible _

/-- Component equations obtained after exposing matcher/slot heads on both
sides of a `TyBisimulation`.  One pair of residuals must relate all four
components; unrelated existential renamings are insufficient for repeated
consumer variables. -/
structure ResolvedOneWayComponents
    (forward reverse : Subst)
    (declarativeProducerCap executableProducerCap : Cap)
    (declarativeProducerTarget executableProducerTarget : Ty)
    (declarativeConsumerCap executableConsumerCap : Cap)
    (declarativeConsumerTarget executableConsumerTarget : Ty) : Prop where
  producerCapForward :
    declarativeProducerCap = executableProducerCap.apply forward.cap
  producerCapReverse :
    executableProducerCap = declarativeProducerCap.apply reverse.cap
  producerTargetForward :
    declarativeProducerTarget = forward.apply executableProducerTarget
  producerTargetReverse :
    executableProducerTarget = reverse.apply declarativeProducerTarget
  consumerCapForward :
    declarativeConsumerCap = executableConsumerCap.apply forward.cap
  consumerCapReverse :
    executableConsumerCap = declarativeConsumerCap.apply reverse.cap
  consumerTargetForward :
    declarativeConsumerTarget = forward.apply executableConsumerTarget
  consumerTargetReverse :
    executableConsumerTarget = reverse.apply declarativeConsumerTarget

/-- The exact local fact needed after `matchCap` renaming transport: the DD
and executable deltas mutually factor through one another under the same
incoming residuals.  This is stronger than two independent MGU
factorizations and is precisely what chronological state transport consumes.
-/
structure OneWayDeltaBisimulation
    (declarativeLedger executableLedger : CapabilityOriginLedger)
    (forward reverse declarativeDelta executableDelta : Subst) : Type where
  forwardAfter : Subst
  forwardEquation :
    Subst.seq declarativeDelta forward =
      Subst.seq forwardAfter executableDelta
  forwardAdmissible : AdmissiblePostBetween executableLedger
    declarativeLedger forwardAfter
  reverseAfter : Subst
  reverseEquation :
    Subst.seq executableDelta reverse =
      Subst.seq reverseAfter declarativeDelta
  reverseAdmissible : AdmissiblePostBetween declarativeLedger
    executableLedger reverseAfter

/-- Compose a heterogeneous DD/executable delta transport with a second
transport that only changes the executable representative. -/
def OneWayDeltaBisimulation.trans
    {declarativeLedger executableLedger : CapabilityOriginLedger}
    {forward reverse declarativeDelta middleDelta executableDelta : Subst}
    (first : OneWayDeltaBisimulation declarativeLedger executableLedger
      forward reverse
      declarativeDelta middleDelta)
    (second : OneWayDeltaBisimulation executableLedger executableLedger
      Subst.id Subst.id
      middleDelta executableDelta) :
    OneWayDeltaBisimulation declarativeLedger executableLedger forward reverse
      declarativeDelta executableDelta where
  forwardAfter := Subst.seq first.forwardAfter second.forwardAfter
  forwardEquation := by
    calc
      Subst.seq declarativeDelta forward =
          Subst.seq first.forwardAfter middleDelta := first.forwardEquation
      _ = Subst.seq first.forwardAfter
          (Subst.seq second.forwardAfter executableDelta) := by
        rw [← second.forwardEquation, Subst.seq_id_right]
      _ = Subst.seq
          (Subst.seq first.forwardAfter second.forwardAfter)
            executableDelta :=
        PhasedPost.seq_assoc first.forwardAfter second.forwardAfter
          executableDelta
  forwardAdmissible :=
    first.forwardAdmissible.seq second.forwardAdmissible
  reverseAfter := Subst.seq second.reverseAfter first.reverseAfter
  reverseEquation := by
    calc
      Subst.seq executableDelta reverse =
          Subst.seq (Subst.seq executableDelta Subst.id) reverse := by
        rw [Subst.seq_id_right]
      _ = Subst.seq
          (Subst.seq second.reverseAfter middleDelta) reverse := by
        rw [second.reverseEquation]
      _ = Subst.seq second.reverseAfter
          (Subst.seq middleDelta reverse) :=
        (PhasedPost.seq_assoc second.reverseAfter middleDelta reverse).symm
      _ = Subst.seq second.reverseAfter
          (Subst.seq first.reverseAfter declarativeDelta) := by
        rw [first.reverseEquation]
      _ = Subst.seq
          (Subst.seq second.reverseAfter first.reverseAfter)
            declarativeDelta :=
        PhasedPost.seq_assoc second.reverseAfter first.reverseAfter
          declarativeDelta
  reverseAdmissible :=
    second.reverseAdmissible.seq first.reverseAdmissible

/-- Delta-level bisimulation is exactly sufficient to extend the global state
relation across the emitted one-way solver step.  No solver implementation or
capability syntax is unfolded here. -/
def StateBisimulation.oneWayCut_recordSolve
    {ledger : CapabilityOriginLedger} {declarative declarativeDelta : Subst}
    {state : InferState} {step : SolveStep} {executableDelta : Subst}
    (before : StateBisimulation ledger declarative state)
    (deltaRelation : OneWayDeltaBisimulation ledger state.capabilityOrigins
      before.forward before.reverse declarativeDelta executableDelta)
    (declarativeAfterIdempotent :
      (Subst.seq declarativeDelta declarative).Idempotent)
    (executableAfterIdempotent :
      (Subst.seq executableDelta state.prevailing).Idempotent)
    (stepDelta : step.delta = executableDelta) :
    BisimulationExtension before ledger
      (Subst.seq declarativeDelta declarative) (state.recordSolve step) := by
  let after : StateBisimulation ledger
      (Subst.seq declarativeDelta declarative) (state.recordSolve step) :=
    { forward := deltaRelation.forwardAfter
      forwardEquation := by
        rw [InferState.prevailing_recordSolve, stepDelta]
        calc
          Subst.seq declarativeDelta declarative =
              Subst.seq declarativeDelta
                (Subst.seq before.forward state.prevailing) := by
            exact congrArg (Subst.seq declarativeDelta)
              before.forwardEquation
          _ =
              Subst.seq (Subst.seq declarativeDelta before.forward)
                state.prevailing :=
            PhasedPost.seq_assoc declarativeDelta before.forward
              state.prevailing
          _ = Subst.seq
              (Subst.seq deltaRelation.forwardAfter executableDelta)
                state.prevailing := by rw [deltaRelation.forwardEquation]
          _ = Subst.seq deltaRelation.forwardAfter
              (Subst.seq executableDelta state.prevailing) :=
            (PhasedPost.seq_assoc deltaRelation.forwardAfter executableDelta
              state.prevailing).symm
      declarativeIdempotent := declarativeAfterIdempotent
      reverse := deltaRelation.reverseAfter
      reverseEquation := by
        rw [InferState.prevailing_recordSolve, stepDelta]
        calc
          Subst.seq executableDelta state.prevailing =
              Subst.seq executableDelta
                (Subst.seq before.reverse declarative) := by
            exact congrArg (Subst.seq executableDelta)
              before.reverseEquation
          _ =
              Subst.seq (Subst.seq executableDelta before.reverse)
                declarative :=
            PhasedPost.seq_assoc executableDelta before.reverse declarative
          _ = Subst.seq
              (Subst.seq deltaRelation.reverseAfter declarativeDelta) declarative := by
            rw [deltaRelation.reverseEquation]
          _ = Subst.seq deltaRelation.reverseAfter
              (Subst.seq declarativeDelta declarative) :=
            (PhasedPost.seq_assoc deltaRelation.reverseAfter declarativeDelta
              declarative).symm
      ledgerBisimulation :=
        ⟨deltaRelation.forwardAdmissible,
          deltaRelation.reverseAdmissible⟩
      executableIdempotent := by
        rw [InferState.prevailing_recordSolve, stepDelta]
        exact executableAfterIdempotent }
  refine { after := after, transportTy := ?_ }
  intro declarativeTarget executableTarget related
  constructor
  · rw [InferState.prevailing_recordSolve, stepDelta]
    change (Subst.seq declarativeDelta declarative).apply
        declarativeTarget =
      deltaRelation.forwardAfter.apply
        ((Subst.seq executableDelta state.prevailing).apply executableTarget)
    calc
      (Subst.seq declarativeDelta declarative).apply declarativeTarget =
          (Subst.seq declarativeDelta before.forward).apply
            (state.prevailing.apply executableTarget) := by
        simp only [Subst.seq_apply, related.forward]
      _ = (Subst.seq deltaRelation.forwardAfter executableDelta).apply
            (state.prevailing.apply executableTarget) := by
        rw [deltaRelation.forwardEquation]
      _ = deltaRelation.forwardAfter.apply
          ((Subst.seq executableDelta state.prevailing).apply
            executableTarget) := by
        simp only [Subst.seq_apply]
  · rw [InferState.prevailing_recordSolve, stepDelta]
    change (Subst.seq executableDelta state.prevailing).apply
        executableTarget =
      deltaRelation.reverseAfter.apply
        ((Subst.seq declarativeDelta declarative).apply declarativeTarget)
    calc
      (Subst.seq executableDelta state.prevailing).apply executableTarget =
          (Subst.seq executableDelta before.reverse).apply
            (declarative.apply declarativeTarget) := by
        simp only [Subst.seq_apply, related.reverse]
      _ = (Subst.seq deltaRelation.reverseAfter declarativeDelta).apply
            (declarative.apply declarativeTarget) := by
        rw [deltaRelation.reverseEquation]
      _ = deltaRelation.reverseAfter.apply
          ((Subst.seq declarativeDelta declarative).apply
            declarativeTarget) := by
        simp only [Subst.seq_apply]

/-- Every emitted dedicated one-way step also carries an origin-safe exact
one-way delta, not merely local soundness. -/
theorem solveProducerToSlotWithLedger_originSafeOneWayDelta
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {step : SolveStep}
    (success : solveProducerToSlotWithLedger ledger solveCount origin
      producerCap producerTarget consumerCap consumerTarget = some step) :
    OriginSafeOneWayDelta ledger producerCap producerTarget consumerCap
      consumerTarget step.delta := by
  have admissible : AdmissiblePost ledger step.delta :=
    Inference.solveResolvedWithLedger_producerToSlot_admissible success
  refine ⟨?_, admissible⟩
  unfold solveProducerToSlotWithLedger at success
  split at success
  · contradiction
  · rename_i bindings matchSuccess
    simp only at success
    split at success
    · split at success
      · contradiction
      · rename_i targetSubst targetSuccess
        have stepEq := Option.some.inj success
        subst step
        exact ⟨bindings, matchSuccess, rfl,
          Unification.mguTy_exactTargetMGU targetSuccess⟩
    · contradiction

/-- A concrete one-way solver delta is absorbed by every paired post whose
capability component absorbs the matcher and which solves the resulting
capability-adjusted target equation.  This is the chronological form needed
when the ambient residual itself is not support-restricted. -/
theorem solveProducerToSlotWithLedger_absorbs
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {step : SolveStep} {later : Subst}
    (success : solveProducerToSlotWithLedger ledger solveCount origin
      producerCap producerTarget consumerCap consumerTarget = some step)
    (capAbsorbs : later.cap = CapSubst.comp later.cap step.delta.cap)
    (targetSound :
      later.apply (producerTarget.applyCapability step.delta.cap) =
        later.apply (consumerTarget.applyCapability step.delta.cap)) :
    later = Subst.seq later step.delta := by
  unfold solveProducerToSlotWithLedger at success
  split at success
  · contradiction
  · rename_i bindings matched
    simp only at success
    split at success
    · split at success
      · contradiction
      · rename_i targetSubst targetSuccess
        have stepEq := Option.some.inj success
        subst step
        have targetAbsorbs := Unification.mguTy_paired_absorbs
          targetSuccess targetSound
        apply PhasedPost.subst_ext
        · exact capAbsorbs
        · funext varId
          have atVar := congrFun (congrArg Subst.target targetAbsorbs) varId
          change later.target varId = later.apply (targetSubst varId)
          change later.target varId = later.apply (targetSubst varId) at atVar
          exact atVar
    · contradiction

/-- Reverse target factorization lifted to paired sequential composition. -/
theorem OneWaySolverCorrespondence.executable_delta_factorization
    {declarative : Subst} {step : SolveStep}
    (correspondence : OneWaySolverCorrespondence declarative step) :
    ∃ residualTarget : TySubst,
      step.delta = Subst.seq
        (Subst.mk CapSubst.id residualTarget) declarative := by
  rcases correspondence.executableTargetFactorsThroughDeclarative with
    ⟨residualTarget, targetEq⟩
  refine ⟨residualTarget, ?_⟩
  apply PhasedPost.subst_ext
  · rw [correspondence.capabilityEq]
    funext varId
    exact (Cap.apply_id (declarative.cap varId)).symm
  · funext varId
    change step.delta.target varId =
      ((declarative.target varId).applyCapability CapSubst.id).applyTarget
        residualTarget
    rw [Ty.applyCapability_id]
    exact congrFun targetEq varId

private theorem targetOnly_admissible
    (ledger : CapabilityOriginLedger) (target : TySubst) :
    AdmissiblePost ledger (Subst.mk CapSubst.id target) :=
  { cap := AdmissibleCapPost.id ledger }

/-- Any paired post solving a target constraint absorbs an exact target MGU.
We intentionally prove absorption directly rather than selecting the raw
residual returned by ordinary MGU universality: that total-function residual
is unconstrained outside the finite input and need not be bounded.  Direct
absorption retains the already bounded competitor as the residual. -/
theorem ExactTargetMGU.paired_absorbs
    {left right : Ty} {target : TySubst} (exact : ExactTargetMGU left right target)
    {post : Subst} (sound : post.apply left = post.apply right) :
    post = Subst.seq post (Subst.mk CapSubst.id target) := by
  obtain ⟨algorithm, algorithmSuccess⟩ :=
    Unification.mguTy_complete exact.1.1
  have algorithmAbsorbs :=
    Unification.mguTy_paired_absorbs algorithmSuccess sound
  obtain ⟨residual, algorithmFactors⟩ :=
    exact.1.2 algorithm (Unification.mguTy_sound algorithmSuccess)
  let exactPair := Subst.mk CapSubst.id target
  let residualPair := Subst.mk CapSubst.id residual
  have liftedFactor : Subst.mk CapSubst.id algorithm =
      Subst.seq residualPair exactPair := by
    apply PhasedPost.subst_ext
    · funext varId
      exact (Cap.apply_id (CapSubst.id varId)).symm
    · funext varId
      simpa [residualPair, exactPair, Subst.seq, Subst.apply,
        Ty.applyCapability_id, TySubst.comp] using
        congrFun algorithmFactors varId
  have factors : post = Subst.seq (Subst.seq post residualPair) exactPair := by
    calc
      post = Subst.seq post (Subst.mk CapSubst.id algorithm) :=
        algorithmAbsorbs
      _ = Subst.seq post (Subst.seq residualPair exactPair) := by
        rw [← liftedFactor]
      _ = Subst.seq (Subst.seq post residualPair) exactPair :=
        PhasedPost.seq_assoc post residualPair exactPair
  have exactPairIdempotent : Subst.seq exactPair exactPair = exactPair := by
    apply PhasedPost.subst_ext
    · funext varId
      exact Cap.apply_id (CapSubst.id varId)
    · funext varId
      simpa only [exactPair, Subst.seq, Subst.apply, Ty.applyCapability_id,
        Ty.applyCapability, Ty.applyTarget] using
        exact.2.2.2.2 (.var varId)
  calc
    post = Subst.seq (Subst.seq post residualPair) exactPair := factors
    _ = Subst.seq (Subst.seq post residualPair)
        (Subst.seq exactPair exactPair) := by rw [exactPairIdempotent]
    _ = Subst.seq
        (Subst.seq (Subst.seq post residualPair) exactPair) exactPair :=
      PhasedPost.seq_assoc (Subst.seq post residualPair) exactPair exactPair
    _ = Subst.seq post exactPair := by rw [← factors]

/-- The solver correspondence itself is a delta bisimulation with identity
incoming residuals. -/
noncomputable def OneWaySolverCorrespondence.deltaBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {step : SolveStep}
    (correspondence : OneWaySolverCorrespondence declarative step) :
    OneWayDeltaBisimulation ledger ledger Subst.id Subst.id declarative
      step.delta := by
  let forwardTarget := Classical.choose
    correspondence.declarative_delta_factorization
  have forwardEq : declarative = Subst.seq
      (Subst.mk CapSubst.id forwardTarget) step.delta :=
    Classical.choose_spec correspondence.declarative_delta_factorization
  let reverseTarget := Classical.choose
    (executable_delta_factorization correspondence)
  have reverseEq : step.delta = Subst.seq
      (Subst.mk CapSubst.id reverseTarget) declarative :=
    Classical.choose_spec (executable_delta_factorization correspondence)
  exact
    { forwardAfter := Subst.mk CapSubst.id forwardTarget
      forwardEquation := by simpa using forwardEq
      forwardAdmissible := AdmissiblePostBetween.ofAdmissible
        (targetOnly_admissible ledger forwardTarget)
      reverseAfter := Subst.mk CapSubst.id reverseTarget
      reverseEquation := by simpa using reverseEq
      reverseAdmissible := AdmissiblePostBetween.ofAdmissible
        (targetOnly_admissible ledger reverseTarget) }

/-- Complete output package for one heterogeneous one-way cut. -/
structure OneWayCutCompletion
    {ledger : CapabilityOriginLedger}
    {declarative declarativeDelta : Subst} {state : InferState}
    (before : StateBisimulation ledger declarative state)
    (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty)
    (solveCount : Nat) (origin : ConstraintOrigin) : Type where
  executableDelta : Subst
  step : SolveStep
  safe : OriginSafeOneWayDelta state.capabilityOrigins producerCap
    producerTarget consumerCap consumerTarget executableDelta
  success : solveProducerToSlotWithLedger state.capabilityOrigins solveCount
    origin producerCap producerTarget consumerCap consumerTarget = some step
  solverRelation : OneWaySolverCorrespondence executableDelta step
  transition : BisimulationExtension before ledger
    (Subst.seq declarativeDelta declarative) (state.recordSolve step)

/-- Traversal-facing strengthening: every substitution introduced by the
one-way cut, including the two derived state residuals, stays below the
current fresh supply. -/
structure BoundedOneWayCutCompletion
    {ledger : CapabilityOriginLedger}
    {declarative declarativeDelta : Subst} {state : InferState}
    (before : StateBisimulation ledger declarative state)
    (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty)
    (solveCount : Nat) (origin : ConstraintOrigin)
    (q : InferenceBase.FreshSupply) : Type
    extends OneWayCutCompletion (declarativeDelta := declarativeDelta) before
      producerCap producerTarget consumerCap consumerTarget solveCount origin where
  declarativeDeltaBounded : declarativeDelta.BoundedBy q
  executableDeltaBounded : executableDelta.BoundedBy q
  forwardBounded : transition.after.forward.BoundedBy q
  reverseBounded : transition.after.reverse.BoundedBy q

/-- Positive local transport theorem used by the coercive `DDAlign` branch.
It simultaneously obtains the executable origin-safe delta, the actual
solver step, and the chronological bisimulation extension.  Thus callers do
not have to identify the DD and executable `matchCap` bindings or choose a
canonical target-MGU orientation. -/
noncomputable def oneWayCut_complete
    {ledger : CapabilityOriginLedger}
    {declarative declarativeDelta : Subst} {state : InferState}
    {declarativeProducerCap executableProducerCap : Cap}
    {declarativeProducerTarget executableProducerTarget : Ty}
    {declarativeConsumerCap executableConsumerCap : Cap}
    {declarativeConsumerTarget executableConsumerTarget : Ty}
    (before : StateBisimulation ledger declarative state)
    (resolved : ResolvedOneWayComponents before.forward before.reverse
      declarativeProducerCap executableProducerCap
      declarativeProducerTarget executableProducerTarget
      declarativeConsumerCap executableConsumerCap
      declarativeConsumerTarget executableConsumerTarget)
    (dd : OriginSafeOneWayDelta ledger declarativeProducerCap
      declarativeProducerTarget declarativeConsumerCap
      declarativeConsumerTarget declarativeDelta)
    (declarativeProducerCapFixed :
      declarativeProducerCap.apply declarative.cap = declarativeProducerCap)
    (declarativeProducerTargetFixed :
      declarative.apply declarativeProducerTarget =
        declarativeProducerTarget)
    (declarativeConsumerTargetFixed :
      declarative.apply declarativeConsumerTarget =
        declarativeConsumerTarget)
    (executableProducerCapFixed :
      executableProducerCap.apply state.prevailing.cap =
        executableProducerCap)
    (executableConsumerCapFixed :
      executableConsumerCap.apply state.prevailing.cap =
        executableConsumerCap)
    (executableProducerTargetFixed :
      state.prevailing.apply executableProducerTarget =
        executableProducerTarget)
    (executableConsumerTargetFixed :
      state.prevailing.apply executableConsumerTarget =
        executableConsumerTarget)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    OneWayCutCompletion (declarativeDelta := declarativeDelta) before
      executableProducerCap executableProducerTarget executableConsumerCap
      executableConsumerTarget solveCount origin := by
  let capScope := executableConsumerCap.fcv ++
    executableProducerTarget.fcv ++ executableConsumerTarget.fcv
  have capsFixed : ∀ varId ∈ capScope,
      state.prevailing.cap varId = .var varId := by
    intro varId member
    rcases List.mem_append.mp member with earlierMem | consumerTargetMem
    · rcases List.mem_append.mp earlierMem with consumerCapMem | producerMem
      · have point := Cap.apply_eq_on_fcv state.prevailing.cap CapSubst.id
          executableConsumerCap (by
            rw [executableConsumerCapFixed, Cap.apply_id]) varId consumerCapMem
        simpa [CapSubst.id] using point
      · apply before.executableIdempotent.image_cap_fixed
          executableProducerTarget varId
        rw [executableProducerTargetFixed]
        exact producerMem
    · apply before.executableIdempotent.image_cap_fixed
        executableConsumerTarget varId
      rw [executableConsumerTargetFixed]
      exact consumerTargetMem
  have localMap : LocalRenamingOn before.forward before.reverse capScope [] :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn
      before capsFixed (by simp)
  let ddBindings := Classical.choose dd.exact
  have ddExact := Classical.choose_spec dd.exact
  have ddMatched := ddExact.1
  have ddCapEq := ddExact.2.1
  have ddTargetExact := ddExact.2.2
  have ddOneWay : OneWayAt declarativeDelta.cap declarativeProducerCap
      declarativeConsumerCap := by
    rw [ddCapEq]
    exact CapMatch.matchCap_restricted_sound ddMatched
  have capWitness := matchCap_complete_admissible_of_components
      before.ledgerBisimulation.forwardBetween.cap
      before.ledgerBisimulation.reverseBetween.cap dd.admissible.cap
      resolved.producerCapForward resolved.producerCapReverse
      resolved.consumerCapForward resolved.consumerCapReverse ddOneWay
  let bindings := Classical.choose capWitness
  have capProof := Classical.choose_spec capWitness
  have matched := capProof.1
  have capAdmissible := capProof.2
  let executableCap := bindings.toSubstWithin executableConsumerCap.fcv
  have executableOneWay : OneWayAt executableCap executableProducerCap
      executableConsumerCap :=
    CapMatch.matchCap_restricted_sound matched
  have capConjugacy : ∀ varId,
      varId ∈ executableProducerTarget.fcv ++ executableConsumerTarget.fcv →
      ((before.forward.cap varId).apply declarativeDelta.cap).apply
          before.reverse.cap = executableCap varId := by
    apply oneWay_capConjugacy_on_targets localMap
      resolved.producerCapForward resolved.producerCapReverse
      resolved.consumerCapForward resolved.consumerCapReverse ddOneWay
      executableOneWay
    · intro varId member
      exact List.mem_append_left _ (List.mem_append_left _ member)
    · intro varId member
      rcases List.mem_append.mp member with producerMem | consumerMem
      · exact List.mem_append_left _ (List.mem_append_right _ producerMem)
      · exact List.mem_append_right _ consumerMem
  have targetWitness := mguTy_complete_of_oneWay_capConjugacy
      resolved.producerTargetForward resolved.consumerTargetForward
      capConjugacy ddTargetExact
  let executableTarget := Classical.choose targetWitness
  have targetSuccess := Classical.choose_spec targetWitness
  let executableDelta := Subst.mk executableCap executableTarget
  have executableSafe : OriginSafeOneWayDelta state.capabilityOrigins
      executableProducerCap executableProducerTarget executableConsumerCap
      executableConsumerTarget executableDelta := by
    refine ⟨⟨bindings, matched, rfl, ?_⟩, ⟨capAdmissible⟩⟩
    exact Unification.mguTy_exactTargetMGU targetSuccess
  let solverWitness := solveProducerToSlotWithLedger_complete executableSafe
    solveCount origin
  let step := Classical.choose solverWitness
  have solverProof := Classical.choose_spec solverWitness
  have stepSuccess := solverProof.1
  have solverRelation := solverProof.2
  have stepSafe := solveProducerToSlotWithLedger_originSafeOneWayDelta
    stepSuccess
  let forwardLater := Subst.seq declarativeDelta before.forward
  have forwardDemand : DemandMatches forwardLater.cap
      (executableProducerCap.apply forwardLater.cap) executableConsumerCap := by
    simpa only [forwardLater, Subst.seq] using
      oneWayAt_forward_postDemand resolved.producerCapForward
        resolved.consumerCapForward resolved.consumerCapReverse ddOneWay
  have forwardCapAbsorbs : forwardLater.cap =
      CapSubst.comp forwardLater.cap executableDelta.cap := by
    change forwardLater.cap = CapSubst.comp forwardLater.cap executableCap
    exact capMatchRestricted_absorbed matched forwardLater.cap forwardDemand
  have forwardReplay (target : Ty) :
      forwardLater.apply (target.applyCapability executableDelta.cap) =
        forwardLater.apply target := by
    change ((target.applyCapability executableCap).applyCapability
        forwardLater.cap).applyTarget forwardLater.target =
      (target.applyCapability forwardLater.cap).applyTarget forwardLater.target
    rw [← Ty.applyCapability_comp, ← forwardCapAbsorbs]
  have forwardRawSound : forwardLater.apply executableProducerTarget =
      forwardLater.apply executableConsumerTarget := by
    simp only [forwardLater, Subst.seq_apply]
    rw [← resolved.producerTargetForward,
      ← resolved.consumerTargetForward]
    exact ddTargetExact.1.1
  have forwardTargetSound :
      forwardLater.apply
          (executableProducerTarget.applyCapability executableDelta.cap) =
        forwardLater.apply
          (executableConsumerTarget.applyCapability executableDelta.cap) := by
    rw [forwardReplay, forwardReplay]
    exact forwardRawSound
  have forwardAbsorbs : forwardLater =
      Subst.seq forwardLater executableDelta := by
    have targetAbsorbs := Unification.mguTy_paired_absorbs targetSuccess
      forwardTargetSound
    apply PhasedPost.subst_ext
    · exact forwardCapAbsorbs
    · funext varId
      have atVar := congrFun (congrArg Subst.target targetAbsorbs) varId
      change forwardLater.target varId =
        forwardLater.apply (executableTarget varId)
      change forwardLater.target varId =
        forwardLater.apply (executableTarget varId) at atVar
      exact atVar
  let reverseLater := Subst.seq executableDelta before.reverse
  have reverseDemand : DemandMatches reverseLater.cap
      (declarativeProducerCap.apply reverseLater.cap)
      declarativeConsumerCap := by
    simpa only [reverseLater, Subst.seq] using
      oneWayAt_forward_postDemand resolved.producerCapReverse
        resolved.consumerCapReverse resolved.consumerCapForward executableOneWay
  have reverseCapAbsorbs : reverseLater.cap =
      CapSubst.comp reverseLater.cap declarativeDelta.cap := by
    rw [ddCapEq]
    exact capMatchRestricted_absorbed ddMatched reverseLater.cap reverseDemand
  have reverseReplay (target : Ty) :
      reverseLater.apply (target.applyCapability declarativeDelta.cap) =
        reverseLater.apply target := by
    change ((target.applyCapability declarativeDelta.cap).applyCapability
        reverseLater.cap).applyTarget reverseLater.target =
      (target.applyCapability reverseLater.cap).applyTarget reverseLater.target
    rw [← Ty.applyCapability_comp, ← reverseCapAbsorbs]
  have reverseRawSound : reverseLater.apply declarativeProducerTarget =
      reverseLater.apply declarativeConsumerTarget := by
    simp only [reverseLater, Subst.seq_apply]
    rw [← resolved.producerTargetReverse,
      ← resolved.consumerTargetReverse]
    exact Unification.mguTy_sound targetSuccess
  have reverseTargetSound :
      reverseLater.apply
          (declarativeProducerTarget.applyCapability declarativeDelta.cap) =
        reverseLater.apply
          (declarativeConsumerTarget.applyCapability declarativeDelta.cap) := by
    rw [reverseReplay, reverseReplay]
    exact reverseRawSound
  have reverseTargetAbsorbs : reverseLater = Subst.seq reverseLater
      (Subst.mk CapSubst.id declarativeDelta.target) :=
    ExactTargetMGU.paired_absorbs ddTargetExact reverseTargetSound
  have reverseAbsorbs : reverseLater =
      Subst.seq reverseLater declarativeDelta := by
    apply PhasedPost.subst_ext
    · exact reverseCapAbsorbs
    · funext varId
      have atVar := congrFun (congrArg Subst.target reverseTargetAbsorbs) varId
      change reverseLater.target varId =
        reverseLater.apply (declarativeDelta.target varId)
      change reverseLater.target varId =
        reverseLater.apply (declarativeDelta.target varId) at atVar
      exact atVar
  let reverseAfter := reverseLater
  have reverseEquation : Subst.seq executableDelta before.reverse =
      Subst.seq reverseAfter declarativeDelta := by
    exact reverseAbsorbs
  let transportedRelation : OneWayDeltaBisimulation ledger
      state.capabilityOrigins before.forward before.reverse declarativeDelta
      executableDelta :=
    { forwardAfter := forwardLater
      forwardEquation := forwardAbsorbs
      forwardAdmissible := before.ledgerBisimulation.enterAdmissible dd.admissible
      reverseAfter := reverseAfter
      reverseEquation := reverseEquation
      reverseAdmissible :=
        (AdmissiblePostBetween.ofAdmissible executableSafe.admissible).seq
          before.ledgerBisimulation.reverseBetween }
  have declarativeAfterIdempotent :
      (Subst.seq declarativeDelta declarative).Idempotent :=
    DemandTypingIdempotence.OneWayDelta.seq_idempotent_of_fixed
      before.declarativeIdempotent dd.exact declarativeProducerCapFixed
      declarativeProducerTargetFixed declarativeConsumerTargetFixed
  have executableAfterIdempotent :
      (Subst.seq step.delta state.prevailing).Idempotent :=
    DemandTypingIdempotence.OneWayDelta.seq_idempotent_of_fixed
      before.executableIdempotent stepSafe.exact executableProducerCapFixed
      executableProducerTargetFixed executableConsumerTargetFixed
  let finalDeltaRelation := transportedRelation.trans
    (DemandTypingInferenceCompletenessOneWayTransport.OneWaySolverCorrespondence.deltaBisimulation
      (ledger := state.capabilityOrigins) solverRelation)
  exact
    { executableDelta := executableDelta
      step := step
      safe := executableSafe
      success := stepSuccess
      solverRelation := solverRelation
      transition :=
        DemandTypingInferenceCompletenessOneWayTransport.StateBisimulation.oneWayCut_recordSolve
          before finalDeltaRelation declarativeAfterIdempotent
            executableAfterIdempotent rfl }

/-! ## Why mutual instances alone were insufficient

The following executable capabilities are mutual instances of the DD pair
under two collapsed, idempotent solved states.  The forward residual is
admissible, but the reverse residual is not: it maps rigid `0` to structural
`1`.  The DD match `2 ↦ 0` is legal, while the corresponding executable
match `3 ↦ 1` violates the `renameOnly` image policy.
-/

private def boundaryLedger : CapabilityOriginLedger :=
  [(0, .rigid), (1, .structuralFlexible),
    (2, .renameOnly), (3, .renameOnly)]

private def boundaryForward : CapSubst :=
  CapSubst.comp (Unification.CapSubst.single 3 (.var 2))
    (Unification.CapSubst.single 1 (.var 0))

private def boundaryReverse : CapSubst :=
  CapSubst.comp (Unification.CapSubst.single 2 (.var 3))
    (Unification.CapSubst.single 0 (.var 1))

theorem boundary_forward_admissible :
    AdmissibleCapPost boundaryLedger boundaryForward := by
  apply AdmissibleCapPost.comp
  · exact PairedUnification.admissible_single_rename
      boundaryLedger 3 2 rfl (by decide)
  · exact PairedUnification.admissible_single_structuralFlexible
      boundaryLedger 1 (.var 0) rfl

theorem boundary_components_mutual :
    (Cap.var 0).apply boundaryReverse = .var 1 ∧
    (Cap.var 1).apply boundaryForward = .var 0 ∧
    (Cap.var 2).apply boundaryReverse = .var 3 ∧
    (Cap.var 3).apply boundaryForward = .var 2 := by
  decide

theorem boundary_dd_match_admissible :
    AdmissibleCapPost boundaryLedger
      (Unification.CapSubst.single 2 (.var 0)) :=
  PairedUnification.admissible_single_rename boundaryLedger 2 0 rfl
    (by decide)

/-- `matchCap` itself is variant-covariant here, but its transported binding
is rejected by the origin ledger.  This is the exact boundary missed by the
old state invariant. -/
theorem boundary_executable_solver_rejects :
    solveProducerToSlotWithLedger boundaryLedger 0
      { phase := .expression, path := [],
        label := "one-way-transport-boundary" }
      (.var 1) .int (.var 3) .int = none := by
  rfl

end DemandTypingInferenceCompletenessOneWayTransport
end TypePM
