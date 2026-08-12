import TypePM.DemandTypingInferenceCompletenessState
import TypePM.DemandTypingInferenceSoundness

/-!
# Mutual prevailing-state correspondence

One-sided factorization is enough to show that every declarative solve is a
competitor of the executable solver.  Coercion selection also needs the
converse direction: substitutions cannot erase an already visible outer type
constructor, so mutually-instantiating states expose the same matcher/slot
skeleton.  This module packages that stronger invariant and proves that an
ordinary paired cut preserves it without choosing a canonical MGU
orientation.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessStateMutual

open Inference
open DemandTypingInferenceCompletenessState

/-- The DD and executable prevailing substitutions mutually factor through
one another.  The forward residual remains origin-admissible because it is
the direction subsequently used as an executable solver competitor. -/
def MutualStateCorrespondence (ledger : CapabilityOriginLedger)
    (declarative : Subst) (executable : InferState) : Prop :=
  StateCorrespondence ledger declarative executable ∧
    ∃ reverseResidual,
      executable.prevailing = Subst.seq reverseResidual declarative

/-- Proof-relevant form used by the completeness recursion.  Keeping the two
residuals as data lets every synthesized output type refer to the same
factorization witnesses; two unrelated existential choices would be too weak
for a subsequent paired cut. -/
structure StateBisimulation (ledger : CapabilityOriginLedger)
    (declarative : Subst) (executable : InferState) : Type where
  forward : Subst
  forwardEquation :
    declarative = Subst.seq forward executable.prevailing
  forwardAdmissible : AdmissiblePost ledger forward
  reverse : Subst
  reverseEquation :
    executable.prevailing = Subst.seq reverse declarative

/-- One DD raw target and one executable raw target correspond under the
fixed residuals of a state bisimulation. -/
structure TyBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    (state : StateBisimulation ledger declarative executable)
    (declarativeTarget executableTarget : Ty) : Prop where
  forward :
    declarative.apply declarativeTarget =
      state.forward.apply (executable.prevailing.apply executableTarget)
  reverse :
    executable.prevailing.apply executableTarget =
      state.reverse.apply (declarative.apply declarativeTarget)

/-- Pointwise list form sharing one pair of state residuals. -/
inductive TyListBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    (state : StateBisimulation ledger declarative executable) :
    List Ty → List Ty → Prop where
  | nil : TyListBisimulation state [] []
  | cons (head : TyBisimulation state declarativeTarget executableTarget)
      (tail : TyListBisimulation state declarativeTargets executableTargets) :
      TyListBisimulation state (declarativeTarget :: declarativeTargets)
        (executableTarget :: executableTargets)

/-- A chronological DD/executable transition together with transport of every
type pair already related at its input. -/
structure BisimulationExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    (before : StateBisimulation ledger declarative executable)
    (ledger' : CapabilityOriginLedger) (declarative' : Subst)
    (executable' : InferState) : Type where
  after : StateBisimulation ledger' declarative' executable'
  transportTy : ∀ {declarativeTarget executableTarget},
    TyBisimulation before declarativeTarget executableTarget →
      TyBisimulation after declarativeTarget executableTarget

/-- Identity transition. -/
def BisimulationExtension.refl
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    BisimulationExtension relation ledger declarative state where
  after := relation
  transportTy := fun related => related

/-- Chronological extensions compose and retain transport of tracked types. -/
def BisimulationExtension.seq
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ : Subst}
    {state₀ state₁ state₂ : InferState}
    {before : StateBisimulation ledger₀ declarative₀ state₀}
    (first : BisimulationExtension before ledger₁ declarative₁ state₁)
    (second : BisimulationExtension first.after ledger₂ declarative₂
      state₂) :
    BisimulationExtension before ledger₂ declarative₂ state₂ where
  after := second.after
  transportTy := fun related => second.transportTy (first.transportTy related)

/-- Pointwise transport for a previously tracked target list. -/
theorem BisimulationExtension.transportTyList
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeTargets executableTargets : List Ty}
    (related : TyListBisimulation before declarativeTargets executableTargets) :
    TyListBisimulation extension.after declarativeTargets executableTargets := by
  induction related with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (extension.transportTy head) induction

/-- Forget the proof-relevant witnesses when only branch invariance is
needed. -/
theorem StateBisimulation.toMutual
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    MutualStateCorrespondence ledger declarative state :=
  ⟨⟨relation.forward, relation.forwardEquation,
      relation.forwardAdmissible⟩,
    relation.reverse, relation.reverseEquation⟩

/-- Proof-relevant initial correspondence. -/
def StateBisimulation.refl
    (ledger : CapabilityOriginLedger) (state : InferState) :
    StateBisimulation ledger state.prevailing state where
  forward := Subst.id
  forwardEquation := by
    apply PhasedPost.subst_ext
    · funext varId
      exact (Cap.apply_id (state.prevailing.cap varId)).symm
    · funext varId
      change state.prevailing.target varId =
        Subst.id.apply (state.prevailing.target varId)
      rw [Subst.apply_id]
  forwardAdmissible := AdmissiblePost.id ledger
  reverse := Subst.id
  reverseEquation := by
    apply PhasedPost.subst_ext
    · funext varId
      exact (Cap.apply_id (state.prevailing.cap varId)).symm
    · funext varId
      change state.prevailing.target varId =
        Subst.id.apply (state.prevailing.target varId)
      rw [Subst.apply_id]

/-- The same raw target is related by every state bisimulation. -/
theorem StateBisimulation.sameTarget
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (target : Ty) : TyBisimulation relation target target := by
  constructor
  · have pointwise := congrArg (fun S : Subst => S.apply target)
      relation.forwardEquation
    simpa only [Subst.seq_apply] using pointwise
  · have pointwise := congrArg (fun S : Subst => S.apply target)
      relation.reverseEquation
    simpa only [Subst.seq_apply] using pointwise

/-- Events preserve the proof-relevant state relation. -/
def StateBisimulation.recordEvent
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (event : TraceEvent) :
    StateBisimulation ledger declarative (state.recordEvent event) where
  forward := relation.forward
  forwardEquation := by simpa using relation.forwardEquation
  forwardAdmissible := relation.forwardAdmissible
  reverse := relation.reverse
  reverseEquation := by simpa using relation.reverseEquation

/-- Event-only transition as a reusable chronological extension. -/
def StateBisimulation.recordEventExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (event : TraceEvent) :
    BisimulationExtension relation ledger declarative
      (state.recordEvent event) where
  after := relation.recordEvent event
  transportTy := by
    intro declarativeTarget executableTarget related
    constructor
    · change declarative.apply declarativeTarget =
        relation.forward.apply (state.prevailing.apply executableTarget)
      exact related.forward
    · change state.prevailing.apply executableTarget =
        relation.reverse.apply (declarative.apply declarativeTarget)
      exact related.reverse

/-- General paired cut where the DD and executable operands may have
different raw metavariable names but share the current state residuals. -/
noncomputable def StateBisimulation.pairedCut_recordSolve
    {ledger : CapabilityOriginLedger} {declarative delta : Subst}
    {state : InferState} {declarativeLeft declarativeRight : Ty}
    {executableLeft executableRight : Ty} {step : SolveStep}
    (relation : StateBisimulation ledger declarative state)
    (left : TyBisimulation relation declarativeLeft executableLeft)
    (right : TyBisimulation relation declarativeRight executableRight)
    (dd : OriginSafeExactPairedMGU ledger
      (declarative.apply declarativeLeft)
      (declarative.apply declarativeRight) delta)
    (result : PairedUnification.PairedResult ledger
      (state.prevailing.apply executableLeft)
      (state.prevailing.apply executableRight))
    (stepDelta : step.delta = result.subst) :
    BisimulationExtension relation ledger (Subst.seq delta declarative)
      (state.recordSolve step) := by
  let combined := Subst.seq delta relation.forward
  have combinedAdmissible : AdmissiblePost ledger combined :=
    AdmissiblePost.seq dd.admissible relation.forwardAdmissible
  have combinedSound :
      combined.apply (state.prevailing.apply executableLeft) =
        combined.apply (state.prevailing.apply executableRight) := by
    simp only [combined, Subst.seq_apply, ← left.forward, ← right.forward]
    exact dd.exact.1.1
  have forwardAbsorbs : combined = Subst.seq combined result.subst :=
    result.universal combined combinedAdmissible combinedSound
  let reverseCompetitor := Subst.seq result.subst relation.reverse
  have reverseSound :
      reverseCompetitor.apply (declarative.apply declarativeLeft) =
        reverseCompetitor.apply (declarative.apply declarativeRight) := by
    simp only [reverseCompetitor, Subst.seq_apply, ← left.reverse,
      ← right.reverse]
    exact result.sound
  let reverseWitness := dd.exact.1.2 reverseCompetitor reverseSound
  let reverseAfter := Classical.choose reverseWitness
  have reverseFactors :
      reverseCompetitor = Subst.seq reverseAfter delta :=
    Classical.choose_spec reverseWitness
  let after : StateBisimulation ledger (Subst.seq delta declarative)
      (state.recordSolve step) :=
    { forward := combined
      forwardEquation := by
        rw [InferState.prevailing_recordSolve, stepDelta,
          relation.forwardEquation]
        calc
          Subst.seq delta
              (Subst.seq relation.forward state.prevailing) =
              Subst.seq combined state.prevailing :=
            PhasedPost.seq_assoc delta relation.forward state.prevailing
          _ = Subst.seq (Subst.seq combined result.subst)
              state.prevailing := by rw [← forwardAbsorbs]
          _ = Subst.seq combined
              (Subst.seq result.subst state.prevailing) :=
            (PhasedPost.seq_assoc combined result.subst state.prevailing).symm
      forwardAdmissible := combinedAdmissible
      reverse := reverseAfter
      reverseEquation := by
        rw [InferState.prevailing_recordSolve, stepDelta]
        calc
          Subst.seq result.subst state.prevailing =
              Subst.seq result.subst
                (Subst.seq relation.reverse declarative) := by
            exact congrArg (Subst.seq result.subst) relation.reverseEquation
          _ = Subst.seq reverseCompetitor declarative :=
            PhasedPost.seq_assoc result.subst relation.reverse declarative
          _ = Subst.seq (Subst.seq reverseAfter delta) declarative := by
            rw [← reverseFactors]
          _ = Subst.seq reverseAfter (Subst.seq delta declarative) :=
            (PhasedPost.seq_assoc reverseAfter delta declarative).symm }
  refine
    { after := after
      transportTy := ?_ }
  intro trackedDeclarative trackedExecutable tracked
  constructor
  · rw [InferState.prevailing_recordSolve, stepDelta]
    change (Subst.seq delta declarative).apply trackedDeclarative =
      combined.apply
        ((Subst.seq result.subst state.prevailing).apply trackedExecutable)
    calc
      (Subst.seq delta declarative).apply trackedDeclarative =
          combined.apply (state.prevailing.apply trackedExecutable) := by
        simp only [Subst.seq_apply, combined, tracked.forward]
      _ = (Subst.seq combined result.subst).apply
          (state.prevailing.apply trackedExecutable) := by
        rw [← forwardAbsorbs]
      _ = combined.apply
          (result.subst.apply
            (state.prevailing.apply trackedExecutable)) :=
        Subst.seq_apply combined result.subst _
      _ = combined.apply
          ((Subst.seq result.subst state.prevailing).apply
            trackedExecutable) := by
        exact congrArg combined.apply
          (Subst.seq_apply result.subst state.prevailing
            trackedExecutable).symm
  · rw [InferState.prevailing_recordSolve, stepDelta]
    change (Subst.seq result.subst state.prevailing).apply
        trackedExecutable =
      reverseAfter.apply
        ((Subst.seq delta declarative).apply trackedDeclarative)
    calc
      (Subst.seq result.subst state.prevailing).apply trackedExecutable =
          result.subst.apply (state.prevailing.apply trackedExecutable) :=
        Subst.seq_apply result.subst state.prevailing _
      _ =
          reverseCompetitor.apply
            (declarative.apply trackedDeclarative) := by
        simp only [reverseCompetitor, Subst.seq_apply, tracked.reverse]
      _ = (Subst.seq reverseAfter delta).apply
          (declarative.apply trackedDeclarative) := by
        rw [← reverseFactors]
      _ = reverseAfter.apply
          ((Subst.seq delta declarative).apply trackedDeclarative) := by
        simp only [Subst.seq_apply]

/-- Initially the two prevailing states coincide. -/
theorem MutualStateCorrespondence.refl
    (ledger : CapabilityOriginLedger) (state : InferState) :
    MutualStateCorrespondence ledger state.prevailing state := by
  refine ⟨StateCorrespondence.refl ledger state, Subst.id, ?_⟩
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (state.prevailing.cap varId)).symm
  · funext varId
    change state.prevailing.target varId =
      Subst.id.apply (state.prevailing.target varId)
    rw [Subst.apply_id]

/-- Reconstruction events do not affect either direction. -/
theorem MutualStateCorrespondence.recordEvent
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (event : TraceEvent) :
    MutualStateCorrespondence ledger declarative
      (state.recordEvent event) := by
  rcases relation with ⟨forward, reverseResidual, reverseEquation⟩
  exact ⟨forward.recordEvent event, reverseResidual,
    by simpa using reverseEquation⟩

/-- The executable paired result, transported through the incoming reverse
residual, is a solution of the DD-side constraint. -/
theorem pairedReverseCompetitorSound
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {left right : Ty} {reverseResidual : Subst}
    (reverseEquation :
      state.prevailing = Subst.seq reverseResidual declarative)
    (result : PairedUnification.PairedResult ledger
      (state.prevailing.apply left) (state.prevailing.apply right)) :
    (Subst.seq result.subst reverseResidual).apply
        (declarative.apply left) =
      (Subst.seq result.subst reverseResidual).apply
        (declarative.apply right) := by
  rw [Subst.seq_apply, Subst.seq_apply]
  have leftTransport := congrArg (fun S : Subst => S.apply left)
    reverseEquation
  have rightTransport := congrArg (fun S : Subst => S.apply right)
    reverseEquation
  simp only [Subst.seq_apply] at leftTransport rightTransport
  rw [← leftTransport, ← rightTransport]
  exact result.sound

/-- An ordinary paired DD cut and the corresponding executable solver cut
preserve mutual factorization. -/
theorem MutualStateCorrespondence.pairedCut_recordSolve
    {ledger : CapabilityOriginLedger} {declarative delta : Subst}
    {state : InferState} {left right : Ty} {step : SolveStep}
    (relation : MutualStateCorrespondence ledger declarative state)
    (dd : OriginSafeExactPairedMGU ledger
      (declarative.apply left) (declarative.apply right) delta)
    (result : PairedUnification.PairedResult ledger
      (state.prevailing.apply left) (state.prevailing.apply right))
    (stepDelta : step.delta = result.subst) :
    MutualStateCorrespondence ledger (Subst.seq delta declarative)
      (state.recordSolve step) := by
  rcases relation with ⟨forwardBefore, reverseBefore, reverseEquation⟩
  have forward :=
    DemandTypingInferenceCompletenessState.pairedCut_recordSolve
      forwardBefore dd result stepDelta
  let competitor := Subst.seq result.subst reverseBefore
  have competitorSound :
      competitor.apply (declarative.apply left) =
        competitor.apply (declarative.apply right) :=
    pairedReverseCompetitorSound reverseEquation result
  rcases dd.exact.1.2 competitor competitorSound with
    ⟨reverseAfter, competitorFactors⟩
  refine ⟨forward, reverseAfter, ?_⟩
  rw [InferState.prevailing_recordSolve, stepDelta]
  calc
    Subst.seq result.subst state.prevailing =
        Subst.seq result.subst
          (Subst.seq reverseBefore declarative) := by
      exact congrArg (Subst.seq result.subst) reverseEquation
    _ = Subst.seq competitor declarative :=
      PhasedPost.seq_assoc result.subst reverseBefore declarative
    _ = Subst.seq (Subst.seq reverseAfter delta) declarative := by
      rw [← competitorFactors]
    _ = Subst.seq reverseAfter (Subst.seq delta declarative) :=
      (PhasedPost.seq_assoc reverseAfter delta declarative).symm

/-! ## Coercion-selector views -/

/-- Mutual instances either both expose a product-of-matchers view or both
fail to expose one.  The component duals may differ by the residual
substitutions; branch selection depends only on success of the view. -/
theorem productMatcherView_iff_of_mutualInstances
    {declarative executable : Ty} {forward reverse : Subst}
    (forwardEq : declarative = forward.apply executable)
    (reverseEq : executable = reverse.apply declarative) :
    (∃ duals, Inference.productMatcherDuals? declarative = some duals) ↔
      ∃ duals, Inference.productMatcherDuals? executable = some duals := by
  constructor
  · rintro ⟨duals, view⟩
    refine ⟨duals.map (Dual.applySubst reverse), ?_⟩
    rw [reverseEq]
    exact Inference.productMatcherDuals?_apply view
  · rintro ⟨duals, view⟩
    refine ⟨duals.map (Dual.applySubst forward), ?_⟩
    rw [forwardEq]
    exact Inference.productMatcherDuals?_apply view

/-- Slot-product recognition has the same mutual-instance invariance. -/
theorem productSlotView_iff_of_mutualInstances
    {declarative executable : Ty} {forward reverse : Subst}
    (forwardEq : declarative = forward.apply executable)
    (reverseEq : executable = reverse.apply declarative) :
    (∃ duals, Inference.productSlotDuals? declarative = some duals) ↔
      ∃ duals, Inference.productSlotDuals? executable = some duals := by
  constructor
  · rintro ⟨duals, view⟩
    refine ⟨duals.map (Dual.applySubst reverse), ?_⟩
    rw [reverseEq]
    exact Inference.productSlotDuals?_apply view
  · rintro ⟨duals, view⟩
    refine ⟨duals.map (Dual.applySubst forward), ?_⟩
    rw [forwardEq]
    exact Inference.productSlotDuals?_apply view

/-- A slot head cannot be created in only one direction of a pair of mutual
instances. -/
theorem slotHead_iff_of_mutualInstances
    {declarative executable : Ty} {forward reverse : Subst}
    (forwardEq : declarative = forward.apply executable)
    (reverseEq : executable = reverse.apply declarative) :
    (∃ capability target, declarative = .slot capability target) ↔
      ∃ capability target, executable = .slot capability target := by
  constructor
  · rintro ⟨capability, target, rfl⟩
    refine ⟨capability.apply reverse.cap, reverse.apply target, ?_⟩
    simpa only [Subst.apply_slot] using reverseEq
  · rintro ⟨capability, target, rfl⟩
    refine ⟨capability.apply forward.cap, forward.apply target, ?_⟩
    simpa only [Subst.apply_slot] using forwardEq

/-- A matcher head is likewise invariant under mutual instantiation. -/
theorem matcherHead_iff_of_mutualInstances
    {declarative executable : Ty} {forward reverse : Subst}
    (forwardEq : declarative = forward.apply executable)
    (reverseEq : executable = reverse.apply declarative) :
    (∃ capability target, declarative = .matcher capability target) ↔
      ∃ capability target, executable = .matcher capability target := by
  constructor
  · rintro ⟨capability, target, rfl⟩
    refine ⟨capability.apply reverse.cap, reverse.apply target, ?_⟩
    simpa only [Subst.apply_matcher] using reverseEq
  · rintro ⟨capability, target, rfl⟩
    refine ⟨capability.apply forward.cap, forward.apply target, ?_⟩
    simpa only [Subst.apply_matcher] using forwardEq

/-- Pointwise mutual-instance equations exposed from the state invariant. -/
theorem MutualStateCorrespondence.apply_equations
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (target : Ty) :
    ∃ (forward reverse : Subst),
      declarative.apply target =
          forward.apply (state.prevailing.apply target) ∧
        state.prevailing.apply target =
          reverse.apply (declarative.apply target) := by
  rcases relation with
    ⟨⟨forward, forwardEquation, _forwardAdmissible⟩,
      reverse, reverseEquation⟩
  refine ⟨forward, reverse, ?_, ?_⟩
  · rw [forwardEquation, Subst.seq_apply]
  · rw [reverseEquation, Subst.seq_apply]

/-- Product-matcher recognition agrees at corresponding DD and executable
cuts. -/
theorem MutualStateCorrespondence.productMatcherView_iff
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (target : Ty) :
    (∃ duals,
      Inference.productMatcherDuals? (declarative.apply target) = some duals) ↔
    ∃ duals,
      Inference.productMatcherDuals? (state.prevailing.apply target) =
        some duals := by
  rcases relation.apply_equations target with
    ⟨forward, reverse, forwardEq, reverseEq⟩
  exact productMatcherView_iff_of_mutualInstances forwardEq reverseEq

/-- Product-slot recognition agrees at corresponding cuts. -/
theorem MutualStateCorrespondence.productSlotView_iff
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (target : Ty) :
    (∃ duals,
      Inference.productSlotDuals? (declarative.apply target) = some duals) ↔
    ∃ duals,
      Inference.productSlotDuals? (state.prevailing.apply target) =
        some duals := by
  rcases relation.apply_equations target with
    ⟨forward, reverse, forwardEq, reverseEq⟩
  exact productSlotView_iff_of_mutualInstances forwardEq reverseEq

/-- Slot-headedness agrees at corresponding cuts. -/
theorem MutualStateCorrespondence.slotHead_iff
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (target : Ty) :
    (∃ capability body,
      declarative.apply target = .slot capability body) ↔
    ∃ capability body,
      state.prevailing.apply target = .slot capability body := by
  rcases relation.apply_equations target with
    ⟨forward, reverse, forwardEq, reverseEq⟩
  exact slotHead_iff_of_mutualInstances forwardEq reverseEq

/-- Matcher-headedness agrees at corresponding cuts. -/
theorem MutualStateCorrespondence.matcherHead_iff
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : MutualStateCorrespondence ledger declarative state)
    (target : Ty) :
    (∃ capability body,
      declarative.apply target = .matcher capability body) ↔
    ∃ capability body,
      state.prevailing.apply target = .matcher capability body := by
  rcases relation.apply_equations target with
    ⟨forward, reverse, forwardEq, reverseEq⟩
  exact matcherHead_iff_of_mutualInstances forwardEq reverseEq

end DemandTypingInferenceCompletenessStateMutual
end TypePM
