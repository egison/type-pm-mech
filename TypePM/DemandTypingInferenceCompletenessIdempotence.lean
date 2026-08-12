import TypePM.DemandTypingIdempotence
import TypePM.DemandTypingInferenceSoundness

/-!
# Executable prevailing solved-form preservation

The demand-directed rules already preserve `Subst.Idempotent`.  Completeness also needs the
executable replay state in solved form.  This module isolates the corresponding
state invariant and the three local solver cuts.  Recording chronology alone
is deliberately not enough: each theorem consumes the exact certificate from
the solver success equation, and capability equality additionally needs the
already-resolved capability inputs to be fixed by the incoming prevailing
substitution.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessIdempotence

open Inference

def PrevailingIdempotent (state : InferState) : Prop :=
  state.prevailing.Idempotent

theorem initialState_prevailingIdempotent
    (signature : FrozenSig) (context : Context) :
    PrevailingIdempotent (initialState signature context) := by
  exact Subst.id_idempotent

theorem PrevailingIdempotent.recordEvent
    {state : InferState} (idem : PrevailingIdempotent state)
    (event : TraceEvent) :
    PrevailingIdempotent (state.recordEvent event) := by
  simpa [PrevailingIdempotent] using idem

theorem PrevailingIdempotent.recordSource
    {state : InferState} (idem : PrevailingIdempotent state)
    (source : ProducerSource) :
    PrevailingIdempotent (state.recordSource source) := by
  simpa [PrevailingIdempotent, InferState.recordSource,
    InferState.prevailing] using idem

theorem PrevailingIdempotent.freshTy
    {state : InferState} (idem : PrevailingIdempotent state)
    (origin : ConstraintOrigin) :
    PrevailingIdempotent (state.freshTy origin).2 := by
  simpa [PrevailingIdempotent, InferState.freshTy, InferState.recordEvent,
    InferState.prevailing] using idem

theorem PrevailingIdempotent.freshCap
    {state : InferState} (idem : PrevailingIdempotent state)
    (origin : ConstraintOrigin) :
    PrevailingIdempotent (state.freshCap origin).2 := by
  simpa [PrevailingIdempotent, InferState.freshCap, InferState.recordEvent,
    InferState.prevailing] using idem

theorem PrevailingIdempotent.protectMatcherCapability
    {state : InferState} (idem : PrevailingIdempotent state)
    (capability : Cap) :
    PrevailingIdempotent (state.protectMatcherCapability capability) := by
  simpa [PrevailingIdempotent] using idem

theorem PrevailingIdempotent.freezeCapabilityExport
    {state : InferState} (idem : PrevailingIdempotent state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    PrevailingIdempotent
      (state.freezeCapabilityExport capImages exportedPayload) := by
  simpa [PrevailingIdempotent, InferState.freezeCapabilityExport,
    InferState.recordEvent, InferState.prevailing] using idem

theorem PrevailingIdempotent.instantiateSchemeInState
    {state : InferState} (idem : PrevailingIdempotent state)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (scheme : Scheme) :
    PrevailingIdempotent
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  simpa [PrevailingIdempotent, Inference.instantiateSchemeInState,
    InferState.recordEvent, InferState.prevailing] using idem

theorem PrevailingIdempotent.instantiateCtorInState
    {state : InferState} (idem : PrevailingIdempotent state)
    (scheme : CtorScheme) :
    PrevailingIdempotent (instantiateCtorInState state scheme).2 := by
  simpa [PrevailingIdempotent, Inference.instantiateCtorInState,
    InferState.recordEvent, InferState.prevailing] using idem

theorem PrevailingIdempotent.instantiateDualInState
    {state : InferState} (idem : PrevailingIdempotent state)
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (scheme : DualScheme) :
    PrevailingIdempotent
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  simpa [PrevailingIdempotent, Inference.instantiateDualInState,
    InferState.recordEvent, InferState.prevailing] using idem

private def capOnly (substitution : CapSubst) : Subst :=
  ⟨substitution, TySubst.id⟩

/-- Capability-only exact solving preserves solved form once the resolved
capability inputs are fixed at the incoming cut. -/
private theorem exactCap_seq_idempotent_of_fixed
    {S : Subst} {left right : Cap} {C : CapSubst}
    (idem : S.Idempotent) (exact : ExactCapMGU left right C)
    (leftFixed : left.apply S.cap = left)
    (rightFixed : right.apply S.cap = right) :
    (Subst.seq (capOnly C) S).Idempotent := by
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
      have mem' : varId ∈ ((S.apply target).applyCapability C).fcv := by
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

/-- One successful exact capability step preserves executable solved form.
The fixedness premises are genuinely necessary at this raw `recordSolve`
boundary; the higher alignment wrappers derive them from incoming
idempotence and their resolved-view equations. -/
theorem PrevailingIdempotent.recordCapEq
    {state : InferState} (idem : PrevailingIdempotent state)
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {left right : Cap} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin
      (.capEq left right) = some step)
    (leftFixed : left.apply state.prevailing.cap = left)
    (rightFixed : right.apply state.prevailing.cap = right) :
    PrevailingIdempotent (state.recordSolve step) := by
  have solverSuccess := success
  change solveCapEqWithLedger ledger solveCount origin left right =
    some step at solverSuccess
  have exactWithOrigin :=
    solveCapEqWithLedger_originSafeExactCapMGU solverSuccess
  rw [PrevailingIdempotent, InferState.prevailing_recordSolve]
  have deltaTarget : step.delta.target = TySubst.id := exactWithOrigin.1
  have exact := exactWithOrigin.2.exact
  have preserved := exactCap_seq_idempotent_of_fixed idem exact
    leftFixed rightFixed
  have deltaEq : step.delta = capOnly step.delta.cap := by
    cases deltaShape : step.delta with
    | mk cap target =>
        rw [deltaShape] at deltaTarget
        change target = TySubst.id at deltaTarget
        subst target
        rfl
  rwa [deltaEq]

/-- One successful exact paired target step preserves executable solved form.
The view equations state that the solver received the incoming prevailing
images, as `runConstraint`/alignment do. -/
theorem PrevailingIdempotent.recordTargetEq
    {state : InferState} (idem : PrevailingIdempotent state)
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {rawLeft rawRight left right : Ty}
    {step : SolveStep}
    (leftView : state.prevailing.apply rawLeft = left)
    (rightView : state.prevailing.apply rawRight = right)
    (success : solveResolvedWithLedger ledger solveCount origin
      (.targetEq left right) = some step) :
    PrevailingIdempotent (state.recordSolve step) := by
  have solverSuccess := success
  change solveTargetEqWithLedger ledger solveCount origin left right =
    some step at solverSuccess
  have exactWithOrigin :=
    solveTargetEqWithLedger_originSafeExactPairedMGU solverSuccess
  have exactResolved : ExactPairedMGU
      (state.prevailing.apply rawLeft)
      (state.prevailing.apply rawRight) step.delta := by
    simpa only [leftView, rightView] using exactWithOrigin.exact
  rw [PrevailingIdempotent, InferState.prevailing_recordSolve]
  exact exactResolved.seq_idempotent idem

/-- One successful producer-to-slot step preserves executable solved form.
Using the public demand-directed idempotence theorem avoids duplicating the two-phase
capability-match/target-unification argument. -/
theorem PrevailingIdempotent.recordProducerToSlot
    {state : InferState} (idem : PrevailingIdempotent state)
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {raw expected : Ty}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {step : SolveStep}
    (rawView : state.prevailing.apply raw =
      .matcher producerCap producerTarget)
    (expectedView : state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : solveResolvedWithLedger ledger solveCount origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) =
        some step) :
    PrevailingIdempotent (state.recordSolve step) := by
  have oneWay :=
    (solveResolvedWithLedger_originSafeOneWayDelta success).exact
  have aligned : DemandAlign state.prevailing raw expected
      (Subst.seq step.delta state.prevailing) :=
    DemandAlign.matcherToSlot rawView expectedView oneWay
  rw [PrevailingIdempotent, InferState.prevailing_recordSolve]
  exact DemandTypingIdempotence.DemandAlign.idempotent aligned idem

/-- Any reconstructed executable alignment run transports the invariant in
one step; branch-specific solver details have already been packaged by the
soundness-side run certificate. -/
theorem PrevailingIdempotent.of_ddAlignRun
    {initial final : InferState} (idem : PrevailingIdempotent initial)
    {raw expected : Ty} (run : DemandAlignRun raw expected initial final) :
    PrevailingIdempotent final := by
  rcases run with ⟨_, _, aligned⟩
  exact DemandTypingIdempotence.DemandAlign.idempotent aligned.erase idem

theorem PrevailingIdempotent.of_ddAlignTypesRun
    {initial final : InferState} (idem : PrevailingIdempotent initial)
    {left right : Ty} (run : DemandAlignTypesRun left right initial final) :
    PrevailingIdempotent final := by
  rcases run with ⟨_, _, aligned⟩
  exact DemandTypingIdempotence.DemandAlignTypes.idempotent aligned.erase idem

end DemandTypingInferenceCompletenessIdempotence
end TypePM
