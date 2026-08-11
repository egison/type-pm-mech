import TypePM.DemandTypingOrigin
import TypePM.InferenceLedgerAdmissibility

/-!
# Executable traversal to demand-directed typing

This module starts the direct soundness proof from successful executable
traversals to the public demand-directed judgment.  The intermediate
`DDSynthRun` certificate deliberately retains only the pieces of `InferState`
that occur in `DDSynth` and `DDSynthOrigin`: the fresh supply, prevailing
substitution, and capability-origin ledger.  Trace events remain evidence for
constructing the certificate, rather than becoming an additional premise of
source typing.

The initial slices cover variable lookup, lambda, tuple, the two expression
leaves whose executable traversal performs no solve, and expression-list
nil/cons.  Their shape is the mutual induction invariant required by the
remaining expression constructors: executable raw targets are preserved, and
the output indices of the DD derivation are exactly the output state of the
run.
-/

namespace TypePM
namespace Inference

@[simp] theorem InferState.recordEvent_supply
    (state : InferState) (event : TraceEvent) :
    (state.recordEvent event).supply = state.supply :=
  rfl

@[simp] theorem InferState.recordEvent_capabilityOrigins
    (state : InferState) (event : TraceEvent) :
    (state.recordEvent event).capabilityOrigins = state.capabilityOrigins :=
  rfl

@[simp] theorem InferState.recordSource_supply
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).supply = state.supply :=
  rfl

@[simp] theorem InferState.recordSource_prevailing
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).prevailing = state.prevailing :=
  rfl

@[simp] theorem InferState.recordSource_capabilityOrigins
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).capabilityOrigins =
      state.capabilityOrigins :=
  rfl

@[simp] theorem instantiateSchemeInState_prevailing
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.prevailing = state.prevailing :=
  rfl

@[simp] theorem instantiateSchemeInState_target
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).1 = (InferenceBase.instantiateScheme state.supply scheme).value :=
  rfl

@[simp] theorem instantiateSchemeInState_supply
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.supply =
        (InferenceBase.instantiateScheme state.supply scheme).supply :=
  rfl

@[simp] theorem instantiateSchemeInState_capabilityOrigins
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.capabilityOrigins =
        state.capabilityOrigins.setOrigins
          (freshCapImages state.supply scheme.capBinders) .renameOnly :=
  rfl

/-- The DD certificate reconstructed from one successful executable
expression traversal.  This is an internal induction package for proving
`infer` sound with respect to `DDTyping`; it is not a second typing judgment. -/
def DDSynthRun (signature : FrozenSig) (context : Context)
    (expression : Expr) (initial : InferState) (result : ExprResult) : Prop :=
  ∃ rawTarget,
    ∃ derived : DDSynth signature initial.supply initial.prevailing context
        expression rawTarget result.state.supply result.state.prevailing,
      result.target = rawTarget ∧
        DDSynthOrigin signature derived initial.capabilityOrigins
          result.state.capabilityOrigins

/-- List form of `DDSynthRun`, retaining the executable raw target list and
the exact terminal state indices. -/
def DDSynthsRun (signature : FrozenSig) (context : Context)
    (expressions : List Expr) (initial : InferState)
    (result : ExprsResult) : Prop :=
  ∃ rawTargets,
    ∃ derived : DDSynths signature initial.supply initial.prevailing context
        expressions rawTargets result.state.supply result.state.prevailing,
      result.targets = rawTargets ∧
        DDSynthsOrigin signature derived initial.capabilityOrigins
          result.state.capabilityOrigins

/-- Exact-state certificate for one checking traversal. -/
def DDCheckRun (signature : FrozenSig) (context : Context)
    (expression : Expr) (expected : Ty) (initial final : InferState) : Prop :=
  ∃ derived : DDCheck signature initial.supply initial.prevailing context
      expression expected final.supply final.prevailing,
    DDCheckOrigin signature derived initial.capabilityOrigins
      final.capabilityOrigins

/-- State-indexed declarative image of an executable expected-type alignment.
Alignment never allocates variables or changes the origin ledger; only its
prevailing substitution advances. -/
def DDAlignRun (raw expected : Ty) (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignWithLedger initial.capabilityOrigins initial.prevailing raw
        expected final.prevailing

/-- Exact-state certificate for one executable ordinary type alignment.
Alignment preserves the fresh supply and origin ledger while advancing the
prevailing substitution by the declarative ledger-aware equality rule. -/
def DDAlignTypesRun (left right : Ty) (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignTypesWithLedger initial.capabilityOrigins initial.prevailing
        left right final.prevailing

/-- Dispatching a capability equality through the common resolved solver
retains the exact origin-safe capability MGU carried by its result. -/
theorem solveResolvedWithLedger_capEq_originSafeExactCapMGU
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {left right : Cap} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin
      (.capEq left right) = some step) :
    step.delta.target = TySubst.id ∧
      OriginSafeExactCapMGU ledger left right step.delta.cap := by
  exact solveCapEqWithLedger_originSafeExactCapMGU success

/-- Dispatching a target equality through the common resolved solver retains
the exact origin-safe paired MGU carried by its result. -/
theorem solveResolvedWithLedger_targetEq_originSafeExactPairedMGU
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {left right : Ty} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin
      (.targetEq left right) = some step) :
    OriginSafeExactPairedMGU ledger left right step.delta := by
  exact solveTargetEqWithLedger_originSafeExactPairedMGU success

/-- Eliminate one capability-equality run while retaining its exact solver
step and the precise recorded terminal state. -/
private theorem runResolvedConstraint_capEq_exact
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Cap}
    (success : runResolvedConstraint state origin (.capEq left right) =
      some final) :
    ∃ step,
      solveResolvedWithLedger state.capabilityOrigins
        state.trace.solves.length origin (.capEq left right) = some step ∧
      final = state.recordSolve step ∧
      step.delta.target = TySubst.id ∧
      OriginSafeExactCapMGU state.capabilityOrigins left right
        step.delta.cap := by
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin (.capEq left right) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      have finalEq := Option.some.inj success
      subst final
      rcases solveResolvedWithLedger_capEq_originSafeExactCapMGU stepEq with
        ⟨targetId, exactCap⟩
      exact ⟨step, rfl, rfl, targetId, exactCap⟩

/-- Eliminate one target-equality run while retaining its exact solver step
and the precise recorded terminal state. -/
private theorem runResolvedConstraint_targetEq_exact
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (success : runResolvedConstraint state origin (.targetEq left right) =
      some final) :
    ∃ step,
      solveResolvedWithLedger state.capabilityOrigins
        state.trace.solves.length origin (.targetEq left right) = some step ∧
      final = state.recordSolve step ∧
      OriginSafeExactPairedMGU state.capabilityOrigins left right
        step.delta := by
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin (.targetEq left right) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      have finalEq := Option.some.inj success
      subst final
      exact ⟨step, rfl, rfl,
        solveResolvedWithLedger_targetEq_originSafeExactPairedMGU stepEq⟩

/-- Reconstruct the one-step ordinary branch of executable type alignment.
The two annotated homogeneous branches are intentionally excluded here; each
of those performs a capability solve before its target solve. -/
theorem alignTypesCore_ordinary_ddAlignTypesRun
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (pairClass : alignPairClass (state.prevailing.apply left)
      (state.prevailing.apply right) = .ordinary)
    (success : alignTypesCore state origin left right = some final) :
    DDAlignTypesRun left right state final := by
  unfold alignTypesCore at success
  simp only at success
  split at success
  · simp_all [alignPairClass]
  · simp_all [alignPairClass]
  · unfold runResolvedConstraint at success
    cases stepEq : solveResolvedWithLedger state.capabilityOrigins
        state.trace.solves.length origin
        (.targetEq (state.prevailing.apply left)
          (state.prevailing.apply right)) with
    | none => simp [stepEq] at success
    | some step =>
        simp only [stepEq] at success
        have finalEq := Option.some.inj success
        subst final
        refine ⟨rfl, rfl, ?_⟩
        rw [InferState.prevailing_recordSolve]
        exact DDAlignTypesWithLedger.ordinary pairClass
          (solveResolvedWithLedger_targetEq_originSafeExactPairedMGU stepEq)

/-- Reconstruct the two-step matcher/matcher branch: first solve its
capability annotations, then solve the capability-adjusted target pair. -/
theorem alignTypesCore_matcherPair_ddAlignTypesRun
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty} {leftCap rightCap : Cap}
    {leftTarget rightTarget : Ty}
    (leftView : state.prevailing.apply left =
      .matcher leftCap leftTarget)
    (rightView : state.prevailing.apply right =
      .matcher rightCap rightTarget)
    (success : alignTypesCore state origin left right = some final) :
    DDAlignTypesRun left right state final := by
  unfold alignTypesCore at success
  simp only [leftView, rightView] at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, targetBranchSuccess⟩
  rcases runResolvedConstraint_capEq_exact capSuccess with
    ⟨capStep, _, middleEq, capTargetId, exactCap⟩
  subst middle
  split at targetBranchSuccess <;> try contradiction
  · rename_i afterLeft afterRight ignoredLeftCap adjustedLeftTarget
      ignoredRightCap adjustedRightTarget afterLeftView afterRightView
    rcases runResolvedConstraint_targetEq_exact targetBranchSuccess with
      ⟨targetStep, _, finalEq, exactTarget⟩
    subst final
    have capDeltaEq : capStep.delta =
        ⟨capStep.delta.cap, TySubst.id⟩ := by
      rw [← capTargetId]
    have adjustedLeftEq :
        adjustedLeftTarget = leftTarget.applyCapability capStep.delta.cap := by
      have applied :
          (state.recordSolve capStep).prevailing.apply left =
            capStep.delta.apply (state.prevailing.apply left) := by
        rw [InferState.prevailing_recordSolve, Subst.seq_apply]
      rw [leftView, afterLeftView] at applied
      simp only [Subst.apply, Ty.applyCapability, capTargetId,
        Ty.applyTarget_id] at applied
      exact Ty.matcher.inj applied |>.2
    have adjustedRightEq :
        adjustedRightTarget = rightTarget.applyCapability capStep.delta.cap := by
      have applied :
          (state.recordSolve capStep).prevailing.apply right =
            capStep.delta.apply (state.prevailing.apply right) := by
        rw [InferState.prevailing_recordSolve, Subst.seq_apply]
      rw [rightView, afterRightView] at applied
      simp only [Subst.apply, Ty.applyCapability, capTargetId,
        Ty.applyTarget_id] at applied
      exact Ty.matcher.inj applied |>.2
    refine ⟨rfl, rfl, ?_⟩
    rw [InferState.prevailing_recordSolve,
      InferState.prevailing_recordSolve, capDeltaEq]
    exact DDAlignTypesWithLedger.matcherPair leftView rightView exactCap
      (adjustedLeftEq ▸ adjustedRightEq ▸ exactTarget)
  · rename_i afterLeft afterRight ignoredLeftCap adjustedLeftTarget
      ignoredRightCap adjustedRightTarget afterLeftView afterRightView
    have applied :
        (state.recordSolve capStep).prevailing.apply left =
          capStep.delta.apply (state.prevailing.apply left) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [leftView, afterLeftView] at applied
    simp [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied

/-- Reconstruct the two-step slot/slot branch: first solve its capability
annotations, then solve the capability-adjusted target pair. -/
theorem alignTypesCore_slotPair_ddAlignTypesRun
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty} {leftCap rightCap : Cap}
    {leftTarget rightTarget : Ty}
    (leftView : state.prevailing.apply left = .slot leftCap leftTarget)
    (rightView : state.prevailing.apply right = .slot rightCap rightTarget)
    (success : alignTypesCore state origin left right = some final) :
    DDAlignTypesRun left right state final := by
  unfold alignTypesCore at success
  simp only [leftView, rightView] at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, targetBranchSuccess⟩
  rcases runResolvedConstraint_capEq_exact capSuccess with
    ⟨capStep, _, middleEq, capTargetId, exactCap⟩
  subst middle
  split at targetBranchSuccess <;> try contradiction
  · rename_i afterLeft afterRight ignoredLeftCap adjustedLeftTarget
      ignoredRightCap adjustedRightTarget afterLeftView afterRightView
    have applied :
        (state.recordSolve capStep).prevailing.apply left =
          capStep.delta.apply (state.prevailing.apply left) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [leftView, afterLeftView] at applied
    simp [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied
  · rename_i afterLeft afterRight ignoredLeftCap adjustedLeftTarget
      ignoredRightCap adjustedRightTarget afterLeftView afterRightView
    rcases runResolvedConstraint_targetEq_exact targetBranchSuccess with
      ⟨targetStep, _, finalEq, exactTarget⟩
    subst final
    have capDeltaEq : capStep.delta =
        ⟨capStep.delta.cap, TySubst.id⟩ := by
      rw [← capTargetId]
    have adjustedLeftEq :
        adjustedLeftTarget = leftTarget.applyCapability capStep.delta.cap := by
      have applied :
          (state.recordSolve capStep).prevailing.apply left =
            capStep.delta.apply (state.prevailing.apply left) := by
        rw [InferState.prevailing_recordSolve, Subst.seq_apply]
      rw [leftView, afterLeftView] at applied
      simp only [Subst.apply, Ty.applyCapability, capTargetId,
        Ty.applyTarget_id] at applied
      exact Ty.slot.inj applied |>.2
    have adjustedRightEq :
        adjustedRightTarget = rightTarget.applyCapability capStep.delta.cap := by
      have applied :
          (state.recordSolve capStep).prevailing.apply right =
            capStep.delta.apply (state.prevailing.apply right) := by
        rw [InferState.prevailing_recordSolve, Subst.seq_apply]
      rw [rightView, afterRightView] at applied
      simp only [Subst.apply, Ty.applyCapability, capTargetId,
        Ty.applyTarget_id] at applied
      exact Ty.slot.inj applied |>.2
    refine ⟨rfl, rfl, ?_⟩
    rw [InferState.prevailing_recordSolve,
      InferState.prevailing_recordSolve, capDeltaEq]
    exact DDAlignTypesWithLedger.slotPair leftView rightView exactCap
      (adjustedLeftEq ▸ adjustedRightEq ▸ exactTarget)

/-- Every successful executable type-alignment core reconstructs the branch
selected from its two resolved input views. -/
theorem alignTypesCore_ddAlignTypesRun
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (success : alignTypesCore state origin left right = some final) :
    DDAlignTypesRun left right state final := by
  cases leftEq : state.prevailing.apply left <;>
    cases rightEq : state.prevailing.apply right <;>
    first
    | exact alignTypesCore_matcherPair_ddAlignTypesRun leftEq rightEq success
    | exact alignTypesCore_slotPair_ddAlignTypesRun leftEq rightEq success
    | exact alignTypesCore_ordinary_ddAlignTypesRun
        (by simp [alignPairClass, leftEq, rightEq]) success

/-- Lift the complete type-alignment core through its event-only executable
wrapper.  Recording the alignment event changes none of the DD state indices. -/
theorem alignTypes_ddAlignTypesRun
    {state final : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (success : alignTypes state origin left right = some final) :
    DDAlignTypesRun left right state final := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, coreSuccess, finished⟩
  have finalEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length left right
      (state.prevailing.apply left) (state.prevailing.apply right)) = final :=
    Option.some.inj finished
  subst final
  simpa [DDAlignTypesRun] using
    (alignTypesCore_ddAlignTypesRun coreSuccess)

/-- Reconstruct the ordinary checking fallback.  An ordinary demand class
excludes both specialized resolved-head branches, leaving the event-wrapped
type alignment. -/
theorem alignAtSlot_ordinary_ddAlignRun
    {state final : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty}
    (demand : demandClass (state.prevailing.apply raw)
      (state.prevailing.apply expected) = .ordinary)
    (success : alignAtSlot state origin raw expected = some final) :
    DDAlignRun raw expected state final := by
  unfold alignAtSlot at success
  simp only at success
  split at success
  · simp_all [demandClass, productMatcherDuals?, productSlotDuals?]
  · simp_all [demandClass, productMatcherDuals?, productSlotDuals?]
  · rcases alignTypes_ddAlignTypesRun success with
      ⟨supplyEq, ledgerEq, aligned⟩
    exact ⟨supplyEq, ledgerEq,
      DDAlignWithLedger.ordinary demand aligned⟩

/-- The executable one-way solver returns exactly the origin-safe delta used
by the DD matcher-to-slot rule. -/
theorem solveResolvedWithLedger_originSafeOneWayDelta
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) =
        some step) :
    OriginSafeOneWayDelta ledger producerCap producerTarget consumerCap
      consumerTarget step.delta := by
  have admissible :=
    solveResolvedWithLedger_producerToSlot_admissible success
  change solveProducerToSlotWithLedger ledger solveCount origin producerCap
    producerTarget consumerCap consumerTarget = some step at success
  unfold solveProducerToSlotWithLedger at success
  split at success
  · contradiction
  · rename_i bindings matched
    simp only at success
    split at success
    · split at success
      · contradiction
      · rename_i targetSubst unified
        have stepEq := Option.some.inj success
        subst step
        refine ⟨⟨bindings, matched, rfl, ?_⟩, admissible⟩
        exact Unification.mguTy_exactTargetMGU unified
    · contradiction

/-- Reconstruct the raw matcher-to-slot branch of executable slot alignment.
The protected-producer check is retained by the executable success equation;
the DD rule consumes the exact origin-safe one-way delta from the same solve. -/
theorem alignAtSlot_matcherToSlot_ddAlignRun
    {state final : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (rawView : state.prevailing.apply raw =
      .matcher producerCap producerTarget)
    (expectedView : state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : alignAtSlot state origin raw expected = some final) :
    DDAlignRun raw expected state final := by
  unfold alignAtSlot at success
  simp only [rawView, expectedView] at success
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      dsimp at success
      split at success
      · rename_i checked
        have finalEq := Option.some.inj success
        subst final
        refine ⟨rfl, rfl, ?_⟩
        rw [InferState.prevailing_recordSolve]
        exact DDAlignWithLedger.matcherToSlot rawView expectedView
          (solveResolvedWithLedger_originSafeOneWayDelta stepEq)
      · contradiction

/-- Reconstruct raw slot-to-slot checking from its capability solve followed
by the capability-adjusted target solve. -/
theorem alignAtSlot_slotToSlot_ddAlignRun
    {state final : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty} {sourceCap requestedCap : Cap}
    {sourceTarget requestedTarget : Ty}
    (rawView : state.prevailing.apply raw =
      .slot sourceCap sourceTarget)
    (expectedView : state.prevailing.apply expected =
      .slot requestedCap requestedTarget)
    (success : alignAtSlot state origin raw expected = some final) :
    DDAlignRun raw expected state final := by
  unfold alignAtSlot at success
  simp only [rawView, expectedView] at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, targetBranchSuccess⟩
  rcases runResolvedConstraint_capEq_exact capSuccess with
    ⟨capStep, _, middleEq, capTargetId, exactCap⟩
  subst middle
  split at targetBranchSuccess <;> try contradiction
  rename_i afterSource afterRequested ignoredSourceCap adjustedSourceTarget
    ignoredRequestedCap adjustedRequestedTarget afterSourceView
    afterRequestedView
  rcases runResolvedConstraint_targetEq_exact targetBranchSuccess with
    ⟨targetStep, _, finalEq, exactTarget⟩
  subst final
  have capDeltaEq : capStep.delta =
      ⟨capStep.delta.cap, TySubst.id⟩ := by
    rw [← capTargetId]
  have adjustedSourceEq :
      adjustedSourceTarget =
        sourceTarget.applyCapability capStep.delta.cap := by
    have applied :
        (state.recordSolve capStep).prevailing.apply raw =
          capStep.delta.apply (state.prevailing.apply raw) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [rawView, afterSourceView] at applied
    simp only [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied
    exact Ty.slot.inj applied |>.2
  have adjustedRequestedEq :
      adjustedRequestedTarget =
        requestedTarget.applyCapability capStep.delta.cap := by
    have applied :
        (state.recordSolve capStep).prevailing.apply expected =
          capStep.delta.apply (state.prevailing.apply expected) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [expectedView, afterRequestedView] at applied
    simp only [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied
    exact Ty.slot.inj applied |>.2
  refine ⟨rfl, rfl, ?_⟩
  rw [InferState.prevailing_recordSolve,
    InferState.prevailing_recordSolve, capDeltaEq]
  exact DDAlignWithLedger.slotToSlot rawView expectedView exactCap
    (adjustedSourceEq ▸ adjustedRequestedEq ▸ exactTarget)

/-- A raw product-matcher view is preserved by the prevailing paired
substitution, with that substitution applied pointwise to its duals. -/
theorem productMatcherDuals?_apply
    {raw : Ty} {duals : List Dual} {S : Subst}
    (rawView : productMatcherDuals? raw = some duals) :
    productMatcherDuals? (S.apply raw) =
      some (duals.map (Dual.applySubst S)) := by
  have rawShape := productMatcherDuals?_sound rawView
  subst raw
  clear rawView
  have mapped : List.mapM (fun dual : Dual =>
      some (Dual.applySubst S dual)) duals =
      some (duals.map (Dual.applySubst S)) := by
    induction duals with
    | nil => rfl
    | cons dual duals induction => simp [List.mapM_cons, induction]
  simpa [productMatcherDuals?, matcherDual?, Subst.apply_prod,
    List.map_map, Dual.applySubst, Dual.apply, Function.comp_def] using mapped

/-- A raw product-slot view is preserved by the prevailing paired
substitution, with that substitution applied pointwise to its duals. -/
theorem productSlotDuals?_apply
    {raw : Ty} {duals : List Dual} {S : Subst}
    (rawView : productSlotDuals? raw = some duals) :
    productSlotDuals? (S.apply raw) =
      some (duals.map (Dual.applySubst S)) := by
  have rawShape := productSlotDuals?_sound rawView
  subst raw
  clear rawView
  have mapped : List.mapM (fun dual : Dual =>
      some (Dual.applySubst S dual)) duals =
      some (duals.map (Dual.applySubst S)) := by
    induction duals with
    | nil => rfl
    | cons dual duals induction => simp [List.mapM_cons, induction]
  simpa [productSlotDuals?, slotDual?, Subst.apply_prod,
    List.map_map, Dual.applySubst, Dual.apply, Function.comp_def] using mapped

/-- A nonempty raw product of slots cannot become a product of matchers under
substitution.  The explicit raw matcher failure excludes the empty product,
for which both product recognizers succeed vacuously. -/
theorem productMatcherDuals?_apply_none_of_productSlot
    {raw : Ty} {duals : List Dual} {S : Subst}
    (matcherNone : productMatcherDuals? raw = none)
    (slotView : productSlotDuals? raw = some duals) :
    productMatcherDuals? (S.apply raw) = none := by
  have rawShape := productSlotDuals?_sound slotView
  subst raw
  cases duals with
  | nil => simp [productMatcherDuals?] at matcherNone
  | cons dual duals =>
      simp [productMatcherDuals?, matcherDual?, Subst.apply_prod,
        Subst.apply_slot]

/-- Reconstruct the product-matcher lift from the executable synthetic unary
matcher source.  The DD rule remains indexed by the original product type. -/
theorem alignAtSlot_productMatcherLift_ddAlignRun
    {state final : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (rawView : productMatcherDuals? raw = some duals)
    (expectedView : state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : alignAtSlot state origin (productMatcherTarget duals) expected =
      some final) :
    DDAlignRun raw expected state final := by
  let resolvedDuals := duals.map (Dual.applySubst state.prevailing)
  have sourceView : state.prevailing.apply (productMatcherTarget duals) =
      .matcher (.prod (resolvedDuals.map Dual.cap))
        (.prod (resolvedDuals.map Dual.target)) := by
    simp [resolvedDuals, productMatcherTarget, Subst.apply_matcher,
      Cap.apply_prod, Subst.apply_prod, List.map_map, Dual.applySubst,
      Dual.apply, Function.comp_def]
  unfold alignAtSlot at success
  simp only [sourceView, expectedView] at success
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin
      (.producerToSlot (.prod (resolvedDuals.map Dual.cap))
        (.prod (resolvedDuals.map Dual.target)) consumerCap consumerTarget) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      dsimp at success
      split at success
      · rename_i checked
        have finalEq := Option.some.inj success
        subst final
        refine ⟨rfl, rfl, ?_⟩
        rw [InferState.prevailing_recordSolve]
        exact DDAlignWithLedger.productMatcherLift
          (by simpa [resolvedDuals] using productMatcherDuals?_apply rawView)
          expectedView
          (solveResolvedWithLedger_originSafeOneWayDelta stepEq)
      · contradiction

/-- Reconstruct the slot-tuple lift from the executable synthetic unary slot.
The DD rule remains indexed by the original raw product of slots. -/
theorem alignAtSlot_slotTupleLift_ddAlignRun
    {state final : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (rawView : productSlotDuals? raw = some duals)
    (expectedView : state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (demand : demandClass (state.prevailing.apply raw)
      (state.prevailing.apply expected) = .slotTupleLift)
    (success : alignAtSlot state origin (slotTupleTarget duals) expected =
      some final) :
    DDAlignRun raw expected state final := by
  let resolvedDuals := duals.map (Dual.applySubst state.prevailing)
  have sourceView : state.prevailing.apply (slotTupleTarget duals) =
      .slot (.prod (resolvedDuals.map Dual.cap))
        (.prod (resolvedDuals.map Dual.target)) := by
    simp [resolvedDuals, slotTupleTarget, Subst.apply_slot,
      Cap.apply_prod, Subst.apply_prod, List.map_map, Dual.applySubst,
      Dual.apply, Function.comp_def]
  unfold alignAtSlot at success
  simp only [sourceView, expectedView] at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, targetBranchSuccess⟩
  rcases runResolvedConstraint_capEq_exact capSuccess with
    ⟨capStep, _, middleEq, capTargetId, exactCap⟩
  subst middle
  split at targetBranchSuccess <;> try contradiction
  rename_i afterSource afterRequested ignoredSourceCap adjustedSourceTarget
    ignoredRequestedCap adjustedRequestedTarget afterSourceView
    afterRequestedView
  rcases runResolvedConstraint_targetEq_exact targetBranchSuccess with
    ⟨targetStep, _, finalEq, exactTarget⟩
  subst final
  have capDeltaEq : capStep.delta =
      ⟨capStep.delta.cap, TySubst.id⟩ := by
    rw [← capTargetId]
  have adjustedSourceEq : adjustedSourceTarget =
      (Ty.prod (resolvedDuals.map Dual.target)).applyCapability
        capStep.delta.cap := by
    have applied :
        (state.recordSolve capStep).prevailing.apply
            (slotTupleTarget duals) =
          capStep.delta.apply
            (state.prevailing.apply (slotTupleTarget duals)) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [sourceView, afterSourceView] at applied
    simp only [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied
    exact Ty.slot.inj applied |>.2
  have adjustedRequestedEq : adjustedRequestedTarget =
      consumerTarget.applyCapability capStep.delta.cap := by
    have applied :
        (state.recordSolve capStep).prevailing.apply expected =
          capStep.delta.apply (state.prevailing.apply expected) := by
      rw [InferState.prevailing_recordSolve, Subst.seq_apply]
    rw [expectedView, afterRequestedView] at applied
    simp only [Subst.apply, Ty.applyCapability, capTargetId,
      Ty.applyTarget_id] at applied
    exact Ty.slot.inj applied |>.2
  refine ⟨rfl, rfl, ?_⟩
  rw [InferState.prevailing_recordSolve,
    InferState.prevailing_recordSolve, capDeltaEq]
  exact DDAlignWithLedger.slotTupleLift demand
    (by simpa [resolvedDuals] using productSlotDuals?_apply rawView)
    expectedView exactCap
    (adjustedSourceEq ▸ adjustedRequestedEq ▸ exactTarget)

/-- A type whose cut-resolved view is a matcher cannot be one of the raw
product coercion sources, so the executable selector leaves it unchanged. -/
theorem expectedCoercionSource_of_resolvedMatcher
    (state : InferState) (raw expected : Ty)
    {producerCap : Cap} {producerTarget : Ty}
    (rawView : state.prevailing.apply raw =
      .matcher producerCap producerTarget) :
    expectedCoercionSource state raw expected = raw := by
  cases raw <;> simp [expectedCoercionSource, productMatcherDuals?,
    productSlotDuals?, Subst.apply, Ty.applyCapability, Ty.applyTarget]
      at rawView ⊢

/-- Lift the raw matcher-to-slot branch through the event-only
`alignExprResultAtExpected` wrapper. -/
theorem alignExprResultAtExpected_matcherToSlot_ddAlignRun
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final : InferState} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (rawView : expressionResult.state.prevailing.apply
      expressionResult.target = .matcher producerCap producerTarget)
    (expectedView : expressionResult.state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    DDAlignRun expressionResult.target expected expressionResult.state final := by
  have sourceEq := expectedCoercionSource_of_resolvedMatcher
    expressionResult.state expressionResult.target expected rawView
  unfold alignExprResultAtExpected at success
  cases alignmentEq : alignAtSlot expressionResult.state
      (freshOrigin .expression path "expected-type") expressionResult.target
      expected with
  | none => simp [sourceEq, alignmentEq] at success
  | some aligned =>
      simp only [sourceEq, alignmentEq, Option.some.injEq] at success
      subst final
      rcases alignAtSlot_matcherToSlot_ddAlignRun rawView expectedView
          alignmentEq with
        ⟨supplyEq, ledgerEq, alignedDD⟩
      exact ⟨by simpa using supplyEq, by simpa using ledgerEq,
        by simpa using alignedDD⟩

/-- Lift the raw product-matcher branch through coercion-source selection and
the event-only expected-alignment wrapper. -/
theorem alignExprResultAtExpected_productMatcherLift_ddAlignRun
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final : InferState} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (rawView : productMatcherDuals? expressionResult.target = some duals)
    (expectedView : expressionResult.state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    DDAlignRun expressionResult.target expected expressionResult.state final := by
  have sourceEq : expectedCoercionSource expressionResult.state
      expressionResult.target expected = productMatcherTarget duals := by
    simp [expectedCoercionSource, rawView, expectedView]
  unfold alignExprResultAtExpected at success
  cases alignmentEq : alignAtSlot expressionResult.state
      (freshOrigin .expression path "expected-type")
      (productMatcherTarget duals) expected with
  | none => simp [sourceEq, alignmentEq] at success
  | some aligned =>
      simp only [sourceEq, alignmentEq, Option.some.injEq] at success
      subst final
      rcases alignAtSlot_productMatcherLift_ddAlignRun rawView expectedView
          alignmentEq with
        ⟨supplyEq, ledgerEq, alignedDD⟩
      exact ⟨by simpa using supplyEq, by simpa using ledgerEq,
        by simpa using alignedDD⟩

/-- Lift the raw product-slot branch through coercion-source selection and
the event-only expected-alignment wrapper.  Raw matcher failure fixes the
empty-product precedence in favor of this slot-tuple branch. -/
theorem alignExprResultAtExpected_slotTupleLift_ddAlignRun
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final : InferState} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (matcherNone : productMatcherDuals? expressionResult.target = none)
    (rawView : productSlotDuals? expressionResult.target = some duals)
    (expectedView : expressionResult.state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    DDAlignRun expressionResult.target expected expressionResult.state final := by
  have sourceEq : expectedCoercionSource expressionResult.state
      expressionResult.target expected = slotTupleTarget duals := by
    simp [expectedCoercionSource, matcherNone, rawView, expectedView]
  have resolvedMatcherNone : productMatcherDuals?
      (expressionResult.state.prevailing.apply expressionResult.target) =
        none :=
    productMatcherDuals?_apply_none_of_productSlot matcherNone rawView
  have resolvedSlotView : productSlotDuals?
      (expressionResult.state.prevailing.apply expressionResult.target) =
        some (duals.map
          (Dual.applySubst expressionResult.state.prevailing)) :=
    productSlotDuals?_apply rawView
  have demand : demandClass
      (expressionResult.state.prevailing.apply expressionResult.target)
      (expressionResult.state.prevailing.apply expected) =
        .slotTupleLift := by
    simp [demandClass, resolvedMatcherNone, resolvedSlotView, expectedView]
  unfold alignExprResultAtExpected at success
  cases alignmentEq : alignAtSlot expressionResult.state
      (freshOrigin .expression path "expected-type")
      (slotTupleTarget duals) expected with
  | none => simp [sourceEq, alignmentEq] at success
  | some aligned =>
      simp only [sourceEq, alignmentEq, Option.some.injEq] at success
      subst final
      rcases alignAtSlot_slotTupleLift_ddAlignRun rawView expectedView demand
          alignmentEq with
        ⟨supplyEq, ledgerEq, alignedDD⟩
      exact ⟨by simpa using supplyEq, by simpa using ledgerEq,
        by simpa using alignedDD⟩

/-- The paired kernel rejects a product/slot outer-constructor mismatch at
every fuel. -/
private theorem solvePairedTy_prod_slot_eq_none
    (fuel : Nat) (ledger : CapabilityOriginLedger) (components : List Ty)
    (consumerCap : Cap) (consumerTarget : Ty) :
    PairedUnification.solvePairedTy fuel ledger (.prod components)
      (.slot consumerCap consumerTarget) = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [PairedUnification.solvePairedTy]
      split
      · contradiction
      · rfl

/-- A resolved product cannot take the raw fallback path to a slot: paired
equality preserves the two distinct outer constructors and fails immediately. -/
private theorem alignAtSlot_resolvedProd_slot_eq_none
    (state : InferState) (origin : ConstraintOrigin) (raw expected : Ty)
    (components : List Ty) (consumerCap : Cap) (consumerTarget : Ty)
    (rawView : state.prevailing.apply raw = .prod components)
    (expectedView : state.prevailing.apply expected =
      .slot consumerCap consumerTarget) :
    alignAtSlot state origin raw expected = none := by
  have targetSolveNone : solveTargetEqWithLedger state.capabilityOrigins
      state.trace.solves.length origin (.prod components)
        (.slot consumerCap consumerTarget) = none := by
    unfold solveTargetEqWithLedger
    split
    · rfl
    · rename_i result solved
      rw [solvePairedTy_prod_slot_eq_none] at solved
      contradiction
  have coreNone : alignTypesCore state origin raw expected = none := by
    unfold alignTypesCore
    simp only [rawView, expectedView]
    unfold runResolvedConstraint
    change (do
      let step ← solveTargetEqWithLedger state.capabilityOrigins
        state.trace.solves.length origin (.prod components)
          (.slot consumerCap consumerTarget)
      pure (state.recordSolve step)) = none
    rw [targetSolveNone]
    rfl
  unfold alignAtSlot
  simp only [rawView, expectedView]
  unfold alignTypes
  rw [coreNone]
  rfl

/-- Lift any raw-source `alignAtSlot` reconstruction through the event-only
expected-alignment wrapper. -/
private theorem alignExprResultAtExpected_of_rawSource_ddAlignRun
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final : InferState}
    (sourceEq : expectedCoercionSource expressionResult.state
      expressionResult.target expected = expressionResult.target)
    (alignSound : ∀ aligned,
      alignAtSlot expressionResult.state
        (freshOrigin .expression path "expected-type")
        expressionResult.target expected = some aligned →
      DDAlignRun expressionResult.target expected expressionResult.state
        aligned)
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    DDAlignRun expressionResult.target expected expressionResult.state final := by
  unfold alignExprResultAtExpected at success
  cases alignmentEq : alignAtSlot expressionResult.state
      (freshOrigin .expression path "expected-type") expressionResult.target
      expected with
  | none => simp [sourceEq, alignmentEq] at success
  | some aligned =>
      simp only [sourceEq, alignmentEq, Option.some.injEq] at success
      subst final
      rcases alignSound aligned alignmentEq with
        ⟨supplyEq, ledgerEq, alignedDD⟩
      exact ⟨by simpa using supplyEq, by simpa using ledgerEq,
        by simpa using alignedDD⟩

/-- Reconstruct every successful expected-type alignment using the same raw
coercion-source precedence and resolved-head dispatch as the executable
selector. -/
theorem alignExprResultAtExpected_ddAlignRun
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    DDAlignRun expressionResult.target expected expressionResult.state final := by
  cases matcherView : productMatcherDuals? expressionResult.target with
  | some duals =>
      cases expectedView : expressionResult.state.prevailing.apply expected <;>
        first
        | exact alignExprResultAtExpected_productMatcherLift_ddAlignRun
            matcherView expectedView success
        | exact alignExprResultAtExpected_of_rawSource_ddAlignRun
            (by simp [expectedCoercionSource, matcherView, expectedView])
            (by
              intro aligned alignmentEq
              exact alignAtSlot_ordinary_ddAlignRun
                (by simp [demandClass, expectedView]) alignmentEq)
            success
  | none =>
      cases slotView : productSlotDuals? expressionResult.target with
      | some duals =>
          cases expectedView :
              expressionResult.state.prevailing.apply expected <;>
            first
            | exact alignExprResultAtExpected_slotTupleLift_ddAlignRun
                matcherView slotView expectedView success
            | exact alignExprResultAtExpected_of_rawSource_ddAlignRun
                (by simp [expectedCoercionSource, matcherView, slotView,
                  expectedView])
                (by
                  intro aligned alignmentEq
                  exact alignAtSlot_ordinary_ddAlignRun
                    (by simp [demandClass, expectedView]) alignmentEq)
                success
      | none =>
          apply alignExprResultAtExpected_of_rawSource_ddAlignRun
            (by simp [expectedCoercionSource, matcherView, slotView]) ?_ success
          intro aligned alignmentEq
          cases rawView :
              expressionResult.state.prevailing.apply expressionResult.target <;>
            cases expectedView :
              expressionResult.state.prevailing.apply expected <;>
            first
            | exact alignAtSlot_matcherToSlot_ddAlignRun rawView expectedView
                alignmentEq
            | exact alignAtSlot_slotToSlot_ddAlignRun rawView expectedView
                alignmentEq
            | (have impossible := alignAtSlot_resolvedProd_slot_eq_none
                  expressionResult.state
                  (freshOrigin .expression path "expected-type")
                  expressionResult.target expected _ _ _ rawView expectedView
               rw [impossible] at alignmentEq
               contradiction)
            | exact alignAtSlot_ordinary_ddAlignRun
                (by simp [demandClass, productMatcherDuals?,
                  productSlotDuals?, rawView, expectedView]) alignmentEq

/-- Compose synthesis and expected-type alignment into the single public DD
checking rule. -/
theorem DDSynthRun.check
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {expected : Ty} {initial : InferState} {synthesized : ExprResult}
    {final : InferState}
    (synthRun : DDSynthRun signature context expression initial synthesized)
    (alignRun : DDAlignRun synthesized.target expected synthesized.state final) :
    DDCheckRun signature context expression expected initial final := by
  rcases synthRun with ⟨raw, synthDerived, targetEq, synthOrigin⟩
  rcases alignRun with ⟨supplyEq, ledgerEq, aligned⟩
  subst raw
  unfold DDCheckRun
  rw [supplyEq, ledgerEq]
  refine ⟨DDCheck.mk synthDerived aligned.erase, ?_⟩
  exact DDCheckOrigin.mk synthOrigin aligned

/-- Any successful checking traversal composes its synthesis run with the
generic expected-alignment reconstruction. -/
theorem checkExprFuel_ddCheckRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected : Ty} {initial final : InferState}
    {synthesized : ExprResult}
    (inferEq : inferExprFuel fuel signature context selfEnv path expression
      initial = some synthesized)
    (synthRun : DDSynthRun signature context expression initial synthesized)
    (success : checkExprFuel (fuel + 1) signature context selfEnv path
      expression expected initial = some final) :
    DDCheckRun signature context expression expected initial final := by
  have alignmentEq :
      alignExprResultAtExpected path synthesized expected = some final := by
    simpa [checkExprFuel, inferEq] using success
  exact DDSynthRun.check synthRun
    (alignExprResultAtExpected_ddAlignRun alignmentEq)

/-- The matcher-to-slot branch of executable checking reconstructs the single
DD checking rule from its synthesis induction hypothesis. -/
theorem checkExprFuel_matcherToSlot_ddCheckRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected : Ty} {initial final : InferState}
    {synthesized : ExprResult} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (inferEq : inferExprFuel fuel signature context selfEnv path expression
      initial = some synthesized)
    (synthRun : DDSynthRun signature context expression initial synthesized)
    (rawView : synthesized.state.prevailing.apply synthesized.target =
      .matcher producerCap producerTarget)
    (expectedView : synthesized.state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : checkExprFuel (fuel + 1) signature context selfEnv path
      expression expected initial = some final) :
    DDCheckRun signature context expression expected initial final := by
  have alignmentEq :
      alignExprResultAtExpected path synthesized expected = some final := by
    simpa [checkExprFuel, inferEq] using success
  exact DDSynthRun.check synthRun
    (alignExprResultAtExpected_matcherToSlot_ddAlignRun rawView expectedView
      alignmentEq)

/-- The raw product-matcher branch reconstructs the explicit DD product lift
before composing it with checking. -/
theorem checkExprFuel_productMatcherLift_ddCheckRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected : Ty} {initial final : InferState}
    {synthesized : ExprResult} {duals : List Dual}
    {consumerCap : Cap} {consumerTarget : Ty}
    (inferEq : inferExprFuel fuel signature context selfEnv path expression
      initial = some synthesized)
    (synthRun : DDSynthRun signature context expression initial synthesized)
    (rawView : productMatcherDuals? synthesized.target = some duals)
    (expectedView : synthesized.state.prevailing.apply expected =
      .slot consumerCap consumerTarget)
    (success : checkExprFuel (fuel + 1) signature context selfEnv path
      expression expected initial = some final) :
    DDCheckRun signature context expression expected initial final := by
  have alignmentEq :
      alignExprResultAtExpected path synthesized expected = some final := by
    simpa [checkExprFuel, inferEq] using success
  exact DDSynthRun.check synthRun
    (alignExprResultAtExpected_productMatcherLift_ddAlignRun rawView
      expectedView alignmentEq)

/-- The domain and state produced by the executable lambda-entry allocation. -/
def lambdaDomain (initial : InferState) (path : SyntaxPath) : Ty :=
  ((visit initial .exprLam path).freshTy
    (freshOrigin .expression path "lambda-domain")).1

def lambdaEntryState (initial : InferState) (path : SyntaxPath) : InferState :=
  ((visit initial .exprLam path).freshTy
    (freshOrigin .expression path "lambda-domain")).2

@[simp] theorem lambdaDomain_eq
    (initial : InferState) (path : SyntaxPath) :
    lambdaDomain initial path = .var initial.supply.nextTy :=
  rfl

@[simp] theorem lambdaEntryState_supply
    (initial : InferState) (path : SyntaxPath) :
    (lambdaEntryState initial path).supply =
      { initial.supply with nextTy := initial.supply.nextTy + 1 } :=
  rfl

@[simp] theorem lambdaEntryState_prevailing
    (initial : InferState) (path : SyntaxPath) :
    (lambdaEntryState initial path).prevailing = initial.prevailing :=
  rfl

@[simp] theorem lambdaEntryState_capabilityOrigins
    (initial : InferState) (path : SyntaxPath) :
    (lambdaEntryState initial path).capabilityOrigins =
      initial.capabilityOrigins :=
  rfl

/-- The empty executable expression-list result is the empty DD derivation. -/
theorem DDSynthsRun.nil
    (signature : FrozenSig) (context : Context) (initial : InferState) :
    DDSynthsRun signature context [] initial ⟨[], initial⟩ := by
  refine ⟨[], DDSynths.nil, rfl, ?_⟩
  exact DDSynthsOrigin.nil

/-- Compose exact head and tail run certificates in source order. -/
theorem DDSynthsRun.cons
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {expressions : List Expr} {initial : InferState} {head : ExprResult}
    {tail : ExprsResult}
    (headRun : DDSynthRun signature context expression initial head)
    (tailRun : DDSynthsRun signature context expressions head.state tail) :
    DDSynthsRun signature context (expression :: expressions) initial
      ⟨head.target :: tail.targets, tail.state⟩ := by
  rcases headRun with ⟨headTarget, headDerived, headEq, headOrigin⟩
  rcases tailRun with ⟨tailTargets, tailDerived, tailEq, tailOrigin⟩
  refine ⟨headTarget :: tailTargets, DDSynths.cons headDerived tailDerived,
    ?_, ?_⟩
  · simp [headEq, tailEq]
  · exact DDSynthsOrigin.cons headOrigin tailOrigin

/-- Reconstruct lambda synthesis from the exact body-entry run. -/
theorem DDSynthRun.lam
    {signature : FrozenSig} {context : Context} {name : String} {body : Expr}
    {initial : InferState} {path : SyntaxPath} {bodyResult : ExprResult}
    (bodyRun : DDSynthRun signature
      ((name, Scheme.mono (lambdaDomain initial path)) :: context) body
      (lambdaEntryState initial path) bodyResult) :
    DDSynthRun signature context (.lam name body) initial
      (finishExpr (.lam name body) path
        (.fn (lambdaDomain initial path) bodyResult.target)
        bodyResult.state) := by
  rcases bodyRun with ⟨bodyTarget, bodyDerived, bodyEq, bodyOrigin⟩
  change DDSynth signature
    { initial.supply with nextTy := initial.supply.nextTy + 1 }
    initial.prevailing
    ((name, Scheme.mono (.var initial.supply.nextTy)) :: context) body
    bodyTarget bodyResult.state.supply bodyResult.state.prevailing at bodyDerived
  change DDSynthOrigin signature bodyDerived initial.capabilityOrigins
    bodyResult.state.capabilityOrigins at bodyOrigin
  refine ⟨.fn (.var initial.supply.nextTy) bodyTarget,
    DDSynth.lam bodyDerived, ?_, ?_⟩
  · simp [finishExpr, bodyEq]
  · simpa [finishExpr] using DDSynthOrigin.lam bodyOrigin

/-- Reconstruct tuple synthesis from the exact expression-list run after the
tuple visit event. -/
theorem DDSynthRun.tuple
    {signature : FrozenSig} {context : Context} {expressions : List Expr}
    {initial : InferState} {path : SyntaxPath} {children : ExprsResult}
    (childrenRun : DDSynthsRun signature context expressions
      (visit initial .exprTuple path) children) :
    DDSynthRun signature context (.tuple expressions) initial
      (finishExpr (.tuple expressions) path (.prod children.targets)
        children.state) := by
  rcases childrenRun with
    ⟨childTargets, childrenDerived, targetsEq, childrenOrigin⟩
  change DDSynths signature initial.supply initial.prevailing context
    expressions childTargets children.state.supply
    children.state.prevailing at childrenDerived
  change DDSynthsOrigin signature childrenDerived initial.capabilityOrigins
    children.state.capabilityOrigins at childrenOrigin
  refine ⟨.prod childTargets, DDSynth.tuple childrenDerived, ?_, ?_⟩
  · simp [finishExpr, targetsEq]
  · simpa [finishExpr] using DDSynthOrigin.tuple childrenOrigin

/-- The empty branch of the executable expression-list traversal reconstructs
the empty DD list certificate. -/
theorem inferExprsFuel_nil_ddSynthsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {initial : InferState} {result : ExprsResult}
    (success : inferExprsFuel (fuel + 1) signature context selfEnv parent index
      [] initial = some result) :
    DDSynthsRun signature context [] initial result := by
  simp only [inferExprsFuel] at success
  have resultEq := Option.some.inj success
  subst result
  exact DDSynthsRun.nil signature context initial

/-- The cons branch of expression-list traversal preserves the exact
left-to-right state boundary.  The two functional premises are precisely the
head and tail induction hypotheses that the eventual mutual traversal theorem
will supply; no typing or runtime certificate is assumed. -/
theorem inferExprsFuel_cons_ddSynthsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {initial : InferState} {result : ExprsResult}
    (headSound : ∀ head : ExprResult,
      inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial = some head →
      DDSynthRun signature context expression initial head)
    (tailSound : ∀ (head : ExprResult) (tail : ExprsResult),
      inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions head.state = some tail →
      DDSynthsRun signature context expressions head.state tail)
    (success : inferExprsFuel (fuel + 1) signature context selfEnv parent index
      (expression :: expressions) initial = some result) :
    DDSynthsRun signature context (expression :: expressions) initial result := by
  simp only [inferExprsFuel] at success
  cases headEq : inferExprFuel fuel signature context selfEnv
      (index :: parent) expression initial with
  | none => simp [headEq] at success
  | some head =>
      cases tailEq : inferExprsFuel fuel signature context selfEnv parent
          (index + 1) expressions head.state with
      | none => simp [headEq, tailEq] at success
      | some tail =>
          simp only [headEq, tailEq, Option.some.injEq] at success
          subst result
          exact DDSynthsRun.cons (headSound head headEq)
            (tailSound head tail tailEq)

/-- A reconstructed run from the executable initial state is already a
public `DDTyping` derivation at the run's resolved result type. -/
theorem DDSynthRun.toDDTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (run : DDSynthRun signature context expression
      (initialState signature context) result) :
    DDTyping signature context expression result.resolvedTarget := by
  rcases run with ⟨rawTarget, derived, targetEq, origin⟩
  change DDSynth signature (initialSupply signature context) Subst.id context
    expression rawTarget result.state.supply result.state.prevailing at derived
  change DDSynthOrigin signature derived []
    result.state.capabilityOrigins at origin
  refine ⟨rawTarget, result.state.supply, result.state.prevailing, ?_,
    result.state.capabilityOrigins, ?_, ?_⟩
  · exact derived
  · exact origin
  · simp [ExprResult.resolvedTarget, targetEq]

/-- The lambda branch delegates exactly one smaller traversal to its body;
the functional premise is the expression induction hypothesis at the fresh
domain state. -/
theorem inferExprFuel_lam_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {body : Expr}
    {initial : InferState} {result : ExprResult}
    (bodySound : ∀ bodyResult : ExprResult,
      inferExprFuel fuel signature
        ((name, Scheme.mono (lambdaDomain initial path)) :: context)
        (selfEnv.erase name) (0 :: path) body
        (lambdaEntryState initial path) = some bodyResult →
      DDSynthRun signature
        ((name, Scheme.mono (lambdaDomain initial path)) :: context) body
        (lambdaEntryState initial path) bodyResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lam name body) initial = some result) :
    DDSynthRun signature context (.lam name body) initial result := by
  cases bodyEq : inferExprFuel fuel signature
      ((name, Scheme.mono (lambdaDomain initial path)) :: context)
      (selfEnv.erase name) (0 :: path) body
      (lambdaEntryState initial path) with
  | none =>
      have actualBodyEq := bodyEq
      simp only [lambdaDomain, lambdaEntryState] at actualBodyEq
      simp [inferExprFuel, actualBodyEq] at success
  | some bodyResult =>
      have actualBodyEq := bodyEq
      simp only [lambdaDomain, lambdaEntryState] at actualBodyEq
      have resultEq :
          finishExpr (.lam name body) path
            (.fn (lambdaDomain initial path) bodyResult.target)
            bodyResult.state = result := by
        apply Option.some.inj
        simpa [inferExprFuel, lambdaDomain, actualBodyEq] using success
      subst result
      exact DDSynthRun.lam (bodySound bodyResult bodyEq)

/-- The tuple branch delegates to the expression-list induction hypothesis
after recording its syntax visit. -/
theorem inferExprFuel_tuple_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expressions : List Expr}
    {initial : InferState} {result : ExprResult}
    (childrenSound : ∀ children : ExprsResult,
      inferExprsFuel fuel signature context selfEnv path 0 expressions
        (visit initial .exprTuple path) = some children →
      DDSynthsRun signature context expressions
        (visit initial .exprTuple path) children)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.tuple expressions) initial = some result) :
    DDSynthRun signature context (.tuple expressions) initial result := by
  cases childrenEq : inferExprsFuel fuel signature context selfEnv path 0
      expressions (visit initial .exprTuple path) with
  | none => simp [inferExprFuel, childrenEq] at success
  | some children =>
      have resultEq :
          finishExpr (.tuple expressions) path (.prod children.targets)
            children.state = result := by
        apply Option.some.inj
        simpa [inferExprFuel, childrenEq] using success
      subst result
      exact DDSynthRun.tuple (childrenSound children childrenEq)

/-- Context lookup uses the executable scheme-instantiation helper and
reconstructs the matching rename-only origin transition.  A direct-self hit
adds only trace/source evidence and therefore does not change any DD index. -/
theorem inferExprFuel_var_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.var name) initial = some result) :
    DDSynthRun signature context (.var name) initial result := by
  let entered := visit initial .exprVar path
  let normalizedContext := context.applySubst entered.prevailing
  cases lookup : normalizedContext.find? name with
  | none =>
      simp [inferExprFuel, entered, normalizedContext, lookup] at success
  | some scheme =>
      cases active : selfEnv.find? name with
      | none =>
          simp only [inferExprFuel, entered, normalizedContext, lookup,
            active] at success
          have resultEq := Option.some.inj success
          subst result
          have ddLookup :
              (context.applySubst initial.prevailing).find? name = some scheme := by
            simpa [normalizedContext, entered, visit] using lookup
          refine ⟨(InferenceBase.instantiateScheme initial.supply scheme).value,
            DDSynth.var ddLookup, ?_, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit]
          · simpa [finishExpr, visit,
              DDLedger.markSchemeInstance] using
              (DDSynthOrigin.var (signature := signature)
                (q := initial.supply) (S := initial.prevailing)
                (context := context) (ledger := initial.capabilityOrigins)
                ddLookup)
      | some placeholder =>
          simp only [inferExprFuel, entered, normalizedContext, lookup,
            active] at success
          have resultEq := Option.some.inj success
          subst result
          have ddLookup :
              (context.applySubst initial.prevailing).find? name = some scheme := by
            simpa [normalizedContext, entered, visit] using lookup
          refine ⟨(InferenceBase.instantiateScheme initial.supply scheme).value,
            DDSynth.var ddLookup, ?_, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit,
              recordSelfReference]
          · simpa [finishExpr, visit,
              recordSelfReference, DDLedger.markSchemeInstance] using
              (DDSynthOrigin.var (signature := signature)
                (q := initial.supply) (S := initial.prevailing)
                (context := context) (ledger := initial.capabilityOrigins)
                ddLookup)

/-- A successful literal traversal directly reconstructs the corresponding
DD synthesis and its unchanged origin ledger. -/
theorem inferExprFuel_lit_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {value : Int}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lit value) initial = some result) :
    DDSynthRun signature context (.lit value) initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.int, DDSynth.lit, rfl, ?_⟩
  exact DDSynthOrigin.lit

/-- A successful `something` traversal reconstructs the same one-target-meta
allocation as the DD rule, while leaving the origin ledger unchanged. -/
theorem inferExprFuel_something_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      .something initial = some result) :
    DDSynthRun signature context .something initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.matcher .any (.var initial.supply.nextTy), DDSynth.something,
    rfl, ?_⟩
  exact DDSynthOrigin.something

end Inference
end TypePM
