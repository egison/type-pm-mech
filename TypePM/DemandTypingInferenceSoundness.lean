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

@[simp] theorem InferState.freshTy_prevailing
    (state : InferState) (origin : ConstraintOrigin) :
    (state.freshTy origin).2.prevailing = state.prevailing :=
  rfl

@[simp] theorem InferState.freshTy_capabilityOrigins
    (state : InferState) (origin : ConstraintOrigin) :
    (state.freshTy origin).2.capabilityOrigins = state.capabilityOrigins :=
  rfl

@[simp] theorem InferState.freshCap_prevailing
    (state : InferState) (origin : ConstraintOrigin) :
    (state.freshCap origin).2.prevailing = state.prevailing :=
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
    (name : String) (state : InferState) (scheme : NamedScheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.prevailing = state.prevailing :=
  rfl

@[simp] theorem instantiateSchemeInState_target
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : NamedScheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).1 = (InferenceBase.instantiateScheme state.supply scheme).value :=
  rfl

@[simp] theorem instantiateSchemeInState_supply
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : NamedScheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.supply =
        (InferenceBase.instantiateScheme state.supply scheme).supply :=
  rfl

@[simp] theorem instantiateSchemeInState_capabilityOrigins
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : NamedScheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.capabilityOrigins =
        state.capabilityOrigins.setOrigins
          (freshCapImages state.supply scheme.capBinders) .renameOnly :=
  rfl

@[simp] theorem instantiateCtorInState_target
    (state : InferState) (scheme : CtorScheme) :
    (instantiateCtorInState state scheme).1 =
      (InferenceBase.instantiateCtorScheme state.supply scheme).value :=
  rfl

@[simp] theorem instantiateCtorInState_supply
    (state : InferState) (scheme : CtorScheme) :
    (instantiateCtorInState state scheme).2.supply =
      (InferenceBase.instantiateCtorScheme state.supply scheme).supply :=
  rfl

@[simp] theorem instantiateCtorInState_prevailing
    (state : InferState) (scheme : CtorScheme) :
    (instantiateCtorInState state scheme).2.prevailing = state.prevailing :=
  rfl

@[simp] theorem instantiateCtorInState_capabilityOrigins
    (state : InferState) (scheme : CtorScheme) :
    (instantiateCtorInState state scheme).2.capabilityOrigins =
      DDLedger.markCtorInstance state.capabilityOrigins state.supply scheme :=
  rfl

/-- Executable and DD export selection name the same surviving capability
leaves. -/
theorem capabilityExportLeaves_eq_exportLeaves
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    capabilityExportLeaves state capImages exportedPayload =
      DDLedger.exportLeaves state.capabilityOrigins state.prevailing capImages
        exportedPayload := by
  unfold capabilityExportLeaves DDLedger.exportLeaves
  dsimp only
  congr 1
  funext varId
  cases state.capabilityOrigins.originOf varId <;> rfl

@[simp] theorem InferState.freezeCapabilityExport_supply
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).supply =
      state.supply :=
  rfl

@[simp] theorem InferState.freezeCapabilityExport_prevailing
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).prevailing =
      state.prevailing :=
  rfl

@[simp] theorem InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins =
      DDLedger.freezeExport state.capabilityOrigins state.prevailing capImages
        exportedPayload := by
  simp [InferState.freezeCapabilityExport, DDLedger.freezeExport,
    capabilityExportLeaves_eq_exportLeaves]

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

/-- Exact-state certificate for pointwise checking of expression/type lists. -/
def DDChecksRun (signature : FrozenSig) (context : Context)
    (expressions : List Expr) (expecteds : List Ty)
    (initial final : InferState) : Prop :=
  ∃ derived : DDChecks signature initial.supply initial.prevailing context
      expressions expecteds final.supply final.prevailing,
    DDChecksOrigin signature derived initial.capabilityOrigins
      final.capabilityOrigins

/-- Exact-state certificate for one executable user-pattern traversal. -/
def DDPatternRun (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) (pattern : Pattern)
    (initial : InferState) (result : PatternResult) : Prop :=
  ∃ derived : DDPattern signature initial.supply initial.prevailing context
      parameters bindings pattern result.dual result.bindings
      result.state.supply result.state.prevailing,
    DDPatternOrigin signature derived initial.capabilityOrigins
      result.state.capabilityOrigins

/-- List form of `DDPatternRun`, retaining the exact output bindings and
state indices of the executable left-to-right traversal. -/
def DDPatternsRun (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) (patterns : List Pattern)
    (initial : InferState) (result : PatternsResult) : Prop :=
  ∃ derived : DDPatterns signature initial.supply initial.prevailing context
      parameters bindings patterns result.duals result.bindings
      result.state.supply result.state.prevailing,
    DDPatternsOrigin signature derived initial.capabilityOrigins
      result.state.capabilityOrigins

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

/-- The application domain allocated immediately after function synthesis. -/
def applicationDomain (functionResult : ExprResult) (path : SyntaxPath) : Ty :=
  (functionResult.state.freshTy
    (freshOrigin .expression path "application-domain")).1

/-- The application result allocated immediately after its domain. -/
def applicationResultTarget
    (functionResult : ExprResult) (path : SyntaxPath) : Ty :=
  (((functionResult.state.freshTy
      (freshOrigin .expression path "application-domain")).2).freshTy
    (freshOrigin .expression path "application-result")).1

/-- State after the two application target allocations. -/
def applicationFreshState
    (functionResult : ExprResult) (path : SyntaxPath) : InferState :=
  (((functionResult.state.freshTy
      (freshOrigin .expression path "application-domain")).2).freshTy
    (freshOrigin .expression path "application-result")).2

/-- The ordinary recursive-binder domain allocated after visiting `fix`. -/
def fixDomain (initial : InferState) (path : SyntaxPath) : Ty :=
  ((visit initial .exprFix path).freshTy
    (freshOrigin .recursiveBinder path "fix-domain")).1

/-- The ordinary recursive-binder codomain allocated after its domain. -/
def fixCodomain (initial : InferState) (path : SyntaxPath) : Ty :=
  ((((visit initial .exprFix path).freshTy
      (freshOrigin .recursiveBinder path "fix-domain")).2).freshTy
    (freshOrigin .recursiveBinder path "fix-codomain")).1

/-- State after the ordinary recursive placeholder's two allocations. -/
def fixFreshState (initial : InferState) (path : SyntaxPath) : InferState :=
  ((((visit initial .exprFix path).freshTy
      (freshOrigin .recursiveBinder path "fix-domain")).2).freshTy
    (freshOrigin .recursiveBinder path "fix-codomain")).2

/-- State passed to an ordinary recursive body, including its two
provenance-only acceptance events. -/
def fixBodyEntryState (initial : InferState) (path : SyntaxPath)
    (self argument : String) : InferState :=
  let placeholder := .fn (fixDomain initial path) (fixCodomain initial path)
  ((fixFreshState initial path).recordEvent
    (.fixPlaceholder self argument placeholder path)).recordEvent
    (.directSelfAccepted self placeholder path)

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

@[simp] theorem applicationDomain_eq
    (functionResult : ExprResult) (path : SyntaxPath) :
    applicationDomain functionResult path =
      .var functionResult.state.supply.nextTy :=
  rfl

@[simp] theorem applicationResultTarget_eq
    (functionResult : ExprResult) (path : SyntaxPath) :
    applicationResultTarget functionResult path =
      .var (functionResult.state.supply.nextTy + 1) :=
  rfl

@[simp] theorem applicationFreshState_supply
    (functionResult : ExprResult) (path : SyntaxPath) :
    (applicationFreshState functionResult path).supply =
      { functionResult.state.supply with
        nextTy := functionResult.state.supply.nextTy + 2 } :=
  rfl

@[simp] theorem applicationFreshState_prevailing
    (functionResult : ExprResult) (path : SyntaxPath) :
    (applicationFreshState functionResult path).prevailing =
      functionResult.state.prevailing :=
  rfl

@[simp] theorem applicationFreshState_capabilityOrigins
    (functionResult : ExprResult) (path : SyntaxPath) :
    (applicationFreshState functionResult path).capabilityOrigins =
      functionResult.state.capabilityOrigins :=
  rfl

@[simp] theorem fixDomain_eq
    (initial : InferState) (path : SyntaxPath) :
    fixDomain initial path = .var initial.supply.nextTy :=
  rfl

@[simp] theorem fixCodomain_eq
    (initial : InferState) (path : SyntaxPath) :
    fixCodomain initial path = .var (initial.supply.nextTy + 1) :=
  rfl

@[simp] theorem fixFreshState_supply
    (initial : InferState) (path : SyntaxPath) :
    (fixFreshState initial path).supply =
      { initial.supply with nextTy := initial.supply.nextTy + 2 } :=
  rfl

@[simp] theorem fixFreshState_prevailing
    (initial : InferState) (path : SyntaxPath) :
    (fixFreshState initial path).prevailing = initial.prevailing :=
  rfl

@[simp] theorem fixFreshState_capabilityOrigins
    (initial : InferState) (path : SyntaxPath) :
    (fixFreshState initial path).capabilityOrigins =
      initial.capabilityOrigins :=
  rfl

@[simp] theorem fixBodyEntryState_supply
    (initial : InferState) (path : SyntaxPath) (self argument : String) :
    (fixBodyEntryState initial path self argument).supply =
      { initial.supply with nextTy := initial.supply.nextTy + 2 } := by
  simp [fixBodyEntryState]

@[simp] theorem fixBodyEntryState_prevailing
    (initial : InferState) (path : SyntaxPath) (self argument : String) :
    (fixBodyEntryState initial path self argument).prevailing =
      initial.prevailing := by
  simp [fixBodyEntryState]

@[simp] theorem fixBodyEntryState_capabilityOrigins
    (initial : InferState) (path : SyntaxPath) (self argument : String) :
    (fixBodyEntryState initial path self argument).capabilityOrigins =
      initial.capabilityOrigins := by
  simp [fixBodyEntryState]

/-- Away from matcher literals, the executable placeholder selector is
exactly the two-fresh ordinary `fix` allocation named above. -/
theorem buildFixPlaceholder_nonMatcher
    (signature : FrozenSig) (initial : InferState) (path : SyntaxPath)
    (body : Expr) (nonMatcher : NonMatcherBody body) :
    buildFixPlaceholder signature path body (visit initial .exprFix path) =
      some (fixDomain initial path, fixCodomain initial path,
        fixFreshState initial path) := by
  cases body <;>
    simp [NonMatcherBody, matcherProducingRoot, buildFixPlaceholder,
      fixDomain, fixCodomain, fixFreshState] at nonMatcher ⊢

/-- The empty executable expression-list result is the empty DD derivation. -/
theorem DDSynthsRun.nil
    (signature : FrozenSig) (context : Context) (initial : InferState) :
    DDSynthsRun signature context [] initial ⟨[], initial⟩ := by
  refine ⟨[], DDSynths.nil, rfl, ?_⟩
  exact DDSynthsOrigin.nil

/-- Empty pointwise checking preserves the exact executable state. -/
theorem DDChecksRun.nil
    (signature : FrozenSig) (context : Context) (initial : InferState) :
    DDChecksRun signature context [] [] initial initial := by
  exact ⟨DDChecks.nil, DDChecksOrigin.nil⟩

/-- Empty user-pattern-list synthesis preserves bindings and state exactly. -/
theorem DDPatternsRun.nil
    (signature : FrozenSig) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (initial : InferState) :
    DDPatternsRun signature context parameters bindings [] initial
      ⟨[], bindings, initial⟩ := by
  exact ⟨DDPatterns.nil, DDPatternsOrigin.nil⟩

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

/-- Compose exact head checking with the tail run in source order. -/
theorem DDChecksRun.cons
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {expressions : List Expr} {expected : Ty} {expecteds : List Ty}
    {initial middle final : InferState}
    (headRun : DDCheckRun signature context expression expected initial middle)
    (tailRun : DDChecksRun signature context expressions expecteds middle final) :
    DDChecksRun signature context (expression :: expressions)
      (expected :: expecteds) initial final := by
  rcases headRun with ⟨headDerived, headOrigin⟩
  rcases tailRun with ⟨tailDerived, tailOrigin⟩
  exact ⟨DDChecks.cons headDerived tailDerived,
    DDChecksOrigin.cons headOrigin tailOrigin⟩

/-- Compose exact head and tail user-pattern runs while threading the binding
context and inference state left to right. -/
theorem DDPatternsRun.cons
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {patterns : List Pattern}
    {initial : InferState} {head : PatternResult} {tail : PatternsResult}
    (headRun : DDPatternRun signature context parameters bindings pattern
      initial head)
    (tailRun : DDPatternsRun signature context parameters head.bindings
      patterns head.state tail) :
    DDPatternsRun signature context parameters bindings (pattern :: patterns)
      initial ⟨head.dual :: tail.duals, tail.bindings, tail.state⟩ := by
  rcases headRun with ⟨headDerived, headOrigin⟩
  rcases tailRun with ⟨tailDerived, tailOrigin⟩
  exact ⟨DDPatterns.cons headDerived tailDerived,
    DDPatternsOrigin.cons headOrigin tailOrigin⟩

/-- Reconstruct lambda synthesis from the exact body-entry run. -/
theorem DDSynthRun.lam
    {signature : FrozenSig} {context : Context} {name : String} {body : Expr}
    {initial : InferState} {path : SyntaxPath} {bodyResult : ExprResult}
    (bodyRun : DDSynthRun signature
      ((name, NamedScheme.mono (lambdaDomain initial path)) :: context) body
      (lambdaEntryState initial path) bodyResult) :
    DDSynthRun signature context (.lam name body) initial
      (finishExpr (.lam name body) path
        (.fn (lambdaDomain initial path) bodyResult.target)
        bodyResult.state) := by
  rcases bodyRun with ⟨bodyTarget, bodyDerived, bodyEq, bodyOrigin⟩
  change DDSynth signature
    { initial.supply with nextTy := initial.supply.nextTy + 1 }
    initial.prevailing
    ((name, NamedScheme.mono (.var initial.supply.nextTy)) :: context) body
    bodyTarget bodyResult.state.supply bodyResult.state.prevailing at bodyDerived
  change DDSynthOrigin signature bodyDerived initial.capabilityOrigins
    bodyResult.state.capabilityOrigins at bodyOrigin
  refine ⟨.fn (.var initial.supply.nextTy) bodyTarget,
    DDSynth.lam bodyDerived, ?_, ?_⟩
  · simp [finishExpr, bodyEq]
  · simpa [finishExpr] using DDSynthOrigin.lam bodyOrigin

/-- Compose the ordinary recursive-body run with its codomain alignment.  The
two acceptance events at body entry affect neither DD state index nor the
origin ledger. -/
theorem DDSynthRun.fix
    {signature : FrozenSig} {context : Context} {self argument : String}
    {body : Expr} {initial : InferState} {path : SyntaxPath}
    {bodyResult : ExprResult} {alignedState : InferState}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (bodyRun : DDSynthRun signature
      ((argument, NamedScheme.mono (fixDomain initial path)) ::
        (self, NamedScheme.mono
          (.fn (fixDomain initial path) (fixCodomain initial path))) :: context)
      body (fixBodyEntryState initial path self argument) bodyResult)
    (alignRun : DDAlignTypesRun bodyResult.target (fixCodomain initial path)
      bodyResult.state alignedState) :
    DDSynthRun signature context (.fix self argument body) initial
      (finishExpr (.fix self argument body) path
        (.fn (fixDomain initial path) (fixCodomain initial path))
        alignedState) := by
  rcases bodyRun with ⟨bodyTarget, bodyDerived, bodyTargetEq, bodyOrigin⟩
  rcases alignRun with ⟨alignedSupplyEq, alignedLedgerEq, aligned⟩
  subst bodyTarget
  change DDSynth signature
    { initial.supply with nextTy := initial.supply.nextTy + 2 }
    initial.prevailing
    ((argument, NamedScheme.mono (.var initial.supply.nextTy)) ::
      (self, NamedScheme.mono
        (.fn (.var initial.supply.nextTy)
          (.var (initial.supply.nextTy + 1)))) :: context)
    body bodyResult.target bodyResult.state.supply
      bodyResult.state.prevailing at bodyDerived
  change DDSynthOrigin signature bodyDerived initial.capabilityOrigins
    bodyResult.state.capabilityOrigins at bodyOrigin
  simp only [fixCodomain_eq] at aligned
  have baseRun : DDSynthRun signature context (.fix self argument body) initial
      ⟨.fn (.var initial.supply.nextTy) (.var (initial.supply.nextTy + 1)),
        alignedState⟩ := by
    unfold DDSynthRun
    let rawDerived :=
      DDSynth.fix distinct direct nonMatcher bodyDerived aligned.erase
    let finalDerived : DDSynth signature initial.supply initial.prevailing
        context (.fix self argument body)
        (.fn (.var initial.supply.nextTy) (.var (initial.supply.nextTy + 1)))
        alignedState.supply alignedState.prevailing :=
      alignedSupplyEq.symm ▸ rawDerived
    refine ⟨.fn (.var initial.supply.nextTy)
        (.var (initial.supply.nextTy + 1)), finalDerived, rfl, ?_⟩
    simp only [alignedSupplyEq, alignedLedgerEq]
    exact DDSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned
  unfold DDSynthRun at baseRun ⊢
  simpa [finishExpr] using baseRun

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

/-- Compose function synthesis, exact function-shape alignment, and generic
argument checking into an application synthesis run. -/
theorem DDSynthRun.app
    {signature : FrozenSig} {context : Context}
    {function argument : Expr} {initial : InferState} {path : SyntaxPath}
    {functionResult : ExprResult} {functionAligned argumentFinal : InferState}
    (functionRun : DDSynthRun signature context function
      (visit initial .exprApp path) functionResult)
    (functionAlignRun : DDAlignTypesRun functionResult.target
      (.fn (applicationDomain functionResult path)
        (applicationResultTarget functionResult path))
      (applicationFreshState functionResult path) functionAligned)
    (argumentRun : DDCheckRun signature context argument
      (applicationDomain functionResult path) functionAligned argumentFinal) :
    DDSynthRun signature context (.app function argument) initial
      (finishExpr (.app function argument) path
        (applicationResultTarget functionResult path) argumentFinal) := by
  rcases functionRun with
    ⟨functionTarget, functionDerived, functionTargetEq, functionOrigin⟩
  rcases functionAlignRun with
    ⟨alignedSupplyEq, alignedLedgerEq, functionAlignedDD⟩
  unfold DDCheckRun at argumentRun
  rw [alignedSupplyEq, alignedLedgerEq] at argumentRun
  simp only [applicationFreshState_supply, applicationFreshState_capabilityOrigins,
    applicationDomain_eq] at argumentRun
  rcases argumentRun with ⟨argumentDerived, argumentOrigin⟩
  subst functionTarget
  change DDSynth signature initial.supply initial.prevailing context function
    functionResult.target functionResult.state.supply
      functionResult.state.prevailing at functionDerived
  change DDSynthOrigin signature functionDerived initial.capabilityOrigins
    functionResult.state.capabilityOrigins at functionOrigin
  simp only [applicationFreshState_capabilityOrigins,
    applicationFreshState_prevailing, applicationDomain_eq,
    applicationResultTarget_eq] at functionAlignedDD
  refine ⟨.var (functionResult.state.supply.nextTy + 1),
    DDSynth.app functionDerived functionAlignedDD.erase argumentDerived,
    ?_, ?_⟩
  · simp [finishExpr]
  · simpa [finishExpr] using
      DDSynthOrigin.app functionOrigin functionAlignedDD argumentOrigin

/-- Reconstruct a data-constructor result from exact pointwise argument
checking and the executable export freeze. -/
theorem DDSynthRun.ctor
    {signature : FrozenSig} {context : Context} {name : String}
    {expressions : List Expr} {scheme : CtorScheme}
    {initial childrenFinal : InferState} {path : SyntaxPath}
    (lookup : signature.findDataCtor name = some scheme)
    (childrenRun : DDChecksRun signature context expressions
      (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
      (instantiateCtorInState (visit initial .exprCtor path) scheme).2
      childrenFinal) :
    DDSynthRun signature context (.ctor name expressions) initial
      (finishExpr (.ctor name expressions) path
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
        (childrenFinal.freezeCapabilityExport
          (freshCapImages initial.supply scheme.capBinders)
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2)) := by
  rcases childrenRun with ⟨childrenDerived, childrenOrigin⟩
  simp only [instantiateCtorInState_supply,
    instantiateCtorInState_prevailing,
    instantiateCtorInState_capabilityOrigins, visit,
    InferState.recordEvent_supply, InferState.prevailing_recordEvent,
    InferState.recordEvent_capabilityOrigins] at childrenDerived childrenOrigin
  refine ⟨(InferenceBase.instantiateCtorScheme initial.supply scheme).value.2,
    DDSynth.ctor lookup childrenDerived, ?_, ?_⟩
  · rfl
  · simpa [finishExpr] using DDSynthOrigin.ctor lookup childrenOrigin

/-- Primitive application has the same instantiation, checking, and export
freeze boundary as a data constructor. -/
theorem DDSynthRun.prim
    {signature : FrozenSig} {context : Context} {op : PrimOp}
    {expressions : List Expr} {scheme : CtorScheme}
    {initial childrenFinal : InferState} {path : SyntaxPath}
    (lookup : signature.findPrimitive op = some scheme)
    (childrenRun : DDChecksRun signature context expressions
      (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
      (instantiateCtorInState (visit initial .exprPrim path) scheme).2
      childrenFinal) :
    DDSynthRun signature context (.prim op expressions) initial
      (finishExpr (.prim op expressions) path
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
        (childrenFinal.freezeCapabilityExport
          (freshCapImages initial.supply scheme.capBinders)
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2)) := by
  rcases childrenRun with ⟨childrenDerived, childrenOrigin⟩
  simp only [instantiateCtorInState_supply,
    instantiateCtorInState_prevailing,
    instantiateCtorInState_capabilityOrigins, visit,
    InferState.recordEvent_supply, InferState.prevailing_recordEvent,
    InferState.recordEvent_capabilityOrigins] at childrenDerived childrenOrigin
  refine ⟨(InferenceBase.instantiateCtorScheme initial.supply scheme).value.2,
    DDSynth.prim lookup childrenDerived, ?_, ?_⟩
  · rfl
  · simpa [finishExpr] using DDSynthOrigin.prim lookup childrenOrigin

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

/-- Successful empty checking-list traversal is the exact empty DD run. -/
theorem checkExprsFuel_nil_ddChecksRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {initial final : InferState}
    (success : checkExprsFuel (fuel + 1) signature context selfEnv parent index
      [] [] initial = some final) :
    DDChecksRun signature context [] [] initial final := by
  simp only [checkExprsFuel] at success
  have finalEq := Option.some.inj success
  subst final
  exact DDChecksRun.nil signature context initial

/-- The cons branch checks its synthesized head through the generic checking
bridge, then threads that exact terminal state into the tail list run. -/
theorem checkExprsFuel_cons_ddChecksRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {initial final : InferState}
    (headSound : ∀ synthesized : ExprResult,
      inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial = some synthesized →
      DDSynthRun signature context expression initial synthesized)
    (tailSound : ∀ (middle tailFinal : InferState),
      checkExprsFuel (fuel + 1) signature context selfEnv parent (index + 1)
        expressions expecteds middle = some tailFinal →
      DDChecksRun signature context expressions expecteds middle tailFinal)
    (success : checkExprsFuel (fuel + 2) signature context selfEnv parent index
      (expression :: expressions) (expected :: expecteds) initial =
        some final) :
    DDChecksRun signature context (expression :: expressions)
      (expected :: expecteds) initial final := by
  simp only [checkExprsFuel] at success
  cases headCheckEq : checkExprFuel (fuel + 1) signature context selfEnv
      (index :: parent) expression expected initial with
  | none => simp [headCheckEq] at success
  | some middle =>
      have tailEq : checkExprsFuel (fuel + 1) signature context selfEnv parent
          (index + 1) expressions expecteds middle = some final := by
        simpa [headCheckEq] using success
      cases headInferEq : inferExprFuel fuel signature context selfEnv
          (index :: parent) expression initial with
      | none => simp [checkExprFuel, headInferEq] at headCheckEq
      | some synthesized =>
          have headRun := checkExprFuel_ddCheckRun headInferEq
            (headSound synthesized headInferEq) headCheckEq
          exact DDChecksRun.cons headRun
            (tailSound middle final tailEq)

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
        ((name, NamedScheme.mono (lambdaDomain initial path)) :: context)
        (selfEnv.erase name) (0 :: path) body
        (lambdaEntryState initial path) = some bodyResult →
      DDSynthRun signature
        ((name, NamedScheme.mono (lambdaDomain initial path)) :: context) body
        (lambdaEntryState initial path) bodyResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lam name body) initial = some result) :
    DDSynthRun signature context (.lam name body) initial result := by
  cases bodyEq : inferExprFuel fuel signature
      ((name, NamedScheme.mono (lambdaDomain initial path)) :: context)
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

/-- The ordinary (non-matcher-literal) recursive branch reconstructs the
declarative gate, its two-fresh monomorphic placeholder, the exact recursive
body run, and the trailing codomain alignment. -/
theorem inferExprFuel_fix_nonMatcher_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {self argument : String}
    {body : Expr} {initial : InferState} {result : ExprResult}
    (nonMatcher : NonMatcherBody body)
    (bodySound : ∀ (bodyContext : Context) (bodySelfEnv : SelfEnv)
        (bodyInitial : InferState) (bodyResult : ExprResult),
      inferExprFuel fuel signature bodyContext bodySelfEnv (0 :: path) body
        bodyInitial = some bodyResult →
      DDSynthRun signature bodyContext body bodyInitial bodyResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.fix self argument body) initial = some result) :
    DDSynthRun signature context (.fix self argument body) initial result := by
  cases gate : (self != argument && DirectSelf.check self body) with
  | false => simp [inferExprFuel, gate] at success
  | true =>
      rcases (DirectSelf.fix_gate_eq_true self argument body).mp gate with
        ⟨distinct, direct⟩
      have placeholderEq := buildFixPlaceholder_nonMatcher signature initial
        path body nonMatcher
      cases bodyEq : inferExprFuel fuel signature
          ((argument, NamedScheme.mono (fixDomain initial path)) ::
            (self, NamedScheme.mono
              (.fn (fixDomain initial path) (fixCodomain initial path))) ::
              context)
          ((self, .fn (fixDomain initial path) (fixCodomain initial path)) ::
            selfEnv.eraseMany [self, argument])
          (0 :: path) body (fixBodyEntryState initial path self argument) with
      | none =>
          have actualPlaceholderEq := placeholderEq
          simp only [fixDomain, fixCodomain, fixFreshState]
            at actualPlaceholderEq
          have actualBodyEq := bodyEq
          simp only [fixDomain, fixCodomain, fixFreshState,
            fixBodyEntryState] at actualBodyEq
          simp [inferExprFuel, gate, actualPlaceholderEq, actualBodyEq]
            at success
      | some bodyResult =>
          have actualPlaceholderEq := placeholderEq
          simp only [fixDomain, fixCodomain, fixFreshState]
            at actualPlaceholderEq
          have actualBodyEq := bodyEq
          simp only [fixDomain, fixCodomain, fixFreshState,
            fixBodyEntryState] at actualBodyEq
          cases alignEq : alignTypes bodyResult.state
              (freshOrigin .recursiveBinder path "fix-result")
              bodyResult.target (fixCodomain initial path) with
          | none =>
              have actualAlignEq := alignEq
              simp only [fixCodomain] at actualAlignEq
              simp [inferExprFuel, gate, actualPlaceholderEq, actualBodyEq,
                actualAlignEq] at success
          | some alignedState =>
              have actualAlignEq := alignEq
              simp only [fixCodomain] at actualAlignEq
              have resultEq : finishExpr (.fix self argument body) path
                  (.fn (fixDomain initial path) (fixCodomain initial path))
                  alignedState = result := by
                apply Option.some.inj
                simpa [inferExprFuel, gate, actualPlaceholderEq, actualBodyEq,
                  actualAlignEq, fixDomain, fixCodomain] using success
              subst result
              exact DDSynthRun.fix distinct direct nonMatcher
                (bodySound _ _ _ bodyResult bodyEq)
                (alignTypes_ddAlignTypesRun alignEq)

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

/-- The application branch uses the function synthesis hypothesis, aligns it
with the two freshly allocated arrow indices, and checks the argument through
the generic expected-alignment theorem. -/
theorem inferExprFuel_app_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {function argument : Expr}
    {initial : InferState} {result : ExprResult}
    (functionSound : ∀ functionResult : ExprResult,
      inferExprFuel fuel signature context selfEnv (0 :: path) function
        (visit initial .exprApp path) = some functionResult →
      DDSynthRun signature context function (visit initial .exprApp path)
        functionResult)
    (argumentSound : ∀ (argumentInitial : InferState)
        (argumentResult : ExprResult),
      inferExprFuel fuel signature context selfEnv (1 :: path) argument
        argumentInitial = some argumentResult →
      DDSynthRun signature context argument argumentInitial argumentResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.app function argument) initial = some result) :
    DDSynthRun signature context (.app function argument) initial result := by
  cases functionEq : inferExprFuel fuel signature context selfEnv (0 :: path)
      function (visit initial .exprApp path) with
  | none => simp [inferExprFuel, functionEq] at success
  | some functionResult =>
      cases functionAlignEq : alignTypes
          (applicationFreshState functionResult path)
          (freshOrigin .expression path "application-function")
          functionResult.target
          (.fn (applicationDomain functionResult path)
            (applicationResultTarget functionResult path)) with
      | none =>
          have actualFunctionAlignEq := functionAlignEq
          simp only [applicationDomain, applicationResultTarget,
            applicationFreshState] at actualFunctionAlignEq
          simp [inferExprFuel, functionEq, actualFunctionAlignEq] at success
      | some functionAligned =>
          have actualFunctionAlignEq := functionAlignEq
          simp only [applicationDomain, applicationResultTarget,
            applicationFreshState] at actualFunctionAlignEq
          cases argumentEq : inferExprFuel fuel signature context selfEnv
              (1 :: path) argument functionAligned with
          | none =>
              simp [inferExprFuel, functionEq, actualFunctionAlignEq,
                argumentEq] at success
          | some argumentResult =>
              cases argumentAlignEq : alignExprResultAtExpected (1 :: path)
                  argumentResult (applicationDomain functionResult path) with
              | none =>
                  have actualArgumentAlignEq := argumentAlignEq
                  simp only [applicationDomain] at actualArgumentAlignEq
                  simp [inferExprFuel, functionEq, actualFunctionAlignEq,
                    argumentEq, actualArgumentAlignEq] at success
              | some argumentFinal =>
                  have actualArgumentAlignEq := argumentAlignEq
                  simp only [applicationDomain] at actualArgumentAlignEq
                  have resultEq : finishExpr (.app function argument) path
                      (applicationResultTarget functionResult path)
                      argumentFinal = result := by
                    apply Option.some.inj
                    simpa [inferExprFuel, functionEq, actualFunctionAlignEq,
                      argumentEq, actualArgumentAlignEq,
                      applicationResultTarget] using success
                  subst result
                  have argumentCheckSuccess :
                      checkExprFuel (fuel + 1) signature context selfEnv
                        (1 :: path) argument
                        (applicationDomain functionResult path)
                        functionAligned = some argumentFinal := by
                    simpa [checkExprFuel, argumentEq] using argumentAlignEq
                  have argumentRun := checkExprFuel_ddCheckRun argumentEq
                    (argumentSound functionAligned argumentResult argumentEq)
                    argumentCheckSuccess
                  exact DDSynthRun.app
                    (functionSound functionResult functionEq)
                    (alignTypes_ddAlignTypesRun functionAlignEq) argumentRun

/-- A successful constructor branch instantiates its scheme, checks all
arguments, freezes the exported result leaves, and reconstructs `DDSynth.ctor`. -/
theorem inferExprFuel_ctor_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {expressions : List Expr} {initial : InferState} {result : ExprResult}
    (childrenSound : ∀ (scheme : CtorScheme) (childrenFinal : InferState),
      checkExprsFuel fuel signature context selfEnv path 0 expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprCtor path) scheme).2 =
          some childrenFinal →
      DDChecksRun signature context expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprCtor path) scheme).2
        childrenFinal)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.ctor name expressions) initial = some result) :
    DDSynthRun signature context (.ctor name expressions) initial result := by
  cases lookup : signature.findDataCtor name with
  | none => simp [inferExprFuel, lookup] at success
  | some scheme =>
      cases childrenEq : checkExprsFuel fuel signature context selfEnv path 0
          expressions
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
          (instantiateCtorInState (visit initial .exprCtor path) scheme).2 with
      | none =>
          have actualChildrenEq := childrenEq
          simp only [visit] at actualChildrenEq
          simp [inferExprFuel, lookup, visit, actualChildrenEq] at success
      | some childrenFinal =>
          have actualChildrenEq := childrenEq
          simp only [visit] at actualChildrenEq
          have resultEq : finishExpr (.ctor name expressions) path
              (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
              (childrenFinal.freezeCapabilityExport
                (freshCapImages initial.supply scheme.capBinders)
                (InferenceBase.instantiateCtorScheme initial.supply
                  scheme).value.2) = result := by
            apply Option.some.inj
            simpa [inferExprFuel, lookup, visit, actualChildrenEq] using success
          subst result
          exact DDSynthRun.ctor lookup
            (childrenSound scheme childrenFinal childrenEq)

/-- Primitive synthesis shares the constructor instantiation/check/freeze
pipeline and reconstructs `DDSynth.prim`. -/
theorem inferExprFuel_prim_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {op : PrimOp}
    {expressions : List Expr} {initial : InferState} {result : ExprResult}
    (childrenSound : ∀ (scheme : CtorScheme) (childrenFinal : InferState),
      checkExprsFuel fuel signature context selfEnv path 0 expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprPrim path) scheme).2 =
          some childrenFinal →
      DDChecksRun signature context expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprPrim path) scheme).2
        childrenFinal)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.prim op expressions) initial = some result) :
    DDSynthRun signature context (.prim op expressions) initial result := by
  cases lookup : signature.findPrimitive op with
  | none => simp [inferExprFuel, lookup] at success
  | some scheme =>
      cases childrenEq : checkExprsFuel fuel signature context selfEnv path 0
          expressions
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
          (instantiateCtorInState (visit initial .exprPrim path) scheme).2 with
      | none =>
          have actualChildrenEq := childrenEq
          simp only [visit] at actualChildrenEq
          simp [inferExprFuel, lookup, visit, actualChildrenEq] at success
      | some childrenFinal =>
          have actualChildrenEq := childrenEq
          simp only [visit] at actualChildrenEq
          have resultEq : finishExpr (.prim op expressions) path
              (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
              (childrenFinal.freezeCapabilityExport
                (freshCapImages initial.supply scheme.capBinders)
                (InferenceBase.instantiateCtorScheme initial.supply
                  scheme).value.2) = result := by
            apply Option.some.inj
            simpa [inferExprFuel, lookup, visit, actualChildrenEq] using success
          subst result
          exact DDSynthRun.prim lookup
            (childrenSound scheme childrenFinal childrenEq)

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

/-! ## User-pattern reconstruction slices -/

/-- The empty executable pattern-list traversal is the exact nil DD run. -/
theorem inferPatternsFuel_nil_ddPatternsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {initial : InferState}
    {result : PatternsResult}
    (success : inferPatternsFuel (fuel + 1) signature context parameters
      bindings selfEnv parent index [] initial = some result) :
    DDPatternsRun signature context parameters bindings [] initial result := by
  simp only [inferPatternsFuel, Option.some.injEq] at success
  subst result
  exact DDPatternsRun.nil signature context parameters bindings initial

/-- The executable pattern-list cons branch is exactly the left-to-right DD
composition of its head and tail induction hypotheses. -/
theorem inferPatternsFuel_cons_ddPatternsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {pattern : Pattern}
    {patterns : List Pattern} {initial : InferState}
    {result : PatternsResult}
    (headSound : ∀ head : PatternResult,
      inferPatternFuel fuel signature context parameters bindings selfEnv
        (index :: parent) pattern initial = some head →
      DDPatternRun signature context parameters bindings pattern initial head)
    (tailSound : ∀ (head : PatternResult) (tail : PatternsResult),
      inferPatternsFuel fuel signature context parameters head.bindings
        selfEnv parent (index + 1) patterns head.state = some tail →
      DDPatternsRun signature context parameters head.bindings patterns
        head.state tail)
    (success : inferPatternsFuel (fuel + 1) signature context parameters
      bindings selfEnv parent index (pattern :: patterns) initial =
        some result) :
    DDPatternsRun signature context parameters bindings (pattern :: patterns)
      initial result := by
  simp only [inferPatternsFuel] at success
  cases headEq : inferPatternFuel fuel signature context parameters bindings
      selfEnv (index :: parent) pattern initial with
  | none => simp [headEq] at success
  | some head =>
      cases tailEq : inferPatternsFuel fuel signature context parameters
          head.bindings selfEnv parent (index + 1) patterns head.state with
      | none => simp [headEq, tailEq] at success
      | some tail =>
          simp only [headEq, tailEq, Option.some.injEq] at success
          subst result
          exact DDPatternsRun.cons (headSound head headEq)
            (tailSound head tail tailEq)

/-- A successful pattern-variable leaf reconstructs its two fresh indices,
binding extension, and single structural capability-origin update exactly. -/
theorem inferPatternFuel_pvar_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {initial : InferState}
    {result : PatternResult}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pvar name) initial = some result) :
    DDPatternRun signature context parameters bindings (.pvar name) initial
      result := by
  simp only [inferPatternFuel] at success
  split at success
  · contradiction
  · rename_i absent
    have resultEq := Option.some.inj success
    subst result
    have freshName : name ∉ bindings.names := by
      simpa using absent
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.pvar name)
          ⟨.var ⟨initial.supply.nextCap⟩, .var initial.supply.nextTy⟩
          (bindings ++ [(name, .var initial.supply.nextTy)])
          { initial.supply with
            nextCap := initial.supply.nextCap + 1
            nextTy := initial.supply.nextTy + 1 }
          initial.prevailing,
      DDPatternOrigin signature derived initial.capabilityOrigins
        (DDLedger.markFreshCap initial.capabilityOrigins initial.supply)
    exact ⟨DDPattern.pvar freshName,
      DDPatternOrigin.pvar (signature := signature)
        (q := initial.supply) (S := initial.prevailing) (context := context)
        (parameters := parameters) (bindings := bindings)
        (ledger := initial.capabilityOrigins) freshName⟩

/-- A successful wildcard leaf has the same exact fresh-state transition as
`pvar`, without extending the binding context. -/
theorem inferPatternFuel_wild_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {initial : InferState} {result : PatternResult}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path .wild initial = some result) :
    DDPatternRun signature context parameters bindings .wild initial result := by
  simp only [inferPatternFuel, Option.some.injEq] at success
  subst result
  change ∃ derived : DDPattern signature initial.supply initial.prevailing
      context parameters bindings .wild
        ⟨.var ⟨initial.supply.nextCap⟩, .var initial.supply.nextTy⟩ bindings
        { initial.supply with
          nextCap := initial.supply.nextCap + 1
          nextTy := initial.supply.nextTy + 1 }
        initial.prevailing,
    DDPatternOrigin signature derived initial.capabilityOrigins
      (DDLedger.markFreshCap initial.capabilityOrigins initial.supply)
  exact ⟨DDPattern.wild, DDPatternOrigin.wild⟩

/-- Value-pattern synthesis reuses the exact expression run and records the
single fresh consumer capability at the expression's output cut. -/
theorem inferPatternFuel_pval_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {initial : InferState}
    {result : PatternResult}
    (expressionSound : ∀ expressionResult : ExprResult,
      inferExprFuel fuel signature (bindings.toContext ++ context) selfEnv
        (0 :: path) expression (visit initial .patternValue path) =
          some expressionResult →
      DDSynthRun signature (bindings.toContext ++ context) expression
        (visit initial .patternValue path) expressionResult)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pval expression) initial = some result) :
    DDPatternRun signature context parameters bindings (.pval expression)
      initial result := by
  cases expressionEq : inferExprFuel fuel signature
      (bindings.toContext ++ context) selfEnv (0 :: path) expression
      (visit initial .patternValue path) with
  | none => simp [inferPatternFuel, expressionEq] at success
  | some expressionResult =>
      simp only [inferPatternFuel, expressionEq, Option.some.injEq] at success
      subst result
      rcases expressionSound expressionResult expressionEq with
        ⟨rawTarget, expressionDerived, targetEq, expressionOrigin⟩
      subst rawTarget
      simp only [visit, InferState.recordEvent_supply,
        InferState.prevailing_recordEvent,
        InferState.recordEvent_capabilityOrigins] at expressionDerived expressionOrigin
      change ∃ derived : DDPattern signature initial.supply
          initial.prevailing context parameters bindings (.pval expression)
          ⟨.var ⟨expressionResult.state.supply.nextCap⟩,
            expressionResult.target⟩ bindings
          { expressionResult.state.supply with
            nextCap := expressionResult.state.supply.nextCap + 1 }
          expressionResult.state.prevailing,
        DDPatternOrigin signature derived initial.capabilityOrigins
          (DDLedger.markFreshCap expressionResult.state.capabilityOrigins
            expressionResult.state.supply)
      exact ⟨DDPattern.pval expressionDerived,
        DDPatternOrigin.pval (parameters := parameters) expressionOrigin⟩

/-- A successful parameter embedding performs no allocation or solve, so its
lookup directly gives the exact DD pattern and origin certificates. -/
theorem inferPatternFuel_embed_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {initial : InferState}
    {result : PatternResult}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.embed name) initial = some result) :
    DDPatternRun signature context parameters bindings (.embed name) initial
      result := by
  cases lookup : parameters.find? name with
  | none => simp [inferPatternFuel, lookup] at success
  | some dual =>
      simp only [inferPatternFuel, lookup, Option.some.injEq] at success
      subst result
      change ∃ derived : DDPattern signature initial.supply
          initial.prevailing context parameters bindings (.embed name) dual
          bindings initial.supply initial.prevailing,
        DDPatternOrigin signature derived initial.capabilityOrigins
          initial.capabilityOrigins
      exact ⟨DDPattern.embed lookup,
        DDPatternOrigin.embed (signature := signature)
          (q := initial.supply) (S := initial.prevailing) (context := context)
          (parameters := parameters) (bindings := bindings)
          (ledger := initial.capabilityOrigins) lookup⟩

/-- Tuple-pattern synthesis is the direct image of its exact list traversal;
the trailing trace event changes none of the DD indices. -/
theorem inferPatternFuel_ptuple_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {patterns : List Pattern} {initial : InferState}
    {result : PatternResult}
    (childrenSound : ∀ children : PatternsResult,
      inferPatternsFuel fuel signature context parameters bindings selfEnv
        path 0 patterns (visit initial .patternTuple path) = some children →
      DDPatternsRun signature context parameters bindings patterns
        (visit initial .patternTuple path) children)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.ptuple patterns) initial = some result) :
    DDPatternRun signature context parameters bindings (.ptuple patterns)
      initial result := by
  cases childrenEq : inferPatternsFuel fuel signature context parameters
      bindings selfEnv path 0 patterns (visit initial .patternTuple path) with
  | none => simp [inferPatternFuel, childrenEq] at success
  | some children =>
      simp only [inferPatternFuel, childrenEq, Option.some.injEq] at success
      subst result
      rcases childrenSound children childrenEq with
        ⟨childrenDerived, childrenOrigin⟩
      simp only [visit, InferState.recordEvent_supply,
        InferState.prevailing_recordEvent,
        InferState.recordEvent_capabilityOrigins] at childrenDerived childrenOrigin
      change ∃ derived : DDPattern signature initial.supply
          initial.prevailing context parameters bindings (.ptuple patterns)
          ⟨.prod (children.duals.map Dual.cap),
            .prod (children.duals.map Dual.target)⟩ children.bindings
          children.state.supply children.state.prevailing,
        DDPatternOrigin signature derived initial.capabilityOrigins
          children.state.capabilityOrigins
      exact ⟨DDPattern.ptuple childrenDerived,
        DDPatternOrigin.ptuple childrenOrigin⟩

end Inference
end TypePM
