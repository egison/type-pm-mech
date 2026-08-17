import TypePM.InferenceLedgerAdmissibility

/-!
# Per-solve origin admissibility

Every chronological solver step stores the capability-origin ledger observed
at its own solve cut.  This module records the trace invariant that the step's
paired delta is admissible for that stored snapshot.  Event, source, and export
updates leave the solve history unchanged; a solver update extends the
invariant with the admissibility theorem of its newly returned step.
-/

namespace TypePM
namespace Inference

/-- One solver step respects the origin ledger captured at its solve cut. -/
def SolveStep.LedgerAdmissible (step : SolveStep) : Prop :=
  AdmissiblePost step.ledgerSnapshot step.delta

/-- Every step in a chronological solve list respects its own snapshot. -/
def LedgerAdmissibleSteps (steps : List SolveStep) : Prop :=
  ∀ step, step ∈ steps → step.LedgerAdmissible

/-- Per-solve ledger admissibility for an inference state's whole trace. -/
def InferState.AdmissibleTrace (state : InferState) : Prop :=
  LedgerAdmissibleSteps state.trace.solves

/-- The empty inference state has no solver steps to audit. -/
theorem InferState.admissibleTrace_empty
    (supply : InferenceBase.FreshSupply :=
      InferenceBase.FreshSupply.empty) :
    (InferState.empty supply).AdmissibleTrace := by
  intro step membership
  simp [InferState.empty] at membership

/-- Recording a reconstruction event does not alter solve admissibility. -/
theorem InferState.AdmissibleTrace.recordEvent
    {state : InferState} (admissible : state.AdmissibleTrace)
    (event : TraceEvent) :
    (state.recordEvent event).AdmissibleTrace := by
  simpa [InferState.AdmissibleTrace, LedgerAdmissibleSteps,
    InferState.recordEvent] using admissible

/-- Recording a provenance source does not alter solve admissibility. -/
theorem InferState.AdmissibleTrace.recordSource
    {state : InferState} (admissible : state.AdmissibleTrace)
    (source : ProducerSource) :
    (state.recordSource source).AdmissibleTrace := by
  simpa [InferState.AdmissibleTrace, LedgerAdmissibleSteps,
    InferState.recordSource] using admissible

/-- Final matcher protection changes ledgers but no stored solve snapshot. -/
theorem InferState.AdmissibleTrace.protectMatcherCapability
    {state : InferState} (admissible : state.AdmissibleTrace)
    (capability : Cap) :
    (state.protectMatcherCapability capability).AdmissibleTrace := by
  simpa [InferState.AdmissibleTrace, LedgerAdmissibleSteps] using admissible

/-- Selective matcher protection also leaves all stored solve snapshots
unchanged. -/
theorem InferState.AdmissibleTrace.protectMatcherCapabilityExcept
    {state : InferState} (admissible : state.AdmissibleTrace)
    (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).AdmissibleTrace := by
  simpa [InferState.AdmissibleTrace, LedgerAdmissibleSteps] using admissible

/-- Export freezing appends an event and changes only current producer ledgers;
all earlier solve snapshots remain unchanged. -/
theorem InferState.AdmissibleTrace.freezeCapabilityExport
    {state : InferState} (admissible : state.AdmissibleTrace)
    (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).AdmissibleTrace := by
  simpa [InferState.AdmissibleTrace, LedgerAdmissibleSteps,
    InferState.freezeCapabilityExport, InferState.recordEvent] using admissible

/-- Appending one independently admissible solver step preserves the trace
invariant. -/
theorem InferState.AdmissibleTrace.recordSolve
    {state : InferState} (admissible : state.AdmissibleTrace)
    (step : SolveStep) (stepAdmissible : step.LedgerAdmissible) :
    (state.recordSolve step).AdmissibleTrace := by
  intro candidate membership
  simp only [InferState.recordSolve, List.mem_append, List.mem_singleton] at membership
  rcases membership with previous | latest
  · exact admissible candidate previous
  · subst candidate
    exact stepAdmissible

/-! ## Solver results carry their own snapshot -/

/-- A successful ledger-aware local solve stores precisely the ledger supplied
to that solve call. -/
theorem solveResolvedWithLedger_ledgerSnapshot
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    step.ledgerSnapshot = ledger := by
  cases constraint with
  | capEq left right =>
      change solveCapEqWithLedger ledger solveCount origin left right =
        some step at success
      unfold solveCapEqWithLedger at success
      split at success
      · contradiction
      · have stepEquation := Option.some.inj success
        subst step
        rfl
  | targetEq left right =>
      change solveTargetEqWithLedger ledger solveCount origin left right =
        some step at success
      unfold solveTargetEqWithLedger at success
      split at success
      · contradiction
      · have stepEquation := Option.some.inj success
        subst step
        rfl
  | producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      change solveProducerToSlotWithLedger ledger solveCount origin producerCap
          producerTarget consumerCap consumerTarget = some step at success
      unfold solveProducerToSlotWithLedger at success
      split at success
      · contradiction
      · simp only at success
        split at success
        · split at success
          · contradiction
          · have stepEquation := Option.some.inj success
            subst step
            rfl
        · contradiction

/-- A successful local solve is admissible for the snapshot stored in the
returned step itself. -/
theorem solveResolvedWithLedger_stepLedgerAdmissible
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    step.LedgerAdmissible := by
  unfold SolveStep.LedgerAdmissible
  rw [solveResolvedWithLedger_ledgerSnapshot success]
  exact solveResolvedWithLedger_admissible success

/-! ## Single-constraint preservation -/

/-- Running an already-resolved constraint appends one snapshot-admissible
step on every successful path. -/
theorem runResolvedConstraint_admissibleTrace
    {state result : InferState} (admissible : state.AdmissibleTrace)
    {origin : ConstraintOrigin} {constraint : Constraint}
    (success : runResolvedConstraint state origin constraint = some result) :
    result.AdmissibleTrace := by
  unfold runResolvedConstraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      have stepAdmissible :=
        solveResolvedWithLedger_stepLedgerAdmissible stepEquation
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          have resultEquation := Option.some.inj success
          subst result
          exact admissible.recordSolve step stepAdmissible
      | producerToSlot _ _ _ _ =>
          change (if capSubstSafeVarsCheck state.capabilityOrigins
              step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have resultEquation := Option.some.inj success
          subst result
          exact admissible.recordSolve step stepAdmissible

/-- Resolving and running a raw constraint likewise appends one
snapshot-admissible step on every successful path. -/
theorem runConstraint_admissibleTrace
    {state result : InferState} (admissible : state.AdmissibleTrace)
    {origin : ConstraintOrigin} {raw : Constraint}
    (success : runConstraint state origin raw = some result) :
    result.AdmissibleTrace := by
  unfold runConstraint at success
  generalize constraintEquation : raw.resolve state.prevailing = constraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      have stepAdmissible :=
        solveResolvedWithLedger_stepLedgerAdmissible stepEquation
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          have resultEquation := Option.some.inj success
          subst result
          exact admissible.recordSolve step stepAdmissible
      | producerToSlot _ _ _ _ =>
          change (if capSubstSafeVarsCheck state.capabilityOrigins
              step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have resultEquation := Option.some.inj success
          subst result
          exact admissible.recordSolve step stepAdmissible

/-! ## History suffixes -/

/-- Ledger admissibility distributes over chronological list append. -/
theorem ledgerAdmissibleSteps_append
    {front tail : List SolveStep}
    (frontAdmissible : LedgerAdmissibleSteps front)
    (tailAdmissible : LedgerAdmissibleSteps tail) :
    LedgerAdmissibleSteps (front ++ tail) := by
  intro step membership
  simp only [List.mem_append] at membership
  exact membership.elim (frontAdmissible step) (tailAdmissible step)

/-- Restricting an admissible final trace to any chronological history prefix
preserves the invariant. -/
theorem InferState.AdmissibleTrace.of_historyPrefix
    {earlier later : InferState} (laterAdmissible : later.AdmissibleTrace)
    (history : earlier.HistoryPrefix later) :
    earlier.AdmissibleTrace := by
  rcases history with
    ⟨solveSuffix, _eventSuffix, solveEquation, _eventEquation⟩
  intro step membership
  apply laterAdmissible step
  rw [solveEquation]
  exact List.mem_append_left solveSuffix membership

/-- An admissible prefix plus an admissible chronological solve suffix yields
an admissible extended trace. -/
theorem InferState.AdmissibleTrace.extend_historySuffix
    {earlier later : InferState} (earlierAdmissible : earlier.AdmissibleTrace)
    (history : earlier.HistoryPrefix later)
    (suffixAdmissible : ∀ solveSuffix,
      later.trace.solves = earlier.trace.solves ++ solveSuffix →
        LedgerAdmissibleSteps solveSuffix) :
    later.AdmissibleTrace := by
  rcases history with
    ⟨solveSuffix, _eventSuffix, solveEquation, _eventEquation⟩
  change LedgerAdmissibleSteps later.trace.solves
  rw [solveEquation]
  exact ledgerAdmissibleSteps_append earlierAdmissible
    (suffixAdmissible solveSuffix solveEquation)

end Inference
end TypePM
