import TypePM.InferenceLocalFactorization

/-!
# Scoped factorization of chronological solve traces

Local factorization cannot be iterated from per-step admissibility alone.  The
residual left after factoring one delta must itself be admissible for the next
step's ledger snapshot and solve that next already-resolved constraint.  This
module makes that changing residual explicit and proves the safe one-step
extension used to build a prefix or suffix argument.
-/

namespace TypePM
namespace Inference

/-- `competitor` factors through the chronological replay of `steps`, leaving
`residual` to act after the entire replay. -/
def TraceFactorization
    (steps : List SolveStep) (competitor residual : Subst) : Prop :=
  competitor = Subst.seq residual (replay steps)

/-- The empty trace leaves the competitor itself as residual. -/
@[simp] theorem traceFactorization_nil (competitor : Subst) :
    TraceFactorization [] competitor competitor := by
  simp [TraceFactorization, replay, replayFrom]

/-- Algebraic core of one-step extension.  No solver property is hidden here:
the premise is exactly the local delta factorization needed for the new
chronological step. -/
theorem TraceFactorization.snoc_of_deltaFactorization
    {steps : List SolveStep} {step : SolveStep}
    {competitor currentResidual nextResidual : Subst}
    (prior : TraceFactorization steps competitor currentResidual)
    (deltaEquation :
      currentResidual = Subst.seq nextResidual step.delta) :
    TraceFactorization (steps ++ [step]) competitor nextResidual := by
  unfold TraceFactorization at prior ⊢
  rw [replay_snoc]
  calc
    competitor = Subst.seq currentResidual (replay steps) := prior
    _ = Subst.seq (Subst.seq nextResidual step.delta) (replay steps) := by
      rw [deltaEquation]
    _ = Subst.seq nextResidual
          (Subst.seq step.delta (replay steps)) :=
      (PhasedPost.seq_assoc nextResidual step.delta (replay steps)).symm

/-- Safe scoped append theorem.  The residual of the prefix, rather than the
original competitor, is checked at the new step's exact snapshot and resolved
constraint. -/
theorem TraceFactorization.snoc
    {steps : List SolveStep} {step : SolveStep}
    {competitor currentResidual : Subst}
    (prior : TraceFactorization steps competitor currentResidual)
    (localFactorization : step.HasLocalFactorization)
    (currentAdmissible :
      AdmissiblePost step.ledgerSnapshot currentResidual)
    (currentSound : step.constraint.SolvedBy currentResidual) :
    ∃ nextResidual : Subst,
      AdmissiblePost step.ledgerSnapshot nextResidual ∧
        TraceFactorization (steps ++ [step]) competitor nextResidual := by
  obtain ⟨nextResidual, nextAdmissible, localEquation⟩ :=
    localFactorization currentResidual currentAdmissible currentSound
  exact ⟨nextResidual, nextAdmissible,
    TraceFactorization.snoc_of_deltaFactorization prior localEquation⟩

/-- Solver-specific append theorem.  A successful ledger-aware solve supplies
the safe local factorization, while the caller supplies the scope facts for
the prefix residual at the call ledger and resolved constraint. -/
theorem TraceFactorization.snoc_solveResolvedWithLedger
    {steps : List SolveStep} {competitor currentResidual : Subst}
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (prior : TraceFactorization steps competitor currentResidual)
    (stepSuccess : solveResolvedWithLedger ledger solveCount origin constraint =
      some step)
    (currentAdmissible : AdmissiblePost ledger currentResidual)
    (currentSound : constraint.SolvedBy currentResidual) :
    ∃ nextResidual : Subst,
      AdmissiblePost ledger nextResidual ∧
        TraceFactorization (steps ++ [step]) competitor nextResidual := by
  obtain ⟨nextResidual, nextAdmissible, localEquation⟩ :=
    solveResolvedWithLedger_factorization stepSuccess currentAdmissible
      currentSound
  exact ⟨nextResidual, nextAdmissible,
    TraceFactorization.snoc_of_deltaFactorization prior localEquation⟩

/-! ## State-level packaging -/

/-- Scoped factorization through the solve history currently stored in a
state.  The residual is intentionally an explicit parameter: later solve cuts
must audit that residual against their own snapshots. -/
def InferState.ScopedTraceFactorization
    (state : InferState) (competitor residual : Subst) : Prop :=
  TraceFactorization state.trace.solves competitor residual

/-- Empty inference history has the canonical scoped factorization. -/
@[simp] theorem InferState.scopedTraceFactorization_empty
    (supply : InferenceBase.FreshSupply) (competitor : Subst) :
    (InferState.empty supply).ScopedTraceFactorization competitor competitor := by
  simp [InferState.ScopedTraceFactorization, InferState.empty]

/-- Recording a locally factorizing step extends a state-level scoped
factorization by exactly one chronological solve. -/
theorem InferState.ScopedTraceFactorization.recordSolve
    {state : InferState} {step : SolveStep}
    {competitor currentResidual : Subst}
    (prior : state.ScopedTraceFactorization competitor currentResidual)
    (localFactorization : step.HasLocalFactorization)
    (currentAdmissible :
      AdmissiblePost step.ledgerSnapshot currentResidual)
    (currentSound : step.constraint.SolvedBy currentResidual) :
    ∃ nextResidual : Subst,
      AdmissiblePost step.ledgerSnapshot nextResidual ∧
        (state.recordSolve step).ScopedTraceFactorization
          competitor nextResidual := by
  obtain ⟨nextResidual, nextAdmissible, extended⟩ :=
    TraceFactorization.snoc prior localFactorization currentAdmissible
      currentSound
  refine ⟨nextResidual, nextAdmissible, ?_⟩
  simpa [InferState.ScopedTraceFactorization, InferState.recordSolve] using
    extended

/-- State-level form specialized to a step returned by the ledger-aware
solver. -/
theorem InferState.ScopedTraceFactorization.recordSolve_solved
    {state : InferState} {competitor currentResidual : Subst}
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (prior : state.ScopedTraceFactorization competitor currentResidual)
    (stepSuccess : solveResolvedWithLedger ledger solveCount origin constraint =
      some step)
    (currentAdmissible : AdmissiblePost ledger currentResidual)
    (currentSound : constraint.SolvedBy currentResidual) :
    ∃ nextResidual : Subst,
      AdmissiblePost ledger nextResidual ∧
        (state.recordSolve step).ScopedTraceFactorization
          competitor nextResidual := by
  obtain ⟨nextResidual, nextAdmissible, extended⟩ :=
    TraceFactorization.snoc_solveResolvedWithLedger prior stepSuccess
      currentAdmissible currentSound
  refine ⟨nextResidual, nextAdmissible, ?_⟩
  simpa [InferState.ScopedTraceFactorization, InferState.recordSolve] using
    extended

/-- A successful already-resolved constraint run extends scoped trace
factorization by its single emitted step.  The protection audit in the
producer branch affects success, but not the factorization once the step has
been accepted. -/
theorem runResolvedConstraint_scopedTraceFactorization
    {state result : InferState} {competitor currentResidual : Subst}
    {origin : ConstraintOrigin} {constraint : Constraint}
    (prior : state.ScopedTraceFactorization competitor currentResidual)
    (currentAdmissible :
      AdmissiblePost state.capabilityOrigins currentResidual)
    (currentSound : constraint.SolvedBy currentResidual)
    (success : runResolvedConstraint state origin constraint = some result) :
    ∃ nextResidual : Subst,
      AdmissiblePost state.capabilityOrigins nextResidual ∧
        result.ScopedTraceFactorization competitor nextResidual := by
  unfold runResolvedConstraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      have extended := prior.recordSolve_solved stepEquation
        currentAdmissible currentSound
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          have resultEquation := Option.some.inj success
          subst result
          exact extended
      | producerToSlot _ _ _ _ =>
          change (if capSubstFixesVarsCheck step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have resultEquation := Option.some.inj success
          subst result
          exact extended

/-- Raw constraint execution has the same scoped theorem after resolving the
constraint at the state's complete chronological prefix. -/
theorem runConstraint_scopedTraceFactorization
    {state result : InferState} {competitor currentResidual : Subst}
    {origin : ConstraintOrigin} {raw : Constraint}
    (prior : state.ScopedTraceFactorization competitor currentResidual)
    (currentAdmissible :
      AdmissiblePost state.capabilityOrigins currentResidual)
    (currentSound :
      (raw.resolve state.prevailing).SolvedBy currentResidual)
    (success : runConstraint state origin raw = some result) :
    ∃ nextResidual : Subst,
      AdmissiblePost state.capabilityOrigins nextResidual ∧
        result.ScopedTraceFactorization competitor nextResidual := by
  change runResolvedConstraint state origin (raw.resolve state.prevailing) =
    some result at success
  exact runResolvedConstraint_scopedTraceFactorization prior
    currentAdmissible currentSound success

end Inference
end TypePM
