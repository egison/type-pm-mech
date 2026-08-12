import TypePM.DemandTyping

/-!
# Solver correspondence for inference completeness

An exact DD witness and the executable paired MGU need not be equal.  The
constraint `α = β`, for example, admits the two solved orientations
`[α ↦ β]` and `[β ↦ α]`.  Requiring literal equality, or choosing a canonical
orientation in the declarative judgment, would therefore be the wrong bridge
for inference completeness.

The traversal needs a weaker and more useful triangle.  The origin-safe DD
solution is an admissible competitor of the executable kernel, so relative
universality says that it *absorbs* the executable result.  Conversely, global
most-generality of the DD witness makes the executable result an instance of
it.  Thus inserting the executable solve before the DD residual leaves every
subsequent normalized type, and the complete prevailing state, unchanged.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessSolver

open Inference

/-- The state-level relation between one origin-safe exact DD solution and
the executable result for the same already-resolved paired constraint. -/
structure PairedStateCorrespondence
    (declarative executable : Subst) : Prop where
  /-- Replaying the executable delta before the declarative residual is
  observationally the same declarative state. -/
  declarativeAbsorbsExecutable :
    declarative = Subst.seq declarative executable
  /-- The executable result is also an instance of the declarative MGU.
  This direction is global; its residual need not satisfy the current origin
  ledger because traversal completeness uses the absorption direction. -/
  executableFactorsThroughDeclarative :
    ∃ residual, executable = Subst.seq residual declarative

/-- Two proof-carrying MGUs of the same constraint have the state
correspondence needed by traversal completeness.  No equality or canonical
orientation premise is required. -/
theorem pairedResult_correspondence
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {declarative : Subst}
    (dd : OriginSafeExactPairedMGU ledger left right declarative)
    (executable : PairedUnification.PairedResult ledger left right) :
    PairedStateCorrespondence declarative executable.subst := by
  refine ⟨?_, ?_⟩
  · exact executable.universal declarative dd.admissible dd.exact.1.1
  · exact dd.exact.1.2 executable.subst executable.sound

/-- Public-wrapper form of `pairedResult_correspondence`. -/
theorem mguPairedTy_correspondence
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {declarative executable : Subst}
    (dd : OriginSafeExactPairedMGU ledger left right declarative)
    (success : PairedUnification.mguPairedTy ledger left right =
      some executable) :
    PairedStateCorrespondence declarative executable := by
  unfold PairedUnification.mguPairedTy at success
  cases run : PairedUnification.solvePairedTy
      (PairedUnification.mguPairedTyCompleteFuel ledger left right)
      ledger left right with
  | none => simp [run] at success
  | some result =>
      have executableEq : result.subst = executable := by
        simpa [run] using success
      subst executable
      exact pairedResult_correspondence dd result

/-! ## Concrete executable steps -/

/-- An origin-admissible capability solution makes the executable
capability-equality solver emit a proof-carrying step. -/
theorem solveCapEqWithLedger_complete_of_admissible
    {ledger : CapabilityOriginLedger} {left right : Cap}
    {competitor : CapSubst}
    (competitorAdmissible : AdmissibleCapPost ledger competitor)
    (competitorSound : left.apply competitor = right.apply competitor)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    ∃ (result : PairedUnification.OrientedCapResult ledger left right)
        (step : SolveStep),
      solveCapEqWithLedger ledger solveCount origin left right = some step ∧
        step.delta = ⟨result.subst, TySubst.id⟩ := by
  unfold solveCapEqWithLedger
  split
  next run =>
    obtain ⟨_executable, success⟩ :=
      PairedUnification.mguOrientedCap_complete_of_admissible
        competitorAdmissible competitorSound
    unfold PairedUnification.mguOrientedCap at success
    rw [run] at success
    contradiction
  next result run =>
    refine ⟨result, _, rfl, rfl⟩

/-- Capability-only counterpart of `solveTargetEqWithLedger_complete`. -/
theorem solveCapEqWithLedger_complete
    {ledger : CapabilityOriginLedger} {left right : Cap}
    {declarative : CapSubst}
    (dd : OriginSafeExactCapMGU ledger left right declarative)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    ∃ (result : PairedUnification.OrientedCapResult ledger left right)
        (step : SolveStep),
      solveCapEqWithLedger ledger solveCount origin left right = some step ∧
        step.delta = ⟨result.subst, TySubst.id⟩ :=
  solveCapEqWithLedger_complete_of_admissible
    dd.admissible dd.exact.1.1 solveCount origin

/-- Any origin-admissible solution makes the executable target-equality
solver emit a step retaining the proof-carrying kernel result.  This is the
form needed when the DD and executable traversals use bisimilar, rather than
literally identical, metavariable names. -/
theorem solveTargetEqWithLedger_complete_of_admissible
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {competitor : Subst}
    (competitorAdmissible : AdmissiblePost ledger competitor)
    (competitorSound : competitor.apply left = competitor.apply right)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    ∃ (result : PairedUnification.PairedResult ledger left right)
        (step : SolveStep),
      solveTargetEqWithLedger ledger solveCount origin left right = some step ∧
        step.delta = result.subst := by
  unfold solveTargetEqWithLedger
  split
  next run =>
    obtain ⟨_executable, success⟩ :=
      PairedUnification.mguPairedTy_complete_of_admissible
        competitorAdmissible competitorSound
    unfold PairedUnification.mguPairedTy at success
    rw [run] at success
    contradiction
  next result run =>
    refine ⟨result, _, rfl, rfl⟩

/-- An origin-safe exact paired solution makes the executable equality
solver emit a step retaining the proof-carrying kernel result. -/
theorem solveTargetEqWithLedger_complete
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {declarative : Subst}
    (dd : OriginSafeExactPairedMGU ledger left right declarative)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    ∃ (result : PairedUnification.PairedResult ledger left right)
        (step : SolveStep),
      solveTargetEqWithLedger ledger solveCount origin left right = some step ∧
        step.delta = result.subst :=
  solveTargetEqWithLedger_complete_of_admissible
    dd.admissible dd.exact.1.1 solveCount origin

/-- Applying the DD residual after the executable result gives exactly the DD
normal form of every type.  This is the pointwise form used to transport raw
traversal indices without choosing a variable renaming. -/
theorem PairedStateCorrespondence.apply_triangle
    {declarative executable : Subst}
    (correspondence : PairedStateCorrespondence declarative executable)
    (target : Ty) :
    declarative.apply (executable.apply target) =
      declarative.apply target := by
  rw [← Subst.seq_apply,
    ← correspondence.declarativeAbsorbsExecutable]

/-- The same triangle at the prevailing-state level.  If `initial` is the
state before this cut, the executable successor followed by the DD residual
is literally the declarative successor. -/
theorem PairedStateCorrespondence.prevailing_triangle
    {declarative executable : Subst}
    (correspondence : PairedStateCorrespondence declarative executable)
    (initial : Subst) :
    Subst.seq declarative (Subst.seq executable initial) =
      Subst.seq declarative initial := by
  rw [PhasedPost.seq_assoc,
    ← correspondence.declarativeAbsorbsExecutable]

/-- Every executable normal form can be mapped back through the DD witness's
instance residual.  This direction records mutual MGU generality without
claiming that the residual is a mere syntactic variable permutation. -/
theorem PairedStateCorrespondence.executable_apply_as_declarative_instance
    {declarative executable : Subst}
    (correspondence : PairedStateCorrespondence declarative executable)
    (target : Ty) :
    ∃ residual : Subst,
      executable.apply target = residual.apply (declarative.apply target) := by
  rcases correspondence.executableFactorsThroughDeclarative with
    ⟨residual, equation⟩
  refine ⟨residual, ?_⟩
  rw [equation, Subst.seq_apply]

end DemandTypingInferenceCompletenessSolver
end TypePM
