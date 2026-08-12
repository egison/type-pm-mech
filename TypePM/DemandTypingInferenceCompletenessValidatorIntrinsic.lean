import TypePM.DemandTypingInferenceCompletenessValidatorTrace
import TypePM.DemandTypingInferenceSoundnessPatterns
import TypePM.InferenceTraversalStateExtension

/-!
# Intrinsic terminal-validator facts

Several terminal checks merely replay facts that the executable traversal
itself established.  They do not depend on the proof-relevant terminal audit
stored by `SourceTyping`.  This module isolates the corresponding transport
lemmas.  In particular, an equality established at an alignment cut remains
an equality after every later solver suffix, while the event's local views
are recovered from the append-only history.

The matcher-finalization, let-generalization, and pattern-constructor checks
are intentionally absent: those are exactly the three terminal-sensitive
facts represented in `DemandSynthTerminalAudit`.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-- Pointwise form of the ordinary type-alignment trace fold. -/
def TypeAlignmentEventCondition
    (terminal : InferState) (event : TraceEvent) : Prop :=
  match event with
  | .typeAlignment start stop rawLeft rawRight localLeft localRight =>
      start ≤ stop ∧ stop ≤ terminal.trace.solves.length ∧
      localLeft = (replay (terminal.trace.solves.take start)).apply rawLeft ∧
      localRight = (replay (terminal.trace.solves.take start)).apply rawRight ∧
      terminal.prevailing.apply rawLeft = terminal.prevailing.apply rawRight
  | _ => True

/-- Pointwise form of the dual-alignment trace fold. -/
def DualAlignmentEventCondition
    (terminal : InferState) (event : TraceEvent) : Prop :=
  match event with
  | .dualAlignment start stop rawLeft rawRight localLeft localRight =>
      start ≤ stop ∧ stop ≤ terminal.trace.solves.length ∧
      localLeft = rawLeft.applySubst
        (replay (terminal.trace.solves.take start)) ∧
      localRight = rawRight.applySubst
        (replay (terminal.trace.solves.take start)) ∧
      rawLeft.applySubst terminal.prevailing =
        rawRight.applySubst terminal.prevailing
  | _ => True

/-- Pointwise type-event coverage is definitionally the existing trace fold. -/
theorem traceTypeAlignmentConditions_iff_eventCoverage
    (state : InferState) :
    TraceTypeAlignmentConditions state ↔
      ∀ event, event ∈ state.trace.events →
        TypeAlignmentEventCondition state event := by
  rfl

/-- Pointwise dual-event coverage is definitionally the existing trace fold. -/
theorem traceDualAlignmentConditions_iff_eventCoverage
    (state : InferState) :
    TraceDualAlignmentConditions state ↔
      ∀ event, event ∈ state.trace.events →
        DualAlignmentEventCondition state event := by
  rfl

/-! ## Equality transport through a later executable suffix -/

/-- Applying the solver suffix of a history extension preserves an equality
that already held at the earlier cut. -/
theorem HistoryPrefix.final_type_eq
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    {left right : Ty}
    (equal : earlier.prevailing.apply left =
      earlier.prevailing.apply right) :
    later.prevailing.apply left = later.prevailing.apply right := by
  rcases history.prevailing_eq with ⟨suffix, prevailingEq⟩
  rw [prevailingEq]
  rw [replayFrom_apply, replayFrom_apply, equal]

/-- Dual equality is the componentwise type/capability instance of the same
suffix transport. -/
theorem HistoryPrefix.final_dual_eq
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    {left right : Dual}
    (equal : left.applySubst earlier.prevailing =
      right.applySubst earlier.prevailing) :
    left.applySubst later.prevailing = right.applySubst later.prevailing := by
  rcases history.prevailing_eq with ⟨suffix, prevailingEq⟩
  rw [prevailingEq]
  have transport : ∀ (prevailing : Subst) (steps : List SolveStep),
      left.applySubst prevailing = right.applySubst prevailing →
      left.applySubst (replayFrom prevailing steps) =
        right.applySubst (replayFrom prevailing steps) := by
    intro prevailing steps equality
    induction steps generalizing prevailing with
    | nil => exact equality
    | cons step steps induction =>
        apply induction (prevailing := Subst.seq step.delta prevailing)
        simpa only [Dual.applySubst_seq] using
          congrArg (Dual.applySubst step.delta) equality
  exact transport earlier.prevailing suffix equal

/-! ## Ordinary type-alignment events -/

/-- A successful executable type alignment contributes exactly the semantic
terminal condition required by `traceTypeAlignmentCheck`, at every later
history cut. -/
theorem alignTypes_terminal_condition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (success : alignTypes state origin left right = some aligned)
    (suffix : aligned.HistoryPrefix terminal) :
    let start := state.trace.solves.length
    let stop := aligned.trace.solves.length
    start ≤ stop ∧ stop ≤ terminal.trace.solves.length ∧
      state.prevailing.apply left =
        (replay (terminal.trace.solves.take start)).apply left ∧
      state.prevailing.apply right =
        (replay (terminal.trace.solves.take start)).apply right ∧
      terminal.prevailing.apply left = terminal.prevailing.apply right := by
  dsimp only
  have localHistory := alignTypes_historyPrefix success
  have totalHistory := localHistory.trans suffix
  have alignedRun := alignTypes_ddAlignTypesRun success
  rcases alignedRun with ⟨_supplyEq, _ledgerEq, alignedDD⟩
  refine ⟨localHistory.solve_length_le, suffix.solve_length_le, ?_, ?_, ?_⟩
  · rw [totalHistory.take_solves]
    rfl
  · rw [totalHistory.take_solves]
    rfl
  · exact HistoryPrefix.final_type_eq suffix alignedDD.output_equal

/-- Direct emitter API: a successful ordinary alignment, followed by the
overall traversal suffix, justifies its exact recorded event at the root
terminal cut. -/
theorem alignTypes_typeAlignmentEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (success : alignTypes state origin left right = some aligned)
    (suffix : aligned.HistoryPrefix terminal) :
    TypeAlignmentEventCondition terminal
      (.typeAlignment state.trace.solves.length aligned.trace.solves.length
        left right (state.prevailing.apply left)
        (state.prevailing.apply right)) := by
  exact alignTypes_terminal_condition success suffix

/-! ## Dual-alignment events -/

/-- Origin-safe dual alignment makes both components equal at its output
substitution. -/
theorem ddAlignDual_output_equal_intrinsic
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : Dual}
    (aligned : DemandAlignDualWithLedger ledger S left right S') :
    left.applySubst S' = right.applySubst S' := by
  cases aligned with
  | mk capSafe targetsAligned =>
      rename_i capDelta
      have capAtMiddle :
          (Subst.seq ⟨capDelta, TySubst.id⟩ S).apply
              (.matcher left.cap .unit) =
            (Subst.seq ⟨capDelta, TySubst.id⟩ S).apply
              (.matcher right.cap .unit) := by
        simp only [Subst.apply_matcher, Subst.apply_unit]
        change Ty.matcher (left.cap.apply (CapSubst.comp capDelta S.cap))
            .unit =
          Ty.matcher (right.cap.apply (CapSubst.comp capDelta S.cap)) .unit
        rw [Cap.apply_comp, Cap.apply_comp]
        exact congrArg (fun capability => Ty.matcher capability .unit)
          capSafe.exact.1.1
      have capAtFinal := targetsAligned.erase.replayExtends.apply_eq capAtMiddle
      have capEquality : left.cap.apply S'.cap = right.cap.apply S'.cap :=
        (Ty.matcher.inj capAtFinal).1
      have targetEquality := targetsAligned.output_equal
      cases left
      cases right
      simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality ⊢
      rw [capEquality, targetEquality]

/-- A successful executable dual alignment contributes exactly the semantic
terminal condition required by `traceDualAlignmentCheck`, at every later
history cut. -/
theorem alignDuals_terminal_condition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some aligned)
    (suffix : aligned.HistoryPrefix terminal) :
    let start := state.trace.solves.length
    let stop := aligned.trace.solves.length
    start ≤ stop ∧ stop ≤ terminal.trace.solves.length ∧
      left.applySubst state.prevailing =
        left.applySubst (replay (terminal.trace.solves.take start)) ∧
      right.applySubst state.prevailing =
        right.applySubst (replay (terminal.trace.solves.take start)) ∧
      left.applySubst terminal.prevailing =
        right.applySubst terminal.prevailing := by
  dsimp only
  have localHistory := alignDuals_historyPrefix success
  have totalHistory := localHistory.trans suffix
  rcases alignDuals_ddAlignDualRun success with
    ⟨_supplyEq, _ledgerEq, alignedDD⟩
  refine ⟨localHistory.solve_length_le, suffix.solve_length_le, ?_, ?_, ?_⟩
  · rw [totalHistory.take_solves]
    rfl
  · rw [totalHistory.take_solves]
    rfl
  · exact HistoryPrefix.final_dual_eq suffix
      (ddAlignDual_output_equal_intrinsic alignedDD)

/-- Direct emitter API for a successful dual alignment and its overall
traversal suffix. -/
theorem alignDuals_dualAlignmentEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some aligned)
    (suffix : aligned.HistoryPrefix terminal) :
    DualAlignmentEventCondition terminal
      (.dualAlignment state.trace.solves.length aligned.trace.solves.length
        left right (left.applySubst state.prevailing)
        (right.applySubst state.prevailing)) := by
  exact alignDuals_terminal_condition success suffix

/-! ## Fresh-allocation arithmetic -/

/-- The next capability identifier is outside every list already bounded by
the incoming supply. -/
theorem nextCap_not_mem_of_below
    {supply : InferenceBase.FreshSupply} {variables : List CapVar}
    (below : InferenceBase.CapVarsBelow supply variables) :
    (⟨supply.nextCap⟩ : CapVar) ∉ variables := by
  intro membership
  exact Nat.lt_irrefl supply.nextCap (below _ membership)

/-- The next ordinary-type identifier is outside every list already bounded
by the incoming supply. -/
theorem nextTy_not_mem_of_below
    {supply : InferenceBase.FreshSupply}
    {variables : List TypePM.TyVar}
    (below : InferenceBase.TyVarsBelow supply variables) :
    supply.nextTy ∉ variables := by
  intro membership
  exact Nat.lt_irrefl supply.nextTy (below _ membership)

/-- Source-signature capability variables are below the canonical initial
allocation cut. -/
theorem initial_nextCap_fresh_for_signature
    (signature : FrozenSig) (context : Context) :
    (⟨(initialSupply signature context).nextCap⟩ : CapVar) ∉
      signature.capVars := by
  apply nextCap_not_mem_of_below
  intro varId membership
  simpa only [initialSupply] using
    InferenceBase.mem_lt_binderSpan
      (List.mem_map.mpr
        ⟨varId, List.mem_append_left context.allCapVars membership, rfl⟩)

/-- Source-signature target variables are below the canonical initial
allocation cut. -/
theorem initial_nextTy_fresh_for_signature
    (signature : FrozenSig) (context : Context) :
    (initialSupply signature context).nextTy ∉ signature.tyVars := by
  apply nextTy_not_mem_of_below
  intro varId membership
  simpa only [initialSupply] using
    InferenceBase.mem_lt_binderSpan
      (List.mem_append_left context.allTyVars membership)

end Reconstruction
end Inference
end TypePM
