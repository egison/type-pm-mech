import TypePM.RecursiveExamples
import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingInferenceSoundnessMutual
import TypePM.InterpreterAdequacy

/-!
# Terminal matcher-finalization audit counterexample

This regression isolates a source program for which the protected raw W
traversal succeeds but the public terminal audit rejects.  The program uses a
one-field tuple matcher.  Its field capability is the recursive matcher's
borrowed argument-slot capability, so raw inference intentionally leaves that
capability structurally flexible.  The enclosing application later specializes
it to the opaque constructor `K`.

The matcher itself only decomposes the outer tuple and delegates its field to
the matcher supplied as its argument.  It never observes `K`.  Nevertheless,
the terminal matcher-finalization check recursively finalizes `K` and rejects
because the signature does not declare `K` observable.

The mutually recursive executable inference functions are opaque to kernel
reduction.  The concrete run is therefore fixed with `#guard`, rather than
introducing `native_decide`.  Symbolic theorems below connect every successful
raw result to the existing demand-directed traversal soundness theorem.
-/

namespace TypePM
namespace TerminalAuditCounterexample

open Inference
open Inference.Reconstruction

/-! ## A well-formed signature with one opaque matcher consumer -/

/-- A value constructor that forces its argument matcher capability to `K`.
Its result remains an ordinary data root, as required by `FrozenSigWF`. -/
def consumeKScheme : CtorScheme where
  capBinders := []
  tyBinders := []
  args := [.matcher (.con "K" []) .int]
  result := .data "Witness" []

/-- `K` stays opaque because the inherited observability table recognizes only
`List`. -/
def signature : FrozenSig :=
  { RecursiveExamples.listSignature with
      dataCtors := ("consumeK", consumeKScheme) ::
        RecursiveExamples.listSignature.dataCtors }

theorem signature_checker_accepts :
    frozenSigWFCheck signature = true := by
  decide

theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound signature_checker_accepts rfl

theorem k_is_opaque : signature.observability "K" = none := by
  rfl

/-! ## Minimal closed source program -/

/-- The only structural clause decomposes a one-field tuple and delegates the
field to the recursive matcher's argument slot. -/
def tupleClause : Clause :=
  .mk (generalTuplePP 1) (.var "argument")
    [.mk .wild (.ctor "nil" [])]

def clauses : List Clause :=
  [tupleClause, RecursiveExamples.catchClause]

/-- `self` is deliberately unused.  The `fix` form is needed only because its
matcher placeholder allocates the shared argument-slot capability and records
that capability as structurally flexible. -/
def delegatedTupleMatcher : Expr :=
  .fix "self" "argument" (.matcher clauses)

def programBody : Expr :=
  .tuple [
    .ctor "consumeK" [.var "opaqueMatcher"],
    .app delegatedTupleMatcher (.var "opaqueMatcher")]

/-- The first tuple component fixes the lambda parameter at `Matcher K Int`.
The later matcher application consequently specializes the borrowed slot
capability to `K`, after the matcher literal's local finalization event. -/
def program : Expr :=
  .lam "opaqueMatcher" programBody

def rawResult : Option Inference.ExprResult :=
  Inference.inferRaw signature [] program

def publicResult : Option Inference.ExprResult :=
  Inference.infer signature [] program

/-- The exact inferred result target observed before the terminal audit. -/
def expectedTarget : Ty :=
  .fn (.matcher (.con "K" []) .int)
    (.prod [
      .data "Witness" [],
      .matcher (.prod [.con "K" []]) (.prod [.int])])

/-- The nine public audit components, in `wBridgeCheck` order. -/
def auditProfile : Option (List Bool) :=
  rawResult.map fun result =>
    [tracePrimitiveHoleCheck signature result.state.trace,
     tracePatternLeafCheck signature result.state.trace,
     tracePatternCtorCheck signature result.state,
     traceInstanceSuffixCheck result.state,
     traceSlotAlignmentCheck result.state,
     traceTypeAlignmentCheck result.state,
     traceDualAlignmentCheck result.state,
     traceFinalizationSuffixCheck signature result.state,
     traceGeneralizationCheck signature result.state]

/-! These guards are executable regressions.  They intentionally use neither
`native_decide` nor a handwritten copy of the inferred state. -/

#guard rawResult.isSome
#guard !publicResult.isSome
#guard DirectSelf.check "self" (.matcher clauses)
#guard auditProfile == some
  [true, true, true, true, true, true, true, false, true]
#guard match rawResult with
  | none => false
  | some result => decide (result.resolvedTarget = expectedTarget)
#guard match rawResult with
  | none => false
  | some result => result.state.protectedCaps.isEmpty
#guard match rawResult with
  | none => false
  | some result => decide (result.state.prevailing.cap ⟨1⟩ = .con "K" [])
#guard match rawResult with
  | none => false
  | some result =>
      !traceFinalizationSuffixCheck signature result.state &&
        !wBridgeCheck signature result

/-! ## Symbolic connection to the raw demand-directed derivation -/

/-- Producer protection does not change a successful raw result, so a raw
success exposes the exact underlying fuelled traversal. -/
theorem raw_success_inferExprFuel
    {result : Inference.ExprResult}
    (success : rawResult = some result) :
    Inference.inferExprFuel (Inference.inferenceFuel program) signature [] [] []
      program (Inference.initialState signature []) = some result := by
  unfold rawResult Inference.inferRaw at success
  cases core : Inference.inferExprFuel (Inference.inferenceFuel program)
      signature [] [] [] program (Inference.initialState signature []) with
  | none => simp [core] at success
  | some candidate =>
      have guarded : Inference.enforceProtectedResult candidate =
          some result := by
        simpa [core] using success
      have equality := (Inference.enforceProtectedResult_sound guarded).1
      subst candidate
      rfl

/-- Every concrete raw result guarded above carries the existing chronological
demand-directed synthesis derivation.  No terminal audit is used here. -/
theorem raw_success_demand_synth_run
    {result : Inference.ExprResult}
    (success : rawResult = some result) :
    Inference.DemandSynthRun signature [] program
      (Inference.initialState signature []) result :=
  Inference.inferExprFuel_ddSynthRun
    (raw_success_inferExprFuel success)

/-- If the executable public rejection is supplied as an equation, acceptance
equivalence and signature well-formedness rule out the current audit-bearing
`SourceTyping` judgment.  This states exactly why the raw derivation above is
not itself a public source-typing derivation. -/
theorem public_rejection_not_source_typable
    (rejected : publicResult = none) :
    ¬ ∃ target, SourceTyping signature [] program target := by
  intro typed
  have accepted : (Inference.infer signature [] program).isSome = true :=
    (Inference.sourceTypable_iff_infer_isSome signature_wf).1 typed
  rw [← publicResult] at accepted
  rw [rejected] at accepted
  contradiction

/-! ## Operational witness -/

/-- Evaluation of the closed source term produces a closure immediately.  This
is only an operational non-stuck witness; it is not the global typed no-stuck
theorem, whose premise is the audit-bearing `SourceTyping` judgment. -/
def programClosure : Value :=
  .closure none [] "opaqueMatcher" programBody

theorem program_runs :
    evalFuel [] 1 [] program = .ok programClosure := by
  rfl

theorem program_runs_relationally :
    Eval [] [] program programClosure :=
  evalFuel_ok program_runs

end TerminalAuditCounterexample
end TypePM
