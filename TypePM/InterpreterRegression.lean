import TypePM.InterpreterAdequacy
import TypePM.InterpreterDispatchBridge
import TypePM.DynamicSafetyRegression

/-!
# Interpreter regression

Runs the end-to-end dynamic-safety fixture through the fuel-indexed
reference interpreter and replays the run as the relational evaluation via
adequacy.  The relational derivation obtained this way is definitionally
independent of the hand-built `program_evaluation` witness.
-/

namespace TypePM
namespace InterpreterRegression

open DynamicSafetyRegression

/-- The reference interpreter computes the fixture's value. -/
theorem program_runs :
    evalFuel runtimeSignature 20 [] program = .ok programValue := by
  rfl

/-- Adequacy replays the executable run as a big-step derivation. -/
theorem program_runs_relationally :
    Eval runtimeSignature [] program programValue :=
  evalFuel_ok program_runs

/-- Interpreter preservation on the fixture: the computed value is typed at
the inferred type, through adequacy and the safety package. -/
theorem program_run_typed :
    ValueTy signature programValue (Ty.listT .int) :=
  safetyPackage.evalPreservation
    (EvalRuntimeSigAgrees.of_global global_runtime_agreement
      program_runs_relationally)
    EnvPristine.nil
    (fun name value found => by simp [Env.find?] at found)
    program_typed

/-- The headline no-stuck theorem on the fixture: the typed closed program
cannot stick, at any fuel. -/
theorem program_never_stuck (fuel : Nat) :
    evalFuel [] fuel [] program ≠ .stuck :=
  typed_never_stuck signature_wf global_runtime_agreement program_typed
    rfl fuel

end InterpreterRegression
end TypePM
