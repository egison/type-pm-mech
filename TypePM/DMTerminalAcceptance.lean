import TypePM.DamasMilner
import TypePM.CertifiedInference

/-!
# A terminal-acceptance milestone for the Damas--Milner fragment

The general algorithmic-acceptance theorem for every `DM.HasTy` derivation is
still open.  This module fixes a first nontrivial terminal milestone at the
classic polymorphic-let witness from `TypePM.DamasMilner`: raw Algorithm W
succeeds, its exact raw result passes `wBridgeCheck`, and the public certified
entry point accepts the program at `Int`.
-/

namespace TypePM
namespace DMTerminalAcceptance

/-- The closed empty signature used by the pattern-free DM witness. -/
def emptySignature : FrozenSig where
  observability := fun _ => none
  dataCtors := []
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

/-- The exact raw result produced for the polymorphic identity program. -/
def idProgramRawResult : Inference.ExprResult :=
  (Inference.inferRaw emptySignature [] DM.idProgram).get (by native_decide)

/-- Raw W accepts the polymorphic-let DM witness. -/
theorem idProgram_raw_success :
    Inference.inferRaw emptySignature [] DM.idProgram =
      some idProgramRawResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- The exact raw result passes every finite terminal bridge audit. -/
theorem idProgram_raw_terminal_checked :
    Inference.Reconstruction.wBridgeCheck emptySignature idProgramRawResult =
      true := by
  native_decide

/-- The successful Boolean audit constructs the semantic bridge certificate
consumed by reconstruction; it is not merely an acceptance-bit regression. -/
theorem idProgram_raw_bridge :
    Inference.Reconstruction.WBridgeWF emptySignature
      idProgramRawResult.state :=
  Inference.Reconstruction.wBridgeCheck_sound
    idProgram_raw_terminal_checked

/-- The checked raw result has the declaratively predicted result type. -/
theorem idProgram_raw_result_type :
    idProgramRawResult.resolvedTarget = .int := by
  native_decide

/-- A single theorem packages the Stage-2 terminal milestone in its intended
raw-success-implies-audited-success shape for this nontrivial DM witness. -/
theorem idProgram_raw_success_and_checked :
    ∃ result : Inference.ExprResult,
      Inference.inferRaw emptySignature [] DM.idProgram = some result ∧
      Inference.Reconstruction.wBridgeCheck emptySignature result = true ∧
      result.resolvedTarget = .int := by
  exact ⟨idProgramRawResult, idProgram_raw_success,
    idProgram_raw_terminal_checked, idProgram_raw_result_type⟩

/-- The executable milestone is attached to the existing DM typing
derivation, rather than being only an untyped evaluation regression. -/
theorem idProgram_dm_terminal_milestone :
    DM.HasTy [] DM.idProgram .int ∧
      ∃ result : Inference.ExprResult,
        Inference.inferRaw emptySignature [] DM.idProgram = some result ∧
        Inference.Reconstruction.wBridgeCheck emptySignature result = true ∧
        result.resolvedTarget = .int :=
  ⟨DM.idProgram_dm_typed, idProgram_raw_success_and_checked⟩

/-- Consequently the public, terminally certified entry point accepts the
same polymorphic-let program. -/
theorem idProgram_public_acceptance :
    Inference.inferenceSucceeds emptySignature [] DM.idProgram = true := by
  native_decide

end DMTerminalAcceptance
end TypePM
