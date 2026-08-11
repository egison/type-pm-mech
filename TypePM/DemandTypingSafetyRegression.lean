import TypePM.Soundness
import TypePM.DynamicSafetyRegression

/-!
# Demand-typing safety regressions

The concrete closed `matchAll` run enters dynamic safety through the public
source judgment.  This pins both routes exposed by `Soundness`: direct
`DDTyping` safety and the certified-inference composition that first
reconstructs `DDTyping`.
-/

namespace TypePM
namespace DemandTypingSafetyRegression

open DynamicSafetyRegression

/-- The certified run exposes source acceptance together with the internal
runtime certificate and the reusable concrete safety package. -/
def inferenceSafety : Inference.SafeResult signature [] program
    inferenceResult runtimeSignature :=
  Inference.infer_safe inference_success signature_wf

/-- The source derivation reconstructed from inference enters M4's public
closed-program safety boundary. -/
def sourceSafety : DDTyping.SafeResult signature program
    inferenceResult.resolvedTarget runtimeSignature :=
  Inference.infer_closed_safe inference_success signature_wf

/-- M4 state erasure publishes the exact source result type, without exposing
an inference state or accepting a runtime certificate as a premise. -/
theorem source_runtimeTyping :
    RuntimeTyping signature [] program inferenceResult.resolvedTarget :=
  sourceSafety.runtimeTyping

/-- The same source-facing result exposes all concrete dynamic consequences. -/
def source_coreSafety : CoreSafety signature runtimeSignature :=
  sourceSafety.core

/-- Evaluation preservation is usable from the DD-facing package itself: the
runtime value receives exactly the type published by certified inference. -/
theorem source_program_value_typed :
    ValueTy signature programValue inferenceResult.resolvedTarget :=
  sourceSafety.core.evalPreservation evaluation_mirror EnvPristine.nil
    (by
      intro name value found
      simp [Env.find?] at found)
    sourceSafety.runtimeTyping

end DemandTypingSafetyRegression
end TypePM
