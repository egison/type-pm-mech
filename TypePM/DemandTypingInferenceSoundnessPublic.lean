import TypePM.CertifiedInference
import TypePM.DemandTypingInferenceSoundnessCertified

/-!
# Public executable-to-demand-directed soundness

The public inference boundary combines successful raw traversal with the
terminal bridge validated by `infer`.  Terminal-audited reconstruction then
erases its execution indices to the source-facing `SourceTyping` judgment.
-/

namespace TypePM
namespace Inference

/-- Every successful public inference run has a demand-directed typing
derivation at the reported result type. -/
theorem infer_success_sourceTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    SourceTyping signature context expression result.resolvedTarget :=
  (inferExprFuel_certifiedRunAt
    (infer_success_inferExprFuel success)
    (infer_success_wBridgeWF success)
    (InferState.HistoryPrefix.refl result.state)).toSourceTyping

end Inference
end TypePM
