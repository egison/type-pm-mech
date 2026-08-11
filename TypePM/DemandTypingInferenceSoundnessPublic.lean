import TypePM.CertifiedInference
import TypePM.DemandTypingInferenceSoundnessCertified

/-!
# Public executable-to-DD soundness

The public inference boundary combines successful raw traversal with the
terminal bridge validated by `infer`.  Terminal-audited reconstruction then
erases its execution indices to the source-facing `DDTyping` judgment.
-/

namespace TypePM
namespace Inference

/-- Every successful public inference run has a demand-directed typing
derivation at the reported result type. -/
theorem infer_success_ddTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    DDTyping signature context expression result.resolvedTarget :=
  (inferExprFuel_certifiedRunAt
    (infer_success_inferExprFuel success)
    (infer_success_wBridgeWF success)
    (InferState.HistoryPrefix.refl result.state)).toDDTyping

end Inference
end TypePM
