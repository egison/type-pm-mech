import TypePM.CertifiedInference
import TypePM.Safety

/-!
# End-to-end soundness

This module composes executable inference with the concrete dynamic
metatheory.  The public Algorithm W entry point performs its finite
reconstruction audit itself, so a successful run produces the internal
`RuntimeTyping` certificate without a caller-supplied bridge.  `FrozenSigWF`
then supplies the reusable runtime safety package.  Source acceptance itself
is defined only by `DDTyping`.
-/

namespace TypePM
namespace Inference

/-- The two concrete conclusions exposed by one certified inference run. -/
structure SafeResult
    (signature : FrozenSig) (context : NamedContext) (expression : Expr)
    (result : ExprResult) (SF : RuntimeSigF) : Prop where
  /-- State-free certificate for the inferred term and resolved result. -/
  runtimeTyping :
    RuntimeTyping signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/--
A successful certified W run and the concrete static runtime conditions
jointly yield a state-free runtime certificate and the dynamic safety interface.
-/
theorem infer_safe
    {signature : FrozenSig} {context : NamedContext} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature context expression = some result)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature context expression result SF where
  runtimeTyping := infer_success_runtimeTyping success
  core := core_safety signatureWF

end Inference
end TypePM
