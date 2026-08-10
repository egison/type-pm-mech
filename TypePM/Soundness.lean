import TypePM.CertifiedInference
import TypePM.Safety

/-!
# End-to-end soundness

This module is the public composition point between executable inference and
the concrete dynamic metatheory.  The public Algorithm W entry point performs
its finite reconstruction audit itself, so successful inference reconstructs
source typing without a caller-supplied bridge.  `FrozenSigWF` and the local
primitive-pattern order invariant supply the reusable runtime safety package.
-/

namespace TypePM
namespace Inference

/-- The two concrete conclusions exposed by one certified inference run. -/
structure SafeResult
    (signature : FrozenSig) (context : Context) (expression : Expr)
    (result : ExprResult) (SF : RuntimeSigF) : Prop where
  /-- The inferred term is typable at its fully resolved result. -/
  typing :
    SemanticTyping signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/--
A successful certified W run and the concrete static runtime conditions
jointly yield source typing and the full dynamic safety interface.
-/
theorem infer_safe
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature context expression = some result)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature context expression result SF where
  typing := infer_success_sound success
  core := core_safety signatureWF

end Inference
end TypePM
