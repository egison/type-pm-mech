import TypePM.P2.Reconstruction
import TypePM.P2.Safety

/-!
# End-to-end conditional soundness

This module is the public composition point between executable inference and
the concrete dynamic metatheory.  A successful Algorithm W run is useful only
with its finite `WBridgeWF` audit; together they reconstruct source typing.
`FrozenSigWF` and the local value-pattern capture condition independently
supply the reusable runtime safety package.  `WBridgeWF` stores no source
typing derivation, while `OperationalCaptureAdm` contains only the local
value-pattern expression typings consumed by preservation; neither stores an
operational result.
-/

namespace TypePM.P2
namespace Inference

/-- The two concrete conclusions exposed by one audited inference run. -/
structure SafeResult
    (signature : FrozenSig) (context : Context) (expression : Expr)
    (result : ExprResult) (SF : RuntimeSigF) : Prop where
  /-- The inferred term is typable at its fully resolved result. -/
  typing :
    HasTy signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/--
An audited successful W run and the concrete static runtime conditions jointly
yield source typing and the full dynamic safety interface.
-/
theorem infer_safe
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature context expression = some result)
    (bridge : Reconstruction.WBridgeWF signature context expression result)
    (signatureWF : FrozenSigWF signature)
    (captureAdm : OperationalCaptureAdm signature SF) :
    SafeResult signature context expression result SF where
  typing := infer_success_sound success bridge
  core := core_safety signatureWF captureAdm

end Inference
end TypePM.P2
