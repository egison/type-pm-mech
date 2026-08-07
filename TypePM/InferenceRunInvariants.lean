import TypePM.InferenceTraversalStateExtension
import TypePM.InferenceTraversalAdmissibleTrace
import TypePM.InferenceTraversalLocalFactorization

/-!
# Combined invariants of successful raw inference

The traversal proofs deliberately expose three independent properties: state
resources extend monotonically, every emitted delta respects its captured
origin ledger, and every emitted certificate has local factorization.  This
module packages exactly those already-proved properties at the public raw-W
boundary without turning them into an unconditional whole-trace
factorization claim.
-/

namespace TypePM
namespace Inference

/-- The three global invariants currently established for one successful raw
inference traversal. -/
structure InferState.RawRunInvariants
    (initial final : InferState) : Prop where
  stateExtension : initial.StateExtension final
  admissibleTrace : final.AdmissibleTrace
  factorizingTrace : final.FactorizingTrace

/-- Successful `inferRaw` simultaneously preserves resource/history
extension and produces ledger-admissible, locally factorizing solve steps. -/
theorem inferRaw_runInvariants
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : inferRaw signature context expression = some result) :
    InferState.RawRunInvariants
      (initialState signature context) result.state where
  stateExtension := inferRaw_stateExtension success
  admissibleTrace := inferRaw_admissibleTrace success
  factorizingTrace := inferRaw_factorizingTrace success

end Inference
end TypePM
