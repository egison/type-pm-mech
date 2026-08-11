import TypePM.CertifiedInference
import TypePM.DemandTypingErasure
import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.Safety

/-!
# End-to-end soundness

This module exposes the two source-facing routes into the concrete dynamic
metatheory.  A closed `DDTyping` derivation erases to the internal
`RuntimeTyping` certificate, while `FrozenSigWF` supplies the reusable runtime
safety package.  Executable inference additionally returns the source
`DDTyping` derivation justified by its successful certified traversal.
-/

namespace TypePM

namespace DDTyping

/-- The dynamic conclusions available from one closed source-typing
derivation.  `RuntimeTyping` remains an internal certificate; this package is
obtained publicly through `DDTyping.safe`. -/
structure SafeResult
    (signature : FrozenSig) (expression : Expr) (target : Ty)
    (SF : RuntimeSigF) : Prop where
  /-- State-free certificate at exactly the published source type. -/
  runtimeTyping : RuntimeTyping signature [] expression target
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/-- A closed source program accepted by `DDTyping` is connected directly to
the concrete dynamic safety interface under the single global signature
condition. -/
theorem safe
    {signature : FrozenSig} {expression : Expr} {target : Ty}
    {SF : RuntimeSigF}
    (typed : DDTyping signature [] expression target)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature expression target SF where
  runtimeTyping := typed.runtimeTyping signatureWF.schemesClosed
  core := core_safety signatureWF

end DDTyping

namespace Inference

/-- Source typing and the two concrete dynamic conclusions exposed by one
certified inference run.  The runtime certificate for a general context uses
the inference reconstruction route independently of closed-program DD state
erasure. -/
structure SafeResult
    (signature : FrozenSig) (context : Context) (expression : Expr)
    (result : ExprResult) (SF : RuntimeSigF) : Prop where
  /-- Source acceptance at the reported result type. -/
  sourceTyping :
    DDTyping signature context expression result.resolvedTarget
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
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature context expression = some result)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature context expression result SF where
  sourceTyping := infer_success_ddTyping success
  runtimeTyping := infer_success_runtimeTyping success
  core := core_safety signatureWF

/-- On a closed program, successful inference enters the dynamic metatheory
through the public DD route: inference reconstructs `DDTyping`, and
`DDTyping.safe` performs state erasure and packages concrete safety. -/
theorem infer_closed_safe
    {signature : FrozenSig} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature [] expression = some result)
    (signatureWF : FrozenSigWF signature) :
    DDTyping.SafeResult signature expression result.resolvedTarget SF :=
  (infer_success_ddTyping success).safe signatureWF

end Inference
end TypePM
