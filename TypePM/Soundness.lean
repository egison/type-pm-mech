import TypePM.CertifiedInference
import TypePM.DemandTypingErasure
import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.Safety

/-!
# End-to-end soundness

This module exposes the two source-facing routes into the concrete dynamic
metatheory. A closed `SourceTyping` derivation yields the internal
`TypingInvariant`, while `FrozenSigWF` supplies the reusable runtime
safety package.  Executable inference additionally returns the source
`SourceTyping` derivation justified by its successful certified traversal.
-/

namespace TypePM

namespace SourceTyping

/-- The dynamic conclusions available from one closed source-typing
derivation. `TypingInvariant` remains an internal invariant; this package is
obtained publicly through `SourceTyping.safe`. -/
structure SafeResult
    (signature : FrozenSig) (expression : Expr) (target : Ty)
    (SF : RuntimeSigF) : Prop where
  /-- State-free invariant at exactly the published source type. -/
  typingInvariant : TypingInvariant signature [] expression target
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/-- A closed source program accepted by `SourceTyping` is connected directly to
the concrete dynamic safety interface under the single global signature
condition. -/
theorem safe
    {signature : FrozenSig} {expression : Expr} {target : Ty}
    {SF : RuntimeSigF}
    (typed : SourceTyping signature [] expression target)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature expression target SF where
  typingInvariant := typed.typingInvariant signatureWF.schemesClosed
  core := core_safety signatureWF

end SourceTyping

namespace Inference

/-- Source typing and the two concrete dynamic conclusions exposed by one
certified inference run. The typing invariant for a general context uses the
inference reconstruction route independently of closed-program state
erasure. -/
structure SafeResult
    (signature : FrozenSig) (context : Context) (expression : Expr)
    (result : ExprResult) (SF : RuntimeSigF) : Prop where
  /-- Source acceptance at the reported result type. -/
  sourceTyping :
    SourceTyping signature context expression result.resolvedTarget
  /-- State-free invariant for the inferred term and resolved result. -/
  typingInvariant :
    TypingInvariant signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget
  /-- The concrete operational judgments satisfy the public safety package. -/
  core : CoreSafety signature SF

/--
A successful certified W run and the concrete static runtime conditions
jointly yield a state-free typing invariant and the dynamic safety interface.
-/
theorem infer_safe
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature context expression = some result)
    (signatureWF : FrozenSigWF signature) :
    SafeResult signature context expression result SF where
  sourceTyping := infer_success_sourceTyping success
  typingInvariant := infer_success_typingInvariant success
  core := core_safety signatureWF

/-- On a closed program, successful inference enters the dynamic metatheory
through the public `SourceTyping` route: inference reconstructs `SourceTyping`, and
`SourceTyping.safe` performs state erasure and packages concrete safety. -/
theorem infer_closed_safe
    {signature : FrozenSig} {expression : Expr}
    {result : ExprResult} {SF : RuntimeSigF}
    (success : infer signature [] expression = some result)
    (signatureWF : FrozenSigWF signature) :
    SourceTyping.SafeResult signature expression result.resolvedTarget SF :=
  (infer_success_sourceTyping success).safe signatureWF

end Inference
end TypePM
