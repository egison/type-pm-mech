import TypePM.DemandTypingInferenceCompletenessGlobalRecursion
import TypePM.DemandTypingInferenceCompletenessGlobalRoot

/-!
# Public acceptance-completeness facade

The structural completeness dispatcher reconstructs one executable run from
the demand-directed derivation.  Pattern-constructor audit events deliberately retain the
demand-directed operands together with their bisimilar executable operands, so the only
root certificate accepted here is `PairedRootCertifiedSynthesis`.

This module owns the proof-erasure boundary from a nonempty internal root
certificate to Boolean acceptance and the final `SourceTyping.infer_isSome`
theorem.  The global recursion constructs the certificate from the audited demand-directed
derivation; `FrozenSigWF` discharges exactly the closed-scheme and canonical
arm-checker conditions needed by its root projection.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPublic

open Inference
open DemandTypingInferenceCompletenessPairedRoot
open DemandTypingInferenceCompletenessGlobalRecursion
open DemandTypingInferenceCompletenessGlobalRoot
open DemandTypingInferenceCompletenessGlobalCertified

/-- Eliminate the proof-relevant paired root certificate only inside the
proposition that public inference accepts.  No executable run, solver result,
validator condition, or raw-inference success is exposed to callers. -/
theorem infer_isSome_of_rootCertified
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature)
    (root : Nonempty
      (PairedRootCertifiedSynthesis signature context expression)) :
    (infer signature context expression).isSome = true :=
  infer_isSome_of_nonempty_pairedRoot signatureWF root

/-- Public acceptance completeness.  The caller supplies only the audited demand-directed
typing derivation and the same frozen-signature well-formedness boundary used
by dynamic safety. -/
theorem SourceTyping.infer_isSome
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typed : SourceTyping signature context expression target)
    (signatureWF : FrozenSigWF signature) :
    (infer signature context expression).isSome = true := by
  obtain ⟨rawTarget, finalSupply, terminal, derived, ledger, origin, audit,
    published⟩ := typed
  let complete : PairedAuditedSynthCompletenessAt terminal signature
      (inferenceFuel expression) := pairedAuditedSynthCompleteness
    (terminal := terminal) signatureWF.schemesClosed
    signatureWF.armExhaustiveBasic (inferenceFuel expression)
  have root := pairedRoot_of_global (complete := complete) audit
  exact infer_isSome_of_rootCertified signatureWF root

end DemandTypingInferenceCompletenessPublic
end TypePM
