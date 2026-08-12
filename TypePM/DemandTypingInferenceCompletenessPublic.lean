import TypePM.DemandTypingInferenceCompletenessPairedRoot

/-!
# Public acceptance-completeness facade

The structural completeness dispatcher reconstructs one executable run from
the DD derivation.  Pattern-constructor audit events deliberately retain the
DD operands together with their bisimilar executable operands, so the only
root certificate accepted here is `PairedRootCertifiedSynthesis`.

This module contains only the proof-erasure boundary from a nonempty internal
root certificate to Boolean acceptance.  The final `DDTyping.infer_isSome`
theorem is added by the global dispatcher, which constructs this certificate
from the audited DD derivation and `FrozenSigWF`.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPublic

open Inference
open DemandTypingInferenceCompletenessPairedRoot

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

end DemandTypingInferenceCompletenessPublic
end TypePM
