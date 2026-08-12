import TypePM.DemandTypingInferenceCompletenessPublic

/-!
# Final public bridge for Damas--Milner W runs

The DM completeness induction already constructs a chronological demand run,
its empty-ledger origin, and the terminal audit.  Public acceptance does not
need an intermediate `SourceTyping` existential: the established global
completeness recursion consumes those three witnesses directly.
-/

namespace TypePM
namespace DM

open Inference
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessGlobalRecursion
open DemandTypingInferenceCompletenessGlobalRoot
open DemandTypingInferenceCompletenessPublic

/-- The shortest acceptance boundary from a completed DM Algorithm W run to
the public certified inference option. -/
theorem infer_isSome_of_auditedWRun
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {rawTarget : Ty} {finalSupply : InferenceBase.FreshSupply}
    {terminal : Subst}
    {derived : DemandSynth signature (initialSupply signature context)
      Subst.id context expression rawTarget finalSupply terminal}
    {origin : DemandSynthOrigin signature derived [] []}
    (signatureWF : FrozenSigWF signature)
    (audit : DemandSynthTerminalAudit terminal signature origin) :
    (infer signature context expression).isSome = true := by
  let complete : PairedAuditedSynthCompletenessAt terminal signature
      (inferenceFuel expression) := pairedAuditedSynthCompleteness
    (terminal := terminal) signatureWF.schemesClosed
    signatureWF.armExhaustiveBasic (inferenceFuel expression)
  have root := pairedRoot_of_global (complete := complete) audit
  exact infer_isSome_of_rootCertified signatureWF root

/-- Boolean spelling used by the roadmap statement. -/
theorem inferenceSucceeds_of_auditedWRun
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {rawTarget : Ty} {finalSupply : InferenceBase.FreshSupply}
    {terminal : Subst}
    {derived : DemandSynth signature (initialSupply signature context)
      Subst.id context expression rawTarget finalSupply terminal}
    {origin : DemandSynthOrigin signature derived [] []}
    (signatureWF : FrozenSigWF signature)
    (audit : DemandSynthTerminalAudit terminal signature origin) :
    Inference.inferenceSucceeds signature context expression = true := by
  exact infer_isSome_of_auditedWRun signatureWF audit

end DM
end TypePM
