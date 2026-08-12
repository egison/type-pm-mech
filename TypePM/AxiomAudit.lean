import Lean
import TypePM.PublicTheorems

/-!
# Axiom audit for the public theorem surface

The paper and `README.md` claim that the headline theorems are checked by the
kernel against Lean's standard axioms only.  This module turns that claim into
a build-time check: `#audit_standard_axioms` recomputes the axiom closure of
every audited constant and fails elaboration if anything outside `propext`,
`Classical.choice`, and `Quot.sound` appears --- in particular the per-proof
auxiliary axioms introduced by `native_decide` (which is reserved for
executable regressions), `sorryAx`, and any project-defined axiom.

The audited list is the public surface indexed by `PublicTheorems` together
with the decidability and closed-safety corollaries advertised in `README.md`.
The double-backquote name literals are resolved when this module elaborates,
so renaming a public theorem without updating this list is itself a build
error.
-/

namespace TypePM.AxiomAudit

open Lean Elab Command

/-- The only axioms the audited constants may depend on. -/
def standardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The audited public surface. -/
def auditedConstants : List Name :=
  [``TypePM.Inference.annotation_freeness,
   ``TypePM.DemandTypingInferenceCompletenessPublic.SourceTyping.infer_isSome,
   ``TypePM.Inference.infer_success_sourceTyping,
   ``TypePM.Inference.sourceTypable_iff_infer_isSome,
   ``TypePM.Inference.inferType_success_sourceTyping,
   ``TypePM.Inference.inferType_principal,
   ``TypePM.Inference.inferType_closed_principal,
   ``TypePM.Inference.infer_relative_principal,
   ``TypePM.Inference.infer_closed_relative_principal,
   ``TypePM.Inference.sourceTypableDecidable,
   ``TypePM.Inference.infer_closed_safe,
   ``TypePM.DemandTypingTargetUniqueness.SourceTyping.target_unique_modulo_renaming,
   ``TypePM.SourceTyping.safe,
   ``TypePM.SourceTyping.typingInvariant,
   ``TypePM.DM.sourceTyping_to_dm,
   ``TypePM.DM.Typing.inferenceSucceeds,
   ``TypePM.PrincipalityCounterexample.no_principal_type]

/--
Fail elaboration unless every constant in `auditedConstants` depends only on
`standardAxioms`.  On success, report the audited count once.
-/
elab "#audit_standard_axioms" : command => do
  let mut failures : Array MessageData := #[]
  for name in auditedConstants do
    let axioms ← liftCoreM (collectAxioms name)
    let offending := axioms.filter fun a => !standardAxioms.contains a
    unless offending.isEmpty do
      failures := failures.push
        m!"'{name}' depends on non-standard axioms: {offending.toList}"
  unless failures.isEmpty do
    throwError (MessageData.joinSep (m!"axiom audit failed:" :: failures.toList) m!"\n")
  logInfo m!"axiom audit: {auditedConstants.length} public constants depend only on {standardAxioms}"

#audit_standard_axioms

end TypePM.AxiomAudit
