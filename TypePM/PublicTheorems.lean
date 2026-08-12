import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingTargetUniqueness
import TypePM.SourcePrincipality
import TypePM.RelativePrincipality
import TypePM.PrincipalityCounterexample
import TypePM.Soundness
import TypePM.DamasMilnerConservativity

/-!
# Public theorem index

This import-only facade gives reviewers and the paper one stable module from
which to find the main results.  The declarations retain their original
namespaces and source modules; no compatibility aliases or duplicate theorem
statements are introduced.

* `Inference.annotation_freeness` — closed source terms need no type
  annotation for source typability to be decided by public inference.
* `SourceTyping.infer_isSome` — an audited `SourceTyping` derivation is
  accepted by public inference under the frozen-signature boundary.
* `Inference.infer_success_sourceTyping` — every successful public inference run
  reconstructs `SourceTyping` at its reported type.
* `SourceTyping.safe` — closed `SourceTyping` enters the concrete dynamic safety
  package under the single public signature condition.
* `SourceTyping.typingInvariant` — closed `SourceTyping` yields the internal
  state-free typing invariant at exactly its published type.
* `SourceTyping.target_unique_modulo_renaming` — any two audited
  `SourceTyping` targets for the same source share a representative up to
  residual two-sort renaming.
* `Inference.inferType_principal` — the type reported by public inference is
  principal in the finite-scope two-sorted instance preorder.
* `Inference.infer_relative_principal` — open-term principality compares the
  resolved context and target together under one paired substitution.
* `DM.sourceTyping_to_dm` — a closed audited source typing in the explicit
  pattern-free fragment erases to a Damas--Milner typing.
* `PrincipalityCounterexample.no_principal_type` — the internal
  `TypingInvariant` family is not a source principal-type
  specification; this is not a counterexample about `SourceTyping`.

The acceptance equivalence `Inference.sourceTypable_iff_infer_isSome` and result
soundness `Inference.inferType_success_sourceTyping` are also re-exported because
they state the two most useful API-level corollaries of the headline results.
-/
