import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingTargetUniqueness
import TypePM.PrincipalityCounterexample
import TypePM.Soundness

/-!
# Public theorem index

This import-only facade gives reviewers and the paper one stable module from
which to find the main results.  The declarations retain their original
namespaces and source modules; no compatibility aliases or duplicate theorem
statements are introduced.

* `Inference.annotation_freeness` — closed source terms need no type
  annotation for DD typability to be decided by public inference.
* `DDTyping.infer_isSome` — an audited DD derivation is accepted by public
  inference under the frozen-signature boundary.
* `Inference.infer_success_ddTyping` — every successful public inference run
  reconstructs source-facing demand-directed typing at its reported type.
* `DDTyping.safe` — closed DD typing enters the concrete dynamic safety
  package under the single public signature condition.
* `DDTyping.runtimeTyping` — closed DD typing erases to the internal
  state-free runtime certificate at exactly its published type.
* `DDTyping.target_unique_modulo_renaming` — any two audited DD targets for
  the same source share a representative up to residual two-sort renaming.
* `PrincipalityCounterexample.no_principal_type` — the internal
  `RuntimeTyping` certificate family is not a source principal-type
  specification; this is not a counterexample about `DDTyping`.

The acceptance equivalence `Inference.ddTypable_iff_infer_isSome` and result
soundness `Inference.inferType_success_ddTyping` are also re-exported because
they state the two most useful API-level corollaries of the six headline
results.
-/
