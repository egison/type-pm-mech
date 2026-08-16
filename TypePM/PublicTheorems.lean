import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingTargetUniqueness
import TypePM.SourcePrincipality
import TypePM.RelativePrincipality
import TypePM.PrincipalityCounterexample
import TypePM.Soundness
import TypePM.Readiness
import TypePM.InterpreterDispatchBridge
import TypePM.InterpreterCompleteness
import TypePM.InterpreterRegression
import TypePM.DamasMilnerConservativity
import TypePM.DamasMilnerAcceptanceMutual

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
* `MStateTy.progress_of_evals` — a typed nonterminal matching state whose
  embedded evaluations converge takes one concrete step; decode success and
  dispatch reachability are discharged from the typing evidence, so the
  `StepReady` premise of local progress reduces to convergence alone.
* `typed_never_stuck_runtime` — expression-layer progress for a checked,
  scoped runtime pattern-function table: a typed closed program run by the
  fuel-indexed reference interpreter never reaches a stuck configuration at
  any fuel.  Proved by `noStuck_master`, a strong
  induction on fuel that ties every interpreter layer (expression, atom,
  state, search, clause dispatch, header match) to its safety statement.
* `typed_never_stuck` — the empty-runtime specialization.
* `SourceTyping.never_stuck_paper1` — source-facing specialization for the
  paper-1 fragment, explicitly requiring `signature.patternFuns = []` and
  deriving global empty-runtime agreement via `runtimeSigAgrees_nil`.
* `typed_all_timeout_iff_no_finite_eval` — for a typed closed program,
  timeout at every fuel is equivalent to the absence of a finite relational
  evaluation; this is not presented as a coinductive divergence theorem.
* `SourceTyping.all_timeout_iff_no_finite_eval_paper1` — the corresponding
  source-facing paper-1 specialization.
* `evalFuel_ok` — adequacy of the reference interpreter: every successful
  fuel-indexed run replays as a relational big-step derivation, connecting
  `typed_never_stuck` to the relational preservation theorems.
* `evalFuel_eventually_ok` — completeness of the reference interpreter:
  every finite relational evaluation is reproduced at some fuel and at all
  larger fuels.  Together with adequacy, persistent timeout means precisely
  that no finite relational evaluation exists; identifying that fact with a
  separate coinductive divergence judgment would require another theorem.
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
* `DM.Typing.inferenceSucceeds` — every Damas--Milner typing derivation is
  accepted by executable inference on the embedded context.  The result does
  not identify the derivation's selected target with the inference return
  value syntactically.
* `PrincipalityCounterexample.no_principal_type` — the internal
  `TypingInvariant` family is not a source principal-type
  specification; this is not a counterexample about `SourceTyping`.

The acceptance equivalence `Inference.sourceTypable_iff_infer_isSome` and result
soundness `Inference.inferType_success_sourceTyping` are also re-exported because
they state the two most useful API-level corollaries of the headline results.
-/
