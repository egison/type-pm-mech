import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.DemandTypingInferenceSoundnessPublic

/-!
# Executable acceptance equivalence

Executable soundness and acceptance completeness combine into a decision
procedure for the demand-directed source judgment.  The main equivalence is
stated for an arbitrary source context; the closed-program theorem is the
annotation-freeness boundary advertised by the public development.

`inferType` reports the type of its unique executable run.  We prove that
this reported type has a `SourceTyping` derivation.  We deliberately do not claim
that it equals the target of every independently supplied `SourceTyping`
derivation: such a statement would require a separate uniqueness or
principality theorem (possibly modulo metavariable renaming).
-/

namespace TypePM
namespace Inference

open DemandTypingInferenceCompletenessPublic

/-- Demand-directed typability is exactly acceptance by public inference.

Unlike the dynamic-safety corollary, this theorem is valid for arbitrary
contexts: executable-to-demand-directed soundness and demand-directed-to-executable completeness are
both already context-general. -/
theorem sourceTypable_iff_infer_isSome
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature context expression target) ↔
      (infer signature context expression).isSome = true := by
  constructor
  · rintro ⟨target, typed⟩
    exact SourceTyping.infer_isSome typed signatureWF
  · intro present
    let result := (infer signature context expression).get present
    have success : infer signature context expression = some result :=
      option_eq_some_get_of_isSome _ present
    exact ⟨result.resolvedTarget, infer_success_sourceTyping success⟩

/-- The public result-type projection succeeds exactly when full inference
succeeds. -/
theorem inferType_isSome_eq_infer_isSome
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    (inferType signature context expression).isSome =
      (infer signature context expression).isSome := by
  unfold inferType
  cases infer signature context expression <;> simp

/-- The type returned by `inferType` is accepted by the demand-directed
source judgment.  This is result soundness, not uniqueness of all possible
demand-directed targets. -/
theorem inferType_success_sourceTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (success : inferType signature context expression = some target) :
    SourceTyping signature context expression target := by
  unfold inferType at success
  cases runEq : infer signature context expression with
  | none => simp [runEq] at success
  | some result =>
      have targetEq : result.resolvedTarget = target := by
        simpa [runEq] using success
      rw [← targetEq]
      exact infer_success_sourceTyping runEq

/-- Typability is equivalently witnessed by the concrete type returned by
`inferType`, together with its demand-directed derivation.  The source target used to prove
the forward direction need not be definitionally equal to the returned one;
no principality claim is hidden in this statement. -/
theorem sourceTypable_iff_inferType_some_sourceTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature context expression target) ↔
      ∃ target, inferType signature context expression = some target ∧
        SourceTyping signature context expression target := by
  constructor
  · rintro ⟨sourceTarget, typed⟩
    have present : (infer signature context expression).isSome = true :=
      SourceTyping.infer_isSome typed signatureWF
    let result := (infer signature context expression).get present
    have success : infer signature context expression = some result :=
      option_eq_some_get_of_isSome _ present
    refine ⟨result.resolvedTarget, ?_, infer_success_sourceTyping success⟩
    simp [inferType, success]
  · rintro ⟨target, _returned, typed⟩
    exact ⟨target, typed⟩

/-- Ergonomic result-presence form: a source term is demand-directed-typable exactly when
`inferType` returns some type.  The stronger preceding theorem additionally
records that the concrete returned type itself has a demand-directed derivation. -/
theorem sourceTypable_iff_inferType_eq_some
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature context expression target) ↔
      ∃ inferred, inferType signature context expression = some inferred := by
  constructor
  · intro typed
    rcases (sourceTypable_iff_inferType_some_sourceTyping signatureWF).1 typed with
      ⟨inferred, returned, _typed⟩
    exact ⟨inferred, returned⟩
  · rintro ⟨inferred, returned⟩
    exact ⟨inferred, inferType_success_sourceTyping returned⟩

/-- Equivalent Boolean presentation through the public type-only API. -/
theorem sourceTypable_iff_inferType_isSome
    {signature : FrozenSig} {context : Context} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature context expression target) ↔
      (inferType signature context expression).isSome = true := by
  rw [inferType_isSome_eq_infer_isSome]
  exact sourceTypable_iff_infer_isSome signatureWF

/-- Closed-program annotation-freeness.  `Expr` contains no type-ascription
constructor, so public inference decides whether an unannotated closed source
term has some `SourceTyping` derivation. -/
theorem closed_sourceTypable_iff_infer_isSome
    {signature : FrozenSig} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature [] expression target) ↔
      (infer signature [] expression).isSome = true :=
  sourceTypable_iff_infer_isSome signatureWF

/-- Public annotation-freeness theorem for closed source programs. -/
theorem annotation_freeness
    {signature : FrozenSig} {expression : Expr}
    (signatureWF : FrozenSigWF signature) :
    (∃ target, SourceTyping signature [] expression target) ↔
      (infer signature [] expression).isSome = true :=
  closed_sourceTypable_iff_infer_isSome signatureWF

/-- Demand-directed typability is decidable by running public inference.
The `FrozenSigWF` proof is used only to reflect a negative executable answer
back to the source judgment. -/
def sourceTypableDecidable
    (signature : FrozenSig) (context : Context) (expression : Expr)
    (signatureWF : FrozenSigWF signature) :
    Decidable (∃ target, SourceTyping signature context expression target) :=
  if present : (infer signature context expression).isSome = true then
    isTrue ((sourceTypable_iff_infer_isSome signatureWF).2 present)
  else
    isFalse fun typed =>
      present ((sourceTypable_iff_infer_isSome signatureWF).1 typed)

end Inference
end TypePM
