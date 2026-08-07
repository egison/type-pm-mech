import TypePM.CertifiedInferenceRegression
import TypePM.CoherentTyping

/-!
# Acceptance gap regressions

`Coherent.AnnotationFree` is a target for the completed inference pipeline,
not a property of the current one.  This module pins the first concrete
counterexample for the shipped `infer`: an or-pattern binding the same
variable in both alternatives.  Declaratively both alternatives may choose
the same fresh binder pair, so the program is typed at `List Integer`; the
executable traversal freshens each alternative separately and then demands
syntactically equal raw binding contexts, so already the raw traversal
fails.  `annotationFree_current_refuted` records the resulting refutation of
the goal proposition for the current pipeline.

The intended fix — sharing one binder skeleton across the alternatives, or
aligning binders by name and emitting type constraints instead of comparing
raw metavariable identities — is roadmap work; these regressions keep the
gap visible (and will fail closed) until it lands.
-/

namespace TypePM
namespace AcceptanceGapRegression

open CertifiedInferenceRegression

/-- `matchAll 0 something ($x | $x) x` — both alternatives bind `x`. -/
def orProgram : Expr :=
  .matchAll (.lit 0) .something
    (.por (.pvar "x") (.pvar "x")) (.var "x")

/-- The single-alternative control is accepted by public inference. -/
theorem orControl_accepted :
    Inference.inferenceSucceeds emptySignature []
      (.matchAll (.lit 0) .something (.pvar "x") (.var "x")) = true := by
  native_decide

/-- The or-pattern program is rejected already by the raw traversal. -/
theorem orProgram_raw_rejected :
    (Inference.inferRaw emptySignature [] orProgram).isSome = false := by
  native_decide

/-- Public inference therefore rejects it as well. -/
theorem orProgram_rejected :
    Inference.inferenceSucceeds emptySignature [] orProgram = false := by
  native_decide

/-- The prevailing substitution of the declarative derivation below. -/
def orPrevailing : Subst :=
  Subst.mk (Unification.CapSubst.single 0 .any)
    (Unification.TySubst.single 0 .int)

/-- One alternative, resolved at the shared fresh binder pair. -/
private theorem orBranch_resolved :
    TerminalPatternResolution emptySignature orPrevailing [] [] []
      (.pvar "x") .any .int [("x", .int)] :=
  TerminalPatternResolution.pvar
    (rawContext := []) (rawParameters := []) (rawBindings := [])
    (name := "x") (capVar := 0) (tyVar := 0) (actualContext := [])
    (by decide)
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩

/-- Declaratively both alternatives may choose the same fresh binder pair, so
the or-pattern resolves. -/
theorem orPattern_resolved :
    ResolvedPatternTy emptySignature orPrevailing [] [] []
      (.por (.pvar "x") (.pvar "x")) .any .int [("x", .int)] :=
  ResolvedPatternTy.ofTerminal
    (TerminalPatternResolution.or orBranch_resolved orBranch_resolved)

/-- `something` inhabits the slot demanded by the match site. -/
private theorem something_slot_typed :
    HasTy emptySignature [] .something (.slot .any .int) := by
  refine HasTy.coerceMatcherToSlot
    (producerCap := .any) (consumerCap := .any)
    (producerTarget := .int) (consumerTarget := .int)
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    HasTy.something ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := rfl
      rangeFixed := Subst.id_rangeFixed }

/-- Declaratively the or-pattern program is typed at `List Integer`. -/
theorem orProgram_typed :
    HasTy emptySignature [] orProgram (Ty.listT .int) :=
  HasTy.matchAll (prevailing := orPrevailing)
    HasTy.lit orPattern_resolved something_slot_typed
    (HasTy.var rfl (Scheme.mono_valueFlowInst _))

/-- The annotation-freeness proposition is refuted for the current
inferencer: fixing the or-pattern binder discipline is prerequisite roadmap
work before the goal can be established. -/
theorem annotationFree_current_refuted : ¬ Coherent.AnnotationFree := by
  intro h
  have accepted := h emptySignature orProgram (Ty.listT .int) orProgram_typed
  rw [orProgram_rejected] at accepted
  exact Bool.noConfusion accepted

end AcceptanceGapRegression
end TypePM
