import TypePM.CertifiedInferenceRegression
import TypePM.CoherentTyping

/-!
# Acceptance gap regressions

This module tracks the concrete acceptance gaps between declarative typing
and the executable pipeline.  The first gap — an or-pattern binding the same
variable in both alternatives, previously rejected because the traversal
compared raw binding contexts for syntactic identity — is fixed: the or case
now aligns binder names positionally and unifies the bound types
(`alignBindings`), so both the original program and a variant binding `x` at
different positions of the alternatives are accepted.  The declarative
derivation is kept alongside as the specification witness.

The remaining known gaps (constructor/primitive instance capabilities pinned
by the producer guard, and nested matcher capabilities compared rigidly) are
conceptual and tracked on the roadmap together with the origin-aware paired
unifier; they will be pinned here once their signatures are expressible.
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

/-- The or-pattern program is accepted: both alternatives may allocate
separate metavariables for `x`, and the or case aligns the binding contexts
by name instead of comparing raw identities. -/
theorem orProgram_accepted :
    Inference.inferenceSucceeds emptySignature [] orProgram = true := by
  native_decide

/-- Alignment also identifies binders sitting at different positions of the
alternatives. -/
def orMixedProgram : Expr :=
  .matchAll (.lit 0) .something
    (.por (.pand (.pvar "x") .wild) (.pand .wild (.pvar "x"))) (.var "x")

theorem orMixedProgram_accepted :
    Inference.inferenceSucceeds emptySignature [] orMixedProgram = true := by
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

end AcceptanceGapRegression
end TypePM
