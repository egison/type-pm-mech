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

The second gap is pinned below: a shared monomorphic consumer that
declaratively has a wildcard slot domain (`Slot Any (prod [Int, Int])`) can
consume both a bare `something` and a product of `something`s through
explicit coercions, but the executable pipeline resolves the consumer's
domain from the first use to the raw `Matcher Any ?τ` and then compares the
product lift's capability `prod [Any, Any]` against `Any` as a rigid
annotation inside `mguTy`, so the program is rejected.  The swapped order is
rejected as well: there the domain is pinned to the raw product of matchers
and the second use fails against a non-matcher expected head before any
coercion branch fires.  Both witnesses refute `AnnotationFree` for the
current inferencer and are scheduled to be fixed by the origin-aware
recursive paired unifier (and the solve-cut event for the swapped order).
The remaining conceptual gap — constructor/primitive instance capabilities
pinned by the producer guard (`Pack something`) — is tracked on the roadmap
and will be pinned once its signature fixture is expressible.
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

/-! ## Nested matcher capability: rigid annotation comparison -/

/-- A shared monomorphic consumer applied to two matcher producers whose
capabilities differ: the bare `something` synthesizes `Matcher Any ?τ`,
while the tuple lifts to `Matcher (prod [Any, Any]) (prod [?τ₁, ?τ₂])`. -/
def nestedCapProgram : Expr :=
  .app
    (.lam "f" (.tuple
      [.app (.var "f") .something,
       .app (.var "f") (.tuple [.something, .something])]))
    (.lam "m" (.var "m"))

/-- The same program with the product producer consumed first. -/
def nestedCapSwappedProgram : Expr :=
  .app
    (.lam "f" (.tuple
      [.app (.var "f") (.tuple [.something, .something]),
       .app (.var "f") .something]))
    (.lam "m" (.var "m"))

/-- The declarative domain shared by both uses: a wildcard-consumer slot. -/
def sharedSlot : Ty := .slot .any (.prod [.int, .int])

/-- The context binding the consumer at its monomorphic slot type. -/
def consumerContext : Context :=
  [("f", Scheme.mono (.fn sharedSlot sharedSlot))]

/-- `something` fills the wildcard slot at the product target. -/
private theorem something_sharedSlot_typed :
    HasTy emptySignature consumerContext .something sharedSlot := by
  refine HasTy.coerceMatcherToSlot
    (producerCap := .any) (consumerCap := .any)
    (producerTarget := .prod [.int, .int])
    (consumerTarget := .prod [.int, .int])
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    HasTy.something ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := rfl
      rangeFixed := Subst.id_rangeFixed }

/-- The tuple of `something`s lifts to a product matcher. -/
private theorem tuple_productMatcher_typed :
    HasTy emptySignature consumerContext (.tuple [.something, .something])
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  HasTy.coerceProductMatcher
    (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
    (HasTy.tuple (ExprsTy.cons HasTy.something
      (ExprsTy.cons HasTy.something ExprsTy.nil)))

/-- The product matcher also fills the wildcard slot: the consumer-side
literal `Any` accepts the structured producer capability. -/
private theorem tuple_sharedSlot_typed :
    HasTy emptySignature consumerContext (.tuple [.something, .something])
      sharedSlot := by
  refine HasTy.coerceMatcherToSlot
    (producerCap := .prod [.any, .any]) (consumerCap := .any)
    (producerTarget := .prod [.int, .int])
    (consumerTarget := .prod [.int, .int])
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    tuple_productMatcher_typed ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := rfl
      rangeFixed := Subst.id_rangeFixed }

/-- The shared consumer variable at its monomorphic type. -/
private theorem consumer_var_typed :
    HasTy emptySignature consumerContext (.var "f")
      (.fn sharedSlot sharedSlot) :=
  HasTy.var rfl (Scheme.mono_valueFlowInst _)

/-- Declaratively the program is typed: both producers coerce into the same
wildcard slot domain. -/
theorem nestedCapProgram_typed :
    HasTy emptySignature [] nestedCapProgram
      (.prod [sharedSlot, sharedSlot]) :=
  HasTy.app
    (HasTy.lam (HasTy.tuple
      (ExprsTy.cons (HasTy.app consumer_var_typed something_sharedSlot_typed)
        (ExprsTy.cons
          (HasTy.app consumer_var_typed tuple_sharedSlot_typed)
          ExprsTy.nil))))
    (HasTy.lam (HasTy.var rfl (Scheme.mono_valueFlowInst _)))

/-- The swapped order is typed by the same pieces. -/
theorem nestedCapSwappedProgram_typed :
    HasTy emptySignature [] nestedCapSwappedProgram
      (.prod [sharedSlot, sharedSlot]) :=
  HasTy.app
    (HasTy.lam (HasTy.tuple
      (ExprsTy.cons (HasTy.app consumer_var_typed tuple_sharedSlot_typed)
        (ExprsTy.cons
          (HasTy.app consumer_var_typed something_sharedSlot_typed)
          ExprsTy.nil))))
    (HasTy.lam (HasTy.var rfl (Scheme.mono_valueFlowInst _)))

/-- Consuming the same producer twice is accepted: the shared domain
resolves to one raw matcher type and the second use aligns rigidly. -/
theorem nestedCapControl_accepted :
    Inference.inferenceSucceeds emptySignature []
      (.app
        (.lam "f" (.tuple
          [.app (.var "f") .something,
           .app (.var "f") .something]))
        (.lam "m" (.var "m"))) = true := by
  native_decide

/-- The pipeline rejects the program: the first use pins the domain to the
raw `Matcher Any ?τ`, and the second compares the lifted capability
`prod [Any, Any]` against `Any` as a rigid annotation inside `mguTy`. -/
theorem nestedCapProgram_rejected :
    Inference.inferenceSucceeds emptySignature [] nestedCapProgram =
      false := by
  native_decide

/-- The swapped order is rejected as well: the domain is pinned to the raw
product of matchers, and the bare `something` then fails against a
non-matcher expected head before any coercion branch fires. -/
theorem nestedCapSwappedProgram_rejected :
    Inference.inferenceSucceeds emptySignature [] nestedCapSwappedProgram =
      false := by
  native_decide

/-- The nested-capability gap refutes annotation-freeness for the current
inferencer; the goal statement stays a target for the origin-aware solver. -/
theorem annotationFree_current_refuted : ¬ Coherent.AnnotationFree := by
  intro hfree
  have haccept :=
    hfree emptySignature nestedCapProgram (.prod [sharedSlot, sharedSlot])
      nestedCapProgram_typed
  rw [nestedCapProgram_rejected] at haccept
  cases haccept

end AcceptanceGapRegression
end TypePM
