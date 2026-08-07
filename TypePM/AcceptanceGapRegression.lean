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

The second family is pinned below as a boundary example of the wide
declarative system, not as an inference defect: a shared monomorphic
consumer declaratively receives the wildcard slot domain
(`Slot Any (prod [Int, Int])`) and consumes both a bare `something` and a
product of `something`s, but only through `coerceMatcherToSlot` steps taken
at argument positions where no slot demand exists — the domain is a plain
lambda-bound metavariable, and the derivation invents the slot structure
that makes both coercions succeed.  The pipeline is demand-directed:
coercions are inserted only where the substituted expected type already
demands a matcher/slot head, and unresolved domains are never structured to
enable a coercion.  It therefore resolves the domain from the first use to
the raw `Matcher Any ?τ` and rejects the product lift's capability
`prod [Any, Any]` against `Any` inside `mguTy`; the swapped order is
rejected against a non-matcher expected head.  Both rejections are intended
behaviour and permanently refute the wide-premise `AnnotationFree`
(`annotationFree_wide_refuted`); they are not scheduled to be fixed by the
origin-aware unifier.  The accepted idiom — let-polymorphism giving each
use its own domain instance — is pinned as `nestedCapLetProgram_accepted`.

The third gap — constructor instance capabilities pinned by the producer
guard — is pinned below as well: `Pack : ∀κ α. Matcher κ α → Packed`
declaratively instantiates `κ := Any`, so `Pack something` is typed, but the
executable pipeline records the fresh instance capability as a protected
producer variable and the guard rejects the solver step that would bind it,
so the program is rejected.  The control signature that fixes the field
capability to `Any` in the scheme itself is accepted.  This is the
`structuralFlexible`-versus-`protectedCaps` discrepancy that the
origin-aware ledger (`CapabilityOrigin`) already records as shadow
metadata; switching the guard to the ledger is the scheduled fix.
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

/-- The accepted idiom for the two producers: `let`-polymorphism gives each
use its own instance of the generalized domain, so no demand-free coercion
is needed. -/
def nestedCapLetProgram : Expr :=
  .letE "f" (.lam "m" (.var "m"))
    (.tuple
      [.app (.var "f") .something,
       .app (.var "f") (.tuple [.something, .something])])

theorem nestedCapLetProgram_accepted :
    Inference.inferenceSucceeds emptySignature [] nestedCapLetProgram =
      true := by
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

/-- The nested-capability boundary example permanently refutes the
wide-premise `AnnotationFree`: the declarative typing exists only through
demand-free matcher-to-slot coercions, and rejecting those is the intended
demand-directed behaviour.  The pursued completeness statement keeps the
conclusion but replaces the wide `HasTy` premise with a demand-directed
judgment (stage 3 of the roadmap). -/
theorem annotationFree_wide_refuted : ¬ Coherent.AnnotationFree := by
  intro hfree
  have haccept :=
    hfree emptySignature nestedCapProgram (.prod [sharedSlot, sharedSlot])
      nestedCapProgram_typed
  rw [nestedCapProgram_rejected] at haccept
  cases haccept

/-! ## Capability freeze: constructor instance capabilities -/

/-- `Pack : ∀κ α. Matcher κ α → Packed` — a constructor whose field
mentions its capability binder. -/
def packScheme : CtorScheme where
  capBinders := [0]
  tyBinders := [0]
  args := [.matcher (.var 0) (.var 0)]
  result := .data "Packed" []

/-- A signature holding only the polymorphic `Pack` constructor. -/
def packSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("Pack", packScheme)]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

/-- The control scheme fixes the field capability to `Any` itself. -/
def packMonoScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [.matcher .any (.var 0)]
  result := .data "Packed" []

/-- The control signature holding the capability-monomorphic `Pack`. -/
def packMonoSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("Pack", packMonoScheme)]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

/-- The freeze-gap program. -/
def packProgram : Expr := .ctor "Pack" [.something]

/-- Declaratively the constructor instance may choose `κ := Any`, so the
program is typed. -/
theorem packProgram_typed :
    HasTy packSignature [] packProgram (.data "Packed" []) := by
  refine HasTy.ctor (scheme := packScheme)
    (targets := [.matcher .any .int]) rfl ?_ ?_
  · refine ⟨Unification.CapSubst.single 0 .any,
      Unification.TySubst.single 0 .int, ?_,
      Unification.TySubst.single_supportWithin 0 .int, ?_, rfl⟩
    · intro candidate outside
      simp only [packScheme, List.mem_singleton] at outside
      have reverse : (0 : CapVar) ≠ candidate := Ne.symm outside
      simp [Unification.CapSubst.single, reverse]
    · simp [packScheme, Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Cap.apply, Unification.CapSubst.single, Unification.TySubst.single]
  · exact ExprsTy.cons HasTy.something ExprsTy.nil

/-- Raw W already rejects the instance: the fresh capability of the value
producer instance is protected and the guard refuses to bind it. -/
theorem packProgram_raw_rejected :
    (Inference.inferRaw packSignature [] packProgram).isSome = false := by
  native_decide

/-- Public inference rejects the freeze-gap program. -/
theorem packProgram_rejected :
    Inference.inferenceSucceeds packSignature [] packProgram = false := by
  native_decide

/-- Fixing the capability in the scheme itself is accepted, so the
rejection is exactly about the protected fresh instance capability. -/
theorem packMonoProgram_accepted :
    Inference.inferenceSucceeds packMonoSignature [] packProgram = true := by
  native_decide

/-- The freeze gap independently refutes annotation-freeness for the
current inferencer. -/
theorem annotationFree_current_refuted_by_freeze :
    ¬ Coherent.AnnotationFree := by
  intro hfree
  have haccept :=
    hfree packSignature packProgram (.data "Packed" []) packProgram_typed
  rw [packProgram_rejected] at haccept
  cases haccept

end AcceptanceGapRegression
end TypePM
