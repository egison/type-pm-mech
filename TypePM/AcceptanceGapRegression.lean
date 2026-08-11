import TypePM.CertifiedInferenceRegression
import TypePM.CoherentTyping

/-!
# DD acceptance and state-erasure boundary regressions

This module tracks concrete boundaries of DD acceptance and the internal
runtime certificate.  The first gap — an or-pattern binding the same
variable in both alternatives, previously rejected because the traversal
compared raw binding contexts for syntactic identity — is fixed: the or case
now aligns binder names positionally and unifies the bound types
(`alignBindings`), so both the original program and a variant binding `x` at
different positions of the alternatives are accepted.  Its runtime
certificate is kept as a downstream safety witness.

The second family shows why `RuntimeTyping` must not be read backwards as a
source-acceptance rule: a shared monomorphic consumer receives the wildcard slot domain
(`Slot Any (prod [Int, Int])`) and consumes both a bare `something` and a
product of `something`s.  The exhibited derivations below choose
`coerceMatcherToSlot` steps at argument positions where no slot demand exists
— the domain is a plain lambda-bound metavariable, and those witnesses invent
the slot structure that makes both coercions succeed.  No inversion theorem
claiming that every `RuntimeTyping` certificate must have this form is made here.
The pipeline is demand-directed:
coercions are inserted only where the substituted expected type already
demands a slot head, and unresolved domains are never structured to
enable a coercion.  It therefore resolves the domain from the first use to
the raw `Matcher Any ?τ`, and the second use finds no slot demand there:
the raw product of matchers stays unlifted and ordinary alignment rejects
the `prod`/`matcher` head mismatch.  In the swapped order the domain is
pinned to the raw product type and the bare matcher likewise meets no slot
demand.  Both rejections are intended behaviour.  The accepted idiom —
let-polymorphism giving each
use its own domain instance — is pinned as `nestedCapLetProgram_accepted`.

The former third gap — constructor instance capabilities pinned before their
local argument solve — is closed below.  For
`Pack : ∀κ α. Matcher κ α → Packed`, the fresh instance of `κ` is marked
`structuralFlexible`, the paired solver specializes it to `Any`, and the
export boundary freezes only variable leaves that survive in the prevailing
result.  Since `Packed` exports no capability, this instance leaves no frozen
leaf.  A separate structured-image regression shows that if a local image
does survive, its prevailing leaf is frozen to `renameOnly` and cannot later
be structurally strengthened.
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

/-- The prevailing substitution of the runtime certificate below. -/
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
    RuntimeTyping emptySignature [] .something (.slot .any .int) := by
  refine RuntimeTyping.coerceMatcherToSlot
    (producerCap := .any) (consumerCap := .any)
    (producerTarget := .int) (consumerTarget := .int)
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    RuntimeTyping.something ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := Unification.mguTy_self _
      rangeFixed := Subst.id_rangeFixed }

/-- Declaratively the or-pattern program is typed at `List Integer`. -/
theorem orProgram_typed :
    RuntimeTyping emptySignature [] orProgram (Ty.listT .int) :=
  RuntimeTyping.matchAll (prevailing := orPrevailing)
    RuntimeTyping.lit orPattern_resolved something_slot_typed
    (RuntimeTyping.var rfl (Scheme.mono_valueFlowInst _))

/-! ## Nested matcher capability: DD rejection boundary -/

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
    RuntimeTyping emptySignature consumerContext .something sharedSlot := by
  refine RuntimeTyping.coerceMatcherToSlot
    (producerCap := .any) (consumerCap := .any)
    (producerTarget := .prod [.int, .int])
    (consumerTarget := .prod [.int, .int])
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    RuntimeTyping.something ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := Unification.mguTy_self _
      rangeFixed := Subst.id_rangeFixed }

/-- The tuple of `something`s lifts to a product matcher. -/
private theorem tuple_productMatcher_typed :
    RuntimeTyping emptySignature consumerContext (.tuple [.something, .something])
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) :=
  RuntimeTyping.coerceProductMatcher
    (duals := [⟨.any, .int⟩, ⟨.any, .int⟩])
    (RuntimeTyping.tuple (ExprsTy.cons RuntimeTyping.something
      (ExprsTy.cons RuntimeTyping.something ExprsTy.nil)))

/-- The product matcher also fills the wildcard slot: the consumer-side
literal `Any` accepts the structured producer capability. -/
private theorem tuple_sharedSlot_typed :
    RuntimeTyping emptySignature consumerContext (.tuple [.something, .something])
      sharedSlot := by
  refine RuntimeTyping.coerceMatcherToSlot
    (producerCap := .prod [.any, .any]) (consumerCap := .any)
    (producerTarget := .prod [.int, .int])
    (consumerTarget := .prod [.int, .int])
    (bindings := []) (C := CapSubst.id) (T := TySubst.id) (post := Subst.id)
    tuple_productMatcher_typed ?_ VariablePost.id
  exact
    { matched := rfl
      capSubstitution := rfl
      targetUnified := Unification.mguTy_self _
      rangeFixed := Subst.id_rangeFixed }

/-- The shared consumer variable at its monomorphic type. -/
private theorem consumer_var_typed :
    RuntimeTyping emptySignature consumerContext (.var "f")
      (.fn sharedSlot sharedSlot) :=
  RuntimeTyping.var rfl (Scheme.mono_valueFlowInst _)

/-- Declaratively the program is typed: both producers coerce into the same
wildcard slot domain. -/
theorem nestedCapProgram_typed :
    RuntimeTyping emptySignature [] nestedCapProgram
      (.prod [sharedSlot, sharedSlot]) :=
  RuntimeTyping.app
    (RuntimeTyping.lam (RuntimeTyping.tuple
      (ExprsTy.cons (RuntimeTyping.app consumer_var_typed something_sharedSlot_typed)
        (ExprsTy.cons
          (RuntimeTyping.app consumer_var_typed tuple_sharedSlot_typed)
          ExprsTy.nil))))
    (RuntimeTyping.lam (RuntimeTyping.var rfl (Scheme.mono_valueFlowInst _)))

/-- The swapped order is typed by the same pieces. -/
theorem nestedCapSwappedProgram_typed :
    RuntimeTyping emptySignature [] nestedCapSwappedProgram
      (.prod [sharedSlot, sharedSlot]) :=
  RuntimeTyping.app
    (RuntimeTyping.lam (RuntimeTyping.tuple
      (ExprsTy.cons (RuntimeTyping.app consumer_var_typed tuple_sharedSlot_typed)
        (ExprsTy.cons
          (RuntimeTyping.app consumer_var_typed something_sharedSlot_typed)
          ExprsTy.nil))))
    (RuntimeTyping.lam (RuntimeTyping.var rfl (Scheme.mono_valueFlowInst _)))

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

/-- The polymorphic control keeps both producer forms raw.  The concrete
target-variable identifiers are intentionally ignored, but the three targets
must remain pairwise-distinct variables: the stable shape is a bare matcher
in the first component and an unlifted product of two bare matchers in the
second. -/
def nestedCapLetRawTargetShape : Ty → Bool
  | .prod [.matcher .any (.var first),
      .prod [.matcher .any (.var second),
        .matcher .any (.var third)]] =>
      first != second && first != third && second != third
  | _ => false

/-- Check that a successful raw result contains no matcher-to-slot solver
constraint.  Returning `false` for `none` makes this check pin raw acceptance
as well as the absence of the coercion. -/
def rawResultHasNoProducerToSlot : Option Inference.ExprResult → Bool
  | none => false
  | some result =>
      result.state.trace.solves.all fun step =>
        match step.constraint with
        | .producerToSlot _ _ _ _ => false
        | _ => true

/-- Raw inference returns exactly the intended producer-level result shape. -/
theorem nestedCapLetProgram_raw_target_shape :
    (match Inference.inferRawType emptySignature [] nestedCapLetProgram with
      | none => false
      | some target => nestedCapLetRawTargetShape target) = true := by
  native_decide

/-- Let-polymorphism accepts the two uses without emitting any
`producerToSlot` constraint. -/
theorem nestedCapLetProgram_raw_has_no_producerToSlot :
    rawResultHasNoProducerToSlot
      (Inference.inferRaw emptySignature [] nestedCapLetProgram) = true := by
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

/-- The former freeze-gap program. -/
def packProgram : Expr := .ctor "Pack" [.something]

/-- Declaratively the constructor instance may choose `κ := Any`, so the
program is typed. -/
theorem packProgram_typed :
    RuntimeTyping packSignature [] packProgram (.data "Packed" []) := by
  refine RuntimeTyping.ctor (scheme := packScheme)
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
  · exact ExprsTy.cons RuntimeTyping.something ExprsTy.nil

/-- Raw W accepts the local structural specialization. -/
theorem packProgram_raw_accepted :
    (Inference.inferRaw packSignature [] packProgram).isSome = true := by
  native_decide

/-- Certified public inference accepts the former freeze-gap program. -/
theorem packProgram_accepted :
    Inference.inferenceSucceeds packSignature [] packProgram = true := by
  native_decide

/-- A tuple of matchers offered to the same matcher-headed constructor
field. -/
def packPairProgram : Expr := .ctor "Pack" [.tuple [.something, .something]]

/-- A matcher-headed constructor field is not a slot demand: the raw product
of matchers is not lifted there, so `Pack (something, something)` is
rejected while the raw matcher argument of `packProgram` is accepted by
ordinary alignment.  This pins the intended boundary of the slot-demand
principle at a signature-declared matcher position. -/
theorem packPairProgram_rejected :
    Inference.inferenceSucceeds packSignature [] packPairProgram = false := by
  native_decide

/-- The concrete successful public result, extracted from the executable
acceptance check. -/
def packResult : Inference.ExprResult :=
  (Inference.infer packSignature [] packProgram).get packProgram_accepted

/-- The public result equation retained for soundness and coherence reuse. -/
theorem packProgram_result :
    Inference.infer packSignature [] packProgram = some packResult :=
  Inference.option_eq_some_get_of_isSome _ packProgram_accepted

/-- The accepted program has the constructor's declared result type. -/
theorem packProgram_result_type :
    packResult.resolvedTarget = .data "Packed" [] := by
  native_decide

/-- Acceptance carries the recursive coherent reconstruction certificate. -/
theorem packProgram_coherent :
    Coherent.CoherentExpr packSignature [] packProgram
      packResult.resolvedTarget := by
  simpa [Inference.ResolvedContext, Context.applySubst] using
    Coherent.infer_success_coherent packProgram_result

/-- Public inference independently reconstructs the advertised runtime
certificate from the executable success equation. -/
theorem packProgram_typed_by_inference :
    RuntimeTyping packSignature [] packProgram (.data "Packed" []) := by
  have typing := Inference.infer_success_runtimeTyping packProgram_result
  rw [packProgram_result_type] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

/-- The local `κ = Any` solve observes `κ` as structurally flexible at that
exact chronological cut. -/
def packTraceHasFlexibleCapabilitySolve : Bool :=
  match Inference.inferRaw packSignature [] packProgram with
  | none => false
  | some result =>
      result.state.trace.solves.any fun step =>
        match step.constraint with
        | .capEq (.var varId) .any
        | .capEq .any (.var varId) =>
            step.ledgerSnapshot.originOf varId ==
              .structuralFlexible &&
                step.delta.cap varId == .any
        | _ => false

theorem packProgram_uses_flexible_capability_solve :
    packTraceHasFlexibleCapabilitySolve = true := by
  native_decide

/-- `Pack` exports no capability, so its nonempty raw binder-image list
produces an empty export-freeze leaf list. -/
def packTraceHasEmptyExportLeaves : Bool :=
  match Inference.inferRaw packSignature [] packProgram with
  | none => false
  | some result =>
      result.state.trace.events.any fun event =>
        match event with
        | .capabilityExportFreeze _ capImages _ _ leaves =>
            !capImages.isEmpty && leaves.isEmpty
        | _ => false

theorem packProgram_freezes_no_dead_capability_leaf :
    packTraceHasEmptyExportLeaves = true := by
  native_decide

/-- Fixing the capability in the scheme itself is accepted, so the
monomorphic control remains accepted. -/
theorem packMonoProgram_accepted :
    Inference.inferenceSucceeds packMonoSignature [] packProgram = true := by
  native_decide

/-! ### Prevailing-image leaves are frozen, not the dead local root -/

/-- A synthetic local constructor solve in which binder `κ₀` receives the
structured image `List κ₁`; both variables are local and flexible. -/
def structuredExportStart : Inference.InferState :=
  { Inference.InferState.empty with
    capabilityOrigins :=
      [(0, .structuralFlexible), (1, .structuralFlexible)] }

def structuredExportOrigin : Inference.ConstraintOrigin :=
  ⟨.expression, [], "structured export regression"⟩

theorem structuredExportSolve_present :
    (Inference.runResolvedConstraint structuredExportStart
      structuredExportOrigin
      (.capEq (.var 0) (.con "List" [.var 1]))).isSome = true := by
  native_decide

def structuredExportSolved : Inference.InferState :=
  (Inference.runResolvedConstraint structuredExportStart
    structuredExportOrigin
    (.capEq (.var 0) (.con "List" [.var 1]))).get
      structuredExportSolve_present

/-- Model a pattern result whose result target itself exports no capability,
but whose binding-like second payload component still contains `κ₀`. -/
def structuredExportPayload : Ty :=
  Inference.capabilityExportPayload []
    [.data "PatternResult" [], .matcher (.var 0) .int]

/-- The raw root `κ₀` has disappeared; the binding-like exported payload
exposes exactly the prevailing image leaf `κ₁`. -/
theorem structuredExport_prevailing_leaves :
    Inference.capabilityExportLeaves structuredExportSolved [0]
      structuredExportPayload = [1] := by
  native_decide

def structuredExportFrozen : Inference.InferState :=
  structuredExportSolved.freezeCapabilityExport [0]
    structuredExportPayload

theorem structuredExport_freezes_image_leaf :
    structuredExportFrozen.protectedCaps = [1] ∧
      structuredExportFrozen.capabilityOrigins.originOf 1 =
        .renameOnly := by
  native_decide

/-- Once exported, the surviving leaf cannot be structurally strengthened. -/
theorem structuredExport_rejects_later_strengthening :
    (Inference.runResolvedConstraint structuredExportFrozen
      structuredExportOrigin
      (.capEq (.var 1) (.con "Tree" []))).isSome = false := by
  native_decide

end AcceptanceGapRegression
end TypePM
