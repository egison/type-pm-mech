import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.DemandTypingInferenceCompletenessValidatorCoverage
import TypePM.DemandTypingInferenceCompletenessSignatureBounds
import TypePM.DemandTypingInferenceSoundnessMutual
import TypePM.InferenceRunInvariants
import TypePM.DemandTypingInferenceCompletenessPairedChecking
import TypePM.DemandTypingInferenceCompletenessPrimitivePatternCertified
import TypePM.DemandTypingInferenceCompletenessPatternCertified
import TypePM.DemandTypingInferenceCompletenessFixMatcher

/-!
# Audit-independent validator facts of raw inference

This module collects reusable lemmas for the part of the terminal validator
which does not consume `DemandSynthTerminalAudit`.  It defines the six
audit-independent conditions, projects them through certified non-recursive
operations, and covers primitive patterns plus the variable and wildcard user
patterns.  It does not claim a whole-traversal theorem from `inferRaw` success.
-/

namespace TypePM
namespace Inference
namespace RawOrdinaryValidator

open Reconstruction
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessSignatureBounds

/-- The six validator premises which do not mention a terminal audit. -/
structure Conditions
    (signature : FrozenSig) (state : InferState) : Prop where
  primitiveHoles : TracePrimitiveHoleConditions signature state.trace
  patternLeaves : TracePatternLeafConditions signature state.trace
  instanceSuffixes : CanonicalTraceInstanceSuffixConditions state
  slotAlignments : CanonicalTraceSlotAlignmentConditions state
  typeAlignments : TraceTypeAlignmentConditions state
  dualAlignments : TraceDualAlignmentConditions state

/-- Projection from the prefix-open traversal invariant at its final cut. -/
theorem Conditions.ofOpenCoverage
    {signature : FrozenSig} {state : InferState}
    (coverage : OpenOrdinaryValidatorEventCoverage signature state)
    (producerSafe : ProtectedProducerTrace state) :
    Conditions signature state := by
  obtain ⟨traversal, types, duals⟩ :=
    coverage.atTerminal producerSafe
  let conditions := TraversalValidatorConditions.ofEventCoverage traversal
  exact ⟨conditions.primitiveHoles, conditions.patternLeaves,
    conditions.instances, conditions.slots, types, duals⟩

/-- Local solved-form and source-scope facts needed when an ordinary event is
emitted. -/
structure CutWF (signature : FrozenSig) (state : InferState) : Prop where
  signatureBelow : SignatureVarsBelow state.supply signature
  substBounded : state.prevailing.BoundedBy state.supply
  substIdempotent : state.prevailing.Idempotent

theorem CutWF.initial (signature : FrozenSig) (context : Context) :
    CutWF signature (initialState signature context) := by
  let initial := initialTraversalState signature context
  exact ⟨DemandTypingInferenceCompletenessSignatureBounds.initial
      signature context,
    initial.executable_bounded,
    initial.prevailing.executableIdempotent⟩

/-! Small projections of the already certified non-recursive operations. -/

theorem OrdinaryValidatorHistoryExtension.ofAlignTypes
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some final) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofAlignTypes
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofAlignDuals
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {left right : Dual}
    (success : alignDuals state origin left right = some final) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofAlignDuals
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofAlignDualLists
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {left right : List Dual}
    (success : alignDualLists state origin left right = some final) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofAlignDualLists
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofAlignBindings
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {left right : MonoCtx}
    (success : alignBindings state origin left right = some final) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofAlignBindings
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofAlignPatternTargets
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some final) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofAlignPatternTargets
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofExpectedAlignment
    {signature : FrozenSig} {path : SyntaxPath}
    {expressionResult : ExprResult} {expected : Ty} {final : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some final) :
    OrdinaryValidatorHistoryExtension signature expressionResult.state final :=
  (DemandTypingInferenceCompletenessPairedChecking.ValidatorRunExtension.ofAlignExprResultAtExpected
      (terminal := Subst.id)
      (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofSolvePatternCtorCapability
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {children : List Cap}
    {state final : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin children
      state = some (capability, final)) :
    OrdinaryValidatorHistoryExtension signature state final :=
  (ValidatorRunExtension.ofSolvePatternCtorCapability
    (terminal := Subst.id) (signature := signature) success).ordinary

theorem OrdinaryValidatorHistoryExtension.ofFreshTargets
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {count : Nat} {targets : List Ty}
    (success : freshTargets state origin count = (targets, final)) :
    OrdinaryValidatorHistoryExtension signature state final := by
  induction count generalizing state targets final with
  | zero =>
      simp only [freshTargets, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact .refl signature state
  | succ count ih =>
      simp only [freshTargets] at success
      let middle := (state.freshTy origin).2
      rcases restEq : freshTargets middle origin count with ⟨rest, last⟩
      have lastEq : (freshTargets middle origin count).2 = final :=
        congrArg Prod.snd success
      simp only [restEq] at lastEq
      subst final
      exact (OrdinaryValidatorHistoryExtension.freshTy signature state
        origin).trans (ih restEq)

theorem OrdinaryValidatorHistoryExtension.right_congr
    {signature : FrozenSig} {initial first second : InferState}
    (extension : OrdinaryValidatorHistoryExtension signature initial first)
    (equality : first = second) :
    OrdinaryValidatorHistoryExtension signature initial second := by
  subst second
  exact extension

theorem OrdinaryValidatorHistoryExtension.snd_of_eq
    {signature : FrozenSig} {alpha : Type} {initial final : InferState}
    {pair : alpha × InferState} {value : alpha}
    (extension : OrdinaryValidatorHistoryExtension signature initial pair.2)
    (equality : pair = (value, final)) :
    OrdinaryValidatorHistoryExtension signature initial final :=
  OrdinaryValidatorHistoryExtension.right_congr extension
    (congrArg Prod.snd equality)

theorem OrdinaryValidatorHistoryExtension.freshTy_of_eq
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {target : Ty}
    (success : state.freshTy origin = (target, final)) :
    OrdinaryValidatorHistoryExtension signature state final :=
  OrdinaryValidatorHistoryExtension.snd_of_eq
    (OrdinaryValidatorHistoryExtension.freshTy signature state origin) success

theorem OrdinaryValidatorHistoryExtension.freshCap_of_eq
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {capability : Cap}
    (success : state.freshCap origin = (capability, final)) :
    OrdinaryValidatorHistoryExtension signature state final :=
  OrdinaryValidatorHistoryExtension.snd_of_eq
    (OrdinaryValidatorHistoryExtension.freshCap signature state origin) success

/-- The three audit-only event constructors impose no condition on any of the
six ordinary validator folds. -/
inductive AuditOnlyEvent : TraceEvent → Prop where
  | patternCtor (solveCount name children capability) :
      AuditOnlyEvent (.patternCtorCompatibility solveCount name children
        capability)
  | matcher (solveCount clauses rawTarget rawHoles target holeCaps evidence
      capability) :
      AuditOnlyEvent (.matcherFinalization solveCount clauses rawTarget
        rawHoles target holeCaps evidence capability)
  | letE (solveCount name rawContext rawTarget context target scheme) :
      AuditOnlyEvent (.letGeneralization solveCount name rawContext rawTarget
        context target scheme)

theorem AuditOnlyEvent.ordinaryCondition
    {event : TraceEvent} (auditOnly : AuditOnlyEvent event)
    (signature : FrozenSig) (terminal : InferState) :
    OrdinaryValidatorEventCondition signature terminal event := by
  cases auditOnly <;>
    exact
      { traversal :=
          { primitiveHole := ⟨by trivial⟩
            patternLeaf := ⟨by trivial⟩
            canonicalInstance := ⟨by trivial⟩
            slot := ⟨by trivial⟩ }
        typeAlignment := by trivial
        dualAlignment := by trivial }

theorem OrdinaryValidatorHistoryExtension.recordAuditOnly
    {signature : FrozenSig} {state : InferState} {event : TraceEvent}
    (auditOnly : AuditOnlyEvent event) :
    OrdinaryValidatorHistoryExtension signature state
      (state.recordEvent event) :=
  OrdinaryValidatorHistoryExtension.recordEvent fun terminal _suffix _safe =>
    auditOnly.ordinaryCondition signature terminal

theorem OrdinaryValidatorHistoryExtension.finishPattern
    (signature : FrozenSig) (state : InferState) (pattern : Pattern)
    (dual : Dual) (bindings : MonoCtx) (path : SyntaxPath) :
    OrdinaryValidatorHistoryExtension signature state
      (state.recordEvent (.inferredPattern pattern dual bindings path)) :=
  OrdinaryValidatorHistoryExtension.recordNeutral
    (ValidatorNeutralEvent.inferredPattern pattern dual bindings path)

theorem OrdinaryValidatorHistoryExtension.recordPatternValueFresh
    {signature : FrozenSig} {state : InferState}
    {origin : ConstraintOrigin}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {target : Ty}
    (signatureBelow : SignatureVarsBelow state.supply signature)
    (contextBounded : context.BoundedBy state.supply)
    (parametersBounded : parameters.BoundedBy state.supply)
    (bindingsBounded : bindings.BoundedBy state.supply)
    (targetBounded : target.BoundedBy state.supply) :
    OrdinaryValidatorHistoryExtension signature
      (state.freshCap origin).2
      ((state.freshCap origin).2.recordEvent
        (.patternValueFresh context parameters bindings
          ⟨state.supply.nextCap⟩ target)) := by
  apply OrdinaryValidatorHistoryExtension.recordEvent
  intro terminal _suffix _safe
  exact patternValue_ordinaryValidatorEventCondition
    signatureBelow.caps
    (DemandTypingInferenceCompletenessPatternCertified.contextBounded_capVarsBelow
      contextBounded)
    (DemandTypingInferenceCompletenessPatternCertified.patternCtxBounded_capVarsBelow
      parametersBounded)
    (DemandTypingInferenceCompletenessPatternCertified.monoCtxBounded_capVarsBelow
      bindingsBounded)
    targetBounded

theorem OrdinaryValidatorHistoryExtension.ofInstantiateScheme
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state : InferState} {scheme : Scheme}
    (before : CutWF signature state)
    (lookup : (rawContext.applySubst state.prevailing).find? name =
      some scheme) :
    OrdinaryValidatorHistoryExtension signature state
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 :=
  OrdinaryValidatorHistoryExtension.instantiateSchemeInState
    (DemandTypingInferenceCompletenessValidationMain.instantiateScheme_terminalLookup
      before.substIdempotent lookup)

theorem OrdinaryValidatorHistoryExtension.ofBuildFixPlaceholder
    {signature : FrozenSig} {path : SyntaxPath} {body : Expr}
    {state final : InferState} {domain codomain : Ty}
    (success : buildFixPlaceholder signature path body state =
      some (domain, codomain, final)) :
    OrdinaryValidatorHistoryExtension signature state final := by
  cases body <;> simp_all [buildFixPlaceholder]
  case matcher clauses =>
    exact (DemandTypingInferenceCompletenessFixMatcher.ValidatorRunExtension.ofBuildFixPlaceholderMatcher
      (terminal := Subst.id) success).ordinary
  all_goals
    rcases success with ⟨_, _, rfl⟩
    exact (OrdinaryValidatorHistoryExtension.freshTy signature state _).trans
      (OrdinaryValidatorHistoryExtension.freshTy signature _ _)

/-- Project the ordinary half of the existing certified primitive-pattern
traversal theorem. -/
theorem inferPPatFuel_ordinaryHistoryExtension
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : PPat} {target : Ty} {state : InferState}
    {result : PPatResult}
    (closed : signature.SchemesClosed)
    (before : CutWF signature state)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferPPatFuel fuel signature path pattern target state =
      some result) :
    OrdinaryValidatorHistoryExtension signature state result.state :=
  (DemandTypingInferenceCompletenessPrimitivePatternCertified.inferPPatFuel_validation
      (terminal := Subst.id) closed
      before.signatureBelow targetBounded success).ordinary

theorem inferDPatFuel_ordinaryHistoryExtension
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : DPat} {target : Ty} {state : InferState}
    {result : DPatResult}
    (closed : signature.SchemesClosed)
    (before : CutWF signature state)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferDPatFuel fuel signature path pattern target state =
      some result) :
    OrdinaryValidatorHistoryExtension signature state result.state :=
  (DemandTypingInferenceCompletenessPrimitivePatternCertified.inferDPatFuel_validation
      (terminal := Subst.id) closed
      before.signatureBelow targetBounded success).ordinary

theorem inferPatternFuel_var_ordinaryHistoryExtension
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {state : InferState}
    {result : PatternResult}
    (before : CutWF signature state)
    (contextBounded : context.BoundedBy state.supply)
    (parametersBounded : parameters.BoundedBy state.supply)
    (bindingsBounded : bindings.BoundedBy state.supply)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pvar name) state = some result) :
    OrdinaryValidatorHistoryExtension signature state result.state := by
  simp only [inferPatternFuel] at success
  split at success
  · contradiction
  · simp only [Option.some.injEq] at success
    subst result
    exact (DemandTypingInferenceCompletenessPatternCertified.variableLeaf
      (terminal := Subst.id) before.signatureBelow contextBounded
      parametersBounded bindingsBounded).ordinary

theorem inferPatternFuel_wild_ordinaryHistoryExtension
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {state : InferState} {result : PatternResult}
    (before : CutWF signature state)
    (contextBounded : context.BoundedBy state.supply)
    (parametersBounded : parameters.BoundedBy state.supply)
    (bindingsBounded : bindings.BoundedBy state.supply)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path .wild state = some result) :
    OrdinaryValidatorHistoryExtension signature state result.state := by
  simp only [inferPatternFuel, Option.some.injEq] at success
  subst result
  exact (DemandTypingInferenceCompletenessPatternCertified.wildcardLeaf
    (terminal := Subst.id) before.signatureBelow contextBounded
    parametersBounded bindingsBounded).ordinary

end RawOrdinaryValidator
end Inference
end TypePM
