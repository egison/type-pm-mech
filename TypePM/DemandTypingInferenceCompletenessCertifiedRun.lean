import TypePM.DemandTypingInferenceCompletenessValidatorCoverage
import TypePM.DemandTypingInferenceCompletenessMatcherExprTraversal

/-!
# Validator-certified raw traversal completions

This module is the integration boundary between the raw completeness packages
and terminal-validator completeness.  Existing reconstruction modules keep
returning their focused `*RunCompletion` objects.  The audited global
recursion wraps those objects with one chronological validator extension:
ordinary executable events and terminal-audit-sensitive events compose in
lockstep, without adding validator fields to every raw package.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessCertifiedRun

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessMatcherExprTraversal
open DemandTypingInferenceCompletenessProtectedTrace

/-- The two independent validator extensions produced by one chronological
raw traversal. -/
structure ValidatorRunExtension
    (terminal : Subst) (signature : FrozenSig)
    (initial final : InferState) : Prop where
  ordinary : OrdinaryValidatorHistoryExtension signature initial final
  sensitive : TerminalAuditHistoryExtension terminal signature initial final

theorem ValidatorRunExtension.refl
    (terminal : Subst) (signature : FrozenSig) (state : InferState) :
    ValidatorRunExtension terminal signature state state :=
  ⟨OrdinaryValidatorHistoryExtension.refl signature state,
    TerminalAuditHistoryExtension.refl terminal signature state⟩

/-- Validator extensions compose in the same chronological order as raw
completion packages. -/
theorem ValidatorRunExtension.trans
    {terminal : Subst} {signature : FrozenSig}
    {first middle last : InferState}
    (front : ValidatorRunExtension terminal signature first middle)
    (back : ValidatorRunExtension terminal signature middle last) :
    ValidatorRunExtension terminal signature first last :=
  ⟨front.ordinary.trans back.ordinary,
    front.sensitive.trans back.sensitive⟩

/-- Lift a validator-ordinary traversal when all of its newly added events
avoid the three terminal-audit forms. -/
theorem ValidatorRunExtension.ofOrdinary
    {terminal : Subst} {signature : FrozenSig}
    {initial final : InferState}
    (ordinary : OrdinaryValidatorHistoryExtension signature initial final)
    (notSensitive : ∀ event,
      event ∈ final.trace.events → event ∉ initial.trace.events →
        ¬ TerminalAuditSensitiveEvent event) :
    ValidatorRunExtension terminal signature initial final :=
  ⟨ordinary, ordinary.auditExtension notSensitive⟩

/-- Append one ordinary event after a certified prefix. -/
theorem ValidatorRunExtension.recordOrdinaryEvent
    {terminal : Subst} {signature : FrozenSig}
    {state : InferState} {event : TraceEvent}
    (latest : ∀ future,
      (state.recordEvent event).StateExtension future →
      ProtectedProducerTrace future →
      OrdinaryValidatorEventCondition signature future event)
    (notSensitive : ¬ TerminalAuditSensitiveEvent event) :
    ValidatorRunExtension terminal signature state
      (state.recordEvent event) := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.recordEvent latest)
  intro candidate membership previous
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst candidate
    exact notSensitive

/-- Append a whitelisted neutral event. -/
theorem ValidatorRunExtension.recordNeutral
    {terminal : Subst} {signature : FrozenSig}
    {state : InferState} {event : TraceEvent}
    (neutral : ValidatorNeutralEvent event) :
    ValidatorRunExtension terminal signature state
      (state.recordEvent event) := by
  apply ValidatorRunExtension.recordOrdinaryEvent
  · intro future extension safe
    exact neutral.ordinaryCondition signature future
  · cases neutral <;> simp [TerminalAuditSensitiveEvent]

/-- Append one audit-sensitive event.  Such events are nevertheless trivial
for all ordinary validator folds; their semantic content lives solely in the
provided terminal-audit witness. -/
theorem ValidatorRunExtension.recordSensitive
    {terminal : Subst} {signature : FrozenSig}
    {state : InferState} {event : TraceEvent}
    (witness : TerminalAuditEventWitness terminal signature
      (state.recordEvent event) event) :
    ValidatorRunExtension terminal signature state
      (state.recordEvent event) := by
  refine ⟨?_, TerminalAuditHistoryExtension.recordSensitive witness⟩
  apply OrdinaryValidatorHistoryExtension.recordEvent
  intro future extension producerSafe
  refine
    { traversal := ?_
      typeAlignment := by cases event <;> trivial
      dualAlignment := by cases event <;> trivial }
  exact
    { primitiveHole := ⟨by cases event <;> trivial⟩
      patternLeaf := ⟨by cases event <;> trivial⟩
      canonicalInstance := ⟨by cases event <;> trivial⟩
      slot := ⟨by cases event <;> trivial⟩ }

/-- Add one ordinary suffix after an already certified prefix. -/
theorem ValidatorRunExtension.finishOrdinary
    {terminal : Subst} {signature : FrozenSig}
    {first middle last : InferState}
    (front : ValidatorRunExtension terminal signature first middle)
    (suffix : OrdinaryValidatorHistoryExtension signature middle last)
    (notSensitive : ∀ event,
      event ∈ last.trace.events → event ∉ middle.trace.events →
        ¬ TerminalAuditSensitiveEvent event) :
    ValidatorRunExtension terminal signature first last :=
  front.trans (ValidatorRunExtension.ofOrdinary suffix notSensitive)

/-! ## Local state emitters -/

theorem ValidatorRunExtension.visit
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (kind : NodeKind) (path : SyntaxPath) :
    ValidatorRunExtension terminal signature state
      (Inference.visit state kind path) := by
  simpa [Inference.visit] using
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature) (state := state)
      (ValidatorNeutralEvent.visit kind path))

theorem ValidatorRunExtension.finishExpr
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (expression : Expr) (path : SyntaxPath) (target : Ty) :
    ValidatorRunExtension terminal signature state
      (Inference.finishExpr expression path target state).state := by
  simpa [Inference.finishExpr] using
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature) (state := state)
      (ValidatorNeutralEvent.inferredExpr expression target path))

theorem ValidatorRunExtension.recordSource
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (source : ProducerSource) :
    ValidatorRunExtension terminal signature state
      (state.recordSource source) := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.recordSource signature state source)
  intro event membership previous
  exact False.elim (previous (by simpa [InferState.recordSource] using membership))

theorem ValidatorRunExtension.recordSelfReference
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (binder : String) (placeholder : Ty) (path : SyntaxPath) :
    ValidatorRunExtension terminal signature state
      (Inference.recordSelfReference state binder placeholder path) := by
  unfold Inference.recordSelfReference
  exact (ValidatorRunExtension.recordNeutral
    (terminal := terminal) (signature := signature) (state := state)
    (ValidatorNeutralEvent.directSelfReference binder placeholder path)).trans
      (ValidatorRunExtension.recordSource terminal signature _ _)

theorem ValidatorRunExtension.freshTy
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (origin : ConstraintOrigin) :
    ValidatorRunExtension terminal signature state (state.freshTy origin).2 := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.freshTy signature state origin)
  intro event membership previous
  simp only [InferState.freshTy, InferenceBase.freshTyMeta,
    InferState.recordEvent, List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.freshCap
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (origin : ConstraintOrigin) :
    ValidatorRunExtension terminal signature state (state.freshCap origin).2 := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.freshCap signature state origin)
  intro event membership previous
  simp only [InferState.freshCap, InferenceBase.freshCapMeta,
    InferState.recordEvent, List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.protectMatcherCapability
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (capability : Cap) :
    ValidatorRunExtension terminal signature state
      (state.protectMatcherCapability capability) := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.protectMatcherCapability signature state
      capability)
  intro event membership previous
  exact False.elim (previous (by simpa using membership))

theorem ValidatorRunExtension.freezeCapabilityExport
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (images : List CapVar) (payload : Ty) :
    ValidatorRunExtension terminal signature state
      (state.freezeCapabilityExport images payload) := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.freezeCapabilityExport signature state
      images payload)
  intro event membership previous
  simp only [InferState.freezeCapabilityExport, InferState.recordEvent,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.instantiateCtorInState
    {terminal : Subst} {signature : FrozenSig}
    (state : InferState) (scheme : CtorScheme) (closed : scheme.Closed) :
    ValidatorRunExtension terminal signature state
      (Inference.instantiateCtorInState state scheme).2 := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.instantiateCtorInState state scheme
      closed)
  intro event membership previous
  simp only [Inference.instantiateCtorInState, InferState.recordEvent,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.instantiateSchemeInState
    {terminal : Subst} {signature : FrozenSig}
    {rawContext normalizedContext : Context} {name : String}
    {state : InferState} {scheme : Scheme}
    (terminalLookup : ∀ future,
      (Inference.instantiateSchemeInState signature rawContext
        normalizedContext name state scheme).2.StateExtension future →
      (rawContext.applySubst future.prevailing).find? name =
        some (scheme.applyMeta future.prevailing)) :
    ValidatorRunExtension terminal signature state
      (Inference.instantiateSchemeInState signature rawContext
        normalizedContext name state scheme).2 := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.instantiateSchemeInState terminalLookup)
  intro event membership previous
  simp only [Inference.instantiateSchemeInState, InferState.recordEvent,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.instantiateDualInState
    {terminal : Subst} {signature : FrozenSig}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawBindings : MonoCtx} {context : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {state : InferState} {scheme : DualScheme}
    (closed : scheme.Closed) :
    ValidatorRunExtension terminal signature state
      (Inference.instantiateDualInState signature rawContext rawParameters
        rawBindings context parameters bindings state scheme).2 := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.instantiateDualInState closed)
  intro event membership previous
  simp only [Inference.instantiateDualInState, InferState.recordEvent,
    List.mem_append, List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst event
    simp [TerminalAuditSensitiveEvent]

/-! ## Alignment finishers -/

theorem ValidatorRunExtension.finishAlignTypes
    {terminal : Subst} {signature : FrozenSig}
    {state aligned : InferState} {origin : ConstraintOrigin}
    {left right : Ty}
    (core : ValidatorRunExtension terminal signature state aligned)
    (success : alignTypes state origin left right = some
      (aligned.recordEvent (.typeAlignment state.trace.solves.length
        aligned.trace.solves.length left right (state.prevailing.apply left)
        (state.prevailing.apply right)))) :
    ValidatorRunExtension terminal signature state
      (aligned.recordEvent (.typeAlignment state.trace.solves.length
        aligned.trace.solves.length left right (state.prevailing.apply left)
        (state.prevailing.apply right))) := by
  let event := TraceEvent.typeAlignment state.trace.solves.length
    aligned.trace.solves.length left right (state.prevailing.apply left)
    (state.prevailing.apply right)
  apply core.finishOrdinary
    (OrdinaryValidatorHistoryExtension.recordEvent (event := event) (by
      intro future extension producerSafe
      have condition := alignTypes_ordinaryValidatorEventCondition
        (signature := signature) success extension.history
      simpa [event, InferState.recordEvent] using condition))
  intro candidate membership previous
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst candidate
    simp [event, TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.finishAlignDuals
    {terminal : Subst} {signature : FrozenSig}
    {state aligned : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (core : ValidatorRunExtension terminal signature state aligned)
    (success : alignDuals state origin left right = some
      (aligned.recordEvent (.dualAlignment state.trace.solves.length
        aligned.trace.solves.length left right
        (left.applySubst state.prevailing)
        (right.applySubst state.prevailing)))) :
    ValidatorRunExtension terminal signature state
      (aligned.recordEvent (.dualAlignment state.trace.solves.length
        aligned.trace.solves.length left right
        (left.applySubst state.prevailing)
        (right.applySubst state.prevailing))) := by
  let event := TraceEvent.dualAlignment state.trace.solves.length
    aligned.trace.solves.length left right (left.applySubst state.prevailing)
    (right.applySubst state.prevailing)
  apply core.finishOrdinary
    (OrdinaryValidatorHistoryExtension.recordEvent (event := event) (by
      intro future extension producerSafe
      have condition := alignDuals_ordinaryValidatorEventCondition
        (signature := signature) success extension.history
      simpa [event, InferState.recordEvent] using condition))
  intro candidate membership previous
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst candidate
    simp [event, TerminalAuditSensitiveEvent]

theorem ValidatorRunExtension.finishExpectedAlignment
    {terminal : Subst} {signature : FrozenSig} {path : SyntaxPath}
    {expressionResult : ExprResult} {expected : Ty} {aligned : InferState}
    (core : ValidatorRunExtension terminal signature expressionResult.state
      aligned)
    (success : alignExprResultAtExpected path expressionResult expected = some
      (aligned.recordEvent (.slotAlignment
        expressionResult.state.trace.solves.length aligned.trace.solves.length
        (match expectedCoercionPlan expressionResult.state
            expressionResult.target expected with
          | .productMatcherLift duals => productMatcherTarget duals
          | .slotTupleLift duals => slotTupleTarget duals
          | .raw => expressionResult.state.prevailing.apply
              expressionResult.target)
        (expressionResult.state.prevailing.apply expected)))) :
    ValidatorRunExtension terminal signature expressionResult.state
      (aligned.recordEvent (.slotAlignment
        expressionResult.state.trace.solves.length aligned.trace.solves.length
        (match expectedCoercionPlan expressionResult.state
            expressionResult.target expected with
          | .productMatcherLift duals => productMatcherTarget duals
          | .slotTupleLift duals => slotTupleTarget duals
          | .raw => expressionResult.state.prevailing.apply
              expressionResult.target)
        (expressionResult.state.prevailing.apply expected))) := by
  let inferred := match expectedCoercionPlan expressionResult.state
      expressionResult.target expected with
    | .productMatcherLift duals => productMatcherTarget duals
    | .slotTupleLift duals => slotTupleTarget duals
    | .raw => expressionResult.state.prevailing.apply expressionResult.target
  let requested := expressionResult.state.prevailing.apply expected
  let event := TraceEvent.slotAlignment
    expressionResult.state.trace.solves.length aligned.trace.solves.length
    inferred requested
  apply core.finishOrdinary
    (OrdinaryValidatorHistoryExtension.recordEvent (event := event) (by
      intro future extension producerSafe
      have condition :=
        alignExprResultAtExpected_ordinaryValidatorEventCondition
          (signature := signature) success extension.history
      change OrdinaryValidatorEventCondition signature future
        (.slotAlignment expressionResult.state.trace.solves.length
          aligned.trace.solves.length
          (match expectedCoercionPlan expressionResult.state
              expressionResult.target expected with
            | .productMatcherLift duals => productMatcherTarget duals
            | .slotTupleLift duals => slotTupleTarget duals
            | .raw => expressionResult.state.prevailing.apply
                expressionResult.target)
          (expressionResult.state.prevailing.apply expected))
      exact condition))
  intro candidate membership previous
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst candidate
    simp [event, TerminalAuditSensitiveEvent]

/-! ## Terminal-audit-sensitive emitters -/

theorem ValidatorRunExtension.recordPatternCtor
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {name : String} {entry : PatternCtorScheme signature.observability}
    {duals : List Dual} {capability : Cap}
    (lookup : signature.findPatternCtor name = some entry)
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
    ValidatorRunExtension terminal signature state
      (state.recordEvent (.patternCtorCompatibility state.trace.solves.length
        name (duals.map Dual.cap) capability)) := by
  apply ValidatorRunExtension.recordSensitive
  exact .patternCtor (Nat.le_refl _) lookup facts

theorem ValidatorRunExtension.recordLetGeneralization
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {name : String} {rawContext : Context} {rawTarget : Ty}
    (facts : DDTerminalAudit.LetFacts terminal signature rawContext rawTarget
      state.prevailing) :
    ValidatorRunExtension terminal signature state
      (state.recordEvent (.letGeneralization state.trace.solves.length name
        rawContext rawTarget (rawContext.applySubst state.prevailing)
        (state.prevailing.apply rawTarget)
        (signature.generalize (rawContext.applySubst state.prevailing)
          (state.prevailing.apply rawTarget)))) := by
  apply ValidatorRunExtension.recordSensitive
  exact .letE (Nat.le_refl _)
    (by simp only [InferState.recordEvent, List.take_length,
      InferState.prevailing])
    (by simp only [InferState.recordEvent, List.take_length,
      InferState.prevailing]) rfl
    (by simpa only [InferState.recordEvent, List.take_length,
      InferState.prevailing] using facts)

theorem ValidatorRunExtension.recordLiteralMatcherFinalization
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {evidence : List Shape.Evidence}
    {capability : Cap}
    (catchAll : catchAllLastCheck clauses = true)
    (binders : matcherBindersCheck clauses = true)
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      rawHoleLists capability rawTarget) :
    let covered := state.recordEvent (.literalCoverage clauses capability)
    let finalized := covered.recordEvent (.matcherFinalization
      covered.trace.solves.length clauses rawTarget rawHoleLists
      (covered.prevailing.apply rawTarget)
      (resolvedHoleCaps covered.prevailing rawHoleLists) evidence capability)
    ValidatorRunExtension terminal signature state
      (finalized.protectMatcherCapability capability) := by
  let coverageEvent := TraceEvent.literalCoverage clauses capability
  let covered := state.recordEvent coverageEvent
  let finalizationEvent := TraceEvent.matcherFinalization
    covered.trace.solves.length clauses rawTarget rawHoleLists
    (covered.prevailing.apply rawTarget)
    (resolvedHoleCaps covered.prevailing rawHoleLists) evidence capability
  let finalized := covered.recordEvent finalizationEvent
  have coverageRun : ValidatorRunExtension terminal signature state covered :=
    ValidatorRunExtension.recordNeutral
      (ValidatorNeutralEvent.literalCoverage clauses capability)
  have finalizationRun : ValidatorRunExtension terminal signature covered
      finalized := by
    apply ValidatorRunExtension.recordSensitive
    exact .matcher (Nat.le_refl _)
      (by simp only [InferState.recordEvent, List.take_length,
        InferState.prevailing])
      (by simp only [InferState.recordEvent, List.take_length,
        InferState.prevailing]) catchAll binders facts
  exact (coverageRun.trans finalizationRun).trans
    (ValidatorRunExtension.protectMatcherCapability terminal signature
      finalized capability)

/-- Apply an incremental run to already accumulated root-prefix coverage. -/
theorem ValidatorRunExtension.applyCoverage
    {terminal : Subst} {signature : FrozenSig}
    {initial final : InferState}
    (extension : ValidatorRunExtension terminal signature initial final)
    (ordinary : OpenOrdinaryValidatorEventCoverage signature initial)
    (sensitive : TerminalAuditEventCoverage terminal signature initial) :
    RootValidatorEventCoverage terminal signature final :=
  ⟨extension.ordinary.applyCoverage ordinary,
    extension.sensitive.applyCoverage sensitive⟩

/-- Root initialization: both event folds are vacuous on the canonical empty
state, so a completed validator extension directly yields root coverage. -/
theorem ValidatorRunExtension.applyEmpty
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply} {final : InferState}
    (extension : ValidatorRunExtension terminal signature
      (InferState.empty supply) final) :
    RootValidatorEventCoverage terminal signature final :=
  extension.applyCoverage
    (OpenOrdinaryValidatorEventCoverage.empty signature supply)
    (TerminalAuditEventCoverage.empty terminal signature supply)

/-! ## Raw state and expression wrappers -/

structure CertifiedStateRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  run : StateRunCompletion before operation q' declarative ledger
  validation : ValidatorRunExtension terminal signature initial run.result

structure CertifiedSynthRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  run : SynthRunCompletion before operation q' declarative ledger target
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-- Chronological state-only certified runs compose without reopening either
raw completion proof. -/
def CertifiedStateRunCompletion.seq
    {terminal : Subst} {signature : FrozenSig}
    {q q' q'' : InferenceBase.FreshSupply} {S S' S'' : Subst}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {firstOperation : Option InferState}
    (first : CertifiedStateRunCompletion terminal signature before
      firstOperation q' S' ledger₁)
    {secondOperation : InferState → Option InferState}
    (second : CertifiedStateRunCompletion terminal signature
      first.run.completion (secondOperation first.run.result)
      q'' S'' ledger₂) :
    CertifiedStateRunCompletion terminal signature before
      (do
        let middle ← firstOperation
        secondOperation middle)
      q'' S'' ledger₂ :=
  ⟨StateRunCompletion.seq first.run second.run,
    first.validation.trans second.validation⟩

/-! ## User-pattern wrappers -/

structure CertifiedPatternRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  run : PatternRunCompletion before operation q' declarative ledger dual
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedPatternsRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  run : PatternsRunCompletion before operation q' declarative ledger duals
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedPPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  run : PPatRunCompletion before operation q' declarative ledger target holes
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedDPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  run : DPatRunCompletion before operation q' declarative ledger target
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-! ## Matcher-clause wrappers -/

structure CertifiedClauseRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClauseResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) : Type where
  run : ClauseRunCompletion before operation q' declarative ledger target holes
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedClausesRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClausesResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holeLists : List (List Dual)) : Type where
  run : ClausesRunCompletion before operation q' declarative ledger target
    holeLists
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-- A matcher literal returns the ordinary expression synthesis package; this
name documents its role at the audited matcher dispatcher boundary. -/
abbrev CertifiedMatcherRunCompletion := CertifiedSynthRunCompletion

/-! ## Root projection -/

/-- A certified root synthesis run beginning at an empty state supplies all
four event-coverage premises.  Current protected safety retained by the raw
completion discharges the only terminal premise of ordinary coverage. -/
theorem CertifiedSynthRunCompletion.rootConditions
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger₀ ledger' : CapabilityOriginLedger}
    {before : TraversalStateCorrespondence supply Subst.id ledger₀
      (InferState.empty supply)}
    {operation : Option ExprResult} {target : Ty}
    (certified : CertifiedSynthRunCompletion terminal signature before
      operation q' S' ledger' target) :
    TraversalValidatorEventCoverage signature certified.run.result.state ∧
      TerminalAuditEventCoverage terminal signature
        certified.run.result.state ∧
      TraceTypeAlignmentConditions certified.run.result.state ∧
      TraceDualAlignmentConditions certified.run.result.state := by
  let coverage := certified.validation.applyEmpty
  exact coverage.atTerminal
    ((currentProtectedProducerSafe_iff certified.run.result.state).mp
      certified.run.protected_safe)

end DemandTypingInferenceCompletenessCertifiedRun
end TypePM
