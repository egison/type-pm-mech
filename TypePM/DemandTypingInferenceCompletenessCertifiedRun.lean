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

/-- A resolved solver step changes the solve history but emits no
reconstruction event, so it transports both validator extensions unchanged. -/
theorem ValidatorRunExtension.ofRunResolvedConstraint
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {constraint : Constraint}
    (success : Inference.runResolvedConstraint state origin constraint =
      some result) :
    ValidatorRunExtension terminal signature state result := by
  have extension := runResolvedConstraint_stateExtension success
  have eventsEq : result.trace.events = state.trace.events := by
    unfold Inference.runResolvedConstraint at success
    cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
        state.trace.solves.length origin constraint with
    | none => simp [stepEquation] at success
    | some step =>
        simp only [stepEquation] at success
        cases constraint with
        | capEq _ _ | targetEq _ _ =>
            simpa [InferState.recordSolve] using (congrArg
              (fun current : InferState => current.trace.events)
              (Option.some.inj success)).symm
        | producerToSlot _ _ _ _ =>
            change (if capSubstSafeVarsCheck state.capabilityOrigins
                step.delta.cap state.protectedCaps
              then some (state.recordSolve step) else none) =
                some result at success
            split at success <;> try contradiction
            simpa [InferState.recordSolve] using (congrArg
              (fun current : InferState => current.trace.events)
              (Option.some.inj success)).symm
  apply ValidatorRunExtension.ofOrdinary
    (Inference.Reconstruction.OrdinaryValidatorHistoryExtension.ofNoEvents
      extension eventsEq)
  intro event membership previous
  exfalso
  exact previous (by simpa [eventsEq] using membership)

/-- The private core of type alignment consists only of one or two resolved
solver steps; it emits no public alignment event of its own. -/
theorem ValidatorRunExtension.ofAlignTypesCore
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypesCore state origin left right = some result) :
    ValidatorRunExtension terminal signature state result := by
  unfold alignTypesCore at success
  simp only at success
  split at success
  all_goals try
    rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, rest⟩
  all_goals try
    have first := ValidatorRunExtension.ofRunResolvedConstraint
      (terminal := terminal) (signature := signature) firstSuccess
  all_goals try
    split at rest
  all_goals try
    exact first.trans (ValidatorRunExtension.ofRunResolvedConstraint
      (terminal := terminal) (signature := signature) rest)
  all_goals try contradiction
  all_goals exact (ValidatorRunExtension.ofRunResolvedConstraint
    (terminal := terminal) (signature := signature) success)

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

theorem ValidatorRunExtension.protectMatcherCapabilityExcept
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (capability : Cap) (borrowed : List CapVar) :
    ValidatorRunExtension terminal signature state
      (state.protectMatcherCapabilityExcept capability borrowed) := by
  apply ValidatorRunExtension.ofOrdinary
    (OrdinaryValidatorHistoryExtension.protectMatcherCapabilityExcept
      signature state capability borrowed)
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

/-- Certify the solver core and then append the public type-alignment event. -/
theorem ValidatorRunExtension.ofAlignTypes
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some result) :
    ValidatorRunExtension terminal signature state result := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, coreSuccess, finished⟩
  have resultEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length left right
      (state.prevailing.apply left) (state.prevailing.apply right)) = result :=
    Option.some.inj finished
  subst result
  exact ValidatorRunExtension.finishAlignTypes
    (ValidatorRunExtension.ofAlignTypesCore
      (terminal := terminal) (signature := signature) coreSuccess) success

/-- Certify capability equality, target alignment, and the public dual event
in their executable chronological order. -/
theorem ValidatorRunExtension.ofAlignDuals
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some result) :
    ValidatorRunExtension terminal signature state result := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with
    ⟨aligned, targetSuccess, finished⟩
  have resultEq : aligned.recordEvent (.dualAlignment
      state.trace.solves.length aligned.trace.solves.length left right
      (left.applySubst state.prevailing)
      (right.applySubst state.prevailing)) = result := Option.some.inj finished
  subst result
  exact ValidatorRunExtension.finishAlignDuals
    ((ValidatorRunExtension.ofRunResolvedConstraint
      (terminal := terminal) (signature := signature) capSuccess).trans
      (ValidatorRunExtension.ofAlignTypes
        (terminal := terminal) (signature := signature) targetSuccess)) success

/-- Pointwise dual-list alignment is the chronological composition of its
certified head alignments. -/
theorem ValidatorRunExtension.ofAlignDualLists
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {lefts rights : List Dual}
    (success : alignDualLists state origin lefts rights = some result) :
    ValidatorRunExtension terminal signature state result := by
  induction lefts generalizing state result rights with
  | nil =>
      cases rights with
      | nil =>
          simp only [alignDualLists, Option.some.injEq] at success
          subst result
          exact ValidatorRunExtension.refl terminal signature state
      | cons _ _ => simp [alignDualLists] at success
  | cons left lefts induction =>
      cases rights with
      | nil => simp [alignDualLists] at success
      | cons right rights =>
          simp only [alignDualLists] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, headSuccess, tailSuccess⟩
          exact (ValidatorRunExtension.ofAlignDuals
            (terminal := terminal) (signature := signature) headSuccess).trans
              (induction tailSuccess)

/-- Binding-context alignment differs only by its positional name guard; each
successful payload step is an ordinary certified type alignment. -/
theorem ValidatorRunExtension.ofAlignBindings
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {lefts rights : MonoCtx}
    (success : alignBindings state origin lefts rights = some result) :
    ValidatorRunExtension terminal signature state result := by
  induction lefts generalizing state result rights with
  | nil =>
      cases rights with
      | nil =>
          simp only [alignBindings, Option.some.injEq] at success
          subst result
          exact ValidatorRunExtension.refl terminal signature state
      | cons _ _ => simp [alignBindings] at success
  | cons left lefts induction =>
      cases rights with
      | nil => simp [alignBindings] at success
      | cons right rights =>
          simp only [alignBindings] at success
          split at success
          · rcases Option.bind_eq_some_iff.mp success with
              ⟨middle, headSuccess, tailSuccess⟩
            exact (ValidatorRunExtension.ofAlignTypes
              (terminal := terminal) (signature := signature)
              headSuccess).trans (induction tailSuccess)
          · contradiction

/-- Constructor target alignment is pointwise type alignment with no extra
event beyond the events emitted by each element. -/
theorem ValidatorRunExtension.ofAlignPatternTargets
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some result) :
    ValidatorRunExtension terminal signature state result := by
  induction duals generalizing state result targets with
  | nil =>
      cases targets with
      | nil =>
          simp only [alignPatternTargets, Option.some.injEq] at success
          subst result
          exact ValidatorRunExtension.refl terminal signature state
      | cons _ _ => simp [alignPatternTargets] at success
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, headSuccess, tailSuccess⟩
          exact (ValidatorRunExtension.ofAlignTypes
            (terminal := terminal) (signature := signature) headSuccess).trans
              (induction tailSuccess)

/-! ## Pattern-constructor capability solving -/

mutual

/-- Freshening one structural skeleton emits only the fresh-capability events
at its observable unknown leaves. -/
theorem ValidatorRunExtension.ofFreshenSkeleton
    {terminal : Subst} {signature : FrozenSig}
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidence : Shape.Evidence} {state result : InferState} {capability : Cap}
    (success : freshenSkeleton observable origin evidence state =
      some (capability, result)) :
    ValidatorRunExtension terminal signature state result := by
  cases evidence with
  | unseen =>
      simp only [freshenSkeleton, Option.some.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ValidatorRunExtension.freshCap terminal signature state origin
  | known leaf =>
      simp only [freshenSkeleton, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ValidatorRunExtension.refl terminal signature state
  | con name children =>
      simp only [freshenSkeleton] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨mask, maskSuccess, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with
        ⟨pair, childrenSuccess, finished⟩
      rcases pair with ⟨capabilities, middle⟩
      have resultEq : middle = result := by
        exact (Prod.mk.inj (Option.some.inj finished)).2
      subst result
      exact ValidatorRunExtension.ofFreshenSkeletonMasked childrenSuccess
  | prod components =>
      simp only [freshenSkeleton] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨pair, componentsSuccess, finished⟩
      rcases pair with ⟨capabilities, middle⟩
      have resultEq : middle = result := by
        exact (Prod.mk.inj (Option.some.inj finished)).2
      subst result
      exact ValidatorRunExtension.ofFreshenSkeletonList componentsSuccess

/-- Product skeleton freshening composes its component histories. -/
theorem ValidatorRunExtension.ofFreshenSkeletonList
    {terminal : Subst} {signature : FrozenSig}
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidences : List Shape.Evidence} {state result : InferState}
    {capabilities : List Cap}
    (success : freshenSkeletonList observable origin evidences state =
      some (capabilities, result)) :
    ValidatorRunExtension terminal signature state result := by
  cases evidences with
  | nil =>
      simp only [freshenSkeletonList, Option.some.injEq, Prod.mk.injEq]
        at success
      rcases success with ⟨_, rfl⟩
      exact ValidatorRunExtension.refl terminal signature state
  | cons evidence rest =>
      simp only [freshenSkeletonList] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPair, headSuccess, remaining⟩
      rcases headPair with ⟨head, middle⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨tailPair, tailSuccess, finished⟩
      rcases tailPair with ⟨tail, last⟩
      have resultEq : last = result := by
        exact (Prod.mk.inj (Option.some.inj finished)).2
      subst result
      exact (ValidatorRunExtension.ofFreshenSkeleton headSuccess).trans
        (ValidatorRunExtension.ofFreshenSkeletonList tailSuccess)

/-- Masked constructor skeleton freshening skips unobservable fields and
recurses through observable ones. -/
theorem ValidatorRunExtension.ofFreshenSkeletonMasked
    {terminal : Subst} {signature : FrozenSig}
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {mask : List Bool} {evidences : List Shape.Evidence}
    {state result : InferState} {capabilities : List Cap}
    (success : freshenSkeletonMasked observable origin mask evidences state =
      some (capabilities, result)) :
    ValidatorRunExtension terminal signature state result := by
  cases mask with
  | nil =>
      cases evidences with
      | nil =>
          simp only [freshenSkeletonMasked, Option.some.injEq, Prod.mk.injEq]
            at success
          rcases success with ⟨_, rfl⟩
          exact ValidatorRunExtension.refl terminal signature state
      | cons _ _ => simp [freshenSkeletonMasked] at success
  | cons observableHead mask =>
      cases evidences with
      | nil => simp [freshenSkeletonMasked] at success
      | cons evidence rest =>
          cases observableHead with
          | false =>
              simp [freshenSkeletonMasked] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, last⟩
              have resultEq : last = result := by
                exact (Prod.mk.inj (Option.some.inj finished)).2
              subst result
              exact ValidatorRunExtension.ofFreshenSkeletonMasked tailSuccess
          | true =>
              simp only [freshenSkeletonMasked, ↓reduceIte] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨headPair, headSuccess, remaining⟩
              rcases headPair with ⟨head, middle⟩
              rcases Option.bind_eq_some_iff.mp remaining with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, last⟩
              have resultEq : last = result := by
                exact (Prod.mk.inj (Option.some.inj finished)).2
              subst result
              exact (ValidatorRunExtension.ofFreshenSkeleton
                headSuccess).trans
                (ValidatorRunExtension.ofFreshenSkeletonMasked tailSuccess)

end

/-- Allocate the shared fallback assignments in list order. -/
theorem ValidatorRunExtension.ofFreshPatternCtorAssignments
    {terminal : Subst} {signature : FrozenSig}
    {origin : ConstraintOrigin} {variables : List TyVar}
    {state result : InferState} {assignments : Projection.Assignments}
    (success : freshPatternCtorAssignments origin variables state =
      (assignments, result)) :
    ValidatorRunExtension terminal signature state result := by
  induction variables generalizing state assignments result with
  | nil =>
      simp only [freshPatternCtorAssignments, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ValidatorRunExtension.refl terminal signature state
  | cons varId variables ih =>
      simp only [freshPatternCtorAssignments] at success
      let middle := (state.freshCap origin).2
      rcases tailEq : freshPatternCtorAssignments origin variables middle with
        ⟨tailAssignments, last⟩
      have resultEq : last = result := by
        simp [middle, tailEq] at success
        exact success.2
      subst result
      exact (ValidatorRunExtension.freshCap terminal signature state
        origin).trans (ih tailEq)

/-- Child-capability alignment contains only resolved capability equations. -/
theorem ValidatorRunExtension.ofAlignPatternCtorCapabilities
    {terminal : Subst} {signature : FrozenSig}
    {state result : InferState} {origin : ConstraintOrigin}
    {children : List Cap} {demands : List (Option Cap)}
    (success : alignPatternCtorCapabilities state origin children demands =
      some result) :
    ValidatorRunExtension terminal signature state result := by
  induction children generalizing state result demands with
  | nil =>
      cases demands with
      | nil =>
          simp only [alignPatternCtorCapabilities, Option.some.injEq] at success
          subst result
          exact ValidatorRunExtension.refl terminal signature state
      | cons _ _ => simp [alignPatternCtorCapabilities] at success
  | cons child children induction =>
      cases demands with
      | nil => simp [alignPatternCtorCapabilities] at success
      | cons demand demands =>
          cases demand with
          | none =>
              simp only [alignPatternCtorCapabilities] at success
              exact induction success
          | some expected =>
              simp only [alignPatternCtorCapabilities] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨middle, headSuccess, tailSuccess⟩
              exact (ValidatorRunExtension.ofRunResolvedConstraint
                (terminal := terminal) (signature := signature)
                headSuccess).trans (induction tailSuccess)

/-- Both the direct projection and fallback branches of constructor
capability solving are validator-complete. -/
theorem ValidatorRunExtension.ofSolvePatternCtorCapability
    {terminal : Subst} {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {childCaps : List Cap}
    {state result : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin childCaps
      state = some (capability, result)) :
    ValidatorRunExtension terminal signature state result := by
  unfold solvePatternCtorCapability at success
  simp only at success
  split at success
  · exact ValidatorRunExtension.ofFreshenSkeleton success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨resultVariables, _, remaining⟩
    rcases allocationEq : freshPatternCtorAssignments origin
        resultVariables.eraseDups state with
      ⟨assignments, allocated⟩
    simp only [allocationEq] at remaining
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨demands, demandsSuccess, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨aligned, alignmentSuccess, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨projected, _, skeletonSuccess⟩
    exact (ValidatorRunExtension.ofFreshPatternCtorAssignments
      (terminal := terminal) (signature := signature) allocationEq).trans
      ((ValidatorRunExtension.ofAlignPatternCtorCapabilities
        (terminal := terminal) (signature := signature)
        alignmentSuccess).trans
        (ValidatorRunExtension.ofFreshenSkeleton skeletonSuccess))

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
