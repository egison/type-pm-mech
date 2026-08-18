import TypePM.BridgeChecks
import TypePM.DamasMilnerWLetStability
import TypePM.DemandTypingInferenceCompletenessPairedChecking
import TypePM.DemandTypingInferenceCompletenessFixMatcher
import TypePM.DemandTypingInferenceCompletenessPrimitivePatternCertified

/-!
# Actual-trace interface for terminal let generalization

The executable terminal check combines two logically separate facts for every
recorded `let`:

* the event faithfully records the solver cut at which generalization was
  performed;
* the generalized scheme remains stable across the later solver suffix.

The first fact follows locally from append-only inference history.  The second
is exactly `DM.PendingLetCut.StableAt`, for which
`DamasMilnerWLetStability` provides registration and one-step preservation
lemmas.  This file connects those facts to the existing executable checker.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-- Cut-local fields of one terminal-sensitive `let` event. -/
def LetEventLocalAt (signature : FrozenSig) (state : InferState) :
    TraceEvent → Prop
  | .letGeneralization solveCount _name rawContext rawTarget context target
      scheme =>
      solveCount ≤ state.trace.solves.length ∧
      context = rawContext.applySubst
        (replay (state.trace.solves.take solveCount)) ∧
      target = (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
      scheme = signature.generalize context target
  | _ => True

/-- The genuinely terminal part of one recorded `let` event. -/
def LetEventStableAt (signature : FrozenSig) (state : InferState) :
    TraceEvent → Prop
  | .letGeneralization solveCount _name rawContext rawTarget _context _target
      _scheme =>
      (DM.PendingLetCut.mk rawContext rawTarget
        (replay (state.trace.solves.take solveCount))).StableAt
          signature state.prevailing
  | _ => True

/-- Every recorded event has faithful cut-local fields. -/
def TraceLetLocalConditions (signature : FrozenSig)
    (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events → LetEventLocalAt signature state event

/-- Every recorded `let` cut is stable at the root terminal substitution. -/
def TraceLetStableConditions (signature : FrozenSig)
    (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events → LetEventStableAt signature state event

/-- A chronological run has introduced only locally faithful `let` events.
Unlike `TraceLetLocalConditions`, this incremental form composes without any
assumption about events already present at the incoming cut. -/
structure LetLocalHistoryExtension (signature : FrozenSig)
    (earlier later : InferState) : Prop where
  history : earlier.HistoryPrefix later
  newEvents : ∀ event,
    event ∈ later.trace.events → event ∉ earlier.trace.events →
      LetEventLocalAt signature later event

namespace LetEventLocalAt

/-- Local event fidelity is stable under every later append-only suffix. -/
theorem transport
    {signature : FrozenSig} {earlier later : InferState} {event : TraceEvent}
    (localAt : LetEventLocalAt signature earlier event)
    (history : earlier.HistoryPrefix later) :
    LetEventLocalAt signature later event := by
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target
      scheme =>
      rcases localAt with
        ⟨solveBound, contextEq, targetEq, schemeEq⟩
      have prefixEq :
          later.trace.solves.take solveCount =
            earlier.trace.solves.take solveCount := by
        rcases history with ⟨suffix, _eventSuffix, solvesEq, _eventsEq⟩
        rw [solvesEq, List.take_append_of_le_length solveBound]
      exact ⟨Nat.le_trans solveBound history.solve_length_le,
        by simpa [prefixEq] using contextEq,
        by simpa [prefixEq] using targetEq, schemeEq⟩
  | _ => trivial

end LetEventLocalAt

namespace LetLocalHistoryExtension

theorem refl (signature : FrozenSig) (state : InferState) :
    LetLocalHistoryExtension signature state state := by
  refine ⟨InferState.HistoryPrefix.refl state, ?_⟩
  intro event membership previous
  exact False.elim (previous membership)

theorem trans
    {signature : FrozenSig} {first middle last : InferState}
    (front : LetLocalHistoryExtension signature first middle)
    (back : LetLocalHistoryExtension signature middle last) :
    LetLocalHistoryExtension signature first last := by
  refine ⟨front.history.trans back.history, ?_⟩
  intro event finalMembership notFirst
  by_cases inMiddle : event ∈ middle.trace.events
  · exact (front.newEvents event inMiddle notFirst).transport back.history
  · exact back.newEvents event finalMembership inMiddle

theorem right_congr
    {signature : FrozenSig} {initial first second : InferState}
    (extension : LetLocalHistoryExtension signature initial first)
    (equality : first = second) :
    LetLocalHistoryExtension signature initial second := by
  subst second
  exact extension

theorem snd_of_eq
    {signature : FrozenSig} {α : Type} {initial final : InferState}
    {pair : α × InferState} {value : α}
    (extension : LetLocalHistoryExtension signature initial pair.2)
    (equality : pair = (value, final)) :
    LetLocalHistoryExtension signature initial final := by
  exact extension.right_congr (congrArg Prod.snd equality)

/-- Advance the absolute local invariant through one certified extension. -/
theorem apply
    {signature : FrozenSig} {earlier later : InferState}
    (extension : LetLocalHistoryExtension signature earlier later)
    (before : TraceLetLocalConditions signature earlier) :
    TraceLetLocalConditions signature later := by
  intro event membership
  by_cases previous : event ∈ earlier.trace.events
  · exact (before event previous).transport extension.history
  · exact extension.newEvents event membership previous

/-- Package one explicit event append. -/
theorem recordEvent
    {signature : FrozenSig} {state : InferState} {event : TraceEvent}
    (latest : LetEventLocalAt signature (state.recordEvent event) event) :
    LetLocalHistoryExtension signature state (state.recordEvent event) := by
  refine ⟨state.historyPrefix_recordEvent event, ?_⟩
  intro candidate membership previous
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with old | newest
  · exact False.elim (previous old)
  · subst candidate
    exact latest

/-- Every event constructor other than `letGeneralization` is locally
vacuous. -/
theorem recordNonLetEvent
    {signature : FrozenSig} {state : InferState} {event : TraceEvent}
    (nonLet : match event with
      | .letGeneralization _ _ _ _ _ _ _ => False
      | _ => True) :
    LetLocalHistoryExtension signature state (state.recordEvent event) := by
  apply recordEvent
  cases event <;> simp_all [LetEventLocalAt]

/-- The actual `let` emitter records the exact current solver cut and the
scheme generalized there. -/
theorem recordLetGeneralization
    (signature : FrozenSig) (state : InferState) (name : String)
    (rawContext : Context) (rawTarget : Ty) :
    LetLocalHistoryExtension signature state
      (state.recordEvent (.letGeneralization state.trace.solves.length name
        rawContext rawTarget (rawContext.applySubst state.prevailing)
        (state.prevailing.apply rawTarget)
        (signature.generalize (rawContext.applySubst state.prevailing)
          (state.prevailing.apply rawTarget)))) := by
  apply recordEvent
  unfold LetEventLocalAt
  simp only [InferState.recordEvent, List.take_length, InferState.prevailing]
  exact ⟨Nat.le_refl _, trivial, trivial, trivial⟩

/-- Package a history extension which adds no reconstruction event. -/
theorem ofNoEvents
    {signature : FrozenSig} {earlier later : InferState}
    (history : earlier.HistoryPrefix later)
    (eventsEq : later.trace.events = earlier.trace.events) :
    LetLocalHistoryExtension signature earlier later := by
  refine ⟨history, ?_⟩
  intro event membership previous
  exfalso
  exact previous (by simpa [eventsEq] using membership)

/-- A non-history state update followed by one ordinary event. -/
theorem sameTraceThenRecordNonLet
    {signature : FrozenSig} {earlier middle : InferState}
    (sameTrace : middle.trace = earlier.trace) (event : TraceEvent)
    (nonLet : match event with
      | .letGeneralization _ _ _ _ _ _ _ => False
      | _ => True) :
    LetLocalHistoryExtension signature earlier (middle.recordEvent event) := by
  have front : LetLocalHistoryExtension signature earlier middle :=
    ofNoEvents (InferState.HistoryPrefix.of_same_trace sameTrace)
      (by simpa using congrArg InferTrace.events sameTrace)
  exact front.trans (recordNonLetEvent nonLet)

/-- A validator chronology for an event-free helper can be projected to the
strictly weaker local-let chronology.  The projection discards every
terminal semantic fact; only the four cut-local fields of a hypothetical
`let` witness are retained. -/
theorem ofValidatorRun
    {terminal : Subst} {signature : FrozenSig}
    {earlier later : InferState}
    (run :
      DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension
        terminal signature earlier later) :
    LetLocalHistoryExtension signature earlier later := by
  refine ⟨run.sensitive.state.history, ?_⟩
  intro event membership previous
  have covered := run.sensitive.newEvents event membership previous
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target
      scheme =>
      simp only [TerminalAuditCoveredEvent] at covered
      cases covered with
      | letE solveBound contextEq targetEq schemeEq facts =>
          exact ⟨solveBound, contextEq, targetEq, schemeEq⟩
  | _ => trivial

theorem freshTy (signature : FrozenSig) (state : InferState)
    (origin : ConstraintOrigin) :
    LetLocalHistoryExtension signature state (state.freshTy origin).2 :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.freshTy
      Subst.id signature state origin)

theorem freshCap (signature : FrozenSig) (state : InferState)
    (origin : ConstraintOrigin) :
    LetLocalHistoryExtension signature state (state.freshCap origin).2 :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.freshCap
      Subst.id signature state origin)

theorem freshTy_of_eq
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {target : Ty}
    (success : state.freshTy origin = (target, final)) :
    LetLocalHistoryExtension signature state final :=
  snd_of_eq (freshTy signature state origin) success

theorem freshCap_of_eq
    {signature : FrozenSig} {state final : InferState}
    {origin : ConstraintOrigin} {capability : Cap}
    (success : state.freshCap origin = (capability, final)) :
    LetLocalHistoryExtension signature state final :=
  snd_of_eq (freshCap signature state origin) success

theorem visit (signature : FrozenSig) (state : InferState)
    (kind : NodeKind) (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      (Inference.visit state kind path) :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.visit
      Subst.id signature state kind path)

theorem finishExpr (signature : FrozenSig) (state : InferState)
    (expression : Expr) (path : SyntaxPath) (target : Ty) :
    LetLocalHistoryExtension signature state
      (Inference.finishExpr expression path target state).state :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.finishExpr
      Subst.id signature state expression path target)

theorem recordInferredPPat (signature : FrozenSig) (state : InferState)
    (pattern : PPat) (target : Ty) (holes : List Dual)
    (bindings : MonoCtx) (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      (state.recordEvent
        (.inferredPPat pattern target holes bindings path)) :=
  recordNonLetEvent trivial

theorem recordInferredDPat (signature : FrozenSig) (state : InferState)
    (pattern : DPat) (target : Ty) (bindings : MonoCtx)
    (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      (state.recordEvent (.inferredDPat pattern target bindings path)) :=
  recordNonLetEvent trivial

theorem finishInferredPPat (signature : FrozenSig) (state : InferState)
    (kind : NodeKind) (pattern : PPat) (target : Ty)
    (holes : List Dual) (bindings : MonoCtx) (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      ((Inference.visit state kind path).recordEvent
        (.inferredPPat pattern target holes bindings path)) :=
  (visit signature state kind path).trans
    (recordInferredPPat signature _ pattern target holes bindings path)

theorem finishInferredDPat (signature : FrozenSig) (state : InferState)
    (kind : NodeKind) (pattern : DPat) (target : Ty)
    (bindings : MonoCtx) (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      ((Inference.visit state kind path).recordEvent
        (.inferredDPat pattern target bindings path)) :=
  (visit signature state kind path).trans
    (recordInferredDPat signature _ pattern target bindings path)

theorem recordSelfReference (signature : FrozenSig) (state : InferState)
    (binder : String) (placeholder : Ty) (path : SyntaxPath) :
    LetLocalHistoryExtension signature state
      (Inference.recordSelfReference state binder placeholder path) :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.recordSelfReference
      Subst.id signature state binder placeholder path)

theorem protectMatcherCapability (signature : FrozenSig) (state : InferState)
    (capability : Cap) :
    LetLocalHistoryExtension signature state
      (state.protectMatcherCapability capability) :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.protectMatcherCapability
      Subst.id signature state capability)

theorem protectMatcherCapabilityExcept (signature : FrozenSig)
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    LetLocalHistoryExtension signature state
      (state.protectMatcherCapabilityExcept capability borrowed) :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.protectMatcherCapabilityExcept
      Subst.id signature state capability borrowed)

theorem freezeCapabilityExport (signature : FrozenSig) (state : InferState)
    (images : List CapVar) (payload : Ty) :
    LetLocalHistoryExtension signature state
      (state.freezeCapabilityExport images payload) :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.freezeCapabilityExport
      Subst.id signature state images payload)

theorem instantiateSchemeInState (signature : FrozenSig)
    (rawContext normalizedContext : Context) (name : String)
    (state : InferState) (scheme : Scheme) :
    LetLocalHistoryExtension signature state
      (Inference.instantiateSchemeInState signature rawContext
        normalizedContext name state scheme).2 := by
  unfold Inference.instantiateSchemeInState
  dsimp only
  apply sameTraceThenRecordNonLet
  · rfl
  · trivial

theorem instantiateCtorInState (signature : FrozenSig)
    (state : InferState) (scheme : CtorScheme) :
    LetLocalHistoryExtension signature state
      (Inference.instantiateCtorInState state scheme).2 := by
  unfold Inference.instantiateCtorInState
  dsimp only
  apply sameTraceThenRecordNonLet
  · rfl
  · trivial

theorem instantiateDualInState (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (state : InferState) (scheme : DualScheme) :
    LetLocalHistoryExtension signature state
      (Inference.instantiateDualInState signature rawContext rawParameters
        rawBindings context parameters bindings state scheme).2 := by
  unfold Inference.instantiateDualInState
  dsimp only
  apply sameTraceThenRecordNonLet
  · rfl
  · trivial

theorem instantiateSchemeInState_of_eq
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state final : InferState} {scheme : Scheme}
    {target : Ty}
    (success : Inference.instantiateSchemeInState signature rawContext
      normalizedContext name state scheme = (target, final)) :
    LetLocalHistoryExtension signature state final :=
  snd_of_eq
    (instantiateSchemeInState signature rawContext normalizedContext name
      state scheme) success

theorem instantiateCtorInState_of_eq
    {signature : FrozenSig} {state final : InferState} {scheme : CtorScheme}
    {arguments : List Ty} {target : Ty}
    (success : Inference.instantiateCtorInState state scheme =
      ((arguments, target), final)) :
    LetLocalHistoryExtension signature state final :=
  snd_of_eq (instantiateCtorInState signature state scheme) success

theorem instantiateDualInState_of_eq
    {signature : FrozenSig} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {state final : InferState} {scheme : DualScheme}
    {arguments : List Dual} {target : Dual}
    (success : Inference.instantiateDualInState signature rawContext
      rawParameters rawBindings context parameters bindings state scheme =
      ((arguments, target), final)) :
    LetLocalHistoryExtension signature state final :=
  snd_of_eq
    (instantiateDualInState signature rawContext rawParameters rawBindings
      context parameters bindings state scheme) success

theorem runResolvedConstraint
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {constraint : Constraint}
    (success : Inference.runResolvedConstraint state origin constraint =
      some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofRunResolvedConstraint
      (terminal := Subst.id) (signature := signature) success)

theorem alignTypes
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {left right : Ty}
    (success : Inference.alignTypes state origin left right = some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofAlignTypes
      (terminal := Subst.id) (signature := signature) success)

theorem alignDuals
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {left right : Dual}
    (success : Inference.alignDuals state origin left right = some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofAlignDuals
      (terminal := Subst.id) (signature := signature) success)

theorem alignDualLists
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {left right : List Dual}
    (success : Inference.alignDualLists state origin left right = some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofAlignDualLists
      (terminal := Subst.id) (signature := signature) success)

theorem alignBindings
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {left right : MonoCtx}
    (success : Inference.alignBindings state origin left right = some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofAlignBindings
      (terminal := Subst.id) (signature := signature) success)

theorem alignPatternTargets
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {duals : List Dual} {targets : List Ty}
    (success : Inference.alignPatternTargets state origin duals targets =
      some result) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofAlignPatternTargets
      (terminal := Subst.id) (signature := signature) success)

theorem solvePatternCtorCapability
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {childCaps : List Cap}
    {state result : InferState} {capability : Cap}
    (success : Inference.solvePatternCtorCapability signature entry origin
      childCaps state = some (capability, result)) :
    LetLocalHistoryExtension signature state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessCertifiedRun.ValidatorRunExtension.ofSolvePatternCtorCapability
      (terminal := Subst.id) (signature := signature) success)

theorem alignExprResultAtExpected
    {signature : FrozenSig} {path : SyntaxPath}
    {expressionResult : ExprResult} {expected : Ty} {result : InferState}
    (success : Inference.alignExprResultAtExpected path expressionResult
      expected = some result) :
    LetLocalHistoryExtension signature expressionResult.state result :=
  ofValidatorRun
    (DemandTypingInferenceCompletenessPairedChecking.ValidatorRunExtension.ofAlignExprResultAtExpected
      (terminal := Subst.id) (signature := signature) success)

theorem freshTargets
    {signature : FrozenSig} {state result : InferState}
    {origin : ConstraintOrigin} {count : Nat} {targets : List Ty}
    (success : Inference.freshTargets state origin count = (targets, result)) :
    LetLocalHistoryExtension signature state result := by
  induction count generalizing state targets result with
  | zero =>
      simp only [Inference.freshTargets, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact refl signature state
  | succ count induction =>
      simp only [Inference.freshTargets] at success
      let fresh := state.freshTy origin
      let rest := Inference.freshTargets fresh.2 origin count
      have first : LetLocalHistoryExtension signature state fresh.2 :=
        freshTy signature state origin
      have tail : LetLocalHistoryExtension signature fresh.2 rest.2 :=
        induction (state := fresh.2) (targets := rest.1)
          (result := rest.2) rfl
      exact (first.trans tail).right_congr (congrArg Prod.snd success)

theorem buildFixPlaceholder
    {signature : FrozenSig} {path : SyntaxPath} {body : Expr}
    {state result : InferState} {domain codomain : Ty}
    (success : Inference.buildFixPlaceholder signature path body state =
      some (domain, codomain, result)) :
    LetLocalHistoryExtension signature state result := by
  cases body <;> simp_all [Inference.buildFixPlaceholder]
  case matcher clauses =>
    exact ofValidatorRun
      (DemandTypingInferenceCompletenessFixMatcher.ValidatorRunExtension.ofBuildFixPlaceholderMatcher
        (terminal := Subst.id) success)
  all_goals
    rcases success with ⟨_, _, rfl⟩
    exact (freshTy signature state _).trans (freshTy signature _ _)

end LetLocalHistoryExtension

/-- Well-formed primitive-pattern runs add only locally faithful `let` events
(in fact they add no `let` event at all). -/
theorem inferPPatFuel_letLocalHistoryExtension_of_wellFormed
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : PPat} {target : Ty} {state : InferState}
    {result : PPatResult}
    (closed : signature.SchemesClosed)
    (signatureBelow :
      DemandTypingInferenceCompletenessSignatureBounds.SignatureVarsBelow
        state.supply signature)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferPPatFuel fuel signature path pattern target state =
      some result) :
    LetLocalHistoryExtension signature state result.state :=
  LetLocalHistoryExtension.ofValidatorRun
    (DemandTypingInferenceCompletenessPrimitivePatternCertified.inferPPatFuel_validation
      (terminal := Subst.id) closed signatureBelow targetBounded success)

/-- The same local chronology projection for primitive data patterns. -/
theorem inferDPatFuel_letLocalHistoryExtension_of_wellFormed
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : DPat} {target : Ty} {state : InferState}
    {result : DPatResult}
    (closed : signature.SchemesClosed)
    (signatureBelow :
      DemandTypingInferenceCompletenessSignatureBounds.SignatureVarsBelow
        state.supply signature)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferDPatFuel fuel signature path pattern target state =
      some result) :
    LetLocalHistoryExtension signature state result.state :=
  LetLocalHistoryExtension.ofValidatorRun
    (DemandTypingInferenceCompletenessPrimitivePatternCertified.inferDPatFuel_validation
      (terminal := Subst.id) closed signatureBelow targetBounded success)

/-- Local event fidelity plus pending-cut stability is exactly the semantic
condition consumed by `traceGeneralizationCheck`. -/
theorem traceGeneralizationConditions_of_local_stable
    {signature : FrozenSig} {state : InferState}
    (localCond : TraceLetLocalConditions signature state)
    (stable : TraceLetStableConditions signature state) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have localAt := localCond event membership
  have stableAt := stable event membership
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target
      scheme =>
      rcases localAt with
        ⟨solveBound, contextEq, targetEq, schemeEq⟩
      refine ⟨solveBound, contextEq, targetEq, schemeEq, ?_⟩
      unfold LetEventStableAt at stableAt
      unfold DM.PendingLetCut.StableAt DM.PendingLetCut.localScheme at stableAt
      simpa [contextEq, targetEq, schemeEq] using stableAt
  | _ => trivial

/-- Consequently the finite Boolean check accepts once the two actual-trace
invariants have been established. -/
theorem traceGeneralizationCheck_of_local_stable
    {signature : FrozenSig} {state : InferState}
    (localCond : TraceLetLocalConditions signature state)
    (stable : TraceLetStableConditions signature state) :
    traceGeneralizationCheck signature state = true :=
  traceGeneralizationCheck_complete
    (traceGeneralizationConditions_of_local_stable localCond stable)

/-- Recording one `let` event at the current solver length gives faithful
local fields at every append-only extension of that state. -/
theorem letEventLocalAt_of_recorded_history
    {signature : FrozenSig} {cut terminal : InferState}
    {name : String} {rawContext : Context} {rawTarget : Ty}
    (history :
      (cut.recordEvent (.letGeneralization cut.trace.solves.length name
        rawContext rawTarget (rawContext.applySubst cut.prevailing)
        (cut.prevailing.apply rawTarget)
        (signature.generalize (rawContext.applySubst cut.prevailing)
          (cut.prevailing.apply rawTarget)))).HistoryPrefix terminal) :
    LetEventLocalAt signature terminal
      (.letGeneralization cut.trace.solves.length name rawContext rawTarget
        (rawContext.applySubst cut.prevailing)
        (cut.prevailing.apply rawTarget)
        (signature.generalize (rawContext.applySubst cut.prevailing)
          (cut.prevailing.apply rawTarget))) := by
  have solveBound := history.solve_length_le
  have takeSolves := history.take_solves
  simp only [InferState.recordEvent] at solveBound takeSolves
  unfold LetEventLocalAt
  refine ⟨solveBound, ?_, ?_, rfl⟩
  · rw [takeSolves]
    rfl
  · rw [takeSolves]
    rfl

/-- The remaining premise for one real event is precisely the pending-cut
stability property maintained by the Damas--Milner stability framework. -/
theorem letEventConditions_of_recorded_history
    {signature : FrozenSig} {cut terminal : InferState}
    {name : String} {rawContext : Context} {rawTarget : Ty}
    (history :
      (cut.recordEvent (.letGeneralization cut.trace.solves.length name
        rawContext rawTarget (rawContext.applySubst cut.prevailing)
        (cut.prevailing.apply rawTarget)
        (signature.generalize (rawContext.applySubst cut.prevailing)
          (cut.prevailing.apply rawTarget)))).HistoryPrefix terminal)
    (stable : (DM.PendingLetCut.mk rawContext rawTarget cut.prevailing).StableAt
      signature terminal.prevailing) :
    let event := .letGeneralization cut.trace.solves.length name rawContext
      rawTarget (rawContext.applySubst cut.prevailing)
      (cut.prevailing.apply rawTarget)
      (signature.generalize (rawContext.applySubst cut.prevailing)
        (cut.prevailing.apply rawTarget))
    LetEventLocalAt signature terminal event ∧
      LetEventStableAt signature terminal event := by
  dsimp only
  refine ⟨letEventLocalAt_of_recorded_history history, ?_⟩
  simp only [LetEventStableAt]
  have takeSolves := history.take_solves
  simp only [InferState.recordEvent] at takeSolves
  simp only [takeSolves]
  exact stable

end Reconstruction
end Inference
end TypePM
