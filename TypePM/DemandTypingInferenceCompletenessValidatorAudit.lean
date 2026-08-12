import TypePM.DemandTypingInferenceCompletenessValidatorTraversal
import TypePM.DemandTypingTerminalAuditTree

/-!
# Terminal-audit/event correspondence for validator completeness

The proof-relevant terminal audit contains the three semantic facts that are
not stable under an arbitrary solver suffix.  The executable validator sees
the corresponding chronological events instead.  This module gives the exact
interface between those views.

`TerminalAuditEventCoverage` is intended to be constructed internally by the
raw-traversal completeness recursion.  It contains no typing derivation and is
not a public caller premise: every sensitive event is paired with the local
terminal-audit fact at the syntax node that emitted it, plus the append-only
prefix equations already established by executable traversal.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-- Exact audit/event correspondence for one of the three terminal-sensitive
events.  Constructor indices fix every raw operand, preventing a fact for one
syntax node from being used to justify another event. -/
inductive TerminalAuditEventWitness
    (terminal : Subst) (signature : FrozenSig) (state : InferState) :
    TraceEvent -> Prop where
  | patternCtor
      {solveCount : Nat} {name : String}
      {entry : PatternCtorScheme signature.observability}
      {duals : List Dual} {capability : Cap}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (lookup : signature.findPatternCtor name = some entry)
      (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
      TerminalAuditEventWitness terminal signature state
        (.patternCtorCompatibility solveCount name
          (duals.map Dual.cap) capability)
  | matcher
      {solveCount : Nat} {clauses : List Clause} {rawTarget : Ty}
      {rawHoleLists : List (List Dual)} {localTarget : Ty}
      {localHoleLists : List (List Cap)} {localEvidence : List Shape.Evidence}
      {rawCapability : Cap}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (localTargetEq : localTarget =
        (replay (state.trace.solves.take solveCount)).apply rawTarget)
      (localHolesEq : localHoleLists = resolvedHoleCaps
        (replay (state.trace.solves.take solveCount)) rawHoleLists)
      (catchAll : catchAllLastCheck clauses = true)
      (binders : matcherBindersCheck clauses = true)
      (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
        rawHoleLists rawCapability rawTarget) :
      TerminalAuditEventWitness terminal signature state
        (.matcherFinalization solveCount clauses rawTarget rawHoleLists
          localTarget localHoleLists localEvidence rawCapability)
  | letE
      {solveCount : Nat} {name : String} {rawContext : Context}
      {rawTarget : Ty} {context : Context} {target : Ty} {scheme : Scheme}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (contextEq : context = rawContext.applySubst
        (replay (state.trace.solves.take solveCount)))
      (targetEq : target =
        (replay (state.trace.solves.take solveCount)).apply rawTarget)
      (schemeEq : scheme = signature.generalize context target)
      (facts : DDTerminalAudit.LetFacts terminal signature rawContext rawTarget
        (replay (state.trace.solves.take solveCount))) :
      TerminalAuditEventWitness terminal signature state
        (.letGeneralization solveCount name rawContext rawTarget context target
          scheme)

/-- Every sensitive event in the executable trace is covered by the audit
node that emitted it.  Non-sensitive events impose no obligation. -/
def TerminalAuditEventCoverage
    (terminal : Subst) (signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .patternCtorCompatibility _ _ _ _
    | .matcherFinalization _ _ _ _ _ _ _ _
    | .letGeneralization _ _ _ _ _ _ _ =>
        TerminalAuditEventWitness terminal signature state event
    | _ => True

/-- The three event forms whose terminal meaning is supplied by the
proof-relevant audit tree.  Every other reconstruction event is ordinary for
the audit/event correspondence, even when it contributes to one of the
audit-independent validator folds. -/
def TerminalAuditSensitiveEvent : TraceEvent -> Prop
  | .patternCtorCompatibility _ _ _ _
  | .matcherFinalization _ _ _ _ _ _ _ _
  | .letGeneralization _ _ _ _ _ _ _ => True
  | _ => False

/-- Initial traces contain no sensitive events. -/
theorem TerminalAuditEventCoverage.empty
    (terminal : Subst) (signature : FrozenSig)
    (supply : InferenceBase.FreshSupply) :
    TerminalAuditEventCoverage terminal signature (InferState.empty supply) := by
  intro event membership
  simp [InferState.empty] at membership

/-- Every cut no later than a history prefix sees exactly the same solver
prefix after append-only extension. -/
theorem HistoryPrefix.take_solves_of_le
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    {count : Nat} (bound : count ≤ earlier.trace.solves.length) :
    later.trace.solves.take count = earlier.trace.solves.take count := by
  rcases history with ⟨suffix, _eventSuffix, solves, _events⟩
  rw [solves, List.take_append_of_le_length bound]

/-- An event witness remains valid through every append-only history suffix.
Terminal semantic facts are already stated at the root terminal substitution;
only solve bounds and the retained local prefix equations need transport. -/
theorem TerminalAuditEventWitness.transport
    {terminal : Subst} {signature : FrozenSig} {earlier later : InferState}
    {event : TraceEvent}
    (witness : TerminalAuditEventWitness terminal signature earlier event)
    (history : earlier.HistoryPrefix later) :
    TerminalAuditEventWitness terminal signature later event := by
  cases witness with
  | patternCtor solveBound lookup facts =>
      exact .patternCtor
        (Nat.le_trans solveBound history.solve_length_le) lookup facts
  | matcher solveBound localTargetEq localHolesEq catchAll binders facts =>
      have prefixEq := HistoryPrefix.take_solves_of_le history solveBound
      exact .matcher
        (Nat.le_trans solveBound history.solve_length_le)
        (by simpa [prefixEq] using localTargetEq)
        (by simpa [prefixEq] using localHolesEq)
        catchAll binders facts
  | letE solveBound contextEq targetEq schemeEq facts =>
      have prefixEq := HistoryPrefix.take_solves_of_le history solveBound
      exact .letE
        (Nat.le_trans solveBound history.solve_length_le)
        (by simpa [prefixEq] using contextEq)
        (by simpa [prefixEq] using targetEq)
        schemeEq
        (by simpa [prefixEq] using facts)

/-- Solver/allocation updates that append no reconstruction events transport
the whole coverage fold.  This is the preservation boundary used between
syntax emitters in the executable traversal. -/
theorem TerminalAuditEventCoverage.transportNoEvents
    {terminal : Subst} {signature : FrozenSig} {earlier later : InferState}
    (coverage : TerminalAuditEventCoverage terminal signature earlier)
    (history : earlier.HistoryPrefix later)
    (eventsEq : later.trace.events = earlier.trace.events) :
    TerminalAuditEventCoverage terminal signature later := by
  intro event membership
  have previous : event ∈ earlier.trace.events := by
    simpa [eventsEq] using membership
  have covered := coverage event previous
  cases event <;> try trivial
  all_goals exact covered.transport history

/-- Transport coverage across an actual traversal suffix that emits no new
terminal-sensitive event.  The premise is phrased extensionally on the final
trace instead of exposing a chosen event suffix: if an event value was already
present in the prefix, its existing witness transports; genuinely new values
must be ordinary.  This is robust to duplicate ordinary events and is the
direct adapter needed by successful raw traversal packages. -/
theorem TerminalAuditEventCoverage.transportOrdinaryExtension
    {terminal : Subst} {signature : FrozenSig} {earlier later : InferState}
    (coverage : TerminalAuditEventCoverage terminal signature earlier)
    (history : earlier.HistoryPrefix later)
    (ordinaryNew : ∀ event,
      event ∈ later.trace.events → event ∉ earlier.trace.events →
        ¬ TerminalAuditSensitiveEvent event) :
    TerminalAuditEventCoverage terminal signature later := by
  intro event membership
  by_cases previous : event ∈ earlier.trace.events
  · have covered := coverage event previous
    cases event <;> try trivial
    all_goals exact covered.transport history
  · have ordinary := ordinaryNew event membership previous
    cases event <;> simp_all [TerminalAuditSensitiveEvent]

/-- A successful history extension whose complete final trace contains no
sensitive event is covered without any audit premise.  This is the base case
for primitive-pattern and data-pattern traversals, which cannot emit any of
the three terminal-sensitive events. -/
theorem TerminalAuditEventCoverage.ofNoSensitiveEvents
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (noneSensitive : ∀ event, event ∈ state.trace.events →
      ¬ TerminalAuditSensitiveEvent event) :
    TerminalAuditEventCoverage terminal signature state := by
  intro event membership
  have ordinary := noneSensitive event membership
  cases event <;> simp_all [TerminalAuditSensitiveEvent]

/-- Non-sensitive events extend coverage without a new audit fact. -/
theorem TerminalAuditEventCoverage.recordOrdinaryEvent
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {event : TraceEvent}
    (before : TerminalAuditEventCoverage terminal signature state)
    (ordinary :
      match event with
      | .patternCtorCompatibility _ _ _ _
      | .matcherFinalization _ _ _ _ _ _ _ _
      | .letGeneralization _ _ _ _ _ _ _ => False
      | _ => True) :
    TerminalAuditEventCoverage terminal signature (state.recordEvent event) := by
  intro candidate membership
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with previous | newest
  · have covered := before candidate previous
    cases candidate <;> try trivial
    all_goals exact covered.transport (state.historyPrefix_recordEvent event)
  · subst candidate
    cases event <;> simp_all

/-- A sensitive emitter appends its exact local terminal-audit witness while
transporting every earlier witness through the event-only history suffix. -/
theorem TerminalAuditEventCoverage.recordSensitiveEvent
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {event : TraceEvent}
    (before : TerminalAuditEventCoverage terminal signature state)
    (latest : TerminalAuditEventWitness terminal signature
      (state.recordEvent event) event) :
    TerminalAuditEventCoverage terminal signature (state.recordEvent event) := by
  intro candidate membership
  simp only [InferState.recordEvent, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with previous | newest
  · have covered := before candidate previous
    cases candidate <;> try trivial
    all_goals exact covered.transport (state.historyPrefix_recordEvent event)
  · subst candidate
    cases event <;> try trivial
    all_goals exact latest

/-! ## Elimination at the executable terminal state -/

/-- A covered pattern-constructor event satisfies its validator condition. -/
theorem TerminalAuditEventWitness.patternCtor_condition
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {solveCount : Nat} {name : String} {childCaps : List Cap}
    {resultCap : Cap}
    (terminalEq : terminal = state.prevailing)
    (witness : TerminalAuditEventWitness terminal signature state
      (.patternCtorCompatibility solveCount name childCaps resultCap)) :
    solveCount ≤ state.trace.solves.length ∧
      ∃ entry,
        signature.findPatternCtor name = some entry ∧
        entry.CapCompatible
          (childCaps.map fun cap => cap.apply state.prevailing.cap)
          (resultCap.apply state.prevailing.cap) := by
  cases witness with
  | @patternCtor solveCount name entry duals capability solveBound lookup facts =>
      subst terminal
      refine ⟨solveBound, _, lookup, ?_⟩
      have capListEq :
          (duals.map Dual.cap).map
              (fun capability => capability.apply state.prevailing.cap) =
            (duals.map (Dual.applySubst state.prevailing)).map Dual.cap := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro dual _membership
        rfl
      rw [capListEq]
      exact facts.compatible

/-- A covered matcher-finalization event satisfies its complete terminal
suffix condition. -/
theorem TerminalAuditEventWitness.matcher_condition
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {solveCount : Nat} {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {localTarget : Ty}
    {localHoleLists : List (List Cap)} {localEvidence : List Shape.Evidence}
    {localCapability : Cap}
    (terminalEq : terminal = state.prevailing)
    (witness : TerminalAuditEventWitness terminal signature state
      (.matcherFinalization solveCount clauses rawTarget rawHoleLists
        localTarget localHoleLists localEvidence localCapability)) :
    solveCount ≤ state.trace.solves.length ∧
      localTarget =
        (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
      localHoleLists = resolvedHoleCaps
        (replay (state.trace.solves.take solveCount)) rawHoleLists ∧
      let terminalTarget := state.prevailing.apply rawTarget
      let terminalHoleLists := resolvedHoleCaps state.prevailing rawHoleLists
      let terminalCapability := localCapability.apply state.prevailing.cap
      ∃ evidence,
        collectClauseEvidence signature.toMatcherSig clauses
            terminalHoleLists = some evidence ∧
        Shape.inferShape signature.observability evidence =
            some terminalCapability ∧
        clauseCapsListCheck signature terminalCapability clauses
            terminalHoleLists = true ∧
        catchAllLastCheck clauses = true ∧
        matcherBindersCheck clauses = true ∧
        armExhaustiveCheck signature clauses terminalTarget = true ∧
        coverageCheck signature.toMatcherSig clauses terminalCapability = true := by
  cases witness with
  | matcher solveBound localTargetEq localHolesEq catchAll binders facts =>
      subst terminal
      rcases facts.valid with
        ⟨evidence, collected, inferred, clauseCaps, arms, coverage⟩
      exact ⟨solveBound, localTargetEq, localHolesEq, evidence, collected,
        inferred, clauseCaps, catchAll, binders, arms, coverage⟩

/-- A covered let-generalization event satisfies the commuting equation at
the complete executable cut. -/
theorem TerminalAuditEventWitness.let_condition
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {solveCount : Nat} {name : String} {rawContext : Context}
    {rawTarget : Ty} {context : Context} {target : Ty} {scheme : Scheme}
    (terminalEq : terminal = state.prevailing)
    (witness : TerminalAuditEventWitness terminal signature state
      (.letGeneralization solveCount name rawContext rawTarget context target
        scheme)) :
    solveCount ≤ state.trace.solves.length ∧
      context = rawContext.applySubst
        (replay (state.trace.solves.take solveCount)) ∧
      target = (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
      scheme = signature.generalize context target ∧
      scheme.applyMeta state.prevailing =
        signature.generalize (rawContext.applySubst state.prevailing)
          (state.prevailing.apply rawTarget) := by
  cases witness with
  | letE solveBound contextEq targetEq schemeEq facts =>
      subst terminal
      refine ⟨solveBound, contextEq, targetEq, schemeEq, ?_⟩
      rw [schemeEq, contextEq, targetEq]
      exact facts.stable

/-! ## Whole-trace folds -/

theorem TerminalAuditEventCoverage.patternCtors
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (terminalEq : terminal = state.prevailing)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TracePatternCtorConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | patternCtorCompatibility solveCount name childCaps resultCap =>
      exact TerminalAuditEventWitness.patternCtor_condition terminalEq covered
  | _ => trivial

theorem TerminalAuditEventCoverage.finalizations
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (terminalEq : terminal = state.prevailing)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TraceFinalizationSuffixConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | matcherFinalization solveCount clauses rawTarget rawHoleLists localTarget
      localHoleLists localEvidence localCapability =>
      exact TerminalAuditEventWitness.matcher_condition terminalEq covered
  | _ => trivial

theorem TerminalAuditEventCoverage.generalizations
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (terminalEq : terminal = state.prevailing)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target scheme =>
      exact TerminalAuditEventWitness.let_condition terminalEq covered
  | _ => trivial

/-- One internally constructed audit/event coverage certificate discharges
all three terminal-sensitive predicates consumed by `wBridgeCheck_complete`. -/
theorem terminalAuditConditions
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (terminalEq : terminal = state.prevailing)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TracePatternCtorConditions signature state ∧
      TraceFinalizationSuffixConditions signature state ∧
      TraceGeneralizationConditions signature state :=
  ⟨coverage.patternCtors terminalEq,
    coverage.finalizations terminalEq,
    coverage.generalizations terminalEq⟩

end Reconstruction
end Inference
end TypePM
