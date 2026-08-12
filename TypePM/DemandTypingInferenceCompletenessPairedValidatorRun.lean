import TypePM.DemandTypingInferenceCompletenessCertifiedRun
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation

/-!
# Paired terminal-audit coverage for completeness

The ordinary validator proof is local to the executable trace.  A sensitive
pattern-constructor event is different: its audit fact stores DD operands,
whereas the executable event stores the paired raw operands reconstructed by
the inference run.  This module delays that comparison while carrying the
same `BisimulationExtension` as raw completeness.  At the root terminal cut,
the paired witness projects to the existing exact terminal-audit witness.

This is a completeness-only layer.  It does not change the validator, its
trace conditions, or the public terminal-audit tree.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPairedValidatorRun

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessValidatorBisimulation
open DemandTypingInferenceCompletenessMatcherTraversal

/-- A sensitive event justified either exactly, as before, or by paired DD
and executable constructor operands under the current traversal relation. -/
inductive PairedTerminalAuditEventWitness
    (terminal : Subst) (signature : FrozenSig)
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    TraceEvent → Prop where
  | exact
      (witness : TerminalAuditEventWitness terminal signature state event) :
      PairedTerminalAuditEventWitness terminal signature relation event
  | patternCtor
      {solveCount : Nat} {name : String}
      {entry : PatternCtorScheme signature.observability}
      {declarativeDuals executableDuals : List Dual}
      {declarativeCapability executableCapability : Cap}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (lookup : signature.findPatternCtor name = some entry)
      (duals : DualListBisimulation relation declarativeDuals executableDuals)
      (capability : CapBisimulation relation declarativeCapability
        executableCapability)
      (facts : DDTerminalAudit.PatternCtorFacts terminal entry
        declarativeDuals declarativeCapability) :
      PairedTerminalAuditEventWitness terminal signature relation
        (.patternCtorCompatibility solveCount name
          (executableDuals.map Dual.cap) executableCapability)
  | matcher
      {solveCount : Nat} {clauses : List Clause}
      {declarativeTarget executableTarget localTarget : Ty}
      {declarativeHoleLists executableHoleLists : List (List Dual)}
      {localHoleLists : List (List Cap)}
      {localEvidence : List Shape.Evidence}
      {declarativeCapability executableCapability : Cap}
      (solveBound : solveCount ≤ state.trace.solves.length)
      (localTargetEq : localTarget =
        (replay (state.trace.solves.take solveCount)).apply executableTarget)
      (localHolesEq : localHoleLists = terminalHoleCaps
        (replay (state.trace.solves.take solveCount)) executableHoleLists)
      (target : TyBisimulation relation declarativeTarget executableTarget)
      (holes : DualListsBisimulation relation declarativeHoleLists
        executableHoleLists)
      (capability : CapBisimulation relation declarativeCapability
        executableCapability)
      (catchAll : catchAllLastCheck clauses = true)
      (binders : matcherBindersCheck clauses = true)
      (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
        declarativeHoleLists declarativeCapability declarativeTarget) :
      PairedTerminalAuditEventWitness terminal signature relation
        (.matcherFinalization solveCount clauses executableTarget
          executableHoleLists localTarget localHoleLists localEvidence
          executableCapability)

/-- Paired witnesses transport with the same chronological bisimulation
extension used by the raw completeness package. -/
theorem PairedTerminalAuditEventWitness.transport
    {terminal : Subst} {signature : FrozenSig}
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    (stateExtension : state.StateExtension state')
    {event : TraceEvent}
    (witness : PairedTerminalAuditEventWitness terminal signature before
      event) :
    PairedTerminalAuditEventWitness terminal signature extension.after
      event := by
  cases witness with
  | exact witness =>
      exact .exact (TerminalAuditEventWitness.transport witness
        stateExtension.history)
  | patternCtor solveBound lookup duals capability facts =>
      exact .patternCtor
        (Nat.le_trans solveBound stateExtension.history.solve_length_le)
        lookup
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          extension duals)
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          extension capability)
        facts
  | matcher solveBound localTargetEq localHolesEq target holes capability
      catchAll binders facts =>
      apply PairedTerminalAuditEventWitness.matcher
        (Nat.le_trans solveBound stateExtension.history.solve_length_le)
      · rw [HistoryPrefix.take_solves_of_le stateExtension.history solveBound]
        exact localTargetEq
      · rw [HistoryPrefix.take_solves_of_le stateExtension.history solveBound]
        exact localHolesEq
      · exact
        (extension.transportTy target)
      · exact
        (BisimulationExtension.transportDualLists extension holes)
      · exact
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          extension capability)
      · exact catchAll
      · exact binders
      · exact facts

/-- At the root cut, paired constructor operands directly satisfy the
executable validator condition.  We deliberately do not manufacture an
`exact` audit witness: its indices require syntactically identical operands,
whereas completeness promises only bisimulation. -/
theorem PairedTerminalAuditEventWitness.patternCtorCondition
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {solveCount : Nat} {name : String} {childCaps : List Cap}
    {resultCap : Cap}
    (witness : PairedTerminalAuditEventWitness terminal signature relation
      (.patternCtorCompatibility solveCount name childCaps resultCap)) :
    solveCount ≤ state.trace.solves.length ∧
      ∃ entry,
        signature.findPatternCtor name = some entry ∧
        entry.CapCompatible
          (childCaps.map fun cap => cap.apply state.prevailing.cap)
          (resultCap.apply state.prevailing.cap) := by
  cases witness with
  | exact witness =>
      exact TerminalAuditEventWitness.patternCtor_condition_bisimulation
        relation witness
  | @patternCtor solveCount name entry declarativeDuals executableDuals
      declarativeCapability executableCapability solveBound lookup duals
      capability facts =>
      have compatible :=
        DDTerminalAudit.PatternCtorFacts.compatible_bisimulation relation
          duals capability facts
      exact ⟨solveBound, entry, lookup, compatible⟩

/-- At the root cut, paired matcher operands satisfy the executable
finalization condition.  The chronological prefix equations are stored by
the paired witness, while the terminal checks transfer across the final
bisimulation. -/
theorem PairedTerminalAuditEventWitness.matcherCondition
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {solveCount : Nat} {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {localTarget : Ty}
    {localHoleLists : List (List Cap)} {localEvidence : List Shape.Evidence}
    {localCapability : Cap}
    (witness : PairedTerminalAuditEventWitness terminal signature relation
      (.matcherFinalization solveCount clauses rawTarget rawHoleLists
        localTarget localHoleLists localEvidence localCapability)) :
    solveCount ≤ state.trace.solves.length ∧
      localTarget = (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
      localHoleLists = resolvedHoleCaps
        (replay (state.trace.solves.take solveCount)) rawHoleLists ∧
      let terminalTarget := state.prevailing.apply rawTarget
      let terminalHoleLists := resolvedHoleCaps state.prevailing rawHoleLists
      let terminalCapability := localCapability.apply state.prevailing.cap
      ∃ evidence,
        collectClauseEvidence signature.toMatcherSig clauses terminalHoleLists =
            some evidence ∧
        Shape.inferShape signature.observability evidence =
            some terminalCapability ∧
        clauseCapsListCheck signature terminalCapability clauses
            terminalHoleLists = true ∧
        catchAllLastCheck clauses = true ∧
        matcherBindersCheck clauses = true ∧
        armExhaustiveCheck signature clauses terminalTarget = true ∧
        coverageCheck signature.toMatcherSig clauses terminalCapability = true := by
  cases witness with
  | exact witness =>
      exact TerminalAuditEventWitness.matcher_condition_bisimulation relation
        armBasic witness
  | matcher solveBound localTargetEq localHolesEq target holes capability
      catchAll binders facts =>
      rcases DDTerminalAudit.MatcherFacts.valid_bisimulation_related relation
        armBasic target holes capability facts with
        ⟨evidence, collected, inferred, caps, arms, coverage⟩
      exact ⟨solveBound, localTargetEq, localHolesEq, evidence, collected,
        inferred, caps, catchAll, binders, arms, coverage⟩

/-- Pointwise paired coverage of every sensitive event in one trace. -/
def PairedTerminalAuditEventCoverage
    (terminal : Subst) (signature : FrozenSig)
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) : Prop :=
  ∀ event, event ∈ state.trace.events →
    match event with
    | .patternCtorCompatibility _ _ _ _
    | .matcherFinalization _ _ _ _ _ _ _ _
    | .letGeneralization _ _ _ _ _ _ _ =>
        PairedTerminalAuditEventWitness terminal signature relation event
    | _ => True

/-- Root projection of the constructor fragment to the existing validator
condition.  Exact matcher/let witnesses remain available in the other paired
witness branch and are projected by the final whole-trace connector. -/
theorem PairedTerminalAuditEventCoverage.patternCtors
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    (coverage : PairedTerminalAuditEventCoverage terminal signature relation) :
    TracePatternCtorConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | patternCtorCompatibility _ _ _ _ =>
      exact PairedTerminalAuditEventWitness.patternCtorCondition covered
  | _ => trivial

/-- Incremental paired sensitive coverage synchronized with a raw
`BisimulationExtension`.  The relation index makes transport through later
solver suffixes explicit rather than relying on history extension alone. -/
structure PairedTerminalAuditHistoryExtension
    (terminal : Subst) (signature : FrozenSig)
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    (transition : BisimulationExtension before ledger' declarative' final)
    (stateExtension : initial.StateExtension final) :
    Prop where
  newEvents : ∀ event,
    event ∈ final.trace.events → event ∉ initial.trace.events →
      match event with
      | .patternCtorCompatibility _ _ _ _
      | .matcherFinalization _ _ _ _ _ _ _ _
      | .letGeneralization _ _ _ _ _ _ _ =>
          PairedTerminalAuditEventWitness terminal signature transition.after
            event
      | _ => True

/-- Validator chronology used by final completeness: ordinary conditions stay
executable-local, while sensitive conditions use the paired layer above. -/
structure PairedValidatorRunExtension
    (terminal : Subst) (signature : FrozenSig)
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    (transition : BisimulationExtension before ledger' declarative' final)
    (stateExtension : initial.StateExtension final) :
    Prop where
  ordinary : OrdinaryValidatorHistoryExtension signature initial final
  sensitive : PairedTerminalAuditHistoryExtension terminal signature transition
    stateExtension

/-- Existing exact validator chronology embeds into paired chronology without
changing any event proof. -/
theorem PairedValidatorRunExtension.ofExact
    {terminal : Subst} {signature : FrozenSig}
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {initial final : InferState}
    {before : StateBisimulation ledger declarative initial}
    (transition : BisimulationExtension before ledger' declarative' final)
    (exact : ValidatorRunExtension terminal signature initial final) :
    PairedValidatorRunExtension terminal signature transition
      exact.ordinary.history := by
  refine ⟨exact.ordinary, ⟨?_⟩⟩
  intro event membership previous
  have covered := exact.sensitive.newEvents event membership previous
  cases event <;> try trivial
  all_goals exact .exact covered

/-- Empty paired chronology. -/
theorem PairedValidatorRunExtension.refl
    (terminal : Subst) (signature : FrozenSig)
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    PairedValidatorRunExtension terminal signature
      (BisimulationExtension.refl relation)
      (InferState.StateExtension.refl state) :=
  PairedValidatorRunExtension.ofExact
    (BisimulationExtension.refl relation)
    (ValidatorRunExtension.refl terminal signature state)

/-- Record a constructor-compatibility event whose trace operands are the
executable representatives of the DD operands.  The event itself does not
change the state relation, so the paired witness is established exactly at
the post-recording cut and can subsequently be transported by `trans`. -/
theorem PairedValidatorRunExtension.recordPatternCtor
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {name : String} {entry : PatternCtorScheme signature.observability}
    {declarativeDuals executableDuals : List Dual}
    {declarativeCapability executableCapability : Cap}
    (lookup : signature.findPatternCtor name = some entry)
    (duals : DualListBisimulation relation declarativeDuals executableDuals)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry
      declarativeDuals declarativeCapability) :
    let event := TraceEvent.patternCtorCompatibility
      state.trace.solves.length name (executableDuals.map Dual.cap)
      executableCapability
    PairedValidatorRunExtension terminal signature
      (relation.recordEventExtension event)
      (state.stateExtension_recordEvent event) := by
  dsimp only
  let event := TraceEvent.patternCtorCompatibility
    state.trace.solves.length name (executableDuals.map Dual.cap)
    executableCapability
  let transition := relation.recordEventExtension event
  let history := state.stateExtension_recordEvent event
  refine ⟨?_, ⟨?_⟩⟩
  · apply OrdinaryValidatorHistoryExtension.recordEvent
    intro future extension producerSafe
    refine
      { traversal := ?_
        typeAlignment := by trivial
        dualAlignment := by trivial }
    exact
      { primitiveHole := ⟨by trivial⟩
        patternLeaf := ⟨by trivial⟩
        canonicalInstance := ⟨by trivial⟩
        slot := ⟨by trivial⟩ }
  · intro candidate membership previous
    simp only [InferState.recordEvent, List.mem_append,
      List.mem_singleton] at membership
    rcases membership with old | newest
    · exact False.elim (previous old)
    · subst candidate
      exact .patternCtor (Nat.le_refl _) lookup
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          transition duals)
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          transition capability)
        facts

/-- Record the two-event matcher-finalization suffix with DD and executable
raw operands kept explicitly paired. -/
theorem PairedValidatorRunExtension.recordMatcherFinalization
    {terminal : Subst} {signature : FrozenSig}
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {declarativeHoleLists executableHoleLists : List (List Dual)}
    {declarativeCapability executableCapability : Cap}
    {evidence : List Shape.Evidence}
    (target : TyBisimulation relation declarativeTarget executableTarget)
    (holes : DualListsBisimulation relation declarativeHoleLists
      executableHoleLists)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (catchAll : catchAllLastCheck clauses = true)
    (binders : matcherBindersCheck clauses = true)
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      declarativeHoleLists declarativeCapability declarativeTarget) :
    let coverageEvent := TraceEvent.literalCoverage clauses executableCapability
    let covered := state.recordEvent coverageEvent
    let finalizationEvent := TraceEvent.matcherFinalization
      covered.trace.solves.length clauses executableTarget executableHoleLists
      (covered.prevailing.apply executableTarget)
      (terminalHoleCaps covered.prevailing executableHoleLists)
      evidence executableCapability
    let coverageTransition := relation.recordEventExtension coverageEvent
    let finalizationTransition :=
      coverageTransition.after.recordEventExtension finalizationEvent
    PairedValidatorRunExtension terminal signature
      (coverageTransition.seq finalizationTransition)
      ((state.stateExtension_recordEvent coverageEvent).trans
        (covered.stateExtension_recordEvent finalizationEvent)) := by
  dsimp only
  let coverageEvent := TraceEvent.literalCoverage clauses executableCapability
  let covered := state.recordEvent coverageEvent
  let finalizationEvent := TraceEvent.matcherFinalization
    covered.trace.solves.length clauses executableTarget executableHoleLists
    (covered.prevailing.apply executableTarget)
    (terminalHoleCaps covered.prevailing executableHoleLists)
    evidence executableCapability
  let coverageTransition := relation.recordEventExtension coverageEvent
  let finalizationTransition :=
    coverageTransition.after.recordEventExtension finalizationEvent
  have coverageValidation := PairedValidatorRunExtension.ofExact
    coverageTransition
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (ValidatorNeutralEvent.literalCoverage clauses executableCapability))
  have finalizationHistory := covered.stateExtension_recordEvent finalizationEvent
  have finalizationValidation : PairedValidatorRunExtension terminal signature
      finalizationTransition finalizationHistory := by
    refine ⟨?_, ⟨?_⟩⟩
    · apply OrdinaryValidatorHistoryExtension.recordEvent
      intro future extension producerSafe
      refine
        { traversal := ?_
          typeAlignment := by trivial
          dualAlignment := by trivial }
      exact
        { primitiveHole := ⟨by trivial⟩
          patternLeaf := ⟨by trivial⟩
          canonicalInstance := ⟨by trivial⟩
          slot := ⟨by trivial⟩ }
    · intro candidate membership previous
      simp only [InferState.recordEvent, List.mem_append,
        List.mem_singleton] at membership
      rcases membership with old | newest
      · exact False.elim (previous (by
          simpa [InferState.recordEvent] using old))
      · subst candidate
        have witness : PairedTerminalAuditEventWitness terminal signature
            finalizationTransition.after finalizationEvent := by
          dsimp [finalizationEvent]
          refine PairedTerminalAuditEventWitness.matcher
            (terminal := terminal)
            (signature := signature)
            (relation := finalizationTransition.after)
            (declarativeTarget := declarativeTarget)
            (executableTarget := executableTarget)
            (declarativeHoleLists := declarativeHoleLists)
            (executableHoleLists := executableHoleLists)
            (declarativeCapability := declarativeCapability)
            (executableCapability := executableCapability)
            (clauses := clauses) (localEvidence := evidence)
            (Nat.le_refl covered.trace.solves.length) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · simp [InferState.recordEvent, InferState.prevailing,
              finalizationEvent, covered]
          · simp [InferState.recordEvent, InferState.prevailing,
              finalizationEvent, covered]
          · exact finalizationTransition.transportTy
              (coverageTransition.transportTy target)
          · exact BisimulationExtension.transportDualLists
              finalizationTransition
              (BisimulationExtension.transportDualLists coverageTransition holes)
          · exact
              DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
                finalizationTransition
                (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
                  coverageTransition capability)
          · exact catchAll
          · exact binders
          · exact facts
        simpa [finalizationEvent, covered, coverageEvent,
          InferState.recordEvent] using witness
  refine ⟨coverageValidation.ordinary.trans finalizationValidation.ordinary,
    ⟨?_⟩⟩
  intro event membership notFirst
  by_cases inCovered : event ∈ covered.trace.events
  · have coveredWitness := coverageValidation.sensitive.newEvents event
      inCovered notFirst
    cases event <;> try trivial
    all_goals simpa only [BisimulationExtension.seq] using
      (PairedTerminalAuditEventWitness.transport finalizationTransition
        finalizationHistory coveredWitness)
  · have finalWitness := finalizationValidation.sensitive.newEvents event
      membership inCovered
    cases event <;> try trivial
    all_goals simpa only [BisimulationExtension.seq] using finalWitness

/-- Chronological paired traversals compose along their raw bisimulation
transitions. -/
theorem PairedValidatorRunExtension.trans
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ : Subst}
    {first middle last : InferState}
    {before : StateBisimulation ledger₀ declarative₀ first}
    {frontTransition : BisimulationExtension before ledger₁ declarative₁
      middle}
    {backTransition : BisimulationExtension frontTransition.after ledger₂
      declarative₂ last}
    {frontState : first.StateExtension middle}
    {backState : middle.StateExtension last}
    (front : PairedValidatorRunExtension terminal signature frontTransition
      frontState)
    (back : PairedValidatorRunExtension terminal signature backTransition
      backState) :
    PairedValidatorRunExtension terminal signature
      (frontTransition.seq backTransition) (frontState.trans backState) := by
  refine ⟨front.ordinary.trans back.ordinary, ⟨?_⟩⟩
  intro event membership notFirst
  by_cases inMiddle : event ∈ middle.trace.events
  · have covered := front.sensitive.newEvents event inMiddle notFirst
    cases event <;> try trivial
    all_goals simpa only [BisimulationExtension.seq] using
      (PairedTerminalAuditEventWitness.transport backTransition backState
        covered)
  · have covered := back.sensitive.newEvents event membership inMiddle
    cases event <;> try trivial
    all_goals simpa only [BisimulationExtension.seq] using covered

end DemandTypingInferenceCompletenessPairedValidatorRun
end TypePM
