import TypePM.DemandTypingInferenceCompletenessValidatorEquivariance
import TypePM.Preservation

/-!
# Terminal-audit elimination through final state bisimulation

Terminal DD and executable substitutions need not be equal.  Their reverse
residual is nevertheless a variable renaming on the finite set of variables
occurring in terminal-normalized audit operands.  This module extracts that
renaming and consumes terminal facts observationally at the executable cut.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessValidatorBisimulation

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessValidatorEquivariance

/-- The reverse residual is a local renaming on all variables in a finite
bundle of terminal-normalized DD operands. -/
theorem StateBisimulation.reverseLocalRenamingOn_bundleImages
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger terminal state)
    (operands : List Ty) :
    LocalRenamingOn relation.reverse relation.forward
      (Ty.fcvList (operands.map terminal.apply))
      (Ty.ftvList (operands.map terminal.apply)) := by
  apply localRenamingOn_of_mutualFactorization relation.reverseEquation
    relation.forwardEquation
  · intro varId membership
    rcases Ty.mem_fcvList_split membership with
      ⟨normalized, normalizedMem, free⟩
    rcases List.mem_map.mp normalizedMem with ⟨raw, _rawMem, rfl⟩
    exact relation.declarativeIdempotent.image_cap_fixed raw varId free
  · intro varId membership
    rcases Ty.mem_ftvList_split membership with
      ⟨normalized, normalizedMem, free⟩
    rcases List.mem_map.mp normalizedMem with ⟨raw, _rawMem, rfl⟩
    exact relation.declarativeIdempotent.image_target_fixed raw varId free

/-- On every member of the audited bundle, executable normalization agrees
with normalization through the total pure representative of the extracted
local renaming. -/
theorem StateBisimulation.executable_apply_eq_pure_of_mem
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger terminal state)
    (operands : List Ty) {operand : Ty} (member : operand ∈ operands) :
    state.prevailing.apply operand =
      (Subst.seq
        (LocalRenamingOn.pureSubst
          (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
            operands)) terminal).apply
        operand := by
  let localMap := StateBisimulation.reverseLocalRenamingOn_bundleImages
    relation operands
  have pure : relation.reverse.apply (terminal.apply operand) =
      (LocalRenamingOn.pureSubst localMap).apply
        (terminal.apply operand) := by
    apply LocalRenamingOn.forward_apply_eq_pure localMap
    · intro varId free
      exact Ty.mem_fcvList_of_mem
        (List.mem_map.mpr ⟨operand, member, rfl⟩) free
    · intro varId free
      exact Ty.mem_ftvList_of_mem
        (List.mem_map.mpr ⟨operand, member, rfl⟩) free
  rw [relation.reverseEquation, Subst.seq_apply, Subst.seq_apply]
  exact pure

/-- Capability observation is the matcher-shell instance of bundle
observational equality. -/
theorem StateBisimulation.executable_cap_eq_pure_of_mem
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger terminal state)
    (operands : List Ty) {capability : Cap}
    (member : Ty.matcher capability .unit ∈ operands) :
    capability.apply state.prevailing.cap =
      capability.apply
        (Subst.seq
          (LocalRenamingOn.pureSubst
            (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
              operands)) terminal).cap := by
  have equal := StateBisimulation.executable_apply_eq_pure_of_mem relation
    operands member
  exact (Ty.matcher.inj equal).1

/-! ## Individual event elimination -/

/-- Pattern-constructor audit elimination needs only the finite capability
shells stored in that event. -/
theorem TerminalAuditEventWitness.patternCtor_condition_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    {solveCount : Nat} {name : String} {childCaps : List Cap}
    {resultCap : Cap}
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
      let operands := (duals.map fun dual => Ty.matcher dual.cap .unit) ++
        [Ty.matcher resultCap .unit]
      let localMap := StateBisimulation.reverseLocalRenamingOn_bundleImages
        relation operands
      have moved :=
        DDTerminalAudit.PatternCtorFacts.transportLocalRenaming localMap facts
      refine ⟨solveBound, entry, lookup, ?_⟩
      have childrenEq :
          (duals.map Dual.cap).map (fun cap => cap.apply state.prevailing.cap) =
            (duals.map Dual.cap).map (fun cap => cap.apply
              (Subst.seq (LocalRenamingOn.pureSubst localMap) terminal).cap) := by
        apply List.map_congr_left
        intro cap capMem
        rcases List.mem_map.mp capMem with ⟨dual, dualMem, rfl⟩
        exact StateBisimulation.executable_cap_eq_pure_of_mem relation operands
          (by
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨dual, dualMem, rfl⟩)
      have resultEq : resultCap.apply state.prevailing.cap =
          resultCap.apply
            (Subst.seq (LocalRenamingOn.pureSubst localMap) terminal).cap :=
        StateBisimulation.executable_cap_eq_pure_of_mem relation operands
          (by exact List.mem_append_right _ (by simp))
      rw [childrenEq, resultEq]
      simpa only [List.map_map, Function.comp_def, Dual.applySubst, Dual.apply]
        using moved.compatible

/-- Matcher-finalization audit elimination is observational over its raw
target, raw capability, and primitive-hole capabilities. -/
theorem TerminalAuditEventWitness.matcher_condition_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {solveCount : Nat} {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {localTarget : Ty}
    {localHoleLists : List (List Cap)} {localEvidence : List Shape.Evidence}
    {localCapability : Cap}
    (witness : TerminalAuditEventWitness terminal signature state
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
  | matcher solveBound localTargetEq localHolesEq catchAll binders facts =>
      let holeShells := rawHoleLists.flatMap fun holes =>
        holes.map fun dual => Ty.matcher dual.cap .unit
      let operands := rawTarget :: Ty.matcher localCapability .unit :: holeShells
      let localMap := StateBisimulation.reverseLocalRenamingOn_bundleImages
        relation operands
      have moved := DDTerminalAudit.MatcherFacts.transportLocalRenaming
        localMap armBasic facts
      rcases moved.valid with
        ⟨evidence, collected, inferred, caps, arms, coverage⟩
      have targetEq := StateBisimulation.executable_apply_eq_pure_of_mem
        relation operands
        (operand := rawTarget) (by simp [operands])
      have capabilityEq := StateBisimulation.executable_cap_eq_pure_of_mem
        relation operands
        (capability := localCapability) (by simp [operands])
      have holesEq : resolvedHoleCaps state.prevailing rawHoleLists =
          resolvedHoleCaps
            (Subst.seq (LocalRenamingOn.pureSubst localMap) terminal)
            rawHoleLists := by
        unfold resolvedHoleCaps
        apply List.map_congr_left
        intro holes holesMem
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro dual dualMem
        exact StateBisimulation.executable_cap_eq_pure_of_mem relation operands (by
          simp only [operands, holeShells, List.mem_cons, List.mem_flatMap,
            List.mem_map]
          exact Or.inr (Or.inr ⟨holes, holesMem, dual, dualMem, rfl⟩))
      refine ⟨solveBound, localTargetEq, localHolesEq, evidence, ?_, ?_, ?_,
        catchAll, binders, ?_, ?_⟩
      · rw [holesEq]
        exact collected
      · rw [capabilityEq]
        exact inferred
      · rw [capabilityEq, holesEq]
        exact caps
      · rw [targetEq]
        exact arms
      · rw [capabilityEq]
        exact coverage

/-- The same raw scheme is normalized-bisimilar under mutually factoring
idempotent states. -/
theorem NormalizedSchemeBisimulation.same
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger terminal state) (scheme : Scheme) :
    NormalizedSchemeBisimulation relation scheme scheme := by
  constructor
  · have equation := congrArg (Scheme.applyMeta · scheme)
      relation.forwardEquation
    simpa only [Scheme.applyMeta_seq] using equation
  · have equation := congrArg (Scheme.applyMeta · scheme)
      relation.reverseEquation
    simpa only [Scheme.applyMeta_seq] using equation

/-- Let audit elimination uses canonical generalization equivariance rather
than terminal-substitution equality. -/
theorem TerminalAuditEventWitness.let_condition_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (signatureClosed : signature.SchemesClosed)
    {solveCount : Nat} {name : String} {rawContext : Context}
    {rawTarget : Ty} {context : Context} {target : Ty} {scheme : Scheme}
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
      refine ⟨solveBound, contextEq, targetEq, schemeEq, ?_⟩
      rw [schemeEq, contextEq, targetEq]
      exact DDTerminalAudit.LetFacts.stable_of_sameContext facts
        signatureClosed
        (relation.sameTarget rawTarget)
        (NormalizedSchemeBisimulation.same relation
          (signature.generalize
            (rawContext.applySubst
              (replay (state.trace.solves.take solveCount)))
            ((replay (state.trace.solves.take solveCount)).apply rawTarget)))

/-! ## Whole-trace connector -/

theorem TerminalAuditEventCoverage.patternCtors_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TracePatternCtorConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | patternCtorCompatibility _ _ _ _ =>
      exact TerminalAuditEventWitness.patternCtor_condition_bisimulation
        relation covered
  | _ => trivial

theorem TerminalAuditEventCoverage.finalizations_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TraceFinalizationSuffixConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | matcherFinalization _ _ _ _ _ _ _ _ =>
      exact TerminalAuditEventWitness.matcher_condition_bisimulation relation
        armBasic covered
  | _ => trivial

theorem TerminalAuditEventCoverage.generalizations_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (signatureClosed : signature.SchemesClosed)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have covered := coverage event membership
  cases event with
  | letGeneralization _ _ _ _ _ _ _ =>
      exact TerminalAuditEventWitness.let_condition_bisimulation relation
        signatureClosed covered
  | _ => trivial

/-- Equality-free replacement for `terminalAuditConditions`. -/
theorem terminalAuditConditions_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (signatureWF : FrozenSigWF signature)
    (coverage : TerminalAuditEventCoverage terminal signature state) :
    TracePatternCtorConditions signature state ∧
      TraceFinalizationSuffixConditions signature state ∧
      TraceGeneralizationConditions signature state :=
  ⟨TerminalAuditEventCoverage.patternCtors_bisimulation relation coverage,
    TerminalAuditEventCoverage.finalizations_bisimulation relation
      signatureWF.armExhaustiveBasic coverage,
    TerminalAuditEventCoverage.generalizations_bisimulation relation
      signatureWF.schemesClosed coverage⟩

/-- Root-run terminal package for the public validator.  Ordinary traversal
events are supplied once in pointwise membership form, the three
suffix-sensitive events come from the terminal audit tree, and the two
alignment-equality folds are intrinsic traversal invariants.  No typing
judgment or Boolean validator success is a premise. -/
theorem wBridgeCheck_complete_of_rootCoverage
    {terminal : Subst} {signature : FrozenSig} {result : ExprResult}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal result.state)
    (signatureWF : FrozenSigWF signature)
    (traversal : TraversalValidatorEventCoverage signature result.state)
    (audit : TerminalAuditEventCoverage terminal signature result.state)
    (types : TraceTypeAlignmentConditions result.state)
    (duals : TraceDualAlignmentConditions result.state) :
    wBridgeCheck signature result = true := by
  let traversalConditions :=
    TraversalValidatorConditions.ofEventCoverage traversal
  obtain ⟨patternCtors, finalizations, generalizations⟩ :=
    terminalAuditConditions_bisimulation relation signatureWF audit
  exact wBridgeCheck_complete
    traversalConditions.primitiveHoles
    traversalConditions.patternLeaves
    patternCtors
    traversalConditions.instances
    traversalConditions.slots
    types duals finalizations generalizations

end DemandTypingInferenceCompletenessValidatorBisimulation
end TypePM
