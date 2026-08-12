import TypePM.DemandTypingInferenceCompletenessValidatorEquivariance
import TypePM.DemandTypingInferenceCompletenessPatternMain
import TypePM.DemandTypingInferenceCompletenessMatcherTraversal
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
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternCtorCapability
open DemandTypingInferenceCompletenessMatcherTraversal

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

/-- Bundle-local observational equality for a pair of distinct raw operands. -/
theorem TyBisimulation.executable_eq_pure_of_mem
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger terminal state)
    (operands : List Ty) {declarativeTarget executableTarget : Ty}
    (member : declarativeTarget ∈ operands)
    (related : TyBisimulation relation declarativeTarget executableTarget) :
    state.prevailing.apply executableTarget =
      (Subst.seq
        (LocalRenamingOn.pureSubst
          (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
            operands)) terminal).apply declarativeTarget := by
  let localMap :=
    StateBisimulation.reverseLocalRenamingOn_bundleImages relation operands
  have pure : relation.reverse.apply (terminal.apply declarativeTarget) =
      (LocalRenamingOn.pureSubst localMap).apply
        (terminal.apply declarativeTarget) := by
    apply LocalRenamingOn.forward_apply_eq_pure localMap
    · intro varId free
      exact Ty.mem_fcvList_of_mem
        (List.mem_map.mpr ⟨declarativeTarget, member, rfl⟩) free
    · intro varId free
      exact Ty.mem_ftvList_of_mem
        (List.mem_map.mpr ⟨declarativeTarget, member, rfl⟩) free
  rw [related.reverse, Subst.seq_apply]
  exact pure

theorem DualListBisimulation.resolvedCaps_eq_pure
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {declarativeHoles executableHoles : List Dual}
    (related : DualListBisimulation relation declarativeHoles executableHoles)
    (operands : List Ty)
    (included : ∀ declarativeDual, declarativeDual ∈ declarativeHoles →
      Ty.matcher declarativeDual.cap .unit ∈ operands) :
    (executableHoles.map (Dual.applySubst state.prevailing)).map Dual.cap =
      (declarativeHoles.map (Dual.applySubst
        (Subst.seq
          (LocalRenamingOn.pureSubst
            (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
              operands)) terminal))).map Dual.cap := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · have shell := TyBisimulation.executable_eq_pure_of_mem relation
            operands (included _ (by simp)) head.cap
        exact (Ty.matcher.inj shell).1
      · exact induction (fun item itemMem => included item (by simp [itemMem]))

theorem DualListsBisimulation.resolved_eq_pure
    {ledger : CapabilityOriginLedger} {terminal : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {declarativeLists executableLists : List (List Dual)}
    (related : DualListsBisimulation relation declarativeLists executableLists)
    (operands : List Ty)
    (included : ∀ declarativeDual,
      declarativeDual ∈ declarativeLists.flatten →
      Ty.matcher declarativeDual.cap .unit ∈ operands) :
    terminalHoleCaps state.prevailing executableLists =
      terminalHoleCaps
        (Subst.seq
          (LocalRenamingOn.pureSubst
            (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
              operands)) terminal)
        declarativeLists := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [terminalHoleCaps, List.map_cons, List.cons.injEq]
      constructor
      · exact DualListBisimulation.resolvedCaps_eq_pure head operands
          (fun item itemMem => included item (by
            exact List.mem_flatten.mpr ⟨_, by simp, itemMem⟩))
      · exact induction (fun item itemMem => included item (by
          obtain ⟨holes, holesMem, within⟩ := List.mem_flatten.mp itemMem
          exact List.mem_flatten.mpr ⟨holes, by simp [holesMem], within⟩))

/-- Matcher terminal facts transfer directly across paired raw operands. -/
theorem DDTerminalAudit.MatcherFacts.valid_bisimulation_related
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {declarativeHoleLists executableHoleLists : List (List Dual)}
    {declarativeCapability executableCapability : Cap}
    (target : TyBisimulation relation declarativeTarget executableTarget)
    (holes : DualListsBisimulation relation declarativeHoleLists
      executableHoleLists)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      declarativeHoleLists declarativeCapability declarativeTarget) :
    let terminalTarget := state.prevailing.apply executableTarget
    let terminalHoleLists := terminalHoleCaps state.prevailing
      executableHoleLists
    let terminalCapability := executableCapability.apply state.prevailing.cap
    ∃ evidence,
      collectClauseEvidence signature.toMatcherSig clauses terminalHoleLists =
          some evidence ∧
      Shape.inferShape signature.observability evidence =
          some terminalCapability ∧
      clauseCapsListCheck signature terminalCapability clauses
          terminalHoleLists = true ∧
      armExhaustiveCheck signature clauses terminalTarget = true ∧
      coverageCheck signature.toMatcherSig clauses terminalCapability = true := by
  dsimp only
  let holeShells := declarativeHoleLists.flatMap fun holeList =>
    holeList.map fun dual => Ty.matcher dual.cap .unit
  let operands := declarativeTarget ::
    Ty.matcher declarativeCapability .unit :: holeShells
  let localMap := StateBisimulation.reverseLocalRenamingOn_bundleImages
    relation operands
  let post := LocalRenamingOn.pureSubst localMap
  have moved := DDTerminalAudit.MatcherFacts.transportLocalRenaming localMap
    armBasic facts
  have targetEq : state.prevailing.apply executableTarget =
      (Subst.seq post terminal).apply declarativeTarget :=
    TyBisimulation.executable_eq_pure_of_mem relation operands
      (by simp [operands]) target
  have holesEq : terminalHoleCaps state.prevailing executableHoleLists =
      terminalHoleCaps (Subst.seq post terminal) declarativeHoleLists := by
    apply DualListsBisimulation.resolved_eq_pure holes operands
    intro dual membership
    simp only [operands, holeShells, List.mem_cons, List.mem_flatMap,
      List.mem_map]
    obtain ⟨holeList, listMem, dualMem⟩ := List.mem_flatten.mp membership
    exact Or.inr (Or.inr ⟨holeList, listMem, dual, dualMem, rfl⟩)
  have capabilityEq : executableCapability.apply state.prevailing.cap =
      declarativeCapability.apply (Subst.seq post terminal).cap := by
    have shell := TyBisimulation.executable_eq_pure_of_mem relation operands
      (by simp [operands]) capability
    exact (Ty.matcher.inj shell).1
  rcases moved.valid with ⟨evidence, collected, inferred, caps, arms, coverage⟩
  exact ⟨evidence, by simpa [holesEq] using collected,
    by simpa [capabilityEq] using inferred,
    by simpa [holesEq, capabilityEq] using caps,
    by simpa [targetEq] using arms,
    by simpa [capabilityEq] using coverage⟩

theorem DualListBisimulation.capabilities_append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    {declarativeCapability executableCapability : Cap}
    (duals : DualListBisimulation relation declarativeDuals executableDuals)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability) :
    CapListBisimulation relation
      (declarativeDuals.map Dual.cap ++ [declarativeCapability])
      (executableDuals.map Dual.cap ++ [executableCapability]) := by
  induction duals with
  | nil => exact .cons capability .nil
  | cons head tail induction => exact .cons head.cap induction

theorem DualListBisimulation.length_eq_local
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    (duals : DualListBisimulation relation declarativeDuals executableDuals) :
    declarativeDuals.length = executableDuals.length := by
  induction duals with
  | nil => rfl
  | cons _ _ induction => exact congrArg Nat.succ induction

theorem Cap.applyRenList_append (rename : CapVar → CapVar) :
    ∀ left right,
      Cap.applyRenList rename (left ++ right) =
        Cap.applyRenList rename left ++ Cap.applyRenList rename right
  | [], _ => rfl
  | _ :: _, _ => by
      simp only [List.cons_append, Cap.applyRenList]
      rw [Cap.applyRenList_append]

theorem Cap.length_applyRenList (rename : CapVar → CapVar) :
    ∀ capabilities,
      (Cap.applyRenList rename capabilities).length = capabilities.length
  | [] => rfl
  | _ :: rest => by
      simp only [Cap.applyRenList, List.length_cons, Nat.succ.injEq]
      exact Cap.length_applyRenList rename rest

/-- Terminal constructor facts transfer across paired DD/executable operands.
This is the semantic core needed when a trace event stores executable raw
operands while the terminal audit tree stores their DD counterparts. -/
theorem DDTerminalAudit.PatternCtorFacts.compatible_bisimulation
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {ledger : CapabilityOriginLedger}
    (relation : StateBisimulation ledger terminal state)
    {entry : PatternCtorScheme signature.observability}
    {declarativeDuals executableDuals : List Dual}
    {declarativeCapability executableCapability : Cap}
    (dualsRelated : DualListBisimulation relation declarativeDuals
      executableDuals)
    (capabilityRelated : CapBisimulation relation declarativeCapability
      executableCapability)
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry declarativeDuals
      declarativeCapability) :
    entry.CapCompatible
      ((executableDuals.map Dual.cap).map
        (fun capability => capability.apply state.prevailing.cap))
      (executableCapability.apply state.prevailing.cap) := by
  let allRelated := DualListBisimulation.capabilities_append dualsRelated
    capabilityRelated
  obtain ⟨rename, resolved⟩ :=
    CapListBisimulation.executableResolved_eq_applyRen allRelated
  let post : Subst :=
    { cap := fun varId => .var (rename varId)
      target := fun varId => .var varId }
  have variablePost : VariablePost post :=
    { capVariable := fun varId => ⟨rename varId, rfl⟩ }
  have capRenEq : variablePost.capRen = rename := by
    funext varId
    have point := variablePost.capEquation varId
    change Cap.var (rename varId) = Cap.var (variablePost.capRen varId) at point
    exact (Cap.var.inj point).symm
  have moved :=
    DDTerminalAudit.PatternCtorFacts.transportVariablePost variablePost facts
  simp only [List.map_append, List.map_singleton, List.map_map] at resolved
  rw [Cap.applyRenList_append] at resolved
  have dualLengths : executableDuals.length = declarativeDuals.length :=
    (DualListBisimulation.length_eq_local dualsRelated).symm
  have leftLengths : executableDuals.length =
      (Cap.applyRenList rename
        (declarativeDuals.map
          ((fun capability => capability.apply terminal.cap) ∘ Dual.cap))).length := by
    simp only [List.length_map, Cap.length_applyRenList]
    exact dualLengths
  have resolvedParts := List.append_inj resolved (by
    simpa only [List.length_map] using leftLengths)
  have resultEq : executableCapability.apply state.prevailing.cap =
      (declarativeCapability.apply terminal.cap).applyRen rename := by
    simpa [Cap.applyRenList] using (List.cons.inj resolvedParts.2).1
  simp only [List.map_map]
  rw [resolvedParts.1, resultEq]
  have movedCompatible := moved.compatible
  change entry.CapCompatible
      ((declarativeDuals.map (Dual.applySubst (Subst.seq post terminal))).map
        Dual.cap)
      (declarativeCapability.apply (Subst.seq post terminal).cap)
    at movedCompatible
  rw [Dual.map_applySubst_seq, Dual.map_cap_applySubst]
    at movedCompatible
  rw [show (Subst.seq post terminal).cap =
      CapSubst.comp post.cap terminal.cap from rfl,
    Cap.apply_comp] at movedCompatible
  change entry.CapCompatible
      (Cap.applyList post.cap
        ((declarativeDuals.map (Dual.applySubst terminal)).map Dual.cap))
      ((declarativeCapability.apply terminal.cap).apply post.cap)
    at movedCompatible
  rw [variablePost.applyCapList_eq_applyRenList,
    variablePost.applyCap_eq_applyRen] at movedCompatible
  rw [capRenEq] at movedCompatible
  have normalizedCaps :
      declarativeDuals.map (Dual.cap ∘ Dual.applySubst terminal) =
        declarativeDuals.map
          ((fun capability => capability.apply terminal.cap) ∘ Dual.cap) := by
    apply List.map_congr_left
    intro dual _
    rfl
  simp only [List.map_map] at movedCompatible
  rw [normalizedCaps] at movedCompatible
  exact movedCompatible

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
