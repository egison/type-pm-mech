import TypePM.DemandTypingInferenceCompletenessMatcherClauseCertified
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation

/-!
# Certified matcher finalization

This module transfers the declarative matcher-finalization checks across the
current demand-directed/executable bisimulation.  It then records the executable
finalization event in the paired validator chronology.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherFinalizationCertified

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessMatcherExprTraversal
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessValidatorBisimulation
open DemandTypingInferenceCompletenessValidatorEquivariance
open DemandTypingInferenceCompletenessGeneralizationEquivariance

/-- A related executable operand normalizes to the pure-renaming image of its
declarative partner on any bundle containing that partner. -/
theorem TyBisimulation.executable_eq_pure_of_mem
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (operands : List Ty) {declarativeTarget executableTarget : Ty}
    (member : declarativeTarget ∈ operands)
    (related : TyBisimulation relation declarativeTarget executableTarget) :
    state.prevailing.apply executableTarget =
      (Subst.seq
        (LocalRenamingOn.pureSubst
          (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
            operands)) declarative).apply declarativeTarget := by
  let localMap :=
    StateBisimulation.reverseLocalRenamingOn_bundleImages relation operands
  have pure : relation.reverse.apply (declarative.apply declarativeTarget) =
      (LocalRenamingOn.pureSubst localMap).apply
        (declarative.apply declarativeTarget) := by
    apply LocalRenamingOn.forward_apply_eq_pure localMap
    · intro varId free
      exact Ty.mem_fcvList_of_mem
        (List.mem_map.mpr ⟨declarativeTarget, member, rfl⟩) free
    · intro varId free
      exact Ty.mem_ftvList_of_mem
        (List.mem_map.mpr ⟨declarativeTarget, member, rfl⟩) free
  rw [related.reverse, Subst.seq_apply]
  exact pure

/-- One primitive-hole list normalizes pointwise under the same finite pure
renaming. -/
theorem DualListBisimulation.resolvedCaps_eq_pure
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeHoles executableHoles : List Dual}
    (related : DualListBisimulation relation declarativeHoles executableHoles)
    (operands : List Ty)
    (included : ∀ declarativeDual,
      declarativeDual ∈ declarativeHoles →
      Ty.matcher declarativeDual.cap .unit ∈ operands) :
    (executableHoles.map (Dual.applySubst state.prevailing)).map Dual.cap =
      (declarativeHoles.map (Dual.applySubst
        (Subst.seq
          (LocalRenamingOn.pureSubst
            (StateBisimulation.reverseLocalRenamingOn_bundleImages relation
              operands)) declarative))).map Dual.cap := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · have shell := TyBisimulation.executable_eq_pure_of_mem relation
            operands (included _ (by simp)) head.cap
        exact (Ty.matcher.inj shell).1
      · exact induction (fun item itemMem => included item (by simp [itemMem]))

/-- Nested primitive-hole capabilities normalize pointwise under the same
finite pure renaming. -/
theorem DualListsBisimulation.resolved_eq_pure
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
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
              operands)) declarative)
        declarativeLists := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [terminalHoleCaps, List.map_cons, List.cons.injEq]
      constructor
      · exact DualListBisimulation.resolvedCaps_eq_pure head operands
          (fun item itemMem => included item (by
            apply List.mem_flatten.mpr
            exact ⟨_, by simp, itemMem⟩))
      · exact induction (fun item itemMem => included item (by
          obtain ⟨holes, holesMem, within⟩ := List.mem_flatten.mp itemMem
          exact List.mem_flatten.mpr ⟨holes, by simp [holesMem], within⟩))

/-- Transfer all local matcher checks to the executable clause result. -/
noncomputable def matcherFinalization_complete
    {signature : FrozenSig} (armBasic : signature.armExhaustive =
      basicArmExhaustive)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ClausesResult} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger' : CapabilityOriginLedger}
    {target : Ty} {rawHoleLists : List (List Dual)}
    (run : ClausesRunCompletion before operation q' S' ledger' target
      rawHoleLists)
    {clauses : List Clause} {evidence : List Shape.Evidence}
    {capability : Cap}
    (collected : collectClauseEvidence signature.toMatcherSig clauses
      (terminalHoleCaps S' rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability)
    (clauseCaps : clauseCapsListCheck signature capability clauses
      (terminalHoleCaps S' rawHoleLists) = true)
    (catchAll : catchAllLastCheck clauses = true)
    (binders : matcherBindersCheck clauses = true)
    (arms : armExhaustiveCheck signature clauses (S'.apply target) = true)
    (coverage : coverageCheck signature.toMatcherSig clauses capability = true)
    (rawHolesBounded : ∀ holes ∈ rawHoleLists, ∀ dual ∈ holes,
      Dual.BoundedBy q' dual) :
    MatcherFinalizationCompletion run signature clauses capability := by
  let holeShells := rawHoleLists.flatMap fun holes =>
    holes.map fun dual => Ty.matcher dual.cap .unit
  let operands := target :: Ty.matcher capability .unit :: holeShells
  let localMap := StateBisimulation.reverseLocalRenamingOn_bundleImages
    run.transition.after operands
  let post := LocalRenamingOn.pureSubst localMap
  have capabilityFixed : capability.apply S'.cap = capability :=
    DemandTypingInferenceCompletenessMain.matcherInferredCapability_fixed
      run.transition.after.declarativeIdempotent collected inferred
  have localFacts : DDTerminalAudit.MatcherFacts S' signature clauses
      rawHoleLists capability target := by
    refine ⟨evidence, collected, ?_, ?_, arms, ?_⟩
    · simpa [capabilityFixed] using inferred
    · simpa [capabilityFixed] using clauseCaps
    · simpa [capabilityFixed] using coverage
  have moved := DDTerminalAudit.MatcherFacts.transportLocalRenaming localMap
    armBasic localFacts
  let executableEvidence := Classical.choose moved.valid
  have movedFacts := Classical.choose_spec moved.valid
  have movedCollected := movedFacts.1
  have movedInferred := movedFacts.2.1
  have movedClauseCaps := movedFacts.2.2.1
  have movedArms := movedFacts.2.2.2.1
  have movedCoverage := movedFacts.2.2.2.2
  have holesEq : terminalHoleCaps run.result.state.prevailing
      run.result.rawHoleLists = terminalHoleCaps (Subst.seq post S')
        rawHoleLists := by
    apply DualListsBisimulation.resolved_eq_pure run.holes operands
    intro dual membership
    simp only [operands, holeShells, List.mem_cons, List.mem_flatMap,
      List.mem_map]
    obtain ⟨holes, holesMem, dualMem⟩ := List.mem_flatten.mp membership
    exact Or.inr (Or.inr ⟨holes, holesMem, dual, dualMem, rfl⟩)
  let executableCapability := capability.apply (Subst.seq post S').cap
  have executableCapabilityEq : executableCapability =
      capability.apply post.cap := by
    change capability.apply (CapSubst.comp post.cap S'.cap) =
      capability.apply post.cap
    rw [Cap.apply_comp, capabilityFixed]
  have capNormalized : executableCapability.apply
      run.result.state.prevailing.cap = executableCapability := by
    apply DemandTypingInferenceCompletenessMain.matcherInferredCapability_fixed
      run.transition.after.executableIdempotent
    · rw [holesEq]
      exact movedCollected
    · exact movedInferred
  have declarativeCapabilityBounded : capability.BoundedBy q' := by
    intro varId membership
    have evidenceMember := Shape.inferShape_fcv inferred membership
    obtain ⟨resolvedHoles, resolvedHolesMem, inResolved⟩ :=
      Inference.collectClauseEvidence_fcv collected varId evidenceMember
    obtain ⟨holes, holesMem, rfl⟩ := List.mem_map.mp resolvedHolesMem
    obtain ⟨resolvedCap, resolvedCapMem, inCapability⟩ :=
      Cap.mem_fcvList_split inResolved
    obtain ⟨resolvedDual, resolvedDualMem, resolvedCapEq⟩ :=
      List.mem_map.mp resolvedCapMem
    subst resolvedCap
    obtain ⟨rawDual, rawDualMem, resolvedDualEq⟩ :=
      List.mem_map.mp resolvedDualMem
    subst resolvedDual
    exact (run.declarative_bounded.applyCap
      (rawHolesBounded holes holesMem rawDual rawDualMem).1) varId inCapability
  have executableCapabilityBounded : executableCapability.BoundedBy q' := by
    rw [executableCapabilityEq]
    intro image imageMem
    rw [Unification.Cap.fcv_apply] at imageMem
    simp only [List.mem_flatMap] at imageMem
    obtain ⟨varId, varMem, imageMem⟩ := imageMem
    have below := declarativeCapabilityBounded varId varMem
    have scope : varId ∈ (S'.apply (.matcher capability .unit)).fcv := by
      simpa [Subst.apply_matcher, capabilityFixed, Ty.fcv] using varMem
    have bundleScope : varId ∈ Ty.fcvList (operands.map S'.apply) :=
      Ty.mem_fcvList_of_mem
        (List.mem_map.mpr ⟨.matcher capability .unit, by simp [operands], rfl⟩)
        scope
    have reverseBound := run.reverse_bounded.capImagesBounded varId below
    have imageEq : image = localMap.capImage varId := by
      simpa [post, LocalRenamingOn.pureSubst, Cap.fcv] using imageMem
    subst image
    exact reverseBound _ (by
      rw [localMap.cap_forward bundleScope]
      simp [Cap.fcv])
  have capRelated : CapBisimulation run.transition.after capability
      executableCapability := by
    constructor
    · simp only [Subst.apply_matcher, Subst.apply_unit, capabilityFixed,
        Ty.matcher.injEq, and_true]
      rw [capNormalized]
      rw [executableCapabilityEq]
      symm
      rw [← Cap.apply_comp]
      apply Cap.apply_eq_self_of_fcv_fixed
      intro varId membership
      have scope : varId ∈
          (S'.apply (.matcher capability .unit)).fcv := by
        simpa [Subst.apply_matcher, capabilityFixed, Ty.fcv] using membership
      have bundleScope : varId ∈ Ty.fcvList (operands.map S'.apply) :=
        Ty.mem_fcvList_of_mem
          (List.mem_map.mpr ⟨.matcher capability .unit, by simp [operands], rfl⟩)
          scope
      change run.transition.after.forward.cap (localMap.capImage varId) =
        .var varId
      rw [localMap.cap_reverse bundleScope]
    · simp only [Subst.apply_matcher, Subst.apply_unit, capabilityFixed,
        capNormalized, Ty.matcher.injEq, and_true]
      rw [executableCapabilityEq]
      apply Cap.apply_eq_of_fcv_agree
      intro varId membership
      have scope : varId ∈
          (S'.apply (.matcher capability .unit)).fcv := by
        simpa [Subst.apply_matcher, capabilityFixed, Ty.fcv] using membership
      have bundleScope : varId ∈ Ty.fcvList (operands.map S'.apply) :=
        Ty.mem_fcvList_of_mem
          (List.mem_map.mpr ⟨.matcher capability .unit, by simp [operands], rfl⟩)
          scope
      simp only [post, LocalRenamingOn.pureSubst]
      rw [localMap.cap_forward bundleScope]
  have targetEq : run.result.state.prevailing.apply run.result.target =
      (Subst.seq post S').apply target :=
    TyBisimulation.executable_eq_pure_of_mem run.transition.after operands
      (by simp [operands]) run.target
  refine
    { declarativeEvidence := evidence
      declarativeCollected := collected
      declarativeInferred := inferred
      declarativeClauseCaps := clauseCaps
      catchAll := catchAll
      binders := binders
      declarativeArms := arms
      declarativeCoverage := coverage
      executableEvidence := executableEvidence
      executableCapability := executableCapability
      executableCollected := ?_
      executableInferred := movedInferred
      executableClauseCaps := ?_
      executableArms := ?_
      executableCoverage := movedCoverage
      capability := capRelated
      declarativeFixed := capabilityFixed
      executableFixed := capNormalized
      executableCapabilityBounded := ?_ }
  · rw [holesEq]
    exact movedCollected
  · rw [holesEq]
    exact movedClauseCaps
  · rw [targetEq]
    exact movedArms
  · exact executableCapabilityBounded

end DemandTypingInferenceCompletenessMatcherFinalizationCertified
end TypePM
