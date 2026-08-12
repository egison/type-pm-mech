import TypePM.DemandTypingInferenceCompletenessMatcherTraversal

/-!
# Matcher-literal expression completeness

This module sits above clause traversal to avoid an import cycle between the
generic expression and matcher traversal modules.  It first establishes the
heterogeneous selective-freezing bridge needed when DD and executable MGUs
choose different capability representatives.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherExprTraversal

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessProtected

private theorem structural_origin_mem_keys
    {ledger : CapabilityOriginLedger} {varId : CapVar}
    (origin : ledger.originOf varId = .structuralFlexible) :
    varId ∈ ledger.map Prod.fst := by
  induction ledger with
  | nil => simp [CapabilityOriginLedger.originOf] at origin
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateOrigin⟩
      by_cases same : candidate = varId
      · subst candidate
        simp
      · simp only [CapabilityOriginLedger.originOf, same, if_false] at origin
        simp [ih origin]

/-- Selected executable matcher-producer representatives map to selected DD
representatives under a mutually factoring solved state. -/
theorem StateBisimulation.forwardMatcherProducerLeavesOfRelated
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {declarativeCapability executableCapability : Cap}
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (declarativeFixed : declarativeCapability.apply declarative.cap =
      declarativeCapability)
    (executableFixed : executableCapability.apply state.prevailing.cap =
      executableCapability) :
    ∀ varId,
      varId ∈ DDLedger.matcherProducerLeaves state.capabilityOrigins
        executableCapability →
      ∃ image, relation.forward.cap varId = .var image ∧
        image ∈ DDLedger.matcherProducerLeaves ledger
          declarativeCapability := by
  classical
  intro varId membership
  have executableMember :=
    DDLedger.matcherProducerLeaves_recorded state.capabilityOrigins
      executableCapability varId membership
  have executableStructural :=
    DDLedger.matcherProducerLeaves_origin state.capabilityOrigins
      executableCapability varId membership
  have normalizedMember : varId ∈
      (state.prevailing.apply (.matcher executableCapability .unit)).fcv := by
    simpa [Subst.apply_matcher, executableFixed, Ty.fcv] using
      executableMember.1
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn_image
      relation (.matcher executableCapability .unit)
  let image := localMap.capImage varId
  have forwardImage : relation.forward.cap varId = .var image :=
    localMap.cap_forward normalizedMember
  have reverseImage : relation.reverse.cap image = .var varId :=
    localMap.cap_reverse normalizedMember
  have declarativeMember : image ∈ declarativeCapability.fcv := by
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
        localMap
        (state.prevailing.apply (.matcher executableCapability .unit))
        (fun _ member => member) (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv
        localMap
        (state.prevailing.apply (.matcher executableCapability .unit))
    have normalizedDeclarative : image ∈
        (declarative.apply (.matcher declarativeCapability .unit)).fcv := by
      rw [capability.forward, pure, freeVars]
      exact List.mem_map.mpr ⟨varId, normalizedMember, rfl⟩
    simpa [Subst.apply_matcher, declarativeFixed, Ty.fcv] using
      normalizedDeclarative
  have declarativeStructural : ledger.originOf image =
      .structuralFlexible := by
    cases destinationOrigin : ledger.originOf image with
    | structuralFlexible => rfl
    | rigid =>
        have reverseAt := relation.ledgerBisimulation.reverseBetween.cap image
        simp only [destinationOrigin] at reverseAt
        have equal : image = varId := by
          rw [reverseImage] at reverseAt
          exact Cap.var.inj reverseAt.1.symm
        have rigidSource := reverseAt.2
        rw [equal, executableStructural] at rigidSource
        contradiction
    | renameOnly =>
        have reverseAt := relation.ledgerBisimulation.reverseBetween.cap image
        simp only [destinationOrigin] at reverseAt
        rcases reverseAt with ⟨actualImage, equation, safe⟩
        rw [reverseImage] at equation
        have equal : actualImage = varId := (Cap.var.inj equation).symm
        subst actualImage
        exact False.elim (safe executableStructural)
  refine ⟨image, forwardImage, ?_⟩
  unfold DDLedger.matcherProducerLeaves Inference.matcherProducerLedgerLeaves
  simp only [List.mem_filter, List.mem_eraseDups]
  exact ⟨⟨declarativeMember, decide_eq_true
    (structural_origin_mem_keys declarativeStructural)⟩,
    decide_eq_true declarativeStructural⟩

/-- Reverse counterpart of `forwardMatcherProducerLeavesOfRelated`. -/
theorem StateBisimulation.reverseMatcherProducerLeavesOfRelated
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {declarativeCapability executableCapability : Cap}
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (declarativeFixed : declarativeCapability.apply declarative.cap =
      declarativeCapability)
    (executableFixed : executableCapability.apply state.prevailing.cap =
      executableCapability) :
    ∀ varId,
      varId ∈ DDLedger.matcherProducerLeaves ledger declarativeCapability →
      ∃ image, relation.reverse.cap varId = .var image ∧
        image ∈ DDLedger.matcherProducerLeaves state.capabilityOrigins
          executableCapability := by
  classical
  intro varId membership
  have declarativeMember := DDLedger.matcherProducerLeaves_recorded ledger
    declarativeCapability varId membership
  have declarativeStructural := DDLedger.matcherProducerLeaves_origin ledger
    declarativeCapability varId membership
  have normalizedMember : varId ∈
      (declarative.apply (.matcher declarativeCapability .unit)).fcv := by
    simpa [Subst.apply_matcher, declarativeFixed, Ty.fcv] using
      declarativeMember.1
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
      relation (.matcher declarativeCapability .unit)
  let image := localMap.capImage varId
  have reverseImage : relation.reverse.cap varId = .var image :=
    localMap.cap_forward normalizedMember
  have forwardImage : relation.forward.cap image = .var varId :=
    localMap.cap_reverse normalizedMember
  have executableMember : image ∈ executableCapability.fcv := by
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
        localMap
        (declarative.apply (.matcher declarativeCapability .unit))
        (fun _ member => member) (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv
        localMap
        (declarative.apply (.matcher declarativeCapability .unit))
    have normalizedExecutable : image ∈
        (state.prevailing.apply (.matcher executableCapability .unit)).fcv := by
      rw [capability.reverse, pure, freeVars]
      exact List.mem_map.mpr ⟨varId, normalizedMember, rfl⟩
    simpa [Subst.apply_matcher, executableFixed, Ty.fcv] using
      normalizedExecutable
  have executableStructural : state.capabilityOrigins.originOf image =
      .structuralFlexible := by
    cases destinationOrigin : state.capabilityOrigins.originOf image with
    | structuralFlexible => rfl
    | rigid =>
        have forwardAt := relation.ledgerBisimulation.forwardBetween.cap image
        simp only [destinationOrigin] at forwardAt
        have equal : image = varId := by
          rw [forwardImage] at forwardAt
          exact Cap.var.inj forwardAt.1.symm
        have rigidSource := forwardAt.2
        rw [equal, declarativeStructural] at rigidSource
        contradiction
    | renameOnly =>
        have forwardAt := relation.ledgerBisimulation.forwardBetween.cap image
        simp only [destinationOrigin] at forwardAt
        rcases forwardAt with ⟨declarativeImage, equation, safe⟩
        rw [forwardImage] at equation
        have equal : declarativeImage = varId := (Cap.var.inj equation).symm
        subst declarativeImage
        exact False.elim (safe declarativeStructural)
  refine ⟨image, reverseImage, ?_⟩
  unfold DDLedger.matcherProducerLeaves Inference.matcherProducerLedgerLeaves
  simp only [List.mem_filter, List.mem_eraseDups]
  exact ⟨⟨executableMember, decide_eq_true
    (structural_origin_mem_keys executableStructural)⟩,
    decide_eq_true executableStructural⟩

/-- Freeze related DD/executable matcher capabilities and retain the complete
traversal correspondence. -/
def TraversalStateCorrespondence.protectMatcherCapabilityRelated
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    {declarativeCapability executableCapability : Cap}
    (capability : CapBisimulation relation.prevailing declarativeCapability
      executableCapability)
    (declarativeFixed : declarativeCapability.apply declarative.cap =
      declarativeCapability)
    (executableFixed : executableCapability.apply state.prevailing.cap =
      executableCapability) :
    TraversalStateCorrespondence q declarative
      (DDLedger.freezeMatcherProducer ledger declarativeCapability)
      (state.protectMatcherCapability executableCapability) := by
  let afterLedger := DDLedger.freezeMatcherProducer ledger
    declarativeCapability
  let afterState := state.protectMatcherCapability executableCapability
  have ledgerTransport : LedgerBisimulation afterLedger
      afterState.capabilityOrigins relation.prevailing.forward
      relation.prevailing.reverse := by
    constructor
    · unfold afterLedger DDLedger.freezeMatcherProducer
      rw [show afterState.capabilityOrigins =
        state.capabilityOrigins.setOrigins
          (DDLedger.matcherProducerLeaves state.capabilityOrigins
            executableCapability) .renameOnly by rfl]
      constructor
      exact relation.prevailing.ledgerBisimulation.forwardBetween.cap.freezeSelected
        (fun varId membership => DDLedger.matcherProducerLeaves_origin ledger
          declarativeCapability varId membership)
        (StateBisimulation.forwardMatcherProducerLeavesOfRelated
          relation.prevailing capability declarativeFixed executableFixed)
    · unfold afterLedger DDLedger.freezeMatcherProducer
      rw [show afterState.capabilityOrigins =
        state.capabilityOrigins.setOrigins
          (DDLedger.matcherProducerLeaves state.capabilityOrigins
            executableCapability) .renameOnly by rfl]
      constructor
      exact relation.prevailing.ledgerBisimulation.reverseBetween.cap.freezeSelected
        (fun varId membership =>
          DDLedger.matcherProducerLeaves_origin state.capabilityOrigins
            executableCapability varId membership)
        (StateBisimulation.reverseMatcherProducerLeavesOfRelated
          relation.prevailing capability declarativeFixed executableFixed)
  let after : StateBisimulation afterLedger declarative afterState :=
    { forward := relation.prevailing.forward
      forwardEquation := by simpa [afterState] using
        relation.prevailing.forwardEquation
      declarativeIdempotent := relation.prevailing.declarativeIdempotent
      reverse := relation.prevailing.reverse
      reverseEquation := by simpa [afterState] using
        relation.prevailing.reverseEquation
      ledgerBisimulation := ledgerTransport
      executableIdempotent := by
        change state.prevailing.Idempotent
        exact relation.prevailing.executableIdempotent }
  exact
    { supply_eq := by simpa [afterState] using relation.supply_eq
      prevailing := after
      declarative_bounded := relation.declarative_bounded
      executable_bounded := by simpa [afterState] using
        relation.executable_bounded
      forward_bounded := relation.forward_bounded
      reverse_bounded := relation.reverse_bounded
      ledger_below := DDLedger.LedgerBelow.freezeMatcherProducer
        declarativeCapability relation.ledger_below
      executable_ledger_below := by
        simpa [afterState, DDLedger.freezeMatcherProducer,
          DDLedger.matcherProducerLeaves] using
          DDLedger.LedgerBelow.freezeMatcherProducer executableCapability
            relation.executable_ledger_below
      protected_origins := relation.protected_origins.protectMatcherCapability
        executableCapability
      protected_below := relation.protected_below.protectMatcherCapability
        (allocatedCapsBelowSupply_of_recorded relation.allocated_recorded (by
          rw [relation.supply_eq]
          exact relation.executable_ledger_below)) executableCapability
      allocated_recorded :=
        relation.allocated_recorded.protectMatcherCapability
          executableCapability }

def TraversalStateCorrespondence.protectMatcherCapabilityRelatedExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    {declarativeCapability executableCapability : Cap}
    (capability : CapBisimulation relation.prevailing declarativeCapability
      executableCapability)
    (declarativeFixed : declarativeCapability.apply declarative.cap =
      declarativeCapability)
    (executableFixed : executableCapability.apply state.prevailing.cap =
      executableCapability) :
    BisimulationExtension relation.prevailing
      (DDLedger.freezeMatcherProducer ledger declarativeCapability)
      declarative (state.protectMatcherCapability executableCapability) where
  after :=
    (DemandTypingInferenceCompletenessMatcherExprTraversal.TraversalStateCorrespondence.protectMatcherCapabilityRelated
      relation capability declarativeFixed executableFixed).prevailing
  transportTy := by
    intro declarativeTarget executableTarget related
    exact ⟨by
      change declarative.apply declarativeTarget =
        relation.prevailing.forward.apply
          (state.prevailing.apply executableTarget)
      exact related.forward,
      by
        change state.prevailing.apply executableTarget =
          relation.prevailing.reverse.apply
            (declarative.apply declarativeTarget)
        exact related.reverse⟩

end DemandTypingInferenceCompletenessMatcherExprTraversal
end TypePM
