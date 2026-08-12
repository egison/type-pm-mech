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

/-! ## Completed matcher finalization -/

/-- DD finalization evidence paired with the corresponding executable checks.
The executable half is kept as one proof-relevant package so the outer mutual
recursion does not expose individual Boolean validator obligations. -/
structure MatcherFinalizationCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ClausesResult} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger' : CapabilityOriginLedger}
    {target : Ty} {rawHoleLists : List (List Dual)}
    (run : ClausesRunCompletion before operation q' S' ledger' target
      rawHoleLists)
    (signature : FrozenSig) (clauses : List Clause)
    (declarativeCapability : Cap) : Type where
  declarativeEvidence : List Shape.Evidence
  declarativeCollected : collectClauseEvidence signature.toMatcherSig clauses
    (terminalHoleCaps S' rawHoleLists) = some declarativeEvidence
  declarativeInferred : Shape.inferShape signature.observability
    declarativeEvidence = some declarativeCapability
  declarativeClauseCaps : clauseCapsListCheck signature declarativeCapability
    clauses (terminalHoleCaps S' rawHoleLists) = true
  catchAll : catchAllLastCheck clauses = true
  binders : matcherBindersCheck clauses = true
  declarativeArms : armExhaustiveCheck signature clauses
    (S'.apply target) = true
  declarativeCoverage : coverageCheck signature.toMatcherSig clauses
    declarativeCapability = true
  executableEvidence : List Shape.Evidence
  executableCapability : Cap
  executableCollected : collectClauseEvidence signature.toMatcherSig clauses
    (terminalHoleCaps run.result.state.prevailing
      run.result.rawHoleLists) = some executableEvidence
  executableInferred : Shape.inferShape signature.observability
    executableEvidence = some executableCapability
  executableClauseCaps : clauseCapsListCheck signature executableCapability
    clauses (terminalHoleCaps run.result.state.prevailing
      run.result.rawHoleLists) = true
  executableArms : armExhaustiveCheck signature clauses
    (run.result.state.prevailing.apply run.result.target) = true
  executableCoverage : coverageCheck signature.toMatcherSig clauses
    executableCapability = true
  capability : CapBisimulation run.transition.after declarativeCapability
    executableCapability
  declarativeFixed : declarativeCapability.apply S'.cap =
    declarativeCapability
  executableFixed : executableCapability.apply
    run.result.state.prevailing.cap = executableCapability
  executableCapabilityBounded : executableCapability.BoundedBy q'

/-- Capability and target correspondences combine under a matcher shell. -/
def TyBisimulation.matcher
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeCapability executableCapability : Cap}
    {declarativeTarget executableTarget : Ty}
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (target : TyBisimulation relation declarativeTarget executableTarget) :
    TyBisimulation relation (.matcher declarativeCapability declarativeTarget)
      (.matcher executableCapability executableTarget) := by
  constructor
  · have capEq := (Ty.matcher.inj capability.forward).1
    have targetEq := (Ty.matcher.inj capability.forward).2
    simp only [Subst.apply_matcher]
    rw [capEq]
    exact congrArg (Ty.matcher _) target.forward
  · have capEq := (Ty.matcher.inj capability.reverse).1
    simp only [Subst.apply_matcher]
    rw [capEq]
    exact congrArg (Ty.matcher _) target.reverse

/-- Clause-list traversal preserves its caller-supplied raw target literally. -/
theorem inferClausesFuel_result_target
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {clauses : List Clause} {target : Ty} {state : InferState}
    {result : ClausesResult}
    (success : inferClausesFuel fuel signature context selfEnv parent index
      clauses target state = some result) :
    result.target = target := by
  induction fuel generalizing index clauses state result with
  | zero => simp [inferClausesFuel] at success
  | succ fuel ih =>
      cases clauses with
      | nil =>
          simp [inferClausesFuel] at success
          subst result
          rfl
      | cons clause clauses =>
          simp only [inferClausesFuel] at success
          cases headEq : inferClauseFuel fuel signature context selfEnv
              (index :: parent) clause target state with
          | none => simp [headEq] at success
          | some head =>
              cases tailEq : inferClausesFuel fuel signature context selfEnv
                  parent (index + 1) clauses target head.state with
              | none => simp [headEq, tailEq] at success
              | some tail =>
                  simp only [headEq, tailEq, Option.some.injEq] at success
                  subst result
                  rfl

/-- Complete `inferMatcherFuel` from one reconstructed clause-list traversal
and its paired finalization evidence. -/
def inferMatcherFuel_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clauses : List Clause}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (clausesRun : ClausesRunCompletion
      (before.freshTy (freshOrigin .matcherClause path "matcher-target")).state
      (inferClausesFuel fuel signature context selfEnv path 0 clauses
        (.var q.nextTy)
        (initial.freshTy
          (freshOrigin .matcherClause path "matcher-target")).2)
      q' S' ledger' (.var q.nextTy) rawHoleLists)
    (finalization : MatcherFinalizationCompletion clausesRun signature clauses
      declarativeCapability) :
    SynthRunCompletion before
      (inferMatcherFuel (fuel + 1) signature context selfEnv path clauses initial)
      q' S' (DDLedger.freezeMatcherProducer ledger' declarativeCapability)
      (.matcher declarativeCapability (.var q.nextTy)) := by
  let targetOrigin := freshOrigin .matcherClause path "matcher-target"
  let targetAllocation := before.freshTy targetOrigin
  let coverageEvent := TraceEvent.literalCoverage clauses
    finalization.executableCapability
  let coverageExtension := clausesRun.transition.after.recordEventExtension
    coverageEvent
  let coverageRelation := clausesRun.completion.recordEvent coverageEvent
    (by simp [coverageEvent, TraceEvent.allocatedCapVars])
  let executableTarget := clausesRun.result.state.prevailing.apply
    clausesRun.result.target
  let executableHoleLists := terminalHoleCaps
    clausesRun.result.state.prevailing clausesRun.result.rawHoleLists
  let finalizationEvent := TraceEvent.matcherFinalization
    (clausesRun.result.state.recordEvent coverageEvent).trace.solves.length
    clauses (.var q.nextTy)
    clausesRun.result.rawHoleLists executableTarget executableHoleLists
    finalization.executableEvidence finalization.executableCapability
  let finalizationExtension := coverageExtension.after.recordEventExtension
    finalizationEvent
  let finalizedRelation := coverageRelation.recordEvent finalizationEvent
    (by simp [finalizationEvent, TraceEvent.allocatedCapVars])
  let capabilityAtFinal :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
      finalizationExtension
      (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
        coverageExtension finalization.capability)
  have declarativeFixedAtFinal :
      declarativeCapability.apply S'.cap = declarativeCapability :=
    finalization.declarativeFixed
  have executableFixedAtFinal :
      finalization.executableCapability.apply
        (clausesRun.result.state.recordEvent coverageEvent |>.recordEvent
          finalizationEvent).prevailing.cap =
        finalization.executableCapability := by
    exact finalization.executableFixed
  let protectedRelation :=
    DemandTypingInferenceCompletenessMatcherExprTraversal.TraversalStateCorrespondence.protectMatcherCapabilityRelated
      finalizedRelation capabilityAtFinal declarativeFixedAtFinal
      executableFixedAtFinal
  let protectExtension :=
    DemandTypingInferenceCompletenessMatcherExprTraversal.TraversalStateCorrespondence.protectMatcherCapabilityRelatedExtension
      finalizedRelation capabilityAtFinal declarativeFixedAtFinal
      executableFixedAtFinal
  let rawTargetRelation := TyBisimulation.matcher finalization.capability
    (clausesRun.transition.after.sameTarget (.var q.nextTy))
  let afterCoverage := coverageExtension.transportTy rawTargetRelation
  let afterFinalization := finalizationExtension.transportTy afterCoverage
  let finalTarget := protectExtension.transportTy afterFinalization
  let result : ExprResult :=
    ⟨.matcher finalization.executableCapability (.var q.nextTy),
      (clausesRun.result.state.recordEvent coverageEvent |>.recordEvent
        finalizationEvent).protectMatcherCapability
          finalization.executableCapability⟩
  have clausesTargetEq : clausesRun.result.target = .var q.nextTy :=
    inferClausesFuel_result_target clausesRun.success
  have executableCollected : collectClauseEvidence signature.toMatcherSig clauses
      (clausesRun.result.rawHoleLists.map fun holes =>
        (holes.map
          (Dual.applySubst clausesRun.result.state.prevailing)).map Dual.cap) =
      some finalization.executableEvidence := by
    simpa [terminalHoleCaps] using finalization.executableCollected
  refine
    { result := result
      success := ?_
      supply_eq := protectedRelation.supply_eq
      transition := ((before.freshTyExtension targetOrigin).seq
        clausesRun.transition |>.seq coverageExtension |>.seq
        finalizationExtension).seq protectExtension
      declarative_bounded := protectedRelation.declarative_bounded
      executable_bounded := protectedRelation.executable_bounded
      forward_bounded := protectedRelation.forward_bounded
      reverse_bounded := protectedRelation.reverse_bounded
      ledger_below := protectedRelation.ledger_below
      executable_ledger_below := protectedRelation.executable_ledger_below
      protected_origins := protectedRelation.protected_origins
      protected_below := protectedRelation.protected_below
      allocated_recorded := protectedRelation.allocated_recorded
      target := finalTarget }
  simp only [inferMatcherFuel]
  rw [targetAllocation.target_eq, clausesRun.success]
  simp only
  rw [executableCollected]
  simp only [finalization.executableInferred]
  have executableArms : armExhaustiveCheck signature clauses
      (clausesRun.result.state.prevailing.apply (.var q.nextTy)) = true := by
    simpa only [clausesTargetEq] using finalization.executableArms
  have checks :
      (clauseCapsListCheck signature finalization.executableCapability clauses
          (clausesRun.result.rawHoleLists.map fun holes =>
            (holes.map (Dual.applySubst
              clausesRun.result.state.prevailing)).map Dual.cap) &&
        catchAllLastCheck clauses && matcherBindersCheck clauses &&
        armExhaustiveCheck signature clauses
          (clausesRun.result.state.prevailing.apply (.var q.nextTy)) &&
        coverageCheck signature.toMatcherSig clauses
          finalization.executableCapability) = true := by
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, finalization.catchAll⟩, finalization.binders⟩,
      executableArms⟩, finalization.executableCoverage⟩
    simpa [terminalHoleCaps] using finalization.executableClauseCaps
  rw [if_pos checks]
  apply congrArg some
  change ExprResult.mk _ _ = ExprResult.mk _ _
  congr 1
  simp [coverageEvent, finalizationEvent, executableTarget,
    executableHoleLists, clausesTargetEq, terminalHoleCaps, List.map_map,
    Function.comp_def]

/-! ## Recursive matcher expressions -/

/-- Deterministic completion of the recursive-matcher placeholder allocator.
The executable domain, codomain, and state are not exposed as independent
choices: the success equation pins all three to `buildFixPlaceholder` at the
visited state.  The ledger is exactly the capability-allocation range recorded
by `DDSynthOrigin.fixMatcher`. -/
structure FixMatcherPlaceholderCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (signature : FrozenSig) (path : SyntaxPath) (clauses : List Clause)
    (domain codomain : Ty) (q₀ : InferenceBase.FreshSupply) : Type where
  state : InferState
  success : buildFixPlaceholder signature path (.matcher clauses) initial =
    some (domain, codomain, state)
  supply_eq : state.supply = q₀
  transition : BisimulationExtension before.prevailing
    (DDLedger.markCapRange ledger q q₀) S state
  declarative_bounded : S.BoundedBy q₀
  executable_bounded : state.prevailing.BoundedBy q₀
  forward_bounded : transition.after.forward.BoundedBy q₀
  reverse_bounded : transition.after.reverse.BoundedBy q₀
  ledger_below : DDLedger.LedgerBelow q₀
    (DDLedger.markCapRange ledger q q₀)
  executable_ledger_below :
    DDLedger.LedgerBelow q₀ state.capabilityOrigins
  protected_origins : ProtectedCapOrigins state
  protected_below : ProtectedCapsBelowSupply state
  allocated_recorded : AllocatedCapsRecorded state

/-- Output-only traversal relation of a completed recursive-matcher
placeholder allocation. -/
def FixMatcherPlaceholderCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger initial}
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
    (run : FixMatcherPlaceholderCompletion before signature path clauses
      domain codomain q₀) :
    TraversalStateCorrespondence q₀ S
      (DDLedger.markCapRange ledger q q₀) run.state :=
  ⟨run.supply_eq, run.transition.after,
    run.declarative_bounded, run.executable_bounded,
    run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below,
    run.protected_origins, run.protected_below, run.allocated_recorded⟩

/-- Complete the matcher-bodied recursive-expression branch after the
deterministic placeholder allocation, recursive matcher synthesis, and final
codomain alignment have been reconstructed. -/
def inferExprFuel_fixMatcher_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {self argument : String}
    {clauses : List Clause} {domain codomain bodyTarget : Ty}
    {q q₀ q₁ q' : InferenceBase.FreshSupply}
    {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholderRun : FixMatcherPlaceholderCompletion
      (before.visit .exprFix path) signature path clauses domain codomain q₀)
    (bodyRun :
      let placeholder := Ty.fn domain codomain
      let placeholderEvent := TraceEvent.fixPlaceholder self argument
        placeholder path
      let directEvent := TraceEvent.directSelfAccepted self placeholder path
      let bodyBefore :=
        (placeholderRun.completion.recordEvent placeholderEvent
          (by simp [placeholderEvent, TraceEvent.allocatedCapVars])).recordEvent
          directEvent (by simp [directEvent, TraceEvent.allocatedCapVars])
      SynthRunCompletion bodyBefore
        (inferExprFuel fuel signature
          ((argument, Scheme.mono domain) ::
            (self, Scheme.mono placeholder) :: context)
          ((self, placeholder) :: selfEnv.eraseMany [self, argument])
          (0 :: path) (.matcher clauses)
          ((placeholderRun.state.recordEvent placeholderEvent).recordEvent
            directEvent))
        q₁ S₁ ledger₁ bodyTarget)
    (alignmentRun : StateRunCompletion bodyRun.completion.state
      (alignTypes bodyRun.result.state
        (freshOrigin .recursiveBinder path "fix-result")
        bodyRun.result.target codomain)
      q' S' ledger') :
    SynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.fix self argument (.matcher clauses)) initial)
      q' S' ledger' (.fn domain codomain) := by
  let placeholder := Ty.fn domain codomain
  let expression := Expr.fix self argument (.matcher clauses)
  let placeholderEvent := TraceEvent.fixPlaceholder self argument
    placeholder path
  let directEvent := TraceEvent.directSelfAccepted self placeholder path
  let placeholderEventExtension :=
    placeholderRun.transition.after.recordEventExtension placeholderEvent
  let directEventExtension :=
    placeholderEventExtension.after.recordEventExtension directEvent
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.StateRunCompletion.finishExpr
      alignmentRun expression path placeholder placeholder
      (alignmentRun.transition.after.sameTarget placeholder)
  let prefixTransition :=
    ((((((before.visitExtension .exprFix path).seq
      placeholderRun.transition).seq placeholderEventExtension).seq
      directEventExtension).seq bodyRun.transition).seq
      alignmentRun.transition)
  let finishExtension :=
    alignmentRun.transition.after.recordEventExtension
      (.inferredExpr expression placeholder path)
  refine { finished with
    transition := prefixTransition.seq finishExtension
    success := ?_ }
  simp only [inferExprFuel]
  have gate : (self != argument &&
      DirectSelf.check self (.matcher clauses)) = true :=
    (DirectSelf.fix_gate_eq_true self argument (.matcher clauses)).2
      ⟨distinct, direct⟩
  rw [gate]
  simp only [if_true]
  let continuePlaceholder : Option (Ty × Ty × InferState) →
      Option ExprResult := fun candidate =>
    match candidate with
    | none => none
    | some (executableDomain, executableCodomain, state) =>
        let executablePlaceholder := Ty.fn executableDomain executableCodomain
        let state := (state.recordEvent
          (.fixPlaceholder self argument executablePlaceholder path)).recordEvent
          (.directSelfAccepted self executablePlaceholder path)
        let insideContext :=
          (argument, Scheme.mono executableDomain) ::
            (self, Scheme.mono executablePlaceholder) :: context
        let insideSelf :=
          (self, executablePlaceholder) :: selfEnv.eraseMany [self, argument]
        match inferExprFuel fuel signature insideContext insideSelf
            (0 :: path) (.matcher clauses) state with
        | none => none
        | some bodyResult =>
            match alignTypes bodyResult.state
                (freshOrigin .recursiveBinder path "fix-result")
                bodyResult.target executableCodomain with
            | none => none
            | some state => some (Inference.finishExpr expression path
                executablePlaceholder state)
  change continuePlaceholder
      (buildFixPlaceholder signature path (.matcher clauses)
        (visit initial .exprFix path)) = some finished.result
  calc
    _ = continuePlaceholder (some (domain, codomain,
          placeholderRun.state)) :=
      congrArg continuePlaceholder placeholderRun.success
    _ = (match inferExprFuel fuel signature
          ((argument, Scheme.mono domain) ::
            (self, Scheme.mono placeholder) :: context)
          ((self, placeholder) :: selfEnv.eraseMany [self, argument])
          (0 :: path) (.matcher clauses)
          ((placeholderRun.state.recordEvent placeholderEvent).recordEvent
            directEvent) with
        | none => none
        | some bodyResult =>
            match alignTypes bodyResult.state
                (freshOrigin .recursiveBinder path "fix-result")
                bodyResult.target codomain with
            | none => none
            | some state => some (Inference.finishExpr expression path
                placeholder state)) := rfl
    _ = (match alignTypes bodyRun.result.state
          (freshOrigin .recursiveBinder path "fix-result")
          bodyRun.result.target codomain with
        | none => none
        | some state => some (Inference.finishExpr expression path
            placeholder state)) := by
      let continueBody : Option ExprResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some bodyResult =>
            match alignTypes bodyResult.state
                (freshOrigin .recursiveBinder path "fix-result")
                bodyResult.target codomain with
            | none => none
            | some state => some (Inference.finishExpr expression path
                placeholder state)
      exact congrArg continueBody bodyRun.success
    _ = some (Inference.finishExpr expression path placeholder
          alignmentRun.result) := by
      let continueAlignment : Option InferState → Option ExprResult :=
        fun candidate =>
          match candidate with
          | none => none
          | some state => some (Inference.finishExpr expression path
              placeholder state)
      exact congrArg continueAlignment alignmentRun.success
    _ = some finished.result := rfl

end DemandTypingInferenceCompletenessMatcherExprTraversal
end TypePM
