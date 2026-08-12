import TypePM.DemandTypingInferenceCompletenessMatcherExprTraversal
import TypePM.DemandTypingInferenceCompletenessPatternCtorCapability
import TypePM.DemandTypingInferenceCompletenessCertifiedRun

/-! # Recursive-matcher placeholder completeness -/

namespace TypePM
namespace DemandTypingInferenceCompletenessFixMatcher

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessPatternCtorCapability
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessMatcherExprTraversal

private theorem setOrigins_append (ledger : CapabilityOriginLedger)
    (left right : List CapVar) (origin : CapabilityOrigin) :
    ledger.setOrigins (left ++ right) origin =
      (ledger.setOrigins right origin).setOrigins left origin := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, CapabilityOriginLedger.setOrigins]
      rw [induction]

/-- Consecutive pure fresh-capability ranges compose in executable stack
order. -/
private theorem markCapRange_trans
    (ledger : CapabilityOriginLedger)
    (q middle final : InferenceBase.FreshSupply)
    (front : SupplyExtends q middle) (back : SupplyExtends middle final) :
    DDLedger.markCapRange (DDLedger.markCapRange ledger q middle)
        middle final =
      DDLedger.markCapRange ledger q final := by
  rcases front with ⟨frontCap, frontTy⟩
  rcases back with ⟨backCap, backTy⟩
  unfold DDLedger.markCapRange
  dsimp only
  let frontCount := middle.nextCap - q.nextCap
  let backCount := final.nextCap - middle.nextCap
  have middleEq : q.nextCap + frontCount = middle.nextCap := by
    dsimp [frontCount]
    omega
  have totalEq : final.nextCap - q.nextCap = frontCount + backCount := by
    dsimp [frontCount, backCount]
    omega
  rw [totalEq, List.range_add, List.map_append, List.reverse_append,
    setOrigins_append]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro offset membership
  simp only [Function.comp_apply]
  congr 1
  omega

private theorem freshenSkeletonMasked_supplyExtends
    {observable : Shape.Observability} {origin : ConstraintOrigin} :
    ∀ {mask : List Bool} {evidences : List Shape.Evidence}
      {state final : InferState} {capabilities : List Cap},
      Inference.freshenSkeletonMasked observable origin mask evidences state =
        some (capabilities, final) →
      SupplyExtends state.supply final.supply := by
  intro mask
  induction mask with
  | nil =>
      intro evidences state final capabilities success
      cases evidences with
      | nil =>
          simp only [Inference.freshenSkeletonMasked, Option.some.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact SupplyExtends.refl _
      | cons _ _ => simp [Inference.freshenSkeletonMasked] at success
  | cons observableHead mask induction =>
      intro evidences state final capabilities success
      cases evidences with
      | nil => simp [Inference.freshenSkeletonMasked] at success
      | cons evidence rest =>
          cases observableHead with
          | false =>
              simp only [Inference.freshenSkeletonMasked] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, result⟩
              have resultEq : result = final :=
                (Prod.mk.inj (Option.some.inj finished)).2
              subst final
              exact induction tailSuccess
          | true =>
              simp only [Inference.freshenSkeletonMasked, ↓reduceIte] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨headPair, headSuccess, remaining⟩
              rcases headPair with ⟨head, middle⟩
              rcases Option.bind_eq_some_iff.mp remaining with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, result⟩
              have resultEq : result = final :=
                (Prod.mk.inj (Option.some.inj finished)).2
              subst final
              let headExtension := freshenSkeleton_stateExtension headSuccess
              exact SupplyExtends.trans
                ⟨headExtension.supplyCap, headExtension.supplyTy⟩
                (induction tailSuccess)

/-! ## Solve-free skeleton traversal -/

mutual

/-- Skeleton freshening preserves the complete DD/executable traversal
correspondence, including its exact structural capability range. -/
theorem TraversalStateCorrespondence.freshenSkeleton
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state final : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidence : Shape.Evidence} {capability : Cap}
    (success : Inference.freshenSkeleton observable origin evidence state =
      some (capability, final)) :
    Nonempty (TraversalStateCorrespondence final.supply S
      (DDLedger.markCapRange ledger q final.supply) final) := by
  cases evidence with
  | unseen =>
      simp only [Inference.freshenSkeleton, Option.some.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ⟨by
        simpa [DDLedger.markCapRange, DDLedger.markFreshCap,
          CapabilityOriginLedger.markStructuralFlexible,
          CapabilityOriginLedger.setOrigins,
          before.supply_eq, InferState.freshCap,
          InferenceBase.freshCapMeta, InferState.recordEvent] using
          DemandTypingInferenceCompletenessPatternCtorCapability.TraversalStateCorrespondence.freshCap
            before origin⟩
  | known leaf =>
      simp only [Inference.freshenSkeleton, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ⟨by
        simpa [DDLedger.markCapRange, CapabilityOriginLedger.setOrigins,
          before.supply_eq] using before⟩
  | con name children =>
      simp only [Inference.freshenSkeleton] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨mask, _, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨pair, maskedSuccess, finished⟩
      rcases pair with ⟨capabilities, result⟩
      have resultEq : result = final :=
        (Prod.mk.inj (Option.some.inj finished)).2
      subst final
      exact
        DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeletonMasked
          before maskedSuccess
  | prod components =>
      simp only [Inference.freshenSkeleton] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨pair, listedSuccess, finished⟩
      rcases pair with ⟨capabilities, result⟩
      have resultEq : result = final :=
        (Prod.mk.inj (Option.some.inj finished)).2
      subst final
      exact
        DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeletonList
          before listedSuccess

/-- Left-to-right skeleton-list freshening composes adjacent structural
capability ranges. -/
theorem TraversalStateCorrespondence.freshenSkeletonList
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state final : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidences : List Shape.Evidence} {capabilities : List Cap}
    (success : Inference.freshenSkeletonList observable origin evidences state =
      some (capabilities, final)) :
    Nonempty (TraversalStateCorrespondence final.supply S
      (DDLedger.markCapRange ledger q final.supply) final) := by
  cases evidences with
  | nil =>
      simp only [Inference.freshenSkeletonList, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact ⟨by
        simpa [DDLedger.markCapRange, CapabilityOriginLedger.setOrigins,
          before.supply_eq] using before⟩
  | cons evidence rest =>
      simp only [Inference.freshenSkeletonList] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPair, headSuccess, remaining⟩
      rcases headPair with ⟨head, middle⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨tailPair, tailSuccess, finished⟩
      rcases tailPair with ⟨tail, result⟩
      have resultEq : result = final :=
        (Prod.mk.inj (Option.some.inj finished)).2
      subst final
      let headRun := Classical.choice
        (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
          before headSuccess)
      let tailRun := Classical.choice
        (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeletonList
          headRun tailSuccess)
      have front : SupplyExtends q middle.supply := by
        have pure := (freshenSkeleton_supplyExact headSuccess).1
        simpa [before.supply_eq] using SupplyExtends.freshenSkeleton pure
      have back : SupplyExtends middle.supply result.supply := by
        have wrapped : Inference.freshenSkeleton observable origin (.prod rest)
            middle = some (.prod tail, result) := by
          simp [Inference.freshenSkeleton, tailSuccess]
        let extension := freshenSkeleton_stateExtension wrapped
        exact ⟨extension.supplyCap, extension.supplyTy⟩
      exact ⟨by
        simpa [markCapRange_trans ledger q middle.supply result.supply
          front back] using tailRun⟩

/-- Masked skeleton freshening skips unobservable fields without changing the
range-composition argument. -/
theorem TraversalStateCorrespondence.freshenSkeletonMasked
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state final : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {mask : List Bool} {evidences : List Shape.Evidence}
    {capabilities : List Cap}
    (success : Inference.freshenSkeletonMasked observable origin mask evidences
      state = some (capabilities, final)) :
    Nonempty (TraversalStateCorrespondence final.supply S
      (DDLedger.markCapRange ledger q final.supply) final) := by
  cases mask with
  | nil =>
      cases evidences with
      | nil =>
          simp only [Inference.freshenSkeletonMasked, Option.some.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact ⟨by
            simpa [DDLedger.markCapRange,
              CapabilityOriginLedger.setOrigins, before.supply_eq] using before⟩
      | cons _ _ => simp [Inference.freshenSkeletonMasked] at success
  | cons observableHead mask =>
      cases evidences with
      | nil => simp [Inference.freshenSkeletonMasked] at success
      | cons evidence rest =>
          cases observableHead with
          | false =>
              simp only [Inference.freshenSkeletonMasked] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, result⟩
              have resultEq : result = final :=
                (Prod.mk.inj (Option.some.inj finished)).2
              subst final
              exact
                DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeletonMasked
                  before tailSuccess
          | true =>
              simp only [Inference.freshenSkeletonMasked, ↓reduceIte] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨headPair, headSuccess, remaining⟩
              rcases headPair with ⟨head, middle⟩
              rcases Option.bind_eq_some_iff.mp remaining with
                ⟨tailPair, tailSuccess, finished⟩
              rcases tailPair with ⟨tail, result⟩
              have resultEq : result = final :=
                (Prod.mk.inj (Option.some.inj finished)).2
              subst final
              let headRun := Classical.choice
                (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
                  before headSuccess)
              let tailRun := Classical.choice
                (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeletonMasked
                  headRun tailSuccess)
              have front : SupplyExtends q middle.supply := by
                have pure := (freshenSkeleton_supplyExact headSuccess).1
                simpa [before.supply_eq] using
                  SupplyExtends.freshenSkeleton pure
              have back : SupplyExtends middle.supply result.supply := by
                exact freshenSkeletonMasked_supplyExtends tailSuccess
              exact ⟨by
                simpa [markCapRange_trans ledger q middle.supply result.supply
                  front back] using tailRun⟩

end

/-- The executable recursive-matcher placeholder exists whenever its pure
supply twin succeeds.  The already-proved forward correspondence then pins
the terminal supply exactly. -/
theorem buildFixPlaceholder_complete_of_supply
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {initial : InferState} {domain codomain : Ty}
    {q₀ : InferenceBase.FreshSupply}
    (pure : fixMatcherPlaceholderSupply signature clauses initial.supply =
      some (domain, codomain, q₀)) :
    ∃ final, buildFixPlaceholder signature path (.matcher clauses) initial =
        some (domain, codomain, final) ∧ final.supply = q₀ := by
  unfold fixMatcherPlaceholderSupply at pure
  cases evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses with
  | none => simp [evidenceEq] at pure
  | some evidence =>
      cases evidence with
      | unseen =>
          simp [evidenceEq, Cap.fcv] at pure
          rcases pure with ⟨rfl, rfl, rfl⟩
          let capState := (initial.freshCap
            (freshOrigin .recursiveBinder path
              "fix-argument-capability")).2
          let targetState := (capState.freshTy
            (freshOrigin .recursiveBinder path "fix-argument-target")).2
          let final := (targetState.freshTy
            (freshOrigin .recursiveBinder path "fix-producer-target")).2
          refine ⟨final, ?_, ?_⟩
          · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
              Cap.fcv, capState, targetState, final, InferState.freshCap,
              InferState.freshTy, InferenceBase.freshCapMeta,
              InferenceBase.freshTyMeta]
          · simp [capState, targetState, final, InferState.freshCap,
              InferState.freshTy, InferenceBase.freshCapMeta,
              InferenceBase.freshTyMeta]
      | known leaf =>
          exact completeFresh evidenceEq (by simp) pure
      | con name children =>
          exact completeFresh evidenceEq (by simp) pure
      | prod components =>
          exact completeFresh evidenceEq (by simp) pure
where
  completeFresh
      {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
      {initial : InferState} {evidence : Shape.Evidence}
      {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
      (evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses =
        some evidence)
      (notUnseen : evidence ≠ .unseen)
      (pure : fixMatcherPlaceholderSupply signature clauses initial.supply =
        some (domain, codomain, q₀)) :
      ∃ final, buildFixPlaceholder signature path (.matcher clauses) initial =
          some (domain, codomain, final) ∧ final.supply = q₀ := by
    cases freshEq : freshenSkeletonSupply signature.observability evidence
        initial.supply with
    | none =>
        unfold fixMatcherPlaceholderSupply at pure
        simp [evidenceEq, freshEq] at pure
    | some pair =>
        rcases pair with ⟨capability, q₁⟩
        rcases freshenSkeleton_complete_exact
            (origin := freshOrigin .recursiveBinder path
              "fix-producer-shape") freshEq with
          ⟨middle, executableFresh, supplyEq, _, _⟩
        have pureTail := pure
        unfold fixMatcherPlaceholderSupply at pureTail
        simp [evidenceEq, freshEq] at pureTail
        generalize fcvEq : capability.fcv = variables at pureTail
        cases variables with
        | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq] at pureTail
            rcases pureTail with ⟨rfl, rfl, rfl⟩
            let capState := (middle.freshCap
              (freshOrigin .recursiveBinder path
                "fix-argument-capability")).2
            let targetState := (capState.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
            let final := (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
            refine ⟨final, ?_, ?_⟩
            · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
                executableFresh, fcvEq, capState, targetState, final,
                InferState.freshCap, InferState.freshTy,
                InferenceBase.freshCapMeta, InferenceBase.freshTyMeta,
                supplyEq]
            · rw [← supplyEq]
              simp [capState, targetState, final, InferState.freshCap,
                InferState.freshTy, InferenceBase.freshCapMeta,
                InferenceBase.freshTyMeta]

        | cons first rest =>
            simp only [Option.some.injEq, Prod.mk.injEq] at pureTail
            rcases pureTail with ⟨rfl, rfl, rfl⟩
            let targetState := (middle.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
            let final := (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
            refine ⟨final, ?_, ?_⟩
            · simp [buildFixPlaceholder, recursiveMatcherTemplate, evidenceEq,
                executableFresh, fcvEq, targetState, final,
                InferState.freshTy, InferenceBase.freshTyMeta, supplyEq]
            · rw [← supplyEq]
              simp [targetState, final, InferState.freshTy,
                InferenceBase.freshTyMeta]

/-- Placeholder allocation emits only ordinary allocation events. -/
theorem ValidatorRunExtension.ofBuildFixPlaceholderMatcher
    {terminal : Subst} {signature : FrozenSig} {path : SyntaxPath}
    {clauses : List Clause} {initial final : InferState}
    {domain codomain : Ty}
    (success : buildFixPlaceholder signature path (.matcher clauses) initial =
      some (domain, codomain, final)) :
    ValidatorRunExtension terminal signature initial final := by
  unfold buildFixPlaceholder at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨pair, recursiveSuccess, rest⟩
  rcases pair with ⟨capability, middle⟩
  unfold recursiveMatcherTemplate at recursiveSuccess
  rcases Option.bind_eq_some_iff.mp recursiveSuccess with
    ⟨evidence, _, freshSuccess⟩
  have recursiveRun : ValidatorRunExtension terminal signature initial middle := by
    cases evidence with
    | unseen =>
        simp only at freshSuccess
        rcases freshSuccess with ⟨rfl, rfl⟩
        exact ValidatorRunExtension.refl terminal signature initial
    | known leaf => exact ValidatorRunExtension.ofFreshenSkeleton freshSuccess
    | con name children => exact ValidatorRunExtension.ofFreshenSkeleton freshSuccess
    | prod components => exact ValidatorRunExtension.ofFreshenSkeleton freshSuccess
  generalize fcvEq : capability.fcv = variables at rest
  cases variables with
  | nil =>
      simp only at rest
      rcases rest with ⟨rfl, rfl, rfl⟩
      let capOrigin := freshOrigin .recursiveBinder path
        "fix-argument-capability"
      let targetOrigin := freshOrigin .recursiveBinder path
        "fix-argument-target"
      let producerOrigin := freshOrigin .recursiveBinder path
        "fix-producer-target"
      let capState := (middle.freshCap
        capOrigin).2
      let targetState := (capState.freshTy targetOrigin).2
      simpa [fcvEq, capOrigin, targetOrigin, producerOrigin, capState, targetState] using
        recursiveRun.trans
        ((ValidatorRunExtension.freshCap terminal signature middle capOrigin).trans
          ((ValidatorRunExtension.freshTy terminal signature capState
            targetOrigin).trans
            (ValidatorRunExtension.freshTy terminal signature targetState
              producerOrigin)))
  | cons first tail =>
      simp only at rest
      rcases rest with ⟨rfl, rfl, rfl⟩
      let targetOrigin := freshOrigin .recursiveBinder path
        "fix-argument-target"
      let producerOrigin := freshOrigin .recursiveBinder path
        "fix-producer-target"
      let targetState := (middle.freshTy targetOrigin).2
      simpa [fcvEq, targetOrigin, producerOrigin, targetState] using
        recursiveRun.trans
        ((ValidatorRunExtension.freshTy terminal signature middle
          targetOrigin).trans
          (ValidatorRunExtension.freshTy terminal signature targetState
            producerOrigin))

/-- A solve-free structural allocation range keeps the existing residuals
and extends only the two origin ledgers. -/
def TraversalStateCorrespondence.markCapRangeExtension
    {q q' : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial final : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (supplyExtension : SupplyExtends q q')
    (supplyEq : final.supply = q')
    (prevailingEq : final.prevailing = initial.prevailing)
    (ledgerEq : final.capabilityOrigins =
      DDLedger.markCapRange initial.capabilityOrigins q q') :
    BisimulationExtension before.prevailing
      (DDLedger.markCapRange ledger q q') S final := by
  let _ := supplyExtension
  let _ := supplyEq
  let fresh : List CapVar :=
    ((List.range (q'.nextCap - q.nextCap)).map fun offset =>
    ⟨q.nextCap + offset⟩).reverse
  have freshAbove : ∀ varId, varId ∈ fresh → q.nextCap ≤ varId.id := by
    intro varId membership
    simp only [fresh, List.mem_reverse, List.mem_map] at membership
    rcases membership with ⟨offset, _, rfl⟩
    exact Nat.le_add_right _ _
  have forwardBetween : AdmissiblePostBetween final.capabilityOrigins
      (DDLedger.markCapRange ledger q q') before.prevailing.forward := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.forwardBetween
      before.forward_bounded before.executable_ledger_below freshAbove
    simpa [DDLedger.markCapRange, fresh, ledgerEq] using extended
  have reverseBetween : AdmissiblePostBetween
      (DDLedger.markCapRange ledger q q') final.capabilityOrigins
      before.prevailing.reverse := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.reverseBetween
      before.reverse_bounded before.ledger_below freshAbove
    simpa [DDLedger.markCapRange, fresh, ledgerEq] using extended
  refine
    { after :=
        { forward := before.prevailing.forward
          forwardEquation := by
            simpa [prevailingEq] using before.prevailing.forwardEquation
          declarativeIdempotent := before.prevailing.declarativeIdempotent
          reverse := before.prevailing.reverse
          reverseEquation := by
            simpa [prevailingEq] using before.prevailing.reverseEquation
          ledgerBisimulation := ⟨forwardBetween, reverseBetween⟩
          executableIdempotent := by
            simpa [prevailingEq] using before.prevailing.executableIdempotent }
      transportTy := ?_
      transportScheme := ?_ }
  · intro declarativeTarget executableTarget related
    exact ⟨by simpa [prevailingEq] using related.forward,
      by simpa [prevailingEq] using related.reverse⟩
  · intro _ _ forward reverse
    exact ⟨by simpa [prevailingEq] using forward,
      by simpa [prevailingEq] using reverse⟩

/-- The matcher placeholder allocator preserves the entire traversal
correspondence at the pure range ledger. -/
theorem buildFixPlaceholder_correspondence
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial final : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    {domain codomain : Ty}
    (success : buildFixPlaceholder signature path (.matcher clauses) initial =
      some (domain, codomain, final)) :
    Nonempty (TraversalStateCorrespondence final.supply S
      (DDLedger.markCapRange ledger q final.supply) final) := by
  unfold buildFixPlaceholder at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨pair, recursiveSuccess, rest⟩
  rcases pair with ⟨capability, middle⟩
  unfold recursiveMatcherTemplate at recursiveSuccess
  rcases Option.bind_eq_some_iff.mp recursiveSuccess with
    ⟨evidence, _, freshSuccess⟩
  let middleRun : TraversalStateCorrespondence middle.supply S
      (DDLedger.markCapRange ledger q middle.supply) middle :=
    match evidence with
    | .unseen => by
        simp only at freshSuccess
        rcases freshSuccess with ⟨_, rfl⟩
        simpa [DDLedger.markCapRange, CapabilityOriginLedger.setOrigins,
          before.supply_eq] using before
    | .known leaf => Classical.choice
        (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
          before freshSuccess)
    | .con name children => Classical.choice
        (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
          before freshSuccess)
    | .prod components => Classical.choice
        (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
          before freshSuccess)
  generalize fcvEq : capability.fcv = variables at rest
  cases variables with
  | nil =>
      simp only at rest
      rcases rest with ⟨rfl, rfl, rfl⟩
      let capOrigin := freshOrigin .recursiveBinder path
        "fix-argument-capability"
      let targetOrigin := freshOrigin .recursiveBinder path
        "fix-argument-target"
      let producerOrigin := freshOrigin .recursiveBinder path
        "fix-producer-target"
      let capRun :=
        DemandTypingInferenceCompletenessPatternCtorCapability.TraversalStateCorrespondence.freshCap
          middleRun capOrigin
      let targetRun := capRun.freshTy targetOrigin
      let producerRun := targetRun.state.freshTy producerOrigin
      let producerState :=
        (((middle.freshCap capOrigin).2.freshTy targetOrigin).2.freshTy
          producerOrigin).2
      have front : SupplyExtends q middle.supply := by
        let extension := recursiveMatcherTemplate_stateExtension (by
          simpa [recursiveMatcherTemplate] using recursiveSuccess)
        exact ⟨by simpa [before.supply_eq] using extension.supplyCap,
          by simpa [before.supply_eq] using extension.supplyTy⟩
      have back : SupplyExtends middle.supply producerState.supply := by
        exact ((SupplyExtends.bumpCap middle.supply 1).trans
          (SupplyExtends.bumpTy _ 1)).trans (SupplyExtends.bumpTy _ 1)
      have rangeEq :
          DDLedger.markFreshCap (DDLedger.markCapRange ledger q middle.supply)
              middle.supply =
            DDLedger.markCapRange ledger q producerState.supply := by
        rw [← markCapRange_trans ledger q middle.supply producerState.supply
          front back]
        simp [DDLedger.markCapRange, DDLedger.markFreshCap,
          CapabilityOriginLedger.markStructuralFlexible, producerState,
          CapabilityOriginLedger.setOrigins,
          InferState.freshCap, InferenceBase.freshCapMeta,
          InferState.freshTy, InferenceBase.freshTyMeta,
          InferState.recordEvent]
      refine ⟨?_⟩
      simp only [fcvEq]
      change TraversalStateCorrespondence producerState.supply S
        (DDLedger.markCapRange ledger q producerState.supply) producerState
      have rangeEq' := rangeEq
      dsimp [producerState] at rangeEq'
      rw [producerRun.state.supply_eq]
      simpa only [producerState, rangeEq', producerRun.state.supply_eq] using
        producerRun.state
  | cons first tail =>
      simp only at rest
      rcases rest with ⟨rfl, rfl, rfl⟩
      let targetOrigin := freshOrigin .recursiveBinder path
        "fix-argument-target"
      let producerOrigin := freshOrigin .recursiveBinder path
        "fix-producer-target"
      let targetRun := middleRun.freshTy targetOrigin
      let producerRun := targetRun.state.freshTy producerOrigin
      let producerState :=
        ((middle.freshTy targetOrigin).2.freshTy producerOrigin).2
      have front : SupplyExtends q middle.supply := by
        let extension := recursiveMatcherTemplate_stateExtension (by
          simpa [recursiveMatcherTemplate] using recursiveSuccess)
        exact ⟨by simpa [before.supply_eq] using extension.supplyCap,
          by simpa [before.supply_eq] using extension.supplyTy⟩
      have back : SupplyExtends middle.supply producerState.supply :=
        (SupplyExtends.bumpTy middle.supply 1).trans
          (SupplyExtends.bumpTy _ 1)
      have rangeEq : DDLedger.markCapRange ledger q middle.supply =
          DDLedger.markCapRange ledger q producerState.supply := by
        rw [← markCapRange_trans ledger q middle.supply producerState.supply
          front back]
        simp [DDLedger.markCapRange, producerState,
          CapabilityOriginLedger.setOrigins, InferState.freshTy,
          InferenceBase.freshTyMeta, InferState.recordEvent]
      refine ⟨?_⟩
      simp only [fcvEq]
      change TraversalStateCorrespondence producerState.supply S
        (DDLedger.markCapRange ledger q producerState.supply) producerState
      have rangeEq' := rangeEq
      dsimp [producerState] at rangeEq'
      rw [producerRun.state.supply_eq]
      simpa only [producerState, rangeEq', producerRun.state.supply_eq] using
        producerRun.state

/-- Full recursive-matcher placeholder completion: deterministic result,
state correspondence, and chronological transition. -/
theorem fixMatcherPlaceholder_complete
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {q q₀ : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    {domain codomain : Ty}
    (pure : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q₀)) :
    Nonempty (FixMatcherPlaceholderCompletion before signature path clauses
      domain codomain q₀) := by
  have pureAtState : fixMatcherPlaceholderSupply signature clauses
      initial.supply = some (domain, codomain, q₀) := by
    simpa [before.supply_eq] using pure
  rcases buildFixPlaceholder_complete_of_supply (path := path) pureAtState with
    ⟨final, success, supplyEq⟩
  subst q₀
  let correspondence := Classical.choice
    (buildFixPlaceholder_correspondence before success)
  rcases buildFixPlaceholder_matcher_ddRun success with
    ⟨_, prevailingEq, ledgerEq⟩
  have supplyExtension : SupplyExtends q final.supply := by
    have stateExtension := buildFixPlaceholder_stateExtension success
    exact ⟨by
        rw [← before.supply_eq]
        exact stateExtension.supplyCap,
      by
        rw [← before.supply_eq]
        exact stateExtension.supplyTy⟩
  let transition :=
    DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.markCapRangeExtension
      before supplyExtension rfl
    prevailingEq (by simpa [before.supply_eq] using ledgerEq)
  exact ⟨
    { state := final
      success := success
      supply_eq := rfl
      transition := transition
      declarative_bounded := correspondence.declarative_bounded
      executable_bounded := correspondence.executable_bounded
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := correspondence.ledger_below
      executable_ledger_below := correspondence.executable_ledger_below
      protected_origins := correspondence.protected_origins
      protected_below := correspondence.protected_below
      allocated_recorded := correspondence.allocated_recorded
      protected_safe := correspondence.protected_safe }⟩

end DemandTypingInferenceCompletenessFixMatcher
end TypePM
