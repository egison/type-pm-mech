import TypePM.DemandTypingInferenceCompletenessAlignmentFamilies
import TypePM.DemandTypingInferenceSoundnessFixMatcher

/-!
# Pattern-constructor capability completeness

This module completes the remaining capability-only traversal used by user
pattern constructors.  It first lifts `DDAlignCtorCapsWithLedger` to the
stateful field-demand executor, then packages complete constructor-capability
runs including their returned capability.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternCtorCapability

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessLedgerBisimulation

/-! ## One structural capability allocation -/

def TraversalStateCorrespondence.freshCapExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before.prevailing (DDLedger.markFreshCap ledger q)
      declarative (state.freshCap origin).2 := by
  let afterState := (state.freshCap origin).2
  let afterLedger := DDLedger.markFreshCap ledger q
  have forwardBetween : AdmissiblePostBetween
      afterState.capabilityOrigins afterLedger before.prevailing.forward := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.forwardBetween
      before.forward_bounded before.executable_ledger_below
      (fresh := [⟨q.nextCap⟩]) (fun varId membership => by
        simp only [List.mem_singleton] at membership
        subst varId
        exact Nat.le_refl _)
    simpa [afterState, afterLedger, DDLedger.markFreshCap,
      CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins, InferState.freshCap,
      InferState.recordEvent, before.supply_eq] using extended
  have reverseBetween : AdmissiblePostBetween
      afterLedger afterState.capabilityOrigins before.prevailing.reverse := by
    have extended := admissiblePostBetween_setFreshStructural_of_bounded
      before.prevailing.ledgerBisimulation.reverseBetween
      before.reverse_bounded before.ledger_below
      (fresh := [⟨q.nextCap⟩]) (fun varId membership => by
        simp only [List.mem_singleton] at membership
        subst varId
        exact Nat.le_refl _)
    simpa [afterState, afterLedger, DDLedger.markFreshCap,
      CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins, InferState.freshCap,
      InferState.recordEvent, before.supply_eq] using extended
  refine
    { after :=
        { forward := before.prevailing.forward
          forwardEquation := before.prevailing.forwardEquation
          declarativeIdempotent := before.prevailing.declarativeIdempotent
          reverse := before.prevailing.reverse
          reverseEquation := by
            change state.prevailing =
              Subst.seq before.prevailing.reverse declarative
            exact before.prevailing.reverseEquation
          ledgerBisimulation := ⟨forwardBetween, reverseBetween⟩
          executableIdempotent := by
            change state.prevailing.Idempotent
            exact before.prevailing.executableIdempotent }
      transportTy := ?_
      transportScheme := ?_ }
  intro declarativeTarget executableTarget related
  exact ⟨by
      change declarative.apply declarativeTarget =
        before.prevailing.forward.apply
          (state.prevailing.apply executableTarget)
      exact related.forward,
    by
      change state.prevailing.apply executableTarget =
        before.prevailing.reverse.apply
          (declarative.apply declarativeTarget)
      exact related.reverse⟩
  intro _ _ forward reverse
  exact ⟨forward, reverse⟩

def TraversalStateCorrespondence.freshCap
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    TraversalStateCorrespondence
      { q with nextCap := q.nextCap + 1 } declarative
      (DDLedger.markFreshCap ledger q) (state.freshCap origin).2 := by
  let extension :=
    DemandTypingInferenceCompletenessPatternCtorCapability.TraversalStateCorrespondence.freshCapExtension
      before origin
  let supplyExtension := SupplyExtends.bumpCap q 1
  refine
    { supply_eq := ?_
      prevailing := extension.after
      declarative_bounded := before.declarative_bounded.mono supplyExtension
      executable_bounded := before.executable_bounded.mono supplyExtension
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := DDLedger.LedgerBelow.markFreshCap before.ledger_below
      executable_ledger_below := ?_
      protected_origins := before.protected_origins.freshCap
        before.protected_below origin
      protected_below := before.protected_below.freshCap origin
      allocated_recorded := before.allocated_recorded.freshCap origin
      protected_safe :=
        DemandTypingInferenceCompletenessProtectedPreservation.CurrentProtectedProducerSafe.freshCap
          before.protected_safe
        (before.supply_eq ▸ before.executable_bounded)
        before.protected_below origin }
  · change { state.supply with nextCap := state.supply.nextCap + 1 } =
      { q with nextCap := q.nextCap + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextCap := supply.nextCap + 1 }) before.supply_eq
  · simpa [InferState.freshCap, InferState.recordEvent,
      DDLedger.markFreshCap, CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins,
      before.supply_eq] using
        DDLedger.LedgerBelow.markFreshCap before.executable_ledger_below

/-- Pointwise capability correspondence. -/
inductive CapListBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    List Cap → List Cap → Prop where
  | nil : CapListBisimulation relation [] []
  | cons (head : CapBisimulation relation declarativeHead executableHead)
      (tail : CapListBisimulation relation declarativeTail executableTail) :
      CapListBisimulation relation (declarativeHead :: declarativeTail)
        (executableHead :: executableTail)

/-- Pointwise optional capability correspondence for field demands. -/
inductive OptionalCapListBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    List (Option Cap) → List (Option Cap) → Prop where
  | nil : OptionalCapListBisimulation relation [] []
  | none (tail : OptionalCapListBisimulation relation declarativeTail
      executableTail) : OptionalCapListBisimulation relation
        (none :: declarativeTail) (none :: executableTail)
  | some (head : CapBisimulation relation declarativeHead executableHead)
      (tail : OptionalCapListBisimulation relation declarativeTail
        executableTail) : OptionalCapListBisimulation relation
          (some declarativeHead :: declarativeTail)
          (some executableHead :: executableTail)

theorem BisimulationExtension.transportCapList
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation before declarativeCaps executableCaps) :
    CapListBisimulation extension.after declarativeCaps executableCaps := by
  induction related with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          extension head) induction

theorem BisimulationExtension.transportOptionalCapList
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeCaps executableCaps : List (Option Cap)}
    (related : OptionalCapListBisimulation before declarativeCaps
      executableCaps) :
    OptionalCapListBisimulation extension.after declarativeCaps
      executableCaps := by
  induction related with
  | nil => exact .nil
  | none tail induction => exact .none induction
  | some head tail induction =>
      exact .some
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
          extension head) induction

/-! ## Projection transport under the state residual renaming -/

/-- Resolving corresponding child capabilities on both sides leaves the DD
list equal to the pointwise forward image of the executable list. -/
theorem CapListBisimulation.forwardResolved
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps) :
    declarativeCaps.map (fun capability => capability.apply declarative.cap) =
      (executableCaps.map
        (fun capability => capability.apply state.prevailing.cap)).map
          (fun capability => capability.apply relation.forward.cap) := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons]
      rw [(Ty.matcher.inj head.forward).1, induction]

/-- Reverse counterpart of `CapListBisimulation.forwardResolved`. -/
theorem CapListBisimulation.reverseResolved
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps) :
    executableCaps.map
        (fun capability => capability.apply state.prevailing.cap) =
      (declarativeCaps.map
        (fun capability => capability.apply declarative.cap)).map
          (fun capability => capability.apply relation.reverse.cap) := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons]
      rw [(Ty.matcher.inj head.reverse).1, induction]

/-- The reverse residual is a genuine variable renaming on the finite DD
child-capability image used by constructor projection. -/
theorem CapListBisimulation.executableResolved_eq_applyRen
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps) :
    ∃ rename : CapVar → CapVar,
      executableCaps.map
          (fun capability => capability.apply state.prevailing.cap) =
        Cap.applyRenList rename
          (declarativeCaps.map
            (fun capability => capability.apply declarative.cap)) := by
  classical
  let declarativeResolved := declarativeCaps.map
    (fun capability => capability.apply declarative.cap)
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
      relation (.matcher (.prod declarativeCaps) .unit)
  let rename := localMap.capImage
  refine ⟨rename, ?_⟩
  rw [related.reverseResolved]
  have pure :=
    DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
      localMap (declarative.apply (.matcher (.prod declarativeCaps) .unit))
      (fun _ membership => membership) (fun _ membership => membership)
  have capabilities := Cap.prod.inj (Ty.matcher.inj pure).1
  let variablePost : VariablePost
      (DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
        localMap) :=
    { capVariable := fun varId => ⟨rename varId, rfl⟩ }
  have capRenEq : variablePost.capRen = rename := by
    funext varId
    have point := variablePost.capEquation varId
    change Cap.var (rename varId) =
      Cap.var (variablePost.capRen varId) at point
    exact (Cap.var.inj point).symm
  have pureCaps := variablePost.applyCapList_eq_applyRenList
    declarativeResolved
  rw [capRenEq] at pureCaps
  have resolvedEq : Cap.applyList declarative.cap declarativeCaps =
      declarativeResolved := by
    exact Cap.applyList_eq_map _ _
  rw [resolvedEq] at capabilities
  rw [pureCaps] at capabilities
  rw [Cap.applyList_eq_map] at capabilities
  simpa [declarativeResolved] using capabilities

/-- The forward residual is a genuine variable renaming on the finite
executable child-capability image. -/
theorem CapListBisimulation.declarativeResolved_eq_applyRen
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps) :
    ∃ rename : CapVar → CapVar,
      declarativeCaps.map
          (fun capability => capability.apply declarative.cap) =
        Cap.applyRenList rename
          (executableCaps.map
            (fun capability => capability.apply state.prevailing.cap)) := by
  classical
  let executableResolved := executableCaps.map
    (fun capability => capability.apply state.prevailing.cap)
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn_image
      relation (.matcher (.prod executableCaps) .unit)
  let rename := localMap.capImage
  refine ⟨rename, ?_⟩
  rw [related.forwardResolved]
  have pure :=
    DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
      localMap
      (state.prevailing.apply (.matcher (.prod executableCaps) .unit))
      (fun _ membership => membership) (fun _ membership => membership)
  have capabilities := Cap.prod.inj (Ty.matcher.inj pure).1
  let variablePost : VariablePost
      (DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
        localMap) :=
    { capVariable := fun varId => ⟨rename varId, rfl⟩ }
  have capRenEq : variablePost.capRen = rename := by
    funext varId
    have point := variablePost.capEquation varId
    change Cap.var (rename varId) =
      Cap.var (variablePost.capRen varId) at point
    exact (Cap.var.inj point).symm
  have pureCaps := variablePost.applyCapList_eq_applyRenList
    executableResolved
  rw [capRenEq] at pureCaps
  have resolvedEq : Cap.applyList state.prevailing.cap executableCaps =
      executableResolved := by
    exact Cap.applyList_eq_map _ _
  rw [resolvedEq] at capabilities
  rw [pureCaps] at capabilities
  rw [Cap.applyList_eq_map] at capabilities
  simpa [executableResolved] using capabilities

/-- A successful DD projection is also successful on the corresponding
executable children, with the projected evidence changed only by renaming. -/
theorem CapListBisimulation.projectSignature_success
    {observable : Shape.Observability}
    {projection : Projection.ProjectionSignature observable}
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps)
    {projected : Shape.Evidence}
    (success : Projection.projectSignature projection
      ((declarativeCaps.map
        (fun capability => capability.apply declarative.cap)).map Shape.ofCap) =
        some projected) :
    ∃ rename : CapVar → CapVar,
      Projection.projectSignature projection
          ((executableCaps.map
            (fun capability => capability.apply state.prevailing.cap)).map
              Shape.ofCap) =
        some (projected.applyRen rename) := by
  rcases related.executableResolved_eq_applyRen with ⟨rename, equation⟩
  refine ⟨rename, ?_⟩
  rw [equation, Shape.map_ofCap_applyRen]
  exact Projection.projectSignature_rename_of_success rename projection success

/-- A DD projection miss remains a miss on corresponding executable children.
Otherwise executable success transports back along the forward residual and
contradicts the DD result. -/
theorem CapListBisimulation.projectSignature_miss
    {observable : Shape.Observability}
    {projection : Projection.ProjectionSignature observable}
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeCaps executableCaps : List Cap}
    (related : CapListBisimulation relation declarativeCaps executableCaps)
    (miss : Projection.projectSignature projection
      ((declarativeCaps.map
        (fun capability => capability.apply declarative.cap)).map Shape.ofCap) =
        none) :
    Projection.projectSignature projection
      ((executableCaps.map
        (fun capability => capability.apply state.prevailing.cap)).map
          Shape.ofCap) = none := by
  rcases related.declarativeResolved_eq_applyRen with ⟨rename, equation⟩
  cases executableResult : Projection.projectSignature projection
      ((executableCaps.map
        (fun capability => capability.apply state.prevailing.cap)).map
          Shape.ofCap) with
  | none => rfl
  | some projected =>
      have renamed := Projection.projectSignature_rename_of_success rename
        projection executableResult
      rw [← Shape.map_ofCap_applyRen, ← equation] at renamed
      rw [miss] at renamed
      contradiction

/-! ## Reverse completeness of the pure allocation twins -/

/- The executable skeleton freshener succeeds whenever its pure
supply-indexed twin succeeds.  The proof follows the same three mutually
recursive shapes, so it also pins the executable allocation order. -/
mutual

theorem freshenSkeleton_complete_of_supply
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (evidence : Shape.Evidence) (initial : InferState)
      (capability : Cap) (q' : InferenceBase.FreshSupply),
      freshenSkeletonSupply observable evidence initial.supply =
          some (capability, q') →
        ∃ final, freshenSkeleton observable origin evidence initial =
          some (capability, final)
  | .unseen, initial, capability, q', pureSuccess => by
      simp only [freshenSkeletonSupply, Option.some.injEq,
        Prod.mk.injEq] at pureSuccess
      rcases pureSuccess with ⟨rfl, rfl⟩
      refine ⟨(initial.freshCap origin).2, ?_⟩
      simp [freshenSkeleton, InferState.freshCap]
  | .known leaf, initial, capability, q', pureSuccess => by
      simp only [freshenSkeletonSupply, Option.some.injEq,
        Prod.mk.injEq] at pureSuccess
      rcases pureSuccess with ⟨rfl, rfl⟩
      exact ⟨initial, rfl⟩
  | .con name children, initial, capability, q', pureSuccess => by
      cases maskEq : observable name with
      | none => simp [freshenSkeletonSupply, maskEq] at pureSuccess
      | some mask =>
          cases pureChildren : freshenSkeletonMaskedSupply observable mask
              children initial.supply with
          | none =>
              simp [freshenSkeletonSupply, maskEq, pureChildren] at pureSuccess
          | some pair =>
              rcases pair with ⟨capabilities, childrenSupply⟩
              simp [freshenSkeletonSupply, maskEq, pureChildren] at pureSuccess
              rcases pureSuccess with ⟨rfl, rfl⟩
              rcases freshenSkeletonMasked_complete_of_supply observable origin
                  mask children initial capabilities childrenSupply pureChildren
                with ⟨final, executableChildren⟩
              exact ⟨final, by
                simp [freshenSkeleton, maskEq, executableChildren]⟩
  | .prod components, initial, capability, q', pureSuccess => by
      cases pureComponents : freshenSkeletonListSupply observable components
          initial.supply with
      | none =>
          simp [freshenSkeletonSupply, pureComponents] at pureSuccess
      | some pair =>
          rcases pair with ⟨capabilities, componentsSupply⟩
          simp [freshenSkeletonSupply, pureComponents] at pureSuccess
          rcases pureSuccess with ⟨rfl, rfl⟩
          rcases freshenSkeletonList_complete_of_supply observable origin
              components initial capabilities componentsSupply pureComponents
            with ⟨final, executableComponents⟩
          exact ⟨final, by
            simp [freshenSkeleton, executableComponents]⟩

theorem freshenSkeletonList_complete_of_supply
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (evidences : List Shape.Evidence) (initial : InferState)
      (capabilities : List Cap) (q' : InferenceBase.FreshSupply),
      freshenSkeletonListSupply observable evidences initial.supply =
          some (capabilities, q') →
        ∃ final, freshenSkeletonList observable origin evidences initial =
          some (capabilities, final)
  | [], initial, capabilities, q', pureSuccess => by
      simp only [freshenSkeletonListSupply, Option.some.injEq,
        Prod.mk.injEq] at pureSuccess
      rcases pureSuccess with ⟨rfl, rfl⟩
      exact ⟨initial, rfl⟩
  | evidence :: rest, initial, capabilities, q', pureSuccess => by
      cases pureHead : freshenSkeletonSupply observable evidence initial.supply
          with
      | none => simp [freshenSkeletonListSupply, pureHead] at pureSuccess
      | some headPair =>
          rcases headPair with ⟨head, middleSupply⟩
          cases pureTail : freshenSkeletonListSupply observable rest middleSupply
              with
          | none =>
              simp [freshenSkeletonListSupply, pureHead, pureTail] at pureSuccess
          | some tailPair =>
              rcases tailPair with ⟨tail, tailSupply⟩
              simp [freshenSkeletonListSupply, pureHead, pureTail] at pureSuccess
              rcases pureSuccess with ⟨rfl, rfl⟩
              rcases freshenSkeleton_complete_of_supply observable origin
                  evidence initial head middleSupply pureHead with
                ⟨middle, executableHead⟩
              have middleExact := freshenSkeleton_supplyExact executableHead
              have pairEq := Option.some.inj
                (middleExact.1.symm.trans pureHead)
              have middleSupplyEq : middle.supply = middleSupply :=
                congrArg Prod.snd pairEq
              rw [← middleSupplyEq] at pureTail
              rcases freshenSkeletonList_complete_of_supply observable origin
                  rest middle tail tailSupply pureTail with
                ⟨final, executableTail⟩
              exact ⟨final, by
                simp [freshenSkeletonList, executableHead, executableTail]⟩

theorem freshenSkeletonMasked_complete_of_supply
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (mask : List Bool) (evidences : List Shape.Evidence)
      (initial : InferState) (capabilities : List Cap)
      (q' : InferenceBase.FreshSupply),
      freshenSkeletonMaskedSupply observable mask evidences initial.supply =
          some (capabilities, q') →
        ∃ final, freshenSkeletonMasked observable origin mask evidences
          initial = some (capabilities, final)
  | [], [], initial, capabilities, q', pureSuccess => by
      simp only [freshenSkeletonMaskedSupply, Option.some.injEq,
        Prod.mk.injEq] at pureSuccess
      rcases pureSuccess with ⟨rfl, rfl⟩
      exact ⟨initial, rfl⟩
  | [], _ :: _, _, _, _, pureSuccess => by
      simp [freshenSkeletonMaskedSupply] at pureSuccess
  | _ :: _, [], _, _, _, pureSuccess => by
      simp [freshenSkeletonMaskedSupply] at pureSuccess
  | isObservable :: mask, evidence :: rest, initial, capabilities, q',
      pureSuccess => by
      cases isObservable with
      | false =>
          cases pureTail : freshenSkeletonMaskedSupply observable mask rest
              initial.supply with
          | none =>
              simp [freshenSkeletonMaskedSupply, pureTail] at pureSuccess
          | some tailPair =>
              rcases tailPair with ⟨tail, tailSupply⟩
              simp [freshenSkeletonMaskedSupply, pureTail] at pureSuccess
              rcases pureSuccess with ⟨rfl, rfl⟩
              rcases freshenSkeletonMasked_complete_of_supply observable origin
                  mask rest initial tail tailSupply pureTail with
                ⟨final, executableTail⟩
              exact ⟨final, by
                simp [freshenSkeletonMasked, executableTail]⟩
      | true =>
          cases pureHead : freshenSkeletonSupply observable evidence
              initial.supply with
          | none =>
              simp [freshenSkeletonMaskedSupply, pureHead] at pureSuccess
          | some headPair =>
              rcases headPair with ⟨head, middleSupply⟩
              cases pureTail : freshenSkeletonMaskedSupply observable mask rest
                  middleSupply with
              | none =>
                  simp [freshenSkeletonMaskedSupply, pureHead, pureTail]
                    at pureSuccess
              | some tailPair =>
                  rcases tailPair with ⟨tail, tailSupply⟩
                  simp [freshenSkeletonMaskedSupply, pureHead, pureTail]
                    at pureSuccess
                  rcases pureSuccess with ⟨rfl, rfl⟩
                  rcases freshenSkeleton_complete_of_supply observable origin
                      evidence initial head middleSupply pureHead with
                    ⟨middle, executableHead⟩
                  have middleExact := freshenSkeleton_supplyExact executableHead
                  have pairEq := Option.some.inj
                    (middleExact.1.symm.trans pureHead)
                  have middleSupplyEq : middle.supply = middleSupply :=
                    congrArg Prod.snd pairEq
                  rw [← middleSupplyEq] at pureTail
                  rcases freshenSkeletonMasked_complete_of_supply observable
                      origin mask rest middle tail tailSupply pureTail with
                    ⟨final, executableTail⟩
                  exact ⟨final, by
                    simp [freshenSkeletonMasked, executableHead,
                      executableTail]⟩

end

/-- Exact reverse surface for skeleton freshening, including the terminal
supply, unchanged prevailing substitution, and the structural ledger range. -/
theorem freshenSkeleton_complete_exact
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidence : Shape.Evidence} {initial : InferState}
    {capability : Cap} {q' : InferenceBase.FreshSupply}
    (pureSuccess : freshenSkeletonSupply observable evidence initial.supply =
      some (capability, q')) :
    ∃ final,
      freshenSkeleton observable origin evidence initial =
          some (capability, final) ∧
      final.supply = q' ∧
      final.prevailing = initial.prevailing ∧
      final.capabilityOrigins =
        DDLedger.markCapRange initial.capabilityOrigins initial.supply q' := by
  rcases freshenSkeleton_complete_of_supply observable origin evidence initial
      capability q' pureSuccess with ⟨final, executableSuccess⟩
  rcases freshenSkeleton_supplyExact executableSuccess with
    ⟨pureAgain, prevailing, ledger⟩
  have resultEq := Option.some.inj (pureAgain.symm.trans pureSuccess)
  have supplyEq : final.supply = q' := congrArg Prod.snd resultEq
  exact ⟨final, executableSuccess, supplyEq, prevailing, by
    simpa [supplyEq] using ledger⟩

/-- The total shared-result allocator is literally its pure supply twin. -/
theorem freshPatternCtorAssignments_complete_exact
    (origin : ConstraintOrigin) (variables : List TypePM.TyVar)
    (initial : InferState) :
    let allocated := freshPatternCtorAssignments origin variables initial
    allocated.1 =
        (patternCtorAssignmentsSupply variables initial.supply).1 ∧
      allocated.2.supply =
        (patternCtorAssignmentsSupply variables initial.supply).2 ∧
      allocated.2.prevailing = initial.prevailing ∧
      allocated.2.capabilityOrigins =
        DDLedger.markCapRange initial.capabilityOrigins initial.supply
          allocated.2.supply :=
  freshPatternCtorAssignments_supplyExact origin variables initial

/-! ## Capability-subroutine run package -/

/-- Result package for the pattern-constructor capability subroutine.  It is
kept below the general pattern traversal because the reverse-completeness
proof constructs this package directly. -/
structure PatternCtorCapRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option (Cap × InferState))
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (capability : Cap) : Type where
  result : Cap × InferState
  success : operation = some result
  transition : BisimulationExtension before.prevailing ledger declarative
    result.2
  correspondence : TraversalStateCorrespondence q' declarative ledger result.2
  prevailing_eq : correspondence.prevailing = transition.after
  capability : CapBisimulation transition.after capability result.1

def PatternCtorCapRunCompletion.extension
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option (Cap × InferState)} {capability : Cap}
    (run : PatternCtorCapRunCompletion before operation q' S' ledger
      capability) :
    BisimulationExtension before.prevailing ledger S' run.result.2 where
  after := run.correspondence.prevailing
  transportTy := by
    intro declarativeTarget executableTarget related
    rw [run.prevailing_eq]
    exact run.transition.transportTy related
  transportScheme := by
    intro _ _ forward reverse
    rw [run.prevailing_eq]
    exact run.transition.transportScheme forward reverse

private def StateRunCompletion.refl
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial) :
    StateRunCompletion relation (some initial) q S ledger :=
  { result := initial
    success := rfl
    supply_eq := relation.supply_eq
    transition := BisimulationExtension.refl relation.prevailing
    declarative_bounded := relation.declarative_bounded
    executable_bounded := relation.executable_bounded
    forward_bounded := relation.forward_bounded
    reverse_bounded := relation.reverse_bounded
    ledger_below := relation.ledger_below
    executable_ledger_below := relation.executable_ledger_below
    protected_origins := relation.protected_origins
    protected_below := relation.protected_below
    allocated_recorded := relation.allocated_recorded
    protected_safe := relation.protected_safe }

/-- Generic completeness of the constructor-field capability solver. -/
theorem ddAlignCtorCapsWithLedger_complete_nonempty
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeChildren executableChildren : List Cap}
    {declarativeDemands executableDemands : List (Option Cap)}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (childrenRelated : CapListBisimulation relation.prevailing
      declarativeChildren executableChildren)
    (demandsRelated : OptionalCapListBisimulation relation.prevailing
      declarativeDemands executableDemands)
    (declarativeChildrenBounded : ∀ child ∈ declarativeChildren,
      child.BoundedBy q)
    (declarativeDemandsBounded : ∀ demand ∈ declarativeDemands,
      ∀ capability, demand = some capability → capability.BoundedBy q)
    (executableChildrenBounded : ∀ child ∈ executableChildren,
      child.BoundedBy q)
    (executableDemandsBounded : ∀ demand ∈ executableDemands,
      ∀ capability, demand = some capability → capability.BoundedBy q)
    (aligned : DDAlignCtorCapsWithLedger ledger S declarativeChildren
      declarativeDemands S') :
    Nonempty (StateRunCompletion relation
      (alignPatternCtorCapabilities initial origin executableChildren
        executableDemands) q S' ledger) := by
  induction aligned generalizing initial executableChildren executableDemands with
  | nil =>
      cases childrenRelated
      cases demandsRelated
      exact ⟨StateRunCompletion.refl relation⟩
  | skip tailAligned induction =>
      cases childrenRelated with
      | cons childHead childTail =>
          cases demandsRelated with
          | none demandTail =>
              let tailExists := induction relation childTail demandTail
                (fun child mem => declarativeChildrenBounded child
                  (by simp [mem]))
                (fun demand mem capability equation =>
                  declarativeDemandsBounded demand (by simp [mem]) capability
                    equation)
                (fun child mem => executableChildrenBounded child
                  (by simp [mem]))
                (fun demand mem capability equation =>
                  executableDemandsBounded demand (by simp [mem]) capability
                    equation)
              let tailRun := Classical.choice tailExists
              exact ⟨StateRunCompletion.congrOperation tailRun (by rfl)⟩
  | @solve S₀ child expected children demands capDelta S₁ capDD tailAligned
      induction =>
      cases childrenRelated with
      | cons childHead childTail =>
          rename_i executableChildRaw executableChildrenTail
          cases demandsRelated with
          | some expectedHead demandTail =>
              rename_i executableExpectedRaw executableDemandsTail
              let declarativeChild := child.apply S₀.cap
              let declarativeExpected := expected.apply S₀.cap
              let executableChild := Cap.apply initial.prevailing.cap
                executableChildRaw
              let executableExpected := Cap.apply initial.prevailing.cap
                executableExpectedRaw
              have resolved : ResolvedCapComponents
                  relation.prevailing.forward relation.prevailing.reverse
                  declarativeChild executableChild declarativeExpected
                  executableExpected :=
                ⟨(Ty.matcher.inj childHead.forward).1,
                  (Ty.matcher.inj childHead.reverse).1,
                  (Ty.matcher.inj expectedHead.forward).1,
                  (Ty.matcher.inj expectedHead.reverse).1⟩
              have declarativeChildFixed :
                  declarativeChild.apply S₀.cap = declarativeChild :=
                (Ty.matcher.inj (relation.prevailing.declarativeIdempotent
                  (.matcher _ .unit))).1
              have declarativeExpectedFixed :
                  declarativeExpected.apply S₀.cap = declarativeExpected :=
                (Ty.matcher.inj (relation.prevailing.declarativeIdempotent
                  (.matcher _ .unit))).1
              have executableChildFixed :
                  executableChild.apply initial.prevailing.cap =
                    executableChild :=
                (Ty.matcher.inj (relation.prevailing.executableIdempotent
                  (.matcher _ .unit))).1
              have executableExpectedFixed :
                  executableExpected.apply initial.prevailing.cap =
                    executableExpected :=
                (Ty.matcher.inj (relation.prevailing.executableIdempotent
                  (.matcher _ .unit))).1
              have declarativeChildBounded : declarativeChild.BoundedBy q :=
                relation.declarative_bounded.applyCap
                  (declarativeChildrenBounded _ (by simp))
              have declarativeExpectedBounded :
                  declarativeExpected.BoundedBy q :=
                relation.declarative_bounded.applyCap
                  (declarativeDemandsBounded _ (by simp) _ rfl)
              have executableChildBounded : executableChild.BoundedBy q :=
                relation.executable_bounded.applyCap
                  (executableChildrenBounded _ (by simp))
              have executableExpectedBounded : executableExpected.BoundedBy q :=
                relation.executable_bounded.applyCap
                  (executableDemandsBounded _ (by simp) _ rfl)
              let headRun := runResolvedCapEq_complete (origin := origin)
                relation resolved capDD declarativeChildFixed
                declarativeExpectedFixed executableChildFixed
                executableExpectedFixed declarativeChildBounded
                declarativeExpectedBounded executableChildBounded
                executableExpectedBounded
              let tailExists := induction headRun.completion
                (BisimulationExtension.transportCapList headRun.transition
                  childTail)
                (BisimulationExtension.transportOptionalCapList
                  headRun.transition demandTail)
                (fun child mem => declarativeChildrenBounded child
                  (by simp [mem]))
                (fun demand mem capability equation =>
                  declarativeDemandsBounded demand (by simp [mem]) capability
                    equation)
                (fun child mem => executableChildrenBounded child
                  (by simp [mem]))
                (fun demand mem capability equation =>
                  executableDemandsBounded demand (by simp [mem]) capability
                    equation)
              let tailRun := Classical.choice tailExists
              exact ⟨StateRunCompletion.congrOperation
                (StateRunCompletion.seq
                  (secondOperation := fun state =>
                    alignPatternCtorCapabilities state origin _ _)
                  headRun tailRun) (by
                    simp [alignPatternCtorCapabilities, executableChild,
                      executableExpected])⟩

/-- Noncomputable projection used by the fallback constructor branch. -/
noncomputable def ddAlignCtorCapsWithLedger_complete
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeChildren executableChildren : List Cap}
    {declarativeDemands executableDemands : List (Option Cap)}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (childrenRelated : CapListBisimulation relation.prevailing
      declarativeChildren executableChildren)
    (demandsRelated : OptionalCapListBisimulation relation.prevailing
      declarativeDemands executableDemands)
    (declarativeChildrenBounded : ∀ child ∈ declarativeChildren,
      child.BoundedBy q)
    (declarativeDemandsBounded : ∀ demand ∈ declarativeDemands,
      ∀ capability, demand = some capability → capability.BoundedBy q)
    (executableChildrenBounded : ∀ child ∈ executableChildren,
      child.BoundedBy q)
    (executableDemandsBounded : ∀ demand ∈ executableDemands,
      ∀ capability, demand = some capability → capability.BoundedBy q)
    (aligned : DDAlignCtorCapsWithLedger ledger S declarativeChildren
      declarativeDemands S') :
    StateRunCompletion relation
      (alignPatternCtorCapabilities initial origin executableChildren
        executableDemands) q S' ledger :=
  Classical.choice (ddAlignCtorCapsWithLedger_complete_nonempty relation
    childrenRelated demandsRelated declarativeChildrenBounded
    declarativeDemandsBounded executableChildrenBounded
    executableDemandsBounded aligned)

end DemandTypingInferenceCompletenessPatternCtorCapability
end TypePM
