import TypePM.DemandTypingInferenceCompletenessPatternDispatcher
import TypePM.DemandTypingInferenceCompletenessFixMatcher
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation

/-!
# Closed pattern-constructor capability completeness package

This module closes the isolated capability subroutine used by user pattern
constructors.  Projection success is transported through the finite
DD/executable renaming; projection failure is invariant.  The fallback branch
then replays the shared-result allocation and field-capability alignment before
using the same projected-skeleton completion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternCtorCapComplete

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternCtorCapability
open DemandTypingInferenceCompletenessPatternMain
open DemandTypingInferenceCompletenessPatternDispatcher
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance

/-- The canonical reverse renaming extracted from bounded constructor children
fixes every capability identifier which may be freshly allocated at `q`. -/
theorem reverseChildRenaming_freshAbove
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeChildren : List Cap}
    (childrenBounded : ∀ child ∈ declarativeChildren, child.BoundedBy q) :
    let bundle := Ty.matcher (.prod declarativeChildren) .unit
    let localMap := StateBisimulation.reverseLocalRenamingOn_image
      before.prevailing bundle
    RenamingFreshAbove localMap.capImage q := by
  dsimp only
  intro varId above
  apply dif_neg
  intro membership
  have unitBounded : Ty.BoundedBy q .unit := by
    constructor
    · intro varId membership
      exact nomatch membership
    · intro varId membership
      exact nomatch membership
  have rawBundleBounded : Ty.BoundedBy q
      (.matcher (.prod declarativeChildren) .unit) :=
    Ty.BoundedBy.matcherOf
      (Cap.BoundedBy.prodOfForall childrenBounded) unitBounded
  have normalizedBounded := before.declarative_bounded.apply rawBundleBounded
  exact (Nat.not_le_of_lt (normalizedBounded.1 varId membership)) above

/-- The local reverse renaming gives the concrete executable projection result
and is fresh above the current supply. -/
theorem projectSignature_success_scoped
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeChildren executableChildren : List Cap}
    (children : CapListBisimulation before.prevailing declarativeChildren
      executableChildren)
    (childrenBounded : ∀ child ∈ declarativeChildren, child.BoundedBy q)
    {projected : Shape.Evidence}
    (success : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S.cap).map
        Shape.ofCap) = some projected) :
    let bundle := Ty.matcher (.prod declarativeChildren) .unit
    let localMap := StateBisimulation.reverseLocalRenamingOn_image
      before.prevailing bundle
    Projection.projectSignature entry.projection
      ((executableChildren.map fun child =>
        child.apply state.prevailing.cap).map Shape.ofCap) =
        some (projected.applyRen localMap.capImage) ∧
      RenamingFreshAbove localMap.capImage q := by
  dsimp only
  let bundle := Ty.matcher (.prod declarativeChildren) .unit
  let localMap := StateBisimulation.reverseLocalRenamingOn_image
    before.prevailing bundle
  let rename := localMap.capImage
  have resolved : executableChildren.map
      (fun child => child.apply state.prevailing.cap) =
      Cap.applyRenList rename
        (declarativeChildren.map fun child => child.apply S.cap) := by
    rw [children.reverseResolved]
    have pure := LocalRenamingOn.forward_apply_eq_pure localMap
      (S.apply bundle) (fun _ membership => membership)
      (fun _ membership => membership)
    have capabilities := Cap.prod.inj (Ty.matcher.inj pure).1
    let variablePost : VariablePost (LocalRenamingOn.pureSubst localMap) :=
      { capVariable := fun varId => ⟨rename varId, rfl⟩ }
    have capRenEq : variablePost.capRen = rename := by
      funext varId
      have point := variablePost.capEquation varId
      change Cap.var (rename varId) = Cap.var (variablePost.capRen varId) at point
      exact (Cap.var.inj point).symm
    have pureCaps := variablePost.applyCapList_eq_applyRenList
      (declarativeChildren.map fun child => child.apply S.cap)
    rw [capRenEq] at pureCaps
    have capabilities' :
        (declarativeChildren.map fun child => child.apply S.cap).map
            (fun capability => capability.apply before.prevailing.reverse.cap) =
          Cap.applyList (LocalRenamingOn.pureSubst localMap).cap
            (declarativeChildren.map fun child => child.apply S.cap) := by
      simpa only [Cap.applyList_eq_map] using capabilities
    exact capabilities'.trans pureCaps
  constructor
  · rw [resolved, Shape.map_ofCap_applyRen]
    exact Projection.projectSignature_rename_of_success rename
      entry.projection success
  · exact reverseChildRenaming_freshAbove before childrenBounded

/-! ## Support of pure skeleton freshening -/

mutual

/-- Every variable returned by pure skeleton freshening either came from the
input evidence or was allocated in the fresh interval beginning at `q`. -/
theorem freshenSkeletonSupply_fcv_origin
    {observable : Shape.Observability} :
    ∀ {evidence : Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capability : Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonSupply observable evidence q = some (capability, q') →
      ∀ varId ∈ capability.fcv,
        varId ∈ evidence.fcv ∨ q.nextCap ≤ varId.id
  | .unseen, q, capability, q', success => by
      simp only [freshenSkeletonSupply, Option.some.injEq, Prod.mk.injEq]
        at success
      rcases success with ⟨rfl, rfl⟩
      intro varId membership
      simp only [Cap.fcv, List.mem_singleton] at membership
      subst varId
      exact Or.inr (Nat.le_refl _)
  | .known leaf, q, capability, q', success => by
      simp only [freshenSkeletonSupply, Option.some.injEq, Prod.mk.injEq]
        at success
      rcases success with ⟨rfl, rfl⟩
      intro varId membership
      rw [Shape.Leaf.fcv_toCap] at membership
      exact Or.inl membership
  | .con name children, q, capability, q', success => by
      simp only [freshenSkeletonSupply] at success
      cases maskEq : observable name with
      | none => simp [maskEq] at success
      | some mask =>
          cases childrenEq : freshenSkeletonMaskedSupply observable mask
              children q with
          | none => simp [maskEq, childrenEq] at success
          | some result =>
              rcases result with ⟨capabilities, q₁⟩
              simp [maskEq, childrenEq] at success
              rcases success with ⟨rfl, rfl⟩
              intro varId membership
              simp only [Cap.fcv] at membership
              rcases freshenSkeletonMaskedSupply_fcv_origin childrenEq varId
                  membership with source | fresh
              · exact Or.inl source
              · exact Or.inr fresh
  | .prod components, q, capability, q', success => by
      simp only [freshenSkeletonSupply] at success
      cases componentsEq : freshenSkeletonListSupply observable components q with
      | none => simp [componentsEq] at success
      | some result =>
          rcases result with ⟨capabilities, q₁⟩
          simp [componentsEq] at success
          rcases success with ⟨rfl, rfl⟩
          intro varId membership
          simp only [Cap.fcv] at membership
          exact freshenSkeletonListSupply_fcv_origin componentsEq varId membership

/-- List support counterpart. -/
theorem freshenSkeletonListSupply_fcv_origin
    {observable : Shape.Observability} :
    ∀ {evidences : List Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capabilities : List Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonListSupply observable evidences q =
          some (capabilities, q') →
      ∀ varId ∈ Cap.fcvList capabilities,
        varId ∈ Shape.Evidence.fcvList evidences ∨ q.nextCap ≤ varId.id
  | [], q, capabilities, q', success => by
      simp only [freshenSkeletonListSupply, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro varId membership
      exact nomatch membership
  | evidence :: rest, q, capabilities, q', success => by
      simp only [freshenSkeletonListSupply] at success
      cases headEq : freshenSkeletonSupply observable evidence q with
      | none => simp [headEq] at success
      | some headResult =>
          rcases headResult with ⟨head, middleSupply⟩
          cases tailEq : freshenSkeletonListSupply observable rest middleSupply with
          | none => simp [headEq, tailEq] at success
          | some tailResult =>
              rcases tailResult with ⟨tail, tailSupply⟩
              simp [headEq, tailEq] at success
              rcases success with ⟨rfl, rfl⟩
              intro varId membership
              simp only [Cap.fcvList, List.mem_append,
                Shape.Evidence.fcvList] at membership ⊢
              rcases membership with inHead | inTail
              · rcases freshenSkeletonSupply_fcv_origin headEq varId inHead with
                  source | fresh
                · exact Or.inl (Or.inl source)
                · exact Or.inr fresh
              · rcases freshenSkeletonListSupply_fcv_origin tailEq varId inTail
                  with source | fresh
                · exact Or.inl (Or.inr source)
                · exact Or.inr (Nat.le_trans
                    (SupplyExtends.freshenSkeleton headEq).1 fresh)

/-- Masked-list support counterpart; skipped components contribute `Any`. -/
theorem freshenSkeletonMaskedSupply_fcv_origin
    {observable : Shape.Observability} :
    ∀ {mask : List Bool} {evidences : List Shape.Evidence}
      {q : InferenceBase.FreshSupply} {capabilities : List Cap}
      {q' : InferenceBase.FreshSupply},
      freshenSkeletonMaskedSupply observable mask evidences q =
          some (capabilities, q') →
      ∀ varId ∈ Cap.fcvList capabilities,
        varId ∈ Shape.Evidence.fcvList evidences ∨ q.nextCap ≤ varId.id
  | [], [], q, capabilities, q', success => by
      simp only [freshenSkeletonMaskedSupply, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      intro varId membership
      exact nomatch membership
  | [], _ :: _, _, _, _, success => by
      simp [freshenSkeletonMaskedSupply] at success
  | _ :: _, [], _, _, _, success => by
      simp [freshenSkeletonMaskedSupply] at success
  | isObservable :: mask, evidence :: rest, q, capabilities, q', success => by
      cases isObservable with
      | false =>
          simp only [freshenSkeletonMaskedSupply] at success
          cases tailEq : freshenSkeletonMaskedSupply observable mask rest q with
          | none => simp [tailEq] at success
          | some tailResult =>
              rcases tailResult with ⟨tail, tailSupply⟩
              simp [tailEq] at success
              rcases success with ⟨rfl, rfl⟩
              intro varId membership
              simp only [Cap.fcvList, Cap.fcv, List.not_mem_nil,
                false_or, Shape.Evidence.fcvList, List.mem_append] at membership ⊢
              rcases freshenSkeletonMaskedSupply_fcv_origin tailEq varId
                  membership with source | fresh
              · exact Or.inl (Or.inr source)
              · exact Or.inr fresh
      | true =>
          simp only [freshenSkeletonMaskedSupply, ↓reduceIte] at success
          cases headEq : freshenSkeletonSupply observable evidence q with
          | none => simp [headEq] at success
          | some headResult =>
              rcases headResult with ⟨head, middleSupply⟩
              cases tailEq : freshenSkeletonMaskedSupply observable mask rest
                  middleSupply with
              | none => simp [headEq, tailEq] at success
              | some tailResult =>
                  rcases tailResult with ⟨tail, tailSupply⟩
                  simp [headEq, tailEq] at success
                  rcases success with ⟨rfl, rfl⟩
                  intro varId membership
                  simp only [Cap.fcvList, List.mem_append,
                    Shape.Evidence.fcvList] at membership ⊢
                  rcases membership with inHead | inTail
                  · rcases freshenSkeletonSupply_fcv_origin headEq varId inHead
                      with source | fresh
                    · exact Or.inl (Or.inl source)
                    · exact Or.inr fresh
                  · rcases freshenSkeletonMaskedSupply_fcv_origin tailEq varId
                      inTail with source | fresh
                    · exact Or.inl (Or.inr source)
                    · exact Or.inr (Nat.le_trans
                        (SupplyExtends.freshenSkeleton headEq).1 fresh)

end

end DemandTypingInferenceCompletenessPatternCtorCapComplete
end TypePM
