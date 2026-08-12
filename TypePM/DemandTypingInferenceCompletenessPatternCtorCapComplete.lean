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
open DemandTypingInferenceCompletenessContext

private theorem Cap.mem_fcvList_of_mem_local
    {capability : Cap} {capabilities : List Cap} {varId : CapVar}
    (capabilityMem : capability ∈ capabilities)
    (varMem : varId ∈ capability.fcv) :
    varId ∈ Cap.fcvList capabilities := by
  induction capabilities with
  | nil => contradiction
  | cons head tail induction =>
      simp only [List.mem_cons] at capabilityMem
      simp only [Cap.fcvList, List.mem_append]
      rcases capabilityMem with rfl | inTail
      · exact Or.inl varMem
      · exact Or.inr (induction inTail)

private theorem StateBisimulation.eq_of_forward_reverse
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (left right : StateBisimulation ledger declarative state)
    (forward : left.forward = right.forward)
    (reverse : left.reverse = right.reverse) : left = right := by
  cases left
  cases right
  simp_all

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

/-! ## Freshened projection transport -/

/-- Freshening a projected skeleton preserves the capability relation: old
leaves use the scoped child renaming, while newly allocated leaves are fixed
above the common supply cut. -/
theorem freshenedProjection_capBisimulation
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeChildren : List Cap} {projected : Shape.Evidence}
    {capability : Cap} {q' : InferenceBase.FreshSupply}
    (childrenBounded : ∀ child ∈ declarativeChildren, child.BoundedBy q)
    (projection : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S.cap).map
        Shape.ofCap) = some projected)
    (freshened : freshenSkeletonSupply signature.observability projected q =
      some (capability, q')) :
    let bundle := Ty.matcher (.prod declarativeChildren) .unit
    let localMap := StateBisimulation.reverseLocalRenamingOn_image
      before.prevailing bundle
    CapBisimulation before.prevailing capability
      (capability.applyRen localMap.capImage) := by
  dsimp only
  let bundle := Ty.matcher (.prod declarativeChildren) .unit
  let localMap := StateBisimulation.reverseLocalRenamingOn_image
    before.prevailing bundle
  let rename := localMap.capImage
  have origin := freshenSkeletonSupply_fcv_origin freshened
  have oldScope : ∀ varId ∈ capability.fcv,
      varId.id < q.nextCap → varId ∈ (S.apply bundle).fcv := by
    intro varId membership below
    rcases origin varId membership with source | fresh
    · have projectedSource := Projection.projectSignature_fcv projection source
      rw [Shape.fcvList_map_ofCap] at projectedSource
      obtain ⟨resolved, resolvedMem, varMem⟩ :=
        Cap.mem_fcvList_split projectedSource
      obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp resolvedMem
      have joined : varId ∈ Cap.fcvList
          (declarativeChildren.map fun child => child.apply S.cap) :=
        Cap.mem_fcvList_of_mem_local
          (List.mem_map.mpr ⟨child, childMem, rfl⟩) varMem
      simp only [bundle, Subst.apply_matcher, Subst.apply_unit, Ty.fcv,
        List.mem_append, List.not_mem_nil, or_false]
      change varId ∈ Cap.fcvList (Cap.applyList S.cap declarativeChildren)
      rw [Cap.applyList_eq_map]
      exact joined
    · exact False.elim ((Nat.not_le_of_lt below) fresh)
  have renameFresh : RenamingFreshAbove rename q :=
    reverseChildRenaming_freshAbove before childrenBounded
  have declarativeFixed : capability.apply S.cap = capability := by
    apply Cap.apply_eq_self_of_fcv_fixed
    intro varId membership
    by_cases below : varId.id < q.nextCap
    · exact before.prevailing.declarativeIdempotent.image_cap_fixed bundle
        varId (oldScope varId membership below)
    · exact before.declarative_bounded.capFixedAbove varId
        (Nat.le_of_not_lt below)
  have reverseRenamed : capability.apply before.prevailing.reverse.cap =
      capability.applyRen rename := by
    let post : Subst :=
      { cap := fun varId => .var (rename varId)
        target := fun varId => .var varId }
    let variablePost : VariablePost post :=
      { capVariable := fun varId => ⟨rename varId, rfl⟩ }
    have capRenEq : variablePost.capRen = rename := by
      funext varId
      have point := variablePost.capEquation varId
      change Cap.var (rename varId) = Cap.var (variablePost.capRen varId) at point
      exact (Cap.var.inj point).symm
    rw [← capRenEq, ← variablePost.applyCap_eq_applyRen]
    apply Cap.apply_eq_of_fcv_agree
    intro varId membership
    by_cases below : varId.id < q.nextCap
    · exact localMap.cap_forward (oldScope varId membership below)
    · change before.prevailing.reverse.cap varId = .var (rename varId)
      rw [DemandTypingInferenceCompletenessContext.StateBisimulation.reverse_capFixedAbove
        before.prevailing
        before.declarative_bounded before.executable_bounded varId
        (Nat.le_of_not_lt below), renameFresh varId (Nat.le_of_not_lt below)]
  have executableImage : state.prevailing.apply (.matcher capability .unit) =
      .matcher (capability.applyRen rename) .unit := by
    calc
      state.prevailing.apply (.matcher capability .unit) =
          before.prevailing.reverse.apply (S.apply
            (.matcher capability .unit)) := by
        rw [before.prevailing.reverseEquation, Subst.seq_apply]
      _ = .matcher (capability.apply before.prevailing.reverse.cap) .unit := by
        simp [declarativeFixed]
      _ = .matcher (capability.applyRen rename) .unit := by
        rw [reverseRenamed]
  have executableFixed :
      (capability.applyRen rename).apply state.prevailing.cap =
        capability.applyRen rename := by
    have idempotent := before.prevailing.executableIdempotent
      (.matcher capability .unit)
    rw [executableImage] at idempotent
    exact (Ty.matcher.inj idempotent).1
  constructor
  · simp only [Subst.apply_matcher, Subst.apply_unit, Ty.matcher.injEq,
      and_true]
    change capability.apply S.cap =
      ((capability.applyRen rename).apply state.prevailing.cap).apply
        before.prevailing.forward.cap
    rw [declarativeFixed, executableFixed]
    let post : Subst :=
      { cap := fun varId => .var (rename varId)
        target := fun varId => .var varId }
    let variablePost : VariablePost post :=
      { capVariable := fun varId => ⟨rename varId, rfl⟩ }
    have capRenEq : variablePost.capRen = rename := by
      funext varId
      have point := variablePost.capEquation varId
      change Cap.var (rename varId) = Cap.var (variablePost.capRen varId) at point
      exact (Cap.var.inj point).symm
    rw [← capRenEq, ← variablePost.applyCap_eq_applyRen]
    rw [← Cap.apply_comp]
    symm
    apply Cap.apply_eq_self_of_fcv_fixed
    intro varId membership
    change before.prevailing.forward.cap (rename varId) = .var varId
    by_cases below : varId.id < q.nextCap
    · exact localMap.cap_reverse (oldScope varId membership below)
    · rw [renameFresh varId (Nat.le_of_not_lt below)]
      exact DemandTypingInferenceCompletenessContext.StateBisimulation.forward_capFixedAbove
        before.prevailing
        before.declarative_bounded before.executable_bounded varId
        (Nat.le_of_not_lt below)
  · simp only [Subst.apply_matcher, Subst.apply_unit, Ty.matcher.injEq,
      and_true]
    change (capability.applyRen rename).apply state.prevailing.cap =
      (capability.apply S.cap).apply before.prevailing.reverse.cap
    rw [executableFixed, declarativeFixed]
    exact reverseRenamed.symm

/-! ## Direct projection completion -/

/-- Complete the common projected-skeleton suffix from a correspondence whose
child projection succeeds. -/
noncomputable def projectedSkeleton_complete
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {constraintOrigin : ConstraintOrigin}
    {declarativeChildren executableChildren : List Cap}
    {q q' : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {before : TraversalStateCorrespondence q S ledger state}
    {projected : Shape.Evidence} {capability : Cap}
    (children : CapListBisimulation before.prevailing declarativeChildren
      executableChildren)
    (declarativeChildrenBounded : ∀ child ∈ declarativeChildren,
      child.BoundedBy q)
    (projection : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S.cap).map
        Shape.ofCap) = some projected)
    (freshened : freshenSkeletonSupply signature.observability projected q =
      some (capability, q')) :
    PatternCtorCapRunCompletion before
      (do
        let executableProjected ← Projection.projectSignature entry.projection
          ((executableChildren.map fun child =>
            child.apply state.prevailing.cap).map Shape.ofCap)
        freshenSkeleton signature.observability constraintOrigin
          executableProjected state)
      q' S (DDLedger.markCapRange ledger q q') capability := by
  let bundle := Ty.matcher (.prod declarativeChildren) .unit
  let localMap := StateBisimulation.reverseLocalRenamingOn_image
    before.prevailing bundle
  let rename := localMap.capImage
  obtain ⟨executableProjection, freshAbove⟩ :=
    projectSignature_success_scoped before children declarativeChildrenBounded
      projection
  have renamedFresh := freshenSkeletonSupply_applyRen
    signature.observability rename projected q capability q' freshAbove
    freshened
  have renamedFreshAtState : freshenSkeletonSupply signature.observability
      (projected.applyRen rename) state.supply =
      some (capability.applyRen rename, q') := by
    simpa [before.supply_eq] using renamedFresh
  let exactRun := freshenSkeleton_complete_exact
    (origin := constraintOrigin) renamedFreshAtState
  let final := Classical.choose exactRun
  have exactFacts := Classical.choose_spec exactRun
  have executableFresh := exactFacts.1
  have supplyEq := exactFacts.2.1
  have prevailingEq := exactFacts.2.2.1
  have ledgerEq := exactFacts.2.2.2
  let rawCorrespondence := Classical.choice
    (DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.freshenSkeleton
      before executableFresh)
  let transition :=
    DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.markCapRangeExtension
      before (SupplyExtends.freshenSkeleton freshened) supplyEq prevailingEq
      (by simpa [before.supply_eq] using ledgerEq)
  let supplyExt := SupplyExtends.freshenSkeleton freshened
  let correspondenceAtFinal : TraversalStateCorrespondence q' S
      (DDLedger.markCapRange ledger q q') final :=
    { supply_eq := supplyEq
      prevailing := transition.after
      declarative_bounded := before.declarative_bounded.mono supplyExt
      executable_bounded := by
        rw [prevailingEq]
        exact before.executable_bounded.mono supplyExt
      forward_bounded := before.forward_bounded.mono supplyExt
      reverse_bounded := before.reverse_bounded.mono supplyExt
      ledger_below := by simpa [supplyEq] using rawCorrespondence.ledger_below
      executable_ledger_below := by
        simpa [supplyEq] using rawCorrespondence.executable_ledger_below
      protected_origins := rawCorrespondence.protected_origins
      protected_below := rawCorrespondence.protected_below
      allocated_recorded := rawCorrespondence.allocated_recorded
      protected_safe := rawCorrespondence.protected_safe }
  have capabilityRelated : CapBisimulation transition.after capability
      (capability.applyRen rename) := by
    have base := freshenedProjection_capBisimulation before
      declarativeChildrenBounded projection freshened
    constructor
    · rw [prevailingEq]
      simpa [transition,
        DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.markCapRangeExtension,
        rename, localMap, bundle, prevailingEq] using base.forward
    · rw [prevailingEq]
      simpa [transition,
        DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.markCapRangeExtension,
        rename, localMap, bundle, prevailingEq] using base.reverse
  refine
    { result := (capability.applyRen rename, final)
      success := ?_
      transition := transition
      correspondence := correspondenceAtFinal
      prevailing_eq := rfl
      capability := capabilityRelated }
  · simp only [executableProjection, Option.bind_eq_bind, Option.bind]
    change freshenSkeleton signature.observability constraintOrigin
      (projected.applyRen rename) state =
        some (capability.applyRen rename, final)
    exact executableFresh

end DemandTypingInferenceCompletenessPatternCtorCapComplete
end TypePM
