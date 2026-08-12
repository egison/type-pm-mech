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

private theorem setOrigins_append_local (ledger : CapabilityOriginLedger)
    (left right : List CapVar) (origin : CapabilityOrigin) :
    ledger.setOrigins (left ++ right) origin =
      (ledger.setOrigins right origin).setOrigins left origin := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, CapabilityOriginLedger.setOrigins]
      rw [induction]

private theorem markCapRange_trans_local
    (ledger : CapabilityOriginLedger)
    (q middle final : InferenceBase.FreshSupply)
    (front : SupplyExtends q middle) (back : SupplyExtends middle final) :
    DDLedger.markCapRange (DDLedger.markCapRange ledger q middle)
        middle final = DDLedger.markCapRange ledger q final := by
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
    setOrigins_append_local]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro offset membership
  simp only [Function.comp_apply]
  congr 1
  omega

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

/-- The shared-result allocator preserves traversal correspondence at its
whole structural capability range. -/
noncomputable def TraversalStateCorrespondence.freshPatternCtorAssignments
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (origin : ConstraintOrigin) (variables : List TypePM.TyVar) :
    let allocated := Inference.freshPatternCtorAssignments origin variables state
    TraversalStateCorrespondence allocated.2.supply S
      (DDLedger.markCapRange ledger q allocated.2.supply) allocated.2 := by
  induction variables generalizing q ledger state with
  | nil =>
      simpa [Inference.freshPatternCtorAssignments, DDLedger.markCapRange,
        CapabilityOriginLedger.setOrigins, before.supply_eq] using before
  | cons varId variables induction =>
      let middle := (state.freshCap origin).2
      let middleQ := { q with nextCap := q.nextCap + 1 }
      let middleBefore :=
        DemandTypingInferenceCompletenessPatternCtorCapability.TraversalStateCorrespondence.freshCap
          before origin
      let tail := induction middleBefore
      have front : SupplyExtends q middleQ := SupplyExtends.bumpCap q 1
      have allocationExact := freshPatternCtorAssignments_complete_exact
        origin variables middle
      have back : SupplyExtends middleQ
          (Inference.freshPatternCtorAssignments origin variables middle).2.supply := by
        rw [allocationExact.2.1]
        simpa [middle, middleQ, InferState.freshCap,
          InferenceBase.freshCapMeta, InferState.recordEvent,
          before.supply_eq] using
          SupplyExtends.patternCtorAssignments variables (q := middleQ)
      simpa only [Inference.freshPatternCtorAssignments, middle] using
        (show TraversalStateCorrespondence
          (Inference.freshPatternCtorAssignments origin variables middle).2.supply S
          (DDLedger.markCapRange ledger q
            (Inference.freshPatternCtorAssignments origin variables middle).2.supply)
          (Inference.freshPatternCtorAssignments origin variables middle).2 from by
            rw [← markCapRange_trans_local ledger q middleQ
              (Inference.freshPatternCtorAssignments origin variables middle).2.supply
              front back]
            simpa [middleBefore, middleQ, middle,
              DDLedger.markCapRange, DDLedger.markFreshCap,
              CapabilityOriginLedger.markStructuralFlexible,
              CapabilityOriginLedger.setOrigins, before.supply_eq] using tail)

/-- A list of identical optional capabilities is pointwise bisimilar under an
arbitrary traversal relation. -/
theorem OptionalCapListBisimulation.same
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    (relation : StateBisimulation ledger S state) :
    ∀ demands, OptionalCapListBisimulation relation demands demands
  | [] => .nil
  | none :: tail => .none (OptionalCapListBisimulation.same relation tail)
  | some capability :: tail => .some (CapBisimulation.same relation capability)
      (OptionalCapListBisimulation.same relation tail)

theorem CapListBisimulation.appendCapability
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarative executable : List Cap}
    {declarativeCapability executableCapability : Cap}
    (children : CapListBisimulation relation declarative executable)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability) :
    CapListBisimulation relation
      (declarative ++ [declarativeCapability])
      (executable ++ [executableCapability]) := by
  induction children with
  | nil => exact .cons capability .nil
  | cons head tail induction => exact .cons head induction

theorem CapListBisimulation.length_eq_local
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarative executable : List Cap}
    (children : CapListBisimulation relation declarative executable) :
    declarative.length = executable.length := by
  induction children with
  | nil => rfl
  | cons _ _ induction => exact congrArg Nat.succ induction

private theorem Cap.applyRenList_append_local (rename : CapVar → CapVar) :
    ∀ left right,
      Cap.applyRenList rename (left ++ right) =
        Cap.applyRenList rename left ++ Cap.applyRenList rename right
  | [], _ => rfl
  | _ :: _, _ => by
      simp only [List.cons_append, Cap.applyRenList]
      rw [Cap.applyRenList_append_local]

private theorem Cap.length_applyRenList_local (rename : CapVar → CapVar) :
    ∀ capabilities,
      (Cap.applyRenList rename capabilities).length = capabilities.length
  | [] => rfl
  | _ :: tail => by
      simp only [Cap.applyRenList, List.length_cons, Nat.succ.injEq]
      exact Cap.length_applyRenList_local rename tail

mutual

private theorem Cap.applyRen_boundedBy_of_images
    (rename : CapVar → CapVar) (q : InferenceBase.FreshSupply) :
    ∀ capability : Cap,
      (∀ varId ∈ capability.fcv, (rename varId).id < q.nextCap) →
      (capability.applyRen rename).BoundedBy q
  | .any, _ => by intro varId membership; exact nomatch membership
  | .var source, bounded => by
      intro varId membership
      simp only [Cap.applyRen, Cap.fcv, List.mem_singleton] at membership
      subst varId
      exact bounded source (by simp [Cap.fcv])
  | .skolem _, _ => by intro varId membership; exact nomatch membership
  | .con name children, bounded => by
      intro varId membership
      simp only [Cap.applyRen, Cap.fcv] at membership
      exact Cap.applyRenList_boundedBy_of_images rename q children bounded
        varId membership
  | .prod components, bounded => by
      intro varId membership
      simp only [Cap.applyRen, Cap.fcv] at membership
      exact Cap.applyRenList_boundedBy_of_images rename q components bounded
        varId membership

private theorem Cap.applyRenList_boundedBy_of_images
    (rename : CapVar → CapVar) (q : InferenceBase.FreshSupply) :
    ∀ capabilities : List Cap,
      (∀ varId ∈ Cap.fcvList capabilities,
        (rename varId).id < q.nextCap) →
      ∀ varId ∈ Cap.fcvList (Cap.applyRenList rename capabilities),
        varId.id < q.nextCap
  | [], _, varId, membership => nomatch membership
  | capability :: tail, bounded, varId, membership => by
      simp only [Cap.applyRenList, Cap.fcvList, List.mem_append] at membership
      rcases membership with inHead | inTail
      · exact Cap.applyRen_boundedBy_of_images rename q capability
          (fun source sourceMem => bounded source (by
            simp only [Cap.fcvList, List.mem_append]
            exact Or.inl sourceMem)) varId inHead
      · exact Cap.applyRenList_boundedBy_of_images rename q tail
          (fun source sourceMem => bounded source (by
            simp only [Cap.fcvList, List.mem_append]
            exact Or.inr sourceMem)) varId inTail

end

/-- Constructor compatibility transfers through one final state
bisimulation. -/
theorem capCompatible_bisimulation
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable}
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarativeChildren executableChildren : List Cap}
    {declarativeCapability executableCapability : Cap}
    (children : CapListBisimulation relation declarativeChildren
      executableChildren)
    (capability : CapBisimulation relation declarativeCapability
      executableCapability)
    (compatible : entry.CapCompatible
      (declarativeChildren.map fun child => child.apply S.cap)
      (declarativeCapability.apply S.cap)) :
    entry.CapCompatible
      (executableChildren.map fun child =>
        child.apply state.prevailing.cap)
      (executableCapability.apply state.prevailing.cap) := by
  let allRelated :=
    DemandTypingInferenceCompletenessPatternCtorCapComplete.CapListBisimulation.appendCapability
      children capability
  obtain ⟨rename, resolved⟩ := allRelated.executableResolved_eq_applyRen
  simp only [List.map_append, List.map_singleton] at resolved
  rw [Cap.applyRenList_append_local] at resolved
  have lengths : executableChildren.length =
      (Cap.applyRenList rename
        (declarativeChildren.map fun child => child.apply S.cap)).length := by
    rw [Cap.length_applyRenList_local]
    simp only [List.length_map]
    exact (DemandTypingInferenceCompletenessPatternCtorCapComplete.CapListBisimulation.length_eq_local
      children).symm
  have parts := List.append_inj resolved (by simpa only [List.length_map] using lengths)
  have moved := compatible.applyRen rename
  rw [parts.1]
  have resultEq : executableCapability.apply state.prevailing.cap =
      (declarativeCapability.apply S.cap).applyRen rename := by
    simpa [Cap.applyRenList] using (List.cons.inj parts.2).1
  rw [resultEq]
  exact moved

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

theorem projectedSkeleton_complete_result_bounded
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
    (projectedSkeleton_complete (constraintOrigin := constraintOrigin)
      (before := before) children declarativeChildrenBounded projection
      freshened).result.1.BoundedBy q' := by
  let bundle := Ty.matcher (.prod declarativeChildren) .unit
  let localMap := StateBisimulation.reverseLocalRenamingOn_image
    before.prevailing bundle
  let rename := localMap.capImage
  let run := projectedSkeleton_complete (constraintOrigin := constraintOrigin)
    (before := before) children declarativeChildrenBounded projection freshened
  change run.result.1.BoundedBy q'
  have executableProjection :=
    (projectSignature_success_scoped before children
      declarativeChildrenBounded projection).1
  have capabilityEq : run.result.1 = capability.applyRen rename := by
    have success := run.success
    simp only [executableProjection, Option.bind_eq_bind, Option.bind] at success
    have renamedFresh := freshenSkeletonSupply_applyRen
      signature.observability rename projected q capability q'
      (reverseChildRenaming_freshAbove before declarativeChildrenBounded)
      freshened
    have renamedFreshAtState : freshenSkeletonSupply signature.observability
        (projected.applyRen rename) state.supply =
        some (capability.applyRen rename, q') := by
      simpa [before.supply_eq] using renamedFresh
    let exactRun := freshenSkeleton_complete_exact
      (origin := constraintOrigin) renamedFreshAtState
    let final := Classical.choose exactRun
    have executableFresh := (Classical.choose_spec exactRun).1
    have pairEq := Option.some.inj (executableFresh.symm.trans success)
    exact (congrArg Prod.fst pairEq).symm
  rw [capabilityEq]
  apply Cap.applyRen_boundedBy_of_images
  intro varId membership
  have rawBounded := (DDPatternCtorCap.boundedBy
    (.project projection freshened) before.declarative_bounded
    declarativeChildrenBounded).1 varId membership
  by_cases below : varId.id < q.nextCap
  · have origin := freshenSkeletonSupply_fcv_origin freshened varId membership
    have projectedSource : varId ∈ projected.fcv := by
      rcases origin with source | fresh
      · exact source
      · exact False.elim ((Nat.not_le_of_lt below) fresh)
    have projectedChild := Projection.projectSignature_fcv projection
      projectedSource
    rw [Shape.fcvList_map_ofCap] at projectedChild
    obtain ⟨resolved, resolvedMem, varMem⟩ :=
      Cap.mem_fcvList_split projectedChild
    obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp resolvedMem
    have scope : varId ∈ (S.apply bundle).fcv := by
      simp only [bundle, Subst.apply_matcher, Subst.apply_unit, Ty.fcv,
        List.mem_append, List.not_mem_nil, or_false]
      change varId ∈ Cap.fcvList (Cap.applyList S.cap declarativeChildren)
      rw [Cap.applyList_eq_map]
      exact Cap.mem_fcvList_of_mem_local
        (List.mem_map.mpr ⟨child, childMem, rfl⟩) varMem
    have imageEq := localMap.cap_forward scope
    have imageBound := before.reverse_bounded.capImagesBounded varId below
    rw [imageEq] at imageBound
    have : (localMap.capImage varId).id < q'.nextCap :=
      (imageBound.mono (SupplyExtends.freshenSkeleton freshened)) _
        (by simp [Cap.fcv])
    exact this
  · have fixed := reverseChildRenaming_freshAbove before
      declarativeChildrenBounded varId (Nat.le_of_not_lt below)
    rw [show rename varId = varId from fixed]
    exact rawBounded

/-! ## Fallback completion -/

/-- Replay allocation and field-demand alignment, then reuse the common
projected-skeleton completion at the aligned cut. -/
noncomputable def fallback_complete
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {constraintOrigin : ConstraintOrigin}
    {declarativeChildren executableChildren : List Cap}
    {q q' : InferenceBase.FreshSupply} {S S₁ : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {resultVariables : List TypePM.TyVar}
    {demands : List (Option Cap)} {projected : Shape.Evidence}
    {capability : Cap}
    (before : TraversalStateCorrespondence q S ledger state)
    (children : CapListBisimulation before.prevailing declarativeChildren
      executableChildren)
    (declarativeChildrenBounded : ∀ child ∈ declarativeChildren,
      child.BoundedBy q)
    (executableChildrenBounded : ∀ child ∈ executableChildren,
      child.BoundedBy q)
    (projectionMiss : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S.cap).map
        Shape.ofCap) = none)
    (resultVars : Projection.relevantVars signature.observability
      (Projection.targetVars entry.projection.resultType)
      entry.projection.resultType = some resultVariables)
    (fieldDemands : patternCtorFieldDemands signature.observability
      resultVariables.eraseDups
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).1
      entry.projection.fieldTypes = some demands)
    (aligned : DDAlignCtorCapsWithLedger
      (DDLedger.markCapRange ledger q
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
      S declarativeChildren demands S₁)
    (projectionHit : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S₁.cap).map
        Shape.ofCap) = some projected)
    (freshened : freshenSkeletonSupply signature.observability projected
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 =
        some (capability, q')) :
    BoundedPatternCtorCapRunCompletion before
      (solvePatternCtorCapability signature entry constraintOrigin
        executableChildren state) q' S₁
      (DDLedger.markCapRange
        (DDLedger.markCapRange ledger q
          (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 q')
      capability := by
  let variables := resultVariables.eraseDups
  let qA := (patternCtorAssignmentsSupply variables q).2
  let allocation := freshPatternCtorAssignments constraintOrigin variables state
  have allocationExact := freshPatternCtorAssignments_complete_exact
    constraintOrigin variables state
  have assignmentsEq : allocation.1 =
      (patternCtorAssignmentsSupply variables q).1 := by
    simpa [allocation, before.supply_eq] using allocationExact.1
  have allocationSupply : allocation.2.supply = qA := by
    simpa [allocation, qA, before.supply_eq] using allocationExact.2.1
  have allocationLedger : allocation.2.capabilityOrigins =
      DDLedger.markCapRange state.capabilityOrigins q qA := by
    calc
      allocation.2.capabilityOrigins =
          DDLedger.markCapRange state.capabilityOrigins state.supply
            allocation.2.supply := allocationExact.2.2.2
      _ = DDLedger.markCapRange state.capabilityOrigins q qA := by
        rw [before.supply_eq, allocationSupply]
  let allocationBefore :=
    DemandTypingInferenceCompletenessPatternCtorCapComplete.TraversalStateCorrespondence.freshPatternCtorAssignments
      before constraintOrigin variables
  let allocationTransition :=
    DemandTypingInferenceCompletenessFixMatcher.TraversalStateCorrespondence.markCapRangeExtension
      before (SupplyExtends.patternCtorAssignments variables (q := q))
      allocationSupply allocationExact.2.2.1 allocationLedger
  let allocationBeforeAtQA : TraversalStateCorrespondence qA S
      (DDLedger.markCapRange ledger q qA) allocation.2 :=
    { supply_eq := allocationSupply
      prevailing := allocationTransition.after
      declarative_bounded := before.declarative_bounded.mono
        (SupplyExtends.patternCtorAssignments variables (q := q))
      executable_bounded := by
        rw [allocationExact.2.2.1]
        exact before.executable_bounded.mono
          (SupplyExtends.patternCtorAssignments variables (q := q))
      forward_bounded := before.forward_bounded.mono
        (SupplyExtends.patternCtorAssignments variables (q := q))
      reverse_bounded := before.reverse_bounded.mono
        (SupplyExtends.patternCtorAssignments variables (q := q))
      ledger_below := by
        rw [← allocationSupply]
        exact allocationBefore.ledger_below
      executable_ledger_below := by
        rw [← allocationSupply]
        exact allocationBefore.executable_ledger_below
      protected_origins := allocationBefore.protected_origins
      protected_below := allocationBefore.protected_below
      allocated_recorded := allocationBefore.allocated_recorded
      protected_safe := allocationBefore.protected_safe }
  have childrenAtAllocation : CapListBisimulation
      allocationBeforeAtQA.prevailing declarativeChildren executableChildren :=
    by
      have moved := BisimulationExtension.transportCapList
        allocationTransition children
      exact moved
  have declarativeDemandsBounded : ∀ demand ∈ demands, ∀ cap,
      demand = some cap → cap.BoundedBy qA := by
    intro demand membership cap equation varId varMem
    exact patternCtorAssignmentsSupply_fcv variables q varId
      (patternCtorFieldDemands_fcv fieldDemands demand membership cap equation
        varMem)
  have executableDemandsBounded : ∀ demand ∈ demands, ∀ cap,
      demand = some cap → cap.BoundedBy qA := declarativeDemandsBounded
  let alignment := ddAlignCtorCapsWithLedger_complete
    (origin := constraintOrigin) allocationBeforeAtQA childrenAtAllocation
    (OptionalCapListBisimulation.same allocationBeforeAtQA.prevailing demands)
    (fun child mem => (declarativeChildrenBounded child mem).mono
      (SupplyExtends.patternCtorAssignments variables (q := q)))
    declarativeDemandsBounded
    (fun child mem => (executableChildrenBounded child mem).mono
      (SupplyExtends.patternCtorAssignments variables (q := q)))
    executableDemandsBounded aligned
  let suffix := projectedSkeleton_complete
    (constraintOrigin := constraintOrigin) (before := alignment.completion)
    (BisimulationExtension.transportCapList alignment.transition
      childrenAtAllocation)
    (fun child mem => (declarativeChildrenBounded child mem).mono
      (SupplyExtends.patternCtorAssignments variables (q := q)))
    projectionHit freshened
  let combinedTransition := allocationTransition.seq
    (alignment.transition.seq suffix.transition)
  have executableMiss := children.projectSignature_miss projectionMiss
  let completed : PatternCtorCapRunCompletion before
      (solvePatternCtorCapability signature entry constraintOrigin
        executableChildren state) q' S₁
      (DDLedger.markCapRange
        (DDLedger.markCapRange ledger q qA) qA q') capability := by
    refine
      { result := suffix.result
        success := ?_
        transition := combinedTransition
        correspondence := suffix.correspondence
        prevailing_eq := ?_
        capability := ?_ }
    · unfold solvePatternCtorCapability
      simp only
      rw [show Projection.projectSignature entry.projection
        ((executableChildren.map fun capability =>
          capability.apply state.prevailing.cap).map Shape.ofCap) = none from
        executableMiss]
      rw [show Projection.relevantVars signature.observability
        (Projection.targetVars entry.projection.resultType)
        entry.projection.resultType = some resultVariables from resultVars]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [show freshPatternCtorAssignments constraintOrigin
        resultVariables.eraseDups state = allocation by rfl]
      rw [assignmentsEq]
      rw [fieldDemands]
      let continuation : Option InferState → Option (Cap × InferState) :=
        fun candidate => do
          let alignedState ← candidate
          let projected ← Projection.projectSignature entry.projection
            ((executableChildren.map fun child =>
              child.apply alignedState.prevailing.cap).map Shape.ofCap)
          freshenSkeleton signature.observability constraintOrigin projected
            alignedState
      change continuation
        (alignPatternCtorCapabilities allocation.2 constraintOrigin
          executableChildren demands) = some suffix.result
      calc
        _ = continuation (some alignment.result) := congrArg continuation
          alignment.success
        _ = some suffix.result := suffix.success
    · exact suffix.prevailing_eq
    · exact suffix.capability
  exact ⟨completed, projectedSkeleton_complete_result_bounded
    (BisimulationExtension.transportCapList alignment.transition
      childrenAtAllocation)
    (fun child mem => (declarativeChildrenBounded child mem).mono
      (SupplyExtends.patternCtorAssignments variables (q := q)))
    projectionHit freshened⟩

/-! ## Public package -/

/-- Constructor-capability inference is complete for every DD derivation and
its intrinsic origin certificate. -/
noncomputable def patternCtorCapCompletenessPackage
    (signature : FrozenSig) :
    PatternCtorCapCompletenessPackage signature where
  complete := by
    intro entry constraintOrigin declarativeChildren executableChildren
      capability q q' S S' ledger ledger' state raw rawOrigin before children
      declarativeChildrenBounded executableChildrenBounded compatibleCheck
    cases rawOrigin with
    | project projection freshened =>
        let projectedRun := projectedSkeleton_complete
          (constraintOrigin := constraintOrigin) (before := before) children
          declarativeChildrenBounded projection freshened
        have executableProjection :=
          (projectSignature_success_scoped before children
            declarativeChildrenBounded projection).1
        have solverSuccess : solvePatternCtorCapability signature entry
            constraintOrigin executableChildren state =
            some projectedRun.result := by
          have directSuccess := projectedRun.success
          simp only [executableProjection, Option.bind_eq_bind, Option.bind]
            at directSuccess
          unfold solvePatternCtorCapability
          simp only
          split <;> rename_i equation
          · have eq := Option.some.inj
                (equation.symm.trans executableProjection)
            subst_vars
            exact directSuccess
          · rw [equation] at executableProjection
            contradiction
        let rawRun : PatternCtorCapRunCompletion before
            (solvePatternCtorCapability signature entry constraintOrigin
              executableChildren state) q' S
            (DDLedger.markCapRange ledger q q') capability := by
          exact { projectedRun with success := solverSuccess }
        have rawCapabilityBounded :=
          DDPatternCtorCap.boundedBy (.project projection freshened)
            before.declarative_bounded
            declarativeChildrenBounded |>.1
        let bounded : BoundedPatternCtorCapRunCompletion before
            (solvePatternCtorCapability signature entry constraintOrigin
              executableChildren state) q' S
            (DDLedger.markCapRange ledger q q') capability :=
          ⟨rawRun, projectedSkeleton_complete_result_bounded children
            declarativeChildrenBounded projection freshened⟩
        have finalChildren := BisimulationExtension.transportCapList
          rawRun.transition children
        have compatibleSemantic := capCompatible_bisimulation finalChildren
          rawRun.capability (capCompatibleCheck_sound compatibleCheck)
        refine ⟨⟨bounded, ?_⟩⟩
        exact capCompatibleCheck_complete compatibleSemantic
    | fallback projectionMiss resultVars fieldDemands aligned projectionHit
        freshened =>
        let bounded := fallback_complete
          (constraintOrigin := constraintOrigin) before children
          declarativeChildrenBounded executableChildrenBounded projectionMiss
          resultVars fieldDemands aligned projectionHit freshened
        have finalChildren := BisimulationExtension.transportCapList
          bounded.run.transition children
        have compatibleSemantic := capCompatible_bisimulation finalChildren
          bounded.run.capability (capCompatibleCheck_sound compatibleCheck)
        refine ⟨⟨bounded, ?_⟩⟩
        exact capCompatibleCheck_complete compatibleSemantic

end DemandTypingInferenceCompletenessPatternCtorCapComplete
end TypePM
