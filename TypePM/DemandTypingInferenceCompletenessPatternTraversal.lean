import TypePM.DemandTypingInferenceCompletenessTraversal
import TypePM.DemandTypingInferenceCompletenessDataBisimulation
import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal
import TypePM.DemandTypingInferenceCompletenessAlignmentFamilies

/-!
# Pattern traversal completeness packages

Pattern traversal returns more data than expression synthesis: a dual, a
monomorphic binding context, and, for primitive patterns, a list of holes.
This module packages those outputs under the same DD/executable state
bisimulation used by raw expression completeness.  It also supplies the
solver-independent constructors used by the mutual traversal proof.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternTraversal

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessAlignmentFamilies

/-! ## Compositional output relations -/

theorem DualListBisimulation.append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : List Dual}
    (leftRelated : DualListBisimulation relation left left')
    (rightRelated : DualListBisimulation relation right right') :
    DualListBisimulation relation (left ++ right) (left' ++ right') := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons head tail induction => exact .cons head induction

theorem MonoCtxBisimulation.append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : MonoCtx}
    (leftRelated : MonoCtxBisimulation relation left left')
    (rightRelated : MonoCtxBisimulation relation right right') :
    MonoCtxBisimulation relation (left ++ right) (left' ++ right') := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons target tail induction => exact .cons target induction

theorem TyListBisimulation.append
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : List Ty}
    (leftRelated : TyListBisimulation relation left left')
    (rightRelated : TyListBisimulation relation right right') :
    TyListBisimulation relation (left ++ right) (left' ++ right') := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons head tail induction => exact .cons head induction

theorem MonoCtxBisimulation.targets
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : MonoCtx}
    (related : MonoCtxBisimulation relation declarativeContext
      executableContext) :
    TyListBisimulation relation (declarativeContext.map fun entry => entry.2)
      (executableContext.map fun entry => entry.2) := by
  induction related with
  | nil => exact .nil
  | cons target tail induction => exact .cons target induction

theorem MonoCtxBisimulation.exportPayload
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : MonoCtx} {target : Ty}
    (related : MonoCtxBisimulation relation declarativeContext
      executableContext) :
    TyBisimulation relation
      (capabilityExportPayload []
        (target :: declarativeContext.map fun entry => entry.2))
      (capabilityExportPayload []
        (target :: executableContext.map fun entry => entry.2)) := by
  unfold capabilityExportPayload
  simp only [List.map_nil, List.nil_append]
  apply tyListBisimulation_prod
  exact .cons (relation.sameTarget target)
    (DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.targets
      related)

theorem namesDisjoint_of_bisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {left left' right right' : MonoCtx}
    (leftRelated : MonoCtxBisimulation relation left left')
    (rightRelated : MonoCtxBisimulation relation right right')
    (disjoint : ∀ name, name ∈ left.names → name ∉ right.names) :
    namesDisjoint left'.names right'.names = true := by
  rw [← leftRelated.names_eq, ← rightRelated.names_eq]
  exact (namesDisjoint_eq_true _ _).mpr disjoint

theorem admissiblePostBetween_markDualInstance_of_bounded
    {q : InferenceBase.FreshSupply}
    {source destination : CapabilityOriginLedger} {post : Subst}
    (between : AdmissiblePostBetween source destination post)
    (bounded : post.BoundedBy q)
    (sourceBelow : DDLedger.LedgerBelow q source) (scheme : DualScheme) :
    AdmissiblePostBetween
      (DDLedger.markDualInstance source q scheme)
      (DDLedger.markDualInstance destination q scheme) post := by
  exact admissiblePostBetween_setFreshRenameOnly_of_bounded between bounded
    sourceBelow (freshCapImages_above q scheme.capBinders)

theorem PatternCtxBisimulation.find?_complete
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : PatternCtx}
    (related : PatternCtxBisimulation relation declarativeContext
      executableContext) {name : String} {dual : Dual}
    (lookup : declarativeContext.find? name = some dual) :
    ∃ executableDual,
      executableContext.find? name = some executableDual ∧
        DualBisimulation relation dual executableDual := by
  induction related with
  | nil => simp [PatternCtx.find?] at lookup
  | @cons declarativeDual executableDual declarativeTail executableTail
      entryName head tail induction =>
      by_cases same : entryName = name
      · subst entryName
        simp [PatternCtx.find?] at lookup ⊢
        subst declarativeDual
        exact head
      · have tailLookup : declarativeTail.find? name = some dual := by
          simpa [PatternCtx.find?, same] using lookup
        rcases induction tailLookup with ⟨found, foundLookup, foundRelated⟩
        exact ⟨found, by simpa [PatternCtx.find?, same] using foundLookup,
          foundRelated⟩

theorem DualListBisimulation.prodCaps
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    (related : DualListBisimulation relation declarativeDuals
      executableDuals) :
    CapBisimulation relation (.prod (declarativeDuals.map Dual.cap))
      (.prod (executableDuals.map Dual.cap)) := by
  constructor
  · change declarative.apply (.matcher (.prod _) .unit) =
      relation.forward.apply
        (state.prevailing.apply (.matcher (.prod _) .unit))
    simp only [Subst.apply_matcher, Subst.apply_unit, Cap.apply]
    induction related with
    | nil => rfl
    | cons head tail ih =>
        have pointwise := head.cap.forward
        change Ty.matcher _ Ty.unit = Ty.matcher _ Ty.unit at pointwise
        injection pointwise with capEq
        injection ih with tailEq
        injection tailEq with tailListEq
        simp only [List.map_cons, Cap.apply, Cap.applyList]
        rw [capEq, tailListEq]
  · change state.prevailing.apply (.matcher (.prod _) .unit) =
      relation.reverse.apply
        (declarative.apply (.matcher (.prod _) .unit))
    simp only [Subst.apply_matcher, Subst.apply_unit, Cap.apply]
    induction related with
    | nil => rfl
    | cons head tail ih =>
        have pointwise := head.cap.reverse
        change Ty.matcher _ Ty.unit = Ty.matcher _ Ty.unit at pointwise
        injection pointwise with capEq
        injection ih with tailEq
        injection tailEq with tailListEq
        simp only [List.map_cons, Cap.apply, Cap.applyList]
        rw [capEq, tailListEq]

theorem DualListBisimulation.prodTargets
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    (related : DualListBisimulation relation declarativeDuals
      executableDuals) :
    TyBisimulation relation (.prod (declarativeDuals.map Dual.target))
      (.prod (executableDuals.map Dual.target)) := by
  apply tyListBisimulation_prod
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.target ih

theorem DualListBisimulation.targets
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    (related : DualListBisimulation relation declarativeDuals executableDuals) :
    TyListBisimulation relation (declarativeDuals.map Dual.target)
      (executableDuals.map Dual.target) := by
  induction related with
  | nil => exact .nil
  | cons head tail induction => exact .cons head.target induction

theorem DualListBisimulation.exportPayload
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeDuals executableDuals : List Dual}
    {declarativeBindings executableBindings : MonoCtx} {target : Ty}
    (duals : DualListBisimulation relation declarativeDuals executableDuals)
    (bindings : MonoCtxBisimulation relation declarativeBindings
      executableBindings) :
    TyBisimulation relation
      (capabilityExportPayload (declarativeDuals.map Dual.cap)
        (declarativeDuals.map Dual.target ++
          target :: declarativeBindings.map fun entry => entry.2))
      (capabilityExportPayload (executableDuals.map Dual.cap)
        (executableDuals.map Dual.target ++
          target :: executableBindings.map fun entry => entry.2)) := by
  unfold capabilityExportPayload
  apply tyListBisimulation_prod
  have caps : TyListBisimulation relation
      ((declarativeDuals.map Dual.cap).map fun capability =>
        .matcher capability .unit)
      ((executableDuals.map Dual.cap).map fun capability =>
        .matcher capability .unit) := by
    induction duals with
    | nil => exact .nil
    | cons head tail induction => exact .cons head.cap induction
  have targets :=
    DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.targets
      duals
  exact
    DemandTypingInferenceCompletenessPatternTraversal.TyListBisimulation.append
      caps
      (DemandTypingInferenceCompletenessPatternTraversal.TyListBisimulation.append
        targets (.cons (relation.sameTarget target)
          (DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.targets
            bindings)))

/-! ## Paired export freezing -/

/-- Export leaves selected from two related payloads correspond through the
forward residual.  This is the heterogeneous-payload form needed when a
recursive pattern traversal returns executable bindings that are merely
bisimilar to the DD bindings. -/
theorem StateBisimulation.forwardExportLeavesOfRelated
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (capImages : List CapVar) {declarativePayload executablePayload : Ty}
    (payload : TyBisimulation relation declarativePayload executablePayload) :
    ∀ varId,
      varId ∈ DDLedger.exportLeaves state.capabilityOrigins state.prevailing
        capImages executablePayload →
      ∃ image, relation.forward.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves ledger declarative capImages
          declarativePayload := by
  classical
  intro varId membership
  unfold DDLedger.exportLeaves at membership ⊢
  rcases List.mem_filter.mp membership with ⟨deduplicated, structural⟩
  have filtered : varId ∈
      (capImages.flatMap fun image => (state.prevailing.cap image).fcv).filter
        (fun image => image ∈
          (state.prevailing.apply executablePayload).fcv) := by
    simpa using deduplicated
  rcases List.mem_filter.mp filtered with ⟨imageLeaf, payloadLeaf⟩
  have payloadLeafProp : varId ∈
      (state.prevailing.apply executablePayload).fcv :=
    of_decide_eq_true payloadLeaf
  have structuralProp : state.capabilityOrigins.originOf varId =
      .structuralFlexible := of_decide_eq_true structural
  rcases List.mem_flatMap.mp imageLeaf with
    ⟨binder, binderMem, binderLeaf⟩
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn_image
      relation executablePayload
  let image := localMap.capImage varId
  have forwardImage : relation.forward.cap varId = .var image :=
    localMap.cap_forward payloadLeafProp
  have reverseImage : relation.reverse.cap image = .var varId :=
    localMap.cap_reverse payloadLeafProp
  have imageInBinder : image ∈ (declarative.cap binder).fcv := by
    have equation := congrArg (fun substitution : Subst =>
      substitution.cap binder) relation.forwardEquation
    change declarative.cap binder =
      (state.prevailing.cap binder).apply relation.forward.cap at equation
    rw [equation, Unification.Cap.fcv_apply]
    apply List.mem_flatMap.mpr
    refine ⟨varId, binderLeaf, ?_⟩
    rw [forwardImage]
    simp [Cap.fcv]
  have imageInPayload : image ∈ (declarative.apply declarativePayload).fcv := by
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
        localMap (state.prevailing.apply executablePayload)
        (fun _ member => member) (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv
        localMap (state.prevailing.apply executablePayload)
    rw [payload.forward, pure, freeVars]
    exact List.mem_map.mpr ⟨varId, payloadLeafProp, rfl⟩
  have imageStructural : ledger.originOf image = .structuralFlexible := by
    cases destinationOrigin : ledger.originOf image with
    | structuralFlexible => rfl
    | rigid =>
        have reverseAt := relation.ledgerBisimulation.reverseBetween.cap image
        simp only [destinationOrigin] at reverseAt
        have equal : image = varId := by
          rw [reverseImage] at reverseAt
          exact Cap.var.inj reverseAt.1.symm
        have rigidSource := reverseAt.2
        rw [equal, structuralProp] at rigidSource
        contradiction
    | renameOnly =>
        have reverseAt := relation.ledgerBisimulation.reverseBetween.cap image
        simp only [destinationOrigin] at reverseAt
        rcases reverseAt with ⟨actualImage, equation, safe⟩
        rw [reverseImage] at equation
        have equal : actualImage = varId := (Cap.var.inj equation).symm
        subst actualImage
        exact False.elim (safe structuralProp)
  refine ⟨image, forwardImage, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by exact decide_eq_true imageStructural⟩
  simp only [List.mem_eraseDups]
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr ⟨binder, binderMem, imageInBinder⟩,
    decide_eq_true imageInPayload⟩

/-- Reverse counterpart of `forwardExportLeavesOfRelated`. -/
theorem StateBisimulation.reverseExportLeavesOfRelated
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (capImages : List CapVar) {declarativePayload executablePayload : Ty}
    (payload : TyBisimulation relation declarativePayload executablePayload) :
    ∀ varId,
      varId ∈ DDLedger.exportLeaves ledger declarative capImages
        declarativePayload →
      ∃ image, relation.reverse.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves state.capabilityOrigins state.prevailing
          capImages executablePayload := by
  classical
  intro varId membership
  unfold DDLedger.exportLeaves at membership ⊢
  rcases List.mem_filter.mp membership with ⟨deduplicated, structural⟩
  have filtered : varId ∈
      (capImages.flatMap fun image => (declarative.cap image).fcv).filter
        (fun image => image ∈ (declarative.apply declarativePayload).fcv) := by
    simpa using deduplicated
  rcases List.mem_filter.mp filtered with ⟨imageLeaf, payloadLeaf⟩
  have payloadLeafProp : varId ∈ (declarative.apply declarativePayload).fcv :=
    of_decide_eq_true payloadLeaf
  have structuralProp : ledger.originOf varId = .structuralFlexible :=
    of_decide_eq_true structural
  rcases List.mem_flatMap.mp imageLeaf with
    ⟨binder, binderMem, binderLeaf⟩
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
      relation declarativePayload
  let image := localMap.capImage varId
  have reverseImage : relation.reverse.cap varId = .var image :=
    localMap.cap_forward payloadLeafProp
  have forwardImage : relation.forward.cap image = .var varId :=
    localMap.cap_reverse payloadLeafProp
  have imageInBinder : image ∈ (state.prevailing.cap binder).fcv := by
    have equation := congrArg (fun substitution : Subst =>
      substitution.cap binder) relation.reverseEquation
    change state.prevailing.cap binder =
      (declarative.cap binder).apply relation.reverse.cap at equation
    rw [equation, Unification.Cap.fcv_apply]
    apply List.mem_flatMap.mpr
    refine ⟨varId, binderLeaf, ?_⟩
    rw [reverseImage]
    simp [Cap.fcv]
  have imageInPayload : image ∈
      (state.prevailing.apply executablePayload).fcv := by
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure
        localMap (declarative.apply declarativePayload)
        (fun _ member => member) (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv
        localMap (declarative.apply declarativePayload)
    rw [payload.reverse, pure, freeVars]
    exact List.mem_map.mpr ⟨varId, payloadLeafProp, rfl⟩
  have imageStructural :
      state.capabilityOrigins.originOf image = .structuralFlexible := by
    cases destinationOrigin : state.capabilityOrigins.originOf image with
    | structuralFlexible => rfl
    | rigid =>
        have forwardAt := relation.ledgerBisimulation.forwardBetween.cap image
        simp only [destinationOrigin] at forwardAt
        have equal : image = varId := by
          rw [forwardImage] at forwardAt
          exact Cap.var.inj forwardAt.1.symm
        have rigidSource := forwardAt.2
        rw [equal, structuralProp] at rigidSource
        contradiction
    | renameOnly =>
        have forwardAt := relation.ledgerBisimulation.forwardBetween.cap image
        simp only [destinationOrigin] at forwardAt
        rcases forwardAt with ⟨declarativeImage, equation, safe⟩
        rw [forwardImage] at equation
        have equal : declarativeImage = varId := (Cap.var.inj equation).symm
        subst declarativeImage
        exact False.elim (safe structuralProp)
  refine ⟨image, reverseImage, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by exact decide_eq_true imageStructural⟩
  simp only [List.mem_eraseDups]
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr ⟨binder, binderMem, imageInBinder⟩,
    decide_eq_true imageInPayload⟩

/-- Selective freezing with distinct but related DD and executable payloads. -/
def TraversalStateCorrespondence.freezeCapabilityExportRelated
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (capImages : List CapVar) {declarativePayload executablePayload : Ty}
    (payload : TyBisimulation relation.prevailing declarativePayload
      executablePayload) :
    TraversalStateCorrespondence q declarative
      (DDLedger.freezeExport ledger declarative capImages declarativePayload)
      (state.freezeCapabilityExport capImages executablePayload) := by
  let afterLedger := DDLedger.freezeExport ledger declarative capImages
    declarativePayload
  let afterState := state.freezeCapabilityExport capImages executablePayload
  have ledgerTransport : LedgerBisimulation afterLedger
      afterState.capabilityOrigins relation.prevailing.forward
      relation.prevailing.reverse := by
    rw [InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
    constructor
    · unfold DDLedger.freezeExport
      constructor
      exact relation.prevailing.ledgerBisimulation.forwardBetween.cap.freezeSelected
        (fun varId membership =>
          DDLedger.exportLeaves_origin ledger declarative capImages
            declarativePayload varId membership)
        (DemandTypingInferenceCompletenessPatternTraversal.StateBisimulation.forwardExportLeavesOfRelated
          relation.prevailing capImages payload)
    · unfold DDLedger.freezeExport
      constructor
      exact relation.prevailing.ledgerBisimulation.reverseBetween.cap.freezeSelected
        (fun varId membership =>
          DDLedger.exportLeaves_origin state.capabilityOrigins state.prevailing
            capImages executablePayload varId membership)
        (DemandTypingInferenceCompletenessPatternTraversal.StateBisimulation.reverseExportLeavesOfRelated
          relation.prevailing capImages payload)
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
      ledger_below := DDLedger.LedgerBelow.freezeExport declarative capImages
        declarativePayload relation.ledger_below
      executable_ledger_below := by
        simpa [afterState,
          InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
          using DDLedger.LedgerBelow.freezeExport state.prevailing capImages
            executablePayload relation.executable_ledger_below
      protected_origins := relation.protected_origins.freezeCapabilityExport
        capImages executablePayload
      protected_below :=
        relation.protected_below.freezeCapabilityExport_of_ledgerBelow (by
          rw [relation.supply_eq]
          exact relation.executable_ledger_below) capImages executablePayload
      allocated_recorded := relation.allocated_recorded.freezeCapabilityExport
        capImages executablePayload }

def TraversalStateCorrespondence.freezeCapabilityExportRelatedExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (capImages : List CapVar) {declarativePayload executablePayload : Ty}
    (payload : TyBisimulation relation.prevailing declarativePayload
      executablePayload) :
    BisimulationExtension relation.prevailing
      (DDLedger.freezeExport ledger declarative capImages declarativePayload)
      declarative (state.freezeCapabilityExport capImages executablePayload) where
  after :=
    (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelated
      relation capImages payload).prevailing
  transportTy := by
    intro declarativeTarget executableTarget related
    exact ⟨related.forward, related.reverse⟩

/-! ## One structural capability allocation -/

def TraversalStateCorrespondence.freshCapExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before.prevailing (DDLedger.markFreshCap ledger q)
      declarative (state.freshCap origin).2 := by
  let q' : InferenceBase.FreshSupply :=
    { q with nextCap := q.nextCap + 1 }
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
      transportTy := ?_ }
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

def TraversalStateCorrespondence.freshCap
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    TraversalStateCorrespondence
      { q with nextCap := q.nextCap + 1 } declarative
      (DDLedger.markFreshCap ledger q) (state.freshCap origin).2 := by
  let extension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
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
      allocated_recorded := before.allocated_recorded.freshCap origin }
  · change { state.supply with nextCap := state.supply.nextCap + 1 } =
      { q with nextCap := q.nextCap + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextCap := supply.nextCap + 1 }) before.supply_eq
  · simpa [InferState.freshCap, InferState.recordEvent,
      DDLedger.markFreshCap, CapabilityOriginLedger.markStructuralFlexible,
      CapabilityOriginLedger.setOrigins,
      before.supply_eq] using
        DDLedger.LedgerBelow.markFreshCap before.executable_ledger_below

structure FreshTargetsCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (result : List Ty × InferState) (q' : InferenceBase.FreshSupply)
    (targets : List Ty) : Type where
  targets_eq : result.1 = targets
  transition : BisimulationExtension before.prevailing ledger S result.2
  state : TraversalStateCorrespondence q' S ledger result.2
  prevailing_eq : state.prevailing = transition.after

def FreshTargetsCompletion.extension
    {q q' : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {before : TraversalStateCorrespondence q S ledger state}
    {result : List Ty × InferState} {targets : List Ty}
    (run : FreshTargetsCompletion before result q' targets) :
    BisimulationExtension before.prevailing ledger S result.2 where
  after := run.state.prevailing
  transportTy := by
    intro declarativeTarget executableTarget related
    rw [run.prevailing_eq]
    exact run.transition.transportTy related

/-- Executable tuple-field allocation is literally the pure supply-indexed
DD allocation, including left-to-right order. -/
def freshTargets_complete
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (origin : ConstraintOrigin) (count : Nat) :
    FreshTargetsCompletion before (Inference.freshTargets state origin count)
      (freshTargetsSupply count q).2 (freshTargetsSupply count q).1 := by
  induction count generalizing q state with
  | zero =>
      exact
        { targets_eq := rfl
          transition := .refl before.prevailing
          state := before
          prevailing_eq := rfl }
  | succ count ih =>
      let allocated := before.freshTy origin
      let tail := ih allocated.state
      refine
        { targets_eq := ?_
          transition := before.freshTyExtension origin |>.seq tail.transition
          state := tail.state
          prevailing_eq := tail.prevailing_eq }
      simp only [Inference.freshTargets, freshTargetsSupply]
      rw [allocated.target_eq, tail.targets_eq]

/-! ## Result packages -/

structure PatternRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  result : PatternResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  dual : DualBisimulation transition.after dual result.dual
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PatternsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  result : PatternsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  duals : DualListBisimulation transition.after duals result.duals
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  result : PPatResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target
  holes : DualListBisimulation transition.after holes result.holes
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure PPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  result : PPatsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets
  holes : DualListBisimulation transition.after holes result.holes
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure DPatRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  result : DPatResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

structure DPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) (bindings : MonoCtx) : Type where
  result : DPatsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below : DDLedger.LedgerBelow q'
    result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets
  bindings : MonoCtxBisimulation transition.after bindings result.bindings

def PatternRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {dual : Dual} {bindings : MonoCtx}
    (run : PatternRunCompletion before operation q' declarative ledger dual
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PatternsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {duals : List Dual} {bindings : MonoCtx}
    (run : PatternsRunCompletion before operation q' declarative ledger duals
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PPatRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PPatResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {holes : List Dual} {bindings : MonoCtx}
    (run : PPatRunCompletion before operation q' declarative ledger target
      holes bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def PPatsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PPatsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty} {holes : List Dual} {bindings : MonoCtx}
    (run : PPatsRunCompletion before operation q' declarative ledger targets
      holes bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def DPatRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option DPatResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {target : Ty} {bindings : MonoCtx}
    (run : DPatRunCompletion before operation q' declarative ledger target
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

def DPatsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option DPatsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty} {bindings : MonoCtx}
    (run : DPatsRunCompletion before operation q' declarative ledger targets
      bindings) :
    TraversalStateCorrespondence q' declarative ledger run.result.state :=
  ⟨run.supply_eq, run.transition.after, run.declarative_bounded,
    run.executable_bounded, run.forward_bounded, run.reverse_bounded,
    run.ledger_below, run.executable_ledger_below, run.protected_origins,
    run.protected_below, run.allocated_recorded⟩

/-! ## Trace-only suffixes -/

def TraversalStateCorrespondence.visitThenRecord
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (event : TraceEvent)
    (eventRecorded : ∀ varId, varId ∈ event.allocatedCapVars →
      varId ∈ state.capabilityOrigins.map Prod.fst) :
    TraversalStateCorrespondence q declarative ledger
      ((visit state kind path).recordEvent event) := by
  let entered := before.visit kind path
  exact entered.recordEvent event (by
    intro varId membership
    simpa [visit, InferState.recordEvent] using eventRecorded varId membership)

def TraversalStateCorrespondence.visitThenRecordExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (event : TraceEvent) :
    BisimulationExtension before.prevailing ledger declarative
      ((visit state kind path).recordEvent event) :=
  (before.visitExtension kind path).seq
    ((before.visit kind path).prevailing.recordEventExtension event)

/-! ## Primitive leaf completions -/

def dpatVar_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.var name) target state)
      q S ledger target [(name, target)] := by
  let event := TraceEvent.inferredDPat (.var name) target [(name, target)] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .dpatVar path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .dpatVar path event
  refine
    { result := ⟨target, [(name, target)],
        (visit state .dpatVar path).recordEvent event⟩
      success := by simp [inferDPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget target
      bindings := .cons (transition.after.sameTarget target) .nil }

def dpatWild_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path .wild target state)
      q S ledger target [] := by
  let event := TraceEvent.inferredDPat .wild target [] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .dpatWild path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .dpatWild path event
  refine
    { result := ⟨target, [], (visit state .dpatWild path).recordEvent event⟩
      success := by simp [inferDPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget target
      bindings := .nil }

noncomputable def dpatCtor_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    (patterns : List DPat) {scheme : CtorScheme}
    (lookup : signature.findDataCtor name = some scheme)
    (closed : signature.SchemesClosed)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (expectedTarget : Ty) (expectedBounded : expectedTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q scheme) S
      (InferenceBase.instantiateCtorScheme q scheme).value.2
      expectedTarget S₁)
    {q' : InferenceBase.FreshSupply} {bindings : MonoCtx}
    (children :
      let instantiation := instantiateCtorInState_complete before scheme
      ∀ alignment : StateRunCompletion instantiation.correspondence
          (alignTypes (instantiateCtorInState state scheme).2
            (freshOrigin .dataPattern path "dp-constructor-result")
            (instantiateCtorInState state scheme).1.2 expectedTarget)
          (InferenceBase.instantiateCtorScheme q scheme).supply S₁
          (DDLedger.markCtorInstance ledger q scheme),
        DPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (instantiateCtorInState state scheme).1.1 alignment.result)
          q' S' ledger₂
          (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.ctor name patterns)
        expectedTarget state)
      q' S'
      (DDLedger.freezeExport ledger₂ S'
        (freshCapImages q scheme.capBinders)
        (capabilityExportPayload []
          (expectedTarget :: bindings.map fun entry => entry.2)))
      expectedTarget bindings := by
  let instantiation := instantiateCtorInState_complete before scheme
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.dataCtors lookup).boundedBy)
  let supplyExtension := SupplyExtends.instantiateCtorScheme q scheme
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .dataPattern path "dp-constructor-result")
    instantiation.correspondence instantiation.target
    (instantiation.transition.transportTy
      (before.prevailing.sameTarget expectedTarget))
    instBounded.2 (expectedBounded.mono supplyExtension)
    (by simpa [Inference.instantiateCtorInState, before.supply_eq] using
      instBounded.2)
    (expectedBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let capImages := freshCapImages q scheme.capBinders
  let declarativePayload := capabilityExportPayload []
    (expectedTarget :: bindings.map fun entry => entry.2)
  let executableBindings := childrenRun.result.bindings
  let executablePayload := capabilityExportPayload []
    (expectedTarget :: executableBindings.map fun entry => entry.2)
  let payloadRelated :=
    DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.exportPayload
      (target := expectedTarget) childrenRun.bindings
  let frozen :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelated
      childrenRun.completion capImages payloadRelated
  let freezeExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelatedExtension
      childrenRun.completion capImages payloadRelated
  let visited := frozen.visit .dpatCtor path
  let event := TraceEvent.inferredDPat (.ctor name patterns) expectedTarget
    executableBindings path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let visitExtension := frozen.visitExtension .dpatCtor path
  let eventExtension := visitExtension.after.recordEventExtension event
  let transition := (((instantiation.transition.seq alignment.transition).seq
    childrenRun.transition).seq freezeExtension).seq
      (visitExtension.seq eventExtension)
  refine
    { result := ⟨expectedTarget, executableBindings,
        (visit (childrenRun.result.state.freezeCapabilityExport capImages
          executablePayload)
          .dpatCtor path).recordEvent event⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget expectedTarget
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          (freezeExtension.seq (visitExtension.seq eventExtension))
          childrenRun.bindings }
  simp only [inferDPatFuel]
  rw [lookup]
  simp only
  simp only [alignment.success]
  simp only [childrenRun.success]
  simp [capImages, executablePayload, executableBindings, before.supply_eq,
    event]

noncomputable def dpatTuple_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    (patterns : List DPat)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (expectedTarget : Ty) (expectedBounded : expectedTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expectedTarget S₁)
    {q' : InferenceBase.FreshSupply} {bindings : MonoCtx}
    (children :
      let fresh := freshTargets_complete before
        (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
      ∀ alignment : StateRunCompletion fresh.state
          (alignTypes (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).2
            (freshOrigin .dataPattern path "dp-tuple-result")
            (.prod (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1)
            expectedTarget)
          (freshTargetsSupply patterns.length q).2 S₁ ledger,
        DPatsRunCompletion alignment.completion
          (inferDPatsFuel fuel signature path 0 patterns
            (freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length).1 alignment.result)
          q' S' ledger₂ (freshTargetsSupply patterns.length q).1 bindings) :
    DPatRunCompletion before
      (inferDPatFuel (fuel + 1) signature path (.tuple patterns)
        expectedTarget state)
      q' S' ledger₂ expectedTarget bindings := by
  let fieldOrigin := freshOrigin .dataPattern path "dp-tuple-field"
  let resultOrigin := freshOrigin .dataPattern path "dp-tuple-result"
  let fresh := freshTargets_complete before fieldOrigin patterns.length
  let supplyExtension := SupplyExtends.freshTargets patterns.length q
  have declarativeProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargetsSupply patterns.length q).1) :=
    Ty.BoundedBy.prodOfForall
      (freshTargetsSupply_boundedBy patterns.length q)
  have executableProductRelated : TyBisimulation fresh.state.prevailing
      (.prod (freshTargetsSupply patterns.length q).1)
      (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact fresh.state.prevailing.sameTarget _
  have executableProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact declarativeProductBounded
  let alignment := ddAlignTypesWithLedger_complete
    (origin := resultOrigin) fresh.state executableProductRelated
    (fresh.state.prevailing.sameTarget expectedTarget)
    declarativeProductBounded (expectedBounded.mono supplyExtension)
    executableProductBounded (expectedBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let executableBindings := childrenRun.result.bindings
  let event := TraceEvent.inferredDPat (.tuple patterns) expectedTarget
    executableBindings path
  let visited := childrenRun.completion.visit .dpatTuple path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let visitExtension := childrenRun.completion.visitExtension .dpatTuple path
  let eventExtension := visitExtension.after.recordEventExtension event
  let transition := ((fresh.extension.seq alignment.transition).seq
    childrenRun.transition).seq (visitExtension.seq eventExtension)
  refine
    { result := ⟨expectedTarget, executableBindings,
        (visit childrenRun.result.state .dpatTuple path).recordEvent event⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget expectedTarget
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          (visitExtension.seq eventExtension) childrenRun.bindings }
  simp only [inferDPatFuel]
  have alignmentSuccess := alignment.success
  dsimp [fieldOrigin, resultOrigin] at alignmentSuccess
  simp only [alignmentSuccess]
  simp only [childrenRun.success]
  rfl

noncomputable def ppatCtor_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    (patterns : List PPat) {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (closed : signature.SchemesClosed)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (expectedTarget : Ty) (expectedBounded : expectedTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q entry.scheme) S
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2
      expectedTarget S₁)
    {q' : InferenceBase.FreshSupply} {holes : List Dual}
    {bindings : MonoCtx}
    (children :
      let instantiation := instantiateCtorInState_complete before entry.scheme
      ∀ alignment : StateRunCompletion instantiation.correspondence
          (alignTypes (instantiateCtorInState state entry.scheme).2
            (freshOrigin .primitivePattern path "pp-constructor-result")
            (instantiateCtorInState state entry.scheme).1.2 expectedTarget)
          (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
          (DDLedger.markCtorInstance ledger q entry.scheme),
        PPatsRunCompletion alignment.completion
          (inferPPatsFuel fuel signature path 0 patterns
            (instantiateCtorInState state entry.scheme).1.1 alignment.result)
          q' S' ledger₂
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 holes
          bindings) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.ctor name patterns)
        expectedTarget state)
      q' S'
      (DDLedger.freezeExport ledger₂ S'
        (freshCapImages q entry.scheme.capBinders)
        (capabilityExportPayload (holes.map Dual.cap)
          (holes.map Dual.target ++
            expectedTarget :: bindings.map fun item => item.2)))
      expectedTarget holes bindings := by
  let instantiation := instantiateCtorInState_complete before entry.scheme
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.patternCtors lookup).boundedBy)
  let supplyExtension := SupplyExtends.instantiateCtorScheme q entry.scheme
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .primitivePattern path "pp-constructor-result")
    instantiation.correspondence instantiation.target
    (instantiation.transition.transportTy
      (before.prevailing.sameTarget expectedTarget))
    instBounded.2 (expectedBounded.mono supplyExtension)
    (by simpa [Inference.instantiateCtorInState, before.supply_eq] using
      instBounded.2)
    (expectedBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let capImages := freshCapImages q entry.scheme.capBinders
  let executableHoles := childrenRun.result.holes
  let executableBindings := childrenRun.result.bindings
  let declarativePayload := capabilityExportPayload (holes.map Dual.cap)
    (holes.map Dual.target ++
      expectedTarget :: bindings.map fun item => item.2)
  let executablePayload := capabilityExportPayload
    (executableHoles.map Dual.cap)
    (executableHoles.map Dual.target ++
      expectedTarget :: executableBindings.map fun item => item.2)
  let payloadRelated :=
    DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.exportPayload
      (target := expectedTarget) childrenRun.holes childrenRun.bindings
  let frozen :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelated
      childrenRun.completion capImages payloadRelated
  let freezeExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelatedExtension
      childrenRun.completion capImages payloadRelated
  let visited := frozen.visit .ppatCtor path
  let event := TraceEvent.inferredPPat (.ctor name patterns) expectedTarget
    executableHoles executableBindings path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let visitExtension := frozen.visitExtension .ppatCtor path
  let eventExtension := visitExtension.after.recordEventExtension event
  let finishExtension := freezeExtension.seq
    (visitExtension.seq eventExtension)
  let transition := (((instantiation.transition.seq alignment.transition).seq
    childrenRun.transition).seq freezeExtension).seq
      (visitExtension.seq eventExtension)
  refine
    { result := ⟨expectedTarget, executableHoles, executableBindings,
        (visit (childrenRun.result.state.freezeCapabilityExport capImages
          executablePayload) .ppatCtor path).recordEvent event⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget expectedTarget
      holes :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          finishExtension childrenRun.holes
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          finishExtension childrenRun.bindings }
  simp only [inferPPatFuel]
  rw [lookup]
  simp only
  simp only [alignment.success]
  simp only [childrenRun.success]
  simp [capImages, executablePayload, executableHoles, executableBindings,
    before.supply_eq, event]

noncomputable def ppatTuple_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    (patterns : List PPat)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (expectedTarget : Ty) (expectedBounded : expectedTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expectedTarget S₁)
    {q' : InferenceBase.FreshSupply} {holes : List Dual}
    {bindings : MonoCtx}
    (children :
      let fresh := freshTargets_complete before
        (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length
      ∀ alignment : StateRunCompletion fresh.state
          (alignTypes (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).2
            (freshOrigin .primitivePattern path "pp-tuple-result")
            (.prod (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).1)
            expectedTarget)
          (freshTargetsSupply patterns.length q).2 S₁ ledger,
        PPatsRunCompletion alignment.completion
          (inferPPatsFuel fuel signature path 0 patterns
            (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).1 alignment.result)
          q' S' ledger₂ (freshTargetsSupply patterns.length q).1 holes
          bindings) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.tuple patterns)
        expectedTarget state)
      q' S' ledger₂ expectedTarget holes bindings := by
  let fieldOrigin := freshOrigin .primitivePattern path "pp-tuple-field"
  let resultOrigin := freshOrigin .primitivePattern path "pp-tuple-result"
  let fresh := freshTargets_complete before fieldOrigin patterns.length
  let supplyExtension := SupplyExtends.freshTargets patterns.length q
  have declarativeProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargetsSupply patterns.length q).1) :=
    Ty.BoundedBy.prodOfForall
      (freshTargetsSupply_boundedBy patterns.length q)
  have executableProductRelated : TyBisimulation fresh.state.prevailing
      (.prod (freshTargetsSupply patterns.length q).1)
      (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact fresh.state.prevailing.sameTarget _
  have executableProductBounded :
      Ty.BoundedBy (freshTargetsSupply patterns.length q).2
        (.prod (freshTargets state fieldOrigin patterns.length).1) := by
    rw [fresh.targets_eq]
    exact declarativeProductBounded
  let alignment := ddAlignTypesWithLedger_complete
    (origin := resultOrigin) fresh.state executableProductRelated
    (fresh.state.prevailing.sameTarget expectedTarget)
    declarativeProductBounded (expectedBounded.mono supplyExtension)
    executableProductBounded (expectedBounded.mono supplyExtension) aligned
  let childrenRun := children alignment
  let executableHoles := childrenRun.result.holes
  let executableBindings := childrenRun.result.bindings
  let event := TraceEvent.inferredPPat (.tuple patterns) expectedTarget
    executableHoles executableBindings path
  let visited := childrenRun.completion.visit .ppatTuple path
  let final := visited.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let visitExtension := childrenRun.completion.visitExtension .ppatTuple path
  let eventExtension := visitExtension.after.recordEventExtension event
  let finishExtension := visitExtension.seq eventExtension
  let transition := ((fresh.extension.seq alignment.transition).seq
    childrenRun.transition).seq finishExtension
  refine
    { result := ⟨expectedTarget, executableHoles, executableBindings,
        (visit childrenRun.result.state .ppatTuple path).recordEvent event⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget expectedTarget
      holes :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
          finishExtension childrenRun.holes
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          finishExtension childrenRun.bindings }
  simp only [inferPPatFuel]
  have alignmentSuccess := alignment.success
  dsimp [fieldOrigin, resultOrigin] at alignmentSuccess
  simp only [alignmentSuccess]
  simp only [childrenRun.success]
  rfl

def ppatWild_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .wild target state)
      q S ledger target [] [] := by
  let event := TraceEvent.inferredPPat .wild target [] [] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .ppatWild path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .ppatWild path event
  refine
    { result := ⟨target, [], [],
        (visit state .ppatWild path).recordEvent event⟩
      success := by simp [inferPPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget target
      holes := .nil
      bindings := .nil }

def ppatValue_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.pval name) target state)
      q S ledger target [] [(name, target)] := by
  let event := TraceEvent.inferredPPat (.pval name) target []
    [(name, target)] path
  let final := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord before .ppatValue path event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition := DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension before .ppatValue path event
  refine
    { result := ⟨target, [], [(name, target)],
        (visit state .ppatValue path).recordEvent event⟩
      success := by simp [inferPPatFuel, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget target
      holes := .nil
      bindings := .cons (transition.after.sameTarget target) .nil }

def ppatHole_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (target : Ty) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .hole target state)
      { q with nextCap := q.nextCap + 1 } S
      (DDLedger.markFreshCap ledger q) target
      [⟨.var ⟨q.nextCap⟩, target⟩] [] := by
  let origin := freshOrigin .primitivePattern path "primitive-hole"
  let fresh := state.freshCap origin
  have capabilityEq : fresh.1 = .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  let holes := [Dual.mk fresh.1 target]
  let event := TraceEvent.inferredPPat .hole target holes [] path
  let allocated :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCap
      before origin
  let final :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord
      allocated .ppatHole path event (by
        intro _ membership
        simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition :=
    (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      before origin).seq
      (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
        allocated .ppatHole path event)
  refine
    { result := ⟨target, holes, [],
        (visit fresh.2 .ppatHole path).recordEvent event⟩
      success := by simp [inferPPatFuel, origin, fresh, holes, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      target := transition.after.sameTarget target
      holes := by
        change DualListBisimulation transition.after
          [⟨.var ⟨q.nextCap⟩, target⟩] holes
        have holesEq : holes = [⟨.var ⟨q.nextCap⟩, target⟩] := by
          simp [holes, capabilityEq]
        rw [holesEq]
        exact .cons (DualBisimulation.same transition.after
          ⟨.var ⟨q.nextCap⟩, target⟩) .nil
      bindings := .nil }

/-! ## Solver-free user-pattern branches -/

def patternVar_complete
    (fuel : Nat) (signature : FrozenSig)
    (declarativeContext executableContext : Context)
    (declarativeParameters executableParameters : PatternCtx)
    (selfEnv : SelfEnv) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (absent : name ∉ declarativeBindings.names) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path (.pvar name) state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      (declarativeBindings ++ [(name, .var q.nextTy)]) := by
  let capOrigin := freshOrigin .pattern path "pattern-variable-capability"
  let targetOrigin := freshOrigin .pattern path "pattern-variable-target"
  let freshCap := state.freshCap capOrigin
  let capRelation :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCap
      before capOrigin
  let freshTarget := freshCap.2.freshTy targetOrigin
  let targetCompletion := capRelation.freshTy targetOrigin
  have capabilityEq : freshCap.1 = .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  have targetEq : freshTarget.1 = .var q.nextTy := by
    simpa [freshTarget] using targetCompletion.target_eq
  let executableResultBindings := executableBindings ++ [(name, freshTarget.1)]
  let executableDual := Dual.mk freshCap.1 freshTarget.1
  let freshEvent := TraceEvent.patternVarFresh executableContext
    executableParameters executableBindings ⟨state.supply.nextCap⟩
    freshCap.2.supply.nextTy
  let afterFreshEvent := targetCompletion.state.recordEvent freshEvent (by
    intro _ membership
    simp [freshEvent, TraceEvent.allocatedCapVars] at membership)
  let visited := afterFreshEvent.visit .patternVar path
  let inferredEvent := TraceEvent.inferredPattern (.pvar name) executableDual
    executableResultBindings path
  let final := visited.recordEvent inferredEvent (by
    intro _ membership
    simp [inferredEvent, TraceEvent.allocatedCapVars] at membership)
  let capExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      before capOrigin
  let targetExtension := capRelation.freshTyExtension targetOrigin
  let freshEventExtension :=
    targetCompletion.state.prevailing.recordEventExtension freshEvent
  let visitExtension := afterFreshEvent.visitExtension .patternVar path
  let inferredExtension := visitExtension.after.recordEventExtension inferredEvent
  let suffix := freshEventExtension.seq
    (visitExtension.seq inferredExtension)
  let transition := (capExtension.seq targetExtension).seq suffix
  have executableAbsent : name ∉ executableBindings.names := by
    rw [← bindings.names_eq]
    exact absent
  refine
    { result := ⟨executableDual, executableResultBindings,
        ((freshTarget.2.recordEvent freshEvent |> fun current =>
          visit current .patternVar path).recordEvent inferredEvent)⟩
      success := ?_
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual := by
        change DualBisimulation transition.after
          ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ executableDual
        dsimp [executableDual]
        rw [capabilityEq, targetEq]
        exact DualBisimulation.same transition.after
          ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      bindings := by
        apply DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.append
        · exact
            DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
              transition bindings
        · rw [targetEq]
          exact .cons (transition.after.sameTarget (.var q.nextTy)) .nil }
  simp [inferPatternFuel, executableAbsent, capOrigin, targetOrigin, freshCap,
    freshTarget, executableDual, executableResultBindings, freshEvent,
    inferredEvent]

def patternWild_complete
    (fuel : Nat) (signature : FrozenSig)
    (declarativeContext executableContext : Context)
    (declarativeParameters executableParameters : PatternCtx)
    (selfEnv : SelfEnv) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path .wild state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ declarativeBindings := by
  let capOrigin := freshOrigin .pattern path "pattern-wild-capability"
  let targetOrigin := freshOrigin .pattern path "pattern-wild-target"
  let freshCap := state.freshCap capOrigin
  let capRelation :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCap
      before capOrigin
  let freshTarget := freshCap.2.freshTy targetOrigin
  let targetCompletion := capRelation.freshTy targetOrigin
  have capabilityEq : freshCap.1 = .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  have targetEq : freshTarget.1 = .var q.nextTy := by
    simpa [freshTarget] using targetCompletion.target_eq
  let executableDual := Dual.mk freshCap.1 freshTarget.1
  let freshEvent := TraceEvent.patternWildFresh executableContext
    executableParameters executableBindings ⟨state.supply.nextCap⟩
    freshCap.2.supply.nextTy
  let afterFreshEvent := targetCompletion.state.recordEvent freshEvent (by
    intro _ membership
    simp [freshEvent, TraceEvent.allocatedCapVars] at membership)
  let visited := afterFreshEvent.visit .patternWild path
  let inferredEvent := TraceEvent.inferredPattern .wild executableDual
    executableBindings path
  let final := visited.recordEvent inferredEvent (by
    intro _ membership
    simp [inferredEvent, TraceEvent.allocatedCapVars] at membership)
  let capExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      before capOrigin
  let targetExtension := capRelation.freshTyExtension targetOrigin
  let freshEventExtension :=
    targetCompletion.state.prevailing.recordEventExtension freshEvent
  let visitExtension := afterFreshEvent.visitExtension .patternWild path
  let inferredExtension := visitExtension.after.recordEventExtension inferredEvent
  let suffix := freshEventExtension.seq
    (visitExtension.seq inferredExtension)
  let transition := (capExtension.seq targetExtension).seq suffix
  refine
    { result := ⟨executableDual, executableBindings,
        ((freshTarget.2.recordEvent freshEvent |> fun current =>
          visit current .patternWild path).recordEvent inferredEvent)⟩
      success := by
        simp [inferPatternFuel, capOrigin, targetOrigin, freshCap, freshTarget,
          executableDual, freshEvent, inferredEvent]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual := by
        change DualBisimulation transition.after
          ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ executableDual
        dsimp [executableDual]
        rw [capabilityEq, targetEq]
        exact DualBisimulation.same transition.after
          ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          transition bindings }

def patternValue_complete
    (fuel : Nat) (signature : FrozenSig)
    (declarativeContext executableContext : Context)
    (declarativeParameters executableParameters : PatternCtx)
    (selfEnv : SelfEnv) (path : SyntaxPath) (expression : Expr)
    {q q₁ : InferenceBase.FreshSupply} {S S₁ : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    {target : Ty}
    (expressionRun : SynthRunCompletion (before.visit .patternValue path)
      (inferExprFuel fuel signature
        (executableBindings.toContext ++ executableContext) selfEnv
        (0 :: path) expression (visit state .patternValue path))
      q₁ S₁ ledger₁ target) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path
        (.pval expression) state)
      { q₁ with nextCap := q₁.nextCap + 1 } S₁
      (DDLedger.markFreshCap ledger₁ q₁)
      ⟨.var ⟨q₁.nextCap⟩, target⟩ declarativeBindings := by
  let capOrigin := freshOrigin .pattern path "pattern-value-capability"
  let expressionRelation := expressionRun.completion.state
  let fresh := expressionRun.result.state.freshCap capOrigin
  let freshRelation :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCap
      expressionRelation capOrigin
  have capabilityEq : fresh.1 = .var ⟨q₁.nextCap⟩ := by
    change Cap.var ⟨expressionRun.result.state.supply.nextCap⟩ =
      Cap.var ⟨q₁.nextCap⟩
    rw [expressionRun.supply_eq]
  let executableDual := Dual.mk fresh.1 expressionRun.result.target
  let freshEvent := TraceEvent.patternValueFresh executableContext
    executableParameters executableBindings
    ⟨expressionRun.result.state.supply.nextCap⟩ expressionRun.result.target
  let afterFreshEvent := freshRelation.recordEvent freshEvent (by
    intro _ membership
    simp [freshEvent, TraceEvent.allocatedCapVars] at membership)
  let inferredEvent := TraceEvent.inferredPattern (.pval expression)
    executableDual executableBindings path
  let final := afterFreshEvent.recordEvent inferredEvent (by
    intro _ membership
    simp [inferredEvent, TraceEvent.allocatedCapVars] at membership)
  let visitExtension := before.visitExtension .patternValue path
  let freshExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freshCapExtension
      expressionRelation capOrigin
  let freshEventExtension := freshExtension.after.recordEventExtension freshEvent
  let inferredExtension := freshEventExtension.after.recordEventExtension
    inferredEvent
  let suffix := freshExtension.seq
    (freshEventExtension.seq inferredExtension)
  let transition := visitExtension.seq (expressionRun.transition.seq suffix)
  refine
    { result := ⟨executableDual, executableBindings,
        (fresh.2.recordEvent freshEvent).recordEvent inferredEvent⟩
      success := by
        simp [inferPatternFuel, expressionRun.success, capOrigin, fresh,
          executableDual, freshEvent, inferredEvent]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual := by
        change DualBisimulation transition.after
          ⟨.var ⟨q₁.nextCap⟩, target⟩ executableDual
        refine ⟨?_, ?_⟩
        · dsimp [executableDual]
          rw [capabilityEq]
          exact CapBisimulation.same transition.after (.var ⟨q₁.nextCap⟩)
        · exact
            DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTy
              suffix expressionRun.target
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          transition bindings }

noncomputable def patternEmbed_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (selfEnv : SelfEnv) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeParameters executableParameters : PatternCtx)
    (parameters : PatternCtxBisimulation before.prevailing
      declarativeParameters executableParameters)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    {dual : Dual} (lookup : declarativeParameters.find? name = some dual) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context executableParameters
        executableBindings selfEnv path (.embed name) state)
      q S ledger dual declarativeBindings := by
  let witness :=
    DemandTypingInferenceCompletenessPatternTraversal.PatternCtxBisimulation.find?_complete
      parameters lookup
  let executableDual := Classical.choose witness
  have executableFacts := Classical.choose_spec witness
  have executableLookup := executableFacts.1
  have dualRelated := executableFacts.2
  let event := TraceEvent.inferredPattern (.embed name) executableDual
    executableBindings path
  let final :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecord
      before .patternEmbed path event (by
        intro _ membership
        simp [event, TraceEvent.allocatedCapVars] at membership)
  let transition :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .patternEmbed path event
  refine
    { result := ⟨executableDual, executableBindings,
        (visit state .patternEmbed path).recordEvent event⟩
      success := by
        simp only [inferPatternFuel]
        rw [executableLookup]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          transition dualRelated
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          transition bindings }

def patternTuple_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (declarativeParameters executableParameters : PatternCtx)
    (selfEnv : SelfEnv) (path : SyntaxPath) (patterns : List Pattern)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (executableBindings : MonoCtx)
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger' : CapabilityOriginLedger} {duals : List Dual}
    {bindings : MonoCtx}
    (children : PatternsRunCompletion
      (before.visit .patternTuple path)
      (inferPatternsFuel fuel signature context executableParameters
        executableBindings selfEnv path 0 patterns
        (visit state .patternTuple path))
      q' S' ledger' duals bindings) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context executableParameters
        executableBindings selfEnv path (.ptuple patterns) state)
      q' S' ledger'
      ⟨.prod (duals.map Dual.cap), .prod (duals.map Dual.target)⟩ bindings := by
  let executableDual := Dual.mk (.prod (children.result.duals.map Dual.cap))
    (.prod (children.result.duals.map Dual.target))
  let event := TraceEvent.inferredPattern (.ptuple patterns) executableDual
    children.result.bindings path
  let final := children.completion.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let finishExtension := children.transition.after.recordEventExtension event
  let transition := (before.visitExtension .patternTuple path).seq
    (children.transition.seq finishExtension)
  have caps : CapBisimulation finishExtension.after
      (.prod (duals.map Dual.cap))
      (.prod (children.result.duals.map Dual.cap)) := by
    exact DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.prodCaps
      (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
        finishExtension children.duals)
  have targets : TyBisimulation finishExtension.after
      (.prod (duals.map Dual.target))
      (.prod (children.result.duals.map Dual.target)) := by
    exact DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.prodTargets
      (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
        finishExtension children.duals)
  refine
    { result := ⟨executableDual, children.result.bindings,
        children.result.state.recordEvent event⟩
      success := by simp [inferPatternFuel, children.success, executableDual,
        event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual := ⟨caps, targets⟩
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          finishExtension children.bindings }

/-! ## Composite user-pattern completions -/

/-- Conjunction traverses both children and then aligns their duals. -/
noncomputable def patternAnd_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (path : SyntaxPath)
    (left right : Pattern)
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (executableBindings : MonoCtx)
    {leftDual rightDual : Dual} {leftBindings bindings' : MonoCtx}
    (leftRun : PatternRunCompletion (before.visit .patternAnd path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternAnd path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : PatternRunCompletion leftRun.completion
      (inferPatternFuel fuel signature context parameters
        leftRun.result.bindings selfEnv (1 :: path) right leftRun.result.state)
      q₂ S₂ ledger₂ rightDual bindings')
    (declarativeLeftBounded : Dual.BoundedBy q₂ leftDual)
    (declarativeRightBounded : Dual.BoundedBy q₂ rightDual)
    (executableLeftBounded : Dual.BoundedBy q₂ leftRun.result.dual)
    (executableRightBounded : Dual.BoundedBy q₂ rightRun.result.dual)
    (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S') :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.pand left right) state)
      q₂ S' ledger₂ leftDual bindings' := by
  let leftAtRight :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
      rightRun.transition leftRun.dual
  let alignment := ddAlignDualWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-and") rightRun.completion
    leftAtRight rightRun.dual declarativeLeftBounded declarativeRightBounded
    executableLeftBounded executableRightBounded aligned
  let event := TraceEvent.inferredPattern (.pand left right)
    leftRun.result.dual rightRun.result.bindings path
  let final := alignment.completion.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let finishExtension := alignment.transition.after.recordEventExtension event
  let transition := (before.visitExtension .patternAnd path).seq
    ((leftRun.transition.seq rightRun.transition).seq
      (alignment.transition.seq finishExtension))
  refine
    { result := ⟨leftRun.result.dual, rightRun.result.bindings,
        alignment.result.recordEvent event⟩
      success := by
        simp [inferPatternFuel, leftRun.success, rightRun.success,
          alignment.success, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          (alignment.transition.seq finishExtension) leftAtRight
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          (alignment.transition.seq finishExtension) rightRun.bindings }

/-- Disjunction aligns both the result dual and the two alternative binding
contexts before returning the left representative. -/
noncomputable def patternOr_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (path : SyntaxPath)
    (left right : Pattern)
    {q q₁ q₂ : InferenceBase.FreshSupply}
    {S S₁ S₂ S₃ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (executableBindings : MonoCtx)
    {leftDual rightDual : Dual} {leftBindings rightBindings : MonoCtx}
    (leftRun : PatternRunCompletion (before.visit .patternOr path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternOr path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : PatternRunCompletion leftRun.completion
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (1 :: path) right leftRun.result.state)
      q₂ S₂ ledger₂ rightDual rightBindings)
    (declarativeLeftDualBounded : Dual.BoundedBy q₂ leftDual)
    (declarativeRightDualBounded : Dual.BoundedBy q₂ rightDual)
    (executableLeftDualBounded : Dual.BoundedBy q₂ leftRun.result.dual)
    (executableRightDualBounded : Dual.BoundedBy q₂ rightRun.result.dual)
    (declarativeLeftBindingsBounded : MonoCtx.BoundedBy q₂ leftBindings)
    (declarativeRightBindingsBounded : MonoCtx.BoundedBy q₂ rightBindings)
    (executableLeftBindingsBounded :
      MonoCtx.BoundedBy q₂ leftRun.result.bindings)
    (executableRightBindingsBounded :
      MonoCtx.BoundedBy q₂ rightRun.result.bindings)
    (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual
      S₃)
    (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃
      leftBindings rightBindings S') :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.por left right) state)
      q₂ S' ledger₂ leftDual leftBindings := by
  let leftDualAtRight :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
      rightRun.transition leftRun.dual
  let leftBindingsAtRight :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      rightRun.transition leftRun.bindings
  let dualAlignment := ddAlignDualWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-or") rightRun.completion
    leftDualAtRight rightRun.dual declarativeLeftDualBounded
    declarativeRightDualBounded executableLeftDualBounded
    executableRightDualBounded dualsAligned
  let bindingAlignment := ddAlignBindingsWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-or-bindings")
    dualAlignment.completion
    (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      dualAlignment.transition leftBindingsAtRight)
    (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      dualAlignment.transition rightRun.bindings)
    declarativeLeftBindingsBounded declarativeRightBindingsBounded
    executableLeftBindingsBounded executableRightBindingsBounded
    bindingsAligned
  let event := TraceEvent.inferredPattern (.por left right)
    leftRun.result.dual leftRun.result.bindings path
  let final := bindingAlignment.completion.recordEvent event (by
    intro _ membership
    simp [event, TraceEvent.allocatedCapVars] at membership)
  let finishExtension :=
    bindingAlignment.transition.after.recordEventExtension event
  let suffix := dualAlignment.transition.seq
    (bindingAlignment.transition.seq finishExtension)
  let transition := (before.visitExtension .patternOr path).seq
    ((leftRun.transition.seq rightRun.transition).seq suffix)
  refine
    { result := ⟨leftRun.result.dual, leftRun.result.bindings,
        bindingAlignment.result.recordEvent event⟩
      success := by
        simp [inferPatternFuel, leftRun.success, rightRun.success,
          dualAlignment.success, bindingAlignment.success, event]
      supply_eq := final.supply_eq
      transition := transition
      declarative_bounded := final.declarative_bounded
      executable_bounded := final.executable_bounded
      forward_bounded := final.forward_bounded
      reverse_bounded := final.reverse_bounded
      ledger_below := final.ledger_below
      executable_ledger_below := final.executable_ledger_below
      protected_origins := final.protected_origins
      protected_below := final.protected_below
      allocated_recorded := final.allocated_recorded
      dual :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          suffix leftDualAtRight
      bindings :=
        DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          suffix leftBindingsAtRight }

/-! ## Empty and cons list packaging -/

def patternsNil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (path : SyntaxPath)
    (index : Nat) {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings executableBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings) :
    PatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path index [] state)
      q S ledger [] declarativeBindings := by
  refine
    { result := ⟨[], executableBindings, state⟩
      success := by simp [inferPatternsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      duals := .nil
      bindings := bindings }

def ppatsNil_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    PPatsRunCompletion before
      (inferPPatsFuel (fuel + 1) signature path index [] [] state)
      q S ledger [] [] [] := by
  refine
    { result := ⟨[], [], [], state⟩
      success := by simp [inferPPatsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      targets := .nil
      holes := .nil
      bindings := .nil }

def dpatsNil_complete
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    DPatsRunCompletion before
      (inferDPatsFuel (fuel + 1) signature path index [] [] state)
      q S ledger [] [] := by
  refine
    { result := ⟨[], [], state⟩
      success := by simp [inferDPatsFuel]
      supply_eq := before.supply_eq
      transition := .refl before.prevailing
      declarative_bounded := before.declarative_bounded
      executable_bounded := before.executable_bounded
      forward_bounded := before.forward_bounded
      reverse_bounded := before.reverse_bounded
      ledger_below := before.ledger_below
      executable_ledger_below := before.executable_ledger_below
      protected_origins := before.protected_origins
      protected_below := before.protected_below
      allocated_recorded := before.allocated_recorded
      targets := .nil
      bindings := .nil }

def patternsCons_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (selfEnv : SelfEnv) (parent : SyntaxPath)
    (index : Nat) (pattern : Pattern) (patterns : List Pattern)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {dual : Dual} {duals : List Dual}
    {bindings₁ bindings' : MonoCtx}
    (head : PatternRunCompletion before
      (inferPatternFuel fuel signature context parameters
        executableBindings selfEnv (index :: parent) pattern state)
      q₁ S₁ ledger₁ dual bindings₁)
    (tail : PatternsRunCompletion head.completion
      (inferPatternsFuel fuel signature context parameters
        head.result.bindings selfEnv parent (index + 1) patterns
        head.result.state)
      q' S' ledger' duals bindings') :
    PatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv parent index (pattern :: patterns) state)
      q' S' ledger' (dual :: duals) bindings' := by
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.dual :: tail.result.duals,
        tail.result.bindings, tail.result.state⟩
      success := by simp [inferPatternsFuel, head.success, tail.success]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      duals := .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          tail.transition head.dual) tail.duals
      bindings := tail.bindings }

def ppatsCons_complete
    (fuel : Nat) (signature : FrozenSig) (parent : SyntaxPath) (index : Nat)
    (pattern : PPat) (patterns : List PPat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {target : Ty} {targets : List Ty} {holes restHoles : List Dual}
    {bindings restBindings : MonoCtx}
    (head : PPatRunCompletion before
      (inferPPatFuel fuel signature (index :: parent) pattern
        executableTarget state)
      q₁ S₁ ledger₁ target holes bindings)
    (tail : PPatsRunCompletion head.completion
      (inferPPatsFuel fuel signature parent (index + 1) patterns
        executableTargets head.result.state)
      q' S' ledger' targets restHoles restBindings)
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names) :
    PPatsRunCompletion before
      (inferPPatsFuel (fuel + 1) signature parent index
        (pattern :: patterns) (executableTarget :: executableTargets) state)
      q' S' ledger' (target :: targets) (holes ++ restHoles)
      (bindings ++ restBindings) := by
  let transportedBindings :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      tail.transition head.bindings
  have checked := namesDisjoint_of_bisimulation transportedBindings
    tail.bindings disjoint
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.target :: tail.result.targets,
        head.result.holes ++ tail.result.holes,
        head.result.bindings ++ tail.result.bindings, tail.result.state⟩
      success := by
        simp [inferPPatsFuel, head.success, tail.success, checked]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      targets := .cons (tail.transition.transportTy head.target) tail.targets
      holes :=
        DemandTypingInferenceCompletenessPatternTraversal.DualListBisimulation.append
          (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
            tail.transition head.holes) tail.holes
      bindings := DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.append transportedBindings
        tail.bindings }

def dpatsCons_complete
    (fuel : Nat) (signature : FrozenSig) (parent : SyntaxPath) (index : Nat)
    (pattern : DPat) (patterns : List DPat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger₁ ledger' : CapabilityOriginLedger}
    {target : Ty} {targets : List Ty}
    {bindings restBindings : MonoCtx}
    (head : DPatRunCompletion before
      (inferDPatFuel fuel signature (index :: parent) pattern
        executableTarget state)
      q₁ S₁ ledger₁ target bindings)
    (tail : DPatsRunCompletion head.completion
      (inferDPatsFuel fuel signature parent (index + 1) patterns
        executableTargets head.result.state)
      q' S' ledger' targets restBindings)
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names) :
    DPatsRunCompletion before
      (inferDPatsFuel (fuel + 1) signature parent index
        (pattern :: patterns) (executableTarget :: executableTargets) state)
      q' S' ledger' (target :: targets) (bindings ++ restBindings) := by
  let transportedBindings :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      tail.transition head.bindings
  have checked := namesDisjoint_of_bisimulation transportedBindings
    tail.bindings disjoint
  let transition := head.transition.seq tail.transition
  refine
    { result := ⟨head.result.target :: tail.result.targets,
        head.result.bindings ++ tail.result.bindings, tail.result.state⟩
      success := by
        simp [inferDPatsFuel, head.success, tail.success, checked]
      supply_eq := tail.supply_eq
      transition := transition
      declarative_bounded := tail.declarative_bounded
      executable_bounded := tail.executable_bounded
      forward_bounded := tail.forward_bounded
      reverse_bounded := tail.reverse_bounded
      ledger_below := tail.ledger_below
      executable_ledger_below := tail.executable_ledger_below
      protected_origins := tail.protected_origins
      protected_below := tail.protected_below
      allocated_recorded := tail.allocated_recorded
      targets := .cons (tail.transition.transportTy head.target) tail.targets
      bindings := DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.append transportedBindings
        tail.bindings }

end DemandTypingInferenceCompletenessPatternTraversal
end TypePM
