import TypePM.DemandTypingInferenceCompletenessStateMutual
import TypePM.DemandTypingInferenceCompletenessSolver
import TypePM.DemandTypingInferenceCompletenessContext
import TypePM.DemandTypingInferenceCompletenessContextBisimulation
import TypePM.DemandTypingInferenceCompletenessProtected
import TypePM.DemandTypingInferenceCompletenessIdempotence
import TypePM.DemandTypingOriginMetatheory

/-!
# Raw traversal completeness

This module is the traversal-facing half of inference completeness.  The DD
and executable solvers may choose different orientations for the same MGU, so
the induction invariant does not identify their prevailing substitutions.
Instead it threads mutual factorization together with the pieces of mutable
state that syntax-directed allocation determines literally: the fresh supply
and capability-origin ledger.

The result packages below deliberately stop before terminal validation.  They
are the common motives for the mutually recursive raw traversal proof.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessTraversal

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLedgerBisimulation
open DemandTypingInferenceCompletenessSolver
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessContext
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance

/-! ## Export-leaf transport -/

/-- Every executable export leaf is renamed by the forward residual to a DD
export leaf.  The payload occurrence supplies the finite scope on which
mutual factorization is an actual renaming; the reverse ledger map then rules
out rigid and rename-only destinations for a structural source leaf. -/
theorem StateBisimulation.forwardExportLeaves
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    ∀ varId,
      varId ∈ DDLedger.exportLeaves state.capabilityOrigins state.prevailing
        capImages exportedPayload →
      ∃ image, relation.forward.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves ledger declarative capImages
          exportedPayload := by
  classical
  intro varId membership
  unfold DDLedger.exportLeaves at membership ⊢
  rcases List.mem_filter.mp membership with ⟨deduplicated, structural⟩
  have filtered : varId ∈
      (capImages.flatMap fun image => (state.prevailing.cap image).fcv).filter
        (fun image => image ∈ (state.prevailing.apply exportedPayload).fcv) := by
    simpa using deduplicated
  rcases List.mem_filter.mp filtered with ⟨imageLeaf, payloadLeaf⟩
  have payloadLeafProp :
      varId ∈ (state.prevailing.apply exportedPayload).fcv := by
    exact of_decide_eq_true payloadLeaf
  have structuralProp : state.capabilityOrigins.originOf varId =
      .structuralFlexible := by
    exact of_decide_eq_true structural
  rcases List.mem_flatMap.mp imageLeaf with
    ⟨binder, binderMem, binderLeaf⟩
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn_image
      relation exportedPayload
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
  have imageInPayload : image ∈ (declarative.apply exportedPayload).fcv := by
    have targetRelation := relation.sameTarget exportedPayload
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure localMap
      (state.prevailing.apply exportedPayload) (fun _ member => member)
      (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv localMap
      (state.prevailing.apply exportedPayload)
    rw [targetRelation.forward, pure, freeVars]
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

/-- Symmetric export-leaf transport for the reverse residual. -/
theorem StateBisimulation.reverseExportLeaves
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    ∀ varId,
      varId ∈ DDLedger.exportLeaves ledger declarative capImages
        exportedPayload →
      ∃ image, relation.reverse.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves state.capabilityOrigins state.prevailing
          capImages exportedPayload := by
  classical
  intro varId membership
  unfold DDLedger.exportLeaves at membership ⊢
  rcases List.mem_filter.mp membership with ⟨deduplicated, structural⟩
  have filtered : varId ∈
      (capImages.flatMap fun image => (declarative.cap image).fcv).filter
        (fun image => image ∈ (declarative.apply exportedPayload).fcv) := by
    simpa using deduplicated
  rcases List.mem_filter.mp filtered with ⟨imageLeaf, payloadLeaf⟩
  have payloadLeafProp : varId ∈ (declarative.apply exportedPayload).fcv := by
    exact of_decide_eq_true payloadLeaf
  have structuralProp : ledger.originOf varId = .structuralFlexible := by
    exact of_decide_eq_true structural
  rcases List.mem_flatMap.mp imageLeaf with
    ⟨binder, binderMem, binderLeaf⟩
  let localMap :=
    DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
      relation exportedPayload
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
      (state.prevailing.apply exportedPayload).fcv := by
    have targetRelation := relation.sameTarget exportedPayload
    have pure :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.forward_apply_eq_pure localMap
      (declarative.apply exportedPayload) (fun _ member => member)
      (fun _ member => member)
    have freeVars :=
      DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pure_apply_fcv localMap
      (declarative.apply exportedPayload)
    rw [targetRelation.reverse, pure, freeVars]
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
        rcases forwardAt with ⟨ddImage, equation, safe⟩
        rw [forwardImage] at equation
        have equal : ddImage = varId := (Cap.var.inj equation).symm
        subst ddImage
        exact False.elim (safe structuralProp)
  refine ⟨image, reverseImage, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by exact decide_eq_true imageStructural⟩
  simp only [List.mem_eraseDups]
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr ⟨binder, binderMem, imageInBinder⟩,
    decide_eq_true imageInPayload⟩

/-- State relation used at every recursive traversal boundary.  History,
protected producer leaves, and provenance sources are append-only evidence
owned by the executable run; the DD indices determine only supply, prevailing
substitution up to mutual MGU factorization, and the chronological origin
ledger. -/
structure TraversalStateCorrespondence
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (executable : InferState) : Type where
  supply_eq : executable.supply = q
  prevailing : StateBisimulation ledger declarative executable
  declarative_bounded : declarative.BoundedBy q
  executable_bounded : executable.prevailing.BoundedBy q
  forward_bounded : prevailing.forward.BoundedBy q
  reverse_bounded : prevailing.reverse.BoundedBy q
  ledger_below : DDLedger.LedgerBelow q ledger
  executable_ledger_below :
    DDLedger.LedgerBelow q executable.capabilityOrigins
  protected_origins : ProtectedCapOrigins executable
  protected_below : ProtectedCapsBelowSupply executable
  allocated_recorded : AllocatedCapsRecorded executable

/-- Export freezing is a state-neutral transition for prevailing types while
the two ledgers freeze their corresponding structural representatives. -/
def TraversalStateCorrespondence.freezeCapabilityExport
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    TraversalStateCorrespondence q declarative
      (DDLedger.freezeExport ledger declarative capImages exportedPayload)
      (state.freezeCapabilityExport capImages exportedPayload) := by
  let afterLedger := DDLedger.freezeExport ledger declarative capImages
    exportedPayload
  let afterState := state.freezeCapabilityExport capImages exportedPayload
  have ledgerTransport := relation.prevailing.ledgerBisimulation.freezeExport
    (DemandTypingInferenceCompletenessTraversal.StateBisimulation.forwardExportLeaves
      relation.prevailing capImages exportedPayload)
    (DemandTypingInferenceCompletenessTraversal.StateBisimulation.reverseExportLeaves
      relation.prevailing capImages exportedPayload)
  let after : StateBisimulation afterLedger declarative afterState :=
    { forward := relation.prevailing.forward
      forwardEquation := by simpa [afterState] using
        relation.prevailing.forwardEquation
      declarativeIdempotent := relation.prevailing.declarativeIdempotent
      reverse := relation.prevailing.reverse
      reverseEquation := by simpa [afterState] using
        relation.prevailing.reverseEquation
      ledgerBisimulation := by
        simpa [afterLedger, afterState,
          InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
          using ledgerTransport
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
        exportedPayload relation.ledger_below
      executable_ledger_below := by
        simpa [afterState,
          InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
          using DDLedger.LedgerBelow.freezeExport state.prevailing capImages
            exportedPayload relation.executable_ledger_below
      protected_origins := relation.protected_origins.freezeCapabilityExport
        capImages exportedPayload
      protected_below :=
        relation.protected_below.freezeCapabilityExport_of_ledgerBelow (by
          rw [relation.supply_eq]
          exact relation.executable_ledger_below) capImages exportedPayload
      allocated_recorded := relation.allocated_recorded.freezeCapabilityExport
        capImages exportedPayload }

def TraversalStateCorrespondence.freezeCapabilityExportExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    BisimulationExtension relation.prevailing
      (DDLedger.freezeExport ledger declarative capImages exportedPayload)
      declarative (state.freezeCapabilityExport capImages exportedPayload) where
  after := (relation.freezeCapabilityExport capImages exportedPayload).prevailing
  transportTy := by
    intro declarativeTarget executableTarget related
    constructor
    · change declarative.apply declarativeTarget =
        relation.prevailing.forward.apply
          (state.prevailing.apply executableTarget)
      exact related.forward
    · change state.prevailing.apply executableTarget =
        relation.prevailing.reverse.apply
          (declarative.apply declarativeTarget)
      exact related.reverse

/-- Extending the origin ledger with a canonical scheme-instance batch
preserves an admissible post that is bounded at the incoming supply.  Old
variables retain their origin, while every newly allocated variable is fixed
by boundedness and is therefore admissible at its new rename-only origin. -/
theorem admissiblePost_markSchemeInstance_of_bounded
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {post : Subst} (admissible : AdmissiblePost ledger post)
    (bounded : post.BoundedBy q) (scheme : Scheme) :
    AdmissiblePost (DDLedger.markSchemeInstance ledger q scheme) post := by
  constructor
  intro varId
  by_cases below : varId.id < q.nextCap
  · have notFresh : varId ∉ Scheme.canonicalCapImages q scheme := by
      intro membership
      exact Nat.not_le_of_lt below
        (Scheme.mem_canonicalCapImages_bounds membership).1
    rw [DDLedger.markSchemeInstance,
      CapabilityOriginLedger.originOf_setOrigins_eq, if_neg notFresh]
    cases oldOrigin : ledger.originOf varId with
    | rigid => exact admissible.cap.rigid oldOrigin
    | renameOnly =>
        rcases admissible.cap.renameOnly oldOrigin with
          ⟨image, imageEquation, imageSafe⟩
        refine ⟨image, imageEquation, ?_⟩
        by_cases imageFresh : image ∈ Scheme.canonicalCapImages q scheme
        · rw [CapabilityOriginLedger.originOf_setOrigins_of_mem _ _ _ _
              imageFresh]
          simp
        · rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg imageFresh]
          exact imageSafe
    | structuralFlexible => trivial
  · have fixed := bounded.capFixedAbove varId (Nat.le_of_not_gt below)
    cases origin : (DDLedger.markSchemeInstance ledger q scheme).originOf varId with
    | rigid => exact fixed
    | renameOnly => exact ⟨varId, fixed, by simp [origin]⟩
    | structuralFlexible => trivial

private theorem freshCapImages_above
    (q : InferenceBase.FreshSupply) (binders : List CapVar)
    (varId : CapVar)
    (membership : varId ∈ Inference.freshCapImages q binders) :
    q.nextCap ≤ varId.id := by
  simp only [Inference.freshCapImages] at membership
  rcases List.mem_map.mp membership with ⟨binder, _, rfl⟩
  exact Nat.le_add_right q.nextCap binder.id

private theorem originOf_ne_rigid_mem_keys
    {ledger : CapabilityOriginLedger} {varId : CapVar}
    (nonrigid : ledger.originOf varId ≠ .rigid) :
    varId ∈ ledger.map Prod.fst := by
  induction ledger with
  | nil => simp [CapabilityOriginLedger.originOf] at nonrigid
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateOrigin⟩
      by_cases same : candidate = varId
      · subst candidate
        simp
      · simp only [CapabilityOriginLedger.originOf, same, if_false] at nonrigid
        simp [ih nonrigid]

/-- Adding the same fresh rename-only batch to both sides preserves a
cross-ledger policy map.  Boundedness keeps images of old rename-only
variables below the fresh cut. -/
theorem admissiblePostBetween_setFreshRenameOnly_of_bounded
    {q : InferenceBase.FreshSupply}
    {source destination : CapabilityOriginLedger} {post : Subst}
    {fresh : List CapVar}
    (between : AdmissiblePostBetween source destination post)
    (bounded : post.BoundedBy q)
    (sourceBelow : DDLedger.LedgerBelow q source)
    (freshAbove : ∀ varId, varId ∈ fresh → q.nextCap ≤ varId.id) :
    AdmissiblePostBetween
      (source.setOrigins fresh .renameOnly)
      (destination.setOrigins fresh .renameOnly) post := by
  constructor
  intro varId
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases selected : varId ∈ fresh
  · rw [if_pos selected]
    have fixed := bounded.capFixedAbove varId (freshAbove varId selected)
    exact ⟨varId, fixed, by
      rw [CapabilityOriginLedger.originOf_setOrigins_of_mem _ _ _ _ selected]
      simp⟩
  · rw [if_neg selected]
    cases sourceOrigin : source.originOf varId with
    | rigid =>
        rcases (by simpa [sourceOrigin] using between.cap varId) with
          ⟨fixed, destinationRigid⟩
        exact ⟨fixed, by
          rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg selected]
          exact destinationRigid⟩
    | renameOnly =>
        rcases (by simpa [sourceOrigin] using between.cap varId) with
          ⟨image, imageEquation, imageSafe⟩
        have varBelow : varId.id < q.nextCap :=
          sourceBelow varId (originOf_ne_rigid_mem_keys (by simp [sourceOrigin]))
        have imageBelow : image.id < q.nextCap := by
          apply bounded.capImagesBounded varId varBelow image
          rw [imageEquation]
          simp [Cap.fcv]
        have imageNotSelected : image ∉ fresh := by
          intro membership
          exact Nat.not_le_of_lt imageBelow (freshAbove image membership)
        exact ⟨image, imageEquation, by
          rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg imageNotSelected]
          exact imageSafe⟩
    | structuralFlexible => trivial

/-- Structural allocation on the same fresh batch preserves a cross-ledger
policy map: freshly selected source variables impose no restriction. -/
theorem admissiblePostBetween_setFreshStructural_of_bounded
    {q : InferenceBase.FreshSupply}
    {source destination : CapabilityOriginLedger} {post : Subst}
    {fresh : List CapVar}
    (between : AdmissiblePostBetween source destination post)
    (bounded : post.BoundedBy q)
    (sourceBelow : DDLedger.LedgerBelow q source)
    (freshAbove : ∀ varId, varId ∈ fresh → q.nextCap ≤ varId.id) :
    AdmissiblePostBetween
      (source.setOrigins fresh .structuralFlexible)
      (destination.setOrigins fresh .structuralFlexible) post := by
  constructor
  intro varId
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases selected : varId ∈ fresh
  · simp [selected]
  · rw [if_neg selected]
    cases sourceOrigin : source.originOf varId with
    | rigid =>
        rcases (by simpa [sourceOrigin] using between.cap varId) with
          ⟨fixed, destinationRigid⟩
        exact ⟨fixed, by
          rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg selected]
          exact destinationRigid⟩
    | renameOnly =>
        rcases (by simpa [sourceOrigin] using between.cap varId) with
          ⟨image, imageEquation, imageSafe⟩
        have varBelow : varId.id < q.nextCap :=
          sourceBelow varId (originOf_ne_rigid_mem_keys (by simp [sourceOrigin]))
        have imageBelow : image.id < q.nextCap := by
          apply bounded.capImagesBounded varId varBelow image
          rw [imageEquation]
          simp [Cap.fcv]
        have imageNotSelected : image ∉ fresh := by
          intro membership
          exact Nat.not_le_of_lt imageBelow (freshAbove image membership)
        exact ⟨image, imageEquation, by
          rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg imageNotSelected]
          exact imageSafe⟩
    | structuralFlexible => trivial

theorem admissiblePostBetween_markSchemeInstance_of_bounded
    {q : InferenceBase.FreshSupply}
    {source destination : CapabilityOriginLedger} {post : Subst}
    (between : AdmissiblePostBetween source destination post)
    (bounded : post.BoundedBy q)
    (sourceBelow : DDLedger.LedgerBelow q source) (scheme : Scheme) :
    AdmissiblePostBetween
      (DDLedger.markSchemeInstance source q scheme)
      (DDLedger.markSchemeInstance destination q scheme) post := by
  exact admissiblePostBetween_setFreshRenameOnly_of_bounded between bounded
    sourceBelow (fun varId membership =>
      (Scheme.mem_canonicalCapImages_bounds membership).1)

theorem admissiblePostBetween_markCtorInstance_of_bounded
    {q : InferenceBase.FreshSupply}
    {source destination : CapabilityOriginLedger} {post : Subst}
    (between : AdmissiblePostBetween source destination post)
    (bounded : post.BoundedBy q)
    (sourceBelow : DDLedger.LedgerBelow q source) (scheme : CtorScheme) :
    AdmissiblePostBetween
      (DDLedger.markCtorInstance source q scheme)
      (DDLedger.markCtorInstance destination q scheme) post := by
  exact admissiblePostBetween_setFreshStructural_of_bounded between bounded
    sourceBelow (freshCapImages_above q scheme.capBinders)

/-- Structural ctor-instance allocation also preserves bounded residual
admissibility.  A residual image of an old variable is itself below the old
cut, so it cannot accidentally become one of the new structural variables. -/
theorem admissiblePost_markCtorInstance_of_bounded
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {post : Subst} (admissible : AdmissiblePost ledger post)
    (bounded : post.BoundedBy q) (scheme : CtorScheme) :
    AdmissiblePost (DDLedger.markCtorInstance ledger q scheme) post := by
  constructor
  intro varId
  by_cases below : varId.id < q.nextCap
  · have notFresh : varId ∉ Inference.freshCapImages q scheme.capBinders := by
      intro membership
      exact Nat.not_le_of_lt below
        (freshCapImages_above q scheme.capBinders varId membership)
    rw [DDLedger.markCtorInstance,
      CapabilityOriginLedger.originOf_setOrigins_eq, if_neg notFresh]
    cases oldOrigin : ledger.originOf varId with
    | rigid => exact admissible.cap.rigid oldOrigin
    | renameOnly =>
        rcases admissible.cap.renameOnly oldOrigin with
          ⟨image, imageEquation, imageSafe⟩
        have imageBelow : image.id < q.nextCap := by
          apply bounded.capImagesBounded varId below image
          rw [imageEquation]
          simp [Cap.fcv]
        have imageNotFresh :
            image ∉ Inference.freshCapImages q scheme.capBinders := by
          intro membership
          exact Nat.not_le_of_lt imageBelow
            (freshCapImages_above q scheme.capBinders image membership)
        refine ⟨image, imageEquation, ?_⟩
        rw [CapabilityOriginLedger.originOf_setOrigins_eq,
          if_neg imageNotFresh]
        exact imageSafe
    | structuralFlexible => trivial
  · have fixed := bounded.capFixedAbove varId (Nat.le_of_not_gt below)
    cases origin : (DDLedger.markCtorInstance ledger q scheme).originOf varId with
    | rigid => exact fixed
    | renameOnly => exact ⟨varId, fixed, by simp [origin]⟩
    | structuralFlexible => trivial

theorem subst_seq_self_eq_of_idempotent {substitution : Subst}
    (idempotent : substitution.Idempotent) :
    Subst.seq substitution substitution = substitution := by
  apply PhasedPost.subst_ext
  · funext varId
    have fixed := idempotent (.matcher (.var varId) .unit)
    have capFixed :
        (substitution.cap varId).apply substitution.cap =
          substitution.cap varId :=
      (Ty.matcher.inj fixed).1
    simpa only [Subst.seq, CapSubst.comp] using capFixed
  · funext varId
    change substitution.apply (substitution.target varId) =
      substitution.target varId
    simpa only [Subst.apply, Ty.applyCapability, Ty.applyTarget] using
      idempotent (.var varId)

/-- A scheme obtained by looking up an already-normalized context is fixed
by the idempotent substitution used for that normalization. -/
theorem normalizedContext_lookup_scheme_fixed
    {substitution : Subst} {context : Context} {name : String}
    {scheme : Scheme} (idempotent : substitution.Idempotent)
    (lookup : (context.applySubst substitution).find? name = some scheme) :
    scheme.applyMeta substitution = scheme := by
  have contextFixed :
      (context.applySubst substitution).applySubst substitution =
        context.applySubst substitution := by
    rw [← Context.applySubst_seq,
      subst_seq_self_eq_of_idempotent idempotent]
  have lookupFixed := congrArg (fun actual : Context => actual.find? name)
    contextFixed
  rw [Context.find?_applySubst, lookup] at lookupFixed
  exact Option.some.inj lookupFixed

/-- Trace-only events preserve a traversal boundary. -/
def TraversalStateCorrespondence.recordEvent
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (event : TraceEvent)
    (eventRecorded : ∀ varId, varId ∈ event.allocatedCapVars →
      varId ∈ state.capabilityOrigins.map Prod.fst) :
    TraversalStateCorrespondence q declarative ledger
      (state.recordEvent event) := by
  let extension := relation.prevailing.recordEventExtension event
  exact
    ⟨relation.supply_eq, extension.after,
      relation.declarative_bounded, relation.executable_bounded,
      relation.forward_bounded, relation.reverse_bounded,
      relation.ledger_below, relation.executable_ledger_below,
      relation.protected_origins.recordEvent event,
      relation.protected_below.recordEvent_of_allocated event,
      relation.allocated_recorded.recordEvent event eventRecorded⟩

/-- Provenance-source recording is state-neutral for the typing relation. -/
def stateBisimulationRecordSourceExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (source : ProducerSource) :
    BisimulationExtension relation ledger declarative
      (state.recordSource source) where
  after :=
    { forward := relation.forward
      forwardEquation := by simpa [InferState.prevailing,
        InferState.recordSource] using relation.forwardEquation
      ledgerBisimulation := relation.ledgerBisimulation
      declarativeIdempotent := relation.declarativeIdempotent
      reverse := relation.reverse
      reverseEquation := by simpa [InferState.prevailing,
        InferState.recordSource] using relation.reverseEquation
      executableIdempotent := relation.executableIdempotent }
  transportTy := by
    intro declarativeTarget executableTarget related
    exact ⟨by simpa [InferState.prevailing, InferState.recordSource]
        using related.forward,
      by simpa [InferState.prevailing, InferState.recordSource]
        using related.reverse⟩

def TraversalStateCorrespondence.recordSource
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (source : ProducerSource) :
    TraversalStateCorrespondence q declarative ledger
      (state.recordSource source) := by
  let extension := stateBisimulationRecordSourceExtension
    relation.prevailing source
  exact
    ⟨relation.supply_eq, extension.after,
      relation.declarative_bounded, relation.executable_bounded,
      relation.forward_bounded, relation.reverse_bounded,
      relation.ledger_below, relation.executable_ledger_below,
      relation.protected_origins.recordSource source,
      relation.protected_below.recordSource source,
      relation.allocated_recorded.recordSource source⟩

/-- Visiting one syntax node is trace-only. -/
def TraversalStateCorrespondence.visit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) := by
  exact relation.recordEvent (.visit kind path) (by simp [TraceEvent.allocatedCapVars])

def TraversalStateCorrespondence.visitExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    BisimulationExtension relation.prevailing ledger declarative
      (Inference.visit state kind path) :=
  relation.prevailing.recordEventExtension (.visit kind path)

def TraversalStateCorrespondence.afterVisit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) :=
  relation.visit kind path

def stateBisimulationFreshTyExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (before : StateBisimulation ledger declarative state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before ledger declarative
      (state.freshTy origin).2 where
  after :=
    { forward := before.forward
      forwardEquation := by
        change declarative = Subst.seq before.forward state.prevailing
        exact before.forwardEquation
      ledgerBisimulation := before.ledgerBisimulation
      declarativeIdempotent := before.declarativeIdempotent
      reverse := before.reverse
      reverseEquation := by
        change state.prevailing = Subst.seq before.reverse declarative
        exact before.reverseEquation
      executableIdempotent := before.executableIdempotent }
  transportTy := by
    intro declarativeTarget executableTarget related
    refine ⟨?_, ?_⟩
    · change declarative.apply declarativeTarget =
        before.forward.apply (state.prevailing.apply executableTarget)
      exact related.forward
    · change state.prevailing.apply executableTarget =
        before.reverse.apply (declarative.apply declarativeTarget)
      exact related.reverse

def TraversalStateCorrespondence.afterVisitFreshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (origin : ConstraintOrigin) :
    TraversalStateCorrespondence { q with nextTy := q.nextTy + 1 }
      declarative ledger ((Inference.visit state kind path).freshTy origin).2 :=
  by
    let entered := relation.visit kind path
    let extension := SupplyExtends.bumpTy q 1
    refine
      ⟨?_,
        (stateBisimulationFreshTyExtension
          (relation.visitExtension kind path).after origin).after,
        entered.declarative_bounded.mono extension,
        entered.executable_bounded.mono extension,
        entered.forward_bounded.mono extension,
        entered.reverse_bounded.mono extension,
        entered.ledger_below.mono extension,
        entered.executable_ledger_below.mono extension,
        entered.protected_origins.freshTy origin,
        entered.protected_below.freshTy origin,
        entered.allocated_recorded.freshTy origin⟩
    change { state.supply with nextTy := state.supply.nextTy + 1 } =
      { q with nextTy := q.nextTy + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextTy := supply.nextTy + 1 }) relation.supply_eq

def bisimulationExtensionChain3
    {ledger₀ ledger₁ ledger₂ ledger₃ : CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ : Subst} {s₀ s₁ s₂ s₃ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃) :
    BisimulationExtension before ledger₃ S₃ s₃ where
  after := third.after
  transportTy := fun related =>
    third.transportTy (second.transportTy (first.transportTy related))

def bisimulationExtensionChain4
    {ledger₀ ledger₁ ledger₂ ledger₃ ledger₄ :
      CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ S₄ : Subst}
    {s₀ s₁ s₂ s₃ s₄ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃)
    (fourth : BisimulationExtension third.after ledger₄ S₄ s₄) :
    BisimulationExtension before ledger₄ S₄ s₄ where
  after := fourth.after
  transportTy := fun related => fourth.transportTy
    (third.transportTy (second.transportTy (first.transportTy related)))

structure FreshTyCompletion
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (state : InferState)
    (origin : ConstraintOrigin) : Type where
  target_eq : (state.freshTy origin).1 = .var q.nextTy
  state : TraversalStateCorrespondence
    { q with nextTy := q.nextTy + 1 } declarative ledger
    (state.freshTy origin).2

/-- One target allocation agrees literally with the supply-indexed DD
allocation and leaves the prevailing substitution and origin ledger alone. -/
def TraversalStateCorrespondence.freshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    FreshTyCompletion q declarative ledger state origin := by
  let extension := SupplyExtends.bumpTy q 1
  constructor
  · change Ty.var state.supply.nextTy = Ty.var q.nextTy
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      Ty.var supply.nextTy) relation.supply_eq
  · refine
      ⟨?_,
        (stateBisimulationFreshTyExtension relation.prevailing origin).after,
        relation.declarative_bounded.mono extension,
        relation.executable_bounded.mono extension,
        relation.forward_bounded.mono extension,
        relation.reverse_bounded.mono extension,
        relation.ledger_below.mono extension,
        relation.executable_ledger_below.mono extension,
        relation.protected_origins.freshTy origin,
        relation.protected_below.freshTy origin,
        relation.allocated_recorded.freshTy origin⟩
    change { state.supply with nextTy := state.supply.nextTy + 1 } =
      { q with nextTy := q.nextTy + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextTy := supply.nextTy + 1 }) relation.supply_eq

def TraversalStateCorrespondence.freshTyExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension relation.prevailing ledger declarative
      (state.freshTy origin).2 :=
  stateBisimulationFreshTyExtension relation.prevailing origin

/-- Exact-state initialization is the diagonal of the traversal relation. -/
def TraversalStateCorrespondence.refl
    (state : InferState) (idempotent : state.prevailing.Idempotent)
    (bounded : state.prevailing.BoundedBy state.supply)
    (ledgerBelow : DDLedger.LedgerBelow state.supply
      state.capabilityOrigins)
    (protectedOrigins : ProtectedCapOrigins state)
    (protectedBelow : ProtectedCapsBelowSupply state)
    (allocatedRecorded : AllocatedCapsRecorded state) :
    TraversalStateCorrespondence state.supply state.prevailing
      state.capabilityOrigins state :=
  let prevailing := StateBisimulation.refl state idempotent
  ⟨rfl, prevailing, bounded, bounded,
    Subst.boundedBy_id _, Subst.boundedBy_id _, ledgerBelow, ledgerBelow,
    protectedOrigins, protectedBelow, allocatedRecorded⟩

/-- Output relation for one raw synthesized type.  The two raw types need not
be syntactically equal (context instantiation may see differently oriented
prevailing MGUs), but their resolved forms are mutual instances through the
same residuals that relate the two prevailing states. -/
structure TypedTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTarget : Ty)
    (executable : InferState) (executableTarget : Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  target : TyBisimulation state.prevailing declarativeTarget executableTarget

/-- Output relation for a left-to-right list of synthesized types. -/
structure TypedListTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTargets : List Ty)
    (executable : InferState) (executableTargets : List Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  targets : TyListBisimulation state.prevailing declarativeTargets
    executableTargets

/-- A common raw type on both sides automatically gives a typed relation. -/
def TypedTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedTraversalStateCorrespondence q' declarative ledger target executable
      target := by
  exact ⟨relation, relation.prevailing.sameTarget target⟩

/-- A common raw list gives the pointwise list relation. -/
def TypedListTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {targets : List Ty}
    {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedListTraversalStateCorrespondence q' declarative ledger targets
      executable targets := by
  refine ⟨relation, ?_⟩
  induction targets with
  | nil => exact .nil
  | cons target targets induction =>
      exact .cons (relation.prevailing.sameTarget target) induction

/-- Pointwise mutual type correspondence is closed under product formation. -/
theorem tyListBisimulation_prod
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeTargets executableTargets : List Ty}
    (relation : TyListBisimulation state declarativeTargets executableTargets) :
    TyBisimulation state (.prod declarativeTargets)
      (.prod executableTargets) := by
  constructor
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).forward
    | cons head tail induction =>
        have headForward := head.forward
        unfold Subst.apply at headForward
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headForward]
        injection induction with tailEquality
        rw [tailEquality]
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).reverse
    | cons head tail induction =>
        have headReverse := head.reverse
        unfold Subst.apply at headReverse
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headReverse]
        injection induction with tailEquality
        rw [tailEquality]

/-- Mutual type correspondence is compositional for function types. -/
theorem tyBisimulation_fn
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeDomain declarativeBody executableDomain executableBody : Ty}
    (domain : TyBisimulation state declarativeDomain executableDomain)
    (body : TyBisimulation state declarativeBody executableBody) :
    TyBisimulation state (.fn declarativeDomain declarativeBody)
      (.fn executableDomain executableBody) := by
  constructor
  · have domainForward := domain.forward
    have bodyForward := body.forward
    unfold Subst.apply at domainForward bodyForward ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainForward, bodyForward]
  · have domainReverse := domain.reverse
    have bodyReverse := body.reverse
    unfold Subst.apply at domainReverse bodyReverse ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainReverse, bodyReverse]

/-- Output package for expression synthesis. -/
def SynthCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (target : Ty)
    (result : ExprResult) : Type :=
  TypedTraversalStateCorrespondence q' declarative ledger target result.state
    result.target

/-- Output package for expression-list synthesis. -/
def SynthsCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (targets : List Ty)
    (result : ExprsResult) : Type :=
  TypedListTraversalStateCorrespondence q' declarative ledger targets
    result.state result.targets

/-- Deterministic completion package for one context-scheme instantiation.
It is separated from expression synthesis because variable traversal may add
a direct-self source after instantiation, while `let` reuses the same paired
context and canonical-opening bridge. -/
structure SchemeInstantiationCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (result : Ty × InferState) (q' : InferenceBase.FreshSupply)
    (ledger' : CapabilityOriginLedger) (target : Ty) : Type where
  supply_eq : result.2.supply = q'
  transition : BisimulationExtension before.prevailing ledger' S result.2
  declarative_bounded : S.BoundedBy q'
  executable_bounded : result.2.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger'
  executable_ledger_below :
    DDLedger.LedgerBelow q' result.2.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.2
  protected_below : ProtectedCapsBelowSupply result.2
  allocated_recorded : AllocatedCapsRecorded result.2
  target : TyBisimulation transition.after target result.1

/-- Corresponding normalized schemes instantiate in lockstep.  The fresh
images and ledger update are determined solely by binder arities; ambient
metavariable transport affects only the instantiated body. -/
def instantiateSchemeInState_complete
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (declarativeScheme executableScheme : Scheme)
    (forwardScheme : declarativeScheme =
      executableScheme.applyMeta before.prevailing.forward)
    (reverseScheme : executableScheme =
      declarativeScheme.applyMeta before.prevailing.reverse)
    (declarativeNormalized : declarativeScheme.applyMeta S =
      declarativeScheme)
    (executableNormalized : executableScheme.applyMeta initial.prevailing =
      executableScheme) :
    SchemeInstantiationCompletion before
      (instantiateSchemeInState signature rawContext normalizedContext name
        initial executableScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).supply
      (DDLedger.markSchemeInstance ledger q declarativeScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).value := by
  let operation := instantiateSchemeInState signature rawContext
    normalizedContext name initial executableScheme
  let q' := (InferenceBase.instantiateScheme q declarativeScheme).supply
  let ledger' := DDLedger.markSchemeInstance ledger q declarativeScheme
  have supplyExtension : SupplyExtends q q' := by
    exact SupplyExtends.instantiateScheme q declarativeScheme
  have schemeImagesEq :
      Scheme.canonicalCapImages q declarativeScheme =
        Scheme.canonicalCapImages q executableScheme := by
    rw [forwardScheme]
    simp
  let after : StateBisimulation ledger' S operation.2 :=
    { forward := before.prevailing.forward
      forwardEquation := by
        change S = Subst.seq before.prevailing.forward operation.2.prevailing
        simpa [operation, Inference.instantiateSchemeInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.forwardEquation
      ledgerBisimulation := by
        constructor
        · simpa [ledger', operation, Inference.instantiateSchemeInState,
            before.supply_eq, DDLedger.markSchemeInstance, schemeImagesEq] using
            admissiblePostBetween_markSchemeInstance_of_bounded
              before.prevailing.ledgerBisimulation.forwardBetween
              before.forward_bounded before.executable_ledger_below
              declarativeScheme
        · simpa [ledger', operation, Inference.instantiateSchemeInState,
            before.supply_eq, DDLedger.markSchemeInstance, schemeImagesEq] using
            admissiblePostBetween_markSchemeInstance_of_bounded
              before.prevailing.ledgerBisimulation.reverseBetween
              before.reverse_bounded before.ledger_below declarativeScheme
      declarativeIdempotent := before.prevailing.declarativeIdempotent
      reverse := before.prevailing.reverse
      reverseEquation := by
        change operation.2.prevailing = Subst.seq before.prevailing.reverse S
        simpa [operation, Inference.instantiateSchemeInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.reverseEquation
      executableIdempotent := before.prevailing.executableIdempotent }
  let transition : BisimulationExtension before.prevailing ledger' S
      operation.2 :=
    { after := after
      transportTy := by
        intro declarativeTarget executableTarget related
        exact ⟨by simpa [after, operation, Inference.instantiateSchemeInState,
            InferState.prevailing, InferState.recordEvent]
            using related.forward,
          by simpa [after, operation, Inference.instantiateSchemeInState,
            InferState.prevailing, InferState.recordEvent]
            using related.reverse⟩ }
  have actualTarget : operation.1 =
      (InferenceBase.instantiateScheme q executableScheme).value := by
    simp [operation, Inference.instantiateSchemeInState, before.supply_eq]
  have canonical := canonicalInstantiation_tyBisimulation before.prevailing q
    declarativeScheme executableScheme before.declarative_bounded
    before.executable_bounded before.forward_bounded before.reverse_bounded
    forwardScheme reverseScheme declarativeNormalized executableNormalized
  have schemeSupplyEq :
      (InferenceBase.instantiateScheme q executableScheme).supply = q' := by
    dsimp [q']
    rw [forwardScheme]
    cases executableScheme
    rfl
  refine
    { supply_eq := ?_
      transition := transition
      declarative_bounded := before.declarative_bounded.mono supplyExtension
      executable_bounded := ?_
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := DDLedger.LedgerBelow.markSchemeInstance declarativeScheme
        before.ledger_below
      executable_ledger_below := ?_
      protected_origins := before.protected_origins.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      protected_below := before.protected_below.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      allocated_recorded := before.allocated_recorded.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      target := ?_ }
  · simpa [operation, Inference.instantiateSchemeInState,
      before.supply_eq] using schemeSupplyEq
  · change initial.prevailing.BoundedBy
      (InferenceBase.instantiateScheme q declarativeScheme).supply
    exact before.executable_bounded.mono supplyExtension
  · have actualBelow := DDLedger.LedgerBelow.markSchemeInstance
      executableScheme before.executable_ledger_below
    rw [schemeSupplyEq] at actualBelow
    simpa [operation, Inference.instantiateSchemeInState, before.supply_eq,
      DDLedger.markSchemeInstance] using actualBelow
  · rw [actualTarget]
    exact transition.transportTy canonical

/-- Deterministic completion package for one constructor/primitive scheme
instantiation.  Both the argument list and result target are retained because
the former seeds recursive checking while the latter is exported afterward. -/
structure CtorInstantiationCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (result : (List Ty × Ty) × InferState)
    (q' : InferenceBase.FreshSupply) (ledger' : CapabilityOriginLedger)
    (arguments : List Ty) (target : Ty) : Type where
  supply_eq : result.2.supply = q'
  transition : BisimulationExtension before.prevailing ledger' S result.2
  declarative_bounded : S.BoundedBy q'
  executable_bounded : result.2.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger'
  executable_ledger_below :
    DDLedger.LedgerBelow q' result.2.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.2
  protected_below : ProtectedCapsBelowSupply result.2
  allocated_recorded : AllocatedCapsRecorded result.2
  arguments : TyListBisimulation transition.after arguments result.1.1
  target : TyBisimulation transition.after target result.1.2

/-- Constructor and primitive lookup use the same deterministic scheme
instantiation.  Since the signature scheme is shared literally, both sides
allocate identical raw argument/result types and differ only in prevailing
state. -/
def instantiateCtorInState_complete
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (scheme : CtorScheme) :
    CtorInstantiationCompletion before (instantiateCtorInState initial scheme)
      (InferenceBase.instantiateCtorScheme q scheme).supply
      (DDLedger.markCtorInstance ledger q scheme)
      (InferenceBase.instantiateCtorScheme q scheme).value.1
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  let operation := instantiateCtorInState initial scheme
  let q' := (InferenceBase.instantiateCtorScheme q scheme).supply
  let ledger' := DDLedger.markCtorInstance ledger q scheme
  have supplyExtension : SupplyExtends q q' :=
    SupplyExtends.instantiateCtorScheme q scheme
  let after : StateBisimulation ledger' S operation.2 :=
    { forward := before.prevailing.forward
      forwardEquation := by
        change S = Subst.seq before.prevailing.forward operation.2.prevailing
        simpa [operation, Inference.instantiateCtorInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.forwardEquation
      ledgerBisimulation := by
        constructor
        · simpa [ledger', operation, Inference.instantiateCtorInState,
            before.supply_eq, DDLedger.markCtorInstance] using
            admissiblePostBetween_markCtorInstance_of_bounded
              before.prevailing.ledgerBisimulation.forwardBetween
              before.forward_bounded before.executable_ledger_below scheme
        · simpa [ledger', operation, Inference.instantiateCtorInState,
            before.supply_eq, DDLedger.markCtorInstance] using
            admissiblePostBetween_markCtorInstance_of_bounded
              before.prevailing.ledgerBisimulation.reverseBetween
              before.reverse_bounded before.ledger_below scheme
      declarativeIdempotent := before.prevailing.declarativeIdempotent
      reverse := before.prevailing.reverse
      reverseEquation := by
        change operation.2.prevailing = Subst.seq before.prevailing.reverse S
        simpa [operation, Inference.instantiateCtorInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.reverseEquation
      executableIdempotent := before.prevailing.executableIdempotent }
  let transition : BisimulationExtension before.prevailing ledger' S
      operation.2 :=
    { after := after
      transportTy := by
        intro declarativeTarget executableTarget related
        exact ⟨by simpa [after, operation, Inference.instantiateCtorInState,
            InferState.prevailing, InferState.recordEvent]
            using related.forward,
          by simpa [after, operation, Inference.instantiateCtorInState,
            InferState.prevailing, InferState.recordEvent]
            using related.reverse⟩ }
  have actualValue : operation.1 =
      (InferenceBase.instantiateCtorScheme q scheme).value := by
    simp [operation, Inference.instantiateCtorInState, before.supply_eq]
  have sameArguments : TyListBisimulation transition.after
      (InferenceBase.instantiateCtorScheme q scheme).value.1
      (InferenceBase.instantiateCtorScheme q scheme).value.1 := by
    induction (InferenceBase.instantiateCtorScheme q scheme).value.1 with
    | nil => exact .nil
    | cons head tail induction =>
        exact .cons (transition.after.sameTarget head) induction
  refine
    { supply_eq := by
        simp [Inference.instantiateCtorInState, before.supply_eq]
      transition := transition
      declarative_bounded := before.declarative_bounded.mono supplyExtension
      executable_bounded := ?_
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := DDLedger.LedgerBelow.markCtorInstance scheme
        before.ledger_below
      executable_ledger_below := by
        simpa [operation, Inference.instantiateCtorInState, before.supply_eq,
          DDLedger.markCtorInstance]
          using (DDLedger.LedgerBelow.markCtorInstance scheme
            before.executable_ledger_below)
      protected_origins := before.protected_origins.instantiateCtorInState
        before.protected_below scheme
      protected_below := before.protected_below.instantiateCtorInState scheme
      allocated_recorded := before.allocated_recorded.instantiateCtorInState
        scheme
      arguments := ?_
      target := ?_ }
  · change initial.prevailing.BoundedBy
      (InferenceBase.instantiateCtorScheme q scheme).supply
    exact before.executable_bounded.mono supplyExtension
  · rw [actualValue]
    exact sameArguments
  · rw [actualValue]
    exact transition.after.sameTarget _

def CtorInstantiationCompletion.correspondence
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger initial}
    {result : (List Ty × Ty) × InferState}
    {q' : InferenceBase.FreshSupply} {ledger' : CapabilityOriginLedger}
    {arguments : List Ty} {target : Ty}
    (completion : CtorInstantiationCompletion before result q' ledger'
      arguments target) :
    TraversalStateCorrespondence q' S ledger' result.2 :=
  ⟨completion.supply_eq, completion.transition.after,
    completion.declarative_bounded, completion.executable_bounded,
    completion.forward_bounded, completion.reverse_bounded,
    completion.ledger_below, completion.executable_ledger_below,
    completion.protected_origins, completion.protected_below,
    completion.allocated_recorded⟩

/-- A successful executable expression run paired with its typed output
correspondence.  The package lives in `Type` because the state bisimulation
retains the concrete residual substitutions used by later cuts. -/
structure SynthRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  result : ExprResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below :
    DDLedger.LedgerBelow q' result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target

/-- List counterpart of `SynthRunCompletion`. -/
structure SynthsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) : Type where
  result : ExprsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below :
    DDLedger.LedgerBelow q' result.state.capabilityOrigins
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets

/-- Repackage a run's proof-relevant transition as the output-only relation. -/
def SynthRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger} {target : Ty}
    (run : SynthRunCompletion before operation q' declarative ledger target) :
    SynthCompletion q' declarative ledger target run.result :=
  ⟨⟨run.supply_eq, run.transition.after,
      run.declarative_bounded, run.executable_bounded,
      run.forward_bounded, run.reverse_bounded, run.ledger_below,
      run.executable_ledger_below,
      run.protected_origins, run.protected_below, run.allocated_recorded⟩,
    run.target⟩

def SynthsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty}
    (run : SynthsRunCompletion before operation q' declarative ledger targets) :
    SynthsCompletion q' declarative ledger targets run.result :=
  ⟨⟨run.supply_eq, run.transition.after,
      run.declarative_bounded, run.executable_bounded,
      run.forward_bounded, run.reverse_bounded, run.ledger_below,
      run.executable_ledger_below,
      run.protected_origins, run.protected_below, run.allocated_recorded⟩,
    run.targets⟩

/-- State-only run package used by alignment cuts. -/
structure StateRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  result : InferState
  success : operation = some result
  supply_eq : result.supply = q'
  transition : BisimulationExtension before.prevailing ledger declarative
    result
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  executable_ledger_below :
    DDLedger.LedgerBelow q' result.capabilityOrigins
  protected_origins : ProtectedCapOrigins result
  protected_below : ProtectedCapsBelowSupply result
  allocated_recorded : AllocatedCapsRecorded result

def StateRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    (run : StateRunCompletion before operation q' declarative ledger) :
    TraversalStateCorrespondence q' declarative ledger run.result :=
  ⟨run.supply_eq, run.transition.after,
    run.declarative_bounded, run.executable_bounded,
    run.forward_bounded, run.reverse_bounded, run.ledger_below,
    run.executable_ledger_below,
    run.protected_origins, run.protected_below, run.allocated_recorded⟩

/-- Shared constructor/primitive suffix: once argument checking has produced
its state run, selectively freeze the surviving instance leaves, record the
final expression event, and export the raw result target. -/
def StateRunCompletion.freezeAndFinishExpr
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    (run : StateRunCompletion before operation q' declarative ledger)
    (expression : Expr) (path : SyntaxPath) (capImages : List CapVar)
    (target : Ty) :
    SynthRunCompletion before
      (do
        let state ← operation
        let frozen := state.freezeCapabilityExport capImages target
        pure (finishExpr expression path target frozen))
      q' declarative
      (DDLedger.freezeExport ledger declarative capImages target) target := by
  let checked := run.result
  let frozen := checked.freezeCapabilityExport capImages target
  let result := finishExpr expression path target frozen
  let frozenRelation := run.completion.freezeCapabilityExport capImages target
  let freezeExtension :=
    run.completion.freezeCapabilityExportExtension capImages target
  let finishEvent := TraceEvent.inferredExpr expression target path
  let finishExtension :=
    freezeExtension.after.recordEventExtension finishEvent
  let finalRelation := frozenRelation.recordEvent finishEvent
    (by simp [finishEvent, TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := finalRelation.supply_eq
      transition := (run.transition.seq freezeExtension).seq finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := finishExtension.after.sameTarget target }
  rw [run.success]
  rfl

/-! ## Ordinary paired alignment -/

/-- Once solver completeness supplies the concrete target-equality step, one
resolved equality cut preserves the proof-relevant traversal invariant.  This
lemma isolates the traversal algebra from the executable solver's fuel proof. -/
noncomputable def runResolvedTargetEq_complete_of_step
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin} {step : SolveStep}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta)
    (solver : PairedUnification.PairedResult initial.capabilityOrigins
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
    (stepSuccess : solveResolvedWithLedger initial.capabilityOrigins
      initial.trace.solves.length
      origin (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step)
    (stepDelta : step.delta = solver.subst) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.targetEq (initial.prevailing.apply executableLeft)
          (initial.prevailing.apply executableRight))) q
      (Subst.seq delta S) ledger := by
  let result := initial.recordSolve step
  let transition := relation.prevailing.pairedCut_recordSolve left right dd
    solver stepDelta
  have ddDeltaBounded : delta.BoundedBy q :=
    dd.exact.boundedBy
      (relation.declarative_bounded.apply declarativeLeftBounded)
      (relation.declarative_bounded.apply declarativeRightBounded)
  have executableDeltaBounded : solver.subst.BoundedBy q :=
    solver.exactPairedMGU.boundedBy
      (relation.executable_bounded.apply executableLeftBounded)
      (relation.executable_bounded.apply executableRightBounded)
  refine
    { result := result
      success := ?_
      supply_eq := relation.supply_eq
      transition := transition
      declarative_bounded := ddDeltaBounded.seq relation.declarative_bounded
      executable_bounded := ?_
      forward_bounded := ?_
      reverse_bounded := ?_
      ledger_below := relation.ledger_below
      executable_ledger_below := relation.executable_ledger_below
      protected_origins := relation.protected_origins.recordSolve step
      protected_below := relation.protected_below.recordSolve step
      allocated_recorded := relation.allocated_recorded.recordSolve step }
  · unfold runResolvedConstraint
    rw [stepSuccess]
    rfl
  · rw [InferState.prevailing_recordSolve, stepDelta]
    exact executableDeltaBounded.seq relation.executable_bounded
  · change (Subst.seq delta relation.prevailing.forward).BoundedBy q
    exact ddDeltaBounded.seq relation.forward_bounded
  · change (Subst.seq solver.subst relation.prevailing.reverse).BoundedBy q
    exact executableDeltaBounded.seq relation.reverse_bounded

/-- A DD solution on the declarative views supplies an admissible solution on
the bisimilar executable views.  Paired-solver completeness therefore creates
the concrete step internally; callers need not predict its orientation. -/
noncomputable def runResolvedTargetEq_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.targetEq (initial.prevailing.apply executableLeft)
          (initial.prevailing.apply executableRight))) q
      (Subst.seq delta S) ledger := by
  let combined := Subst.seq delta relation.prevailing.forward
  let transported := Subst.seq relation.prevailing.reverse combined
  have transportedAdmissible :
      AdmissiblePost initial.capabilityOrigins transported := by
    exact relation.prevailing.ledgerBisimulation.transportAdmissible
      dd.admissible
  have combinedSound :
      combined.apply (initial.prevailing.apply executableLeft) =
        combined.apply (initial.prevailing.apply executableRight) := by
    simp only [combined, Subst.seq_apply, ← left.forward, ← right.forward]
    exact dd.exact.1.1
  have transportedSound :
      transported.apply (initial.prevailing.apply executableLeft) =
        transported.apply (initial.prevailing.apply executableRight) := by
    simp only [transported, Subst.seq_apply]
    exact congrArg relation.prevailing.reverse.apply combinedSound
  have solverExists :=
    solveTargetEqWithLedger_complete_of_admissible transportedAdmissible
      transportedSound initial.trace.solves.length origin
  let solver := Classical.choose solverExists
  have stepExists := Classical.choose_spec solverExists
  let step := Classical.choose stepExists
  have stepFacts := Classical.choose_spec stepExists
  have solverSuccess := stepFacts.1
  have stepDelta := stepFacts.2
  have stepSuccess : solveResolvedWithLedger initial.capabilityOrigins
      initial.trace.solves.length origin
      (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step := by
    exact solverSuccess
  exact runResolvedTargetEq_complete_of_step relation left right
    declarativeLeftBounded declarativeRightBounded executableLeftBounded
    executableRightBounded dd solver stepSuccess stepDelta

/-- The ordinary branch of `alignTypes` is complete.  Matcher/slot two-stage
branches are added by the same state-cut lemma after capability-solver
completeness is connected. -/
noncomputable def alignTypes_ordinary_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (_declarativeClass :
      alignPairClass (S.apply declarativeLeft) (S.apply declarativeRight) =
        .ordinary)
    (executableClass :
      alignPairClass (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight) = .ordinary)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta) :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q
      (Subst.seq delta S) ledger := by
  have core := runResolvedTargetEq_complete (origin := origin) relation left right
    declarativeLeftBounded declarativeRightBounded executableLeftBounded
    executableRightBounded dd
  let aligned := core.result
  let result := aligned.recordEvent (.typeAlignment
    initial.trace.solves.length aligned.trace.solves.length executableLeft
    executableRight (initial.prevailing.apply executableLeft)
    (initial.prevailing.apply executableRight))
  let finishExtension := core.transition.after.recordEventExtension
    (.typeAlignment initial.trace.solves.length aligned.trace.solves.length
      executableLeft executableRight
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
  refine
    { result := result
      success := ?_
      supply_eq := core.supply_eq
      transition := core.transition.seq finishExtension
      declarative_bounded := core.declarative_bounded
      executable_bounded := core.executable_bounded
      forward_bounded := core.forward_bounded
      reverse_bounded := core.reverse_bounded
      ledger_below := core.ledger_below
      executable_ledger_below := core.executable_ledger_below
      protected_origins := core.protected_origins.recordEvent _
      protected_below := core.protected_below.recordEvent_of_allocated _
      allocated_recorded := core.allocated_recorded.recordEvent _
        (by simp [TraceEvent.allocatedCapVars]) }
  · have coreEq : alignTypesCore initial origin executableLeft
        executableRight =
        runResolvedConstraint initial origin
          (.targetEq (initial.prevailing.apply executableLeft)
            (initial.prevailing.apply executableRight)) := by
      generalize leftEq : initial.prevailing.apply executableLeft = leftView
      generalize rightEq : initial.prevailing.apply executableRight = rightView
      cases leftView <;> cases rightView <;>
        simp_all [alignTypesCore, alignPairClass]
    unfold alignTypes
    rw [coreEq, core.success]
    rfl

/-- Finishing an expression changes only the trace and retains its raw target. -/
def synthCompletion_finishExpr
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {state : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger state)
    (expression : Expr) (path : SyntaxPath) :
    SynthCompletion q' declarative ledger target
      (finishExpr expression path target state) := by
  exact TypedTraversalStateCorrespondence.of_sameRaw
    (relation.recordEvent (.inferredExpr expression target path)
      (by simp [TraceEvent.allocatedCapVars]))

/-! ## Solver-independent expression constructors -/

/-- Integer literals always complete at any positive fuel. -/
def inferExprFuel_lit_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {value : Int} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path (.lit value)
        initial) q declarative ledger .int := by
  let entered := visit initial .exprLit path
  let result := finishExpr (.lit value) path .int entered
  let visitExtension := relation.visitExtension .exprLit path
  let finishExtension := visitExtension.after.recordEventExtension
    (.inferredExpr (.lit value) .int path)
  let finalRelation := (relation.visit .exprLit path).recordEvent
    (.inferredExpr (.lit value) .int path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := relation.supply_eq
      transition := visitExtension.seq finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp [inferExprFuel, result, entered, finishExpr, visit]
  exact (visitExtension.seq finishExtension).after.sameTarget .int

/-- Variable synthesis is complete for paired declarative/executable
contexts.  Lookup determines corresponding normalized schemes; canonical
fresh instantiation then advances both traversals through the same binder
spans and origin-ledger batch. -/
noncomputable def inferExprFuel_var_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {q : InferenceBase.FreshSupply}
    {S : Subst} {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeScheme : Scheme}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (contexts : ContextBisimulation relation.prevailing declarativeContext
      executableContext)
    (lookup : (declarativeContext.applySubst S).find? name =
      some declarativeScheme)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.var name) initial)
      (InferenceBase.instantiateScheme q declarativeScheme).supply S
      (DDLedger.markSchemeInstance ledger q declarativeScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).value := by
  cases executableLookup :
      (executableContext.applySubst initial.prevailing).find? name with
  | none =>
      have impossible := congrArg (fun context : Context => context.find? name)
        contexts.forward
      simp [lookup, Context.find?_applySubst, executableLookup] at impossible
  | some executableScheme =>
      have schemeDirections := contexts.lookup lookup executableLookup
      have declarativeNormalized := normalizedContext_lookup_scheme_fixed
        relation.prevailing.declarativeIdempotent lookup
      have executableNormalized := normalizedContext_lookup_scheme_fixed
        relation.prevailing.executableIdempotent executableLookup
      let entered := visit initial .exprVar path
      let enteredRelation := relation.visit .exprVar path
      let normalizedExecutable := executableContext.applySubst entered.prevailing
      have executableLookupEntered : normalizedExecutable.find? name =
          some executableScheme := by
        simpa [normalizedExecutable, entered, visit, InferState.prevailing,
          InferState.recordEvent] using executableLookup
      have forwardEntered : declarativeScheme =
          executableScheme.applyMeta enteredRelation.prevailing.forward := by
        exact schemeDirections.1
      have reverseEntered : executableScheme =
          declarativeScheme.applyMeta enteredRelation.prevailing.reverse := by
        exact schemeDirections.2
      have executableNormalizedEntered :
          executableScheme.applyMeta entered.prevailing = executableScheme := by
        simpa [entered, visit, InferState.prevailing, InferState.recordEvent]
          using executableNormalized
      let instantiated := instantiateSchemeInState signature executableContext
        normalizedExecutable name entered executableScheme
      let instantiationComplete := instantiateSchemeInState_complete
        enteredRelation signature executableContext normalizedExecutable name
        declarativeScheme executableScheme forwardEntered reverseEntered
        declarativeNormalized executableNormalizedEntered
      let instantiatedRelation : TraversalStateCorrespondence
          (InferenceBase.instantiateScheme q declarativeScheme).supply S
          (DDLedger.markSchemeInstance ledger q declarativeScheme)
          instantiated.2 :=
        ⟨instantiationComplete.supply_eq,
          instantiationComplete.transition.after,
          instantiationComplete.declarative_bounded,
          instantiationComplete.executable_bounded,
          instantiationComplete.forward_bounded,
          instantiationComplete.reverse_bounded,
          instantiationComplete.ledger_below,
          instantiationComplete.executable_ledger_below,
          instantiationComplete.protected_origins,
          instantiationComplete.protected_below,
          instantiationComplete.allocated_recorded⟩
      let visitExtension := relation.visitExtension .exprVar path
      cases selfLookup : selfEnv.find? name with
      | none =>
          let finishEvent := TraceEvent.inferredExpr (.var name)
            instantiated.1 path
          let finishExtension :=
            instantiationComplete.transition.after.recordEventExtension
              finishEvent
          let result := finishExpr (.var name) path instantiated.1
            instantiated.2
          let finalRelation := instantiatedRelation.recordEvent finishEvent
            (by simp [finishEvent, TraceEvent.allocatedCapVars])
          refine
            { result := result
              success := ?_
              supply_eq := finalRelation.supply_eq
              transition :=
                (visitExtension.seq instantiationComplete.transition).seq
                  finishExtension
              declarative_bounded := finalRelation.declarative_bounded
              executable_bounded := finalRelation.executable_bounded
              forward_bounded := finalRelation.forward_bounded
              reverse_bounded := finalRelation.reverse_bounded
              ledger_below := finalRelation.ledger_below
              executable_ledger_below := finalRelation.executable_ledger_below
              protected_origins := finalRelation.protected_origins
              protected_below := finalRelation.protected_below
              allocated_recorded := finalRelation.allocated_recorded
              target := finishExtension.transportTy
                instantiationComplete.target }
          simp [inferExprFuel, entered, normalizedExecutable, instantiated,
            result, executableLookupEntered, selfLookup]
      | some placeholder =>
          let selfEvent := TraceEvent.directSelfReference name placeholder path
          let selfSource := ProducerSource.selfReference name placeholder path
          let selfEventExtension :=
            instantiationComplete.transition.after.recordEventExtension selfEvent
          let selfSourceExtension := stateBisimulationRecordSourceExtension
            selfEventExtension.after selfSource
          let referenced := recordSelfReference instantiated.2 name placeholder path
          let finishEvent := TraceEvent.inferredExpr (.var name)
            instantiated.1 path
          let finishExtension := selfSourceExtension.after.recordEventExtension
            finishEvent
          let result := finishExpr (.var name) path instantiated.1 referenced
          let finalRelation :=
            ((instantiatedRelation.recordEvent selfEvent
                (by simp [selfEvent, TraceEvent.allocatedCapVars])).recordSource
              selfSource).recordEvent finishEvent
                (by simp [finishEvent, TraceEvent.allocatedCapVars])
          refine
            { result := result
              success := ?_
              supply_eq := finalRelation.supply_eq
              transition :=
                (((visitExtension.seq instantiationComplete.transition).seq
                    selfEventExtension).seq selfSourceExtension).seq
                  finishExtension
              declarative_bounded := finalRelation.declarative_bounded
              executable_bounded := finalRelation.executable_bounded
              forward_bounded := finalRelation.forward_bounded
              reverse_bounded := finalRelation.reverse_bounded
              ledger_below := finalRelation.ledger_below
              executable_ledger_below := finalRelation.executable_ledger_below
              protected_origins := finalRelation.protected_origins
              protected_below := finalRelation.protected_below
              allocated_recorded := finalRelation.allocated_recorded
              target := finishExtension.transportTy
                (selfSourceExtension.transportTy
                  (selfEventExtension.transportTy
                    instantiationComplete.target)) }
          simp [inferExprFuel, entered, normalizedExecutable, instantiated,
            referenced, recordSelfReference, result, executableLookupEntered,
            selfLookup]

/-- `something` performs exactly one deterministic target allocation. -/
def inferExprFuel_something_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path .something
        initial) { q with nextTy := q.nextTy + 1 } declarative ledger
          (.matcher .any (.var q.nextTy)) := by
  let entered := visit initial .exprSomething path
  have enteredRelation := relation.visit .exprSomething path
  let allocated := entered.freshTy
    (freshOrigin .expression path "something-target")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "something-target")
  let result := finishExpr .something path (.matcher .any (.var q.nextTy))
    allocated.2
  let visitExtension := relation.visitExtension .exprSomething path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "something-target")
  let finishExtension := freshExtension.after.recordEventExtension
    (.inferredExpr .something (.matcher .any (.var q.nextTy)) path)
  let finalRelation := allocatedRelation.state.recordEvent
    (.inferredExpr .something (.matcher .any (.var q.nextTy)) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := allocatedRelation.state.supply_eq
      transition :=
        bisimulationExtensionChain3 visitExtension freshExtension finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := by
        change relation.prevailing.forward.BoundedBy
          { q with nextTy := q.nextTy + 1 }
        exact relation.forward_bounded.mono (SupplyExtends.bumpTy q 1)
      reverse_bounded := by
        change relation.prevailing.reverse.BoundedBy
          { q with nextTy := q.nextTy + 1 }
        exact relation.reverse_bounded.mono (SupplyExtends.bumpTy q 1)
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by
      exact allocatedRelation.target_eq]
  exact finishExtension.after.sameTarget _

/-- Lambda synthesis is structural once the recursive body run has been
constructed from the deterministically allocated domain metavariable. -/
def inferExprFuel_lam_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {body : Expr}
    {bodyTarget : Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (bodyComplete : SynthRunCompletion
      (relation.afterVisitFreshTy .exprLam path
        (freshOrigin .expression path "lambda-domain"))
      (inferExprFuel fuel signature
        ((name, Scheme.mono (.var q.nextTy)) :: context)
        (selfEnv.erase name) (0 :: path) body
        ((visit initial .exprLam path).freshTy
          (freshOrigin .expression path "lambda-domain")).2)
      q' S' ledger' bodyTarget) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.lam name body) initial) q' S' ledger'
        (.fn (.var q.nextTy) bodyTarget) := by
  let entered := visit initial .exprLam path
  have enteredRelation := relation.visit .exprLam path
  let allocated := entered.freshTy
    (freshOrigin .expression path "lambda-domain")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "lambda-domain")
  let bodyResult := bodyComplete.result
  let result := finishExpr (.lam name body) path
    (.fn (.var q.nextTy) bodyResult.target) bodyResult.state
  let visitExtension := relation.visitExtension .exprLam path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "lambda-domain")
  let prefixExtension : BisimulationExtension relation.prevailing ledger S
      ((visit initial .exprLam path).freshTy
        (freshOrigin .expression path "lambda-domain")).2 :=
    { after := (relation.afterVisitFreshTy .exprLam path
          (freshOrigin .expression path "lambda-domain")).prevailing
      transportTy := by
        intro declarativeTarget executableTarget related
        have carried := freshExtension.transportTy
          (visitExtension.transportTy related)
        exact carried }
  let finishExtension := bodyComplete.transition.after.recordEventExtension
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyResult.target) path)
  let finalRelation := bodyComplete.completion.state.recordEvent
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyResult.target) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := bodyComplete.supply_eq
      transition := prefixExtension.seq bodyComplete.transition |>.seq
        finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by exact allocatedRelation.target_eq]
    rw [bodyComplete.success]
  · have domainAtFinal : TyBisimulation
        bodyComplete.transition.after
        (.var q.nextTy) (.var q.nextTy) :=
      bodyComplete.transition.after.sameTarget _
    exact finishExtension.transportTy
      (tyBisimulation_fn domainAtFinal bodyComplete.target)

/-! ## List and tuple constructor slices

These lemmas expose the recursive hypotheses expected by the eventual mutual
induction.  Their fuel parameter is the predecessor passed uniformly to all
children by `inferExprFuel`.
-/

/-- The empty expression list succeeds without inspecting solver state. -/
def inferExprsFuel_nil_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index []
        initial) q declarative ledger [] := by
  refine
    { result := ⟨[], initial⟩
      success := ?_
      supply_eq := relation.supply_eq
      transition := .refl relation.prevailing
      declarative_bounded := relation.declarative_bounded
      executable_bounded := relation.executable_bounded
      forward_bounded := relation.forward_bounded
      reverse_bounded := relation.reverse_bounded
      ledger_below := relation.ledger_below
      executable_ledger_below := relation.executable_ledger_below
      protected_origins := relation.protected_origins
      protected_below := relation.protected_below
      allocated_recorded := relation.allocated_recorded
      targets := .nil }
  simp [inferExprsFuel]

/-- One expression-list cell composes the head and tail completion packages. -/
def inferExprsFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (headComplete : SynthRunCompletion relation
      (inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial) q₁ S₁ ledger₁ target)
    (tailComplete : SynthsRunCompletion headComplete.completion.state
      (inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions headComplete.result.state) q' S' ledger' targets)
    :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) initial) q' S' ledger'
        (target :: targets) := by
  let head := headComplete.result
  let tail := tailComplete.result
  have headSuccess := headComplete.success
  have tailSuccess := tailComplete.success
  refine
    { result := ⟨head.target :: tail.targets, tail.state⟩
      success := ?_
      supply_eq := tailComplete.supply_eq
      transition := headComplete.transition.seq tailComplete.transition
      declarative_bounded := tailComplete.declarative_bounded
      executable_bounded := tailComplete.executable_bounded
      forward_bounded := tailComplete.forward_bounded
      reverse_bounded := tailComplete.reverse_bounded
      ledger_below := tailComplete.ledger_below
      executable_ledger_below := tailComplete.executable_ledger_below
      protected_origins := tailComplete.protected_origins
      protected_below := tailComplete.protected_below
      allocated_recorded := tailComplete.allocated_recorded
      targets := ?_ }
  · simp [inferExprsFuel, headSuccess, tailSuccess, head, tail]
  · exact .cons (tailComplete.transition.transportTy headComplete.target)
      tailComplete.targets

/-- Tuple synthesis is immediate once its list traversal completes. -/
def inferExprFuel_tuple_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expressions : List Expr}
    {targets : List Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (childrenComplete : SynthsRunCompletion
      (relation.afterVisit .exprTuple path)
      (inferExprsFuel fuel signature context selfEnv path 0 expressions
        (visit initial .exprTuple path)) q' S' ledger' targets) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.tuple expressions) initial) q' S' ledger' (.prod targets) := by
  let children := childrenComplete.result
  have childrenSuccess := childrenComplete.success
  let result := finishExpr (.tuple expressions) path (.prod children.targets)
    children.state
  let visitExtension := relation.visitExtension .exprTuple path
  let finishExtension := childrenComplete.transition.after.recordEventExtension
    (.inferredExpr (.tuple expressions) (.prod children.targets) path)
  let finalRelation := childrenComplete.completion.state.recordEvent
    (.inferredExpr (.tuple expressions) (.prod children.targets) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := childrenComplete.supply_eq
      transition := bisimulationExtensionChain3 visitExtension
        childrenComplete.transition finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp [inferExprFuel, childrenSuccess, result, children]
  · exact finishExtension.transportTy
      (tyListBisimulation_prod childrenComplete.targets)

/-! ## Constructor and primitive synthesis -/

/-- Constructor synthesis is complete once the mutual recursion supplies the
argument-list checking run.  This wrapper owns deterministic instantiation,
cross-ledger export freezing, and final expression recording. -/
def inferExprFuel_ctor_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {expressions : List Expr} {scheme : CtorScheme}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (lookup : signature.findDataCtor name = some scheme)
    (checksComplete :
      let entered := visit initial .exprCtor path
      let instantiated := instantiateCtorInState entered scheme
      let instantiationComplete := instantiateCtorInState_complete
        (relation.visit .exprCtor path) scheme
      StateRunCompletion instantiationComplete.correspondence
        (checkExprsFuel fuel signature context selfEnv path 0 expressions
          instantiated.1.1 instantiated.2) q' S' ledger') :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.ctor name expressions) initial) q' S'
      (DDLedger.freezeExport ledger' S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  let entered := visit initial .exprCtor path
  let enteredRelation := relation.visit .exprCtor path
  let instantiated := instantiateCtorInState entered scheme
  let instantiationComplete := instantiateCtorInState_complete
    enteredRelation scheme
  let instantiatedRelation := instantiationComplete.correspondence
  let capImages := freshCapImages q scheme.capBinders
  let target := (InferenceBase.instantiateCtorScheme q scheme).value.2
  let suffix := checksComplete.freezeAndFinishExpr
    (.ctor name expressions) path capImages target
  let visitExtension := relation.visitExtension .exprCtor path
  refine
    { result := suffix.result
      success := ?_
      supply_eq := suffix.supply_eq
      transition :=
        (visitExtension.seq instantiationComplete.transition).seq
          suffix.transition
      declarative_bounded := suffix.declarative_bounded
      executable_bounded := suffix.executable_bounded
      forward_bounded := suffix.forward_bounded
      reverse_bounded := suffix.reverse_bounded
      ledger_below := suffix.ledger_below
      executable_ledger_below := suffix.executable_ledger_below
      protected_origins := suffix.protected_origins
      protected_below := suffix.protected_below
      allocated_recorded := suffix.allocated_recorded
      target := suffix.target }
  simp only [inferExprFuel]
  rw (occs := .pos [1]) [lookup]
  simp only
  rw (occs := .pos [1]) [checksComplete.success]
  simp [suffix, StateRunCompletion.freezeAndFinishExpr,
    enteredRelation.supply_eq, capImages, target]

/-- Primitive synthesis has the identical traversal suffix and differs only
in signature lookup and the node/expression tags. -/
def inferExprFuel_prim_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {op : PrimOp}
    {expressions : List Expr} {scheme : CtorScheme}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (lookup : signature.findPrimitive op = some scheme)
    (checksComplete :
      let entered := visit initial .exprPrim path
      let instantiated := instantiateCtorInState entered scheme
      let instantiationComplete := instantiateCtorInState_complete
        (relation.visit .exprPrim path) scheme
      StateRunCompletion instantiationComplete.correspondence
        (checkExprsFuel fuel signature context selfEnv path 0 expressions
          instantiated.1.1 instantiated.2) q' S' ledger') :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.prim op expressions) initial) q' S'
      (DDLedger.freezeExport ledger' S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  let entered := visit initial .exprPrim path
  let enteredRelation := relation.visit .exprPrim path
  let instantiated := instantiateCtorInState entered scheme
  let instantiationComplete := instantiateCtorInState_complete
    enteredRelation scheme
  let instantiatedRelation := instantiationComplete.correspondence
  let capImages := freshCapImages q scheme.capBinders
  let target := (InferenceBase.instantiateCtorScheme q scheme).value.2
  let suffix := checksComplete.freezeAndFinishExpr
    (.prim op expressions) path capImages target
  let visitExtension := relation.visitExtension .exprPrim path
  refine
    { result := suffix.result
      success := ?_
      supply_eq := suffix.supply_eq
      transition :=
        (visitExtension.seq instantiationComplete.transition).seq
          suffix.transition
      declarative_bounded := suffix.declarative_bounded
      executable_bounded := suffix.executable_bounded
      forward_bounded := suffix.forward_bounded
      reverse_bounded := suffix.reverse_bounded
      ledger_below := suffix.ledger_below
      executable_ledger_below := suffix.executable_ledger_below
      protected_origins := suffix.protected_origins
      protected_below := suffix.protected_below
      allocated_recorded := suffix.allocated_recorded
      target := suffix.target }
  simp only [inferExprFuel]
  rw (occs := .pos [1]) [lookup]
  simp only
  rw (occs := .pos [1]) [checksComplete.success]
  simp [suffix, StateRunCompletion.freezeAndFinishExpr,
    enteredRelation.supply_eq, capImages, target]

end DemandTypingInferenceCompletenessTraversal
end TypePM
