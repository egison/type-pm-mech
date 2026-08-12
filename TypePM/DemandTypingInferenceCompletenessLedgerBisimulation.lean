import TypePM.DemandTyping

/-!
# Origin-ledger correspondence up to residual renaming

Inference completeness cannot require the declarative and executable origin
ledgers to contain literally the same frozen variable identifiers.  Opposite
orientations of one exact MGU can expose different representatives of the
same capability-variable class at an export boundary.

This module defines the policy-preserving maps needed instead.  It is kept
independent of traversal state so the three algebraic obligations can be
checked before changing the main induction invariant:

* identity ledgers correspond;
* admissible substitutions transport through a pair of ledger maps; and
* selectively freezing corresponding structural leaves preserves the maps.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessLedgerBisimulation

/-- A capability post maps the policy of `source` into the policy of
`destination`.  Rigid variables retain both their identifier and rigidity;
rename-only variables map to a destination variable that is not structural;
structural variables impose no restriction. -/
def AdmissibleCapPostBetween
    (source destination : CapabilityOriginLedger) (post : CapSubst) : Prop :=
  ∀ varId,
    match source.originOf varId with
    | .rigid =>
        post varId = .var varId ∧ destination.originOf varId = .rigid
    | .renameOnly =>
        ∃ image,
          post varId = .var image ∧
            destination.originOf image ≠ .structuralFlexible
    | .structuralFlexible => True

/-- Paired-substitution form.  Target metavariables carry no origin policy. -/
structure AdmissiblePostBetween
    (source destination : CapabilityOriginLedger) (post : Subst) : Prop where
  cap : AdmissibleCapPostBetween source destination post.cap

namespace AdmissibleCapPostBetween

/-- Ordinary admissibility is the equal-ledger special case. -/
theorem ofAdmissible
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (admissible : AdmissibleCapPost ledger post) :
    AdmissibleCapPostBetween ledger ledger post := by
  intro varId
  cases origin : ledger.originOf varId with
  | rigid =>
      simpa [AdmissibleCapPostBetween, origin] using
        admissible.rigid origin
  | renameOnly =>
      simpa [AdmissibleCapPostBetween, origin] using
        admissible.renameOnly origin
  | structuralFlexible => trivial

/-- Forgetting an equal-ledger transport recovers ordinary admissibility. -/
theorem toAdmissible
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (between : AdmissibleCapPostBetween ledger ledger post) :
    AdmissibleCapPost ledger post := by
  intro varId
  cases origin : ledger.originOf varId with
  | rigid =>
      simpa [AdmissibleCapPostBetween, origin] using between varId
  | renameOnly =>
      simpa [AdmissibleCapPostBetween, origin] using between varId
  | structuralFlexible => trivial

/-- Policy-preserving maps compose in the same order as capability posts. -/
theorem comp
    {first middle last : CapabilityOriginLedger}
    {later earlier : CapSubst}
    (laterBetween : AdmissibleCapPostBetween middle last later)
    (earlierBetween : AdmissibleCapPostBetween first middle earlier) :
    AdmissibleCapPostBetween first last
      (CapSubst.comp later earlier) := by
  intro varId
  cases firstOrigin : first.originOf varId with
  | rigid =>
      have earlierAt := earlierBetween varId
      simp only [firstOrigin] at earlierAt
      rcases earlierAt with ⟨earlierFixed, middleRigid⟩
      have laterAt := laterBetween varId
      simp only [middleRigid] at laterAt
      exact ⟨by simp [CapSubst.comp, earlierFixed, laterAt.1, Cap.apply],
        laterAt.2⟩
  | renameOnly =>
      have earlierAt := earlierBetween varId
      simp only [firstOrigin] at earlierAt
      rcases earlierAt with
        ⟨middleVar, earlierEquation, middleSafe⟩
      cases middleOrigin : middle.originOf middleVar with
      | rigid =>
          have laterAt := laterBetween middleVar
          simp only [middleOrigin] at laterAt
          exact ⟨middleVar,
            by simp [CapSubst.comp, earlierEquation, laterAt.1, Cap.apply],
            by simp [laterAt.2]⟩
      | renameOnly =>
          have laterAt := laterBetween middleVar
          simp only [middleOrigin] at laterAt
          rcases laterAt with
            ⟨lastVar, laterEquation, lastSafe⟩
          exact ⟨lastVar,
            by simp [CapSubst.comp, earlierEquation, laterEquation, Cap.apply],
            lastSafe⟩
      | structuralFlexible => exact False.elim (middleSafe middleOrigin)
  | structuralFlexible => trivial

/-- Identity transports every ledger to itself. -/
theorem id (ledger : CapabilityOriginLedger) :
    AdmissibleCapPostBetween ledger ledger CapSubst.id :=
  ofAdmissible (AdmissibleCapPost.id ledger)

/-! ## Selective freezing -/

/-- Freezing corresponding structural leaves preserves one directional
ledger map.  The selected-leaf premise is the exact boundary obligation:
every source representative being frozen maps to a destination representative
that is frozen at the same cut. -/
theorem freezeSelected
    {source destination : CapabilityOriginLedger} {post : CapSubst}
    {sourceLeaves destinationLeaves : List CapVar}
    (between : AdmissibleCapPostBetween source destination post)
    (destinationStructural : ∀ varId, varId ∈ destinationLeaves →
      destination.originOf varId = .structuralFlexible)
    (selectedTransport : ∀ varId, varId ∈ sourceLeaves →
      ∃ image, post varId = .var image ∧ image ∈ destinationLeaves) :
    AdmissibleCapPostBetween
      (source.setOrigins sourceLeaves .renameOnly)
      (destination.setOrigins destinationLeaves .renameOnly) post := by
  intro varId
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases selected : varId ∈ sourceLeaves
  · rw [if_pos selected]
    rcases selectedTransport varId selected with
      ⟨image, imageEquation, imageSelected⟩
    refine ⟨image, imageEquation, ?_⟩
    rw [CapabilityOriginLedger.originOf_setOrigins_of_mem _ _ _ _
      imageSelected]
    simp
  · rw [if_neg selected]
    cases sourceOrigin : source.originOf varId with
    | rigid =>
        have atVar := between varId
        simp only [sourceOrigin] at atVar
        rcases atVar with ⟨fixed, destinationRigid⟩
        have destinationNotSelected : varId ∉ destinationLeaves := by
          intro membership
          rw [destinationStructural varId membership] at destinationRigid
          contradiction
        refine ⟨fixed, ?_⟩
        rw [CapabilityOriginLedger.originOf_setOrigins_eq,
          if_neg destinationNotSelected]
        exact destinationRigid
    | renameOnly =>
        have atVar := between varId
        simp only [sourceOrigin] at atVar
        rcases atVar with ⟨image, imageEquation, imageSafe⟩
        refine ⟨image, imageEquation, ?_⟩
        rw [CapabilityOriginLedger.originOf_setOrigins_eq]
        by_cases imageSelected : image ∈ destinationLeaves
        · simp [imageSelected]
        · simpa [imageSelected] using imageSafe
    | structuralFlexible => trivial

end AdmissibleCapPostBetween

namespace AdmissiblePostBetween

theorem ofAdmissible
    {ledger : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePost ledger post) :
    AdmissiblePostBetween ledger ledger post :=
  ⟨AdmissibleCapPostBetween.ofAdmissible admissible.cap⟩

theorem toAdmissible
    {ledger : CapabilityOriginLedger} {post : Subst}
    (between : AdmissiblePostBetween ledger ledger post) :
    AdmissiblePost ledger post :=
  ⟨AdmissibleCapPostBetween.toAdmissible between.cap⟩

theorem seq
    {first middle last : CapabilityOriginLedger}
    {later earlier : Subst}
    (laterBetween : AdmissiblePostBetween middle last later)
    (earlierBetween : AdmissiblePostBetween first middle earlier) :
    AdmissiblePostBetween first last (Subst.seq later earlier) := by
  constructor
  change AdmissibleCapPostBetween first last
    (CapSubst.comp later.cap earlier.cap)
  exact AdmissibleCapPostBetween.comp laterBetween.cap earlierBetween.cap

theorem id (ledger : CapabilityOriginLedger) :
    AdmissiblePostBetween ledger ledger Subst.id :=
  ofAdmissible (AdmissiblePost.id ledger)

end AdmissiblePostBetween

/-- Mutual policy transport along the same residuals that relate the two
prevailing substitutions.  `forward` maps executable policy into DD policy;
`reverse` maps DD policy back into executable policy. -/
structure LedgerBisimulation
    (declarative executable : CapabilityOriginLedger)
    (forward reverse : Subst) : Prop where
  forwardBetween : AdmissiblePostBetween executable declarative forward
  reverseBetween : AdmissiblePostBetween declarative executable reverse

namespace LedgerBisimulation

theorem refl (ledger : CapabilityOriginLedger) :
    LedgerBisimulation ledger ledger Subst.id Subst.id :=
  ⟨AdmissiblePostBetween.id ledger, AdmissiblePostBetween.id ledger⟩

/-- Entering the DD representative space through `forward` turns every
DD-admissible delta into a policy-preserving executable-to-DD post. -/
theorem enterAdmissible
    {declarative executable : CapabilityOriginLedger}
    {forward reverse delta : Subst}
    (ledgers : LedgerBisimulation declarative executable forward reverse)
    (deltaAdmissible : AdmissiblePost declarative delta) :
    AdmissiblePostBetween executable declarative
      (Subst.seq delta forward) :=
  (AdmissiblePostBetween.ofAdmissible deltaAdmissible).seq
    ledgers.forwardBetween

/-- A DD-admissible solve transports to an executable-admissible competitor
by entering through `forward` and returning through `reverse`.  The return
map is necessary when the ledgers freeze different representatives. -/
theorem transportAdmissible
    {declarative executable : CapabilityOriginLedger}
    {forward reverse delta : Subst}
    (ledgers : LedgerBisimulation declarative executable forward reverse)
    (deltaAdmissible : AdmissiblePost declarative delta) :
    AdmissiblePost executable
      (Subst.seq reverse (Subst.seq delta forward)) := by
  have entered := ledgers.enterAdmissible deltaAdmissible
  exact (ledgers.reverseBetween.seq entered).toAdmissible

/-- Selective export freezing preserves mutual ledger transport once the
two residuals map the selected representatives in both directions. -/
theorem freezeExport
    {declarative executable : CapabilityOriginLedger}
    {forward reverse declarativeSubst executableSubst : Subst}
    {capImages : List CapVar} {exportedPayload : Ty}
    (ledgers : LedgerBisimulation declarative executable forward reverse)
    (forwardLeaves : ∀ varId,
      varId ∈ DDLedger.exportLeaves executable executableSubst capImages
        exportedPayload →
      ∃ image, forward.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves declarative declarativeSubst capImages
          exportedPayload)
    (reverseLeaves : ∀ varId,
      varId ∈ DDLedger.exportLeaves declarative declarativeSubst capImages
        exportedPayload →
      ∃ image, reverse.cap varId = .var image ∧
        image ∈ DDLedger.exportLeaves executable executableSubst capImages
          exportedPayload) :
    LedgerBisimulation
      (DDLedger.freezeExport declarative declarativeSubst capImages
        exportedPayload)
      (DDLedger.freezeExport executable executableSubst capImages
        exportedPayload)
      forward reverse := by
  constructor
  · unfold DDLedger.freezeExport
    constructor
    exact ledgers.forwardBetween.cap.freezeSelected
        (fun varId membership =>
          DDLedger.exportLeaves_origin declarative declarativeSubst capImages
            exportedPayload varId membership)
        forwardLeaves
  · unfold DDLedger.freezeExport
    constructor
    exact ledgers.reverseBetween.cap.freezeSelected
        (fun varId membership =>
          DDLedger.exportLeaves_origin executable executableSubst capImages
            exportedPayload varId membership)
        reverseLeaves

end LedgerBisimulation
end DemandTypingInferenceCompletenessLedgerBisimulation
end TypePM
