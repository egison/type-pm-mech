import TypePM.DemandTyping

/-!
# Supply-scoped metatheory for demand-typing origin ledgers

The demand-directed rules allocate capability variables monotonically from a
fresh supply.  This module records the two elementary invariants needed to
reason about their origin ledger independently of an executable inference
trace:

* every explicit ledger key lies below the current capability supply; and
* a transition preserves the policy of every variable below the incoming
  supply, except that a structurally flexible variable may be frozen to
  rename-only.

Fresh allocation is therefore allowed only at or above the incoming supply.
The transition lemmas below are proved for each concrete `DDLedger` operation;
there is no blanket transition assumption.
-/

namespace TypePM
namespace DDLedger

/-- Every explicitly recorded capability variable precedes the current fresh
capability counter. -/
def LedgerBelow (q : InferenceBase.FreshSupply)
    (ledger : CapabilityOriginLedger) : Prop :=
  ∀ varId, varId ∈ ledger.map Prod.fst → varId.id < q.nextCap

/-- Pointwise policy refinement.  Rigid and rename-only variables retain
their policies; structural flexibility may either remain local or be frozen
to rename-only. -/
inductive OriginRefines : CapabilityOrigin → CapabilityOrigin → Prop where
  | rigid : OriginRefines .rigid .rigid
  | renameOnly : OriginRefines .renameOnly .renameOnly
  | structural : OriginRefines .structuralFlexible .structuralFlexible
  | freeze : OriginRefines .structuralFlexible .renameOnly

/-- Policy refinement restricted to variables that existed below the
incoming supply.  Variables at and above this cut may be freshly allocated. -/
def RefinesBelow (q : InferenceBase.FreshSupply)
    (earlier later : CapabilityOriginLedger) : Prop :=
  ∀ varId, varId.id < q.nextCap →
    OriginRefines (earlier.originOf varId) (later.originOf varId)

namespace OriginRefines

theorem refl (origin : CapabilityOrigin) : OriginRefines origin origin := by
  cases origin <;> constructor

theorem trans {first middle last : CapabilityOrigin}
    (front : OriginRefines first middle)
    (back : OriginRefines middle last) : OriginRefines first last := by
  cases front <;> cases back <;> constructor

end OriginRefines

theorem RefinesBelow.refl (q : InferenceBase.FreshSupply)
    (ledger : CapabilityOriginLedger) : RefinesBelow q ledger ledger := by
  intro varId _
  exact OriginRefines.refl _

theorem RefinesBelow.trans {q : InferenceBase.FreshSupply}
    {first middle last : CapabilityOriginLedger}
    (front : RefinesBelow q first middle)
    (back : RefinesBelow q middle last) :
    RefinesBelow q first last := by
  intro varId below
  exact (front varId below).trans (back varId below)

theorem LedgerBelow.empty (q : InferenceBase.FreshSupply) :
    LedgerBelow q [] := by
  intro varId membership
  simp at membership

private theorem mem_keys_setOrigins
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (origin : CapabilityOrigin) (varId : CapVar) :
    varId ∈ (ledger.setOrigins varIds origin).map Prod.fst ↔
      varId ∈ varIds ∨ varId ∈ ledger.map Prod.fst := by
  induction varIds generalizing ledger with
  | nil => simp [CapabilityOriginLedger.setOrigins]
  | cons head rest ih =>
      simp only [CapabilityOriginLedger.setOrigins,
        CapabilityOriginLedger.setOrigin, List.map_cons, List.mem_cons]
      rw [ih]
      simp [or_assoc]

private theorem LedgerBelow.setOrigins
    {q q' : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger} {varIds : List CapVar}
    {origin : CapabilityOrigin}
    (oldBelow : LedgerBelow q ledger)
    (supplyMonotone : q.nextCap ≤ q'.nextCap)
    (newBelow : ∀ varId, varId ∈ varIds → varId.id < q'.nextCap) :
    LedgerBelow q' (ledger.setOrigins varIds origin) := by
  intro varId membership
  rw [mem_keys_setOrigins] at membership
  rcases membership with fresh | old
  · exact newBelow varId fresh
  · exact Nat.lt_of_lt_of_le (oldBelow varId old) supplyMonotone

private theorem originOf_eq_structural_mem_keys
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

private theorem refinesBelow_setFreshOrigins
    {q : InferenceBase.FreshSupply}
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (origin : CapabilityOrigin)
    (fresh : ∀ varId, varId ∈ varIds → q.nextCap ≤ varId.id) :
    RefinesBelow q ledger (ledger.setOrigins varIds origin) := by
  intro varId below
  have outside : varId ∉ varIds := by
    intro membership
    exact Nat.not_le_of_lt below (fresh varId membership)
  rw [CapabilityOriginLedger.originOf_setOrigins_eq, if_neg outside]
  exact OriginRefines.refl _

private theorem refinesBelow_freezeStructural
    {q : InferenceBase.FreshSupply}
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (structural : ∀ varId, varId ∈ varIds →
      ledger.originOf varId = .structuralFlexible) :
    RefinesBelow q ledger (ledger.setOrigins varIds .renameOnly) := by
  intro varId _
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases membership : varId ∈ varIds
  · rw [if_pos membership, structural varId membership]
    exact .freeze
  · rw [if_neg membership]
    exact OriginRefines.refl _

private theorem freshCapImages_ge
    (q : InferenceBase.FreshSupply) (binders : List CapVar)
    (varId : CapVar)
    (membership : varId ∈ Inference.freshCapImages q binders) :
    q.nextCap ≤ varId.id := by
  simp only [Inference.freshCapImages] at membership
  rcases List.mem_map.mp membership with ⟨binder, _, rfl⟩
  exact Nat.le_add_right q.nextCap binder.id

private theorem freshCapImages_lt
    (q : InferenceBase.FreshSupply) (binders : List CapVar)
    (varId : CapVar)
    (membership : varId ∈ Inference.freshCapImages q binders) :
    varId.id <
      (InferenceBase.instantiateBinders q binders []).supply.nextCap := by
  simp only [Inference.freshCapImages] at membership
  rcases List.mem_map.mp membership with ⟨binder, binderMem, rfl⟩
  simp only [InferenceBase.instantiateBinders]
  exact Nat.add_lt_add_left
    (InferenceBase.mem_lt_binderSpan
      (List.mem_map.mpr ⟨binder, binderMem, rfl⟩)) q.nextCap

private theorem instantiateBinders_cap_monotone
    (q : InferenceBase.FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    q.nextCap ≤
      (InferenceBase.instantiateBinders q capBinders tyBinders).supply.nextCap := by
  simp [InferenceBase.instantiateBinders]

/-! ## Single fresh capability -/

theorem LedgerBelow.markFreshCap
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (below : LedgerBelow q ledger) :
    LedgerBelow { q with nextCap := q.nextCap + 1 }
      (markFreshCap ledger q) := by
  apply LedgerBelow.setOrigins (q' := { q with nextCap := q.nextCap + 1 })
      (varIds := [⟨q.nextCap⟩]) below
  · simp
  · intro varId membership
    simp only [List.mem_singleton] at membership
    subst varId
    simp

theorem RefinesBelow.markFreshCap
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger) :
    RefinesBelow q ledger (markFreshCap ledger q) := by
  apply refinesBelow_setFreshOrigins ledger [⟨q.nextCap⟩]
      .structuralFlexible
  intro varId membership
  simp only [List.mem_singleton] at membership
  subst varId
  exact Nat.le_refl _

/-! ## Contiguous fresh capability ranges -/

theorem LedgerBelow.markCapRange
    {initial final : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger}
    (below : LedgerBelow initial ledger)
    (monotone : initial.nextCap ≤ final.nextCap) :
    LedgerBelow final (markCapRange ledger initial final) := by
  let varIds :=
    ((List.range (final.nextCap - initial.nextCap)).map fun offset =>
      (⟨initial.nextCap + offset⟩ : CapVar)).reverse
  change LedgerBelow final
    (ledger.setOrigins varIds .structuralFlexible)
  apply LedgerBelow.setOrigins below monotone
  intro varId membership
  simp only [varIds, List.mem_reverse, List.mem_map] at membership
  rcases membership with ⟨offset, offsetMem, rfl⟩
  have offsetBelow : offset < final.nextCap - initial.nextCap := by
    simpa using offsetMem
  change initial.nextCap + offset < final.nextCap
  omega

theorem RefinesBelow.markCapRange
    (initial final : InferenceBase.FreshSupply)
    (ledger : CapabilityOriginLedger) :
    RefinesBelow initial ledger (markCapRange ledger initial final) := by
  let varIds :=
    ((List.range (final.nextCap - initial.nextCap)).map fun offset =>
      (⟨initial.nextCap + offset⟩ : CapVar)).reverse
  change RefinesBelow initial ledger
    (ledger.setOrigins varIds .structuralFlexible)
  apply refinesBelow_setFreshOrigins
  intro varId membership
  simp only [varIds, List.mem_reverse, List.mem_map] at membership
  rcases membership with ⟨offset, _, rfl⟩
  exact Nat.le_add_right _ _

/-! ## Expression-scheme instance batches -/

theorem LedgerBelow.markSchemeInstance
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (scheme : Scheme) (below : LedgerBelow q ledger) :
    LedgerBelow (InferenceBase.instantiateScheme q scheme).supply
      (markSchemeInstance ledger q scheme) := by
  apply LedgerBelow.setOrigins below
  · exact (Scheme.freshInstantiate_supplyExtends q scheme).1
  · intro varId membership
    exact (Scheme.mem_canonicalCapImages_bounds membership).2

theorem RefinesBelow.markSchemeInstance
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (scheme : Scheme) :
    RefinesBelow q ledger (markSchemeInstance ledger q scheme) := by
  exact refinesBelow_setFreshOrigins ledger
    (Scheme.canonicalCapImages q scheme) .renameOnly
    (fun _ membership =>
      (Scheme.mem_canonicalCapImages_bounds membership).1)

theorem LedgerBelow.markDualInstance
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (scheme : DualScheme) (below : LedgerBelow q ledger) :
    LedgerBelow (InferenceBase.instantiateDualScheme q scheme).supply
      (markDualInstance ledger q scheme) := by
  apply LedgerBelow.setOrigins below
  · exact instantiateBinders_cap_monotone q scheme.capBinders scheme.tyBinders
  · intro varId membership
    simpa [InferenceBase.instantiateDualScheme] using
      freshCapImages_lt q scheme.capBinders varId membership

theorem RefinesBelow.markDualInstance
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (scheme : DualScheme) :
    RefinesBelow q ledger (markDualInstance ledger q scheme) := by
  exact refinesBelow_setFreshOrigins ledger
    (Inference.freshCapImages q scheme.capBinders) .renameOnly
    (freshCapImages_ge q scheme.capBinders)

theorem LedgerBelow.markCtorInstance
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (scheme : CtorScheme) (below : LedgerBelow q ledger) :
    LedgerBelow (InferenceBase.instantiateCtorScheme q scheme).supply
      (markCtorInstance ledger q scheme) := by
  apply LedgerBelow.setOrigins below
  · exact instantiateBinders_cap_monotone q scheme.capBinders scheme.tyBinders
  · intro varId membership
    simpa [InferenceBase.instantiateCtorScheme] using
      freshCapImages_lt q scheme.capBinders varId membership

theorem RefinesBelow.markCtorInstance
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (scheme : CtorScheme) :
    RefinesBelow q ledger (markCtorInstance ledger q scheme) := by
  exact refinesBelow_setFreshOrigins ledger
    (Inference.freshCapImages q scheme.capBinders) .structuralFlexible
    (freshCapImages_ge q scheme.capBinders)

/-! ## Selective export freezing -/

theorem LedgerBelow.freezeExport
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (S : Subst) (capImages : List CapVar) (exportedPayload : Ty)
    (below : LedgerBelow q ledger) :
    LedgerBelow q (freezeExport ledger S capImages exportedPayload) := by
  apply LedgerBelow.setOrigins below (Nat.le_refl _)
  intro varId membership
  exact below varId (originOf_eq_structural_mem_keys
    (exportLeaves_origin ledger S capImages exportedPayload varId membership))

theorem RefinesBelow.freezeExport
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (S : Subst) (capImages : List CapVar) (exportedPayload : Ty) :
    RefinesBelow q ledger
      (freezeExport ledger S capImages exportedPayload) := by
  exact refinesBelow_freezeStructural ledger
    (exportLeaves ledger S capImages exportedPayload)
    (exportLeaves_origin ledger S capImages exportedPayload)

theorem LedgerBelow.freezeMatcherProducer
    {q : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger} (capability : Cap)
    (below : LedgerBelow q ledger) :
    LedgerBelow q (freezeMatcherProducer ledger capability) := by
  apply LedgerBelow.setOrigins below (Nat.le_refl _)
  intro varId membership
  exact below varId
    (matcherProducerLeaves_recorded ledger capability varId membership).2

theorem RefinesBelow.freezeMatcherProducer
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (capability : Cap) :
    RefinesBelow q ledger (freezeMatcherProducer ledger capability) := by
  exact refinesBelow_freezeStructural ledger
    (matcherProducerLeaves ledger capability)
    (matcherProducerLeaves_origin ledger capability)

theorem LedgerBelow.freezeMatcherProducerExcept
    {q : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger} (capability : Cap)
    (borrowed : List CapVar) (below : LedgerBelow q ledger) :
    LedgerBelow q (freezeMatcherProducerExcept ledger capability borrowed) := by
  apply LedgerBelow.setOrigins below (Nat.le_refl _)
  intro varId membership
  exact below varId
    (matcherProducerLeavesExcept_recorded ledger capability borrowed varId
      membership).2

theorem RefinesBelow.freezeMatcherProducerExcept
    (q : InferenceBase.FreshSupply) (ledger : CapabilityOriginLedger)
    (capability : Cap) (borrowed : List CapVar) :
    RefinesBelow q ledger
      (freezeMatcherProducerExcept ledger capability borrowed) := by
  exact refinesBelow_freezeStructural ledger
    (matcherProducerLeavesExcept ledger capability borrowed)
    (matcherProducerLeavesExcept_origin ledger capability borrowed)

end DDLedger
end TypePM
