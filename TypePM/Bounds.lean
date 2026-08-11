import TypePM.InferenceBase

/-!
# Fresh-supply bounds

This module contains the representation-independent freshness invariant shared
by executable inference, demand typing, and canonical scheme opening.  It is
kept below `DemandTyping`: boundedness describes ordinary types and
substitutions only and does not depend on a typing derivation.
-/

namespace TypePM

/-- Componentwise order on fresh supplies. -/
def SupplyExtends (earlier later : InferenceBase.FreshSupply) : Prop :=
  earlier.nextCap ≤ later.nextCap ∧ earlier.nextTy ≤ later.nextTy

theorem SupplyExtends.refl (q : InferenceBase.FreshSupply) :
    SupplyExtends q q :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem SupplyExtends.trans {q₁ q₂ q₃ : InferenceBase.FreshSupply}
    (first : SupplyExtends q₁ q₂) (second : SupplyExtends q₂ q₃) :
    SupplyExtends q₁ q₃ :=
  ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩

theorem SupplyExtends.bumpTy (q : InferenceBase.FreshSupply) (count : Nat) :
    SupplyExtends q { q with nextTy := q.nextTy + count } :=
  ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

/-- Canonical scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateScheme
    (q : InferenceBase.FreshSupply) (scheme : Scheme) :
    SupplyExtends q (InferenceBase.instantiateScheme q scheme).supply := by
  constructor
  · rw [InferenceBase.instantiateScheme, Scheme.freshInstantiate_nextCap]
    exact Nat.le_add_right _ _
  · rw [InferenceBase.instantiateScheme, Scheme.freshInstantiate_nextTy]
    exact Nat.le_add_right _ _

/-- Constructor-scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateCtorScheme
    (q : InferenceBase.FreshSupply) (scheme : CtorScheme) :
    SupplyExtends q (InferenceBase.instantiateCtorScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Dual-scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateDualScheme
    (q : InferenceBase.FreshSupply) (scheme : DualScheme) :
    SupplyExtends q (InferenceBase.instantiateDualScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem SupplyExtends.bumpCap (q : InferenceBase.FreshSupply) (count : Nat) :
    SupplyExtends q { q with nextCap := q.nextCap + count } :=
  ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem SupplyExtends.bumpBoth (q : InferenceBase.FreshSupply)
    (capCount tyCount : Nat) :
    SupplyExtends q
      { q with nextCap := q.nextCap + capCount
               nextTy := q.nextTy + tyCount } :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- All capability variables lie below the supply's capability counter. -/
def Cap.BoundedBy (q : InferenceBase.FreshSupply) (capability : Cap) : Prop :=
  ∀ varId ∈ capability.fcv, varId.id < q.nextCap

/-- All variables of both sorts lie below the supply's counters. -/
structure Ty.BoundedBy (q : InferenceBase.FreshSupply) (target : Ty) :
    Prop where
  caps : ∀ varId ∈ target.fcv, varId.id < q.nextCap
  targets : ∀ varId ∈ target.ftv, varId < q.nextTy

/-- A bounded substitution is the identity at and above both counters and has
bounded images below them. -/
structure Subst.BoundedBy (q : InferenceBase.FreshSupply) (S : Subst) :
    Prop where
  capFixedAbove : ∀ varId : CapVar, q.nextCap ≤ varId.id →
    S.cap varId = .var varId
  capImagesBounded : ∀ varId : CapVar, varId.id < q.nextCap →
    Cap.BoundedBy q (S.cap varId)
  targetFixedAbove : ∀ varId : TypePM.TyVar, q.nextTy ≤ varId →
    S.target varId = .var varId
  targetImagesBounded : ∀ varId : TypePM.TyVar, varId < q.nextTy →
    Ty.BoundedBy q (S.target varId)

/-- A substitution bounded at a cut cannot anticipate its next capability
metavariable. -/
theorem Subst.BoundedBy.freshCapFixed
    {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) :
    S.cap ⟨q.nextCap⟩ = .var ⟨q.nextCap⟩ :=
  bounded.capFixedAbove ⟨q.nextCap⟩ (Nat.le_refl _)

/-- Ordinary-variable counterpart of `freshCapFixed`. -/
theorem Subst.BoundedBy.freshTargetFixed
    {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) :
    S.target q.nextTy = .var q.nextTy :=
  bounded.targetFixedAbove q.nextTy (Nat.le_refl _)

/-- Capability boundedness is monotone along supply extension. -/
theorem Cap.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {capability : Cap} (extends_ : SupplyExtends q q')
    (bounded : capability.BoundedBy q) : capability.BoundedBy q' :=
  fun varId mem => Nat.lt_of_lt_of_le (bounded varId mem) extends_.1

/-- Type boundedness is monotone along supply extension. -/
theorem Ty.BoundedBy.mono {q q' : InferenceBase.FreshSupply} {target : Ty}
    (extends_ : SupplyExtends q q') (bounded : target.BoundedBy q) :
    target.BoundedBy q' :=
  ⟨fun varId mem => Nat.lt_of_lt_of_le (bounded.caps varId mem) extends_.1,
    fun varId mem =>
      Nat.lt_of_lt_of_le (bounded.targets varId mem) extends_.2⟩

/-- Substitution boundedness is monotone along supply extension. -/
theorem Subst.BoundedBy.mono {q q' : InferenceBase.FreshSupply} {S : Subst}
    (extends_ : SupplyExtends q q') (bounded : S.BoundedBy q) :
    S.BoundedBy q' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    exact bounded.capFixedAbove varId (Nat.le_trans extends_.1 above)
  · intro varId below
    by_cases original : varId.id < q.nextCap
    · exact (bounded.capImagesBounded varId original).mono extends_
    · rw [bounded.capFixedAbove varId (Nat.le_of_not_lt original)]
      intro image mem
      have : image = varId := by
        simpa [Cap.fcv] using mem
      simpa [this]
  · intro varId above
    exact bounded.targetFixedAbove varId (Nat.le_trans extends_.2 above)
  · intro varId below
    by_cases original : varId < q.nextTy
    · exact (bounded.targetImagesBounded varId original).mono extends_
    · rw [bounded.targetFixedAbove varId (Nat.le_of_not_lt original)]
      constructor
      · intro image mem
        have empty : (Ty.var varId).fcv = ([] : List CapVar) := rfl
        rw [empty] at mem
        nomatch mem
      · intro image mem
        have : image = varId := by
          simpa [Ty.ftv] using mem
        simpa [this]

/-- The identity substitution is bounded by every supply. -/
theorem Subst.boundedBy_id (q : InferenceBase.FreshSupply) :
    Subst.BoundedBy q Subst.id := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, ?_⟩
  · intro varId below image mem
    have : image = varId := by
      simpa [Subst.id, CapSubst.id, Cap.fcv] using mem
    simpa [this]
  · intro varId below
    constructor
    · intro image mem
      have empty : (Subst.id.target varId).fcv = [] := rfl
      rw [empty] at mem
      nomatch mem
    · intro image mem
      have : image = varId := by
        simpa [Subst.id, TySubst.id, Ty.ftv] using mem
      simpa [this]

/-- Applying a bounded substitution to a bounded capability is bounded. -/
theorem Subst.BoundedBy.applyCap {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) {capability : Cap}
    (capBounded : capability.BoundedBy q) :
    (capability.apply S.cap).BoundedBy q := by
  intro varId mem
  rw [Unification.Cap.fcv_apply] at mem
  simp only [List.mem_flatMap] at mem
  obtain ⟨original, originalMem, imageMem⟩ := mem
  exact bounded.capImagesBounded original (capBounded original originalMem)
    varId imageMem

/-- Applying a bounded substitution to a bounded type is bounded. -/
theorem Subst.BoundedBy.apply {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) {target : Ty}
    (targetBounded : target.BoundedBy q) :
    (S.apply target).BoundedBy q := by
  constructor
  · intro varId mem
    rcases Unification.Ty.mem_fcv_applyTarget _ S.target varId mem with
      own | image
    · rw [Unification.Ty.fcv_applyCapability] at own
      simp only [List.mem_flatMap] at own
      obtain ⟨original, originalMem, imageMem⟩ := own
      exact bounded.capImagesBounded original
        (targetBounded.caps original originalMem) varId imageMem
    · obtain ⟨tyVar, tyMem, imageMem⟩ := image
      rw [Unification.Ty.ftv_applyCapability] at tyMem
      exact (bounded.targetImagesBounded tyVar
        (targetBounded.targets tyVar tyMem)).caps varId imageMem
  · intro varId mem
    have mem' : varId ∈
        ((target.applyCapability S.cap).applyTarget S.target).ftv := mem
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability] at mem'
    simp only [List.mem_flatMap] at mem'
    obtain ⟨original, originalMem, imageMem⟩ := mem'
    exact (bounded.targetImagesBounded original
      (targetBounded.targets original originalMem)).targets varId imageMem

/-- Capability-only application of a bounded substitution preserves type
boundedness. -/
theorem Subst.BoundedBy.applyCapabilityTy {q : InferenceBase.FreshSupply}
    {S : Subst} (bounded : S.BoundedBy q) {target : Ty}
    (targetBounded : target.BoundedBy q) :
    (target.applyCapability S.cap).BoundedBy q := by
  constructor
  · intro w hw
    rw [Unification.Ty.fcv_applyCapability] at hw
    simp only [List.mem_flatMap] at hw
    obtain ⟨original, originalMem, imageMem⟩ := hw
    exact bounded.capImagesBounded original
      (targetBounded.caps original originalMem) w imageMem
  · intro w hw
    rw [Unification.Ty.ftv_applyCapability] at hw
    exact targetBounded.targets w hw

/-- Sequencing bounded substitutions is bounded. -/
theorem Subst.BoundedBy.seq {q : InferenceBase.FreshSupply}
    {delta S : Subst} (deltaBounded : delta.BoundedBy q)
    (bounded : S.BoundedBy q) : (Subst.seq delta S).BoundedBy q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    show (S.cap varId).apply delta.cap = .var varId
    rw [bounded.capFixedAbove varId above]
    show delta.cap varId = .var varId
    exact deltaBounded.capFixedAbove varId above
  · intro varId below
    exact deltaBounded.applyCap (bounded.capImagesBounded varId below)
  · intro varId above
    show delta.apply (S.target varId) = .var varId
    rw [bounded.targetFixedAbove varId above]
    show (((Ty.var varId).applyCapability delta.cap).applyTarget
      delta.target) = .var varId
    exact deltaBounded.targetFixedAbove varId above
  · intro varId below
    exact deltaBounded.apply (bounded.targetImagesBounded varId below)

/-- Split membership in the capability variables of a list. -/
theorem Cap.mem_fcvList_split :
    ∀ {caps : List Cap} {varId : CapVar}, varId ∈ Cap.fcvList caps →
      ∃ capability, capability ∈ caps ∧ varId ∈ capability.fcv
  | [], _, mem => nomatch mem
  | cap :: caps, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨cap, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- Split membership in the capability variables of a type list. -/
theorem Ty.mem_fcvList_split :
    ∀ {types : List Ty} {varId : CapVar}, varId ∈ Ty.fcvList types →
      ∃ target, target ∈ types ∧ varId ∈ target.fcv
  | [], _, mem => nomatch mem
  | target :: types, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨target, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Ty.mem_fcvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- Split membership in the target variables of a type list. -/
theorem Ty.mem_ftvList_split :
    ∀ {types : List Ty} {varId : TypePM.TyVar}, varId ∈ Ty.ftvList types →
      ∃ target, target ∈ types ∧ varId ∈ target.ftv
  | [], _, mem => nomatch mem
  | target :: types, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨target, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Ty.mem_ftvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- A product of bounded types is bounded. -/
theorem Ty.BoundedBy.prodOfForall {q : InferenceBase.FreshSupply}
    {components : List Ty}
    (bounded : ∀ target ∈ components, Ty.BoundedBy q target) :
    (Ty.prod components).BoundedBy q := by
  constructor
  · intro w hw
    obtain ⟨target, targetMem, hMem⟩ := Ty.mem_fcvList_split hw
    exact (bounded target targetMem).caps w hMem
  · intro w hw
    obtain ⟨target, targetMem, hMem⟩ := Ty.mem_ftvList_split hw
    exact (bounded target targetMem).targets w hMem

/-- A product of bounded capabilities is bounded. -/
theorem Cap.BoundedBy.prodOfForall {q : InferenceBase.FreshSupply}
    {components : List Cap}
    (bounded : ∀ capability ∈ components, Cap.BoundedBy q capability) :
    (Cap.prod components).BoundedBy q := by
  intro w hw
  obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split hw
  exact bounded inner innerMem w hMem

/-- A constructor capability with bounded children is bounded. -/
theorem Cap.BoundedBy.conOfForall {q : InferenceBase.FreshSupply}
    {name : String} {components : List Cap}
    (bounded : ∀ capability ∈ components, Cap.BoundedBy q capability) :
    (Cap.con name components).BoundedBy q := by
  intro w hw
  obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split hw
  exact bounded inner innerMem w hMem

/-- A capability variable below the counter is bounded. -/
theorem Cap.BoundedBy.varOf {q : InferenceBase.FreshSupply}
    {varId : CapVar} (h : varId.id < q.nextCap) :
    (Cap.var varId).BoundedBy q := by
  intro w hw
  simp only [Cap.fcv, List.mem_singleton] at hw
  subst hw
  exact h

/-- A target variable below the counter is bounded. -/
theorem Ty.BoundedBy.varOf {q : InferenceBase.FreshSupply}
    {varId : TypePM.TyVar} (h : varId < q.nextTy) :
    (Ty.var varId).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv] at hw
    exact nomatch hw
  · intro w hw
    simp only [Ty.ftv, List.mem_singleton] at hw
    subst hw
    exact h

/-- The integer base type is bounded by every supply. -/
theorem Ty.BoundedBy.int {q : InferenceBase.FreshSupply} :
    Ty.int.BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv] at hw
    exact nomatch hw
  · intro w hw
    simp only [Ty.ftv] at hw
    exact nomatch hw

/-- A function type of bounded components is bounded. -/
theorem Ty.BoundedBy.fnOf {q : InferenceBase.FreshSupply}
    {domain codomain : Ty} (domainBounded : domain.BoundedBy q)
    (codomainBounded : codomain.BoundedBy q) :
    (Ty.fn domain codomain).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    exact hw.elim (domainBounded.caps w) (codomainBounded.caps w)
  · intro w hw
    simp only [Ty.ftv, List.mem_append] at hw
    exact hw.elim (domainBounded.targets w) (codomainBounded.targets w)

/-- A matcher type of bounded components is bounded. -/
theorem Ty.BoundedBy.matcherOf {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (capBounded : capability.BoundedBy q)
    (targetBounded : target.BoundedBy q) :
    (Ty.matcher capability target).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    exact hw.elim (capBounded w) (targetBounded.caps w)
  · intro w hw
    simp only [Ty.ftv] at hw
    exact targetBounded.targets w hw

/-- A slot type of bounded components is bounded. -/
theorem Ty.BoundedBy.slotOf {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (capBounded : capability.BoundedBy q)
    (targetBounded : target.BoundedBy q) :
    (Ty.slot capability target).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    exact hw.elim (capBounded w) (targetBounded.caps w)
  · intro w hw
    simp only [Ty.ftv] at hw
    exact targetBounded.targets w hw

end TypePM
