import TypePM.DemandTypingOriginMetatheory

/-!
# Core state erasure for origin-aware demand typing

This module is the staging point for the projection from an intrinsic
`DemandSynthOrigin` certificate to the state-free `TypingInvariant`.
It deliberately defines erasure as a proposition about the indices of an
existing origin derivation, rather than introducing another proof-carrying
typing family.

The first lemmas cover constructors whose terminal substitution is already
the substitution at which their runtime conclusion is consumed.  The
`lam`/`tuple` composition lemmas expose the central obligation for the full
mutual proof: an earlier child must first be transported to the terminal cut
of its parent.
-/

namespace TypePM

/-! ## Supply-scoped residual posts -/

namespace DDErasure

open DDLedger

private theorem DDLedger.OriginRefines.fromRigid
    {later : CapabilityOrigin}
    (refines : OriginRefines .rigid later) : later = .rigid := by
  cases refines
  rfl

private theorem DDLedger.OriginRefines.fromRenameOnly
    {later : CapabilityOrigin}
    (refines : OriginRefines .renameOnly later) : later = .renameOnly := by
  cases refines
  rfl

/-- No structurally flexible key remains below a particular supply cut. -/
def FrozenBelow (q : InferenceBase.FreshSupply)
    (ledger : CapabilityOriginLedger) : Prop :=
  ∀ varId, varId.id < q.nextCap →
    ledger.originOf varId ≠ .structuralFlexible

namespace FrozenBelow

/-- Freezing is stable under an origin refinement on the same prefix. -/
theorem ofRefines
    {q : InferenceBase.FreshSupply}
    {before after : CapabilityOriginLedger}
    (frozen : FrozenBelow q before)
    (refines : RefinesBelow q before after) : FrozenBelow q after := by
  intro varId below
  have refinement := refines varId below
  cases origin : before.originOf varId with
  | rigid =>
      have specialized : OriginRefines .rigid (after.originOf varId) := by
        simpa [origin] using refinement
      rw [DDLedger.OriginRefines.fromRigid specialized]
      decide
  | renameOnly =>
      have specialized :
          OriginRefines .renameOnly (after.originOf varId) := by
        simpa [origin] using refinement
      rw [DDLedger.OriginRefines.fromRenameOnly specialized]
      decide
  | structuralFlexible =>
      exact False.elim (frozen varId below origin)

end FrozenBelow

/--
Origin admissibility for a post between two supply/ledger cuts.

Restricting the domain to `input` is essential: the suffix may allocate keys
at or above that cut.  Recording the output ledger is equally essential: a
rename-only key may be renamed to a fresh rename-only key allocated inside
the suffix, whose safety cannot be read from the input ledger.
-/
structure AdmissiblePostBetween
    (input output : InferenceBase.FreshSupply)
    (before after : CapabilityOriginLedger) (post : Subst) : Prop where
  supplyExtends : SupplyExtends input output
  /-- The post cannot mention a variable that is only allocated by a later
  suffix.  This is the closure condition needed by `seq`. -/
  bounded : post.BoundedBy output
  refines : RefinesBelow input before after
  cap : ∀ varId, varId.id < input.nextCap →
    match before.originOf varId with
    | .rigid => post.cap varId = .var varId
    | .renameOnly =>
        ∃ image,
          post.cap varId = .var image ∧
          image.id < output.nextCap ∧
          after.originOf image ≠ .structuralFlexible
    | .structuralFlexible => True

/-- Variable-only projection restricted to variables below an input cut,
with an explicit bound on the output image. -/
def VariablePostBetween
    (input output : InferenceBase.FreshSupply) (post : Subst) : Prop :=
  ∀ varId, varId.id < input.nextCap →
    ∃ image, post.cap varId = .var image ∧ image.id < output.nextCap

namespace AdmissiblePostBetween

/-- Identity is admissible at one unchanged cut. -/
def id (q : InferenceBase.FreshSupply)
    (ledger : CapabilityOriginLedger) :
    AdmissiblePostBetween q q ledger ledger Subst.id where
  supplyExtends := SupplyExtends.refl q
  bounded := Subst.boundedBy_id q
  refines := RefinesBelow.refl q ledger
  cap := by
    intro varId below
    cases origin : ledger.originOf varId with
    | rigid => rfl
    | renameOnly =>
        exact ⟨varId, rfl, below, by simp [origin]⟩
    | structuralFlexible => trivial

/-- A pure allocation/freeze transition carries the identity post between
the two cuts. -/
def ofTransition
    {input output : InferenceBase.FreshSupply}
    {before after : CapabilityOriginLedger}
    (extension : SupplyExtends input output)
    (refines : RefinesBelow input before after) :
    AdmissiblePostBetween input output before after Subst.id where
  supplyExtends := extension
  bounded := (Subst.boundedBy_id input).mono extension
  refines := refines
  cap := by
    intro varId below
    have outputBelow : varId.id < output.nextCap :=
      Nat.lt_of_lt_of_le below extension.1
    have refinement := refines varId below
    cases origin : before.originOf varId with
    | rigid =>
        have specialized : OriginRefines .rigid (after.originOf varId) := by
          simpa [origin] using refinement
        have afterOrigin := DDLedger.OriginRefines.fromRigid specialized
        rfl
    | renameOnly =>
        have specialized :
            OriginRefines .renameOnly (after.originOf varId) := by
          simpa [origin] using refinement
        have afterOrigin := DDLedger.OriginRefines.fromRenameOnly specialized
        exact ⟨varId, rfl, outputBelow, by simp [afterOrigin]⟩
    | structuralFlexible =>
        trivial

/-- A globally admissible bounded solve is a scoped post at the same cut. -/
def ofAdmissible
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {post : Subst} (admissible : AdmissiblePost ledger post)
    (bounded : post.BoundedBy q) :
    AdmissiblePostBetween q q ledger ledger post where
  supplyExtends := SupplyExtends.refl q
  bounded := bounded
  refines := RefinesBelow.refl q ledger
  cap := by
    intro varId below
    cases origin : ledger.originOf varId with
    | rigid =>
        simpa [origin] using admissible.cap varId
    | renameOnly =>
        rcases admissible.cap.renameOnly origin with
          ⟨image, imageEquation, imageSafe⟩
        refine ⟨image, imageEquation, ?_, imageSafe⟩
        exact bounded.capImagesBounded varId below image (by
          rw [imageEquation]
          simp [Cap.fcv])
    | structuralFlexible =>
        trivial

/-- An origin-safe exact paired solve is a bounded same-cut residual post. -/
def ofExactPaired
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {left right : Ty} {post : Subst}
    (safe : OriginSafeExactPairedMGU ledger left right post)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    AdmissiblePostBetween q q ledger ledger post :=
  ofAdmissible safe.admissible
    (safe.exact.boundedBy leftBounded rightBounded)

/-- An origin-safe producer-to-slot solve is likewise a bounded same-cut
residual post. -/
def ofOneWay
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {post : Subst}
    (safe : OriginSafeOneWayDelta ledger producerCap producerTarget
      consumerCap consumerTarget post)
    (producerCapBounded : producerCap.BoundedBy q)
    (producerTargetBounded : producerTarget.BoundedBy q)
    (consumerCapBounded : consumerCap.BoundedBy q)
    (consumerTargetBounded : consumerTarget.BoundedBy q) :
    AdmissiblePostBetween q q ledger ledger post :=
  ofAdmissible safe.admissible
    (safe.exact.boundedBy producerCapBounded producerTargetBounded
      consumerCapBounded consumerTargetBounded)

/-- Supply-scoped admissibility composes across an intermediate cut. -/
def seq
    {initial middle final : InferenceBase.FreshSupply}
    {firstLedger middleLedger finalLedger : CapabilityOriginLedger}
    {earlier later : Subst}
    (first : AdmissiblePostBetween initial middle
      firstLedger middleLedger earlier)
    (second : AdmissiblePostBetween middle final
      middleLedger finalLedger later) :
    AdmissiblePostBetween initial final firstLedger finalLedger
      (Subst.seq later earlier) where
  supplyExtends := first.supplyExtends.trans second.supplyExtends
  bounded := second.bounded.seq
    (first.bounded.mono second.supplyExtends)
  refines := first.refines.trans
    (second.refines.restrict first.supplyExtends)
  cap := by
    intro varId below
    have middleBelow : varId.id < middle.nextCap :=
      Nat.lt_of_lt_of_le below first.supplyExtends.1
    cases firstOrigin : firstLedger.originOf varId with
    | rigid =>
        have earlierFixed : earlier.cap varId = .var varId := by
          simpa [firstOrigin] using first.cap varId below
        have middleRigid : middleLedger.originOf varId = .rigid := by
          have refinement := first.refines varId below
          have specialized :
              OriginRefines .rigid (middleLedger.originOf varId) := by
            simpa [firstOrigin] using refinement
          exact DDLedger.OriginRefines.fromRigid specialized
        have laterFixed : later.cap varId = .var varId := by
          simpa [middleRigid] using second.cap varId middleBelow
        simp [Subst.seq, CapSubst.comp, earlierFixed,
          laterFixed, Cap.apply]
    | renameOnly =>
        rcases (by simpa [firstOrigin] using first.cap varId below) with
          ⟨middleImage, earlierImage, middleImageBelow, middleImageSafe⟩
        cases middleOrigin : middleLedger.originOf middleImage with
        | rigid =>
            have laterFixed : later.cap middleImage = .var middleImage := by
              simpa [middleOrigin] using
                second.cap middleImage middleImageBelow
            have finalRigid : finalLedger.originOf middleImage = .rigid := by
              have refinement := second.refines middleImage middleImageBelow
              have specialized : OriginRefines .rigid
                  (finalLedger.originOf middleImage) := by
                simpa [middleOrigin] using refinement
              exact DDLedger.OriginRefines.fromRigid specialized
            refine ⟨middleImage, ?_,
              Nat.lt_of_lt_of_le middleImageBelow second.supplyExtends.1,
              by simp [finalRigid]⟩
            simp [Subst.seq, CapSubst.comp, earlierImage, laterFixed, Cap.apply]
        | renameOnly =>
            rcases (by simpa [middleOrigin] using
                second.cap middleImage middleImageBelow) with
              ⟨finalImage, laterImage, finalImageBelow, finalImageSafe⟩
            refine ⟨finalImage, ?_, finalImageBelow, finalImageSafe⟩
            simp [Subst.seq, CapSubst.comp, earlierImage, laterImage, Cap.apply]
        | structuralFlexible =>
            exact False.elim (middleImageSafe middleOrigin)
    | structuralFlexible =>
        trivial

/-- At a frozen input cut, scoped origin admissibility projects to a
variable-only post on every pre-existing key. -/
theorem toVariablePostBetween
    {input output : InferenceBase.FreshSupply}
    {before after : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePostBetween input output before after post)
    (frozen : FrozenBelow input before) :
    VariablePostBetween input output post := by
  intro varId below
  cases origin : before.originOf varId with
  | rigid =>
      refine ⟨varId, ?_, ?_⟩
      · simpa [origin] using admissible.cap varId below
      · exact Nat.lt_of_lt_of_le below admissible.supplyExtends.1
  | renameOnly =>
      rcases (by simpa [origin] using admissible.cap varId below) with
        ⟨image, equation, imageBelow, _⟩
      exact ⟨image, equation, imageBelow⟩
  | structuralFlexible =>
      exact False.elim (frozen varId below origin)

end AdmissiblePostBetween

namespace VariablePostBetween

/-- Identity is variable-only between monotonically related cuts. -/
theorem id
    {input output : InferenceBase.FreshSupply}
    (extension : SupplyExtends input output) :
    VariablePostBetween input output Subst.id := by
  intro varId below
  exact ⟨varId, rfl, Nat.lt_of_lt_of_le below extension.1⟩

/-- Variable-only scoped posts compose by matching their supply boundary. -/
theorem seq
    {initial middle final : InferenceBase.FreshSupply}
    {earlier later : Subst}
    (first : VariablePostBetween initial middle earlier)
    (second : VariablePostBetween middle final later) :
    VariablePostBetween initial final (Subst.seq later earlier) := by
  intro varId below
  rcases first varId below with ⟨middleImage, earlierImage, middleBelow⟩
  rcases second middleImage middleBelow with
    ⟨finalImage, laterImage, finalBelow⟩
  refine ⟨finalImage, ?_, finalBelow⟩
  simp [Subst.seq, CapSubst.comp, earlierImage, laterImage, Cap.apply]

end VariablePostBetween

/-! ## Chronological state factorization -/

/-- The output substitution is obtained from the input by one bounded,
origin-admissible chronological post. -/
def StateFactorization
    (input : InferenceBase.FreshSupply) (initial : Subst)
    (before : CapabilityOriginLedger)
    (output : InferenceBase.FreshSupply) (terminal : Subst)
    (after : CapabilityOriginLedger) : Prop :=
  ∃ post, terminal = Subst.seq post initial ∧
    AdmissiblePostBetween input output before after post

namespace StateFactorization

/-- No solve and no state transition. -/
theorem refl
    (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    StateFactorization q S ledger q S ledger := by
  refine ⟨Subst.id, ?_, AdmissiblePostBetween.id q ledger⟩
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (S.cap varId)).symm
  · funext varId
    exact (Subst.apply_id (S.target varId)).symm

/-- A ledger/supply-only transition contributes the identity post. -/
theorem ofTransition
    {input output : InferenceBase.FreshSupply} {S : Subst}
    {before after : CapabilityOriginLedger}
    (extension : SupplyExtends input output)
    (refines : RefinesBelow input before after) :
    StateFactorization input S before output S after := by
  refine ⟨Subst.id, ?_,
    AdmissiblePostBetween.ofTransition extension refines⟩
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (S.cap varId)).symm
  · funext varId
    exact (Subst.apply_id (S.target varId)).symm

/-- Chronological factorizations compose at their shared state cut. -/
theorem trans
    {q₀ q₁ q₂ : InferenceBase.FreshSupply}
    {S₀ S₁ S₂ : Subst}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    (first : StateFactorization q₀ S₀ ledger₀ q₁ S₁ ledger₁)
    (second : StateFactorization q₁ S₁ ledger₁ q₂ S₂ ledger₂) :
    StateFactorization q₀ S₀ ledger₀ q₂ S₂ ledger₂ := by
  rcases first with ⟨earlier, firstEquation, firstAdmissible⟩
  rcases second with ⟨later, secondEquation, secondAdmissible⟩
  refine ⟨Subst.seq later earlier, ?_,
    firstAdmissible.seq secondAdmissible⟩
  rw [secondEquation, firstEquation]
  exact PhasedPost.seq_assoc later earlier S₀

/-- A factorization and a bounded input substitution imply a bounded
terminal substitution. -/
theorem terminalBounded
    {input output : InferenceBase.FreshSupply}
    {initial terminal : Subst}
    {before after : CapabilityOriginLedger}
    (factorization : StateFactorization input initial before
      output terminal after)
    (initialBounded : initial.BoundedBy input) : terminal.BoundedBy output := by
  rcases factorization with ⟨post, equation, admissible⟩
  rw [equation]
  exact admissible.bounded.seq
    (initialBounded.mono admissible.supplyExtends)

/-- The factorization itself records supply monotonicity. -/
theorem supplyExtends
    {input output : InferenceBase.FreshSupply}
    {initial terminal : Subst}
    {before after : CapabilityOriginLedger}
    (factorization : StateFactorization input initial before
      output terminal after) : SupplyExtends input output := by
  rcases factorization with ⟨_, _, admissible⟩
  exact admissible.supplyExtends

/-- The factorization itself records ledger refinement at the input cut. -/
theorem refines
    {input output : InferenceBase.FreshSupply}
    {initial terminal : Subst}
    {before after : CapabilityOriginLedger}
    (factorization : StateFactorization input initial before
      output terminal after) : RefinesBelow input before after := by
  rcases factorization with ⟨_, _, admissible⟩
  exact admissible.refines

end StateFactorization

end DDErasure

/-! ## Bounded factorization of local alignment cuts -/

namespace DemandAlignTypesWithLedger

open DDErasure

/-- A ledger-aware equality alignment exposes its chronological post, with
the boundedness needed to compose that post with later suffixes. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst} {q : InferenceBase.FreshSupply}
    (aligned : DemandAlignTypesWithLedger ledger S left right S')
    (Sb : S.BoundedBy q) (leftBounded : left.BoundedBy q)
    (rightBounded : right.BoundedBy q) :
    ∃ post, S' = Subst.seq post S ∧
      AdmissiblePostBetween q q ledger ledger post := by
  cases aligned with
  | matcherPair leftView rightView capSafe targetSafe =>
      have resolvedLeft := Sb.apply leftBounded
      have resolvedRight := Sb.apply rightBounded
      rw [leftView] at resolvedLeft
      rw [rightView] at resolvedRight
      obtain ⟨leftCapB, leftTargetB⟩ := resolvedLeft.matcherParts
      obtain ⟨rightCapB, rightTargetB⟩ := resolvedRight.matcherParts
      have capPairB := capSafe.exact.boundedBy_pair leftCapB rightCapB
      have targetB := targetSafe.exact.boundedBy
        (capPairB.applyCapabilityTy leftTargetB)
        (capPairB.applyCapabilityTy rightTargetB)
      refine ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _, ?_⟩
      exact AdmissiblePostBetween.ofAdmissible
        (AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible })
        (targetB.seq capPairB)
  | slotPair leftView rightView capSafe targetSafe =>
      have resolvedLeft := Sb.apply leftBounded
      have resolvedRight := Sb.apply rightBounded
      rw [leftView] at resolvedLeft
      rw [rightView] at resolvedRight
      obtain ⟨leftCapB, leftTargetB⟩ := resolvedLeft.slotParts
      obtain ⟨rightCapB, rightTargetB⟩ := resolvedRight.slotParts
      have capPairB := capSafe.exact.boundedBy_pair leftCapB rightCapB
      have targetB := targetSafe.exact.boundedBy
        (capPairB.applyCapabilityTy leftTargetB)
        (capPairB.applyCapabilityTy rightTargetB)
      refine ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _, ?_⟩
      exact AdmissiblePostBetween.ofAdmissible
        (AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible })
        (targetB.seq capPairB)
  | ordinary _ deltaSafe =>
      exact ⟨_, rfl,
        AdmissiblePostBetween.ofExactPaired deltaSafe
          (Sb.apply leftBounded) (Sb.apply rightBounded)⟩

end DemandAlignTypesWithLedger

namespace DemandAlignWithLedger

open DDErasure

/-- A complete checking alignment has the same bounded chronological
factorization, including its one-way matcher-to-slot cases. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} {q : InferenceBase.FreshSupply}
    (aligned : DemandAlignWithLedger ledger S raw expected S')
    (Sb : S.BoundedBy q) (rawBounded : raw.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    ∃ post, S' = Subst.seq post S ∧
      AdmissiblePostBetween q q ledger ledger post := by
  cases aligned with
  | productMatcherLift rawView expectedView oneWay =>
      rename_i duals consumerCap consumerTarget delta
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [Inference.productMatcherDuals?_sound rawView] at resolvedRaw
      rw [expectedView] at resolvedExpected
      obtain ⟨consumerCapB, consumerTargetB⟩ :=
        resolvedExpected.slotParts
      have dualsB : ∀ dual ∈ duals,
          Cap.BoundedBy q dual.cap ∧ Ty.BoundedBy q dual.target := by
        intro dual dualMem
        have member : Ty.matcher dual.cap dual.target ∈
            duals.map (fun item => Ty.matcher item.cap item.target) :=
          List.mem_map.mpr ⟨dual, dualMem, rfl⟩
        exact resolvedRaw.of_mem_prod member |>.matcherParts
      have producerCapB : Cap.BoundedBy q (.prod (duals.map Dual.cap)) := by
        apply Cap.BoundedBy.prodOfForall
        intro capability capabilityMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp capabilityMem
        exact (dualsB dual dualMem).1
      have producerTargetB :
          Ty.BoundedBy q (.prod (duals.map Dual.target)) := by
        apply Ty.BoundedBy.prodOfForall
        intro target targetMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
        exact (dualsB dual dualMem).2
      exact ⟨delta, rfl,
        AdmissiblePostBetween.ofOneWay oneWay producerCapB producerTargetB
          consumerCapB consumerTargetB⟩
  | slotTupleLift demandClassView rawView expectedView capSafe targetSafe =>
      rename_i duals consumerCap consumerTarget capDelta targetDelta
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [Inference.productSlotDuals?_sound rawView] at resolvedRaw
      rw [expectedView] at resolvedExpected
      obtain ⟨consumerCapB, consumerTargetB⟩ :=
        resolvedExpected.slotParts
      have dualsB : ∀ dual ∈ duals,
          Cap.BoundedBy q dual.cap ∧ Ty.BoundedBy q dual.target := by
        intro dual dualMem
        have member : Ty.slot dual.cap dual.target ∈
            duals.map (fun item => Ty.slot item.cap item.target) :=
          List.mem_map.mpr ⟨dual, dualMem, rfl⟩
        exact resolvedRaw.of_mem_prod member |>.slotParts
      have producerCapB : Cap.BoundedBy q (.prod (duals.map Dual.cap)) := by
        apply Cap.BoundedBy.prodOfForall
        intro capability capabilityMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp capabilityMem
        exact (dualsB dual dualMem).1
      have producerTargetB :
          Ty.BoundedBy q (.prod (duals.map Dual.target)) := by
        apply Ty.BoundedBy.prodOfForall
        intro target targetMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
        exact (dualsB dual dualMem).2
      have capPairB := capSafe.exact.boundedBy_pair producerCapB consumerCapB
      have targetB := targetSafe.exact.boundedBy
        (capPairB.applyCapabilityTy producerTargetB)
        (capPairB.applyCapabilityTy consumerTargetB)
      refine ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _, ?_⟩
      exact AdmissiblePostBetween.ofAdmissible
        (AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible })
        (targetB.seq capPairB)
  | matcherToSlot rawView expectedView oneWay =>
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [rawView] at resolvedRaw
      rw [expectedView] at resolvedExpected
      obtain ⟨producerCapB, producerTargetB⟩ := resolvedRaw.matcherParts
      obtain ⟨consumerCapB, consumerTargetB⟩ :=
        resolvedExpected.slotParts
      exact ⟨_, rfl,
        AdmissiblePostBetween.ofOneWay oneWay producerCapB producerTargetB
          consumerCapB consumerTargetB⟩
  | slotToSlot rawView expectedView capSafe targetSafe =>
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [rawView] at resolvedRaw
      rw [expectedView] at resolvedExpected
      obtain ⟨sourceCapB, sourceTargetB⟩ := resolvedRaw.slotParts
      obtain ⟨requestedCapB, requestedTargetB⟩ :=
        resolvedExpected.slotParts
      have capPairB := capSafe.exact.boundedBy_pair sourceCapB requestedCapB
      have targetB := targetSafe.exact.boundedBy
        (capPairB.applyCapabilityTy sourceTargetB)
        (capPairB.applyCapabilityTy requestedTargetB)
      refine ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _, ?_⟩
      exact AdmissiblePostBetween.ofAdmissible
        (AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible })
        (targetB.seq capPairB)
  | ordinary _ equalityAligned =>
      exact equalityAligned.factorPost Sb rawBounded expectedBounded

end DemandAlignWithLedger

namespace DDErasure.StateFactorization

/-- Regard a bounded ordinary equality alignment as a same-cut state
factorization. -/
theorem ofAlignTypes
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {left right : Ty}
    (aligned : DemandAlignTypesWithLedger ledger S left right S')
    (Sb : S.BoundedBy q) (leftBounded : left.BoundedBy q)
    (rightBounded : right.BoundedBy q) :
    StateFactorization q S ledger q S' ledger :=
  aligned.factorPost Sb leftBounded rightBounded

/-- Regard a bounded complete checking alignment as a same-cut state
factorization. -/
theorem ofAlign
    {q : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger : CapabilityOriginLedger} {raw expected : Ty}
    (aligned : DemandAlignWithLedger ledger S raw expected S')
    (Sb : S.BoundedBy q) (rawBounded : raw.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    StateFactorization q S ledger q S' ledger :=
  aligned.factorPost Sb rawBounded expectedBounded

end DDErasure.StateFactorization

namespace DemandCheckOrigin

/-- State evolution exposed by an origin-aware checking derivation. -/
def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandCheckOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

end DemandCheckOrigin

namespace DemandChecksOrigin

/-- State evolution exposed by an origin-aware checking list. -/
def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandChecksOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

end DemandChecksOrigin

namespace DemandSynthOrigin

/-- State evolution exposed by an origin-aware synthesis derivation. -/
def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandSynthOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

/-- Variable lookup performs only the scheme-instantiation allocation. -/
theorem stateFactorization_var
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (name : String) (scheme : Scheme)
    (ledger : CapabilityOriginLedger)
    (lookup : (context.applySubst S).find? name = some scheme) :
    StateFactorization
      (DemandSynthOrigin.var (signature := signature) (q := q)
        (ledger := ledger) lookup) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.instantiateScheme q scheme)
    (DDLedger.RefinesBelow.markSchemeInstance q ledger scheme)

/-- Literal synthesis is a state identity. -/
theorem stateFactorization_lit
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (value : Int) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DemandSynthOrigin.lit (signature := signature) (q := q) (S := S)
        (context := context) (value := value) (ledger := ledger)) := by
  exact DDErasure.StateFactorization.refl q S ledger

/-- `something` only reserves one fresh target variable. -/
theorem stateFactorization_something
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DemandSynthOrigin.something (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.bumpTy q 1) (DDLedger.RefinesBelow.refl q ledger)

/-- A lambda prepends its target-variable allocation to the body suffix. -/
theorem stateFactorization_lam_of_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {body : Expr} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: context) body bodyTarget q' S'}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw ledger ledger')
    (bodyFactorization : StateFactorization bodyOrigin) :
    StateFactorization (DemandSynthOrigin.lam bodyOrigin) := by
  exact (DDErasure.StateFactorization.ofTransition
    (SupplyExtends.bumpTy q 1) (DDLedger.RefinesBelow.refl q ledger)).trans
      bodyFactorization

/-- A recursive-function synthesis is the body suffix followed by its final
equality alignment. -/
theorem stateFactorization_fix_of_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {body : Expr}
    {bodyTarget : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
      body bodyTarget q₁ S₁}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw ledger ledger₁)
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ bodyTarget
      (.var (q.nextTy + 1)) S')
    (bodyFactorization : StateFactorization bodyOrigin)
    (S₁Bounded : S₁.BoundedBy q₁)
    (bodyBounded : bodyTarget.BoundedBy q₁)
    (codomainBounded : Ty.BoundedBy q₁ (.var (q.nextTy + 1))) :
    StateFactorization
      (DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S)
    (SupplyExtends.bumpTy q 2) (DDLedger.RefinesBelow.refl q ledger)
  have alignment := DDErasure.StateFactorization.ofAlignTypes aligned
    S₁Bounded bodyBounded codomainBounded
  exact (allocation.trans bodyFactorization).trans alignment

/-- Application factors in execution order: function, fresh function-shape
allocation, equality alignment, and argument checking. -/
theorem stateFactorization_app_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {function argument : Expr} {functionTarget : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
    {q₂ : InferenceBase.FreshSupply} {S₃ : Subst}
    {ledger ledger₁ ledger₃ : CapabilityOriginLedger}
    {functionRaw : DemandSynth signature q S context function functionTarget q₁ S₁}
    (functionOrigin : DemandSynthOrigin signature functionRaw ledger ledger₁)
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂)
    {argumentRaw : DemandCheck signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ context argument
      (.var q₁.nextTy) q₂ S₃}
    (argumentOrigin : DemandCheckOrigin signature argumentRaw ledger₁ ledger₃)
    (functionFactorization : StateFactorization functionOrigin)
    (argumentFactorization :
      DemandCheckOrigin.StateFactorization argumentOrigin)
    (S₁Bounded : S₁.BoundedBy { q₁ with nextTy := q₁.nextTy + 2 })
    (functionBounded :
      functionTarget.BoundedBy { q₁ with nextTy := q₁.nextTy + 2 })
    (shapeBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 }
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))) :
    StateFactorization
      (DemandSynthOrigin.app functionOrigin aligned argumentOrigin) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S₁)
    (SupplyExtends.bumpTy q₁ 2)
    (DDLedger.RefinesBelow.refl q₁ ledger₁)
  have alignment := DDErasure.StateFactorization.ofAlignTypes aligned
    S₁Bounded functionBounded shapeBounded
  exact ((functionFactorization.trans allocation).trans alignment).trans
    argumentFactorization

/-- Let synthesis is the chronological composition of value and body. -/
theorem stateFactorization_let_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {value body : Expr}
    {valueTarget : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {valueRaw : DemandSynth signature q S context value valueTarget q₁ S₁}
    (valueOrigin : DemandSynthOrigin signature valueRaw ledger ledger₁)
    {bodyRaw : DemandSynth signature q₁ S₁
      ((name, signature.generalize (context.applySubst S₁)
        (S₁.apply valueTarget)) :: context) body bodyTarget q' S'}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw ledger₁ ledger')
    (valueFactorization : StateFactorization valueOrigin)
    (bodyFactorization : StateFactorization bodyOrigin) :
    StateFactorization
      (DemandSynthOrigin.letE valueOrigin bodyOrigin) := by
  exact valueFactorization.trans bodyFactorization

/-- Shared allocation/check/freeze skeleton for data constructors and
primitives.  Their public Origin constructors differ only in the signature
lookup that selects the same `CtorScheme`. -/
private theorem stateFactorization_ctorLike
    {q : InferenceBase.FreshSupply} {S : Subst} {scheme : CtorScheme}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      (DDLedger.markCtorInstance ledger q scheme) q' S' ledger₁) :
    DDErasure.StateFactorization q S ledger q' S'
      (DDLedger.freezeExport ledger₁ S'
        (Inference.freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.instantiateCtorScheme q scheme)
    (DDLedger.RefinesBelow.markCtorInstance q ledger scheme)
  have freezing := DDErasure.StateFactorization.ofTransition
    (S := S') (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeExport q' ledger₁ S'
      (Inference.freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2)
  exact (allocation.trans childrenFactorization).trans freezing

/-- A data constructor allocates its instance, checks the children, then
freezes precisely the exported capability leaves. -/
theorem stateFactorization_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    {children : DemandChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DemandChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger₁)
    (childrenFactorization :
      DemandChecksOrigin.StateFactorization childrenOrigin) :
    StateFactorization (DemandSynthOrigin.ctor lookup childrenOrigin) := by
  exact stateFactorization_ctorLike childrenFactorization

/-- Primitive application has the same allocation/check/freeze state shape
as a data constructor. -/
theorem stateFactorization_prim_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (lookup : signature.findPrimitive op = some scheme)
    {children : DemandChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DemandChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger₁)
    (childrenFactorization :
      DemandChecksOrigin.StateFactorization childrenOrigin) :
    StateFactorization (DemandSynthOrigin.prim lookup childrenOrigin) := by
  exact stateFactorization_ctorLike childrenFactorization

/-- Matcher synthesis reserves its target, traverses its clauses, and then
freezes the inferred producer capability.  The clause suffix is kept as an
explicit premise until the clause-family factorization joins this module. -/
theorem stateFactorization_matcher_of_clauses
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause}
    {rawHoleLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {evidence : List Shape.Evidence} {capability : Cap}
    {ledger ledger₁ : CapabilityOriginLedger}
    {clausesRaw : DDClauses signature
      { q with nextTy := q.nextTy + 1 } S context clauses
      (.var q.nextTy) rawHoleLists q' S'}
    (clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁)
    (collected : Inference.collectClauseEvidence signature.toMatcherSig
      clauses (terminalHoleCaps S' rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability)
    (clauseCaps : Inference.clauseCapsListCheck signature capability clauses
      (terminalHoleCaps S' rawHoleLists) = true)
    (catchAll : Inference.catchAllLastCheck clauses = true)
    (binders : Inference.matcherBindersCheck clauses = true)
    (arms : Inference.armExhaustiveCheck signature clauses
      (S'.apply (.var q.nextTy)) = true)
    (coverage : Inference.coverageCheck signature.toMatcherSig clauses
      capability = true)
    (clausesFactorization : DDErasure.StateFactorization
      { q with nextTy := q.nextTy + 1 } S ledger q' S' ledger₁) :
    StateFactorization
      (DemandSynthOrigin.matcher clausesOrigin collected inferred clauseCaps
        catchAll binders arms coverage) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.bumpTy q 1)
    (DDLedger.RefinesBelow.refl q ledger)
  have freezing := DDErasure.StateFactorization.ofTransition
    (S := S') (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeMatcherProducer q' ledger₁ capability)
  exact (allocation.trans clausesFactorization).trans freezing

/-- `matchAll` is a direct chronological composition.  The user-pattern
suffix remains explicit until the pattern-family theorem is available. -/
theorem stateFactorization_matchAll_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {target matcher : Expr} {pattern : Pattern}
    {body : Expr} {targetTarget : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {dual : Dual} {bindings : MonoCtx}
    {q₂ : InferenceBase.FreshSupply} {S₂ S₃ : Subst}
    {q₃ : InferenceBase.FreshSupply} {S₄ : Subst}
    {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger₂ ledger₃ ledger' : CapabilityOriginLedger}
    {targetRaw : DemandSynth signature q S context target targetTarget q₁ S₁}
    (targetOrigin : DemandSynthOrigin signature targetRaw ledger ledger₁)
    {patternRaw : DDPattern signature q₁ S₁ context [] [] pattern dual
      bindings q₂ S₂}
    (patternOrigin : DDPatternOrigin signature patternRaw ledger₁ ledger₂)
    (targetAligned : DemandAlignTypesWithLedger ledger₂ S₂ dual.target
      targetTarget S₃)
    {matcherRaw : DemandCheck signature q₂ S₃ context matcher
      (.slot dual.cap targetTarget) q₃ S₄}
    (matcherOrigin : DemandCheckOrigin signature matcherRaw ledger₂ ledger₃)
    {bodyRaw : DemandSynth signature q₃ S₄
      (bindings.toContext ++ context) body bodyTarget q' S'}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw ledger₃ ledger')
    (targetFactorization : StateFactorization targetOrigin)
    (patternFactorization : DDErasure.StateFactorization
      q₁ S₁ ledger₁ q₂ S₂ ledger₂)
    (matcherFactorization :
      DemandCheckOrigin.StateFactorization matcherOrigin)
    (bodyFactorization : StateFactorization bodyOrigin)
    (S₂Bounded : S₂.BoundedBy q₂)
    (dualTargetBounded : dual.target.BoundedBy q₂)
    (targetTargetBounded : targetTarget.BoundedBy q₂) :
    StateFactorization
      (DemandSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
        matcherOrigin bodyOrigin) := by
  have alignment := DDErasure.StateFactorization.ofAlignTypes targetAligned
    S₂Bounded dualTargetBounded targetTargetBounded
  exact ((((targetFactorization.trans patternFactorization).trans alignment).trans
    matcherFactorization).trans bodyFactorization)

/-- A matcher-specific recursive function allocates its placeholder range,
synthesizes the matcher body, and performs the final equality alignment. -/
theorem stateFactorization_fixMatcher_of_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {clauses : List Clause}
    {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
    {bodyTarget : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholder : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q₀))
    {bodyRaw : DemandSynth signature q₀ S
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono (.fn domain codomain)) :: context)
      (.matcher clauses) bodyTarget q₁ S₁}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw
      (DDLedger.markCapRange ledger q q₀) ledger₁)
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ bodyTarget codomain S')
    (bodyFactorization : StateFactorization bodyOrigin)
    (S₁Bounded : S₁.BoundedBy q₁)
    (bodyBounded : bodyTarget.BoundedBy q₁)
    (codomainBounded : codomain.BoundedBy q₁) :
    StateFactorization
      (DemandSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin
        aligned) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.fixMatcherPlaceholder placeholder)
    (DDLedger.RefinesBelow.markCapRange q q₀ ledger)
  have alignment := DDErasure.StateFactorization.ofAlignTypes aligned
    S₁Bounded bodyBounded codomainBounded
  exact (allocation.trans bodyFactorization).trans alignment

/-- The state-free conclusion expected from one origin-aware synthesis
derivation at its own terminal cut. -/
def TypingInvariantErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandSynthOrigin signature raw ledger ledger') : Prop :=
  TypingInvariant signature (context.applySubst S') expression (S'.apply target)

/-- Integer synthesis erases directly: it allocates and solves nothing. -/
theorem typingInvariantErasure_lit
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (value : Int) (ledger : CapabilityOriginLedger) :
    TypingInvariantErasure
      (DemandSynthOrigin.lit (signature := signature) (q := q) (S := S)
        (context := context) (value := value) (ledger := ledger)) := by
  simp only [TypingInvariantErasure, Subst.apply_int]
  exact TypingInvariant.lit

/-- `something` also erases directly; its fresh target remains an arbitrary
runtime target after the terminal substitution is applied. -/
theorem typingInvariantErasure_something
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    TypingInvariantErasure
      (DemandSynthOrigin.something (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  simp only [TypingInvariantErasure, Subst.apply_matcher, Cap.apply]
  exact TypingInvariant.something

/-- Once the body has been projected at the lambda's terminal cut, the
lambda constructor itself is a purely structural erasure step. -/
theorem typingInvariantErasure_lam_of_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {body : Expr} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: context) body bodyTarget q' S'}
    (bodyOrigin : DemandSynthOrigin signature bodyRaw ledger ledger')
    (bodyErasure : TypingInvariantErasure bodyOrigin) :
    TypingInvariantErasure (DemandSynthOrigin.lam bodyOrigin) := by
  simp only [TypingInvariantErasure, Context.applySubst, List.map_cons,
    Scheme.applyMeta_mono, Subst.apply_fn] at bodyErasure ⊢
  exact TypingInvariant.lam bodyErasure

end DemandSynthOrigin

namespace DemandSynthsOrigin

/-- State evolution exposed by an origin-aware synthesis list. -/
def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandSynthsOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DemandSynthsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  exact DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DemandSynth signature q S context expression target q₁ S₁}
    {tail : DemandSynths signature q₁ S₁ context expressions targets q' S'}
    (headOrigin : DemandSynthOrigin signature head ledger ledger₁)
    (tailOrigin : DemandSynthsOrigin signature tail ledger₁ ledger')
    (headFactorization : DemandSynthOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization (DemandSynthsOrigin.cons headOrigin tailOrigin) := by
  exact headFactorization.trans tailFactorization

/-- Terminal state-free conclusion for an origin-aware synthesis list. -/
def TypingInvariantErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DemandSynthsOrigin signature raw ledger ledger') : Prop :=
  ExprsTy signature (context.applySubst S') expressions
    (targets.map S'.apply)

/-- Empty synthesis-list erasure. -/
theorem typingInvariantErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    TypingInvariantErasure
      (DemandSynthsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  exact ExprsTy.nil

/-- List composition after the head has been transported to the tail's
terminal substitution.  Producing `headAtTerminal` from the head origin is
the residual-post transport obligation of the full mutual proof. -/
theorem typingInvariantErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DemandSynth signature q S context expression target q₁ S₁}
    {tail : DemandSynths signature q₁ S₁ context expressions targets q' S'}
    (headOrigin : DemandSynthOrigin signature head ledger ledger₁)
    (tailOrigin : DemandSynthsOrigin signature tail ledger₁ ledger')
    (headAtTerminal :
      TypingInvariant signature (context.applySubst S') expression
        (S'.apply target))
    (tailErasure : TypingInvariantErasure tailOrigin) :
    TypingInvariantErasure (DemandSynthsOrigin.cons headOrigin tailOrigin) := by
  exact ExprsTy.cons headAtTerminal tailErasure

end DemandSynthsOrigin

namespace DemandSynthOrigin

/-- Tuple synthesis has exactly the state suffix of its child traversal. -/
theorem stateFactorization_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DemandSynths signature q S context expressions targets q' S'}
    (childrenOrigin : DemandSynthsOrigin signature children ledger ledger')
    (childrenFactorization :
      DemandSynthsOrigin.StateFactorization childrenOrigin) :
    StateFactorization (DemandSynthOrigin.tuple childrenOrigin) :=
  childrenFactorization

/-- Tuple erasure is structural once the whole child list has been projected
at the tuple's terminal cut. -/
theorem typingInvariantErasure_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DemandSynths signature q S context expressions targets q' S'}
    (childrenOrigin : DemandSynthsOrigin signature children ledger ledger')
    (childrenErasure : DemandSynthsOrigin.TypingInvariantErasure childrenOrigin) :
    TypingInvariantErasure (DemandSynthOrigin.tuple childrenOrigin) := by
  simp only [TypingInvariantErasure, Subst.apply_prod]
  exact TypingInvariant.tuple childrenErasure

end DemandSynthOrigin

namespace DemandCheckOrigin

/-- Checking composes the synthesis suffix with its terminal alignment. -/
theorem stateFactorization_mk
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected raw : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    {synthesized : DemandSynth signature q S context expression raw q₁ S₁}
    (synthOrigin : DemandSynthOrigin signature synthesized ledger ledger₁)
    (aligned : DemandAlignWithLedger ledger₁ S₁ raw expected S')
    (synthFactorization : DemandSynthOrigin.StateFactorization synthOrigin)
    (S₁Bounded : S₁.BoundedBy q₁) (rawBounded : raw.BoundedBy q₁)
    (expectedBounded : expected.BoundedBy q₁) :
    StateFactorization (DemandCheckOrigin.mk synthOrigin aligned) := by
  exact synthFactorization.trans
    (DDErasure.StateFactorization.ofAlign aligned S₁Bounded rawBounded
      expectedBounded)

/-- The boundedness premises normally available at the input cut suffice to
discharge the terminal alignment bounds automatically. -/
theorem stateFactorization_mk_bounded
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected raw : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    {synthesized : DemandSynth signature q S context expression raw q₁ S₁}
    (synthOrigin : DemandSynthOrigin signature synthesized ledger ledger₁)
    (aligned : DemandAlignWithLedger ledger₁ S₁ raw expected S')
    (synthFactorization : DemandSynthOrigin.StateFactorization synthOrigin)
    (closed : signature.SchemesClosed) (SBounded : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) :
    StateFactorization (DemandCheckOrigin.mk synthOrigin aligned) := by
  obtain ⟨S₁Bounded, rawBounded⟩ :=
    synthesized.boundedBy closed SBounded contextBounded
  exact stateFactorization_mk synthOrigin aligned synthFactorization
    S₁Bounded rawBounded
    (expectedBounded.mono synthesized.supplyExtends)

end DemandCheckOrigin

namespace DemandChecksOrigin

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DemandChecksOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  exact DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DemandCheck signature q S context expression expected q₁ S₁}
    {tail : DemandChecks signature q₁ S₁ context expressions expecteds q' S'}
    (headOrigin : DemandCheckOrigin signature head ledger ledger₁)
    (tailOrigin : DemandChecksOrigin signature tail ledger₁ ledger')
    (headFactorization : DemandCheckOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization (DemandChecksOrigin.cons headOrigin tailOrigin) := by
  exact headFactorization.trans tailFactorization

end DemandChecksOrigin

namespace DemandAlignTypesWithLedger

/-- Ordinary equality alignment needs no coercion constructor: equality at
the output cut transports the already-erased runtime conclusion. -/
theorem transportRuntime
    {signature : FrozenSig} {ledger : CapabilityOriginLedger}
    {S : Subst} {left right : Ty} {S' : Subst}
    (aligned : DemandAlignTypesWithLedger ledger S left right S')
    {context : Context} {expression : Expr}
    (typing : TypingInvariant signature (context.applySubst S') expression
      (S'.apply left)) :
    TypingInvariant signature (context.applySubst S') expression
      (S'.apply right) := by
  rw [← aligned.output_equal]
  exact typing

end DemandAlignTypesWithLedger

end TypePM
