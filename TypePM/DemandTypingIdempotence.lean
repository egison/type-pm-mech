import TypePM.DemandTyping

/-!
# Solved-form preservation for demand-directed typing

The demand-directed judgments thread one prevailing substitution.  This file
shows that every local solve, and hence every complete DD derivation, preserves
the solved-form (`Subst.Idempotent`) invariant.
-/

namespace TypePM

namespace DemandTypingIdempotence

/-! ## Local solve steps -/

/-- The capability-only pair associated with a capability substitution. -/
private def capOnly (C : CapSubst) : Subst := ⟨C, TySubst.id⟩

/-- The target-only pair associated with a target substitution. -/
private def targetOnly (T : TySubst) : Subst := ⟨CapSubst.id, T⟩

/-- Exact capability solving preserves a solved-form prevailing substitution
when its already-resolved constraint is fixed by that substitution. -/
private theorem exactCap_seq_idempotent_of_fixed
    {S : Subst} {left right : Cap} {C : CapSubst}
    (idem : S.Idempotent) (exact : ExactCapMGU left right C)
    (leftFixed : left.apply S.cap = left)
    (rightFixed : right.apply S.cap = right) :
    (Subst.seq (capOnly C) S).Idempotent := by
  apply Subst.seq_idempotent
  · exact Subst.idempotent_of_targetId exact.2.2.2
  · intro target
    apply Subst.apply_eq_self_of_fixed
    · intro varId mem
      have mem' : varId ∈ (S.apply target).ftv := by
        simpa [capOnly, Subst.apply, Ty.applyTarget_id,
          Unification.Ty.ftv_applyCapability] using mem
      exact idem.image_target_fixed target varId mem'
    · intro varId mem
      have mem' : varId ∈
          ((S.apply target).applyCapability C).fcv := by
        simpa [capOnly, Subst.apply, Ty.applyTarget_id] using mem
      rw [Unification.Ty.fcv_applyCapability] at mem'
      obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp mem'
      by_cases inConstraint : source ∈ left.fcv ++ right.fcv
      · have imageIn : varId ∈ left.fcv ++ right.fcv :=
          exact.2.2.1 source inConstraint varId imageMem
        rcases List.mem_append.mp imageIn with inLeft | inRight
        · exact Cap.fixed_of_apply_self left leftFixed varId inLeft
        · exact Cap.fixed_of_apply_self right rightFixed varId inRight
      · rw [exact.2.1 source inConstraint] at imageMem
        have equality : varId = source := by
          simpa [Cap.fcv] using imageMem
        subst varId
        exact idem.image_cap_fixed target source sourceMem

/-- Exact target solving preserves a solved-form prevailing substitution when
the two already-resolved target constraints are fixed at the cut. -/
private theorem exactTarget_seq_idempotent_of_fixed
    {S : Subst} {left right : Ty} {T : TySubst}
    (idem : S.Idempotent) (exact : ExactTargetMGU left right T)
    (leftFixed : S.apply left = left) (rightFixed : S.apply right = right) :
    (Subst.seq (targetOnly T) S).Idempotent := by
  apply Subst.seq_idempotent
  · exact Subst.idempotent_of_capId exact.2.2.2.2
  · intro target
    apply Subst.apply_eq_self_of_fixed
    · intro varId mem
      have mem' : varId ∈ ((S.apply target).applyTarget T).ftv := by
        simpa [targetOnly, Subst.apply, Ty.applyCapability_id] using mem
      rw [Unification.Ty.ftv_applyTarget] at mem'
      obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp mem'
      by_cases inConstraint : source ∈ left.ftv ++ right.ftv
      · have imageIn : varId ∈ left.ftv ++ right.ftv :=
          exact.2.2.1 source inConstraint varId imageMem
        rcases List.mem_append.mp imageIn with inLeft | inRight
        · exact Subst.target_fixed_of_apply_self left leftFixed varId inLeft
        · exact Subst.target_fixed_of_apply_self right rightFixed varId inRight
      · rw [exact.2.1 source inConstraint] at imageMem
        have equality : varId = source := by simpa [Ty.ftv] using imageMem
        subst varId
        exact idem.image_target_fixed target source sourceMem
    · intro varId mem
      have mem' : varId ∈ ((S.apply target).applyTarget T).fcv := by
        simpa [targetOnly, Subst.apply, Ty.applyCapability_id] using mem
      rcases Ty.mem_fcv_applyTarget _ _ _ mem' with original | image
      · exact idem.image_cap_fixed target varId original
      · obtain ⟨source, sourceMem, imageMem⟩ := image
        by_cases inConstraint : source ∈ left.ftv ++ right.ftv
        · have imageIn : varId ∈ left.fcv ++ right.fcv :=
            exact.2.2.2.1 source inConstraint varId imageMem
          rcases List.mem_append.mp imageIn with inLeft | inRight
          · exact Subst.cap_fixed_of_apply_self left leftFixed varId inLeft
          · exact Subst.cap_fixed_of_apply_self right rightFixed varId inRight
        · rw [exact.2.1 source inConstraint] at imageMem
          nomatch imageMem

/-- A fixed type may be used as the resolved input expected by the standard
exact-paired sequencing theorem. -/
private theorem exactPaired_seq_idempotent_of_fixed
    {S delta : Subst} {left right : Ty}
    (idem : S.Idempotent) (exact : ExactPairedMGU left right delta)
    (leftFixed : S.apply left = left) (rightFixed : S.apply right = right) :
    (Subst.seq delta S).Idempotent := by
  rw [← leftFixed, ← rightFixed] at exact
  exact exact.seq_idempotent idem

/-- A type whose free variables occur in one prevailing image is fixed by a
solved-form prevailing substitution. -/
private theorem Subst.Idempotent.fixed_of_free_subset
    {S : Subst} (idem : S.Idempotent) (container source : Ty)
    (targetSubset : ∀ varId, varId ∈ source.ftv →
      varId ∈ (S.apply container).ftv)
    (capSubset : ∀ varId, varId ∈ source.fcv →
      varId ∈ (S.apply container).fcv) :
    S.apply source = source := by
  apply Subst.apply_eq_self_of_fixed
  · intro varId mem
    exact idem.image_target_fixed container varId (targetSubset varId mem)
  · intro varId mem
    exact idem.image_cap_fixed container varId (capSubset varId mem)

/-- Capability-zonking by a solved-form paired substitution is itself fixed. -/
private theorem Subst.Idempotent.cap_apply_fixed
    {S : Subst} (idem : S.Idempotent) (capability : Cap) :
    (capability.apply S.cap).apply S.cap = capability.apply S.cap := by
  have reapplied := idem (.matcher capability .unit)
  simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at reapplied
  exact (Ty.matcher.inj reapplied).1

/-- The common capability-then-paired-target solve sequence preserves solved
form once the four resolved components are fixed at the incoming cut. -/
private theorem twoPhase_seq_idempotent_of_fixed
    {S targetDelta : Subst} {leftCap rightCap : Cap}
    {leftTarget rightTarget : Ty} {C : CapSubst}
    (idem : S.Idempotent) (capExact : ExactCapMGU leftCap rightCap C)
    (targetExact : ExactPairedMGU (leftTarget.applyCapability C)
      (rightTarget.applyCapability C) targetDelta)
    (leftCapFixed : leftCap.apply S.cap = leftCap)
    (rightCapFixed : rightCap.apply S.cap = rightCap)
    (leftTargetFixed : S.apply leftTarget = leftTarget)
    (rightTargetFixed : S.apply rightTarget = rightTarget) :
    (Subst.seq targetDelta (Subst.seq (capOnly C) S)).Idempotent := by
  let P := Subst.seq (capOnly C) S
  have Pidem : P.Idempotent :=
    exactCap_seq_idempotent_of_fixed idem capExact leftCapFixed rightCapFixed
  have leftAtP : P.apply leftTarget = leftTarget.applyCapability C := by
    dsimp [P]
    rw [Subst.seq_apply, leftTargetFixed]
    simp [capOnly, Subst.apply, Ty.applyTarget_id]
  have rightAtP : P.apply rightTarget = rightTarget.applyCapability C := by
    dsimp [P]
    rw [Subst.seq_apply, rightTargetFixed]
    simp [capOnly, Subst.apply, Ty.applyTarget_id]
  have leftConstraintFixed :
      P.apply (leftTarget.applyCapability C) =
        leftTarget.applyCapability C := by
    have twice := Pidem leftTarget
    rwa [leftAtP] at twice
  have rightConstraintFixed :
      P.apply (rightTarget.applyCapability C) =
        rightTarget.applyCapability C := by
    have twice := Pidem rightTarget
    rwa [rightAtP] at twice
  exact exactPaired_seq_idempotent_of_fixed Pidem targetExact
    leftConstraintFixed rightConstraintFixed

/-- The support-restricted substitution produced by one-way capability
matching is in solved form. -/
private theorem matchCap_subst_idempotent
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    (run : CapMatch.matchCap producer consumer = some bindings) :
    (bindings.toSubstWithin consumer.fcv).Idempotent := by
  apply CapSubst.idempotent_of_pointwise
  intro source
  by_cases supported : source ∈ consumer.fcv
  · rw [show bindings.toSubstWithin consumer.fcv source =
        bindings.toSubst source by
      simp [CapMatch.Bindings.toSubstWithin, supported]]
    cases lookup : bindings.lookup source with
    | none =>
        have unrestricted : bindings.toSubst source = .var source := by
          simp [CapMatch.Bindings.toSubst, lookup]
        rw [unrestricted]
        show bindings.toSubstWithin consumer.fcv source = .var source
        simp [CapMatch.Bindings.toSubstWithin, CapMatch.Bindings.toSubst,
          supported, lookup]
    | some capability =>
        rw [show bindings.toSubst source = capability by
          simp [CapMatch.Bindings.toSubst, lookup]]
        apply Cap.apply_eq_self_of_fcv_fixed
        intro image imageMem
        have inProducer :=
          matchCap_imagesWithin run source capability lookup image imageMem
        exact Cap.fixed_of_apply_self producer
          ((CapMatch.matchCap_eq_some_iff producer consumer bindings).mp
            run).2 image inProducer
  · have outside : bindings.toSubstWithin consumer.fcv source =
        .var source := by
      simp [CapMatch.Bindings.toSubstWithin, supported]
    rw [outside]
    exact outside

/-- A one-way capability substitution has range within the producer's
capability variables, apart from identity images. -/
private theorem matchCap_subst_range
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    (run : CapMatch.matchCap producer consumer = some bindings) :
    ∀ source image,
      image ∈ (bindings.toSubstWithin consumer.fcv source).fcv →
      image = source ∨ image ∈ producer.fcv := by
  intro source image imageMem
  by_cases supported : source ∈ consumer.fcv
  · rw [show bindings.toSubstWithin consumer.fcv source =
        bindings.toSubst source by
      simp [CapMatch.Bindings.toSubstWithin, supported]] at imageMem
    cases lookup : bindings.lookup source with
    | none =>
        have equality : image = source := by
          simpa [CapMatch.Bindings.toSubst, lookup, Cap.fcv] using imageMem
        exact Or.inl equality
    | some capability =>
        rw [show bindings.toSubst source = capability by
          simp [CapMatch.Bindings.toSubst, lookup]] at imageMem
        exact Or.inr
          (matchCap_imagesWithin run source capability lookup image imageMem)
  · rw [show bindings.toSubstWithin consumer.fcv source = .var source by
        simp [CapMatch.Bindings.toSubstWithin, supported]] at imageMem
    exact Or.inl (by simpa [Cap.fcv] using imageMem)

/-- Sequencing the capability phase of a successful one-way match preserves
solved form when the resolved producer is fixed by the prevailing state. -/
private theorem matchCap_seq_idempotent_of_fixed
    {S : Subst} {producer consumer : Cap}
    {bindings : CapMatch.Bindings}
    (idem : S.Idempotent)
    (run : CapMatch.matchCap producer consumer = some bindings)
    (producerFixed : producer.apply S.cap = producer) :
    (Subst.seq (capOnly (bindings.toSubstWithin consumer.fcv)) S).Idempotent := by
  let C := bindings.toSubstWithin consumer.fcv
  apply Subst.seq_idempotent
  · exact Subst.idempotent_of_targetId (matchCap_subst_idempotent run)
  · intro target
    apply Subst.apply_eq_self_of_fixed
    · intro varId mem
      have mem' : varId ∈ (S.apply target).ftv := by
        simpa [capOnly, C, Subst.apply, Ty.applyTarget_id,
          Unification.Ty.ftv_applyCapability] using mem
      exact idem.image_target_fixed target varId mem'
    · intro varId mem
      have mem' : varId ∈ ((S.apply target).applyCapability C).fcv := by
        simpa [capOnly, C, Subst.apply, Ty.applyTarget_id] using mem
      rw [Unification.Ty.fcv_applyCapability] at mem'
      obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp mem'
      rcases matchCap_subst_range run source varId imageMem with equality | inProducer
      · subst varId
        exact idem.image_cap_fixed target source sourceMem
      · exact Cap.fixed_of_apply_self producer producerFixed varId inProducer

/-- One-way alignment preserves solved form when all four resolved components
are fixed at the checking cut. -/
private theorem oneWay_seq_idempotent_of_fixed
    {S delta : Subst} {producerCap : Cap} {producerTarget : Ty}
    {consumerCap : Cap} {consumerTarget : Ty}
    (idem : S.Idempotent)
    (oneWay : OneWayDelta producerCap producerTarget consumerCap
      consumerTarget delta)
    (producerCapFixed : producerCap.apply S.cap = producerCap)
    (producerTargetFixed : S.apply producerTarget = producerTarget)
    (consumerTargetFixed : S.apply consumerTarget = consumerTarget) :
    (Subst.seq delta S).Idempotent := by
  obtain ⟨bindings, run, capEquation, targetExact⟩ := oneWay
  let C := bindings.toSubstWithin consumerCap.fcv
  have capEquation' : delta.cap = C := capEquation
  rw [capEquation'] at targetExact
  have Pidem : (Subst.seq (capOnly C) S).Idempotent :=
    matchCap_seq_idempotent_of_fixed idem run producerCapFixed
  let P := Subst.seq (capOnly C) S
  have producerAtP : P.apply producerTarget =
      producerTarget.applyCapability C := by
    dsimp [P]
    rw [Subst.seq_apply, producerTargetFixed]
    simp [capOnly, Subst.apply, Ty.applyTarget_id]
  have consumerAtP : P.apply consumerTarget =
      consumerTarget.applyCapability C := by
    dsimp [P]
    rw [Subst.seq_apply, consumerTargetFixed]
    simp [capOnly, Subst.apply, Ty.applyTarget_id]
  have producerConstraintFixed :
      P.apply (producerTarget.applyCapability C) =
        producerTarget.applyCapability C := by
    have twice := Pidem producerTarget
    rwa [producerAtP] at twice
  have consumerConstraintFixed :
      P.apply (consumerTarget.applyCapability C) =
        consumerTarget.applyCapability C := by
    have twice := Pidem consumerTarget
    rwa [consumerAtP] at twice
  have targetStep :
      (Subst.seq (targetOnly delta.target) P).Idempotent :=
    exactTarget_seq_idempotent_of_fixed Pidem targetExact
      producerConstraintFixed consumerConstraintFixed
  have deltaPhases :
      Subst.seq (targetOnly delta.target) (capOnly C) = delta := by
    apply PhasedPost.subst_ext
    · funext varId
      simp [targetOnly, capOnly, Subst.seq, CapSubst.comp, Cap.apply_id,
        capEquation']
    · funext varId
      simp [targetOnly, capOnly, Subst.seq, Subst.apply,
        Ty.applyCapability_id, TySubst.id, Ty.applyTarget]
  rw [show Subst.seq (targetOnly delta.target) P = Subst.seq delta S by
    dsimp [P]
    rw [PhasedPost.seq_assoc, deltaPhases]] at targetStep
  exact targetStep

/-! ## Alignment families -/

/-- Ordinary type alignment preserves solved form. -/
theorem DDAlignTypes.idempotent
    {S : Subst} {left right : Ty} {S' : Subst}
    (aligned : DDAlignTypes S left right S') (idem : S.Idempotent) :
    S'.Idempotent := by
  cases aligned with
  | matcherPair hleft hright capExact targetExact =>
      rename_i leftCap rightCap leftTarget rightTarget C targetDelta
      have leftReapplied := idem left
      have rightReapplied := idem right
      rw [hleft] at leftReapplied
      rw [hright] at rightReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at leftReapplied rightReapplied
      obtain ⟨leftCapFixed, leftTargetFixed⟩ := Ty.matcher.inj leftReapplied
      obtain ⟨rightCapFixed, rightTargetFixed⟩ :=
        Ty.matcher.inj rightReapplied
      let P := Subst.seq (capOnly C) S
      have Pidem : P.Idempotent :=
        exactCap_seq_idempotent_of_fixed idem capExact leftCapFixed
          rightCapFixed
      have Pleft : P.apply left =
          .matcher (leftCap.apply C) (leftTarget.applyCapability C) := by
        dsimp [P]
        rw [Subst.seq_apply, hleft]
        simp [capOnly, Subst.apply, Ty.applyCapability,
          Ty.applyTarget_id]
      have Pright : P.apply right =
          .matcher (rightCap.apply C) (rightTarget.applyCapability C) := by
        dsimp [P]
        rw [Subst.seq_apply, hright]
        simp [capOnly, Subst.apply, Ty.applyCapability,
          Ty.applyTarget_id]
      have leftExactFixed := Pidem left
      have rightExactFixed := Pidem right
      rw [Pleft] at leftExactFixed
      rw [Pright] at rightExactFixed
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at leftExactFixed rightExactFixed
      have leftTargetExactFixed := (Ty.matcher.inj leftExactFixed).2
      have rightTargetExactFixed := (Ty.matcher.inj rightExactFixed).2
      exact exactPaired_seq_idempotent_of_fixed Pidem targetExact
        leftTargetExactFixed rightTargetExactFixed
  | slotPair hleft hright capExact targetExact =>
      rename_i leftCap rightCap leftTarget rightTarget C targetDelta
      have leftReapplied := idem left
      have rightReapplied := idem right
      rw [hleft] at leftReapplied
      rw [hright] at rightReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at leftReapplied rightReapplied
      obtain ⟨leftCapFixed, leftTargetFixed⟩ := Ty.slot.inj leftReapplied
      obtain ⟨rightCapFixed, rightTargetFixed⟩ := Ty.slot.inj rightReapplied
      let P := Subst.seq (capOnly C) S
      have Pidem : P.Idempotent :=
        exactCap_seq_idempotent_of_fixed idem capExact leftCapFixed
          rightCapFixed
      have Pleft : P.apply left =
          .slot (leftCap.apply C) (leftTarget.applyCapability C) := by
        dsimp [P]
        rw [Subst.seq_apply, hleft]
        simp [capOnly, Subst.apply, Ty.applyCapability,
          Ty.applyTarget_id]
      have Pright : P.apply right =
          .slot (rightCap.apply C) (rightTarget.applyCapability C) := by
        dsimp [P]
        rw [Subst.seq_apply, hright]
        simp [capOnly, Subst.apply, Ty.applyCapability,
          Ty.applyTarget_id]
      have leftExactFixed := Pidem left
      have rightExactFixed := Pidem right
      rw [Pleft] at leftExactFixed
      rw [Pright] at rightExactFixed
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at leftExactFixed rightExactFixed
      have leftTargetExactFixed := (Ty.slot.inj leftExactFixed).2
      have rightTargetExactFixed := (Ty.slot.inj rightExactFixed).2
      exact exactPaired_seq_idempotent_of_fixed Pidem targetExact
        leftTargetExactFixed rightTargetExactFixed
  | ordinary _ exact =>
      exact exact.seq_idempotent idem

/-- The complete checking-cut alignment preserves solved form. -/
theorem DDAlign.idempotent
    {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlign S raw expected S') (idem : S.Idempotent) :
    S'.Idempotent := by
  cases aligned with
  | productMatcherLift hduals hslot oneWay =>
      rename_i duals consumerCap consumerTarget delta
      have rawShape := Inference.productMatcherDuals?_sound hduals
      have producerCapFixed :
          (Cap.prod (duals.map Dual.cap)).apply S.cap =
            .prod (duals.map Dual.cap) := by
        apply Cap.apply_eq_self_of_fcv_fixed
        intro varId mem
        apply idem.image_cap_fixed raw varId
        rw [rawShape]
        simp only [Ty.fcv]
        obtain ⟨capability, capabilityMem, varMem⟩ :=
          Cap.mem_fcvList_split mem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp capabilityMem
        exact Ty.mem_fcvList_of_mem
          (List.mem_map.mpr ⟨dual, dualMem, rfl⟩)
          (List.mem_append.mpr (Or.inl varMem))
      have producerTargetFixed :
          S.apply (.prod (duals.map Dual.target)) =
            .prod (duals.map Dual.target) := by
        apply Subst.Idempotent.fixed_of_free_subset idem raw
        · intro varId mem
          rw [rawShape]
          simp only [Ty.ftv]
          obtain ⟨target, targetMem, varMem⟩ := Ty.mem_ftvList_split mem
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
          exact Ty.mem_ftvList_of_mem
            (List.mem_map.mpr ⟨dual, dualMem, rfl⟩) varMem
        · intro varId mem
          rw [rawShape]
          simp only [Ty.fcv]
          obtain ⟨target, targetMem, varMem⟩ := Ty.mem_fcvList_split mem
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
          exact Ty.mem_fcvList_of_mem
            (List.mem_map.mpr ⟨dual, dualMem, rfl⟩)
            (List.mem_append.mpr (Or.inr varMem))
      have expectedReapplied := idem expected
      rw [hslot] at expectedReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at expectedReapplied
      have consumerTargetFixed := (Ty.slot.inj expectedReapplied).2
      exact oneWay_seq_idempotent_of_fixed idem oneWay producerCapFixed
        producerTargetFixed consumerTargetFixed
  | slotTupleLift hclass hduals hslot capExact targetExact =>
      rename_i duals consumerCap consumerTarget C targetDelta
      have rawShape := Inference.productSlotDuals?_sound hduals
      have producerCapFixed :
          (Cap.prod (duals.map Dual.cap)).apply S.cap =
            .prod (duals.map Dual.cap) := by
        apply Cap.apply_eq_self_of_fcv_fixed
        intro varId mem
        apply idem.image_cap_fixed raw varId
        rw [rawShape]
        simp only [Ty.fcv]
        obtain ⟨capability, capabilityMem, varMem⟩ :=
          Cap.mem_fcvList_split mem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp capabilityMem
        exact Ty.mem_fcvList_of_mem
          (List.mem_map.mpr ⟨dual, dualMem, rfl⟩)
          (List.mem_append.mpr (Or.inl varMem))
      have producerTargetFixed :
          S.apply (.prod (duals.map Dual.target)) =
            .prod (duals.map Dual.target) := by
        apply Subst.Idempotent.fixed_of_free_subset idem raw
        · intro varId mem
          rw [rawShape]
          simp only [Ty.ftv]
          obtain ⟨target, targetMem, varMem⟩ := Ty.mem_ftvList_split mem
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
          exact Ty.mem_ftvList_of_mem
            (List.mem_map.mpr ⟨dual, dualMem, rfl⟩) varMem
        · intro varId mem
          rw [rawShape]
          simp only [Ty.fcv]
          obtain ⟨target, targetMem, varMem⟩ := Ty.mem_fcvList_split mem
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp targetMem
          exact Ty.mem_fcvList_of_mem
            (List.mem_map.mpr ⟨dual, dualMem, rfl⟩)
            (List.mem_append.mpr (Or.inr varMem))
      have expectedReapplied := idem expected
      rw [hslot] at expectedReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at expectedReapplied
      obtain ⟨consumerCapFixed, consumerTargetFixed⟩ :=
        Ty.slot.inj expectedReapplied
      exact twoPhase_seq_idempotent_of_fixed idem capExact targetExact
        producerCapFixed consumerCapFixed producerTargetFixed
        consumerTargetFixed
  | matcherToSlot hraw hslot oneWay =>
      rename_i producerCap producerTarget consumerCap consumerTarget delta
      have rawReapplied := idem raw
      have expectedReapplied := idem expected
      rw [hraw] at rawReapplied
      rw [hslot] at expectedReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at rawReapplied expectedReapplied
      obtain ⟨producerCapFixed, producerTargetFixed⟩ :=
        Ty.matcher.inj rawReapplied
      have consumerTargetFixed := (Ty.slot.inj expectedReapplied).2
      exact oneWay_seq_idempotent_of_fixed idem oneWay producerCapFixed
        producerTargetFixed consumerTargetFixed
  | slotToSlot hraw hslot capExact targetExact =>
      rename_i sourceCap sourceTarget requestedCap requestedTarget C targetDelta
      have rawReapplied := idem raw
      have expectedReapplied := idem expected
      rw [hraw] at rawReapplied
      rw [hslot] at expectedReapplied
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget] at rawReapplied expectedReapplied
      obtain ⟨sourceCapFixed, sourceTargetFixed⟩ :=
        Ty.slot.inj rawReapplied
      obtain ⟨requestedCapFixed, requestedTargetFixed⟩ :=
        Ty.slot.inj expectedReapplied
      exact twoPhase_seq_idempotent_of_fixed idem capExact targetExact
        sourceCapFixed requestedCapFixed sourceTargetFixed
        requestedTargetFixed
  | ordinary _ types =>
      exact DemandTypingIdempotence.DDAlignTypes.idempotent types idem

/-- Dual alignment preserves solved form. -/
theorem DDAlignDual.idempotent
    {S : Subst} {left right : Dual} {S' : Subst}
    (aligned : DDAlignDual S left right S') (idem : S.Idempotent) :
    S'.Idempotent := by
  cases aligned with
  | mk capExact targetAlign =>
      have capIdem := exactCap_seq_idempotent_of_fixed idem capExact
        (Subst.Idempotent.cap_apply_fixed idem left.cap)
        (Subst.Idempotent.cap_apply_fixed idem right.cap)
      exact DemandTypingIdempotence.DDAlignTypes.idempotent targetAlign capIdem

/-- Dual-list alignment preserves solved form. -/
theorem DDAlignDualList.idempotent
    {S : Subst} {left right : List Dual} {S' : Subst}
    (aligned : DDAlignDualList S left right S') (idem : S.Idempotent) :
    S'.Idempotent := by
  induction aligned with
  | nil => exact idem
  | cons head tail ih =>
      exact ih (DemandTypingIdempotence.DDAlignDual.idempotent head idem)

/-- Constructor-field target alignment preserves solved form. -/
theorem DDAlignTargetList.idempotent
    {S : Subst} {duals : List Dual} {targets : List Ty} {S' : Subst}
    (aligned : DDAlignTargetList S duals targets S')
    (idem : S.Idempotent) : S'.Idempotent := by
  induction aligned with
  | nil => exact idem
  | cons head tail ih =>
      exact ih (DemandTypingIdempotence.DDAlignTypes.idempotent head idem)

/-- Or-alternative binding alignment preserves solved form. -/
theorem DDAlignBindings.idempotent
    {S : Subst} {left right : MonoCtx} {S' : Subst}
    (aligned : DDAlignBindings S left right S') (idem : S.Idempotent) :
    S'.Idempotent := by
  induction aligned with
  | nil => exact idem
  | cons _ head tail ih =>
      exact ih (DemandTypingIdempotence.DDAlignTypes.idempotent head idem)

/-- Pattern-constructor capability alignment preserves solved form. -/
theorem DDAlignCtorCaps.idempotent
    {S : Subst} {children : List Cap} {demands : List (Option Cap)}
    {S' : Subst} (aligned : DDAlignCtorCaps S children demands S')
    (idem : S.Idempotent) : S'.Idempotent := by
  induction aligned with
  | nil => exact idem
  | skip tail ih => exact ih idem
  | solve capExact tail ih =>
      rename_i child expected children demands C S'
      have capIdem := exactCap_seq_idempotent_of_fixed idem capExact
        (Subst.Idempotent.cap_apply_fixed idem child)
        (Subst.Idempotent.cap_apply_fixed idem expected)
      exact ih capIdem

/-- Pattern-constructor capability inference preserves solved form. -/
theorem DDPatternCtorCap.idempotent
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {children : List Cap} {capability : Cap}
    (typing : DDPatternCtorCap signature entry q S children capability q' S')
    (idem : S.Idempotent) : S'.Idempotent := by
  cases typing with
  | project _ _ => exact idem
  | fallback _ _ _ aligned _ _ =>
      exact DemandTypingIdempotence.DDAlignCtorCaps.idempotent aligned idem

/-! ## Raw DD families -/

mutual

/-- Data-pattern checking preserves solved form. -/
theorem DDDPat.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    (typing : DDDPat signature q S pattern expected bindings q' S')
    (idem : S.Idempotent) : S'.Idempotent := by
  cases typing with
  | var => exact idem
  | wild => exact idem
  | ctor _ aligned children =>
      exact DDDPats.idempotent children
        (DemandTypingIdempotence.DDAlignTypes.idempotent aligned idem)
  | tuple aligned children =>
      exact DDDPats.idempotent children
        (DemandTypingIdempotence.DDAlignTypes.idempotent aligned idem)

/-- Data-pattern list checking preserves solved form. -/
theorem DDDPats.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {patterns : List DPat} {targets : List Ty}
    {bindings : MonoCtx}
    (typing : DDDPats signature q S patterns targets bindings q' S')
    (idem : S.Idempotent) : S'.Idempotent := by
  cases typing with
  | nil => exact idem
  | cons head tail _ =>
      exact DDDPats.idempotent tail (DDDPat.idempotent head idem)

end

mutual

/-- Primitive-pattern checking preserves solved form. -/
theorem DDPPat.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : DDPPat signature q S pattern expected holes bindings q' S')
    (idem : S.Idempotent) : S'.Idempotent := by
  cases typing with
  | hole => exact idem
  | wild => exact idem
  | pval => exact idem
  | ctor _ aligned children =>
      exact DDPPats.idempotent children
        (DemandTypingIdempotence.DDAlignTypes.idempotent aligned idem)
  | tuple aligned children =>
      exact DDPPats.idempotent children
        (DemandTypingIdempotence.DDAlignTypes.idempotent aligned idem)

/-- Primitive-pattern list checking preserves solved form. -/
theorem DDPPats.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {patterns : List PPat} {targets : List Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (typing : DDPPats signature q S patterns targets holes bindings q' S')
    (idem : S.Idempotent) : S'.Idempotent := by
  cases typing with
  | nil => exact idem
  | cons head tail _ =>
      exact DDPPats.idempotent tail (DDPPat.idempotent head idem)

end

mutual

/-- Expression synthesis preserves solved form. -/
theorem DDSynth.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {expression : Expr} {target : Ty}
    (typing : DDSynth signature q S context expression target q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .var _ => idem
  | .lam body => DDSynth.idempotent body idem
  | .fix _ _ _ body aligned =>
      DemandTypingIdempotence.DDAlignTypes.idempotent aligned
        (DDSynth.idempotent body idem)
  | .app function aligned argument => by
      have afterFunction := DDSynth.idempotent function idem
      have afterAlign :=
        DemandTypingIdempotence.DDAlignTypes.idempotent aligned afterFunction
      exact DDCheck.idempotent argument afterAlign
  | .lit => idem
  | .tuple children => DDSynths.idempotent children idem
  | .ctor _ children => DDChecks.idempotent children idem
  | .prim _ children => DDChecks.idempotent children idem
  | .letE value body =>
      DDSynth.idempotent body (DDSynth.idempotent value idem)
  | .something => idem
  | .matcher clauses _ _ _ _ _ _ _ => DDClauses.idempotent clauses idem
  | .matchAll target pattern aligned matcher body => by
      have afterTarget := DDSynth.idempotent target idem
      have afterPattern := DDPattern.idempotent pattern afterTarget
      have afterAlign :=
        DemandTypingIdempotence.DDAlignTypes.idempotent aligned afterPattern
      have afterMatcher := DDCheck.idempotent matcher afterAlign
      exact DDSynth.idempotent body afterMatcher
  | .fixMatcher _ _ _ body aligned =>
      DemandTypingIdempotence.DDAlignTypes.idempotent aligned
        (DDSynth.idempotent body idem)

/-- Expression-list synthesis preserves solved form. -/
theorem DDSynths.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {expressions : List Expr}
    {targets : List Ty}
    (typing : DDSynths signature q S context expressions targets q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .nil => idem
  | .cons head tail =>
      DDSynths.idempotent tail (DDSynth.idempotent head idem)

/-- Expression checking preserves solved form. -/
theorem DDCheck.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {expression : Expr} {expected : Ty}
    (typing : DDCheck signature q S context expression expected q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .mk synth aligned =>
      DemandTypingIdempotence.DDAlign.idempotent aligned
        (DDSynth.idempotent synth idem)

/-- Expression-list checking preserves solved form. -/
theorem DDChecks.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {expressions : List Expr}
    {expecteds : List Ty}
    (typing : DDChecks signature q S context expressions expecteds q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .nil => idem
  | .cons head tail =>
      DDChecks.idempotent tail (DDCheck.idempotent head idem)

/-- User-pattern synthesis preserves solved form. -/
theorem DDPattern.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {parameters : PatternCtx}
    {bindings bindings' : MonoCtx} {pattern : Pattern} {dual : Dual}
    (typing : DDPattern signature q S context parameters bindings pattern
      dual bindings' q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .pvar _ => idem
  | .wild => idem
  | .pval expression => DDSynth.idempotent expression idem
  | .embed _ => idem
  | .ptuple patterns => DDPatterns.idempotent patterns idem
  | .pctor _ patterns targets capability _ => by
      have afterPatterns := DDPatterns.idempotent patterns idem
      have afterTargets :=
        DemandTypingIdempotence.DDAlignTargetList.idempotent targets
          afterPatterns
      exact DemandTypingIdempotence.DDPatternCtorCap.idempotent capability
        afterTargets
  | .pand left right aligned => by
      have afterLeft := DDPattern.idempotent left idem
      have afterRight := DDPattern.idempotent right afterLeft
      exact DemandTypingIdempotence.DDAlignDual.idempotent aligned afterRight
  | .por left right aligned bindings => by
      have afterLeft := DDPattern.idempotent left idem
      have afterRight := DDPattern.idempotent right afterLeft
      have afterDual :=
        DemandTypingIdempotence.DDAlignDual.idempotent aligned afterRight
      exact DemandTypingIdempotence.DDAlignBindings.idempotent bindings
        afterDual
  | .papp _ patterns aligned =>
      DemandTypingIdempotence.DDAlignDualList.idempotent aligned
        (DDPatterns.idempotent patterns idem)

/-- User-pattern-list synthesis preserves solved form. -/
theorem DDPatterns.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {parameters : PatternCtx}
    {bindings bindings' : MonoCtx} {patterns : List Pattern}
    {duals : List Dual}
    (typing : DDPatterns signature q S context parameters bindings patterns
      duals bindings' q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .nil => idem
  | .cons head tail =>
      DDPatterns.idempotent tail (DDPattern.idempotent head idem)

/-- Matcher-arm checking preserves solved form. -/
theorem DDArms.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {bindings : MonoCtx}
    {arms : List Arm} {clauseTarget bodyTarget : Ty}
    (typing : DDArms signature q S context bindings arms clauseTarget
      bodyTarget q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .nil => idem
  | .cons pattern _ body tail => by
      have afterPattern := DDDPat.idempotent pattern idem
      have afterBody := DDCheck.idempotent body afterPattern
      exact DDArms.idempotent tail afterBody

/-- Matcher-clause checking preserves solved form. -/
theorem DDClause.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {clause : Clause}
    {sharedTarget : Ty} {holes : List Dual}
    (typing : DDClause signature q S context clause sharedTarget holes q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .mk pattern _ next arms => by
      have afterPattern := DDPPat.idempotent pattern idem
      have afterNext := DDChecks.idempotent next afterPattern
      exact DDArms.idempotent arms afterNext

/-- Matcher-clause-list checking preserves solved form. -/
theorem DDClauses.idempotent
    {signature : FrozenSig} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {context : Context} {clauses : List Clause}
    {sharedTarget : Ty} {holeLists : List (List Dual)}
    (typing : DDClauses signature q S context clauses sharedTarget holeLists
      q' S')
    (idem : S.Idempotent) : S'.Idempotent :=
  match typing with
  | .nil => idem
  | .cons head tail =>
      DDClauses.idempotent tail (DDClause.idempotent head idem)

end

end DemandTypingIdempotence

end TypePM
