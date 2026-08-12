import TypePM.DemandTypingInferenceCompletenessSolver

/-!
# Dedicated producer-to-slot solver completeness

The one-way branch has no capability-orientation ambiguity: `OneWayDelta`
already records the exact `CapMatch` bindings used by the executable solver.
Only the target MGU may choose a different solved orientation.  We retain
that difference as mutual target-substitution factorization rather than
requiring literal equality of the emitted and demand-directed deltas.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessOneWay

open Inference

/-- Semantic admissibility makes the finite executable origin check succeed
on every chosen support list.  Variables outside the list are irrelevant to
this direction; unlike `check_sound`, no support certificate is needed. -/
theorem admissibleCapPostCheck_complete
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (admissible : AdmissibleCapPost ledger post)
    (supportVars : List CapVar) :
    admissibleCapPostCheck ledger post supportVars = true := by
  apply List.all_eq_true.mpr
  intro varId _membership
  have point := admissible varId
  cases origin : ledger.originOf varId with
  | rigid =>
      rw [origin] at point
      simp [point]
  | renameOnly =>
      rw [origin] at point
      rcases point with ⟨image, imageEq, imageSafe⟩
      simp [imageEq, imageSafe]
  | structuralFlexible =>
      simp

/-- Correspondence between a demand-directed one-way witness and the concrete solver step.
The capability components coincide.  The target components are mutually MGU
instances, which is the strongest unconditional relationship in the presence
of opposite variable orientations. -/
structure OneWaySolverCorrespondence
    (declarative : Subst) (step : SolveStep) : Prop where
  capabilityEq : step.delta.cap = declarative.cap
  declarativeTargetFactorsThroughExecutable :
    ∃ residual : TySubst,
      declarative.target = TySubst.comp residual step.delta.target
  executableTargetFactorsThroughDeclarative :
    ∃ residual : TySubst,
      step.delta.target = TySubst.comp residual declarative.target

/-- The target-factorization residual lifts to an exact paired-state triangle.
It has identity capability action, so it cannot disturb the capability match
already fixed by `CapMatch`. -/
theorem OneWaySolverCorrespondence.declarative_delta_factorization
    {declarative : Subst} {step : SolveStep}
    (correspondence : OneWaySolverCorrespondence declarative step) :
    ∃ residualTarget : TySubst,
      declarative = Subst.seq
        (Subst.mk CapSubst.id residualTarget) step.delta := by
  rcases correspondence.declarativeTargetFactorsThroughExecutable with
    ⟨residualTarget, targetEq⟩
  refine ⟨residualTarget, ?_⟩
  apply PhasedPost.subst_ext
  · rw [← correspondence.capabilityEq]
    funext varId
    exact (Cap.apply_id (step.delta.cap varId)).symm
  · funext varId
    change declarative.target varId =
      ((step.delta.target varId).applyCapability CapSubst.id).applyTarget
        residualTarget
    rw [Ty.applyCapability_id]
    exact congrFun targetEq varId

/-- Running the executable dedicated solver succeeds for every origin-safe demand-directed
one-way witness, at every trace count and source origin. -/
theorem solveProducerToSlotWithLedger_complete
    {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {declarative : Subst}
    (dd : OriginSafeOneWayDelta ledger producerCap producerTarget
      consumerCap consumerTarget declarative)
    (solveCount : Nat) (origin : ConstraintOrigin) :
    ∃ step,
      solveProducerToSlotWithLedger ledger solveCount origin producerCap
        producerTarget consumerCap consumerTarget = some step ∧
      OneWaySolverCorrespondence declarative step := by
  rcases dd.exact with ⟨bindings, matchSuccess, capabilityEq, targetExact⟩
  let capabilitySubst := bindings.toSubstWithin consumerCap.fcv
  have capabilityAdmissible : AdmissibleCapPost ledger capabilitySubst := by
    change AdmissibleCapPost ledger
      (bindings.toSubstWithin consumerCap.fcv)
    rw [← capabilityEq]
    exact dd.admissible.cap
  have checked : admissibleCapPostCheck ledger capabilitySubst
      consumerCap.fcv = true :=
    admissibleCapPostCheck_complete capabilityAdmissible consumerCap.fcv
  obtain ⟨executableTarget, targetSuccess⟩ :=
    Unification.mguTy_complete targetExact.1.1
  have targetSuccess' : Unification.mguTy
      (producerTarget.applyCapability capabilitySubst)
      (consumerTarget.applyCapability capabilitySubst) =
        some executableTarget := by
    change Unification.mguTy
      (producerTarget.applyCapability
        (bindings.toSubstWithin consumerCap.fcv))
      (consumerTarget.applyCapability
        (bindings.toSubstWithin consumerCap.fcv)) = some executableTarget
    rw [← capabilityEq]
    exact targetSuccess
  have forward := Unification.mguTy_universal targetSuccess targetExact.1.1
  have reverse := targetExact.1.2 executableTarget
    (Unification.mguTy_sound targetSuccess)
  let step : SolveStep := {
    solveCount := solveCount
    origin := origin
    ledgerSnapshot := ledger
    constraint := .producerToSlot producerCap producerTarget consumerCap
      consumerTarget
    delta := ⟨capabilitySubst, executableTarget⟩
    targetDomain := Unification.mguTySupport
      (producerTarget.applyCapability capabilitySubst)
      (consumerTarget.applyCapability capabilitySubst)
    targetSupport := Unification.mguTy_support targetSuccess'
    certificate := .producerToSlot matchSuccess targetSuccess'
    locallySound := ⟨CapMatch.matchCap_restricted_sound matchSuccess,
      Unification.mguTy_sound targetSuccess'⟩
  }
  refine ⟨step, ?_, ?_⟩
  · unfold solveProducerToSlotWithLedger
    split
    · rename_i noMatch
      rw [matchSuccess] at noMatch
      contradiction
    · rename_i found foundMatch
      have foundEq : found = bindings := by
        rw [matchSuccess] at foundMatch
        exact (Option.some.inj foundMatch).symm
      subst found
      dsimp only
      rw [checked]
      simp only [↓reduceIte]
      split
      · rename_i noTarget
        rw [targetSuccess'] at noTarget
        contradiction
      · rename_i foundTarget foundTargetSuccess
        have targetEq : foundTarget = executableTarget := by
          rw [targetSuccess'] at foundTargetSuccess
          exact (Option.some.inj foundTargetSuccess).symm
        subst foundTarget
        rfl
  · refine ⟨?_, ?_, ?_⟩
    · exact capabilityEq.symm
    · exact forward
    · exact reverse

end DemandTypingInferenceCompletenessOneWay
end TypePM
