import TypePM.DemandTypingInferenceCompletenessLocalRenaming
import TypePM.DemandTypingInferenceCompletenessOneWayCapability

/-!
# Target-phase transport for heterogeneous one-way cuts

After the capability matcher has run, the dedicated producer-to-slot solver
uses the ordinary target unifier on the two capability-adjusted targets.  A
demand-directed target solution need not itself be an executable target solution: the two
states may use different representatives of their still-free metavariables.

The theorem below conjugates the demand-directed target solution by the scoped renaming
between those representatives.  The reverse residual cancels the forward
residual on every capability variable occurring in the executable adjusted
targets.  Consequently the conjugate has identity capability action on the
constraint, and its target component is an ordinary target-only unifier.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessOneWayTarget

open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessOneWayCapability

private theorem applyCapability_eq_of_fcv_agree
    (left right : CapSubst) (target : Ty)
    (agree : ∀ varId, varId ∈ target.fcv →
      left varId = right varId) :
    target.applyCapability left = target.applyCapability right := by
  have paired := Subst.apply_eq_of_free_agree
    (Subst.mk left TySubst.id) (Subst.mk right TySubst.id) target
      agree (fun _ _ => rfl)
  simpa only [Subst.apply, Ty.applyTarget_id] using paired

/-- Capability matching is conjugate under a scoped ambient renaming.

On variables occurring in the executable consumer this follows from
uniqueness of `DemandMatches`.  Away from the consumer, both matcher
substitutions are identities; injectivity of the scoped renaming ensures that
an outside variable cannot be renamed into the demand-directed consumer support. -/
theorem oneWay_capConjugacy_on
    {forward reverse : Subst}
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {declarativeProducer executableProducer : Cap}
    {declarativeConsumer executableConsumer : Cap}
    (producerForward : declarativeProducer =
      executableProducer.apply forward.cap)
    (producerReverse : executableProducer =
      declarativeProducer.apply reverse.cap)
    (consumerForward : declarativeConsumer =
      executableConsumer.apply forward.cap)
    (consumerReverse : executableConsumer =
      declarativeConsumer.apply reverse.cap)
    {ddCap executableCap : CapSubst}
    (dd : OneWayAt ddCap declarativeProducer declarativeConsumer)
    (executable : OneWayAt executableCap executableProducer
      executableConsumer)
    (consumerCaps : ∀ varId, varId ∈ executableConsumer.fcv →
      varId ∈ capScope)
    {varId : CapVar} (varInScope : varId ∈ capScope) :
    ((forward.cap varId).apply ddCap).apply reverse.cap =
      executableCap varId := by
  by_cases inConsumer : varId ∈ executableConsumer.fcv
  · let later := CapSubst.comp ddCap forward.cap
    have transported : DemandMatches later
        (executableProducer.apply later) executableConsumer :=
      oneWayAt_forward_postDemand producerForward consumerForward
        consumerReverse dd
    have reflected := demandMatches_comp reverse.cap later transported
    have producerStable :
        (executableProducer.apply later).apply reverse.cap =
          executableProducer := by
      change
        (executableProducer.apply
          (CapSubst.comp ddCap forward.cap)).apply reverse.cap =
            executableProducer
      rw [Cap.apply_comp, ← producerForward, dd.2.1, ← producerReverse]
    rw [producerStable] at reflected
    exact demandMatches_unique_on_consumer
      (CapSubst.comp reverse.cap later) executableCap executableProducer
        executableConsumer reflected executable.2.2 varId inConsumer
  · have imageNotInDeclarative :
        certificate.capImage varId ∉ declarativeConsumer.fcv := by
      intro imageMember
      rw [consumerForward, Unification.Cap.fcv_apply] at imageMember
      rcases List.mem_flatMap.mp imageMember with
        ⟨source, sourceMember, imageMember⟩
      have sourceInScope := consumerCaps source sourceMember
      rw [certificate.cap_forward sourceInScope] at imageMember
      have equalImages : certificate.capImage source =
          certificate.capImage varId := by
        have backwards : certificate.capImage varId =
            certificate.capImage source := by
          simpa only [Cap.fcv, List.mem_singleton] using imageMember
        exact backwards.symm
      have sourceEq : source = varId :=
        certificate.capImage_injectiveOn sourceInScope varInScope equalImages
      exact inConsumer (sourceEq ▸ sourceMember)
    rw [certificate.cap_forward varInScope]
    simp only [Cap.apply]
    rw [
      dd.1 (certificate.capImage varId) imageNotInDeclarative]
    simp only [Cap.apply]
    rw [certificate.cap_reverse varInScope]
    exact (executable.1 varId inConsumer).symm

/-- Bundle form of `oneWay_capConjugacy_on`, ready for the two executable raw
targets of a producer-to-slot cut. -/
theorem oneWay_capConjugacy_on_targets
    {forward reverse : Subst}
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {declarativeProducer executableProducer : Cap}
    {declarativeConsumer executableConsumer : Cap}
    (producerForward : declarativeProducer =
      executableProducer.apply forward.cap)
    (producerReverse : executableProducer =
      declarativeProducer.apply reverse.cap)
    (consumerForward : declarativeConsumer =
      executableConsumer.apply forward.cap)
    (consumerReverse : executableConsumer =
      declarativeConsumer.apply reverse.cap)
    {ddCap executableCap : CapSubst}
    (dd : OneWayAt ddCap declarativeProducer declarativeConsumer)
    (executable : OneWayAt executableCap executableProducer
      executableConsumer)
    (consumerCaps : ∀ varId, varId ∈ executableConsumer.fcv →
      varId ∈ capScope)
    {producerTarget consumerTarget : Ty}
    (targetCaps : ∀ varId,
      varId ∈ producerTarget.fcv ++ consumerTarget.fcv →
        varId ∈ capScope) :
    ∀ varId, varId ∈ producerTarget.fcv ++ consumerTarget.fcv →
      ((forward.cap varId).apply ddCap).apply reverse.cap =
        executableCap varId := by
  intro varId member
  exact oneWay_capConjugacy_on certificate producerForward producerReverse
    consumerForward consumerReverse dd executable consumerCaps
      (targetCaps varId member)

/-- The paired conjugate used to reflect a demand-directed target solution back to the
executable representative. -/
def targetConjugate (forward reverse : Subst) (ddTarget : TySubst) : Subst :=
  Subst.seq reverse
    (Subst.seq (Subst.mk CapSubst.id ddTarget) forward)

/-- Conjugate for the complete one-way target phase.  The demand-directed capability
match is inserted before its target solve; the reverse ambient renaming then
returns the result to the executable representative. -/
def oneWayTargetConjugate (forward reverse : Subst)
    (ddCap : CapSubst) (ddTarget : TySubst) : Subst :=
  Subst.seq reverse
    (Subst.seq (Subst.mk CapSubst.id ddTarget)
      (Subst.seq (Subst.mk ddCap TySubst.id) forward))

/-- A target constraint related to a demand-directed constraint by a scoped variable
renaming is unifiable whenever the demand-directed constraint is target-unifiable.

Only capability variables of the executable constraint must lie in the
certified scope.  Target variables introduced by the demand-directed unifier are handled
by the target component of the conjugate and need no inverse-side scope
premise. -/
theorem mguTy_complete_of_forward_renaming
    {forward reverse : Subst}
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {declarativeLeft declarativeRight : Ty}
    {executableLeft executableRight : Ty}
    (leftForward : declarativeLeft = forward.apply executableLeft)
    (rightForward : declarativeRight = forward.apply executableRight)
    (leftCaps : ∀ varId, varId ∈ executableLeft.fcv →
      varId ∈ capScope)
    (rightCaps : ∀ varId, varId ∈ executableRight.fcv →
      varId ∈ capScope)
    {ddTarget : TySubst}
    (ddUnifies : declarativeLeft.applyTarget ddTarget =
      declarativeRight.applyTarget ddTarget) :
    ∃ executableTarget,
      Unification.mguTy executableLeft executableRight =
        some executableTarget := by
  let conjugate := targetConjugate forward reverse ddTarget
  have capFixed : ∀ varId ∈ executableLeft.fcv ++ executableRight.fcv,
      conjugate.cap varId = .var varId := by
    intro varId member
    have inScope : varId ∈ capScope := by
      rcases List.mem_append.mp member with leftMem | rightMem
      · exact leftCaps varId leftMem
      · exact rightCaps varId rightMem
    have forwardPoint := certificate.cap_forward inScope
    have reversePoint := certificate.cap_reverse inScope
    change
      (((forward.cap varId).apply CapSubst.id).apply reverse.cap) =
        .var varId
    rw [Cap.apply_id, forwardPoint]
    simpa only [Cap.apply] using reversePoint
  have leftCapFixed : executableLeft.applyCapability conjugate.cap =
      executableLeft := by
    apply Ty.applyCapability_eq_self_of_fcv_fixed
    intro varId member
    exact capFixed varId (List.mem_append_left _ member)
  have rightCapFixed : executableRight.applyCapability conjugate.cap =
      executableRight := by
    apply Ty.applyCapability_eq_self_of_fcv_fixed
    intro varId member
    exact capFixed varId (List.mem_append_right _ member)
  have pairedUnifies : conjugate.apply executableLeft =
      conjugate.apply executableRight := by
    simp only [conjugate, targetConjugate, Subst.seq_apply]
    rw [← leftForward, ← rightForward]
    simp only [Subst.apply, Ty.applyCapability_id]
    exact congrArg reverse.apply ddUnifies
  have targetUnifies : executableLeft.applyTarget conjugate.target =
      executableRight.applyTarget conjugate.target := by
    simpa only [Subst.apply, leftCapFixed, rightCapFixed] using pairedUnifies
  exact Unification.mguTy_complete targetUnifies

/-- Convenient exact-MGU form used by the one-way demand-directed rule. -/
theorem mguTy_complete_of_exactTargetMGU_forward_renaming
    {forward reverse : Subst}
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {declarativeLeft declarativeRight : Ty}
    {executableLeft executableRight : Ty}
    (leftForward : declarativeLeft = forward.apply executableLeft)
    (rightForward : declarativeRight = forward.apply executableRight)
    (leftCaps : ∀ varId, varId ∈ executableLeft.fcv →
      varId ∈ capScope)
    (rightCaps : ∀ varId, varId ∈ executableRight.fcv →
      varId ∈ capScope)
    {ddTarget : TySubst}
    (dd : ExactTargetMGU declarativeLeft declarativeRight ddTarget) :
    ∃ executableTarget,
      Unification.mguTy executableLeft executableRight =
        some executableTarget :=
  mguTy_complete_of_forward_renaming certificate leftForward rightForward
    leftCaps rightCaps dd.1.1

/-- One-way-cut form of target success transport.

`capConjugacy` is the capability-phase correspondence left after transporting
the executable `matchCap` result: ambient forward renaming, the demand-directed capability
match, and ambient reverse renaming agree with the executable capability
match on every capability variable occurring in the two raw executable
targets.  Under exactly that local equation, the demand-directed target MGU supplies a
target-only unifier for the executable capability-adjusted targets.

The premise is deliberately pointwise on the finite target scope.  Callers
may establish it from a global cap-delta factorization, or directly from the
scoped `matchCap` covariance proof, without requiring equality of the two
binding substitutions outside the cut. -/
theorem mguTy_complete_of_oneWay_capConjugacy
    {forward reverse : Subst}
    {declarativeProducerTarget declarativeConsumerTarget : Ty}
    {executableProducerTarget executableConsumerTarget : Ty}
    (producerForward : declarativeProducerTarget =
      forward.apply executableProducerTarget)
    (consumerForward : declarativeConsumerTarget =
      forward.apply executableConsumerTarget)
    {ddCap executableCap : CapSubst} {ddTarget : TySubst}
    (capConjugacy : ∀ varId,
      varId ∈ executableProducerTarget.fcv ++ executableConsumerTarget.fcv →
      ((forward.cap varId).apply ddCap).apply reverse.cap =
        executableCap varId)
    (dd : ExactTargetMGU
      (declarativeProducerTarget.applyCapability ddCap)
      (declarativeConsumerTarget.applyCapability ddCap) ddTarget) :
    ∃ executableTarget,
      Unification.mguTy
        (executableProducerTarget.applyCapability executableCap)
        (executableConsumerTarget.applyCapability executableCap) =
          some executableTarget := by
  let conjugate := oneWayTargetConjugate forward reverse ddCap ddTarget
  have producerCaps :
      executableProducerTarget.applyCapability conjugate.cap =
        executableProducerTarget.applyCapability executableCap := by
    apply applyCapability_eq_of_fcv_agree
    intro varId member
    change
      (((forward.cap varId).apply ddCap).apply CapSubst.id).apply reverse.cap =
        executableCap varId
    rw [Cap.apply_id]
    exact capConjugacy varId (List.mem_append_left _ member)
  have consumerCaps :
      executableConsumerTarget.applyCapability conjugate.cap =
        executableConsumerTarget.applyCapability executableCap := by
    apply applyCapability_eq_of_fcv_agree
    intro varId member
    change
      (((forward.cap varId).apply ddCap).apply CapSubst.id).apply reverse.cap =
        executableCap varId
    rw [Cap.apply_id]
    exact capConjugacy varId (List.mem_append_right _ member)
  have pairedUnifies : conjugate.apply executableProducerTarget =
      conjugate.apply executableConsumerTarget := by
    simp only [conjugate, oneWayTargetConjugate, Subst.seq_apply]
    rw [← producerForward, ← consumerForward]
    simp only [Subst.apply, Ty.applyCapability_id, Ty.applyTarget_id]
    exact congrArg reverse.apply dd.1.1
  have targetUnifies :
      (executableProducerTarget.applyCapability executableCap).applyTarget
          conjugate.target =
        (executableConsumerTarget.applyCapability executableCap).applyTarget
          conjugate.target := by
    simpa only [Subst.apply, producerCaps, consumerCaps] using pairedUnifies
  exact Unification.mguTy_complete targetUnifies

/-- Global capability-equation wrapper for
`mguTy_complete_of_oneWay_capConjugacy`. -/
theorem mguTy_complete_of_oneWay_capEquation
    {forward reverse : Subst}
    {declarativeProducerTarget declarativeConsumerTarget : Ty}
    {executableProducerTarget executableConsumerTarget : Ty}
    (producerForward : declarativeProducerTarget =
      forward.apply executableProducerTarget)
    (consumerForward : declarativeConsumerTarget =
      forward.apply executableConsumerTarget)
    {ddCap executableCap : CapSubst} {ddTarget : TySubst}
    (capEquation :
      CapSubst.comp reverse.cap (CapSubst.comp ddCap forward.cap) =
        executableCap)
    (dd : ExactTargetMGU
      (declarativeProducerTarget.applyCapability ddCap)
      (declarativeConsumerTarget.applyCapability ddCap) ddTarget) :
    ∃ executableTarget,
      Unification.mguTy
        (executableProducerTarget.applyCapability executableCap)
        (executableConsumerTarget.applyCapability executableCap) =
          some executableTarget := by
  apply mguTy_complete_of_oneWay_capConjugacy producerForward consumerForward
    (dd := dd)
  intro varId _member
  exact congrFun capEquation varId

end DemandTypingInferenceCompletenessOneWayTarget
end TypePM
