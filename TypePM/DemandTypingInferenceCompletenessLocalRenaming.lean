import TypePM.DemandTypingInferenceCompletenessStateMutual

/-!
# Scoped renaming extracted from mutual state factorization

Mutual first-order instances need not be global renamings: either prevailing
substitution may already have eliminated variables that are irrelevant to the
normalized types under consideration.  On variables fixed by one prevailing
state, however, the two residuals are pointwise inverse variable renamings.
This module records exactly that finite, two-sorted consequence.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessLocalRenaming

open Inference
open DemandTypingInferenceCompletenessStateMutual

/-- `forward` is a variable renaming on the indicated finite scopes and
`reverse` is its pointwise inverse there.  No claim is made about variables
outside the scopes. -/
structure LocalRenamingOn (forward reverse : Subst)
    (capScope : List CapVar) (targetScope : List TypePM.TyVar) : Prop where
  cap : ∀ varId ∈ capScope, ∃ image,
    forward.cap varId = .var image ∧
      reverse.cap image = .var varId
  target : ∀ varId ∈ targetScope, ∃ image,
    forward.target varId = .var image ∧
      reverse.target image = .var varId

/-- Restrict a local renaming certificate to smaller scopes. -/
theorem LocalRenamingOn.mono
    {forward reverse : Subst}
    {largeCaps smallCaps : List CapVar}
    {largeTargets smallTargets : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse largeCaps largeTargets)
    (caps : ∀ varId, varId ∈ smallCaps → varId ∈ largeCaps)
    (targets : ∀ varId, varId ∈ smallTargets → varId ∈ largeTargets) :
    LocalRenamingOn forward reverse smallCaps smallTargets := by
  exact ⟨fun varId member => certificate.cap varId (caps varId member),
    fun varId member => certificate.target varId (targets varId member)⟩

/-- The two residuals in a mutual factorization are inverse variable
renamings on every variable fixed by the right-hand prevailing substitution.

This is the reusable algebraic core.  It deliberately asks for fixedness only
on the finite scopes being transported; idempotence supplies these premises
for variables occurring in normalized images. -/
theorem localRenamingOn_of_mutualFactorization
    {left right forward reverse : Subst}
    (forwardEquation : left = Subst.seq forward right)
    (reverseEquation : right = Subst.seq reverse left)
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (capsFixed : ∀ varId ∈ capScope, right.cap varId = .var varId)
    (targetsFixed : ∀ varId ∈ targetScope,
      right.target varId = .var varId) :
    LocalRenamingOn forward reverse capScope targetScope := by
  constructor
  · intro varId member
    have forwardAt := congrArg (fun substitution : Subst =>
      substitution.cap varId) forwardEquation
    have reverseAt := congrArg (fun substitution : Subst =>
      substitution.cap varId) reverseEquation
    change left.cap varId = (right.cap varId).apply forward.cap at forwardAt
    change right.cap varId = (left.cap varId).apply reverse.cap at reverseAt
    rw [capsFixed varId member] at forwardAt reverseAt
    change left.cap varId = forward.cap varId at forwardAt
    rw [forwardAt] at reverseAt
    cases imageEq : forward.cap varId with
    | var image =>
        refine ⟨image, rfl, ?_⟩
        rw [imageEq] at reverseAt
        simpa only [Cap.apply] using reverseAt.symm
    | any => rw [imageEq] at reverseAt; cases reverseAt
    | skolem index => rw [imageEq] at reverseAt; cases reverseAt
    | con name capabilities => rw [imageEq] at reverseAt; cases reverseAt
    | prod capabilities => rw [imageEq] at reverseAt; cases reverseAt
  · intro varId member
    have forwardAt := congrArg (fun substitution : Subst =>
      substitution.apply (.var varId)) forwardEquation
    have reverseAt := congrArg (fun substitution : Subst =>
      substitution.apply (.var varId)) reverseEquation
    have rightFixed : right.apply (.var varId) = .var varId := by
      exact targetsFixed varId member
    rw [Subst.seq_apply, rightFixed] at forwardAt
    rw [Subst.seq_apply, rightFixed] at reverseAt
    rw [forwardAt] at reverseAt
    change Ty.var varId = reverse.apply (forward.target varId) at reverseAt
    cases imageEq : forward.target varId with
    | var image =>
        refine ⟨image, rfl, ?_⟩
        rw [imageEq] at reverseAt
        simpa only [Subst.apply, Ty.applyCapability, Ty.applyTarget] using
          reverseAt.symm
    | skolem index =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | unit =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | int =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | bool =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | data name targets =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | prod targets =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | fn domain codomain =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | matcher capability target =>
        rw [imageEq] at reverseAt
        cases reverseAt
    | slot capability target =>
        rw [imageEq] at reverseAt
        cases reverseAt

/-- State-level wrapper around the substitution algebra. -/
theorem StateBisimulation.localRenamingOn
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (capsFixed : ∀ varId ∈ capScope,
      state.prevailing.cap varId = .var varId)
    (targetsFixed : ∀ varId ∈ targetScope,
      state.prevailing.target varId = .var varId) :
    LocalRenamingOn relation.forward relation.reverse capScope targetScope :=
  localRenamingOn_of_mutualFactorization relation.forwardEquation
    relation.reverseEquation capsFixed targetsFixed

/-- Idempotence makes the state residuals a local renaming on the free
variables of one normalized executable image. -/
theorem StateBisimulation.localRenamingOn_image
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (target : Ty) :
    LocalRenamingOn relation.forward relation.reverse
      (state.prevailing.apply target).fcv
      (state.prevailing.apply target).ftv := by
  exact localRenamingOn_of_mutualFactorization relation.forwardEquation
    relation.reverseEquation
      (relation.executableIdempotent.image_cap_fixed target)
      (relation.executableIdempotent.image_target_fixed target)

/-- Symmetric scope certificate for a normalized declarative image. -/
theorem StateBisimulation.reverseLocalRenamingOn_image
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (target : Ty) :
    LocalRenamingOn relation.reverse relation.forward
      (declarative.apply target).fcv
      (declarative.apply target).ftv := by
  exact localRenamingOn_of_mutualFactorization relation.reverseEquation
    relation.forwardEquation
      (relation.declarativeIdempotent.image_cap_fixed target)
      (relation.declarativeIdempotent.image_target_fixed target)

/-- Bundle form used by heterogeneous cuts and by `let` generalization.  The
scope is the concatenated free-variable traversal of a finite list of already
normalized executable types. -/
theorem StateBisimulation.localRenamingOn_bundle
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (normalized : List Ty)
    (capsFixed : ∀ varId ∈ Ty.fcvList normalized,
      state.prevailing.cap varId = .var varId)
    (targetsFixed : ∀ varId ∈ Ty.ftvList normalized,
      state.prevailing.target varId = .var varId) :
    LocalRenamingOn relation.forward relation.reverse
      (Ty.fcvList normalized) (Ty.ftvList normalized) :=
  localRenamingOn_of_mutualFactorization relation.forwardEquation
    relation.reverseEquation capsFixed targetsFixed

end DemandTypingInferenceCompletenessLocalRenaming
end TypePM
