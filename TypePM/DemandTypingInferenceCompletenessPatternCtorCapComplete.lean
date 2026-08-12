import TypePM.DemandTypingInferenceCompletenessPatternDispatcher
import TypePM.DemandTypingInferenceCompletenessFixMatcher
import TypePM.DemandTypingInferenceCompletenessValidatorBisimulation

/-!
# Closed pattern-constructor capability completeness package

This module closes the isolated capability subroutine used by user pattern
constructors.  Projection success is transported through the finite
DD/executable renaming; projection failure is invariant.  The fallback branch
then replays the shared-result allocation and field-capability alignment before
using the same projected-skeleton completion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternCtorCapComplete

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternCtorCapability
open DemandTypingInferenceCompletenessPatternMain
open DemandTypingInferenceCompletenessPatternDispatcher
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance

/-- The canonical reverse renaming extracted from bounded constructor children
fixes every capability identifier which may be freshly allocated at `q`. -/
theorem reverseChildRenaming_freshAbove
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeChildren : List Cap}
    (childrenBounded : ∀ child ∈ declarativeChildren, child.BoundedBy q) :
    let bundle := Ty.matcher (.prod declarativeChildren) .unit
    let localMap := StateBisimulation.reverseLocalRenamingOn_image
      before.prevailing bundle
    RenamingFreshAbove localMap.capImage q := by
  dsimp only
  intro varId above
  apply dif_neg
  intro membership
  have unitBounded : Ty.BoundedBy q .unit := by
    constructor
    · intro varId membership
      exact nomatch membership
    · intro varId membership
      exact nomatch membership
  have rawBundleBounded : Ty.BoundedBy q
      (.matcher (.prod declarativeChildren) .unit) :=
    Ty.BoundedBy.matcherOf
      (Cap.BoundedBy.prodOfForall childrenBounded) unitBounded
  have normalizedBounded := before.declarative_bounded.apply rawBundleBounded
  exact (Nat.not_le_of_lt (normalizedBounded.1 varId membership)) above

/-- The local reverse renaming gives the concrete executable projection result
and is fresh above the current supply. -/
theorem projectSignature_success_scoped
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {declarativeChildren executableChildren : List Cap}
    (children : CapListBisimulation before.prevailing declarativeChildren
      executableChildren)
    (childrenBounded : ∀ child ∈ declarativeChildren, child.BoundedBy q)
    {projected : Shape.Evidence}
    (success : Projection.projectSignature entry.projection
      ((declarativeChildren.map fun child => child.apply S.cap).map
        Shape.ofCap) = some projected) :
    let bundle := Ty.matcher (.prod declarativeChildren) .unit
    let localMap := StateBisimulation.reverseLocalRenamingOn_image
      before.prevailing bundle
    Projection.projectSignature entry.projection
      ((executableChildren.map fun child =>
        child.apply state.prevailing.cap).map Shape.ofCap) =
        some (projected.applyRen localMap.capImage) ∧
      RenamingFreshAbove localMap.capImage q := by
  dsimp only
  let bundle := Ty.matcher (.prod declarativeChildren) .unit
  let localMap := StateBisimulation.reverseLocalRenamingOn_image
    before.prevailing bundle
  let rename := localMap.capImage
  have resolved : executableChildren.map
      (fun child => child.apply state.prevailing.cap) =
      Cap.applyRenList rename
        (declarativeChildren.map fun child => child.apply S.cap) := by
    rw [children.reverseResolved]
    have pure := LocalRenamingOn.forward_apply_eq_pure localMap
      (S.apply bundle) (fun _ membership => membership)
      (fun _ membership => membership)
    have capabilities := Cap.prod.inj (Ty.matcher.inj pure).1
    let variablePost : VariablePost (LocalRenamingOn.pureSubst localMap) :=
      { capVariable := fun varId => ⟨rename varId, rfl⟩ }
    have capRenEq : variablePost.capRen = rename := by
      funext varId
      have point := variablePost.capEquation varId
      change Cap.var (rename varId) = Cap.var (variablePost.capRen varId) at point
      exact (Cap.var.inj point).symm
    have pureCaps := variablePost.applyCapList_eq_applyRenList
      (declarativeChildren.map fun child => child.apply S.cap)
    rw [capRenEq] at pureCaps
    have capabilities' :
        (declarativeChildren.map fun child => child.apply S.cap).map
            (fun capability => capability.apply before.prevailing.reverse.cap) =
          Cap.applyList (LocalRenamingOn.pureSubst localMap).cap
            (declarativeChildren.map fun child => child.apply S.cap) := by
      simpa only [Cap.applyList_eq_map] using capabilities
    exact capabilities'.trans pureCaps
  constructor
  · rw [resolved, Shape.map_ofCap_applyRen]
    exact Projection.projectSignature_rename_of_success rename
      entry.projection success
  · exact reverseChildRenaming_freshAbove before childrenBounded

end DemandTypingInferenceCompletenessPatternCtorCapComplete
end TypePM
