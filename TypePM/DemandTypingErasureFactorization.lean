import TypePM.DemandTypingErasureCore

/-!
# Premise-free state factorization for demand typing

This module extends the scoped residual-post construction to the auxiliary
pattern alignments and closes state factorization over all 14 origin-aware
demand-typing families.  Its constructor lemmas expose the actual allocation,
solve, child, and freeze sequence; the final mutual theorems require only
signature closure and bounded inputs.
-/

namespace TypePM

namespace DDAlignDualWithLedger

open DDErasure

/-- A dual alignment factors into its capability solve followed by its
target-type solve. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : Dual} {q : InferenceBase.FreshSupply}
    (aligned : DDAlignDualWithLedger ledger S left right S')
    (Sb : S.BoundedBy q) (leftBounded : left.BoundedBy q)
    (rightBounded : right.BoundedBy q) :
    StateFactorization q S ledger q S' ledger := by
  cases aligned
  rename_i capDelta capSafe targetsAligned
  have capPairB := capSafe.exact.boundedBy_pair
    (Sb.applyCap leftBounded.1) (Sb.applyCap rightBounded.1)
  have capFactor : StateFactorization q S ledger q
      (Subst.seq ⟨capDelta, TySubst.id⟩ S) ledger := by
    exact ⟨⟨capDelta, TySubst.id⟩, rfl,
      AdmissiblePostBetween.ofAdmissible
        { cap := capSafe.admissible } capPairB⟩
  have targetFactor := DDErasure.StateFactorization.ofAlignTypes
    targetsAligned (capPairB.seq Sb) leftBounded.2 rightBounded.2
  exact capFactor.trans targetFactor

end DDAlignDualWithLedger

namespace DDAlignDualListWithLedger

open DDErasure

/-- Pointwise dual alignment is the chronological composition of its
element alignments. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {lefts rights : List Dual} {q : InferenceBase.FreshSupply}
    (aligned : DDAlignDualListWithLedger ledger S lefts rights S')
    (Sb : S.BoundedBy q)
    (leftBounded : ∀ dual ∈ lefts, dual.BoundedBy q)
    (rightBounded : ∀ dual ∈ rights, dual.BoundedBy q) :
    StateFactorization q S ledger q S' ledger := by
  induction aligned with
  | nil => exact StateFactorization.refl q _ ledger
  | @cons S left right lefts rights S₁ S' head tail ih =>
      have headFactor := head.factorPost Sb
        (leftBounded left (by simp)) (rightBounded right (by simp))
      have S₁b := head.erase.boundedBy Sb
        (leftBounded left (by simp)) (rightBounded right (by simp))
      exact headFactor.trans (ih S₁b
        (fun dual mem => leftBounded dual (by simp [mem]))
        (fun dual mem => rightBounded dual (by simp [mem])))

end DDAlignDualListWithLedger

namespace DDAlignTargetListWithLedger

open DDErasure

/-- Pointwise result-target alignment factors element by element. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {duals : List Dual} {expecteds : List Ty}
    {q : InferenceBase.FreshSupply}
    (aligned : DDAlignTargetListWithLedger ledger S duals expecteds S')
    (Sb : S.BoundedBy q)
    (dualsBounded : ∀ dual ∈ duals, dual.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ expecteds,
      expected.BoundedBy q) :
    StateFactorization q S ledger q S' ledger := by
  induction aligned with
  | nil => exact StateFactorization.refl q _ ledger
  | @cons S dual expected duals expecteds S₁ S' head tail ih =>
      have headFactor := DDErasure.StateFactorization.ofAlignTypes head Sb
        (dualsBounded dual (by simp)).2
        (expectedsBounded expected (by simp))
      have S₁b := head.erase.boundedBy Sb
        (dualsBounded dual (by simp)).2
        (expectedsBounded expected (by simp))
      exact headFactor.trans (ih S₁b
        (fun item mem => dualsBounded item (by simp [mem]))
        (fun item mem => expectedsBounded item (by simp [mem])))

end DDAlignTargetListWithLedger

namespace DDAlignBindingsWithLedger

open DDErasure

/-- Binding alignment factors entry by entry; name equality does not change
inference state. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {lefts rights : MonoCtx} {q : InferenceBase.FreshSupply}
    (aligned : DDAlignBindingsWithLedger ledger S lefts rights S')
    (Sb : S.BoundedBy q)
    (leftBounded : ∀ entry ∈ lefts, entry.2.BoundedBy q)
    (rightBounded : ∀ entry ∈ rights, entry.2.BoundedBy q) :
    StateFactorization q S ledger q S' ledger := by
  induction aligned with
  | nil => exact StateFactorization.refl q _ ledger
  | @cons S left right lefts rights S₁ S' names head tail ih =>
      have headFactor := DDErasure.StateFactorization.ofAlignTypes head Sb
        (leftBounded left (by simp)) (rightBounded right (by simp))
      have S₁b := head.erase.boundedBy Sb
        (leftBounded left (by simp)) (rightBounded right (by simp))
      exact headFactor.trans (ih S₁b
        (fun entry mem => leftBounded entry (by simp [mem]))
        (fun entry mem => rightBounded entry (by simp [mem])))

end DDAlignBindingsWithLedger

namespace DDAlignCtorCapsWithLedger

open DDErasure

/-- Constructor-field capability alignment factors only the `some` demand
positions; skipped fields contribute identity. -/
theorem factorPost
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {children : List Cap} {demands : List (Option Cap)}
    {q : InferenceBase.FreshSupply}
    (aligned : DDAlignCtorCapsWithLedger ledger S children demands S')
    (Sb : S.BoundedBy q)
    (childrenBounded : ∀ child ∈ children, child.BoundedBy q)
    (demandsBounded : ∀ demand ∈ demands, ∀ capability,
      demand = some capability → capability.BoundedBy q) :
    StateFactorization q S ledger q S' ledger := by
  induction aligned with
  | nil => exact StateFactorization.refl q _ ledger
  | @skip S child children demands S' tail ih =>
      exact ih Sb
        (fun item mem => childrenBounded item (by simp [mem]))
        (fun demand mem => demandsBounded demand (by simp [mem]))
  | @solve S child expected children demands capDelta S' capSafe tail ih =>
      have capPairB := capSafe.exact.boundedBy_pair
        (Sb.applyCap (childrenBounded child (by simp)))
        (Sb.applyCap (demandsBounded (some expected) (by simp) expected rfl))
      have headFactor : StateFactorization q S ledger q
          (Subst.seq ⟨capDelta, TySubst.id⟩ S) ledger := by
        exact ⟨⟨capDelta, TySubst.id⟩, rfl,
          AdmissiblePostBetween.ofAdmissible
            { cap := capSafe.admissible } capPairB⟩
      exact headFactor.trans (ih (capPairB.seq Sb)
        (fun item mem => childrenBounded item (by simp [mem]))
        (fun demand mem => demandsBounded demand (by simp [mem])))

end DDAlignCtorCapsWithLedger

namespace DDPatternCtorCapOrigin

open DDErasure

/-- State evolution exposed by pattern-constructor capability projection. -/
def StateFactorization
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {children : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatternCtorCap signature entry q S children capability q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternCtorCapOrigin signature entry raw ledger ledger') :
    Prop := DDErasure.StateFactorization q S ledger q' S' ledger'

/-- Exact projection only freshens the projected skeleton. -/
theorem stateFactorization_project
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {children : List Cap}
    {projected : Shape.Evidence} {capability : Cap}
    {q' : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (projection : Projection.projectSignature entry.projection
      ((children.map fun child => child.apply S.cap).map Shape.ofCap) =
        some projected)
    (freshened : freshenSkeletonSupply signature.observability projected q =
      some (capability, q')) :
    StateFactorization
      (DDPatternCtorCapOrigin.project (ledger := ledger) projection
        freshened) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.freshenSkeleton freshened)
    (DDLedger.RefinesBelow.markCapRange q q' ledger)

/-- The fallback path allocates its assignment range, performs the explicit
field-demand alignment, and then freshens the projected skeleton. -/
theorem stateFactorization_fallback_of_alignment
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {children : List Cap}
    {resultVariables : List TypePM.TyVar} {demands : List (Option Cap)}
    {S₁ : Subst} {projected : Shape.Evidence} {capability : Cap}
    {q' : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    (projectionMiss : Projection.projectSignature entry.projection
      ((children.map fun child => child.apply S.cap).map Shape.ofCap) = none)
    (resultVars : Projection.relevantVars signature.observability
      (Projection.targetVars entry.projection.resultType)
      entry.projection.resultType = some resultVariables)
    (fieldDemands : Inference.patternCtorFieldDemands
      signature.observability resultVariables.eraseDups
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).1
      entry.projection.fieldTypes = some demands)
    (aligned : DDAlignCtorCapsWithLedger
      (DDLedger.markCapRange ledger q
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
      S children demands S₁)
    (projectionHit : Projection.projectSignature entry.projection
      ((children.map fun child => child.apply S₁.cap).map Shape.ofCap) =
        some projected)
    (freshened : freshenSkeletonSupply signature.observability projected
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 =
        some (capability, q'))
    (alignmentFactorization : DDErasure.StateFactorization
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 S
      (DDLedger.markCapRange ledger q
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
      (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 S₁
      (DDLedger.markCapRange ledger q
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)) :
    StateFactorization
      (DDPatternCtorCapOrigin.fallback projectionMiss resultVars fieldDemands
        aligned projectionHit freshened) := by
  let q₁ := (patternCtorAssignmentsSupply resultVariables.eraseDups q).2
  let ledger₁ := DDLedger.markCapRange ledger q q₁
  have allocation : DDErasure.StateFactorization q S ledger q₁ S ledger₁ :=
    DDErasure.StateFactorization.ofTransition
      (SupplyExtends.patternCtorAssignments (q := q)
        resultVariables.eraseDups)
      (DDLedger.RefinesBelow.markCapRange q q₁ ledger)
  have freshening : DDErasure.StateFactorization q₁ S₁ ledger₁ q' S₁
      (DDLedger.markCapRange ledger₁ q₁ q') :=
    DDErasure.StateFactorization.ofTransition
      (SupplyExtends.freshenSkeleton freshened)
      (DDLedger.RefinesBelow.markCapRange q₁ q' ledger₁)
  exact (allocation.trans alignmentFactorization).trans freshening

end DDPatternCtorCapOrigin

namespace DDDPatOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_var
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDDPatOrigin.var (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDDPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

/-- Constructor data-patterns compose instance allocation, result
alignment, recursive children, and the explicit export freeze. -/
theorem stateFactorization_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List DPat} {expected : Ty}
    {scheme : CtorScheme} {S₁ : Subst} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q scheme) S
      (InferenceBase.instantiateCtorScheme q scheme).value.2 expected S₁)
    {children : DDDPats signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger₂)
    (alignmentFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      (DDLedger.markCtorInstance ledger q scheme)
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁
      (DDLedger.markCtorInstance ledger q scheme))
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁
      (DDLedger.markCtorInstance ledger q scheme) q' S' ledger₂) :
    StateFactorization (DDDPatOrigin.ctor lookup aligned childrenOrigin) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.instantiateCtorScheme q scheme)
    (DDLedger.RefinesBelow.markCtorInstance q ledger scheme)
  have freezing := DDErasure.StateFactorization.ofTransition
    (S := S') (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeExport q' ledger₂ S'
      (Inference.freshCapImages q scheme.capBinders)
      (Inference.capabilityExportPayload []
        (expected :: bindings.map fun entry => entry.2)))
  exact ((allocation.trans alignmentFactorization).trans
    childrenFactorization).trans freezing

/-- Tuple data-patterns allocate their component targets before alignment. -/
theorem stateFactorization_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {expected : Ty} {S₁ : Subst}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDDPats signature (freshTargetsSupply patterns.length q).2
      S₁ patterns (freshTargetsSupply patterns.length q).1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children ledger ledger')
    (alignmentFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S ledger
      (freshTargetsSupply patterns.length q).2 S₁ ledger)
    (childrenFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S₁ ledger q' S' ledger') :
    StateFactorization (DDDPatOrigin.tuple aligned childrenOrigin) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.freshTargets patterns.length q)
    (DDLedger.RefinesBelow.refl q ledger)
  exact (allocation.trans alignmentFactorization).trans childrenFactorization

end DDDPatOrigin

namespace DDDPatsOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatsOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDDPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {patterns : List DPat} {target : Ty}
    {targets : List Ty} {bindings restBindings : MonoCtx}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDDPat signature q S pattern target bindings q₁ S₁}
    {tail : DDDPats signature q₁ S₁ patterns targets restBindings q' S'}
    (headOrigin : DDDPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDDPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headFactorization : DDDPatOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization
      (DDDPatsOrigin.cons headOrigin tailOrigin disjoint) :=
  headFactorization.trans tailFactorization

end DDDPatsOrigin

namespace DDPPatOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_hole
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPPatOrigin.hole (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.bumpCap q 1)
    (DDLedger.RefinesBelow.markFreshCap q ledger)

theorem stateFactorization_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_pval
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPPatOrigin.pval (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List PPat} {expected : Ty}
    {entry : PatternCtorScheme signature.observability} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findPatternCtor name = some entry)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q entry.scheme) S
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2 expected S₁)
    {children : DDPPats signature
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 holes bindings
      q' S'}
    (childrenOrigin : DDPPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q entry.scheme) ledger₂)
    (alignmentFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S
      (DDLedger.markCtorInstance ledger q entry.scheme)
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
      (DDLedger.markCtorInstance ledger q entry.scheme))
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
      (DDLedger.markCtorInstance ledger q entry.scheme) q' S' ledger₂) :
    StateFactorization (DDPPatOrigin.ctor lookup aligned childrenOrigin) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.instantiateCtorScheme q entry.scheme)
    (DDLedger.RefinesBelow.markCtorInstance q ledger entry.scheme)
  have freezing := DDErasure.StateFactorization.ofTransition
    (S := S') (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeExport q' ledger₂ S'
      (Inference.freshCapImages q entry.scheme.capBinders)
      (Inference.capabilityExportPayload (holes.map Dual.cap)
        (holes.map Dual.target ++ expected ::
          bindings.map fun binding => binding.2)))
  exact ((allocation.trans alignmentFactorization).trans
    childrenFactorization).trans freezing

theorem stateFactorization_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {expected : Ty} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDPPats signature (freshTargetsSupply patterns.length q).2
      S₁ patterns (freshTargetsSupply patterns.length q).1 holes bindings
      q' S'}
    (childrenOrigin : DDPPatsOrigin signature children ledger ledger')
    (alignmentFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S ledger
      (freshTargetsSupply patterns.length q).2 S₁ ledger)
    (childrenFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S₁ ledger q' S' ledger') :
    StateFactorization (DDPPatOrigin.tuple aligned childrenOrigin) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.freshTargets patterns.length q)
    (DDLedger.RefinesBelow.refl q ledger)
  exact (allocation.trans alignmentFactorization).trans childrenFactorization

end DDPPatOrigin

namespace DDPPatsOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatsOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {patterns : List PPat} {target : Ty}
    {targets : List Ty} {holes restHoles : List Dual}
    {bindings restBindings : MonoCtx}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDPPat signature q S pattern target holes bindings q₁ S₁}
    {tail : DDPPats signature q₁ S₁ patterns targets restHoles
      restBindings q' S'}
    (headOrigin : DDPPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDPPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headFactorization : DDPPatOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization
      (DDPPatsOrigin.cons headOrigin tailOrigin disjoint) :=
  headFactorization.trans tailFactorization

end DDPPatsOrigin

namespace DDPatternOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_pvar
    {_signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {_context : Context} {_parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {ledger : CapabilityOriginLedger}
    (_freshName : name ∉ bindings.names) :
    DDErasure.StateFactorization q S ledger
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 }
      S (DDLedger.markFreshCap ledger q) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.bumpBoth q 1 1)
    (DDLedger.RefinesBelow.markFreshCap q ledger)

theorem stateFactorization_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPatternOrigin.wild (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.bumpBoth q 1 1)
    (DDLedger.RefinesBelow.markFreshCap q ledger)

theorem stateFactorization_pval_of_expression
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {_parameters : PatternCtx} {bindings : MonoCtx}
    {expression : Expr} {target : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    {expressionRaw : DDSynth signature q S
      (bindings.toContext ++ context) expression target q₁ S₁}
    (expressionOrigin : DDSynthOrigin signature expressionRaw ledger ledger₁)
    (expressionFactorization :
      DDSynthOrigin.StateFactorization expressionOrigin) :
    DDErasure.StateFactorization q S ledger
      { q₁ with nextCap := q₁.nextCap + 1 } S₁
      (DDLedger.markFreshCap ledger₁ q₁) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S₁) (SupplyExtends.bumpCap q₁ 1)
    (DDLedger.RefinesBelow.markFreshCap q₁ ledger₁)
  exact expressionFactorization.trans allocation

theorem stateFactorization_embed
    {_signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {_context : Context} {parameters : PatternCtx} {_bindings : MonoCtx}
    {name : String} {dual : Dual} {ledger : CapabilityOriginLedger}
    (_lookup : parameters.find? name = some dual) :
    DDErasure.StateFactorization q S ledger q S ledger :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_ptuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DDPatterns signature q S context parameters bindings patterns
      duals bindings' q' S'}
    (childrenOrigin : DDPatternsOrigin signature children ledger ledger')
    (childrenFactorization : DDErasure.StateFactorization
      q S ledger q' S' ledger') :
    StateFactorization (DDPatternOrigin.ptuple childrenOrigin) :=
  childrenFactorization

/-- Pattern-constructor traversal exposes each real cut: scheme allocation,
children, target alignment, capability projection, then export freeze. -/
theorem stateFactorization_pctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {patterns : List Pattern}
    {entry : PatternCtorScheme signature.observability}
    {duals : List Dual} {bindings' : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
    {capability : Cap} {q₂ : InferenceBase.FreshSupply} {S₃ : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findPatternCtor name = some entry)
    {children : DDPatterns signature
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S context
      parameters bindings patterns duals bindings' q₁ S₁}
    (childrenOrigin : DDPatternsOrigin signature children
      (DDLedger.markCtorInstance ledger q entry.scheme) ledger₁)
    (targetsAligned : DDAlignTargetListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂)
    {capRaw : DDPatternCtorCap signature entry q₁ S₂
      (duals.map Dual.cap) capability q₂ S₃}
    (capOrigin : DDPatternCtorCapOrigin signature entry capRaw ledger₁
      ledger₂)
    (compatible : Inference.capCompatibleCheck entry
      ((duals.map Dual.cap).map fun child => child.apply S₃.cap)
      (capability.apply S₃.cap) = true)
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S
      (DDLedger.markCtorInstance ledger q entry.scheme) q₁ S₁ ledger₁)
    (targetsFactorization : DDErasure.StateFactorization
      q₁ S₁ ledger₁ q₁ S₂ ledger₁)
    (capFactorization : DDPatternCtorCapOrigin.StateFactorization capOrigin) :
    StateFactorization
      (DDPatternOrigin.pctor lookup childrenOrigin targetsAligned capOrigin
        compatible) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.instantiateCtorScheme q entry.scheme)
    (DDLedger.RefinesBelow.markCtorInstance q ledger entry.scheme)
  have freezing := DDErasure.StateFactorization.ofTransition
    (S := S₃) (SupplyExtends.refl q₂)
    (DDLedger.RefinesBelow.freezeExport q₂ ledger₂ S₃
      (Inference.freshCapImages q entry.scheme.capBinders)
      (Inference.capabilityExportPayload [capability]
        ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
          bindings'.map fun binding => binding.2)))
  exact ((((allocation.trans childrenFactorization).trans
    targetsFactorization).trans capFactorization).trans freezing)

theorem stateFactorization_pand_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {left right : Pattern} {leftDual : Dual} {leftBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {rightDual : Dual} {bindings' : MonoCtx}
    {q₂ : InferenceBase.FreshSupply} {S₂ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {leftRaw : DDPattern signature q S context parameters bindings left
      leftDual leftBindings q₁ S₁}
    (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
    {rightRaw : DDPattern signature q₁ S₁ context parameters
      leftBindings right rightDual bindings' q₂ S₂}
    (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
    (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S')
    (leftFactorization : StateFactorization leftOrigin)
    (rightFactorization : StateFactorization rightOrigin)
    (alignmentFactorization : DDErasure.StateFactorization
      q₂ S₂ ledger₂ q₂ S' ledger₂) :
    StateFactorization
      (DDPatternOrigin.pand leftOrigin rightOrigin aligned) :=
  (leftFactorization.trans rightFactorization).trans alignmentFactorization

theorem stateFactorization_por_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {left right : Pattern} {leftDual : Dual} {leftBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {rightDual : Dual} {rightBindings : MonoCtx}
    {q₂ : InferenceBase.FreshSupply} {S₂ S₃ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {leftRaw : DDPattern signature q S context parameters bindings left
      leftDual leftBindings q₁ S₁}
    (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
    {rightRaw : DDPattern signature q₁ S₁ context parameters bindings
      right rightDual rightBindings q₂ S₂}
    (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
    (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual
      rightDual S₃)
    (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃
      leftBindings rightBindings S')
    (leftFactorization : StateFactorization leftOrigin)
    (rightFactorization : StateFactorization rightOrigin)
    (dualsFactorization : DDErasure.StateFactorization
      q₂ S₂ ledger₂ q₂ S₃ ledger₂)
    (bindingsFactorization : DDErasure.StateFactorization
      q₂ S₃ ledger₂ q₂ S' ledger₂) :
    StateFactorization
      (DDPatternOrigin.por leftOrigin rightOrigin dualsAligned
        bindingsAligned) :=
  (((leftFactorization.trans rightFactorization).trans dualsFactorization).trans
    bindingsFactorization)

theorem stateFactorization_papp_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {patterns : List Pattern} {scheme : DualScheme}
    {duals : List Dual} {bindings' : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (lookup : signature.findPatternFun name = some scheme)
    {children : DDPatterns signature
      (InferenceBase.instantiateDualScheme q scheme).supply S context
      parameters bindings patterns duals bindings' q₁ S₁}
    (childrenOrigin : DDPatternsOrigin signature children
      (DDLedger.markDualInstance ledger q scheme) ledger₁)
    (aligned : DDAlignDualListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateDualScheme q scheme).value.1 S')
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateDualScheme q scheme).supply S
      (DDLedger.markDualInstance ledger q scheme) q₁ S₁ ledger₁)
    (alignmentFactorization : DDErasure.StateFactorization
      q₁ S₁ ledger₁ q₁ S' ledger₁) :
    StateFactorization
      (DDPatternOrigin.papp lookup childrenOrigin aligned) := by
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S) (SupplyExtends.instantiateDualScheme q scheme)
    (DDLedger.RefinesBelow.markDualInstance q ledger scheme)
  exact (allocation.trans childrenFactorization).trans alignmentFactorization

end DDPatternOrigin

namespace DDPatternsOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternsOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDPatternsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {pattern : Pattern} {patterns : List Pattern} {dual : Dual}
    {duals : List Dual} {bindings₁ bindings' : MonoCtx}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDPattern signature q S context parameters bindings pattern dual
      bindings₁ q₁ S₁}
    {tail : DDPatterns signature q₁ S₁ context parameters bindings₁
      patterns duals bindings' q' S'}
    (headOrigin : DDPatternOrigin signature head ledger ledger₁)
    (tailOrigin : DDPatternsOrigin signature tail ledger₁ ledger')
    (headFactorization : DDPatternOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization (DDPatternsOrigin.cons headOrigin tailOrigin) :=
  headFactorization.trans tailFactorization

end DDPatternsOrigin

namespace DDArmsOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDArmsOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (bindings : MonoCtx) (clauseTarget bodyTarget : Ty)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDArmsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ppBindings := bindings)
        (clauseTarget := clauseTarget) (bodyTarget := bodyTarget)
        (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

/-- An arm-list node is exactly data-pattern, body check, then tail. -/
theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {dataPattern : DPat}
    {body : Expr} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {armBindings : MonoCtx} {q₁ q₂ q' : InferenceBase.FreshSupply}
    {S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {patternRaw : DDDPat signature q S dataPattern clauseTarget armBindings
      q₁ S₁}
    (patternOrigin : DDDPatOrigin signature patternRaw ledger ledger₁)
    (disjoint : ∀ name, name ∈ armBindings.names →
      name ∉ ppBindings.names)
    {bodyRaw : DDCheck signature q₁ S₁
      (armBindings.toContext ++ ppBindings.toContext ++ context) body
      bodyTarget q₂ S₂}
    (bodyOrigin : DDCheckOrigin signature bodyRaw ledger₁ ledger₂)
    {tailRaw : DDArms signature q₂ S₂ context ppBindings arms
      clauseTarget bodyTarget q' S'}
    (tailOrigin : DDArmsOrigin signature tailRaw ledger₂ ledger')
    (patternFactorization : DDDPatOrigin.StateFactorization patternOrigin)
    (bodyFactorization : DDCheckOrigin.StateFactorization bodyOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization
      (DDArmsOrigin.cons patternOrigin disjoint bodyOrigin tailOrigin) :=
  (patternFactorization.trans bodyFactorization).trans tailFactorization

end DDArmsOrigin

namespace DDClauseOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClauseOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

/-- A matcher clause is primitive-pattern traversal, checking of all next
matchers at their slot demands, then arm traversal. -/
theorem stateFactorization_mk
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {pp : PPat} {next : Expr} {arms : List Arm}
    {sharedTarget : Ty} {holes : List Dual} {ppBindings : MonoCtx}
    {nextMatchers : List Expr}
    {q₁ q₂ q' : InferenceBase.FreshSupply} {S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {ppRaw : DDPPat signature q S pp sharedTarget holes ppBindings q₁ S₁}
    (ppOrigin : DDPPatOrigin signature ppRaw ledger ledger₁)
    (decomposed : decomposeME next holes.length = some nextMatchers)
    {nextRaw : DDChecks signature q₁ S₁ context nextMatchers
      (holes.map fun hole => .slot hole.cap hole.target) q₂ S₂}
    (nextOrigin : DDChecksOrigin signature nextRaw ledger₁ ledger₂)
    {armsRaw : DDArms signature q₂ S₂ context ppBindings arms
      sharedTarget (Ty.listT (prodTy (holes.map Dual.target))) q' S'}
    (armsOrigin : DDArmsOrigin signature armsRaw ledger₂ ledger')
    (ppFactorization : DDPPatOrigin.StateFactorization ppOrigin)
    (nextFactorization : DDChecksOrigin.StateFactorization nextOrigin)
    (armsFactorization : DDArmsOrigin.StateFactorization armsOrigin) :
    StateFactorization
      (DDClauseOrigin.mk ppOrigin decomposed nextOrigin armsOrigin) :=
  (ppFactorization.trans nextFactorization).trans armsFactorization

end DDClauseOrigin

namespace DDClausesOrigin

open DDErasure

def StateFactorization
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q'
      S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClausesOrigin signature raw ledger ledger') : Prop :=
  DDErasure.StateFactorization q S ledger q' S' ledger'

theorem stateFactorization_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (sharedTarget : Ty)
    (ledger : CapabilityOriginLedger) :
    StateFactorization
      (DDClausesOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (sharedTarget := sharedTarget)
        (ledger := ledger)) :=
  DDErasure.StateFactorization.refl q S ledger

theorem stateFactorization_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {clauses : List Clause}
    {sharedTarget : Ty} {holes : List Dual}
    {holeLists : List (List Dual)}
    {q₁ q' : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDClause signature q S context clause sharedTarget holes q₁ S₁}
    {tail : DDClauses signature q₁ S₁ context clauses sharedTarget
      holeLists q' S'}
    (headOrigin : DDClauseOrigin signature head ledger ledger₁)
    (tailOrigin : DDClausesOrigin signature tail ledger₁ ledger')
    (headFactorization : DDClauseOrigin.StateFactorization headOrigin)
    (tailFactorization : StateFactorization tailOrigin) :
    StateFactorization (DDClausesOrigin.cons headOrigin tailOrigin) :=
  headFactorization.trans tailFactorization

end DDClausesOrigin

/-! ## Premise-free recursive closures for expression-free pattern layers -/

/-- Pattern-constructor capability projection has a premise-free
factorization once its input substitution and child capabilities are known
to be bounded. -/
theorem DDPatternCtorCapOrigin.factorize
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {children : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatternCtorCap signature entry q S children capability q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternCtorCapOrigin signature entry raw ledger ledger')
    (Sb : S.BoundedBy q)
    (childrenBounded : ∀ child ∈ children, child.BoundedBy q) :
    DDPatternCtorCapOrigin.StateFactorization origin :=
  match origin with
  | .project projection freshened =>
      DDPatternCtorCapOrigin.stateFactorization_project projection freshened
  | @DDPatternCtorCapOrigin.fallback _ _ q S children resultVariables demands
      _ _ _ _ ledger projectionMiss resultVars fieldDemands aligned
      projectionHit freshened => by
      let q₁ := (patternCtorAssignmentsSupply resultVariables.eraseDups q).2
      let ledger₁ := DDLedger.markCapRange ledger q q₁
      have extension := SupplyExtends.patternCtorAssignments (q := q)
        resultVariables.eraseDups
      have demandsBounded : ∀ demand ∈ demands, ∀ expected,
          demand = some expected → expected.BoundedBy q₁ := by
        intro demand mem expected equation varId varMem
        exact patternCtorAssignmentsSupply_fcv resultVariables.eraseDups q
          varId (Inference.patternCtorFieldDemands_fcv fieldDemands demand mem
            expected equation varMem)
      have alignmentFactorization := aligned.factorPost (Sb.mono extension)
        (fun child mem => (childrenBounded child mem).mono extension)
        demandsBounded
      exact DDPatternCtorCapOrigin.stateFactorization_fallback_of_alignment
        projectionMiss resultVars fieldDemands aligned projectionHit freshened
        alignmentFactorization

mutual

/-- Data-pattern origin derivations factor without an externally supplied
child factorization. -/
theorem DDDPatOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    DDDPatOrigin.StateFactorization origin :=
  match origin with
  | .var => DDErasure.StateFactorization.refl _ _ _
  | .wild => DDErasure.StateFactorization.refl _ _ _
  | @DDDPatOrigin.ctor _ q S _ _ expected scheme _ _ _ _ ledger _ lookup
      aligned _ childrenOrigin => by
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      have extension := SupplyExtends.instantiateCtorScheme q scheme
      have S₁b := aligned.erase.boundedBy (Sb.mono extension)
        instBounded.2 (expectedBounded.mono extension)
      have alignmentFactorization := aligned.factorPost (Sb.mono extension)
        instBounded.2 (expectedBounded.mono extension)
      exact DDDPatOrigin.stateFactorization_ctor_of_children lookup aligned
        childrenOrigin
        alignmentFactorization
        (DDDPatsOrigin.factorize childrenOrigin closed S₁b instBounded.1)
  | @DDDPatOrigin.tuple _ q S patterns expected _ _ _ _ ledger _ aligned _
      childrenOrigin => by
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      have extension := SupplyExtends.freshTargets patterns.length q
      have productBounded := Ty.BoundedBy.prodOfForall targetsBounded
      have S₁b := aligned.erase.boundedBy (Sb.mono extension)
        productBounded (expectedBounded.mono extension)
      have alignmentFactorization := aligned.factorPost (Sb.mono extension)
        productBounded (expectedBounded.mono extension)
      exact DDDPatOrigin.stateFactorization_tuple_of_children aligned
        childrenOrigin
        alignmentFactorization
        (DDDPatsOrigin.factorize childrenOrigin closed S₁b targetsBounded)

/-- Data-pattern lists factor by recursively composing head and tail. -/
theorem DDDPatsOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q) :
    DDDPatsOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | .cons headOrigin tailOrigin disjoint => by
      have headFactor := DDDPatOrigin.factorize headOrigin closed Sb
        (targetsBounded _ (by simp))
      obtain ⟨S₁b, _⟩ := headOrigin.erase.boundedBy closed Sb
        (targetsBounded _ (by simp))
      have tailFactor := DDDPatsOrigin.factorize tailOrigin closed S₁b
        (fun target mem =>
          (targetsBounded target (by simp [mem])).mono
            headOrigin.erase.supplyExtends)
      exact DDDPatsOrigin.stateFactorization_cons headOrigin tailOrigin
        disjoint headFactor tailFactor

end

/-! ## Premise-free closure of the expression/pattern mutual block -/

mutual

private theorem DDPPatOrigin.factorizeCore
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    DDPPatOrigin.StateFactorization origin :=
  match origin with
  | .hole => DDPPatOrigin.stateFactorization_hole _ _ _ _ _
  | .wild => DDErasure.StateFactorization.refl _ _ _
  | .pval => DDErasure.StateFactorization.refl _ _ _
  | @DDPPatOrigin.ctor _ q S _ _ expected entry _ _ _ _ _ ledger _ lookup
      aligned _ childrenOrigin => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q entry.scheme
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) instB.2
        (expectedBounded.mono ext)
      exact DDPPatOrigin.stateFactorization_ctor_of_children lookup aligned
        childrenOrigin
        (aligned.factorPost (Sb.mono ext) instB.2 (expectedBounded.mono ext))
        (DDPPatsOrigin.factorizeCore childrenOrigin closed S₁b instB.1)
  | @DDPPatOrigin.tuple _ q S patterns expected _ _ _ _ _ ledger _ aligned _
      childrenOrigin => by
      have targetsB := freshTargetsSupply_boundedBy patterns.length q
      have ext := SupplyExtends.freshTargets patterns.length q
      have productB := Ty.BoundedBy.prodOfForall targetsB
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) productB
        (expectedBounded.mono ext)
      exact DDPPatOrigin.stateFactorization_tuple_of_children aligned
        childrenOrigin
        (aligned.factorPost (Sb.mono ext) productB (expectedBounded.mono ext))
        (DDPPatsOrigin.factorizeCore childrenOrigin closed S₁b targetsB)

private theorem DDPPatsOrigin.factorizeCore
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q) :
    DDPPatsOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | @DDPPatsOrigin.cons _ _ _ _ _ target _ _ _ _ _ _ _ _ _ _ _ _ _ _
      headOrigin tailOrigin disjoint => by
      have headB : target.BoundedBy q := targetsBounded target (by simp)
      obtain ⟨S₁b, _, _⟩ := headOrigin.erase.boundedBy closed Sb headB
      exact DDPPatsOrigin.stateFactorization_cons headOrigin tailOrigin
        disjoint (DDPPatOrigin.factorizeCore headOrigin closed Sb headB)
        (DDPPatsOrigin.factorizeCore tailOrigin closed S₁b
          (fun target mem =>
            (targetsBounded target (by simp [mem])).mono
              headOrigin.erase.supplyExtends))

end

mutual

theorem DDSynthOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    DDSynthOrigin.StateFactorization origin :=
  match origin with
  | @DDSynthOrigin.var _ q S context name scheme ledger lookup =>
      DDSynthOrigin.stateFactorization_var signature q S context name scheme
        ledger lookup
  | .lam bodyOrigin => by
      have extension := SupplyExtends.bumpTy q 1
      have domainB : Ty.BoundedBy { q with nextTy := q.nextTy + 1 }
          (.var q.nextTy) := Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      exact DDSynthOrigin.stateFactorization_lam_of_body bodyOrigin
        (DDSynthOrigin.factorize bodyOrigin closed (Sb.mono extension)
          (Context.BoundedBy.cons (NamedScheme.BoundedBy.ofMono domainB)
            (contextBounded.mono extension)))
  | @DDSynthOrigin.fix _ q S context self argument _ _ _ _ _ ledger _
      distinct direct nonMatcher _ bodyOrigin aligned => by
      have extension := SupplyExtends.bumpTy q 2
      have domainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var q.nextTy) := Ty.BoundedBy.varOf
        (show q.nextTy < q.nextTy + 2 by omega)
      have codomainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var (q.nextTy + 1)) := Ty.BoundedBy.varOf
        (show q.nextTy + 1 < q.nextTy + 2 by omega)
      have bodyContextB : Context.BoundedBy
          { q with nextTy := q.nextTy + 2 }
          ((argument, NamedScheme.mono (.var q.nextTy)) ::
            (self, NamedScheme.mono
              (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context) :=
        Context.BoundedBy.cons
        (NamedScheme.BoundedBy.ofMono domainB)
        (Context.BoundedBy.cons
          (NamedScheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
          (contextBounded.mono extension))
      obtain ⟨S₁b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
        (Sb.mono extension) bodyContextB
      exact DDSynthOrigin.stateFactorization_fix_of_body distinct direct
        nonMatcher bodyOrigin aligned
        (DDSynthOrigin.factorize bodyOrigin closed (Sb.mono extension)
          bodyContextB) S₁b bodyB
        (codomainB.mono bodyOrigin.erase.supplyExtends)
  | @DDSynthOrigin.app _ q S context _ _ _ q₁ _ _ _ _ _ _ _ _
      functionOrigin aligned _ argumentOrigin => by
      obtain ⟨S₁b, functionB⟩ := functionOrigin.erase.boundedBy closed Sb
        contextBounded
      have extension := SupplyExtends.bumpTy q₁ 2
      have domainB : Ty.BoundedBy
          { q₁ with nextTy := q₁.nextTy + 2 }
          (.var q₁.nextTy) := Ty.BoundedBy.varOf
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
      have codomainB : Ty.BoundedBy
          { q₁ with nextTy := q₁.nextTy + 2 }
          (.var (q₁.nextTy + 1)) := Ty.BoundedBy.varOf
        (Nat.lt_succ_self _)
      have S₂b := aligned.erase.boundedBy (S₁b.mono extension)
        (functionB.mono extension) (Ty.BoundedBy.fnOf domainB codomainB)
      exact DDSynthOrigin.stateFactorization_app_of_children functionOrigin
        aligned argumentOrigin
        (DDSynthOrigin.factorize functionOrigin closed Sb contextBounded)
        (DDCheckOrigin.factorize argumentOrigin closed S₂b
          (contextBounded.mono
            (functionOrigin.erase.supplyExtends.trans extension)) domainB)
        (S₁b.mono extension) (functionB.mono extension)
        (Ty.BoundedBy.fnOf domainB codomainB)
  | .lit => DDSynthOrigin.stateFactorization_lit _ _ _ _ _ _
  | .tuple childrenOrigin =>
      DDSynthOrigin.stateFactorization_tuple_of_children childrenOrigin
        (DDSynthsOrigin.factorize childrenOrigin closed Sb contextBounded)
  | @DDSynthOrigin.ctor _ q S context name _ scheme _ _ ledger _ lookup _
      childrenOrigin => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q scheme
      exact DDSynthOrigin.stateFactorization_ctor_of_children lookup
        childrenOrigin (DDChecksOrigin.factorize childrenOrigin closed
          (Sb.mono ext) (contextBounded.mono ext) instB.1)
  | @DDSynthOrigin.prim _ q S context op _ scheme _ _ ledger _ lookup _
      childrenOrigin => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.primitives lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q scheme
      exact DDSynthOrigin.stateFactorization_prim_of_children lookup
        childrenOrigin (DDChecksOrigin.factorize childrenOrigin closed
          (Sb.mono ext) (contextBounded.mono ext) instB.1)
  | @DDSynthOrigin.letE _ q S context name _ _ valueTarget q₁ S₁ _ _ _ ledger _ _ _
      valueOrigin _ bodyOrigin stable => by
      obtain ⟨S₁b, valueB⟩ := valueOrigin.erase.boundedBy closed Sb
        contextBounded
      have bodyContextB : Context.BoundedBy q₁
          ((name, signature.generalize (context.applySubst S₁)
            (S₁.apply valueTarget)) :: context) := Context.BoundedBy.cons
        (FrozenSig.generalize_boundedBy (S₁b.apply valueB))
        (contextBounded.mono valueOrigin.erase.supplyExtends)
      exact DDSynthOrigin.stateFactorization_let_of_children valueOrigin
        bodyOrigin stable
        (DDSynthOrigin.factorize valueOrigin closed Sb contextBounded)
        (DDSynthOrigin.factorize bodyOrigin closed S₁b bodyContextB)
  | .something => DDSynthOrigin.stateFactorization_something _ _ _ _ _
  | .matcher clausesOrigin collected inferred clauseCaps catchAll binders arms
      coverage => by
      have ext := SupplyExtends.bumpTy q 1
      exact DDSynthOrigin.stateFactorization_matcher_of_clauses clausesOrigin
        collected inferred clauseCaps catchAll binders arms coverage
        (DDClausesOrigin.factorize clausesOrigin closed (Sb.mono ext)
          (contextBounded.mono ext)
          (Ty.BoundedBy.varOf (Nat.lt_succ_self _)))
  | .matchAll targetOrigin patternOrigin targetAligned matcherOrigin
      bodyOrigin => by
      obtain ⟨S₁b, targetB⟩ := targetOrigin.erase.boundedBy closed Sb
        contextBounded
      have ext₁ := targetOrigin.erase.supplyExtends
      obtain ⟨S₂b, dualB, bindingsB⟩ := patternOrigin.erase.boundedBy
        closed S₁b (contextBounded.mono ext₁)
        (fun entry mem => nomatch mem) (fun entry mem => nomatch mem)
      have ext₂ := patternOrigin.erase.supplyExtends
      have S₃b := targetAligned.erase.boundedBy S₂b dualB.2
        (targetB.mono ext₂)
      have matcherExpectedB := Ty.BoundedBy.slotOf dualB.1
        (targetB.mono ext₂)
      have S₄b := matcherOrigin.erase.boundedBy closed S₃b
        (contextBounded.mono (ext₁.trans ext₂)) matcherExpectedB
      have ext₃ := matcherOrigin.erase.supplyExtends
      exact DDSynthOrigin.stateFactorization_matchAll_of_children targetOrigin
        patternOrigin targetAligned matcherOrigin bodyOrigin
        (DDSynthOrigin.factorize targetOrigin closed Sb contextBounded)
        (DDPatternOrigin.factorize patternOrigin closed S₁b
          (contextBounded.mono ext₁) (fun entry mem => nomatch mem)
          (fun entry mem => nomatch mem))
        (DDCheckOrigin.factorize matcherOrigin closed S₃b
          (contextBounded.mono (ext₁.trans ext₂)) matcherExpectedB)
        (DDSynthOrigin.factorize bodyOrigin closed S₄b
          (Context.BoundedBy.append ((bindingsB.mono ext₃).toContext)
            (contextBounded.mono ((ext₁.trans ext₂).trans ext₃))))
        S₂b dualB.2 (targetB.mono ext₂)
  | @DDSynthOrigin.fixMatcher _ q S context self argument _ domain codomain _
      _ _ _ _ ledger _ distinct direct placeholder _ bodyOrigin aligned => by
      obtain ⟨domainB, codomainB⟩ :=
        fixMatcherPlaceholderSupply_boundedBy placeholder
      have ext := SupplyExtends.fixMatcherPlaceholder placeholder
      have bodyContextB : Context.BoundedBy _
          ((argument, NamedScheme.mono domain) ::
            (self, NamedScheme.mono (.fn domain codomain)) :: context) :=
        Context.BoundedBy.cons
        (NamedScheme.BoundedBy.ofMono domainB)
        (Context.BoundedBy.cons
          (NamedScheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
          (contextBounded.mono ext))
      obtain ⟨S₁b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
        (Sb.mono ext) bodyContextB
      exact DDSynthOrigin.stateFactorization_fixMatcher_of_body distinct direct
        placeholder bodyOrigin aligned
        (DDSynthOrigin.factorize bodyOrigin closed (Sb.mono ext) bodyContextB)
        S₁b bodyB (codomainB.mono bodyOrigin.erase.supplyExtends)

theorem DDSynthsOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    DDSynthsOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | .cons headOrigin tailOrigin => by
      obtain ⟨S₁b, _⟩ := headOrigin.erase.boundedBy closed Sb
        contextBounded
      exact DDSynthsOrigin.stateFactorization_cons headOrigin tailOrigin
        (DDSynthOrigin.factorize headOrigin closed Sb contextBounded)
        (DDSynthsOrigin.factorize tailOrigin closed S₁b
          (contextBounded.mono headOrigin.erase.supplyExtends))

theorem DDCheckOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDCheckOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) :
    DDCheckOrigin.StateFactorization origin :=
  match origin with
  | .mk synthOrigin aligned =>
      DDCheckOrigin.stateFactorization_mk_bounded synthOrigin aligned
        (DDSynthOrigin.factorize synthOrigin closed Sb contextBounded)
        closed Sb contextBounded expectedBounded

theorem DDChecksOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDChecksOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedsBounded : ∀ expected ∈ expecteds, expected.BoundedBy q) :
    DDChecksOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | @DDChecksOrigin.cons _ _ _ _ _ _ expected _ _ _ _ _ _ _ _ _ _
      headOrigin tailOrigin => by
      have headB : expected.BoundedBy q := expectedsBounded expected (by simp)
      have S₁b := headOrigin.erase.boundedBy closed Sb contextBounded headB
      exact DDChecksOrigin.stateFactorization_cons headOrigin tailOrigin
        (DDCheckOrigin.factorize headOrigin closed Sb contextBounded headB)
        (DDChecksOrigin.factorize tailOrigin closed S₁b
          (contextBounded.mono headOrigin.erase.supplyExtends)
          (fun expected mem =>
            (expectedsBounded expected (by simp [mem])).mono
              headOrigin.erase.supplyExtends))

theorem DDPatternOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    DDPatternOrigin.StateFactorization origin :=
  match origin with
  | .pvar freshName =>
      DDErasure.StateFactorization.ofTransition
        (SupplyExtends.bumpBoth q 1 1)
        (DDLedger.RefinesBelow.markFreshCap q ledger)
  | .wild => DDPatternOrigin.stateFactorization_wild _ _ _ _ _ _ _
  | .pval expressionOrigin => by
      have expressionFactor := DDSynthOrigin.factorize expressionOrigin closed
        Sb (Context.BoundedBy.append bindingsBounded.toContext contextBounded)
      exact expressionFactor.trans
        (DDErasure.StateFactorization.ofTransition
          (SupplyExtends.bumpCap _ 1)
          (DDLedger.RefinesBelow.markFreshCap _ _))
  | .embed lookup => DDErasure.StateFactorization.refl _ _ _
  | .ptuple childrenOrigin =>
      DDPatternOrigin.stateFactorization_ptuple_of_children childrenOrigin
        (DDPatternsOrigin.factorize childrenOrigin closed Sb contextBounded
          parametersBounded bindingsBounded)
  | @DDPatternOrigin.pctor _ q S context parameters bindings _ _ entry duals
      bindings' q₁ S₁ S₂ capability q₂ S₃ ledger _ _ lookup _ childrenOrigin
      targetsAligned _ capOrigin compatible => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      have instExt := SupplyExtends.instantiateCtorScheme q entry.scheme
      obtain ⟨S₁b, dualsB, bindingsOutB⟩ :=
        childrenOrigin.erase.boundedBy closed (Sb.mono instExt)
          (contextBounded.mono instExt) (parametersBounded.mono instExt)
          (bindingsBounded.mono instExt)
      have childExt := childrenOrigin.erase.supplyExtends
      have expectedB : ∀ expected ∈
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.1,
          expected.BoundedBy q₁ := by
        intro expected mem
        exact (instB.1 expected mem).mono childExt
      have targetsFactor := targetsAligned.factorPost S₁b dualsB expectedB
      have S₂b := targetsAligned.erase.boundedBy S₁b dualsB expectedB
      have capFactor := DDPatternCtorCapOrigin.factorize capOrigin S₂b
        (fun child mem => by
          obtain ⟨item, itemMem, rfl⟩ := List.mem_map.mp mem
          exact (dualsB item itemMem).1)
      exact DDPatternOrigin.stateFactorization_pctor_of_children lookup
        childrenOrigin targetsAligned capOrigin compatible
        (DDPatternsOrigin.factorize childrenOrigin closed (Sb.mono instExt)
          (contextBounded.mono instExt) (parametersBounded.mono instExt)
          (bindingsBounded.mono instExt)) targetsFactor capFactor
  | .pand leftOrigin rightOrigin aligned => by
      obtain ⟨S₁b, leftDualB, leftBindingsB⟩ :=
        leftOrigin.erase.boundedBy closed Sb contextBounded parametersBounded
          bindingsBounded
      have ext₁ := leftOrigin.erase.supplyExtends
      obtain ⟨S₂b, rightDualB, _⟩ := rightOrigin.erase.boundedBy closed
        S₁b (contextBounded.mono ext₁) (parametersBounded.mono ext₁)
        leftBindingsB
      have ext₂ := rightOrigin.erase.supplyExtends
      have alignFactor := aligned.factorPost S₂b
        (leftDualB.mono ext₂) rightDualB
      exact DDPatternOrigin.stateFactorization_pand_of_children leftOrigin
        rightOrigin aligned
        (DDPatternOrigin.factorize leftOrigin closed Sb contextBounded
          parametersBounded bindingsBounded)
        (DDPatternOrigin.factorize rightOrigin closed S₁b
          (contextBounded.mono ext₁) (parametersBounded.mono ext₁)
          leftBindingsB) alignFactor
  | .por leftOrigin rightOrigin dualsAligned bindingsAligned => by
      obtain ⟨S₁b, leftDualB, leftBindingsB⟩ :=
        leftOrigin.erase.boundedBy closed Sb contextBounded parametersBounded
          bindingsBounded
      have ext₁ := leftOrigin.erase.supplyExtends
      obtain ⟨S₂b, rightDualB, rightBindingsB⟩ :=
        rightOrigin.erase.boundedBy closed S₁b
          (contextBounded.mono ext₁) (parametersBounded.mono ext₁)
          (bindingsBounded.mono ext₁)
      have ext₂ := rightOrigin.erase.supplyExtends
      have dualFactor := dualsAligned.factorPost S₂b
        (leftDualB.mono ext₂) rightDualB
      have S₃b := dualsAligned.erase.boundedBy S₂b
        (leftDualB.mono ext₂) rightDualB
      have bindingFactor := bindingsAligned.factorPost S₃b
        (fun entry mem => (leftBindingsB.mono ext₂) entry mem)
        (fun entry mem => rightBindingsB entry mem)
      exact DDPatternOrigin.stateFactorization_por_of_children leftOrigin
        rightOrigin dualsAligned bindingsAligned
        (DDPatternOrigin.factorize leftOrigin closed Sb contextBounded
          parametersBounded bindingsBounded)
        (DDPatternOrigin.factorize rightOrigin closed S₁b
          (contextBounded.mono ext₁) (parametersBounded.mono ext₁)
          (bindingsBounded.mono ext₁)) dualFactor bindingFactor
  | @DDPatternOrigin.papp _ q S context parameters bindings _ _ scheme duals
      _ q₁ _ _ ledger _ lookup _ childrenOrigin aligned => by
      have instB := instantiateDualScheme_boundedBy (q := q)
        ((closed.patternFuns lookup).boundedBy)
      have instExt := SupplyExtends.instantiateDualScheme q scheme
      obtain ⟨S₁b, dualsB, _⟩ := childrenOrigin.erase.boundedBy closed
        (Sb.mono instExt) (contextBounded.mono instExt)
        (parametersBounded.mono instExt) (bindingsBounded.mono instExt)
      have childExt := childrenOrigin.erase.supplyExtends
      have expectedB : ∀ item ∈
          (InferenceBase.instantiateDualScheme q scheme).value.1,
          item.BoundedBy q₁ := by
        intro item mem
        exact ⟨(instB.1 item mem).1.mono childExt,
          (instB.1 item mem).2.mono childExt⟩
      exact DDPatternOrigin.stateFactorization_papp_of_children lookup
        childrenOrigin aligned
        (DDPatternsOrigin.factorize childrenOrigin closed (Sb.mono instExt)
          (contextBounded.mono instExt) (parametersBounded.mono instExt)
          (bindingsBounded.mono instExt))
        (aligned.factorPost S₁b dualsB expectedB)

theorem DDPatternsOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    DDPatternsOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | .cons headOrigin tailOrigin => by
      obtain ⟨S₁b, _, bindings₁B⟩ := headOrigin.erase.boundedBy closed Sb
        contextBounded parametersBounded bindingsBounded
      have ext := headOrigin.erase.supplyExtends
      exact DDPatternsOrigin.stateFactorization_cons headOrigin tailOrigin
        (DDPatternOrigin.factorize headOrigin closed Sb contextBounded
          parametersBounded bindingsBounded)
        (DDPatternsOrigin.factorize tailOrigin closed S₁b
          (contextBounded.mono ext) (parametersBounded.mono ext) bindings₁B)

theorem DDArmsOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDArmsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (bindingsBounded : MonoCtx.BoundedBy q ppBindings)
    (clauseBounded : clauseTarget.BoundedBy q)
    (bodyBounded : bodyTarget.BoundedBy q) :
    DDArmsOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | .cons patternOrigin disjoint bodyOrigin tailOrigin => by
      obtain ⟨S₁b, armBindingsB⟩ := patternOrigin.erase.boundedBy closed
        Sb clauseBounded
      have ext₁ := patternOrigin.erase.supplyExtends
      have bodyContextB := Context.BoundedBy.append
        (Context.BoundedBy.append armBindingsB.toContext
          ((bindingsBounded.mono ext₁).toContext))
        (contextBounded.mono ext₁)
      have S₂b := bodyOrigin.erase.boundedBy closed S₁b bodyContextB
        (bodyBounded.mono ext₁)
      have ext₂ := bodyOrigin.erase.supplyExtends
      exact DDArmsOrigin.stateFactorization_cons patternOrigin disjoint
        bodyOrigin tailOrigin
        (DDDPatOrigin.factorize patternOrigin closed Sb clauseBounded)
        (DDCheckOrigin.factorize bodyOrigin closed S₁b bodyContextB
          (bodyBounded.mono ext₁))
        (DDArmsOrigin.factorize tailOrigin closed S₂b
          (contextBounded.mono (ext₁.trans ext₂))
          (bindingsBounded.mono (ext₁.trans ext₂))
          (clauseBounded.mono (ext₁.trans ext₂))
          (bodyBounded.mono (ext₁.trans ext₂)))

theorem DDClauseOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDClauseOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q) :
    DDClauseOrigin.StateFactorization origin :=
  match origin with
  | @DDClauseOrigin.mk _ q S context _ _ _ sharedTarget holes _ _ q₁ _ _
      _ _ _ _ _ _ _ _ ppOrigin decomposed _ nextOrigin _ armsOrigin => by
      obtain ⟨S₁b, holesB, ppBindingsB⟩ := ppOrigin.erase.boundedBy closed
        Sb sharedBounded
      have ext₁ := ppOrigin.erase.supplyExtends
      have nextExpectedB : ∀ expected ∈
          (holes.map fun hole => Ty.slot hole.cap hole.target),
          expected.BoundedBy q₁ := by
        intro expected mem
        obtain ⟨hole, holeMem, rfl⟩ := List.mem_map.mp mem
        exact Ty.BoundedBy.slotOf (holesB hole holeMem).1
          (holesB hole holeMem).2
      have S₂b := nextOrigin.erase.boundedBy closed S₁b
        (contextBounded.mono ext₁) nextExpectedB
      have ext₂ := nextOrigin.erase.supplyExtends
      have armBodyB := listT_boundedBy (prodTy_boundedBy (fun target mem => by
        obtain ⟨hole, holeMem, rfl⟩ := List.mem_map.mp mem
        exact (holesB hole holeMem).2.mono ext₂))
      exact DDClauseOrigin.stateFactorization_mk ppOrigin decomposed nextOrigin
        armsOrigin (DDPPatOrigin.factorizeCore ppOrigin closed Sb sharedBounded)
        (DDChecksOrigin.factorize nextOrigin closed S₁b
          (contextBounded.mono ext₁) nextExpectedB)
        (DDArmsOrigin.factorize armsOrigin closed S₂b
          (contextBounded.mono (ext₁.trans ext₂))
          (ppBindingsB.mono ext₂)
          (sharedBounded.mono (ext₁.trans ext₂)) armBodyB)

theorem DDClausesOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q'
      S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDClausesOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q) :
    DDClausesOrigin.StateFactorization origin :=
  match origin with
  | .nil => DDErasure.StateFactorization.refl _ _ _
  | .cons headOrigin tailOrigin => by
      obtain ⟨S₁b, _⟩ := headOrigin.erase.boundedBy closed Sb
        contextBounded sharedBounded
      have ext := headOrigin.erase.supplyExtends
      exact DDClausesOrigin.stateFactorization_cons headOrigin tailOrigin
        (DDClauseOrigin.factorize headOrigin closed Sb contextBounded
          sharedBounded)
        (DDClausesOrigin.factorize tailOrigin closed S₁b
          (contextBounded.mono ext) (sharedBounded.mono ext))

end

/-- Public primitive-pattern closure.  The shared private core is declared
before the expression/pattern mutual block so clause factorization can reuse
it without duplicating the structural recursion. -/
theorem DDPPatOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    DDPPatOrigin.StateFactorization origin :=
  DDPPatOrigin.factorizeCore origin closed Sb expectedBounded

/-- Primitive-pattern lists factor by recursively composing head and tail. -/
theorem DDPPatsOrigin.factorize
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q) :
    DDPPatsOrigin.StateFactorization origin :=
  DDPPatsOrigin.factorizeCore origin closed Sb targetsBounded

end TypePM
