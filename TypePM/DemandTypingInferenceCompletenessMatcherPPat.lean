import TypePM.DemandTypingInferenceCompletenessMatcherMain
import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal

/-!
# Heterogeneous primitive matcher-pattern completeness

Matcher clauses pass a raw DD target and a possibly renamed executable target.
This module generalizes primitive matcher-pattern traversal over that pair.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherPPat

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherMain

theorem StateBisimulation.sameTargets
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    (relation : StateBisimulation ledger S state) : ∀ targets,
    TyListBisimulation relation targets targets
  | [] => .nil
  | target :: targets => .cons (relation.sameTarget target)
      (StateBisimulation.sameTargets relation targets)

theorem StateBisimulation.sameTargetsOfEq
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    (relation : StateBisimulation ledger S state) {left right : List Ty}
    (equal : left = right) : TyListBisimulation relation left right := by
  subst right
  exact StateBisimulation.sameTargets relation left

def ppatWild_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .wild executableTarget state)
      q S ledger target [] [] := by
  let run := ppatWild_complete fuel signature path before executableTarget
  exact { run with
    target := (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .ppatWild path
      (.inferredPPat .wild executableTarget [] [] path)).transportTy related }

def ppatValue_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.pval name) executableTarget state)
      q S ledger target [] [(name, target)] := by
  let run := ppatValue_complete fuel signature path name before executableTarget
  exact { run with
    target := (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .ppatValue path
      (.inferredPPat (.pval name) executableTarget []
        [(name, executableTarget)] path)).transportTy related
    bindings := .cons
      ((DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
        before .ppatValue path
        (.inferredPPat (.pval name) executableTarget []
          [(name, executableTarget)] path)).transportTy related) .nil }

def ppatHole_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .hole executableTarget state)
      { q with nextCap := q.nextCap + 1 } S
      (DDLedger.markFreshCap ledger q) target
      [⟨.var ⟨q.nextCap⟩, target⟩] [] := by
  let run := ppatHole_complete fuel signature path before executableTarget
  let transported := run.transition.transportTy related
  have capabilityEq :
      (state.freshCap
        (freshOrigin .primitivePattern path "primitive-hole")).1 =
        .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  exact { run with
    target := transported
    holes := .cons
      ⟨by rw [capabilityEq]
          exact CapBisimulation.same run.transition.after (.var ⟨q.nextCap⟩),
        transported⟩ .nil }

structure BoundedPPatsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatsResult) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger' : CapabilityOriginLedger)
    (targets : List Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  run : PPatsRunCompletion before operation q' S' ledger' targets holes bindings
  rawTargetsBounded : ∀ target ∈ run.result.targets, target.BoundedBy q'
  rawHolesBounded : ∀ hole ∈ run.result.holes, Dual.BoundedBy q' hole
  rawBindingsBounded : run.result.bindings.BoundedBy q'

noncomputable def ppatCtor_complete_related_bounded
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    (patterns : List PPat) {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (closed : signature.SchemesClosed)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (targetRelated : TyBisimulation before.prevailing target executableTarget)
    (targetBounded : target.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q entry.scheme) S
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2 target S₁)
    {q' : InferenceBase.FreshSupply} {holes : List Dual}
    {bindings : MonoCtx}
    (targetFinalBounded : executableTarget.BoundedBy q')
    (children :
      let instantiation := instantiateCtorInState_complete before entry.scheme
      ∀ alignment : StateRunCompletion instantiation.correspondence
          (alignTypes (instantiateCtorInState state entry.scheme).2
            (freshOrigin .primitivePattern path "pp-constructor-result")
            (instantiateCtorInState state entry.scheme).1.2 executableTarget)
          (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
          (DDLedger.markCtorInstance ledger q entry.scheme),
        BoundedPPatsRunCompletion alignment.completion
          (inferPPatsFuel fuel signature path 0 patterns
            (instantiateCtorInState state entry.scheme).1.1 alignment.result)
          q' S' ledger₂
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 holes
          bindings) :
    BoundedPPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.ctor name patterns)
        executableTarget state)
      q' S' (DDLedger.freezeExport ledger₂ S'
        (freshCapImages q entry.scheme.capBinders)
        (capabilityExportPayload (holes.map Dual.cap)
          (holes.map Dual.target ++ target :: bindings.map fun item => item.2)))
      target holes bindings := by
  let raw := ppatCtor_complete fuel signature path name patterns lookup closed
    before target executableTarget targetRelated targetBounded
    executableTargetBounded aligned
    (children := fun alignment => (children alignment).run)
  let instantiation := instantiateCtorInState_complete before entry.scheme
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.patternCtors lookup).boundedBy)
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .primitivePattern path "pp-constructor-result")
    instantiation.correspondence instantiation.target
    (instantiation.transition.transportTy targetRelated)
    instBounded.2
    (targetBounded.mono (SupplyExtends.instantiateCtorScheme q entry.scheme))
    (by simpa [Inference.instantiateCtorInState, before.supply_eq] using
      instBounded.2)
    (executableTargetBounded.mono
      (SupplyExtends.instantiateCtorScheme q entry.scheme)) aligned
  exact ⟨raw, targetFinalBounded, (children alignment).rawHolesBounded,
    (children alignment).rawBindingsBounded⟩

noncomputable def ppatTuple_complete_related_bounded
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    (patterns : List PPat)
    {q : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (targetRelated : TyBisimulation before.prevailing target executableTarget)
    (targetBounded : target.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) target S₁)
    {q' : InferenceBase.FreshSupply} {holes : List Dual}
    {bindings : MonoCtx}
    (targetFinalBounded : executableTarget.BoundedBy q')
    (children :
      let fresh := freshTargets_complete before
        (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length
      ∀ alignment : StateRunCompletion fresh.state
          (alignTypes (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).2
            (freshOrigin .primitivePattern path "pp-tuple-result")
            (.prod (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).1) executableTarget)
          (freshTargetsSupply patterns.length q).2 S₁ ledger,
        BoundedPPatsRunCompletion alignment.completion
          (inferPPatsFuel fuel signature path 0 patterns
            (freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length).1 alignment.result)
          q' S' ledger₂ (freshTargetsSupply patterns.length q).1 holes
          bindings) :
    BoundedPPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.tuple patterns)
        executableTarget state)
      q' S' ledger₂ target holes bindings := by
  let raw := ppatTuple_complete fuel signature path patterns before target
    executableTarget targetRelated targetBounded executableTargetBounded aligned
    (children := fun alignment => (children alignment).run)
  let fresh := freshTargets_complete before
    (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length
  let targetsBounded := freshTargetsSupply_boundedBy patterns.length q
  have productRelated : TyBisimulation fresh.state.prevailing
      (.prod (freshTargetsSupply patterns.length q).1)
      (.prod (freshTargets state
        (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length).1) := by
    rw [fresh.targets_eq]
    exact fresh.state.prevailing.sameTarget _
  have productBounded : Ty.BoundedBy
      (freshTargetsSupply patterns.length q).2
      (.prod (freshTargets state
        (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length).1) := by
    rw [fresh.targets_eq]
    exact Ty.BoundedBy.prodOfForall targetsBounded
  let alignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .primitivePattern path "pp-tuple-result") fresh.state
    productRelated (fresh.extension.transportTy targetRelated)
    (Ty.BoundedBy.prodOfForall targetsBounded)
    (targetBounded.mono (SupplyExtends.freshTargets patterns.length q))
    productBounded
    (executableTargetBounded.mono
      (SupplyExtends.freshTargets patterns.length q)) aligned
  exact ⟨raw, targetFinalBounded, (children alignment).rawHolesBounded,
    (children alignment).rawBindingsBounded⟩

mutual

theorem ppatOrigin_complete_related_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : PPat} {target executableTarget : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPat signature q S pattern target holes bindings q' S'}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (targetRelated : TyBisimulation before.prevailing target executableTarget)
    (targetBounded : target.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    (adequate : PPatAdequate fuel pattern) :
    Nonempty (BoundedPPatRunCompletion before
      (inferPPatFuel fuel signature path pattern executableTarget state)
      q' S' ledger' target holes bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | hole =>
      let run := ppatHole_complete_related fuel signature path before targetRelated
      refine ⟨⟨run, executableTargetBounded.mono (.bumpCap q 1), ?_, ?_⟩⟩
      · intro hole membership
        have expected : Dual.BoundedBy { q with nextCap := q.nextCap + 1 }
            ⟨Cap.var ⟨q.nextCap⟩, executableTarget⟩ :=
          ⟨Cap.BoundedBy.varOf (Nat.lt_succ_self _),
            executableTargetBounded.mono (.bumpCap q 1)⟩
        have capabilityEq :
            (state.freshCap
              (freshOrigin .primitivePattern path "primitive-hole")).1 =
              Cap.var ⟨q.nextCap⟩ := by
          change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
          rw [before.supply_eq]
        have holeEq : hole = ⟨Cap.var ⟨q.nextCap⟩, executableTarget⟩ := by
          simpa [run, ppatHole_complete_related, ppatHole_complete,
            capabilityEq] using membership
        subst hole
        exact expected
      · intro entry membership
        change entry ∈ ([] : MonoCtx) at membership
        contradiction
  | wild =>
      let run := ppatWild_complete_related fuel signature path before targetRelated
      exact ⟨⟨run, executableTargetBounded,
        fun _ membership => by contradiction,
        fun _ membership => by contradiction⟩⟩
  | pval =>
      rename_i name
      let run := ppatValue_complete_related fuel signature path name before
        targetRelated
      refine ⟨⟨run, executableTargetBounded,
        fun _ membership => by contradiction, ?_⟩⟩
      intro entry membership
      change entry ∈ [(name, executableTarget)] at membership
      simp only [List.mem_singleton] at membership
      subst entry
      exact executableTargetBounded
  | @ctor q S name patterns target entry S₁ holes bindings q' S'
      ledger ledger₂ lookup aligned childrenRaw childrenOrigin =>
      have childAdequate := ppat_ctor (fuel := fuel) adequate
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      let run := ppatCtor_complete_related_bounded fuel signature path name patterns
        lookup closed before targetRelated targetBounded executableTargetBounded
        aligned (executableTargetBounded.mono
          ((SupplyExtends.instantiateCtorScheme q entry.scheme).trans
            childrenOrigin.erase.supplyExtends))
        (children := by
          dsimp
          intro alignedRun
          have targetsEq :
              (InferenceBase.instantiateCtorScheme state.supply entry.scheme).value.1 =
                (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 := by
            rw [before.supply_eq]
          have targetsRelated : TyListBisimulation alignedRun.completion.prevailing
              (InferenceBase.instantiateCtorScheme q entry.scheme).value.1
              (InferenceBase.instantiateCtorScheme state.supply entry.scheme).value.1 := by
            rw [targetsEq]
            exact StateBisimulation.sameTargets alignedRun.completion.prevailing _
          exact Classical.choice
            (ppatsOrigin_complete_related_nonempty (parent := path) (index := 0)
              closed fuel alignedRun.completion childrenOrigin targetsRelated
              instBounded.1 (fun item membership => by
                rw [targetsEq] at membership
                exact instBounded.1 item membership) childAdequate))
      exact ⟨run⟩
  | @tuple q S patterns target S₁ holes bindings q' S' ledger ledger'
      aligned childrenRaw childrenOrigin =>
      have childAdequate := ppat_tuple (fuel := fuel) adequate
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      let run := ppatTuple_complete_related_bounded fuel signature path patterns
        before targetRelated targetBounded executableTargetBounded aligned
        (executableTargetBounded.mono
          ((SupplyExtends.freshTargets patterns.length q).trans
            childrenOrigin.erase.supplyExtends))
        (children := by
          dsimp
          intro alignedRun
          let fresh := freshTargets_complete before
            (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length
          have targetsRelated : TyListBisimulation alignedRun.completion.prevailing
              (freshTargetsSupply patterns.length q).1
              (freshTargets state
                (freshOrigin .primitivePattern path "pp-tuple-field")
                patterns.length).1 := by
            exact StateBisimulation.sameTargetsOfEq
              alignedRun.completion.prevailing fresh.targets_eq.symm
          exact Classical.choice
            (ppatsOrigin_complete_related_nonempty (parent := path) (index := 0)
              closed fuel alignedRun.completion childrenOrigin targetsRelated
              targetsBounded (fun item membership => by
                rw [fresh.targets_eq] at membership
                exact targetsBounded item membership) childAdequate))
      exact ⟨run⟩
termination_by fuel

theorem ppatsOrigin_complete_related_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat} {patterns : List PPat}
    {targets executableTargets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (targetsRelated : TyListBisimulation before.prevailing targets executableTargets)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q)
    (executableTargetsBounded : ∀ target ∈ executableTargets,
      target.BoundedBy q)
    (adequate : PPatListAdequate fuel patterns) :
    Nonempty (BoundedPPatsRunCompletion before
      (inferPPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' targets holes bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | nil =>
      cases targetsRelated
      exact ⟨⟨ppatsNil_complete fuel signature parent index before,
        fun _ membership => by contradiction,
        fun _ membership => by contradiction,
        fun _ membership => by contradiction⟩⟩
  | @cons q S pattern patterns target targets headHoles tailHoles headBindings
      tailBindings q₁ S₁ q' S' ledger ledger₁ ledger' headRaw tailRaw
      headOrigin tailOrigin disjoint =>
      cases targetsRelated with
      | cons headRelated tailRelated =>
          rename_i executableTarget executableTail
          have childAdequate := ppatList_cons (fuel := fuel) adequate
          let headRun := Classical.choice
            (ppatOrigin_complete_related_nonempty (path := index :: parent)
              closed fuel before headOrigin headRelated
              (targetsBounded target (by simp))
              (executableTargetsBounded executableTarget (by simp))
              childAdequate.1)
          have tailTargetsBounded : ∀ item ∈ targets, item.BoundedBy q₁ := by
            intro item membership
            exact (targetsBounded item (by simp [membership])).mono
              headOrigin.erase.supplyExtends
          have tailExecutableBounded : ∀ item ∈ executableTail,
              item.BoundedBy q₁ := by
            intro item membership
            exact (executableTargetsBounded item (by simp [membership])).mono
              headOrigin.erase.supplyExtends
          let tailRun := Classical.choice
            (ppatsOrigin_complete_related_nonempty (parent := parent)
              (index := index + 1) closed fuel headRun.run.completion tailOrigin
              (headRun.run.transition.transportTyList tailRelated)
              tailTargetsBounded tailExecutableBounded childAdequate.2)
          let run := ppatsCons_complete fuel signature parent index pattern patterns
            before headRun.run tailRun.run disjoint
          refine ⟨⟨run, ?_, ?_, ?_⟩⟩
          · intro item membership
            change item ∈ headRun.run.result.target ::
              tailRun.run.result.targets at membership
            rcases List.mem_cons.mp membership with rfl | membership
            · exact headRun.rawTargetBounded.mono tailOrigin.erase.supplyExtends
            · exact tailRun.rawTargetsBounded item membership
          · intro hole membership
            change hole ∈ headRun.run.result.holes ++
              tailRun.run.result.holes at membership
            rcases List.mem_append.mp membership with membership | membership
            · exact (headRun.rawHolesBounded hole membership).mono
                tailOrigin.erase.supplyExtends
            · exact tailRun.rawHolesBounded hole membership
          · exact MonoCtx.BoundedBy.append
              (headRun.rawBindingsBounded.mono tailOrigin.erase.supplyExtends)
              tailRun.rawBindingsBounded
termination_by fuel

end

theorem matcherPPatCompletenessMotive
    {signature : FrozenSig} (closed : signature.SchemesClosed) :
    MatcherPPatCompletenessMotive signature := by
  intro fuel path pattern target executableTarget holes bindings q q' S S'
    ledger ledger' state raw origin before targetRelated targetBounded
    executableTargetBounded adequate
  exact ppatOrigin_complete_related_nonempty closed fuel before origin
    targetRelated targetBounded executableTargetBounded adequate

end DemandTypingInferenceCompletenessMatcherPPat
end TypePM
