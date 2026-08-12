import TypePM.DemandTypingInferenceCompletenessMain
import TypePM.DemandTypingInferenceCompletenessCertifiedRun
import TypePM.DemandTypingInferenceCompletenessSignatureBounds

/-!
# Validator-certified primitive-pattern completeness

This leaf module adds exact validator chronology to the already complete raw
primitive-pattern recursion.  Keeping this layer separate avoids adding
validator fields to the mutually recursive raw completion packages.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPrimitivePatternCertified

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessSignatureBounds

structure BoundedCertifiedPPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  certified : CertifiedPPatRunCompletion terminal signature before operation
    q' declarative ledger target holes bindings
  rawTargetBounded : certified.run.result.target.BoundedBy q'
  rawHolesBounded : ∀ hole ∈ certified.run.result.holes,
    Dual.BoundedBy q' hole
  rawBindingsBounded : certified.run.result.bindings.BoundedBy q'

structure BoundedCertifiedDPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  certified : CertifiedDPatRunCompletion terminal signature before operation
    q' declarative ledger target bindings
  rawTargetBounded : certified.run.result.target.BoundedBy q'
  rawBindingsBounded : certified.run.result.bindings.BoundedBy q'

/-! ## Validator chronology combinators -/

theorem finishPPat
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx} {path : SyntaxPath}
    (neutral : pattern ≠ .hole) :
    ValidatorRunExtension terminal signature state
      ((visit state (match pattern with
        | .hole => .ppatHole | .wild => .ppatWild | .pval _ => .ppatValue
        | .ctor _ _ => .ppatCtor | .tuple _ => .ppatTuple) path).recordEvent
          (.inferredPPat pattern target holes bindings path)) := by
  cases pattern with
  | hole => contradiction
  | wild =>
      exact (ValidatorRunExtension.visit terminal signature state .ppatWild
        path).trans (ValidatorRunExtension.recordNeutral
          (.inferredPPatWild target holes bindings path))
  | pval name =>
      exact (ValidatorRunExtension.visit terminal signature state .ppatValue
        path).trans (ValidatorRunExtension.recordNeutral
          (.inferredPPatValue name target holes bindings path))
  | ctor name patterns =>
      exact (ValidatorRunExtension.visit terminal signature state .ppatCtor
        path).trans (ValidatorRunExtension.recordNeutral
          (.inferredPPatCtor name patterns target holes bindings path))
  | tuple patterns =>
      exact (ValidatorRunExtension.visit terminal signature state .ppatTuple
        path).trans (ValidatorRunExtension.recordNeutral
          (.inferredPPatTuple patterns target holes bindings path))

theorem finishDPat
    {terminal : Subst} {signature : FrozenSig} {state : InferState}
    (pattern : DPat) (target : Ty) (bindings : MonoCtx) (path : SyntaxPath) :
    ValidatorRunExtension terminal signature state
      ((visit state (match pattern with
        | .var _ => .dpatVar | .wild => .dpatWild
        | .ctor _ _ => .dpatCtor | .tuple _ => .dpatTuple) path).recordEvent
          (.inferredDPat pattern target bindings path)) := by
  let kind := match pattern with
    | .var _ => NodeKind.dpatVar | .wild => .dpatWild
    | .ctor _ _ => .dpatCtor | .tuple _ => .dpatTuple
  exact (ValidatorRunExtension.visit terminal signature state kind path).trans
    (ValidatorRunExtension.recordNeutral
      (.inferredDPat pattern target bindings path))

theorem freshTargetsValidation
    (terminal : Subst) (signature : FrozenSig) (state : InferState)
    (origin : ConstraintOrigin) : ∀ count,
    ValidatorRunExtension terminal signature state
      (freshTargets state origin count).2
  | 0 => ValidatorRunExtension.refl terminal signature state
  | count + 1 =>
      (ValidatorRunExtension.freshTy terminal signature state origin).trans
        (freshTargetsValidation terminal signature (state.freshTy origin).2
          origin count)

/-! ## Complete data-pattern chronology -/

mutual

theorem inferDPatFuel_validation
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed) :
    ∀ {fuel path pattern target state result},
      SignatureVarsBelow state.supply signature →
      target.BoundedBy state.supply →
      inferDPatFuel fuel signature path pattern target state = some result →
      ValidatorRunExtension terminal signature state result.state
  | 0, path, pattern, target, state, result, signatureBelow, targetBounded,
      success => by simp [inferDPatFuel] at success
  | fuel + 1, path, .var name, target, state, result, signatureBelow,
      targetBounded, success => by
      simp only [inferDPatFuel, Option.some.injEq] at success
      subst result
      exact finishDPat (.var name) target [(name, target)] path
  | fuel + 1, path, .wild, target, state, result, signatureBelow,
      targetBounded, success => by
      simp only [inferDPatFuel, Option.some.injEq] at success
      subst result
      exact finishDPat .wild target [] path
  | fuel + 1, path, .ctor name patterns, target, state, result,
      signatureBelow, targetBounded, success => by
      simp only [inferDPatFuel] at success
      cases lookup : signature.findDataCtor name with
      | none => simp [lookup] at success
      | some scheme =>
          simp only [lookup] at success
          cases alignedEq : alignTypes (instantiateCtorInState state scheme).2
              (freshOrigin .dataPattern path "dp-constructor-result")
              (instantiateCtorInState state scheme).1.2 target with
          | none =>
              have alignedCoreEq :
                  alignTypes (instantiateCtorInState state scheme).2
                    (freshOrigin .dataPattern path "dp-constructor-result")
                    (InferenceBase.instantiateCtorScheme state.supply scheme).value.2
                    target = none := by
                simpa [Inference.instantiateCtorInState] using alignedEq
              simp [alignedCoreEq] at success
          | some aligned =>
              have alignedCoreEq :
                  alignTypes (instantiateCtorInState state scheme).2
                    (freshOrigin .dataPattern path "dp-constructor-result")
                    (InferenceBase.instantiateCtorScheme state.supply scheme).value.2
                    target = some aligned := by
                simpa [Inference.instantiateCtorInState] using alignedEq
              cases childrenEq : inferDPatsFuel fuel signature path 0 patterns
                  (instantiateCtorInState state scheme).1.1 aligned with
              | none =>
                  have childrenCoreEq :
                      inferDPatsFuel fuel signature path 0 patterns
                        (InferenceBase.instantiateCtorScheme state.supply scheme).value.1
                        aligned = none := by
                    simpa [Inference.instantiateCtorInState] using childrenEq
                  simp [alignedCoreEq, childrenCoreEq] at success
              | some children =>
                  have childrenCoreEq :
                      inferDPatsFuel fuel signature path 0 patterns
                        (InferenceBase.instantiateCtorScheme state.supply scheme).value.1
                        aligned = some children := by
                    simpa [Inference.instantiateCtorInState] using childrenEq
                  simp [alignedCoreEq, childrenCoreEq] at success
                  subst result
                  have instantiateRun :=
                    ValidatorRunExtension.instantiateCtorInState
                      (terminal := terminal) (signature := signature) state scheme
                      (closed.dataCtors lookup)
                  have alignRun := ValidatorRunExtension.ofAlignTypes
                    (terminal := terminal) (signature := signature) alignedEq
                  have initialExtends :=
                    Inference.instantiateCtorInState_stateExtension state scheme
                  have alignmentExtends :=
                    Inference.alignTypes_stateExtension alignedEq
                  have instBounded := instantiateCtorScheme_boundedBy
                    (q := state.supply) ((closed.dataCtors lookup).boundedBy)
                  have childrenRun := inferDPatsFuel_validation
                    (terminal := terminal) closed
                    (signatureBelow.mono
                      ⟨Nat.le_trans initialExtends.supplyCap
                          alignmentExtends.supplyCap,
                        Nat.le_trans initialExtends.supplyTy
                          alignmentExtends.supplyTy⟩)
                    (fun item membership =>
                      (instBounded.1 item (by
                        simpa [Inference.instantiateCtorInState] using membership)
                      ).mono
                        ⟨alignmentExtends.supplyCap,
                          alignmentExtends.supplyTy⟩)
                    childrenEq
                  let images := freshCapImages state.supply scheme.capBinders
                  let payload := capabilityExportPayload []
                    (target :: children.bindings.map fun entry => entry.2)
                  exact instantiateRun.trans (alignRun.trans
                    (childrenRun.trans
                      ((ValidatorRunExtension.freezeCapabilityExport terminal
                        signature children.state images payload).trans
                        (finishDPat (.ctor name patterns) target
                          children.bindings path))))
  | fuel + 1, path, .tuple patterns, target, state, result, signatureBelow,
      targetBounded, success => by
      simp only [inferDPatFuel] at success
      cases alignedEq : alignTypes
          (freshTargets state
            (freshOrigin .dataPattern path "dp-tuple-field") patterns.length).2
          (freshOrigin .dataPattern path "dp-tuple-result")
          (.prod (freshTargets state
            (freshOrigin .dataPattern path "dp-tuple-field") patterns.length).1)
          target with
      | none => simp [alignedEq] at success
      | some aligned =>
          cases childrenEq : inferDPatsFuel fuel signature path 0 patterns
              (freshTargets state
                (freshOrigin .dataPattern path "dp-tuple-field") patterns.length).1
              aligned with
          | none => simp [alignedEq, childrenEq] at success
          | some children =>
              simp [alignedEq, childrenEq] at success
              subst result
              have allocationRun := freshTargetsValidation terminal signature
                state (freshOrigin .dataPattern path "dp-tuple-field")
                  patterns.length
              have allocationExtends := Inference.freshTargets_stateExtension
                (state := state)
                (result := (freshTargets state
                  (freshOrigin .dataPattern path "dp-tuple-field")
                  patterns.length).2)
                (targets := (freshTargets state
                  (freshOrigin .dataPattern path "dp-tuple-field")
                  patterns.length).1)
                (origin := freshOrigin .dataPattern path "dp-tuple-field")
                (count := patterns.length) rfl
              have alignmentRun := ValidatorRunExtension.ofAlignTypes
                (terminal := terminal) (signature := signature) alignedEq
              have alignmentExtends := Inference.alignTypes_stateExtension alignedEq
              have targetsBounded := freshTargetsSupply_boundedBy
                patterns.length state.supply
              have allocatedEq := Inference.freshTargets_eq_freshTargetsSupply
                patterns.length state
                  (freshOrigin .dataPattern path "dp-tuple-field")
              have childrenRun := inferDPatsFuel_validation
                (terminal := terminal) closed
                (signatureBelow.mono
                  ⟨Nat.le_trans allocationExtends.supplyCap
                      alignmentExtends.supplyCap,
                    Nat.le_trans allocationExtends.supplyTy
                      alignmentExtends.supplyTy⟩)
                (fun item membership => by
                  have twinMembership : item ∈
                      (freshTargetsSupply patterns.length state.supply).1 := by
                    rw [← allocatedEq.1]
                    exact membership
                  have allocatedBound := targetsBounded item twinMembership
                  have supplyEq := allocatedEq.2.1
                  rw [← supplyEq] at allocatedBound
                  exact allocatedBound.mono
                    ⟨alignmentExtends.supplyCap, alignmentExtends.supplyTy⟩)
                childrenEq
              exact allocationRun.trans (alignmentRun.trans
                (childrenRun.trans
                  (finishDPat (.tuple patterns) target children.bindings path)))

theorem inferDPatsFuel_validation
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed) :
    ∀ {fuel parent index patterns targets state result},
      SignatureVarsBelow state.supply signature →
      (∀ target ∈ targets, target.BoundedBy state.supply) →
      inferDPatsFuel fuel signature parent index patterns targets state =
        some result →
      ValidatorRunExtension terminal signature state result.state
  | 0, parent, index, patterns, targets, state, result, signatureBelow,
      targetsBounded, success => by simp [inferDPatsFuel] at success
  | fuel + 1, parent, index, [], [], state, result, signatureBelow,
      targetsBounded, success => by
      simp only [inferDPatsFuel, Option.some.injEq] at success
      subst result
      exact ValidatorRunExtension.refl terminal signature state
  | fuel + 1, parent, index, [], _ :: _, state, result, signatureBelow,
      targetsBounded, success => by simp [inferDPatsFuel] at success
  | fuel + 1, parent, index, _ :: _, [], state, result, signatureBelow,
      targetsBounded, success => by simp [inferDPatsFuel] at success
  | fuel + 1, parent, index, pattern :: patterns, target :: targets, state,
      result, signatureBelow, targetsBounded, success => by
      simp only [inferDPatsFuel] at success
      cases headEq : inferDPatFuel fuel signature (index :: parent) pattern
          target state with
      | none => simp [headEq] at success
      | some head =>
          cases tailEq : inferDPatsFuel fuel signature parent (index + 1)
              patterns targets head.state with
          | none => simp [headEq, tailEq] at success
          | some tail =>
              by_cases distinct : namesDisjoint head.bindings.names
                  tail.bindings.names = true
              · simp [headEq, tailEq, distinct] at success
                subst result
                have headRun := inferDPatFuel_validation
                  (terminal := terminal) closed signatureBelow
                  (targetsBounded target (by simp)) headEq
                have extension := Inference.inferDPatFuel_stateExtension headEq
                have tailRun := inferDPatsFuel_validation
                  (terminal := terminal) closed
                  (signatureBelow.mono
                    ⟨extension.supplyCap, extension.supplyTy⟩)
                  (fun item membership =>
                    (targetsBounded item (by simp [membership])).mono
                      ⟨extension.supplyCap, extension.supplyTy⟩) tailEq
                exact headRun.trans tailRun
              · simp [headEq, tailEq, distinct] at success

end

/-! ## Primitive-pattern chronology -/

/-- A primitive hole allocates its capability before emitting the leaf event. -/
theorem inferPPatFuel_hole_validation
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {path : SyntaxPath} {target : Ty} {state : InferState}
    {result : PPatResult}
    (signatureBelow : SignatureVarsBelow state.supply signature)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferPPatFuel (fuel + 1) signature path .hole target state =
      some result) :
    ValidatorRunExtension terminal signature state result.state := by
  simp only [inferPPatFuel, Option.some.injEq] at success
  subst result
  let allocated := (state.freshCap
    (freshOrigin .primitivePattern path "primitive-hole")).2
  have freshRun := ValidatorRunExtension.freshCap terminal signature state
    (freshOrigin .primitivePattern path "primitive-hole")
  have visitRun := ValidatorRunExtension.visit terminal signature allocated
    .ppatHole path
  have eventRun : ValidatorRunExtension terminal signature
      (visit allocated .ppatHole path)
      ((visit allocated .ppatHole path).recordEvent
        (.inferredPPat .hole target
          [Dual.mk (.var ⟨state.supply.nextCap⟩) target] [] path)) := by
    apply ValidatorRunExtension.recordOrdinaryEvent
    · intro future extension producerSafe
      exact Inference.Reconstruction.primitiveHole_ordinaryValidatorEventCondition
        signatureBelow.caps targetBounded
    · simp [Inference.Reconstruction.TerminalAuditSensitiveEvent]
  exact freshRun.trans (visitRun.trans eventRun)

/-- Non-hole primitive leaves emit only their neutral visit and result events. -/
theorem inferPPatFuel_leaf_validation
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {path : SyntaxPath} {pattern : PPat} {target : Ty} {state : InferState}
    {result : PPatResult}
    (leaf : pattern = .wild ∨ ∃ name, pattern = .pval name)
    (success : inferPPatFuel (fuel + 1) signature path pattern target state =
      some result) :
    ValidatorRunExtension terminal signature state result.state := by
  rcases leaf with rfl | ⟨name, rfl⟩
  · simp only [inferPPatFuel, Option.some.injEq] at success
    subst result
    exact finishPPat (pattern := .wild) (target := target) (holes := [])
      (bindings := []) (path := path) (by simp)
  · simp only [inferPPatFuel, Option.some.injEq] at success
    subst result
    exact finishPPat (pattern := .pval name) (target := target) (holes := [])
      (bindings := [(name, target)]) (path := path) (by simp)

/-! ## Packaging adapters -/

/-- Attach the independently reconstructed DPat validator chronology to any
bounded raw matcher-arm completion. -/
def certifyBoundedDPatRun
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {fuel : Nat} {path : SyntaxPath} {pattern : DPat}
    {target : Ty} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {before : TraversalStateCorrespondence q S ledger state}
    (signatureBelow : SignatureVarsBelow q signature)
    (executableTargetBounded : target.BoundedBy q)
    (raw : BoundedDPatRunCompletion before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings) :
    BoundedCertifiedDPatRunCompletion terminal signature before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings := by
  have signatureBelowState : SignatureVarsBelow state.supply signature := by
    rw [before.supply_eq]
    exact signatureBelow
  have targetBoundedState : target.BoundedBy state.supply := by
    rw [before.supply_eq]
    exact executableTargetBounded
  refine
    { certified :=
        { run := raw.run
          validation := inferDPatFuel_validation closed signatureBelowState
            targetBoundedState raw.run.success }
      rawTargetBounded := raw.rawTargetBounded
      rawBindingsBounded := raw.rawBindingsBounded }

/-! These executable-history theorems are deliberately independent of the
raw DD origin.  A raw completion and the corresponding validation proof can
therefore be paired after the global recursion chooses its exact run. -/

end DemandTypingInferenceCompletenessPrimitivePatternCertified
end TypePM
