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

end DemandTypingInferenceCompletenessPrimitivePatternCertified
end TypePM
