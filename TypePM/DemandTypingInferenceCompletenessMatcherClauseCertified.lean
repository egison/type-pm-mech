import TypePM.DemandTypingInferenceCompletenessCertifiedRun

/-!
# Validator-certified matcher-clause composition

This leaf lifts the raw clause-completion constructors to certified runs.  It
keeps the validator chronology explicit: visit the clause, traverse its
primitive pattern, check the next matchers, then check the arms.  Clause lists
compose the certified head with the certified suffix in the same order.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherClauseCertified

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessCertifiedRun

/-! ## One clause -/

/-- Certified counterpart of `inferClauseFuel_complete`. -/
def inferClauseFuel_complete_certified
    {terminal : Subst} {fuel : Nat} {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {primitivePattern : PPat} {next : Expr} {arms : List Arm}
    {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {nextMatchers : List Expr}
    {q q₁ q₂ q' : InferenceBase.FreshSupply}
    {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (primitive : CertifiedPPatRunCompletion terminal signature
      (before.visit .clause path)
      (inferPPatFuel fuel signature (0 :: path) primitivePattern
        executableTarget (visit state .clause path))
      q₁ S₁ ledger₁ declarativeTarget holes bindings)
    (decomposed : decomposeME next holes.length = some nextMatchers)
    (nextRun : CertifiedStateRunCompletion terminal signature
      primitive.run.completion
      (checkExprsFuel fuel signature context selfEnv (1 :: path) 0
        nextMatchers
        (primitive.run.result.holes.map fun hole => .slot hole.cap hole.target)
        primitive.run.result.state)
      q₂ S₂ ledger₂)
    (armsRun : CertifiedStateRunCompletion terminal signature
      nextRun.run.completion
      (checkArmsFuel fuel signature context selfEnv
        primitive.run.result.bindings (2 :: path) 0 arms executableTarget
        (Ty.listT (prodTy (primitive.run.result.holes.map Dual.target)))
        nextRun.run.result)
      q' S' ledger') :
    CertifiedClauseRunCompletion terminal signature before
      (inferClauseFuel (fuel + 1) signature context selfEnv path
        (.mk primitivePattern next arms) executableTarget state)
      q' S' ledger' declarativeTarget holes := by
  let raw := inferClauseFuel_complete before targetRelated primitive.run
    decomposed nextRun.run armsRun.run
  refine ⟨raw, ?_⟩
  exact (((ValidatorRunExtension.visit terminal signature state .clause path).trans
    primitive.validation).trans nextRun.validation).trans armsRun.validation

/-! ## Clause lists -/

/-- The empty clause list is a certified identity run. -/
def inferClausesFuel_nil_complete_certified
    (terminal : Subst) (fuel : Nat) (signature : FrozenSig)
    (context : Context) (selfEnv : SelfEnv) (parent : SyntaxPath) (index : Nat)
    {declarativeTarget executableTarget : Ty}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget) :
    CertifiedClausesRunCompletion terminal signature before
      (inferClausesFuel (fuel + 1) signature context selfEnv parent index []
        executableTarget state)
      q S ledger declarativeTarget [] :=
  ⟨inferClausesFuel_nil_complete fuel signature context selfEnv parent index
      before targetRelated,
    ValidatorRunExtension.refl terminal signature state⟩

/-- Certified head-to-tail clause-list composition. -/
def inferClausesFuel_cons_complete_certified
    {terminal : Subst} {fuel : Nat} {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {clause : Clause} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {holeLists : List (List Dual)}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (head : CertifiedClauseRunCompletion terminal signature before
      (inferClauseFuel fuel signature context selfEnv (index :: parent)
        clause executableTarget state)
      q₁ S₁ ledger₁ declarativeTarget holes)
    (tail : CertifiedClausesRunCompletion terminal signature
      head.run.completion
      (inferClausesFuel fuel signature context selfEnv parent (index + 1)
        clauses executableTarget head.run.result.state)
      q' S' ledger' declarativeTarget holeLists) :
    CertifiedClausesRunCompletion terminal signature before
      (inferClausesFuel (fuel + 1) signature context selfEnv parent index
        (clause :: clauses) executableTarget state)
      q' S' ledger' declarativeTarget (holes :: holeLists) :=
  ⟨inferClausesFuel_cons_complete before targetRelated head.run tail.run,
    head.validation.trans tail.validation⟩

end DemandTypingInferenceCompletenessMatcherClauseCertified
end TypePM
