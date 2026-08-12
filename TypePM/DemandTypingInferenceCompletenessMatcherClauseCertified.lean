import TypePM.DemandTypingInferenceCompletenessPrimitivePatternCertified
import TypePM.DemandTypingInferenceCompletenessMatcherDPat

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
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPrimitivePatternCertified
open DemandTypingInferenceCompletenessSignatureBounds

/-! ## Certified checking boundary -/

/-- Terminal-audited checking at one fuel, carrying the validator chronology
needed by a surrounding matcher clause. -/
abbrev CertifiedMatcherCheckCompletenessAt
    (terminal : Subst) (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {declarativeExpected executableExpected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDCheck signature q S declarativeContext expression
      declarativeExpected q' S'}
    {origin : DDCheckOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    SignatureVarsBelow q signature →
    ContextBisimulation before.prevailing declarativeContext
      executableContext →
    TyBisimulation before.prevailing declarativeExpected executableExpected →
    declarativeContext.BoundedBy q → executableContext.BoundedBy q →
    declarativeExpected.BoundedBy q → executableExpected.BoundedBy q →
    DDCheckTerminalAudit terminal signature origin →
    MatcherCheckBudgetAdequate fuel expression →
    Nonempty (CertifiedStateRunCompletion terminal signature before
      (checkExprFuel fuel signature executableContext selfEnv path expression
        executableExpected state) q' S' ledger')

abbrev CertifiedMatcherCheckCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound →
    CertifiedMatcherCheckCompletenessAt terminal signature fuel

theorem CertifiedMatcherCheckCompletenessBelow.lower
    {terminal : Subst} {signature : FrozenSig} {bound : Nat}
    (below : CertifiedMatcherCheckCompletenessBelow terminal signature
      (bound + 1)) :
    CertifiedMatcherCheckCompletenessBelow terminal signature bound := by
  intro fuel fuelLt
  exact below (Nat.lt_trans fuelLt (Nat.lt_succ_self bound))

/-- Certified left-to-right checking-list reconstruction. -/
theorem checksOrigin_complete_certified_below
    {terminal : Subst} {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contextBounded : context.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ declarativeExpecteds,
      expected.BoundedBy q)
    (executableExpectedsBounded : ∀ expected ∈ executableExpecteds,
      expected.BoundedBy q)
    (expectedsRelated : TyListBisimulation before.prevailing
      declarativeExpecteds executableExpecteds)
    {raw : DDChecks signature q S context expressions declarativeExpecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (CertifiedStateRunCompletion terminal signature before
      (checkExprsFuel fuel signature context selfEnv parent index expressions
        executableExpecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          cases expectedsRelated
          exact ⟨⟨checkExprsFuel_nil_complete fuel signature context selfEnv
            parent index before,
            ValidatorRunExtension.refl terminal signature state⟩⟩
      | cons headAudit tailAudit =>
          rename_i expression expected q₁ S₁ ledger₁ expressions expecteds
            headRaw tailRaw headOrigin tailOrigin
          cases expectedsRelated with
          | cons expectedRelated tailRelated =>
              rename_i executableExpected executableExpecteds
              have headAdequate :
                  MatcherCheckBudgetAdequate fuel expression := by
                simp only [MatcherChecksBudgetAdequate,
                  MatcherCheckBudgetAdequate, exprListTraversalFuel]
                  at adequate ⊢
                omega
              have tailAdequate :
                  MatcherChecksBudgetAdequate fuel expressions := by
                simp only [MatcherChecksBudgetAdequate,
                  exprListTraversalFuel] at adequate ⊢
                omega
              have expectedBounded := expectedsBounded expected (by simp)
              have executableExpectedBounded :=
                executableExpectedsBounded executableExpected (by simp)
              let headRun := Classical.choice
                (checkBelow (Nat.lt_succ_self fuel)
                  (selfEnv := selfEnv) (path := index :: parent) before
                  signatureBelow
                  (ContextBisimulation.same before.prevailing context)
                  expectedRelated contextBounded contextBounded expectedBounded
                  executableExpectedBounded headAudit headAdequate)
              have tailContextBounded : context.BoundedBy q₁ :=
                contextBounded.mono headOrigin.erase.supplyExtends
              have tailExpectedsBounded :
                  ∀ item ∈ expecteds, item.BoundedBy q₁ := by
                intro item membership
                exact (expectedsBounded item (by simp [membership])).mono
                  headOrigin.erase.supplyExtends
              have tailExecutableExpectedsBounded :
                  ∀ item ∈ executableExpecteds, item.BoundedBy q₁ := by
                intro item membership
                exact (executableExpectedsBounded item
                  (by simp [membership])).mono
                    headOrigin.erase.supplyExtends
              let tailRun := Classical.choice
                (checksOrigin_complete_certified_below
                  (selfEnv := selfEnv) (parent := parent)
                  (index := index + 1) fuel checkBelow.lower
                  headRun.run.completion
                  (signatureBelow.mono headOrigin.erase.supplyExtends)
                  tailContextBounded tailExpectedsBounded
                  tailExecutableExpectedsBounded
                  (headRun.run.transition.transportTyList tailRelated) tailAudit
                  tailAdequate)
              exact ⟨⟨checkExprsFuel_cons_complete before headRun.run tailRun.run,
                headRun.validation.trans tailRun.validation⟩⟩
termination_by fuel

/-! ## Certified matcher arms -/

/-- Reconstruct matcher arms while retaining the validator chronology of each
data pattern, body check, and suffix. -/
theorem armsOrigin_complete_certified_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv}
    {ppBindings executablePPBindings : MonoCtx}
    {parent : SyntaxPath} {index : Nat} {arms : List Arm}
    {declarativeClauseTarget declarativeBodyTarget : Ty}
    {executableClauseTarget executableBodyTarget : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (ppRelated : MonoCtxBisimulation before.prevailing ppBindings
      executablePPBindings)
    (clauseTargetRelated : TyBisimulation before.prevailing
      declarativeClauseTarget executableClauseTarget)
    (bodyTargetRelated : TyBisimulation before.prevailing
      declarativeBodyTarget executableBodyTarget)
    (contextBounded : context.BoundedBy q)
    (ppBounded : ppBindings.BoundedBy q)
    (executablePPBounded : executablePPBindings.BoundedBy q)
    (clauseTargetBounded : declarativeClauseTarget.BoundedBy q)
    (bodyTargetBounded : declarativeBodyTarget.BoundedBy q)
    (executableClauseTargetBounded : executableClauseTarget.BoundedBy q)
    (executableBodyTargetBounded : executableBodyTarget.BoundedBy q)
    {raw : DDArms signature q S context ppBindings arms
      declarativeClauseTarget declarativeBodyTarget q' S'}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    (adequate : MatcherArmsBudgetAdequate fuel arms) :
    Nonempty (CertifiedStateRunCompletion terminal signature before
      (checkArmsFuel fuel signature context selfEnv executablePPBindings
        parent index arms executableClauseTarget executableBodyTarget state)
      q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherArmsBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨⟨checkArmsFuel_nil_complete fuel signature context selfEnv
            executablePPBindings parent index executableClauseTarget
            executableBodyTarget before,
            ValidatorRunExtension.refl terminal signature state⟩⟩
      | cons bodyAudit tailAudit =>
          rename_i q₁ S₁ armBindings body q₂ S₂ ledger₁ ledger₂ arms
            dataPattern disjoint patternRaw bodyRaw bodyOrigin tailRaw
            patternOrigin tailOrigin
          have dataAdequate : DPatAdequate fuel dataPattern := by
            simp only [MatcherArmsBudgetAdequate, armListTraversalFuel,
              armTraversalFuel, DPatAdequate] at adequate ⊢
            omega
          have bodyAdequate : MatcherCheckBudgetAdequate fuel body := by
            simp only [MatcherArmsBudgetAdequate, MatcherCheckBudgetAdequate,
              armListTraversalFuel, armTraversalFuel] at adequate ⊢
            omega
          have tailAdequate : MatcherArmsBudgetAdequate fuel arms := by
            simp only [MatcherArmsBudgetAdequate, armListTraversalFuel,
              armTraversalFuel] at adequate ⊢
            omega
          let dataRun := Classical.choice
            (dpatComplete (path := 0 :: index :: parent)
              patternRaw patternOrigin before clauseTargetRelated
              clauseTargetBounded executableClauseTargetBounded dataAdequate)
          have signatureBelowState : SignatureVarsBelow state.supply
              signature := by
            rw [before.supply_eq]
            exact signatureBelow
          have executableClauseTargetBoundedState :
              executableClauseTarget.BoundedBy state.supply := by
            rw [before.supply_eq]
            exact executableClauseTargetBounded
          let dataValidation := inferDPatFuel_validation
            (terminal := terminal) closed signatureBelowState
            executableClauseTargetBoundedState dataRun.run.success
          have ppAtData : MonoCtxBisimulation dataRun.run.transition.after
              ppBindings executablePPBindings :=
            BisimulationExtension.transportMonoCtx dataRun.run.transition
              ppRelated
          let bodyContexts := ContextBisimulation.append
            (ContextBisimulation.append dataRun.run.bindings.toContext
              ppAtData.toContext)
            (ContextBisimulation.same dataRun.run.transition.after context)
          obtain ⟨_, armBindingsBounded⟩ :=
            patternOrigin.erase.boundedBy closed before.declarative_bounded
              clauseTargetBounded
          have bodyContextBounded :
              (armBindings.toContext ++ ppBindings.toContext ++ context).BoundedBy
                q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append armBindingsBounded.toContext
                (ppBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (contextBounded.mono patternOrigin.erase.supplyExtends)
          have bodyExecutableContextBounded :
              (dataRun.run.result.bindings.toContext ++
                executablePPBindings.toContext ++ context).BoundedBy q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append dataRun.rawBindingsBounded.toContext
                (executablePPBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (contextBounded.mono patternOrigin.erase.supplyExtends)
          have bodyExpectedBounded : declarativeBodyTarget.BoundedBy q₁ :=
            bodyTargetBounded.mono patternOrigin.erase.supplyExtends
          let bodyRun := Classical.choice
            (checkBelow (Nat.lt_succ_self fuel)
              (selfEnv := selfEnv.eraseMany
                (executablePPBindings.names ++
                  dataRun.run.result.bindings.names))
              (path := 1 :: index :: parent) dataRun.run.completion
              (signatureBelow.mono patternOrigin.erase.supplyExtends)
              bodyContexts
              (dataRun.run.transition.transportTy bodyTargetRelated)
              bodyContextBounded bodyExecutableContextBounded
              bodyExpectedBounded
              (executableBodyTargetBounded.mono
                patternOrigin.erase.supplyExtends)
              bodyAudit bodyAdequate)
          let prefixExtension := patternOrigin.erase.supplyExtends.trans
            bodyOrigin.erase.supplyExtends
          have tailContextBounded : context.BoundedBy q₂ :=
            contextBounded.mono prefixExtension
          have tailPPBounded : ppBindings.BoundedBy q₂ :=
            ppBounded.mono prefixExtension
          have tailExecutablePPBounded : executablePPBindings.BoundedBy q₂ :=
            executablePPBounded.mono prefixExtension
          have tailClauseBounded : declarativeClauseTarget.BoundedBy q₂ :=
            clauseTargetBounded.mono prefixExtension
          have tailBodyBounded : declarativeBodyTarget.BoundedBy q₂ :=
            bodyTargetBounded.mono prefixExtension
          have tailExecutableClauseBounded :
              executableClauseTarget.BoundedBy q₂ :=
            executableClauseTargetBounded.mono prefixExtension
          have tailExecutableBodyBounded :
              executableBodyTarget.BoundedBy q₂ :=
            executableBodyTargetBounded.mono prefixExtension
          have ppAtBody : MonoCtxBisimulation bodyRun.run.transition.after
              ppBindings executablePPBindings :=
            BisimulationExtension.transportMonoCtx
              (dataRun.run.transition.seq bodyRun.run.transition) ppRelated
          let tailRun := Classical.choice
            (armsOrigin_complete_certified_below closed dpatComplete fuel
              checkBelow.lower
              (selfEnv := selfEnv) (parent := parent) (index := index + 1)
              bodyRun.run.completion
              (signatureBelow.mono prefixExtension) ppAtBody
              ((dataRun.run.transition.seq bodyRun.run.transition).transportTy
                clauseTargetRelated)
              ((dataRun.run.transition.seq bodyRun.run.transition).transportTy
                bodyTargetRelated)
              tailContextBounded tailPPBounded tailExecutablePPBounded
              tailClauseBounded tailBodyBounded tailExecutableClauseBounded
              tailExecutableBodyBounded (origin := tailOrigin)
              tailAudit tailAdequate)
          exact ⟨⟨checkArmsFuel_cons_complete
            (executableClauseTarget := executableClauseTarget)
            (executableBodyTarget := executableBodyTarget)
            (clauseTarget := declarativeClauseTarget)
            (bodyTarget := declarativeBodyTarget)
            before ppRelated dataRun.run disjoint bodyRun.run tailRun.run,
            dataValidation.trans
              (bodyRun.validation.trans tailRun.validation)⟩⟩
termination_by fuel

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
