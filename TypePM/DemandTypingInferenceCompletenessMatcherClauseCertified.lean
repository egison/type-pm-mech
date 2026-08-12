import TypePM.DemandTypingInferenceCompletenessPrimitivePatternCertified
import TypePM.DemandTypingInferenceCompletenessMatcherDPat
import TypePM.DemandTypingInferenceCompletenessMatcherPPat

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
    {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ declarativeExpecteds,
      expected.BoundedBy q)
    (executableExpectedsBounded : ∀ expected ∈ executableExpecteds,
      expected.BoundedBy q)
    (expectedsRelated : TyListBisimulation before.prevailing
      declarativeExpecteds executableExpecteds)
    {raw : DDChecks signature q S declarativeContext expressions
      declarativeExpecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (CertifiedStateRunCompletion terminal signature before
      (checkExprsFuel fuel signature executableContext selfEnv parent index expressions
        executableExpecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          cases expectedsRelated
          exact ⟨⟨checkExprsFuel_nil_complete fuel signature executableContext selfEnv
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
                  contexts expectedRelated contextBounded executableContextBounded
                  expectedBounded
                  executableExpectedBounded headAudit headAdequate)
              have tailContextBounded : declarativeContext.BoundedBy q₁ :=
                contextBounded.mono headOrigin.erase.supplyExtends
              have tailExecutableContextBounded :
                  executableContext.BoundedBy q₁ :=
                executableContextBounded.mono headOrigin.erase.supplyExtends
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
                  (contexts.transport headRun.run.transition)
                  tailContextBounded tailExecutableContextBounded
                  tailExpectedsBounded
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
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
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
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (ppRelated : MonoCtxBisimulation before.prevailing ppBindings
      executablePPBindings)
    (clauseTargetRelated : TyBisimulation before.prevailing
      declarativeClauseTarget executableClauseTarget)
    (bodyTargetRelated : TyBisimulation before.prevailing
      declarativeBodyTarget executableBodyTarget)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (ppBounded : ppBindings.BoundedBy q)
    (executablePPBounded : executablePPBindings.BoundedBy q)
    (clauseTargetBounded : declarativeClauseTarget.BoundedBy q)
    (bodyTargetBounded : declarativeBodyTarget.BoundedBy q)
    (executableClauseTargetBounded : executableClauseTarget.BoundedBy q)
    (executableBodyTargetBounded : executableBodyTarget.BoundedBy q)
    {raw : DDArms signature q S declarativeContext ppBindings arms
      declarativeClauseTarget declarativeBodyTarget q' S'}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    (adequate : MatcherArmsBudgetAdequate fuel arms) :
    Nonempty (CertifiedStateRunCompletion terminal signature before
      (checkArmsFuel fuel signature executableContext selfEnv executablePPBindings
        parent index arms executableClauseTarget executableBodyTarget state)
      q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherArmsBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨⟨checkArmsFuel_nil_complete fuel signature executableContext selfEnv
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
            (contexts.transport dataRun.run.transition)
          obtain ⟨_, armBindingsBounded⟩ :=
            patternOrigin.erase.boundedBy closed before.declarative_bounded
              clauseTargetBounded
          have bodyContextBounded :
              (armBindings.toContext ++ ppBindings.toContext ++
                declarativeContext).BoundedBy
                q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append armBindingsBounded.toContext
                (ppBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (contextBounded.mono patternOrigin.erase.supplyExtends)
          have bodyExecutableContextBounded :
              (dataRun.run.result.bindings.toContext ++
                executablePPBindings.toContext ++ executableContext).BoundedBy q₁ :=
            Context.BoundedBy.append
              (Context.BoundedBy.append dataRun.rawBindingsBounded.toContext
                (executablePPBounded.mono
                  patternOrigin.erase.supplyExtends).toContext)
              (executableContextBounded.mono
                patternOrigin.erase.supplyExtends)
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
          have tailContextBounded : declarativeContext.BoundedBy q₂ :=
            contextBounded.mono prefixExtension
          have tailExecutableContextBounded :
              executableContext.BoundedBy q₂ :=
            executableContextBounded.mono prefixExtension
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
              (signatureBelow.mono prefixExtension)
              (contexts.transport
                (dataRun.run.transition.seq bodyRun.run.transition)) ppAtBody
              ((dataRun.run.transition.seq bodyRun.run.transition).transportTy
                clauseTargetRelated)
              ((dataRun.run.transition.seq bodyRun.run.transition).transportTy
                bodyTargetRelated)
              tailContextBounded tailExecutableContextBounded
              tailPPBounded tailExecutablePPBounded
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

/-! ## Audited clause dispatch -/

mutual

/-- Certified reconstruction of one matcher clause under a strict checking
ceiling. -/
theorem clauseOrigin_complete_certified_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {clause : Clause} {declarativeTarget executableTarget : Ty}
    {holes : List Dual} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClause signature q S declarativeContext clause declarativeTarget
      holes q' S'}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    (audit : DDClauseTerminalAudit terminal signature origin)
    (adequate : MatcherClauseBudgetAdequate fuel clause) :
    Nonempty (CertifiedClauseRunCompletion terminal signature before
      (inferClauseFuel fuel signature executableContext selfEnv path clause
        executableTarget state)
      q' S' ledger' declarativeTarget holes) := by
  cases fuel with
  | zero => simp [MatcherClauseBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | mk nextAudit armsAudit =>
          rename_i q₁ S₁ nextMatchers q₂ S₂ ledger₁ ledger₂ ppBindings
            arms primitivePattern next decomposed nextRaw nextOrigin ppRaw
            armsRaw ppOrigin armsOrigin
          have primitiveAdequate : PPatAdequate fuel primitivePattern := by
            simp only [MatcherClauseBudgetAdequate, clauseTraversalFuel,
              PPatAdequate] at adequate ⊢
            omega
          have nextAdequate : MatcherChecksBudgetAdequate fuel nextMatchers := by
            have measure := exprListTraversalFuel_decomposeME decomposed
            have primitivePositive : 0 < ppatTraversalFuel primitivePattern := by
              cases primitivePattern <;> simp only [ppatTraversalFuel] <;> omega
            have armsPositive : 0 < armListTraversalFuel arms := by
              cases arms <;> simp only [armListTraversalFuel] <;> omega
            simp only [MatcherClauseBudgetAdequate, MatcherChecksBudgetAdequate,
              clauseTraversalFuel] at adequate ⊢
            omega
          have armsAdequate : MatcherArmsBudgetAdequate fuel arms := by
            simp only [MatcherClauseBudgetAdequate, MatcherArmsBudgetAdequate,
              clauseTraversalFuel] at adequate ⊢
            omega
          let visited := before.visit .clause path
          let primitiveRaw := Classical.choice
            (ppatComplete (path := 0 :: path) ppRaw ppOrigin visited
              ((before.visitExtension .clause path).transportTy targetRelated)
              targetBounded executableTargetBounded primitiveAdequate)
          have visitedSignatureBelow : SignatureVarsBelow
              (visit state .clause path).supply signature := by
            simpa [Inference.visit, before.supply_eq] using signatureBelow
          have executableTargetVisitedBounded :
              executableTarget.BoundedBy (visit state .clause path).supply := by
            simpa [Inference.visit, before.supply_eq] using
              executableTargetBounded
          let primitiveValidation := inferPPatFuel_validation
            (terminal := terminal) closed visitedSignatureBelow
            executableTargetVisitedBounded primitiveRaw.run.success
          let primitiveRun : BoundedCertifiedPPatRunCompletion terminal
              signature visited
              (inferPPatFuel fuel signature (0 :: path) primitivePattern
                executableTarget (visit state .clause path))
              q₁ S₁ ledger₁ declarativeTarget
              (match ppRaw with
                | _ => holes)
              ppBindings :=
            certifyBoundedPPatRun primitiveRaw primitiveValidation
          obtain ⟨_, holesBounded, ppBindingsBounded⟩ :=
            ppOrigin.erase.boundedBy closed before.declarative_bounded
              targetBounded
          have nextContextBounded : declarativeContext.BoundedBy q₁ :=
            contextBounded.mono ppOrigin.erase.supplyExtends
          have nextExecutableContextBounded :
              executableContext.BoundedBy q₁ :=
            executableContextBounded.mono ppOrigin.erase.supplyExtends
          have nextExpectedsBounded : ∀ expected : Ty, expected ∈
              (holes.map fun hole => Ty.slot hole.cap hole.target) →
              Ty.BoundedBy q₁ expected := by
            intro expected membership
            obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
            exact Ty.BoundedBy.slotOf (holesBounded hole holeMembership).1
              (holesBounded hole holeMembership).2
          let nextRun := Classical.choice
            (checksOrigin_complete_certified_below
              (selfEnv := selfEnv) (parent := 1 :: path) (index := 0)
              fuel checkBelow.lower primitiveRun.certified.run.completion
              (signatureBelow.mono ppOrigin.erase.supplyExtends)
              ((contexts.transport (before.visitExtension .clause path)).transport
                primitiveRun.certified.run.transition)
              nextContextBounded nextExecutableContextBounded
              nextExpectedsBounded
              (fun expected membership => by
                obtain ⟨hole, holeMembership, rfl⟩ :=
                  List.mem_map.mp membership
                exact Ty.BoundedBy.slotOf
                  (primitiveRun.rawHolesBounded hole holeMembership).1
                  (primitiveRun.rawHolesBounded hole holeMembership).2)
              (DualListBisimulation.slots primitiveRun.certified.run.holes)
              nextAudit nextAdequate)
          let targetAtNext :=
            (primitiveRun.certified.run.transition.seq
              nextRun.run.transition).transportTy
              ((before.visitExtension .clause path).transportTy targetRelated)
          let ppAtNext := BisimulationExtension.transportMonoCtx
            nextRun.run.transition primitiveRun.certified.run.bindings
          let holesAtNext := BisimulationExtension.transportDualList
            nextRun.run.transition primitiveRun.certified.run.holes
          have armsContextBounded : declarativeContext.BoundedBy q₂ :=
            contextBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          have armsExecutableContextBounded :
              executableContext.BoundedBy q₂ :=
            executableContextBounded.mono
              (ppOrigin.erase.supplyExtends.trans
                nextOrigin.erase.supplyExtends)
          have armsPPBounded : ppBindings.BoundedBy q₂ :=
            ppBindingsBounded.mono nextOrigin.erase.supplyExtends
          have armsTargetBounded : declarativeTarget.BoundedBy q₂ :=
            targetBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          let declarativeBodyTarget := Ty.listT (prodTy (holes.map Dual.target))
          let executableBodyTarget := Ty.listT
            (prodTy (primitiveRun.certified.run.result.holes.map Dual.target))
          have bodyTargetRelated : TyBisimulation nextRun.run.transition.after
              declarativeBodyTarget executableBodyTarget :=
            DemandTypingInferenceCompletenessExprTraversal.TyBisimulation.listT
              (DualListBisimulation.prodTargets holesAtNext)
          have armsBodyBounded : declarativeBodyTarget.BoundedBy q₂ := by
            exact listT_boundedBy (prodTy_boundedBy (fun target membership => by
              obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
              exact (holesBounded hole holeMembership).2.mono
                nextOrigin.erase.supplyExtends))
          have armsExecutableTargetBounded : executableTarget.BoundedBy q₂ :=
            executableTargetBounded.mono
              (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
          have armsExecutableBodyBounded : executableBodyTarget.BoundedBy q₂ := by
            exact listT_boundedBy (prodTy_boundedBy (fun target membership => by
              obtain ⟨hole, holeMembership, rfl⟩ := List.mem_map.mp membership
              exact (primitiveRun.rawHolesBounded hole holeMembership).2.mono
                nextOrigin.erase.supplyExtends))
          let armsRun := Classical.choice
            (armsOrigin_complete_certified_below closed dpatComplete fuel
              checkBelow.lower
              (selfEnv := selfEnv) (parent := 2 :: path) (index := 0)
              nextRun.run.completion
              (signatureBelow.mono
                (ppOrigin.erase.supplyExtends.trans
                  nextOrigin.erase.supplyExtends))
              ((contexts.transport (before.visitExtension .clause path)).transport
                (primitiveRun.certified.run.transition.seq
                  nextRun.run.transition))
              ppAtNext targetAtNext bodyTargetRelated armsContextBounded
              armsExecutableContextBounded
              armsPPBounded
              (primitiveRun.rawBindingsBounded.mono
                nextOrigin.erase.supplyExtends)
              armsTargetBounded armsBodyBounded armsExecutableTargetBounded
              armsExecutableBodyBounded armsAudit armsAdequate)
          exact ⟨inferClauseFuel_complete_certified before targetRelated
            primitiveRun.certified decomposed nextRun armsRun⟩
termination_by fuel

/-- Certified reconstruction of a matcher-clause list. -/
theorem clausesOrigin_complete_certified_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holeLists : List (List Dual)}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClauses signature q S declarativeContext clauses
      declarativeTarget holeLists q' S'}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (adequate : MatcherClausesBudgetAdequate fuel clauses) :
    Nonempty (CertifiedClausesRunCompletion terminal signature before
      (inferClausesFuel fuel signature executableContext selfEnv parent index clauses
        executableTarget state)
      q' S' ledger' declarativeTarget holeLists) := by
  cases fuel with
  | zero => simp [MatcherClausesBudgetAdequate] at adequate
  | succ fuel =>
      cases audit with
      | nil =>
          exact ⟨inferClausesFuel_nil_complete_certified terminal fuel signature
            executableContext selfEnv parent index before targetRelated⟩
      | cons headAudit tailAudit =>
          rename_i clause holes q₁ S₁ ledger₁ clauses holeLists headRaw
            tailRaw headOrigin tailOrigin
          have headAdequate : MatcherClauseBudgetAdequate fuel clause := by
            have tailPositive : 0 < clauseListTraversalFuel clauses := by
              cases clauses <;> simp only [clauseListTraversalFuel] <;> omega
            simp only [MatcherClausesBudgetAdequate,
              MatcherClauseBudgetAdequate, clauseListTraversalFuel]
              at adequate ⊢
            omega
          have tailAdequate : MatcherClausesBudgetAdequate fuel clauses := by
            have headPositive : 0 < clauseTraversalFuel clause := by
              cases clause
              simp only [clauseTraversalFuel]
              omega
            simp only [MatcherClausesBudgetAdequate,
              clauseListTraversalFuel] at adequate ⊢
            omega
          let headRun := Classical.choice
            (clauseOrigin_complete_certified_below closed ppatComplete
              dpatComplete (selfEnv := selfEnv) (path := index :: parent)
              fuel checkBelow.lower before signatureBelow contexts targetRelated
              contextBounded executableContextBounded targetBounded
              executableTargetBounded headAudit headAdequate)
          have tailContextBounded : declarativeContext.BoundedBy q₁ :=
            contextBounded.mono headOrigin.erase.supplyExtends
          have tailExecutableContextBounded :
              executableContext.BoundedBy q₁ :=
            executableContextBounded.mono headOrigin.erase.supplyExtends
          have tailTargetBounded : declarativeTarget.BoundedBy q₁ :=
            targetBounded.mono headOrigin.erase.supplyExtends
          have tailExecutableTargetBounded : executableTarget.BoundedBy q₁ :=
            executableTargetBounded.mono headOrigin.erase.supplyExtends
          let tailRun := Classical.choice
            (clausesOrigin_complete_certified_below closed ppatComplete
              dpatComplete (selfEnv := selfEnv) (parent := parent)
              (index := index + 1) fuel checkBelow.lower
              headRun.run.completion
              (signatureBelow.mono headOrigin.erase.supplyExtends)
              (contexts.transport headRun.run.transition)
              (headRun.run.transition.transportTy targetRelated)
              tailContextBounded tailExecutableContextBounded
              tailTargetBounded tailExecutableTargetBounded
              tailAudit tailAdequate)
          exact ⟨inferClausesFuel_cons_complete_certified before targetRelated
            headRun tailRun⟩
termination_by fuel

end

/-- Strict-ceiling entry point consumed by global matcher synthesis. -/
theorem clausesOrigin_complete_certified_from_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (ppatComplete : MatcherPPatCompletenessMotive signature)
    (dpatComplete : MatcherDPatCompletenessMotive signature)
    {bound : Nat}
    (checkBelow : CertifiedMatcherCheckCompletenessBelow terminal signature bound)
    {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {clauses : List Clause}
    {declarativeTarget executableTarget : Ty}
    {holeLists : List (List Dual)}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (fuelLt : fuel < bound)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (targetRelated : TyBisimulation before.prevailing declarativeTarget
      executableTarget)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (targetBounded : declarativeTarget.BoundedBy q)
    (executableTargetBounded : executableTarget.BoundedBy q)
    {raw : DDClauses signature q S declarativeContext clauses
      declarativeTarget holeLists q' S'}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (adequate : MatcherClausesBudgetAdequate fuel clauses) :
    Nonempty (CertifiedClausesRunCompletion terminal signature before
      (inferClausesFuel fuel signature executableContext selfEnv parent index clauses
        executableTarget state)
      q' S' ledger' declarativeTarget holeLists) :=
  clausesOrigin_complete_certified_below closed ppatComplete dpatComplete fuel
    (fun {childFuel} childLt =>
      checkBelow (Nat.lt_trans childLt fuelLt)) before signatureBelow
    contexts targetRelated contextBounded executableContextBounded targetBounded
    executableTargetBounded audit adequate

end DemandTypingInferenceCompletenessMatcherClauseCertified
end TypePM
