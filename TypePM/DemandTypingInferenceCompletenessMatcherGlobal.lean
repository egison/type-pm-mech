import TypePM.DemandTypingInferenceCompletenessGlobalCertified
import TypePM.DemandTypingInferenceCompletenessMatcherClauseCertified
import TypePM.DemandTypingInferenceCompletenessMatcherFinalizationCertified
import TypePM.DemandTypingInferenceCompletenessMatcherPPat
import TypePM.DemandTypingInferenceCompletenessMatcherDPat
import TypePM.DemandTypingInferenceCompletenessSignatureBounds

/-!
# Paired certified matcher-literal reconstruction

Matcher literals cross the expression/clause recursion boundary.  This module
reconstructs that boundary without weakening terminal validation to an exact
state equation: clause traversal and recursive expression checks retain their
paired chronology, while the local matcher-finalization suffix is transferred
across the resulting DD/executable bisimulation.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherGlobal

open Inference
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessMatcherExprTraversal
open DemandTypingInferenceCompletenessMatcherClauseCertified
open DemandTypingInferenceCompletenessMatcherFinalizationCertified
open DemandTypingInferenceCompletenessMatcherPPat
open DemandTypingInferenceCompletenessMatcherDPat
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessSignatureBounds

/-- Reconstruct a terminal-audited matcher literal from paired clause
traversal.  The checking callback is fuel-bounded, so the theorem plugs
directly into the global strong-induction dispatcher. -/
theorem auditedSynthMatcher_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {clauses : List Clause}
    {rawHoleLists : List (List Dual)} {capability : Cap}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (checkBelow : PairedMatcherCheckCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {clausesRaw : DDClauses signature
      { q with nextTy := q.nextTy + 1 } S declarativeContext clauses
      (.var q.nextTy) rawHoleLists q' S'}
    {clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁}
    {evidence : List Shape.Evidence}
    (collected : collectClauseEvidence signature.toMatcherSig clauses
      (terminalHoleCaps S' rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability)
    (clauseCaps : clauseCapsListCheck signature capability clauses
      (terminalHoleCaps S' rawHoleLists) = true)
    (catchAll : catchAllLastCheck clauses = true)
    (binders : matcherBindersCheck clauses = true)
    (arms : armExhaustiveCheck signature clauses
      (S'.apply (.var q.nextTy)) = true)
    (coverage : coverageCheck signature.toMatcherSig clauses capability = true)
    (clausesAudit : DDClausesTerminalAudit terminal signature clausesOrigin)
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      rawHoleLists capability (.var q.nextTy))
    (adequate : SynthBudgetAdequate (fuel + 2) (.matcher clauses)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state)
      q' S' (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy))) := by
  let targetOrigin := freshOrigin .matcherClause path "matcher-target"
  let entered := before.visit .exprMatcher path
  let targetAllocation := entered.freshTy targetOrigin
  have clausesAdequate : MatcherClausesBudgetAdequate fuel clauses := by
    simp only [SynthBudgetAdequate] at adequate
    change 8 * (1 + clauseListTraversalFuel clauses + 1) ≤ fuel + 2
      at adequate
    change 8 * (clauseListTraversalFuel clauses + 1) ≤ fuel
    omega
  have clausesSignatureBelow : SignatureVarsBelow
      { q with nextTy := q.nextTy + 1 } signature :=
    signatureBelow.mono (SupplyExtends.bumpTy q 1)
  have clausesContexts : ContextBisimulation targetAllocation.state.prevailing
      declarativeContext executableContext :=
    (contexts.transport (before.visitExtension .exprMatcher path)).transport
      (entered.freshTyExtension targetOrigin)
  have clausesContextBounded : declarativeContext.BoundedBy
      { q with nextTy := q.nextTy + 1 } :=
    contextBounded.mono (SupplyExtends.bumpTy q 1)
  have clausesExecutableContextBounded : executableContext.BoundedBy
      { q with nextTy := q.nextTy + 1 } :=
    executableContextBounded.mono (SupplyExtends.bumpTy q 1)
  have declarativeTargetBounded : Ty.BoundedBy
      { q with nextTy := q.nextTy + 1 } (.var q.nextTy) :=
    Ty.BoundedBy.varOf (by simp)
  have executableTargetBounded : Ty.BoundedBy
      { q with nextTy := q.nextTy + 1 }
      ((visit state .exprMatcher path).freshTy targetOrigin).1 := by
    rw [targetAllocation.target_eq]
    exact declarativeTargetBounded
  have targetRelated : TyBisimulation targetAllocation.state.prevailing
      (.var q.nextTy)
      ((visit state .exprMatcher path).freshTy targetOrigin).1 := by
    rw [targetAllocation.target_eq]
    exact targetAllocation.state.prevailing.sameTarget _
  let clausesRunFresh := Classical.choice
    (clausesOrigin_complete_certified_below closed
      (matcherPPatCompletenessMotive closed)
      (matcherDPatCompletenessMotive closed) fuel checkBelow
      (selfEnv := selfEnv) (parent := path) (index := 0)
      targetAllocation.state clausesSignatureBelow clausesContexts
      targetRelated
      clausesContextBounded clausesExecutableContextBounded
      declarativeTargetBounded executableTargetBounded clausesAudit
      clausesAdequate)
  let clausesRun : PairedClausesRunCompletion terminal signature
      targetAllocation.state
      (inferClausesFuel fuel signature executableContext selfEnv path 0 clauses
        (.var q.nextTy)
        ((visit state .exprMatcher path).freshTy targetOrigin).2)
      q' S' ledger₁ (.var q.nextTy) rawHoleLists := by
    rw [targetAllocation.target_eq] at clausesRunFresh
    exact clausesRunFresh
  obtain ⟨_, rawHolesBounded⟩ := clausesRaw.boundedBy closed
    targetAllocation.state.declarative_bounded clausesContextBounded
    declarativeTargetBounded
  let finalization := matcherFinalization_complete armBasic clausesRun.run
    collected inferred clauseCaps catchAll binders arms coverage rawHolesBounded
  have clausesTargetEq : clausesRun.run.result.target = .var q.nextTy :=
    inferClausesFuel_result_target clausesRun.run.success
  let rawRun := inferMatcherFuel_complete
    (fuel := fuel) (signature := signature) (context := executableContext)
    (selfEnv := selfEnv) (path := path) (clauses := clauses)
    entered clausesRun.run finalization
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finish
      rawRun (.matcher clauses) path
  have operationEq :
      (do
        let inner ← inferMatcherFuel (fuel + 1) signature executableContext
          selfEnv path clauses (visit state .exprMatcher path)
        pure (finishExpr (.matcher clauses) path inner.target inner.state)) =
      inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state := by
    simp only [inferExprFuel]
    cases inferMatcherFuel (fuel + 1) signature executableContext selfEnv path
        clauses (visit state .exprMatcher path) <;> rfl
  let outerRun : SynthRunCompletion before
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state)
      q' S' (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy)) :=
    { finished with
      success := operationEq.symm.trans finished.success
      transition := (before.visitExtension .exprMatcher path).seq
        finished.transition }
  let rawBounded : BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state)
      q' S' (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy)) :=
    ⟨outerRun, by
      change Ty.BoundedBy q'
        (.matcher finalization.executableCapability (.var q.nextTy))
      exact Ty.BoundedBy.matcherOf
        finalization.executableCapabilityBounded
        ((Ty.BoundedBy.varOf (by simp)).mono
          clausesOrigin.erase.supplyExtends)⟩
  let coverageEvent := TraceEvent.literalCoverage clauses
    finalization.executableCapability
  have runtimeTarget : TyBisimulation clausesRun.run.transition.after
      (.var q.nextTy) (.var q.nextTy) := by
    simpa only [clausesTargetEq] using clausesRun.run.target
  let covered := clausesRun.run.result.state.recordEvent coverageEvent
  let finalizationEvent := TraceEvent.matcherFinalization
    covered.trace.solves.length clauses (.var q.nextTy)
    clausesRun.run.result.rawHoleLists
    (covered.prevailing.apply (.var q.nextTy))
    (terminalHoleCaps covered.prevailing clausesRun.run.result.rawHoleLists)
    finalization.executableEvidence finalization.executableCapability
  let coverageExtension := clausesRun.run.transition.after.recordEventExtension
    coverageEvent
  let finalizationExtension := coverageExtension.after.recordEventExtension
    finalizationEvent
  let coverageRelation := clausesRun.run.completion.recordEvent coverageEvent
    (by simp [coverageEvent, TraceEvent.allocatedCapVars])
  let finalizedRelation := coverageRelation.recordEvent finalizationEvent
    (by simp [finalizationEvent, TraceEvent.allocatedCapVars])
  let capabilityAtFinal :=
    BisimulationExtension.transportCap finalizationExtension
      (BisimulationExtension.transportCap coverageExtension
        finalization.capability)
  let protectExtension :=
    TraversalStateCorrespondence.protectMatcherCapabilityRelatedExtension
      finalizedRelation capabilityAtFinal finalization.declarativeFixed
      finalization.executableFixed
  let localFinalization :=
    PairedValidatorRunExtension.recordMatcherFinalization
      (evidence := finalization.executableEvidence)
      clausesRun.run.transition.after runtimeTarget clausesRun.run.holes
      finalization.capability catchAll binders facts
  let protectValidation := PairedValidatorRunExtension.ofExact protectExtension
    (ValidatorRunExtension.protectMatcherCapability terminal signature
      (covered.recordEvent finalizationEvent)
      finalization.executableCapability)
  let finishTransition := protectExtension.after.recordEventExtension
    (.inferredExpr (.matcher clauses)
      (.matcher finalization.executableCapability (.var q.nextTy)) path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _ (.matcher clauses)
      path (.matcher finalization.executableCapability (.var q.nextTy)))
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprMatcher path)
    (ValidatorRunExtension.visit terminal signature state .exprMatcher path)
  let allocationValidation := PairedValidatorRunExtension.ofExact
    (entered.freshTyExtension targetOrigin)
    (ValidatorRunExtension.freshTy terminal signature
      (visit state .exprMatcher path) targetOrigin)
  let validation :=
    (visitValidation.trans allocationValidation).trans clausesRun.validation
      |>.trans localFinalization
      |>.trans protectValidation |>.trans finishValidation
  have history : state.StateExtension rawBounded.run.result.state := by
    change state.StateExtension finished.result.state
    dsimp only [finished,
      DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finish]
    change state.StateExtension
      (finishExpr (.matcher clauses) path rawRun.result.target
        rawRun.result.state).state
    exact validation.ordinary.history
  have validation' : PairedValidatorRunExtension terminal signature
      rawBounded.run.transition history := by
    change PairedValidatorRunExtension terminal signature
      ((before.visitExtension .exprMatcher path).seq finished.transition)
      history
    dsimp only [finished,
      DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finish]
    exact validation
  exact ⟨⟨rawBounded, history, validation'⟩⟩

end DemandTypingInferenceCompletenessMatcherGlobal
end TypePM
