import TypePM.DemandTypingInferenceCompletenessMain
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessValidationMain
import TypePM.DemandTypingInferenceCompletenessPairedChecking
import TypePM.DemandTypingInferenceCompletenessFixMatcher
import TypePM.DemandTypingInferenceCompletenessPatternCertified
import TypePM.DemandTypingInferenceCompletenessMatcherClauseCertified

/-! # Paired certified global expression traversal

This post-`Main` layer combines each raw bounded synthesis completion with
the paired chronological validator extension built from the same child runs.
Keeping it above both modules avoids an import cycle between raw traversal and
paired terminal-sensitive validation. -/

namespace TypePM
namespace DemandTypingInferenceCompletenessGlobalCertified

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessValidationMain
open DemandTypingInferenceCompletenessPairedChecking
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessCheckingAlignment
open DemandTypingInferenceCompletenessFixMatcher
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessMatcherExprTraversal
open DemandTypingInferenceCompletenessSignatureBounds
open DemandTypingInferenceCompletenessPatternCertified
open DemandTypingInferenceCompletenessPatternDispatcher
open DemandTypingInferenceCompletenessPatternMain
open DemandTypingInferenceCompletenessMatcherClauseCertified

/-- The common output of global certified synthesis. -/
structure BoundedPairedCertifiedSynthRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  raw : BoundedSynthRunCompletion before operation q' declarative ledger target
  history : initial.StateExtension raw.run.result.state
  validation : PairedValidatorRunExtension terminal signature
    raw.run.transition history

/-- The list-valued counterpart used by tuple traversal. -/
structure BoundedPairedCertifiedSynthsRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) : Type where
  raw : BoundedSynthsRunCompletion before operation q' declarative ledger
    targets
  history : initial.StateExtension raw.run.result.state
  validation : PairedValidatorRunExtension terminal signature
    raw.run.transition history

/-- Fuel-bounded paired synthesis used by the final strong induction. -/
abbrev PairedAuditedSynthCompletenessAt
    (terminal : Subst) (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DemandSynth signature q S declarativeContext expression target q' S'}
    {origin : DemandSynthOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    SignatureVarsBelow q signature →
    ContextBisimulation before.prevailing declarativeContext
      executableContext →
    declarativeContext.BoundedBy q →
    executableContext.BoundedBy q →
    DemandSynthTerminalAudit terminal signature origin →
    SynthBudgetAdequate fuel expression →
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel fuel signature executableContext selfEnv path
        expression state) q' S' ledger' target)

abbrev PairedAuditedSynthCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound →
    PairedAuditedSynthCompletenessAt terminal signature fuel

theorem PairedAuditedSynthCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (complete : PairedAuditedSynthCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    PairedAuditedSynthCompletenessBelow terminal signature smaller := by
  intro fuel below
  exact complete (Nat.lt_of_lt_of_le below boundLe)

/-- Exact validator chronology embeds into paired chronology. -/
def BoundedPairedCertifiedSynthRunCompletion.ofExact
    {terminal : Subst} {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger' : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {target : Ty}
    (raw : BoundedSynthRunCompletion before operation q' S' ledger' target)
    (validation : ValidatorRunExtension terminal signature initial
      raw.run.result.state) :
    BoundedPairedCertifiedSynthRunCompletion terminal signature before
      operation q' S' ledger' target :=
  let history := validation.ordinary.history
  ⟨raw, history,
    PairedValidatorRunExtension.ofExact raw.run.transition validation⟩

/-- Exact-state leaves immediately yield the combined package. -/
theorem auditedSynthLeaf_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {raw : DemandSynth signature q S declarativeContext expression target q' S'}
    {origin : DemandSynthOrigin signature raw ledger ledger'}
    (audit : DemandSynthTerminalAudit terminal signature origin)
    (leaf : DemandSynthLeafOrigin signature origin)
    (adequate : SynthBudgetAdequate fuel expression) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel fuel signature executableContext selfEnv path
        expression state) q' S' ledger' target) := by
  let _ := executableContextBounded
  cases fuel with
  | zero => simp [SynthBudgetAdequate] at adequate
  | succ inner =>
      cases leaf with
      | @var a b c d e f g h =>
          let rawRun := boundedSynthVarPaired_complete
            (signature := signature) (selfEnv := selfEnv) (path := path)
            before contexts contextBounded h inner
          let normalized := executableContext.applySubst state.prevailing
          have executableLookup : ∃ executableScheme,
              normalized.find? e = some executableScheme := by
            cases found : normalized.find? e with
            | none =>
                have impossible := congrArg
                  (fun context : Context => context.find? e)
                  contexts.forward
                simp [h, Context.find?_applySubst, normalized, found]
                  at impossible
            | some executableScheme => exact ⟨executableScheme, rfl⟩
          rcases executableLookup with ⟨executableScheme, executableFound⟩
          let entered := visit state .exprVar path
          have atEntered :
              (executableContext.applySubst entered.prevailing).find? e =
              some executableScheme := by
            simpa [entered, normalized, visit,
              InferState.prevailing_recordEvent] using executableFound
          let terminalLookup := instantiateScheme_terminalLookup
            (signature := signature)
            (rawContext := executableContext)
            (normalizedContext := executableContext.applySubst entered.prevailing)
            (by simpa [entered, visit] using
              before.prevailing.executableIdempotent) atEntered
          refine ⟨BoundedPairedCertifiedSynthRunCompletion.ofExact rawRun ?_⟩
          let instantiated := instantiateSchemeInState signature
            executableContext (executableContext.applySubst entered.prevailing)
            e entered executableScheme
          cases selfLookup : selfEnv.find? e with
          | none =>
              let expected := finishExpr (.var e) path instantiated.1
                instantiated.2
              have operationSuccess : inferExprFuel (inner + 1) signature
                  executableContext selfEnv path (.var e) state =
                  some expected := by
                simp [inferExprFuel, entered, instantiated, atEntered,
                  selfLookup, expected]
              have resultEq : rawRun.run.result = expected :=
                Option.some.inj (rawRun.run.success.symm.trans operationSuccess)
              rw [congrArg ExprResult.state resultEq]
              exact DemandTypingInferenceCompletenessValidationMain.synthVar
                (terminal := terminal) terminalLookup
          | some placeholder =>
              let expected := finishExpr (.var e) path instantiated.1
                (recordSelfReference instantiated.2 e placeholder path)
              have operationSuccess : inferExprFuel (inner + 1) signature
                  executableContext selfEnv path (.var e) state =
                  some expected := by
                simp [inferExprFuel, entered, instantiated, atEntered,
                  selfLookup, expected]
              have resultEq : rawRun.run.result = expected :=
                Option.some.inj (rawRun.run.success.symm.trans operationSuccess)
              rw [congrArg ExprResult.state resultEq]
              exact
                DemandTypingInferenceCompletenessValidationMain.synthSelfVar
                  (terminal := terminal) placeholder terminalLookup
      | lit =>
          rename_i value
          let rawRun := boundedSynthLit_complete (signature := signature)
            (context := executableContext) (selfEnv := selfEnv) (path := path)
            (value := value)
            before inner
          refine ⟨BoundedPairedCertifiedSynthRunCompletion.ofExact rawRun ?_⟩
          exact DemandTypingInferenceCompletenessValidationMain.synthLit
            terminal signature state path value
      | something =>
          let rawRun := boundedSynthSomething_complete (signature := signature)
            (context := executableContext) (selfEnv := selfEnv) (path := path)
            before inner
          have allocatedValue :
              ((visit state .exprSomething path).freshTy
                (freshOrigin .expression path "something-target")).1 =
                .var q.nextTy := by
            simp [InferState.freshTy, visit, before.supply_eq]
          refine ⟨BoundedPairedCertifiedSynthRunCompletion.ofExact rawRun ?_⟩
          simpa [rawRun, boundedSynthSomething_complete,
            inferExprFuel_something_complete, allocatedValue] using
              DemandTypingInferenceCompletenessValidationMain.synthSomething
                terminal signature state path

/-- Lambda reconstruction composes its exact visit/allocation prefix, the
paired recursive body, and its exact result event. -/
theorem auditedSynthLam_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {body : Expr} {bodyTarget : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
      (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger ledger'}
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.lam name body)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.lam name body) state) q' S' ledger'
      (.fn (.var q.nextTy) bodyTarget)) := by
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let bodyBefore := before.afterVisitFreshTy .exprLam path
    (freshOrigin .expression path "lambda-domain")
  let domainRelated := bodyBefore.prevailing.sameTarget (.var q.nextTy)
  let bodyContexts :=
    (contexts.transport
      ((before.visitExtension .exprLam path).seq
        ((before.visit .exprLam path).freshTyExtension
          (freshOrigin .expression path "lambda-domain")))).consMono
      name domainRelated
  have bodyContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 1 }
      ((name, Scheme.mono (.var q.nextTy)) :: declarativeContext) :=
    Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono
        (Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)))
      (contextBounded.mono (SupplyExtends.bumpTy q 1))
  have bodyExecutableContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 1 }
      ((name, Scheme.mono (.var q.nextTy)) :: executableContext) :=
    Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono
        (Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)))
      (executableContextBounded.mono (SupplyExtends.bumpTy q 1))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv.erase name) (path := 0 :: path)
      bodyBefore (signatureBelow.mono (SupplyExtends.bumpTy q 1))
      bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  let rawRun := boundedSynthLam_complete before bodyRun.raw
    ((Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)).mono
      bodyOrigin.erase.supplyExtends)
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprLam path)
    (ValidatorRunExtension.visit terminal signature state .exprLam path)
  let freshValidation := PairedValidatorRunExtension.ofExact
    ((before.visit .exprLam path).freshTyExtension
      (freshOrigin .expression path "lambda-domain"))
    (ValidatorRunExtension.freshTy terminal signature _ _)
  let finishTransition := bodyRun.raw.run.transition.after.recordEventExtension
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyRun.raw.run.result.target) path)
  let finishValidation := PairedValidatorRunExtension.ofExact
    finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _ (.lam name body)
      path _)
  let validation :=
    (visitValidation.trans freshValidation).trans bodyRun.validation |>.trans
      finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation

/-- Expression lists preserve the exact left-to-right pairing of raw runs and
validator chronology. -/
theorem auditedSynths_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {raw : DemandSynths signature q S declarativeContext expressions targets q' S'}
    {origin : DemandSynthsOrigin signature raw ledger ledger'}
    (audit : DemandSynthsTerminalAudit terminal signature origin)
    (adequate : SynthsBudgetAdequate fuel expressions) :
    Nonempty (BoundedPairedCertifiedSynthsRunCompletion terminal signature
      before (inferExprsFuel fuel signature executableContext selfEnv parent
        index expressions state) q' S' ledger' targets) := by
  cases fuel with
  | zero => simp [SynthsBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil =>
          let rawRun := boundedSynthsNil_complete inner signature
            executableContext selfEnv parent index before
          refine ⟨⟨rawRun, InferState.StateExtension.refl state, ?_⟩⟩
          exact PairedValidatorRunExtension.refl terminal signature
            before.prevailing
      | cons headAudit tailAudit =>
          rename_i expression target q₁ S₁ ledger₁ expressions targets
            headRaw tailRaw headOrigin tailOrigin
          have headAdequate : SynthBudgetAdequate inner expression := by
            simp only [SynthsBudgetAdequate, SynthBudgetAdequate,
              exprListTraversalFuel] at adequate ⊢
            omega
          have tailAdequate : SynthsBudgetAdequate inner expressions := by
            simp only [SynthsBudgetAdequate, exprListTraversalFuel]
              at adequate ⊢
            omega
          let headRun := Classical.choice
            (synthBelow (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := index :: parent)
              before signatureBelow contexts contextBounded
              executableContextBounded headAudit
              headAdequate)
          have tailContexts : ContextBisimulation
              headRun.raw.run.completion.state.prevailing declarativeContext
              executableContext :=
            contexts.transport headRun.raw.run.transition
          have tailContextBounded : declarativeContext.BoundedBy q₁ :=
            contextBounded.mono headOrigin.erase.supplyExtends
          have tailExecutableContextBounded : executableContext.BoundedBy q₁ :=
            executableContextBounded.mono headOrigin.erase.supplyExtends
          have belowTail : PairedAuditedSynthCompletenessBelow terminal
              signature inner := synthBelow.mono (Nat.le_succ inner)
          let tailRun := Classical.choice
            (auditedSynths_complete_paired
              (selfEnv := selfEnv) (parent := parent) (index := index + 1)
              inner belowTail headRun.raw.run.completion.state
              (signatureBelow.mono headOrigin.erase.supplyExtends) tailContexts
              tailContextBounded tailExecutableContextBounded tailAudit
              tailAdequate)
          let rawRun := boundedSynthsCons_complete before headRun.raw tailRun.raw
            tailOrigin.erase.supplyExtends
          let validation := headRun.validation.trans tailRun.validation
          refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
          exact validation
termination_by fuel

theorem auditedSynthApp_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {function argument : Expr} {functionTarget : Ty}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S₃ : Subst}
    {ledger ledger₁ ledger₃ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {functionRaw : DemandSynth signature q S declarativeContext function
      functionTarget q₁ S₁}
    {functionOrigin : DemandSynthOrigin signature functionRaw ledger ledger₁}
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂)
    {argumentRaw : DemandCheck signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ declarativeContext argument
      (.var q₁.nextTy) q₂ S₃}
    {argumentOrigin : DemandCheckOrigin signature argumentRaw ledger₁ ledger₃}
    (functionAudit : DemandSynthTerminalAudit terminal signature functionOrigin)
    (argumentAudit : DemandCheckTerminalAudit terminal signature argumentOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.app function argument)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.app function argument) state) q₂ S₃ ledger₃
      (.var (q₁.nextTy + 1))) := by
  have functionAdequate : SynthBudgetAdequate fuel function := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  have argumentCheckAdequate : MatcherCheckBudgetAdequate fuel argument := by
    simp only [SynthBudgetAdequate, MatcherCheckBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let functionBefore := before.afterVisit .exprApp path
  have functionContexts : ContextBisimulation functionBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprApp path)
  let functionRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 0 :: path)
      functionBefore signatureBelow functionContexts contextBounded
      executableContextBounded
      functionAudit
      functionAdequate)
  let domainOrigin := freshOrigin .expression path "application-domain"
  let resultOrigin := freshOrigin .expression path "application-result"
  let functionAlignOrigin := freshOrigin .expression path
    "application-function"
  let domainAllocation := functionRun.raw.run.completion.state.freshTy domainOrigin
  let resultAllocation := domainAllocation.state.freshTy resultOrigin
  have arrowBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 }
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) :=
    Ty.BoundedBy.fnOf
      (Ty.BoundedBy.varOf (by simp))
      (Ty.BoundedBy.varOf (by simp))
  have functionDeclarativeBounded : functionTarget.BoundedBy q₁ :=
    (functionRaw.boundedBy closed before.declarative_bounded
      contextBounded).2
  have executableArrowEq :
      (Ty.fn (functionRun.raw.run.result.state.freshTy domainOrigin).1
        ((functionRun.raw.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) =
      (Ty.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) := by
    rw [domainAllocation.target_eq, resultAllocation.target_eq]
  have functionRelatedAtAllocation : TyBisimulation
      resultAllocation.state.prevailing functionTarget
      functionRun.raw.run.result.target :=
    (domainAllocation.state.freshTyExtension resultOrigin).transportTy
      ((functionRun.raw.run.completion.state.freshTyExtension
        domainOrigin).transportTy functionRun.raw.run.target)
  have arrowRelatedAtAllocation : TyBisimulation
      resultAllocation.state.prevailing
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))
      (.fn (functionRun.raw.run.result.state.freshTy domainOrigin).1
        ((functionRun.raw.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) := by
    rw [executableArrowEq]
    exact resultAllocation.state.prevailing.sameTarget _
  have executableArrowBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 }
      (.fn (functionRun.raw.run.result.state.freshTy domainOrigin).1
        ((functionRun.raw.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) := by
    rw [executableArrowEq]
    exact arrowBounded
  let functionAlignment :=
    DemandTypingInferenceCompletenessAlignmentTraversal.ddAlignTypesWithLedger_complete
    (origin := functionAlignOrigin) resultAllocation.state
    functionRelatedAtAllocation arrowRelatedAtAllocation
    (functionDeclarativeBounded.mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
    arrowBounded
    (functionRun.raw.rawTargetBounded.mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
    executableArrowBounded aligned
  let components := AuditedCheckComponents.ofAudit argumentAudit
  have argumentContextBounded : declarativeContext.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } :=
    (contextBounded.mono functionOrigin.erase.supplyExtends).mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1))
  have argumentExecutableContextBounded : executableContext.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } :=
    executableContextBounded.mono
      (functionOrigin.erase.supplyExtends.trans
        ((SupplyExtends.bumpTy q₁ 1).trans
          (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
  have argumentContexts : ContextBisimulation
      functionAlignment.completion.prevailing declarativeContext
      executableContext :=
    (((functionContexts.transport functionRun.raw.run.transition).transport
      (functionRun.raw.run.completion.state.freshTyExtension domainOrigin)).transport
      (domainAllocation.state.freshTyExtension resultOrigin)).transport
      functionAlignment.transition
  have argumentSynthAdequate : SynthBudgetAdequate fuel argument := by
    simp only [SynthBudgetAdequate, MatcherCheckBudgetAdequate]
      at argumentCheckAdequate ⊢
    omega
  let argumentRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 1 :: path)
      functionAlignment.completion
      (signatureBelow.mono
        (functionOrigin.erase.supplyExtends.trans
          ((SupplyExtends.bumpTy q₁ 1).trans
            (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1))))
      argumentContexts argumentContextBounded
      argumentExecutableContextBounded components.synthAudit
      argumentSynthAdequate)
  have expectedBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } (.var q₁.nextTy) :=
    Ty.BoundedBy.varOf (by simp)
  let executableDomain := (functionRun.raw.run.result.state.freshTy domainOrigin).1
  have expectedRelated : TyBisimulation
      functionAlignment.completion.prevailing (.var q₁.nextTy)
      executableDomain := by
    have atAllocation : TyBisimulation resultAllocation.state.prevailing
        (.var q₁.nextTy) executableDomain := by
      change TyBisimulation resultAllocation.state.prevailing
        (.var q₁.nextTy)
        (functionRun.raw.run.result.state.freshTy domainOrigin).1
      rw [domainAllocation.target_eq]
      exact resultAllocation.state.prevailing.sameTarget _
    exact functionAlignment.transition.transportTy atAllocation
  have executableExpectedBounded : executableDomain.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } := by
    simpa [executableDomain, domainAllocation.target_eq] using expectedBounded
  have declarativeArgumentRawBounded :=
    (components.synthesized.boundedBy closed
      functionAlignment.completion.declarative_bounded
      argumentContextBounded).2
  let expectedAlignment := ddAlignWithLedger_complete (path := 1 :: path)
    argumentRun.raw.run.completion.state argumentRun.raw.run.target
    (argumentRun.raw.run.transition.transportTy expectedRelated)
    declarativeArgumentRawBounded
    (expectedBounded.mono components.synthesized.supplyExtends)
    argumentRun.raw.rawTargetBounded
    (executableExpectedBounded.mono components.synthesized.supplyExtends)
    components.aligned
  let rawRun := boundedSynthApp_complete before functionRun.raw
    functionAlignment argumentRun.raw expectedAlignment
    (by
      change Ty.BoundedBy q₂
        ((functionRun.raw.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1
      rw [resultAllocation.target_eq]
      exact Ty.BoundedBy.varOf (by
        have extension := components.synthesized.supplyExtends
        have belowStart : q₁.nextTy + 1 <
            ({ q₁ with nextTy := q₁.nextTy + 2 } :
              InferenceBase.FreshSupply).nextTy := by simp
        exact Nat.lt_of_lt_of_le belowStart extension.2))
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprApp path)
    (ValidatorRunExtension.visit terminal signature state .exprApp path)
  let domainValidation := PairedValidatorRunExtension.ofExact
    (functionRun.raw.run.completion.state.freshTyExtension domainOrigin)
    (ValidatorRunExtension.freshTy terminal signature _ domainOrigin)
  let resultValidation := PairedValidatorRunExtension.ofExact
    (domainAllocation.state.freshTyExtension resultOrigin)
    (ValidatorRunExtension.freshTy terminal signature _ resultOrigin)
  let functionAlignmentValidation := PairedValidatorRunExtension.ofExact
    functionAlignment.transition
    (ValidatorRunExtension.ofAlignTypes
      (terminal := terminal) (signature := signature)
      functionAlignment.success)
  let expectedAlignmentValidation := PairedValidatorRunExtension.ofExact
    expectedAlignment.transition
    (ValidatorRunExtension.ofAlignExprResultAtExpected
      (terminal := terminal) (signature := signature)
      expectedAlignment.success)
  let finishTransition := expectedAlignment.transition.after.recordEventExtension
    (.inferredExpr (.app function argument) rawRun.run.result.target path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.app function argument) path _)
  let validation :=
    (visitValidation.trans functionRun.validation).trans domainValidation |>.trans
      resultValidation |>.trans functionAlignmentValidation |>.trans
      argumentRun.validation |>.trans expectedAlignmentValidation |>.trans
      finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation


/-- Tuple synthesis surrounds the paired child list by exact visit and result
events. -/
theorem auditedSynthTuple_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
      (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {childrenRaw : DemandSynths signature q S declarativeContext expressions
      targets q' S'}
    {childrenOrigin : DemandSynthsOrigin signature childrenRaw ledger ledger'}
    (childrenAudit : DemandSynthsTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.tuple expressions)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.tuple expressions) state) q' S' ledger' (.prod targets)) := by
  have childrenAdequate : SynthsBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, SynthsBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let childrenBefore := before.afterVisit .exprTuple path
  have childrenContexts : ContextBisimulation childrenBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprTuple path)
  have childrenBelow : PairedAuditedSynthCompletenessBelow terminal signature
      fuel := synthBelow.mono (Nat.le_succ fuel)
  let childrenRun := Classical.choice
    (auditedSynths_complete_paired
      (selfEnv := selfEnv) (parent := path) (index := 0)
      fuel childrenBelow childrenBefore signatureBelow childrenContexts
      contextBounded
      executableContextBounded childrenAudit childrenAdequate)
  let rawRun := boundedSynthTuple_complete before childrenRun.raw
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprTuple path)
    (ValidatorRunExtension.visit terminal signature state .exprTuple path)
  let finishTransition := childrenRun.raw.run.transition.after.recordEventExtension
    (.inferredExpr (.tuple expressions) (.prod childrenRun.raw.run.result.targets)
      path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _ (.tuple expressions)
      path _)
  let validation := visitValidation.trans childrenRun.validation |>.trans
    finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation

/-- Let synthesis records the paired generalization boundary between its two
recursive children. -/
theorem auditedSynthLet_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {value body : Expr}
    {valueTarget bodyTarget : Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
      (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {valueRaw : DemandSynth signature q S declarativeContext value valueTarget
      q₁ S₁}
    {valueOrigin : DemandSynthOrigin signature valueRaw ledger ledger₁}
    {bodyRaw : DemandSynth signature q₁ S₁
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger₁ ledger'}
    (valueAudit : DemandSynthTerminalAudit terminal signature valueOrigin)
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (facts : DDTerminalAudit.LetFacts terminal signature declarativeContext
      valueTarget S₁)
    (adequate : SynthBudgetAdequate (fuel + 1) (.letE name value body)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.letE name value body) state) q' S' ledger' bodyTarget) := by
  have valueAdequate : SynthBudgetAdequate fuel value := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let valueBefore := before.afterVisit .exprLet path
  have valueContexts : ContextBisimulation valueBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprLet path)
  let valueRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 0 :: path)
      valueBefore signatureBelow valueContexts contextBounded
      executableContextBounded
      valueAudit valueAdequate)
  let executableScheme := signature.generalize
    (executableContext.applySubst valueRun.raw.run.result.state.prevailing)
    (valueRun.raw.run.result.state.prevailing.apply
      valueRun.raw.run.result.target)
  let event := TraceEvent.letGeneralization
    valueRun.raw.run.result.state.trace.solves.length name executableContext
    valueRun.raw.run.result.target
    (executableContext.applySubst valueRun.raw.run.result.state.prevailing)
    (valueRun.raw.run.result.state.prevailing.apply
      valueRun.raw.run.result.target) executableScheme
  let eventTransition :=
    valueRun.raw.run.completion.state.prevailing.recordEventExtension event
  let bodyBefore := valueRun.raw.run.completion.state.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  have contextsAfterValue : ContextBisimulation
      valueRun.raw.run.completion.state.prevailing declarativeContext
      executableContext := valueContexts.transport valueRun.raw.run.transition
  let generalizations := GeneralizationBisimulation.ofBisimulation
    contextsAfterValue signature closed valueRun.raw.run.target
  have localSchemes : NormalizedSchemeBisimulation
      valueRun.raw.run.completion.state.prevailing
      (signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) executableScheme := by
    constructor
    · rw [FrozenSig.generalize_image_fixed signature declarativeContext
        valueTarget S₁
        valueRun.raw.run.completion.state.prevailing.declarativeIdempotent]
      rw [FrozenSig.generalize_image_fixed signature executableContext
        valueRun.raw.run.result.target
        valueRun.raw.run.result.state.prevailing
        valueRun.raw.run.completion.state.prevailing.executableIdempotent]
      exact generalizations.forward
    · rw [FrozenSig.generalize_image_fixed signature executableContext
        valueRun.raw.run.result.target
        valueRun.raw.run.result.state.prevailing
        valueRun.raw.run.completion.state.prevailing.executableIdempotent]
      rw [FrozenSig.generalize_image_fixed signature declarativeContext
        valueTarget S₁
        valueRun.raw.run.completion.state.prevailing.declarativeIdempotent]
      exact generalizations.reverse
  have bodyContexts : ContextBisimulation bodyBefore.prevailing
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext)
      ((name, executableScheme) :: executableContext) :=
    (contextsAfterValue.cons name localSchemes).transport eventTransition
  have valueTargetBounded : valueTarget.BoundedBy q₁ :=
    (valueRaw.boundedBy closed before.declarative_bounded contextBounded).2
  have bodyContextBounded : Context.BoundedBy q₁
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext) :=
    Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy
        (valueRun.raw.run.completion.state.declarative_bounded.apply
          valueTargetBounded))
      (contextBounded.mono valueOrigin.erase.supplyExtends)
  have bodyExecutableContextBounded : Context.BoundedBy q₁
      ((name, executableScheme) :: executableContext) :=
    Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy
        (valueRun.raw.run.completion.state.executable_bounded.apply
          valueRun.raw.rawTargetBounded))
      (executableContextBounded.mono valueOrigin.erase.supplyExtends)
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv.erase name) (path := 1 :: path)
      bodyBefore (signatureBelow.mono valueOrigin.erase.supplyExtends)
      bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  let rawRun := boundedSynthLet_complete closed before valueRun.raw bodyRun.raw
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprLet path)
    (ValidatorRunExtension.visit terminal signature state .exprLet path)
  let letValidation := PairedValidatorRunExtension.recordLetGeneralization
    (name := name) valueRun.raw.run.completion.state.prevailing contextsAfterValue
    valueRun.raw.run.target localSchemes facts
  let finishTransition := bodyRun.raw.run.transition.after.recordEventExtension
    (.inferredExpr (.letE name value body) bodyRun.raw.run.result.target path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.letE name value body) path _)
  let validation :=
    (visitValidation.trans valueRun.validation).trans letValidation |>.trans
      bodyRun.validation |>.trans finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation

/-- A paired synthesis child followed by the executable expected-type cut. -/
theorem auditedCheck_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed) {fuel : Nat}
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr}
    {declarativeExpected executableExpected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DemandCheck signature q S declarativeContext expression
      declarativeExpected q' S'}
    {origin : DemandCheckOrigin signature raw ledger ledger'}
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (expectedRelated : TyBisimulation before.prevailing declarativeExpected
      executableExpected)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (expectedBounded : declarativeExpected.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q)
    (audit : DemandCheckTerminalAudit terminal signature origin)
    (adequate : MatcherCheckBudgetAdequate fuel expression) :
    Nonempty (PairedCertifiedStateRunCompletion terminal signature before
      (checkExprFuel fuel signature executableContext selfEnv path expression
        executableExpected state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherCheckBudgetAdequate] at adequate
  | succ inner =>
      let components := AuditedCheckComponents.ofAudit audit
      have synthAdequate : SynthBudgetAdequate inner expression := by
        simp only [MatcherCheckBudgetAdequate, SynthBudgetAdequate]
          at adequate ⊢
        omega
      let synth := Classical.choice
        (synthBelow (Nat.lt_succ_self inner)
          (selfEnv := selfEnv) (path := path)
          (origin := components.synthOrigin) before signatureBelow contexts
          contextBounded
          executableContextBounded components.synthAudit synthAdequate)
      obtain ⟨_, declarativeRawBounded⟩ :=
        components.synthesized.boundedBy closed before.declarative_bounded
          contextBounded
      have expectedAtCut := expectedBounded.mono
        components.synthesized.supplyExtends
      have executableExpectedAtCut := executableExpectedBounded.mono
        components.synthesized.supplyExtends
      let alignedRun := ddAlignWithLedger_complete (path := path)
        synth.raw.run.completion.state synth.raw.run.target
        (synth.raw.run.transition.transportTy expectedRelated)
        declarativeRawBounded expectedAtCut synth.raw.rawTargetBounded
        executableExpectedAtCut components.aligned
      let alignmentValidation :=
        ValidatorRunExtension.ofAlignExprResultAtExpected
          (terminal := terminal) (signature := signature) alignedRun.success
      exact ⟨checkOfPairedSynth synth.raw synth.history synth.validation
        alignedRun alignmentValidation⟩

/-- Constructor and primitive argument checks are reconstructed
left-to-right with paired validation. -/
theorem auditedChecks_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel)
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
    {raw : DemandChecks signature q S declarativeContext expressions
      declarativeExpecteds q' S'}
    {origin : DemandChecksOrigin signature raw ledger ledger'}
    (audit : DemandChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (PairedCertifiedStateRunCompletion terminal signature before
      (checkExprsFuel fuel signature executableContext selfEnv parent index
        expressions executableExpecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil =>
          cases expectedsRelated
          exact ⟨checksNil terminal signature inner before⟩
      | cons headAudit tailAudit =>
          rename_i expression expected q₁ S₁ ledger₁ expressions expecteds
            headRaw tailRaw headOrigin tailOrigin
          cases executableExpecteds with
          | nil => cases expectedsRelated
          | cons executableExpected executableExpecteds =>
              cases expectedsRelated with
              | cons expectedRelated tailRelated =>
                have headAdequate : MatcherCheckBudgetAdequate inner
                    expression := by
                  simp only [MatcherChecksBudgetAdequate,
                    MatcherCheckBudgetAdequate, exprListTraversalFuel]
                    at adequate ⊢
                  omega
                have tailAdequate : MatcherChecksBudgetAdequate inner
                    expressions := by
                  simp only [MatcherChecksBudgetAdequate,
                    exprListTraversalFuel] at adequate ⊢
                  omega
                let headRun := Classical.choice
                  (auditedCheck_complete_paired closed
                    (synthBelow.mono (Nat.le_succ inner))
                    (selfEnv := selfEnv) (path := index :: parent)
                    before signatureBelow contexts expectedRelated contextBounded
                    executableContextBounded
                    (expectedsBounded expected (by simp))
                    (executableExpectedsBounded executableExpected (by simp))
                    headAudit headAdequate)
                have tailContexts : ContextBisimulation
                    headRun.raw.completion.prevailing declarativeContext
                    executableContext := contexts.transport headRun.raw.transition
                have tailContextBounded : declarativeContext.BoundedBy q₁ :=
                  contextBounded.mono headOrigin.erase.supplyExtends
                have tailExpectedsBounded : ∀ item ∈ expecteds,
                    item.BoundedBy q₁ := by
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
                  (auditedChecks_complete_paired closed inner
                    (synthBelow.mono (Nat.le_succ inner))
                    (selfEnv := selfEnv) (parent := parent)
                    (index := index + 1) headRun.raw.completion
                    (signatureBelow.mono headOrigin.erase.supplyExtends)
                    tailContexts
                    tailContextBounded
                    (executableContextBounded.mono
                      headOrigin.erase.supplyExtends)
                    tailExpectedsBounded tailExecutableExpectedsBounded
                    (headRun.raw.transition.transportTyList tailRelated)
                    tailAudit tailAdequate)
                exact ⟨checksCons headRun tailRun⟩
termination_by fuel

theorem auditedSynthCtor_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (lookup : signature.findDataCtor name = some scheme)
    {childrenRaw : DemandChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      declarativeContext expressions
      (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    {childrenOrigin : DemandChecksOrigin signature childrenRaw
      (DDLedger.markCtorInstance ledger q scheme) ledger₁}
    (childrenAudit : DemandChecksTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.ctor name expressions)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.ctor name expressions) state) q' S'
      (DDLedger.freezeExport ledger₁ S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  have childrenAdequate : MatcherChecksBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, MatcherChecksBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let instantiated := instantiateCtorInState_complete
    (before.visit .exprCtor path) scheme
  have instanceBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.dataCtors lookup).boundedBy)
  have instanceExtension := SupplyExtends.instantiateCtorScheme q scheme
  have childrenContextBounded : declarativeContext.BoundedBy
      (InferenceBase.instantiateCtorScheme q scheme).supply :=
    contextBounded.mono instanceExtension
  have childrenContexts : ContextBisimulation
      instantiated.correspondence.prevailing declarativeContext
      executableContext :=
    (contexts.transport (before.visitExtension .exprCtor path)).transport
      instantiated.transition
  have childBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel :=
    synthBelow.mono (Nat.le_succ fuel)
  have executableArgumentsBounded : ∀ expected ∈
      (instantiateCtorInState (visit state .exprCtor path) scheme).1.1,
      expected.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply := by
    intro expected membership
    apply instanceBounded.1 expected
    simpa [Inference.instantiateCtorInState, visit, before.supply_eq] using
      membership
  let childrenRun := Classical.choice
    (auditedChecks_complete_paired closed fuel childBelow
      (selfEnv := selfEnv) (parent := path) (index := 0)
      instantiated.correspondence (signatureBelow.mono instanceExtension)
      childrenContexts childrenContextBounded
      (executableContextBounded.mono instanceExtension)
      instanceBounded.1 executableArgumentsBounded
      instantiated.arguments childrenAudit childrenAdequate)
  let rawRun := boundedSynthCtor_complete closed before lookup childrenRun.raw
    childrenOrigin.erase.supplyExtends
  let entered := visit state .exprCtor path
  let instantiatedState := instantiateCtorInState entered scheme
  let frozen := childrenRun.raw.result.freezeCapabilityExport
    (freshCapImages q scheme.capBinders)
    (InferenceBase.instantiateCtorScheme q scheme).value.2
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprCtor path)
    (ValidatorRunExtension.visit terminal signature state .exprCtor path)
  let instantiateValidation := PairedValidatorRunExtension.ofExact
    instantiated.transition
    (ValidatorRunExtension.instantiateCtorInState
      (terminal := terminal) (signature := signature) entered scheme
      (closed.dataCtors lookup))
  let freezeTransition := childrenRun.raw.completion
    |>.freezeCapabilityExportExtension
      (freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2
  let freezeValidation := PairedValidatorRunExtension.ofExact freezeTransition
    (ValidatorRunExtension.freezeCapabilityExport terminal signature _
      (freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2)
  let finishTransition := freezeTransition.after.recordEventExtension
    (.inferredExpr (.ctor name expressions) rawRun.run.result.target path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.ctor name expressions) path _)
  let validation :=
    (visitValidation.trans instantiateValidation).trans
      childrenRun.validation |>.trans freezeValidation |>.trans
      finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation

theorem auditedSynthFix_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {self argument : String} {body : Expr}
    {bodyTarget : Ty} {q q₁ : InferenceBase.FreshSupply}
    {S S₁ S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext)
      body bodyTarget q₁ S₁}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger ledger₁}
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ bodyTarget
      (.var (q.nextTy + 1)) S')
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.fix self argument body)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.fix self argument body) state)
      q₁ S' ledger₁ (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) := by
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let visited := before.afterVisit .exprFix path
  let domainOrigin := freshOrigin .recursiveBinder path "fix-domain"
  let codomainOrigin := freshOrigin .recursiveBinder path "fix-codomain"
  let resultOrigin := freshOrigin .recursiveBinder path "fix-result"
  let domainAllocation := visited.freshTy domainOrigin
  let codomainAllocation := domainAllocation.state.freshTy codomainOrigin
  let executablePlaceholder := Ty.fn (fixDomain state path)
    (fixCodomain state path)
  let placeholderEvent := TraceEvent.fixPlaceholder self argument
    executablePlaceholder path
  let directEvent := TraceEvent.directSelfAccepted self executablePlaceholder path
  let placeholderExtension :=
    codomainAllocation.state.prevailing.recordEventExtension placeholderEvent
  let directExtension := placeholderExtension.after.recordEventExtension directEvent
  let bodyBefore :=
    (codomainAllocation.state.recordEvent placeholderEvent
      (by simp [placeholderEvent, TraceEvent.allocatedCapVars])).recordEvent
      directEvent (by simp [directEvent, TraceEvent.allocatedCapVars])
  have domainRelated : TyBisimulation bodyBefore.prevailing
      (.var q.nextTy) (fixDomain state path) := by
    have atAllocation : TyBisimulation codomainAllocation.state.prevailing
        (.var q.nextTy) (fixDomain state path) := by
      change TyBisimulation codomainAllocation.state.prevailing
        (.var q.nextTy) (visit state .exprFix path |>.freshTy domainOrigin).1
      rw [domainAllocation.target_eq]
      exact codomainAllocation.state.prevailing.sameTarget _
    exact directExtension.transportTy
      (placeholderExtension.transportTy atAllocation)
  have placeholderRelated : TyBisimulation bodyBefore.prevailing
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) executablePlaceholder := by
    have atAllocation : TyBisimulation codomainAllocation.state.prevailing
        (.fn (.var q.nextTy) (.var (q.nextTy + 1))) executablePlaceholder := by
      change TyBisimulation codomainAllocation.state.prevailing
        (.fn (.var q.nextTy) (.var (q.nextTy + 1)))
        (.fn (visit state .exprFix path |>.freshTy domainOrigin).1
          ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
            codomainOrigin).1)
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact codomainAllocation.state.prevailing.sameTarget _
    exact directExtension.transportTy
      (placeholderExtension.transportTy atAllocation)
  have bodyContexts : ContextBisimulation bodyBefore.prevailing
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext)
      ((argument, Scheme.mono (fixDomain state path)) ::
        (self, Scheme.mono executablePlaceholder) :: executableContext) := by
    let base := (((contexts.transport (before.visitExtension .exprFix path)).transport
      (visited.freshTyExtension domainOrigin)).transport
      (domainAllocation.state.freshTyExtension codomainOrigin)).transport
      placeholderExtension |>.transport directExtension
    exact (base.consMono self placeholderRelated).consMono argument domainRelated
  have bodyContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 2 }
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext) :=
    Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono (Ty.BoundedBy.varOf (by simp)))
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf
          (Ty.BoundedBy.varOf (by simp))
          (Ty.BoundedBy.varOf (by simp))))
        (contextBounded.mono (SupplyExtends.bumpTy q 2)))
  have bodyExecutableContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 2 }
      ((argument, Scheme.mono (fixDomain state path)) ::
        (self, Scheme.mono executablePlaceholder) :: executableContext) := by
    have domainBounded : (fixDomain state path).BoundedBy
        { q with nextTy := q.nextTy + 2 } := by
      change ((visit state .exprFix path |>.freshTy domainOrigin).1).BoundedBy _
      rw [domainAllocation.target_eq]
      exact Ty.BoundedBy.varOf (by simp)
    have placeholderBounded : executablePlaceholder.BoundedBy
        { q with nextTy := q.nextTy + 2 } := by
      change (Ty.fn (visit state .exprFix path |>.freshTy domainOrigin).1
        ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
          codomainOrigin).1).BoundedBy _
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact Ty.BoundedBy.fnOf (Ty.BoundedBy.varOf (by simp))
        (Ty.BoundedBy.varOf (by simp))
    exact Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainBounded)
      (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono placeholderBounded)
        (executableContextBounded.mono (SupplyExtends.bumpTy q 2)))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := (self, executablePlaceholder) ::
        selfEnv.eraseMany [self, argument]) (path := 0 :: path)
      bodyBefore (signatureBelow.mono (SupplyExtends.bumpTy q 2))
      bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  have codomainRelatedAtBody : TyBisimulation
      bodyRun.raw.run.completion.state.prevailing (.var (q.nextTy + 1))
      (fixCodomain state path) := by
    have atBody := bodyRun.raw.run.transition.transportTy
      (show TyBisimulation bodyBefore.prevailing (.var (q.nextTy + 1))
          (fixCodomain state path) from by
        have atAllocation : TyBisimulation codomainAllocation.state.prevailing
            (.var (q.nextTy + 1)) (fixCodomain state path) := by
          change TyBisimulation codomainAllocation.state.prevailing
            (.var (q.nextTy + 1))
            ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
              codomainOrigin).1
          rw [codomainAllocation.target_eq]
          exact codomainAllocation.state.prevailing.sameTarget _
        exact directExtension.transportTy
          (placeholderExtension.transportTy atAllocation))
    exact atBody
  have bodyDeclarativeBounded : bodyTarget.BoundedBy q₁ :=
    (bodyRaw.boundedBy closed
      codomainAllocation.state.declarative_bounded bodyContextBounded).2
  have codomainBounded : Ty.BoundedBy q₁ (.var (q.nextTy + 1)) :=
    (Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends
  have executableCodomainBounded : (fixCodomain state path).BoundedBy q₁ := by
    change (((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
      codomainOrigin).1).BoundedBy q₁
    rw [codomainAllocation.target_eq]
    exact codomainBounded
  let alignmentRun :=
    DemandTypingInferenceCompletenessAlignmentTraversal.ddAlignTypesWithLedger_complete
      (origin := resultOrigin) bodyRun.raw.run.completion.state bodyRun.raw.run.target
      codomainRelatedAtBody bodyDeclarativeBounded codomainBounded
      bodyRun.raw.rawTargetBounded executableCodomainBounded aligned
  let rawRun := DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_fix_complete
    before distinct direct nonMatcher bodyRun.raw.run alignmentRun
  let rawBounded : BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.fix self argument body) state) q₁ S' ledger₁
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) := ⟨rawRun, by
    have placeholderBounded : executablePlaceholder.BoundedBy q₁ := by
      change (Ty.fn (visit state .exprFix path |>.freshTy domainOrigin).1
        ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
          codomainOrigin).1).BoundedBy q₁
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact Ty.BoundedBy.fnOf
        ((Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends)
        ((Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends)
    exact placeholderBounded⟩
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprFix path)
    (ValidatorRunExtension.visit terminal signature state .exprFix path)
  let domainValidation := PairedValidatorRunExtension.ofExact
    (visited.freshTyExtension domainOrigin)
    (ValidatorRunExtension.freshTy terminal signature _ domainOrigin)
  let codomainValidation := PairedValidatorRunExtension.ofExact
    (domainAllocation.state.freshTyExtension codomainOrigin)
    (ValidatorRunExtension.freshTy terminal signature _ codomainOrigin)
  let placeholderValidation := PairedValidatorRunExtension.ofExact
    placeholderExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.fixPlaceholder
        self argument executablePlaceholder path))
  let directValidation := PairedValidatorRunExtension.ofExact directExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.directSelfAccepted
        self executablePlaceholder path))
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    alignmentRun.transition
    (ValidatorRunExtension.ofAlignTypes
      (terminal := terminal) (signature := signature) alignmentRun.success)
  let finishTransition := alignmentRun.transition.after.recordEventExtension
    (.inferredExpr (.fix self argument body) rawRun.result.target path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.fix self argument body) path _)
  let validation :=
    visitValidation.trans domainValidation |>.trans codomainValidation |>.trans
      placeholderValidation |>.trans directValidation |>.trans
      bodyRun.validation |>.trans alignmentValidation |>.trans finishValidation
  refine ⟨⟨rawBounded, validation.ordinary.history, ?_⟩⟩
  exact validation


/-- Matcher-bodied recursion uses the deterministic placeholder reconstruction
before its paired recursive body. -/
theorem auditedSynthFixMatcher_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {self argument : String} {clauses : List Clause}
    {domain codomain bodyTarget : Ty}
    {q q₀ q₁ : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
      (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholder : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q₀))
    {bodyRaw : DemandSynth signature q₀ S
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono (.fn domain codomain)) :: declarativeContext)
      (.matcher clauses) bodyTarget q₁ S₁}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw
      (DDLedger.markCapRange ledger q q₀) ledger₁}
    (aligned : DemandAlignTypesWithLedger ledger₁ S₁ bodyTarget codomain S')
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1)
      (.fix self argument (.matcher clauses))) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.fix self argument (.matcher clauses)) state)
      q₁ S' ledger₁ (.fn domain codomain)) := by
  have bodyAdequate : SynthBudgetAdequate fuel (.matcher clauses) := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let visited := before.afterVisit .exprFix path
  let placeholderRun := Classical.choice
    (fixMatcherPlaceholder_complete (path := path) visited placeholder)
  let placeholderTy := Ty.fn domain codomain
  let placeholderEvent := TraceEvent.fixPlaceholder self argument placeholderTy
    path
  let directEvent := TraceEvent.directSelfAccepted self placeholderTy path
  let placeholderExtension :=
    placeholderRun.transition.after.recordEventExtension placeholderEvent
  let directExtension := placeholderExtension.after.recordEventExtension
    directEvent
  let bodyBefore :=
    (placeholderRun.completion.recordEvent placeholderEvent
      (by simp [placeholderEvent, TraceEvent.allocatedCapVars])).recordEvent
      directEvent (by simp [directEvent, TraceEvent.allocatedCapVars])
  have baseContexts : ContextBisimulation placeholderRun.completion.prevailing
      declarativeContext executableContext :=
    (contexts.transport (before.visitExtension .exprFix path)).transport
      placeholderRun.transition
  have domainRelated : TyBisimulation bodyBefore.prevailing domain domain :=
    directExtension.transportTy
      (placeholderExtension.transportTy
        (placeholderRun.completion.prevailing.sameTarget domain))
  have placeholderRelated : TyBisimulation bodyBefore.prevailing
      placeholderTy placeholderTy :=
    directExtension.transportTy
      (placeholderExtension.transportTy
        (placeholderRun.completion.prevailing.sameTarget placeholderTy))
  have bodyContexts : ContextBisimulation bodyBefore.prevailing
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono placeholderTy) :: declarativeContext)
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono placeholderTy) :: executableContext) :=
    ContextBisimulation.consMono
      (ContextBisimulation.consMono
        ((baseContexts.transport placeholderExtension).transport directExtension)
        self placeholderRelated)
      argument domainRelated
  obtain ⟨domainBounded, codomainBounded⟩ :=
    fixMatcherPlaceholderSupply_boundedBy placeholder
  have bodyContextBounded : Context.BoundedBy q₀
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono placeholderTy) :: declarativeContext) :=
    Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainBounded)
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono
          (Ty.BoundedBy.fnOf domainBounded codomainBounded))
        (contextBounded.mono
          (SupplyExtends.fixMatcherPlaceholder placeholder)))
  have bodyExecutableContextBounded : Context.BoundedBy q₀
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono placeholderTy) :: executableContext) :=
    Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainBounded)
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono
          (Ty.BoundedBy.fnOf domainBounded codomainBounded))
        (executableContextBounded.mono
          (SupplyExtends.fixMatcherPlaceholder placeholder)))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := (self, placeholderTy) :: selfEnv.eraseMany [self, argument])
      (path := 0 :: path) bodyBefore
      (signatureBelow.mono (SupplyExtends.fixMatcherPlaceholder placeholder))
      bodyContexts bodyContextBounded
      bodyExecutableContextBounded bodyAudit bodyAdequate)
  have codomainRelated : TyBisimulation bodyRun.raw.run.completion.state.prevailing
      codomain codomain := bodyRun.raw.run.completion.state.prevailing.sameTarget _
  have bodyDeclarativeBounded : bodyTarget.BoundedBy q₁ :=
    (bodyRaw.boundedBy closed bodyBefore.declarative_bounded
      bodyContextBounded).2
  let alignmentRun := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .recursiveBinder path "fix-result")
    bodyRun.raw.run.completion.state bodyRun.raw.run.target codomainRelated
    bodyDeclarativeBounded
    (codomainBounded.mono bodyOrigin.erase.supplyExtends)
    bodyRun.raw.rawTargetBounded
    (codomainBounded.mono bodyOrigin.erase.supplyExtends) aligned
  let rawRun := inferExprFuel_fixMatcher_complete before distinct direct
    placeholderRun bodyRun.raw.run alignmentRun
  let rawBounded : BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.fix self argument (.matcher clauses)) state)
      q₁ S' ledger₁ (.fn domain codomain) := ⟨rawRun,
    Ty.BoundedBy.fnOf
      (domainBounded.mono bodyOrigin.erase.supplyExtends)
      (codomainBounded.mono bodyOrigin.erase.supplyExtends)⟩
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprFix path)
    (ValidatorRunExtension.visit terminal signature state .exprFix path)
  let placeholderValidation := PairedValidatorRunExtension.ofExact
    placeholderRun.transition
    (ValidatorRunExtension.ofBuildFixPlaceholderMatcher
      (terminal := terminal) (signature := signature) placeholderRun.success)
  let placeholderEventValidation := PairedValidatorRunExtension.ofExact
    placeholderExtension (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.fixPlaceholder
        self argument placeholderTy path))
  let directValidation := PairedValidatorRunExtension.ofExact directExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.directSelfAccepted
        self placeholderTy path))
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    alignmentRun.transition (ValidatorRunExtension.ofAlignTypes
      (terminal := terminal) (signature := signature) alignmentRun.success)
  let finishTransition := alignmentRun.transition.after.recordEventExtension
    (.inferredExpr (.fix self argument (.matcher clauses)) placeholderTy path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.fix self argument (.matcher clauses)) path placeholderTy)
  let validation :=
    visitValidation.trans placeholderValidation |>.trans
      placeholderEventValidation |>.trans directValidation |>.trans
      bodyRun.validation |>.trans alignmentValidation |>.trans finishValidation
  refine ⟨⟨rawBounded, validation.ordinary.history, ?_⟩⟩
  exact validation

theorem auditedSynthPrim_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (lookup : signature.findPrimitive op = some scheme)
    {childrenRaw : DemandChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      declarativeContext expressions
      (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    {childrenOrigin : DemandChecksOrigin signature childrenRaw
      (DDLedger.markCtorInstance ledger q scheme) ledger₁}
    (childrenAudit : DemandChecksTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.prim op expressions)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.prim op expressions) state) q' S'
      (DDLedger.freezeExport ledger₁ S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  have childrenAdequate : MatcherChecksBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, MatcherChecksBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let instantiated := instantiateCtorInState_complete
    (before.visit .exprPrim path) scheme
  have instanceBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.primitives lookup).boundedBy)
  have instanceExtension := SupplyExtends.instantiateCtorScheme q scheme
  have childrenContextBounded : declarativeContext.BoundedBy
      (InferenceBase.instantiateCtorScheme q scheme).supply :=
    contextBounded.mono instanceExtension
  have childrenContexts : ContextBisimulation
      instantiated.correspondence.prevailing declarativeContext
      executableContext :=
    (contexts.transport (before.visitExtension .exprPrim path)).transport
      instantiated.transition
  have childBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel :=
    synthBelow.mono (Nat.le_succ fuel)
  have executableArgumentsBounded : ∀ expected ∈
      (instantiateCtorInState (visit state .exprPrim path) scheme).1.1,
      expected.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply := by
    intro expected membership
    apply instanceBounded.1 expected
    simpa [Inference.instantiateCtorInState, visit, before.supply_eq] using
      membership
  let childrenRun := Classical.choice
    (auditedChecks_complete_paired closed fuel childBelow
      (selfEnv := selfEnv) (parent := path) (index := 0)
      instantiated.correspondence (signatureBelow.mono instanceExtension)
      childrenContexts childrenContextBounded
      (executableContextBounded.mono instanceExtension)
      instanceBounded.1 executableArgumentsBounded
      instantiated.arguments childrenAudit childrenAdequate)
  let rawRun := boundedSynthPrim_complete closed before lookup childrenRun.raw
    childrenOrigin.erase.supplyExtends
  let entered := visit state .exprPrim path
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprPrim path)
    (ValidatorRunExtension.visit terminal signature state .exprPrim path)
  let instantiateValidation := PairedValidatorRunExtension.ofExact
    instantiated.transition
    (ValidatorRunExtension.instantiateCtorInState
      (terminal := terminal) (signature := signature) entered scheme
      (closed.primitives lookup))
  let freezeTransition := childrenRun.raw.completion
    |>.freezeCapabilityExportExtension
      (freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2
  let freezeValidation := PairedValidatorRunExtension.ofExact freezeTransition
    (ValidatorRunExtension.freezeCapabilityExport terminal signature _
      (freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2)
  let finishTransition := freezeTransition.after.recordEventExtension
    (.inferredExpr (.prim op expressions) rawRun.run.result.target path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.prim op expressions) path _)
  let validation :=
    (visitValidation.trans instantiateValidation).trans
      childrenRun.validation |>.trans freezeValidation |>.trans
      finishValidation
  refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
  exact validation

/-- Global paired synthesis supplies the expression callback required by the
certified user-pattern recursion. -/
def certifiedPatternSynthCompletenessBelow_of_paired
    {terminal : Subst} {signature : FrozenSig} {bound : Nat}
    (complete : PairedAuditedSynthCompletenessBelow terminal signature bound) :
    CertifiedPatternSynthCompletenessBelow terminal signature bound := by
  constructor
  intro fuel fuelLt declarativeContext executableContext selfEnv path expression
    target q q' S S' ledger ledger' state raw origin before signatureBelow
    contexts contextBounded executableContextBounded audit adequate
  let run := Classical.choice
    (complete fuelLt (selfEnv := selfEnv) (path := path) (origin := origin)
      before signatureBelow contexts contextBounded executableContextBounded
      audit adequate)
  exact ⟨⟨run.raw.run, run.raw.rawTargetBounded, run.history, run.validation⟩⟩

/-- Global paired synthesis also supplies the paired matcher-check callback
used by clause reconstruction. -/
abbrev pairedMatcherCheckCompletenessBelow_of_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed) {bound : Nat}
    (complete : PairedAuditedSynthCompletenessBelow terminal signature bound) :
    PairedMatcherCheckCompletenessBelow terminal signature bound := by
  intro fuel fuelLt declarativeContext executableContext selfEnv path expression
    declarativeExpected executableExpected q q' S S' ledger ledger' state raw
    origin before signatureBelow contexts expectedRelated contextBounded
    executableContextBounded expectedBounded executableExpectedBounded audit
    adequate
  exact auditedCheck_complete_paired closed
    (complete.mono (Nat.le_of_lt fuelLt)) before signatureBelow contexts
    expectedRelated contextBounded executableContextBounded expectedBounded
    executableExpectedBounded audit adequate

/-- Reconstruct `matchAll` with one shared paired validator chronology. -/
theorem auditedSynthMatchAll_complete_paired
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (capComplete : PatternCtorCapCompletenessPackage signature)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {target matcher : Expr} {pattern : Pattern}
    {body : Expr} {targetTarget bodyTarget : Ty} {dual : Dual}
    {bindings : MonoCtx} {q q₁ q₂ q₃ q' : InferenceBase.FreshSupply}
    {S S₁ S₂ S₃ S₄ S' : Subst}
    {ledger ledger₁ ledger₂ ledger₃ ledger' : CapabilityOriginLedger}
    {state : InferState} (fuel : Nat)
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature
      (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {targetRaw : DemandSynth signature q S declarativeContext target targetTarget
      q₁ S₁}
    {targetOrigin : DemandSynthOrigin signature targetRaw ledger ledger₁}
    {patternRaw : DDPattern signature q₁ S₁ declarativeContext [] [] pattern
      dual bindings q₂ S₂}
    {patternOrigin : DDPatternOrigin signature patternRaw ledger₁ ledger₂}
    (targetAligned : DemandAlignTypesWithLedger ledger₂ S₂ dual.target
      targetTarget S₃)
    {matcherRaw : DemandCheck signature q₂ S₃ declarativeContext matcher
      (.slot dual.cap targetTarget) q₃ S₄}
    {matcherOrigin : DemandCheckOrigin signature matcherRaw ledger₂ ledger₃}
    {bodyRaw : DemandSynth signature q₃ S₄
      (bindings.toContext ++ declarativeContext) body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger₃ ledger'}
    (targetAudit : DemandSynthTerminalAudit terminal signature targetOrigin)
    (patternAudit : DDPatternTerminalAudit terminal signature patternOrigin)
    (matcherAudit : DemandCheckTerminalAudit terminal signature matcherOrigin)
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1)
      (.matchAll target matcher pattern body)) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.matchAll target matcher pattern body) state)
      q' S' ledger' (.listT bodyTarget)) := by
  have targetAdequate : SynthBudgetAdequate fuel target := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  have patternAdequate : PatternBudgetAdequate fuel pattern := by
    simp only [SynthBudgetAdequate, PatternBudgetAdequate, exprTraversalFuel]
      at adequate ⊢
    omega
  have matcherAdequate : MatcherCheckBudgetAdequate fuel matcher := by
    simp only [SynthBudgetAdequate, MatcherCheckBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let targetBefore := before.afterVisit .exprMatchAll path
  have targetContexts : ContextBisimulation targetBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprMatchAll path)
  let targetRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel) (selfEnv := selfEnv)
      (path := 0 :: path) targetBefore signatureBelow targetContexts
      contextBounded executableContextBounded targetAudit targetAdequate)
  have patternContexts : ContextBisimulation
      targetRun.raw.run.completion.state.prevailing declarativeContext
      executableContext := targetContexts.transport targetRun.raw.run.transition
  have patternContextBounded : declarativeContext.BoundedBy q₁ :=
    contextBounded.mono targetOrigin.erase.supplyExtends
  have patternExecutableContextBounded : executableContext.BoundedBy q₁ :=
    executableContextBounded.mono targetOrigin.erase.supplyExtends
  let patternFamilies := certifiedPatternFamilies_complete_below closed
    (fuel + 1) (certifiedPatternSynthCompletenessBelow_of_paired synthBelow)
    capComplete
  let patternRun := Classical.choice
    (patternFamilies.1.complete (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 2 :: path)
      targetRun.raw.run.completion.state
      (signatureBelow.mono targetOrigin.erase.supplyExtends)
      patternContexts .nil .nil patternContextBounded
      (by intro entry membership; simp at membership)
      (by intro entry membership; simp at membership)
      patternExecutableContextBounded
      (by intro entry membership; simp at membership)
      (by intro entry membership; simp at membership)
      patternAudit patternAdequate)
  have targetDeclarativeBounded : targetTarget.BoundedBy q₁ :=
    (targetRaw.boundedBy closed before.declarative_bounded contextBounded).2
  have patternBounds := patternRaw.boundedBy closed
    targetRun.raw.run.completion.state.declarative_bounded
    patternContextBounded (by intro entry membership; simp at membership)
    (by intro entry membership; simp at membership)
  have patternDeclarativeBounded := patternBounds.2.1
  have bindingsDeclarativeBounded := patternBounds.2.2
  let targetAlignment := ddAlignTypesWithLedger_complete
    (origin := freshOrigin .pattern (2 :: path) "match-target")
    patternRun.bounded.run.completion patternRun.bounded.run.dual.target
    (patternRun.bounded.run.transition.transportTy targetRun.raw.run.target)
    patternDeclarativeBounded.2
    (targetDeclarativeBounded.mono patternOrigin.erase.supplyExtends)
    patternRun.bounded.rawDualBounded.2
    (targetRun.raw.rawTargetBounded.mono patternOrigin.erase.supplyExtends)
    targetAligned
  have matcherContexts : ContextBisimulation
      targetAlignment.completion.prevailing declarativeContext
      executableContext :=
    (patternContexts.transport patternRun.bounded.run.transition).transport
      targetAlignment.transition
  have matcherContextBounded : declarativeContext.BoundedBy q₂ :=
    patternContextBounded.mono patternOrigin.erase.supplyExtends
  have matcherExecutableContextBounded : executableContext.BoundedBy q₂ :=
    patternExecutableContextBounded.mono patternOrigin.erase.supplyExtends
  let declarativeExpected := Ty.slot dual.cap targetTarget
  let executableExpected := Ty.slot patternRun.bounded.run.result.dual.cap
    targetRun.raw.run.result.target
  have expectedRelated : TyBisimulation targetAlignment.completion.prevailing
      declarativeExpected executableExpected :=
    TyBisimulation.slot
      (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
        targetAlignment.transition patternRun.bounded.run.dual.cap)
      (targetAlignment.transition.transportTy
        (patternRun.bounded.run.transition.transportTy
          targetRun.raw.run.target))
  have expectedBounded : declarativeExpected.BoundedBy q₂ :=
    Ty.BoundedBy.slotOf patternDeclarativeBounded.1
      (targetDeclarativeBounded.mono patternOrigin.erase.supplyExtends)
  have executableExpectedBounded : executableExpected.BoundedBy q₂ :=
    Ty.BoundedBy.slotOf patternRun.bounded.rawDualBounded.1
      (targetRun.raw.rawTargetBounded.mono patternOrigin.erase.supplyExtends)
  let matcherRun := Classical.choice
    (auditedCheck_complete_paired closed
      (synthBelow.mono (Nat.le_succ fuel)) (selfEnv := selfEnv)
      (path := 1 :: path) (origin := matcherOrigin)
      targetAlignment.completion
      (signatureBelow.mono
        (targetOrigin.erase.supplyExtends.trans
          patternOrigin.erase.supplyExtends))
      matcherContexts expectedRelated matcherContextBounded
      matcherExecutableContextBounded expectedBounded executableExpectedBounded
      matcherAudit matcherAdequate)
  have bodyContexts : ContextBisimulation matcherRun.raw.completion.prevailing
      (bindings.toContext ++ declarativeContext)
      (patternRun.bounded.run.result.bindings.toContext ++ executableContext) :=
    DemandTypingInferenceCompletenessPatternMain.ContextBisimulation.append
      ((DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
          matcherRun.raw.transition
          (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
            targetAlignment.transition patternRun.bounded.run.bindings)).toContext)
      (matcherContexts.transport matcherRun.raw.transition)
  have bodyContextBounded : Context.BoundedBy q₃
      (bindings.toContext ++ declarativeContext) :=
    Context.BoundedBy.append
      ((bindingsDeclarativeBounded.mono
        matcherOrigin.erase.supplyExtends).toContext)
      (contextBounded.mono
        (targetOrigin.erase.supplyExtends.trans
          (patternOrigin.erase.supplyExtends.trans
            matcherOrigin.erase.supplyExtends)))
  have bodyExecutableContextBounded : Context.BoundedBy q₃
      (patternRun.bounded.run.result.bindings.toContext ++ executableContext) :=
    Context.BoundedBy.append
      ((patternRun.bounded.rawBindingsBounded.mono
        matcherOrigin.erase.supplyExtends).toContext)
      (executableContextBounded.mono
        (targetOrigin.erase.supplyExtends.trans
          (patternOrigin.erase.supplyExtends.trans
            matcherOrigin.erase.supplyExtends)))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv.eraseMany pattern.patVars) (path := 3 :: path)
      matcherRun.raw.completion
      (signatureBelow.mono
        (targetOrigin.erase.supplyExtends.trans
          (patternOrigin.erase.supplyExtends.trans
            matcherOrigin.erase.supplyExtends)))
      bodyContexts bodyContextBounded bodyExecutableContextBounded bodyAudit
      bodyAdequate)
  let rawRun :=
    DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_matchAll_complete
      before targetRun.raw.run patternRun.bounded.run targetAlignment
      matcherRun.raw bodyRun.raw.run
  let boundedRun : BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.matchAll target matcher pattern body) state)
      q' S' ledger' (.listT bodyTarget) :=
    ⟨rawRun, listT_boundedBy bodyRun.raw.rawTargetBounded⟩
  let visitValidation := PairedValidatorRunExtension.ofExact
    (before.visitExtension .exprMatchAll path)
    (ValidatorRunExtension.visit terminal signature state .exprMatchAll path)
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    targetAlignment.transition
    (ValidatorRunExtension.ofAlignTypes
      (terminal := terminal) (signature := signature) targetAlignment.success)
  let finishTransition := bodyRun.raw.run.transition.after.recordEventExtension
    (.inferredExpr (.matchAll target matcher pattern body)
      (.listT bodyRun.raw.run.result.target) path)
  let finishValidation := PairedValidatorRunExtension.ofExact finishTransition
    (ValidatorRunExtension.finishExpr terminal signature _
      (.matchAll target matcher pattern body) path _)
  let validation :=
    (visitValidation.trans targetRun.validation).trans patternRun.validation
      |>.trans alignmentValidation |>.trans matcherRun.validation
      |>.trans bodyRun.validation |>.trans finishValidation
  refine ⟨⟨boundedRun, validation.ordinary.history, ?_⟩⟩
  exact validation

/-! ## Global dispatcher -/

/-- Constructor dispatch for every branch whose paired reconstruction is
already closed.  Matcher literals and `matchAll` are supplied by the two
cross-family helpers below this layer. -/
theorem auditedSynth_complete_paired_except_matchers
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {fuel : Nat}
    (synthBelow : PairedAuditedSynthCompletenessBelow terminal signature fuel)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DemandSynth signature q S declarativeContext expression target q' S'}
    {origin : DemandSynthOrigin signature raw ledger ledger'}
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (audit : DemandSynthTerminalAudit terminal signature origin)
    (adequate : SynthBudgetAdequate fuel expression)
    (matcherCase : ∀ {clauses : List Clause} {rawHoleLists : List (List Dual)}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {evidence : List Shape.Evidence} {capability : Cap}
      {ledger₁ : CapabilityOriginLedger}
      {clausesRaw : DDClauses signature
        { q with nextTy := q.nextTy + 1 } S declarativeContext clauses
        (.var q.nextTy) rawHoleLists q' S'}
      {clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁}
      {collected : collectClauseEvidence signature.toMatcherSig clauses
        (terminalHoleCaps S' rawHoleLists) = some evidence}
      {inferred : Shape.inferShape signature.observability evidence =
        some capability}
      {clauseCaps : clauseCapsListCheck signature capability clauses
        (terminalHoleCaps S' rawHoleLists) = true}
      {catchAll : catchAllLastCheck clauses = true}
      {binders : matcherBindersCheck clauses = true}
      {arms : armExhaustiveCheck signature clauses
        (S'.apply (.var q.nextTy)) = true}
      {coverage : coverageCheck signature.toMatcherSig clauses capability = true},
      DDClausesTerminalAudit terminal signature
        (let _ := collected
         let _ := inferred
         let _ := clauseCaps
         let _ := catchAll
         let _ := binders
         let _ := arms
         let _ := coverage
         clausesOrigin) →
      DDTerminalAudit.MatcherFacts terminal signature clauses rawHoleLists
        capability (.var q.nextTy) →
      SynthBudgetAdequate fuel (.matcher clauses) →
      Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
        before (inferExprFuel fuel signature executableContext selfEnv path
          (.matcher clauses) state) q' S'
        (DDLedger.freezeMatcherProducerExcept ledger₁ capability
          (borrowedMatcherCapVarsAt S' declarativeContext))
        (.matcher capability (.var q.nextTy))))
    (matchAllCase : ∀ {targetExpr matcher : Expr} {pattern : Pattern}
      {body : Expr} {bodyTy : Ty} {q' : InferenceBase.FreshSupply}
      {S' : Subst} {ledger' : CapabilityOriginLedger}
      {raw : DemandSynth signature q S declarativeContext
        (.matchAll targetExpr matcher pattern body) (.listT bodyTy) q' S'}
      {origin : DemandSynthOrigin signature raw ledger ledger'},
      DemandSynthTerminalAudit terminal signature origin →
      SynthBudgetAdequate fuel
        (.matchAll targetExpr matcher pattern body) →
      Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
        before (inferExprFuel fuel signature executableContext selfEnv path
          (.matchAll targetExpr matcher pattern body) state)
        q' S' ledger' (.listT bodyTy))) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel fuel signature executableContext selfEnv path
        expression state) q' S' ledger' target) := by
  cases audit with
  | var =>
      rename_i name scheme lookup
      exact auditedSynthLeaf_complete_paired fuel before contexts contextBounded
        executableContextBounded
        (audit := DemandSynthTerminalAudit.var (lookup := lookup))
        (leaf := DemandSynthLeafOrigin.var (q := q) (ledger := ledger) lookup)
        adequate
  | lit =>
      exact auditedSynthLeaf_complete_paired fuel before contexts contextBounded
        executableContextBounded .lit .lit adequate
  | something =>
      exact auditedSynthLeaf_complete_paired fuel before contexts contextBounded
        executableContextBounded .something .something adequate
  | lam bodyAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthLam_complete_paired inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded
            bodyAudit adequate
  | tuple childrenAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthTuple_complete_paired inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded childrenAudit
            adequate
  | ctor childrenAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthCtor_complete_paired closed inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded
            (by assumption) childrenAudit
            adequate
  | prim childrenAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthPrim_complete_paired closed inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded
            (by assumption) childrenAudit
            adequate
  | app functionAudit argumentAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthApp_complete_paired closed inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded
            (by assumption) functionAudit argumentAudit adequate
  | letE valueAudit bodyAudit facts =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthLet_complete_paired closed inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded valueAudit
            bodyAudit facts adequate
  | fix bodyAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthFix_complete_paired closed inner synthBelow before
            signatureBelow contexts contextBounded executableContextBounded (by assumption)
            (by assumption) (by assumption) (by assumption) bodyAudit
            adequate
  | fixMatcher bodyAudit =>
      cases fuel with
      | zero => simp [SynthBudgetAdequate] at adequate
      | succ inner =>
          exact auditedSynthFixMatcher_complete_paired closed inner synthBelow
            before signatureBelow contexts contextBounded executableContextBounded
            (by assumption) (by assumption) (by assumption) (by assumption)
            bodyAudit adequate
  | matcher clausesAudit facts =>
      rename_i clauses rawHoleLists evidence capability ledger₁ inferred
        catchAll binders coverage collected clauseCaps arms clausesRaw
        clausesOrigin
      exact matcherCase
        (clausesRaw := clausesRaw) (clausesOrigin := clausesOrigin)
        (collected := collected) (inferred := inferred)
        (clauseCaps := clauseCaps) (catchAll := catchAll)
        (binders := binders) (arms := arms) (coverage := coverage)
        clausesAudit facts adequate
  | matchAll targetAudit patternAudit matcherAudit bodyAudit =>
      rename_i targetExpr targetTarget q₁ S₁ ledger₁ pattern dual bindings q₂
        S₂ ledger₂ S₃ matcherExpr q₃ S₄ ledger₃ body bodyTarget targetAligned
        patternRaw patternOrigin matcherRaw matcherOrigin targetRaw bodyRaw
        targetOrigin bodyOrigin
      exact matchAllCase
        (raw := DemandSynth.matchAll targetRaw patternRaw targetAligned.erase
          matcherRaw bodyRaw)
        (origin := DemandSynthOrigin.matchAll targetOrigin patternOrigin
          targetAligned matcherOrigin bodyOrigin)
        (DemandSynthTerminalAudit.matchAll (targetAligned := targetAligned)
          targetAudit patternAudit matcherAudit bodyAudit) adequate


end DemandTypingInferenceCompletenessGlobalCertified
end TypePM
