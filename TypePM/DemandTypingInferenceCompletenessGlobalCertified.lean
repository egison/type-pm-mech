import TypePM.DemandTypingInferenceCompletenessMain
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessValidationMain

/-! # Paired certified global expression traversal

This post-`Main` layer combines each raw bounded synthesis completion with
the exact chronological validator extension built from the same child runs.
Keeping it above both modules avoids an import cycle between raw traversal and
paired terminal-sensitive validation. -/

namespace TypePM
namespace DemandTypingInferenceCompletenessGlobalCertified

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessValidationMain

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
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext
      executableContext →
    declarativeContext.BoundedBy q →
    executableContext.BoundedBy q →
    DDSynthTerminalAudit terminal signature origin →
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
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (audit : DDSynthTerminalAudit terminal signature origin)
    (leaf : DDSynthLeafOrigin signature origin)
    (adequate : SynthBudgetAdequate fuel expression) :
    Nonempty (BoundedPairedCertifiedSynthRunCompletion terminal signature
      before (inferExprFuel fuel signature executableContext selfEnv path
        expression state) q' S' ledger' target) := by
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
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger'}
    (bodyAudit : DDSynthTerminalAudit terminal signature bodyOrigin)
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
      bodyBefore bodyContexts bodyContextBounded bodyExecutableContextBounded
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

end DemandTypingInferenceCompletenessGlobalCertified
end TypePM
