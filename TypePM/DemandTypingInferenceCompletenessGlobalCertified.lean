import TypePM.DemandTypingInferenceCompletenessMain
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessValidationMain
import TypePM.DemandTypingInferenceCompletenessPairedChecking

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
open DemandTypingInferenceCompletenessPairedChecking
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessCheckingAlignment

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
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {raw : DDSynths signature q S declarativeContext expressions targets q' S'}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (audit : DDSynthsTerminalAudit terminal signature origin)
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
              before contexts contextBounded executableContextBounded headAudit
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
              inner belowTail headRun.raw.run.completion.state tailContexts
              tailContextBounded tailExecutableContextBounded tailAudit
              tailAdequate)
          let rawRun := boundedSynthsCons_complete before headRun.raw tailRun.raw
            tailOrigin.erase.supplyExtends
          let validation := headRun.validation.trans tailRun.validation
          refine ⟨⟨rawRun, validation.ordinary.history, ?_⟩⟩
          exact validation
termination_by fuel

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
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {childrenRaw : DDSynths signature q S declarativeContext expressions
      targets q' S'}
    {childrenOrigin : DDSynthsOrigin signature childrenRaw ledger ledger'}
    (childrenAudit : DDSynthsTerminalAudit terminal signature childrenOrigin)
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
      fuel childrenBelow childrenBefore childrenContexts contextBounded
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
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {valueRaw : DDSynth signature q S declarativeContext value valueTarget
      q₁ S₁}
    {valueOrigin : DDSynthOrigin signature valueRaw ledger ledger₁}
    {bodyRaw : DDSynth signature q₁ S₁
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DDSynthOrigin signature bodyRaw ledger₁ ledger'}
    (valueAudit : DDSynthTerminalAudit terminal signature valueOrigin)
    (bodyAudit : DDSynthTerminalAudit terminal signature bodyOrigin)
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
      valueBefore valueContexts contextBounded executableContextBounded
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
      bodyBefore bodyContexts bodyContextBounded bodyExecutableContextBounded
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
    {raw : DDCheck signature q S declarativeContext expression
      declarativeExpected q' S'}
    {origin : DDCheckOrigin signature raw ledger ledger'}
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (expectedRelated : TyBisimulation before.prevailing declarativeExpected
      executableExpected)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (expectedBounded : declarativeExpected.BoundedBy q)
    (executableExpectedBounded : executableExpected.BoundedBy q)
    (audit : DDCheckTerminalAudit terminal signature origin)
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
          (origin := components.synthOrigin) before contexts contextBounded
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
                    before contexts expectedRelated contextBounded
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
                    (index := index + 1) headRun.raw.completion tailContexts
                    tailContextBounded
                    (executableContextBounded.mono
                      headOrigin.erase.supplyExtends)
                    tailExpectedsBounded tailExecutableExpectedsBounded
                    (headRun.raw.transition.transportTyList tailRelated)
                    tailAudit tailAdequate)
                exact ⟨checksCons headRun tailRun⟩
termination_by fuel

end DemandTypingInferenceCompletenessGlobalCertified
end TypePM
