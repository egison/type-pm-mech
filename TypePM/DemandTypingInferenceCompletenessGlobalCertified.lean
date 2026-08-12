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
      | @var _ _ _ name scheme _ _ lookup =>
          let rawRun := boundedSynthVarPaired_complete
            (signature := signature) (selfEnv := selfEnv) (path := path)
            before contexts contextBounded lookup inner
          let normalized := executableContext.applySubst state.prevailing
          have executableLookup : ∃ executableScheme,
              normalized.find? name = some executableScheme := by
            have sameLookup := congrArg
              (fun context : Context => context.find? name)
              contexts.forward
            rw [Context.find?_applySubst, lookup] at sameLookup
            cases found : normalized.find? _ with
            | none => simp [normalized, found] at sameLookup
            | some executableScheme => exact ⟨executableScheme, found⟩
          rcases executableLookup with ⟨executableScheme, executableFound⟩
          let entered := visit state .exprVar path
          have atEntered :
              (executableContext.applySubst entered.prevailing).find? name =
              some executableScheme := by
            simpa [entered, normalized] using executableFound
          let terminalLookup := instantiateScheme_terminalLookup
            (rawContext := executableContext)
            (normalizedContext := executableContext.applySubst entered.prevailing)
            (by simpa [entered, visit] using
              before.prevailing.executableIdempotent) atEntered
          refine ⟨BoundedPairedCertifiedSynthRunCompletion.ofExact rawRun ?_⟩
          exact DemandTypingInferenceCompletenessValidationMain.synthVar
            terminalLookup
      | lit =>
          let rawRun := boundedSynthLit_complete (signature := signature)
            (context := executableContext) (selfEnv := selfEnv) (path := path)
            before inner
          refine ⟨BoundedPairedCertifiedSynthRunCompletion.ofExact rawRun ?_⟩
          exact DemandTypingInferenceCompletenessValidationMain.synthLit
            terminal signature state path _
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

end DemandTypingInferenceCompletenessGlobalCertified
end TypePM
