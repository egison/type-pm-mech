import TypePM.DemandTypingInferenceCompletenessMain
import TypePM.DemandTypingInferenceCompletenessPairedValidationMain

/-!
# Paired certified checking and state-list runs

Checking and constructor argument lists return state-only runs.  Their
recursive expression synthesis may already contain paired terminal-audit
witnesses, while the expected-type alignment suffix is executable-local and
exact.  This module packages that mixed chronology without depending on the
global expression dispatcher.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPairedChecking

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessMain
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
open DemandTypingInferenceCompletenessPairedValidationMain
open DemandTypingInferenceCompletenessMatcherTraversal

/-- State-only completion with paired sensitive-event chronology. -/
structure PairedCertifiedStateRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  raw : StateRunCompletion before operation q' declarative ledger
  history : initial.StateExtension raw.result
  validation : PairedValidatorRunExtension terminal signature
    raw.transition history

/-- Exact state validation embeds into the paired package. -/
def PairedCertifiedStateRunCompletion.ofExact
    {terminal : Subst} {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger' : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState}
    (raw : StateRunCompletion before operation q' S' ledger')
    (validation : ValidatorRunExtension terminal signature initial raw.result) :
    PairedCertifiedStateRunCompletion terminal signature before operation q'
      S' ledger' :=
  ⟨raw, validation.ordinary.history,
    PairedValidatorRunExtension.ofExact raw.transition validation⟩

/-- Change only the executable operation named by a paired state package. -/
def PairedCertifiedStateRunCompletion.congrOperation
    {terminal : Subst} {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger₀ ledger' : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {first second : Option InferState}
    (run : PairedCertifiedStateRunCompletion terminal signature before first
      q' S' ledger')
    (operationEq : second = first) :
    PairedCertifiedStateRunCompletion terminal signature before second q' S'
      ledger' :=
  let changed : StateRunCompletion before second q' S' ledger' :=
    DemandTypingInferenceCompletenessAlignmentTraversal.StateRunCompletion.congrOperation
      run.raw operationEq
  { run with raw := changed }

/-- Chronological head/tail composition for checking lists. -/
def PairedCertifiedStateRunCompletion.seq
    {terminal : Subst} {signature : FrozenSig}
    {q q' q'' : InferenceBase.FreshSupply} {S S' S'' : Subst}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {firstOperation : Option InferState}
    (first : PairedCertifiedStateRunCompletion terminal signature before
      firstOperation q' S' ledger₁)
    {secondOperation : InferState → Option InferState}
    (second : PairedCertifiedStateRunCompletion terminal signature
      first.raw.completion (secondOperation first.raw.result) q'' S'' ledger₂) :
    PairedCertifiedStateRunCompletion terminal signature before
      (do
        let middle ← firstOperation
        secondOperation middle)
      q'' S'' ledger₂ :=
  ⟨DemandTypingInferenceCompletenessAlignmentTraversal.StateRunCompletion.seq
      first.raw second.raw,
    first.history.trans second.history,
    PairedValidatorRunExtension.trans first.validation second.validation⟩

/-- Synthesis followed by an exact expected-type alignment yields paired
checking.  The caller supplies only the already-reconstructed raw synthesis,
its paired chronology, and the ordinary alignment completion. -/
def checkOfPairedSynth
    {terminal : Subst} {signature : FrozenSig}
    {fuel : Nat} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {expected rawTarget : Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger initial}
    (synth : BoundedSynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression initial)
      q₁ S₁ ledger₁ rawTarget)
    (synthHistory : initial.StateExtension synth.run.result.state)
    (synthValidation : PairedValidatorRunExtension terminal signature
      synth.run.transition synthHistory)
    (aligned : StateRunCompletion synth.run.completion.state
      (alignExprResultAtExpected path synth.run.result expected)
      q' S' ledger')
    (alignmentValidation : ValidatorRunExtension terminal signature
      synth.run.result.state aligned.result) :
    PairedCertifiedStateRunCompletion terminal signature before
      (checkExprFuel (fuel + 1) signature context selfEnv path expression
        expected initial) q' S' ledger' := by
  let raw := checkExprFuel_complete before synth.run aligned
  refine ⟨raw, synthHistory.trans alignmentValidation.ordinary.history, ?_⟩
  exact appendExact (childTransition := synth.run.transition)
    (suffixTransition := aligned.transition) synthValidation
    alignmentValidation

/-- Empty checking list. -/
def checksNil
    (terminal : Subst) (signature : FrozenSig)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state) :
    PairedCertifiedStateRunCompletion terminal signature before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index [] []
        state) q S ledger :=
  PairedCertifiedStateRunCompletion.ofExact
    (checksOrigin_nil_complete fuel before)
    (ValidatorRunExtension.refl terminal signature state)

/-- One checking-list cell, preserving paired head and tail chronology. -/
def checksCons
    {terminal : Subst} {fuel : Nat} {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    {before : TraversalStateCorrespondence q S ledger state}
    (head : PairedCertifiedStateRunCompletion terminal signature before
      (checkExprFuel fuel signature context selfEnv (index :: parent)
        expression expected state) q₁ S₁ ledger₁)
    (tail : PairedCertifiedStateRunCompletion terminal signature
      head.raw.completion
      (checkExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions expecteds head.raw.result) q' S' ledger') :
    PairedCertifiedStateRunCompletion terminal signature before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) (expected :: expecteds) state)
      q' S' ledger' := by
  let sequenced := PairedCertifiedStateRunCompletion.seq head tail
  exact sequenced.congrOperation (by
    simp only [checkExprsFuel]
    cases checkExprFuel fuel signature context selfEnv (index :: parent)
        expression expected state <;> rfl)

end DemandTypingInferenceCompletenessPairedChecking
end TypePM
