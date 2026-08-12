import TypePM.DemandTypingInferenceCompletenessValidatorCoverage
import TypePM.DemandTypingInferenceCompletenessMatcherExprTraversal

/-!
# Validator-certified raw traversal completions

This module is the integration boundary between the raw completeness packages
and terminal-validator completeness.  Existing reconstruction modules keep
returning their focused `*RunCompletion` objects.  The audited global
recursion wraps those objects with one chronological validator extension:
ordinary executable events and terminal-audit-sensitive events compose in
lockstep, without adding validator fields to every raw package.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessCertifiedRun

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherTraversal
open DemandTypingInferenceCompletenessMatcherExprTraversal
open DemandTypingInferenceCompletenessProtectedTrace

/-- The two independent validator extensions produced by one chronological
raw traversal. -/
structure ValidatorRunExtension
    (terminal : Subst) (signature : FrozenSig)
    (initial final : InferState) : Prop where
  ordinary : OrdinaryValidatorHistoryExtension signature initial final
  sensitive : TerminalAuditHistoryExtension terminal signature initial final

theorem ValidatorRunExtension.refl
    (terminal : Subst) (signature : FrozenSig) (state : InferState) :
    ValidatorRunExtension terminal signature state state :=
  ⟨OrdinaryValidatorHistoryExtension.refl signature state,
    TerminalAuditHistoryExtension.refl terminal signature state⟩

/-- Validator extensions compose in the same chronological order as raw
completion packages. -/
theorem ValidatorRunExtension.trans
    {terminal : Subst} {signature : FrozenSig}
    {first middle last : InferState}
    (front : ValidatorRunExtension terminal signature first middle)
    (back : ValidatorRunExtension terminal signature middle last) :
    ValidatorRunExtension terminal signature first last :=
  ⟨front.ordinary.trans back.ordinary,
    front.sensitive.trans back.sensitive⟩

/-- Apply an incremental run to already accumulated root-prefix coverage. -/
theorem ValidatorRunExtension.applyCoverage
    {terminal : Subst} {signature : FrozenSig}
    {initial final : InferState}
    (extension : ValidatorRunExtension terminal signature initial final)
    (ordinary : OpenOrdinaryValidatorEventCoverage signature initial)
    (sensitive : TerminalAuditEventCoverage terminal signature initial) :
    RootValidatorEventCoverage terminal signature final :=
  ⟨extension.ordinary.applyCoverage ordinary,
    extension.sensitive.applyCoverage sensitive⟩

/-- Root initialization: both event folds are vacuous on the canonical empty
state, so a completed validator extension directly yields root coverage. -/
theorem ValidatorRunExtension.applyEmpty
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply} {final : InferState}
    (extension : ValidatorRunExtension terminal signature
      (InferState.empty supply) final) :
    RootValidatorEventCoverage terminal signature final :=
  extension.applyCoverage
    (OpenOrdinaryValidatorEventCoverage.empty signature supply)
    (TerminalAuditEventCoverage.empty terminal signature supply)

/-! ## Raw state and expression wrappers -/

structure CertifiedStateRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  run : StateRunCompletion before operation q' declarative ledger
  validation : ValidatorRunExtension terminal signature initial run.result

structure CertifiedSynthRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  run : SynthRunCompletion before operation q' declarative ledger target
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-- Chronological state-only certified runs compose without reopening either
raw completion proof. -/
def CertifiedStateRunCompletion.seq
    {terminal : Subst} {signature : FrozenSig}
    {q q' q'' : InferenceBase.FreshSupply} {S S' S'' : Subst}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {firstOperation : Option InferState}
    (first : CertifiedStateRunCompletion terminal signature before
      firstOperation q' S' ledger₁)
    {secondOperation : InferState → Option InferState}
    (second : CertifiedStateRunCompletion terminal signature
      first.run.completion (secondOperation first.run.result)
      q'' S'' ledger₂) :
    CertifiedStateRunCompletion terminal signature before
      (do
        let middle ← firstOperation
        secondOperation middle)
      q'' S'' ledger₂ :=
  ⟨StateRunCompletion.seq first.run second.run,
    first.validation.trans second.validation⟩

/-! ## User-pattern wrappers -/

structure CertifiedPatternRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  run : PatternRunCompletion before operation q' declarative ledger dual
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedPatternsRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  run : PatternsRunCompletion before operation q' declarative ledger duals
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedPPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) (bindings : MonoCtx) : Type where
  run : PPatRunCompletion before operation q' declarative ledger target holes
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedDPatRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option DPatResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (bindings : MonoCtx) : Type where
  run : DPatRunCompletion before operation q' declarative ledger target
    bindings
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-! ## Matcher-clause wrappers -/

structure CertifiedClauseRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClauseResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holes : List Dual) : Type where
  run : ClauseRunCompletion before operation q' declarative ledger target holes
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

structure CertifiedClausesRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ClausesResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) (holeLists : List (List Dual)) : Type where
  run : ClausesRunCompletion before operation q' declarative ledger target
    holeLists
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-- A matcher literal returns the ordinary expression synthesis package; this
name documents its role at the audited matcher dispatcher boundary. -/
abbrev CertifiedMatcherRunCompletion := CertifiedSynthRunCompletion

/-! ## Root projection -/

/-- A certified root synthesis run beginning at an empty state supplies all
four event-coverage premises.  Current protected safety retained by the raw
completion discharges the only terminal premise of ordinary coverage. -/
theorem CertifiedSynthRunCompletion.rootConditions
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger₀ ledger' : CapabilityOriginLedger}
    {before : TraversalStateCorrespondence supply Subst.id ledger₀
      (InferState.empty supply)}
    {operation : Option ExprResult} {target : Ty}
    (certified : CertifiedSynthRunCompletion terminal signature before
      operation q' S' ledger' target) :
    TraversalValidatorEventCoverage signature certified.run.result.state ∧
      TerminalAuditEventCoverage terminal signature
        certified.run.result.state ∧
      TraceTypeAlignmentConditions certified.run.result.state ∧
      TraceDualAlignmentConditions certified.run.result.state := by
  let coverage := certified.validation.applyEmpty
  exact coverage.atTerminal
    ((currentProtectedProducerSafe_iff certified.run.result.state).mp
      certified.run.protected_safe)

end DemandTypingInferenceCompletenessCertifiedRun
end TypePM
