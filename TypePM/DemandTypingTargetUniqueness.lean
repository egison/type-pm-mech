import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.DemandTypingInferenceCompletenessLocalRenaming

/-!
# Demand-typing target uniqueness modulo residual renaming

An exact MGU is not canonically oriented, so two demand-directed derivations
need not publish syntactically equal targets.  Completeness nevertheless maps
every audited derivation to the same deterministic executable traversal.
The mutual factorization retained by that traversal is a variable renaming
on the free variables of each normalized published target.  Consequently any
two published targets have a common representative modulo a local, two-sort
renaming.  Source-context metavariables are intentionally included in that
renaming scope; `DemandTypingTargetUniquenessRegression` shows that fixing the
initial scope would make the statement false.
-/

namespace TypePM
namespace DemandTypingTargetUniqueness

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGlobalRecursion
open DemandTypingInferenceCompletenessGlobalRoot
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessPairedRoot
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessSignatureBounds
open DemandTypingInferenceCompletenessMain

/-- A type is obtained from another by a two-sorted variable renaming on all
of the source type's residual variables, with a pointwise inverse there.  The
ambient substitutions may do anything outside that finite scope. -/
def TargetRenaming (source target : Ty) : Prop :=
  ∃ forward reverse,
    LocalRenamingOn forward reverse source.fcv source.ftv ∧
    forward.apply source = target ∧
    reverse.apply target = source

/-- Two targets are equal modulo residual metavariable renaming when they
rename to one common representative.  The common-representative formulation
avoids choosing an arbitrary orientation between equally valid exact MGUs. -/
def TargetRenamingEquivalent (left right : Ty) : Prop :=
  ∃ common, TargetRenaming left common ∧ TargetRenaming right common

theorem TargetRenamingEquivalent.symm {left right : Ty}
    (equivalent : TargetRenamingEquivalent left right) :
    TargetRenamingEquivalent right left := by
  rcases equivalent with ⟨common, leftRenaming, rightRenaming⟩
  exact ⟨common, rightRenaming, leftRenaming⟩

/-- Retain the proof-relevant deterministic root long enough to expose the
local renaming from a published demand-directed target to the executable normal form.
This remains an internal bridge: public acceptance completeness still erases
the root at its existing Boolean boundary. -/
theorem SourceTyping.targetRenamingToExecutable
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typed : SourceTyping signature context expression target)
    (signatureWF : FrozenSigWF signature) :
    ∃ result : ExprResult,
      inferExprFuel (inferenceFuel expression) signature context [] []
        expression (initialState signature context) = some result ∧
      TargetRenaming target
        (result.state.prevailing.apply result.target) := by
  obtain ⟨rawTarget, finalSupply, terminal, derived, ledger, origin, audit,
    published⟩ := typed
  let complete : PairedAuditedSynthCompletenessAt terminal signature
      (inferenceFuel expression) := pairedAuditedSynthCompleteness
    (terminal := terminal) signatureWF.schemesClosed
    signatureWF.armExhaustiveBasic (inferenceFuel expression)
  let before := initialTraversalState signature context
  have contexts : ContextBisimulation before.prevailing context context :=
    ContextBisimulation.same before.prevailing context
  have contextBounded : Context.BoundedBy (initialSupply signature context)
      context := initialSupply_context_boundedBy signature context
  have adequate : SynthBudgetAdequate (inferenceFuel expression)
      expression := by
    change 8 * (exprTraversalFuel expression + 1) ≤
      8 * (exprTraversalFuel expression + 1)
    exact Nat.le_refl _
  have signatureBelow : SignatureVarsBelow
      (initialSupply signature context) signature :=
    DemandTypingInferenceCompletenessSignatureBounds.initial signature context
  rcases complete (selfEnv := []) (path := []) before signatureBelow contexts
      contextBounded contextBounded audit adequate with ⟨certified⟩
  let run := certified.raw.run
  refine ⟨run.result, run.success, run.transition.after.reverse,
    run.transition.after.forward, ?_, ?_, ?_⟩
  · rw [published]
    exact
      DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
        run.transition.after rawTarget
  · rw [published]
    exact run.target.reverse.symm
  · rw [published]
    exact run.target.forward.symm

/-- Published targets of any two audited derivations for the same source
term are unique modulo a local renaming of every residual capability and
ordinary-type metavariable.  This holds for arbitrary well-formed frozen
signatures and open contexts; no closed-program restriction is needed. -/
theorem SourceTyping.target_unique_modulo_renaming
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {left right : Ty}
    (leftTyped : SourceTyping signature context expression left)
    (rightTyped : SourceTyping signature context expression right)
    (signatureWF : FrozenSigWF signature) :
    TargetRenamingEquivalent left right := by
  rcases SourceTyping.targetRenamingToExecutable leftTyped signatureWF with
    ⟨leftResult, leftSuccess, leftRenaming⟩
  rcases SourceTyping.targetRenamingToExecutable rightTyped signatureWF with
    ⟨rightResult, rightSuccess, rightRenaming⟩
  have resultsEqual : leftResult = rightResult := by
    apply Option.some.inj
    exact leftSuccess.symm.trans rightSuccess
  have commonEqual :
      leftResult.state.prevailing.apply leftResult.target =
        rightResult.state.prevailing.apply rightResult.target :=
    congrArg (fun result : ExprResult =>
      result.state.prevailing.apply result.target) resultsEqual
  refine ⟨leftResult.state.prevailing.apply leftResult.target,
    leftRenaming, ?_⟩
  rw [commonEqual]
  exact rightRenaming

end DemandTypingTargetUniqueness
end TypePM
