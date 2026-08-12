import TypePM.SourcePrincipality
import TypePM.DemandTypingInferenceCompletenessPairedRoot

/-!
# Context-relative principality

For an open source, an exact MGU may orient a constraint between two input
metavariables in either direction.  The correct principal object is therefore
the pair consisting of the terminal-normalized context and the published
target.  Both components must be transformed by one and the same paired
substitution.

This module does not introduce another source typing judgment.  A
`SourceTyping.TerminalPair` is only a view extracted from an already existing
audited `SourceTyping` proof.
-/

namespace TypePM

/-- Restriction is observationally invisible on a context whose free
variables are contained in the selected scopes. -/
theorem Context.applySubst_restrict
    (post : Subst) (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) (context : Context)
    (caps : ∀ varId, varId ∈ context.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ context.ftv → varId ∈ targetScope) :
    context.applySubst (post.restrict capScope targetScope) =
      context.applySubst post := by
  unfold Context.applySubst
  apply List.map_congr_left
  intro entry entryMember
  rcases entry with ⟨name, scheme⟩
  apply congrArg (fun result => (name, result))
  apply Scheme.applyMeta_eq_of_free_agree
  · intro varId member
    apply Subst.restrict_cap_of_mem post
    exact caps varId (List.mem_flatMap.mpr
      ⟨(name, scheme), entryMember, member⟩)
  · intro varId member
    apply Subst.restrict_target_of_mem post
    exact targets varId (List.mem_flatMap.mpr
      ⟨(name, scheme), entryMember, member⟩)

/-- One substitution simultaneously instantiates a context and its result
type.  The finite mutable scope is the union of the free variables in the
source pair. -/
def ContextTargetInstance
    (sourceContext : Context) (sourceTarget : Ty)
    (targetContext : Context) (targetTarget : Ty) : Prop :=
  ∃ post : Subst,
    post.cap.SupportWithin (sourceContext.fcv ++ sourceTarget.fcv) ∧
    post.target.SupportWithin (sourceContext.ftv ++ sourceTarget.ftv) ∧
    sourceContext.applySubst post = targetContext ∧
    post.apply sourceTarget = targetTarget

namespace ContextTargetInstance

theorem refl (context : Context) (target : Ty) :
    ContextTargetInstance context target context target := by
  exact ⟨Subst.id, CapSubst.id_supportWithin _, TySubst.id_supportWithin _,
    Context.applySubst_id context, Subst.apply_id target⟩

/-- Any unrestricted simultaneous action has an equivalent witness supported
on the source pair's actual finite free-variable scope. -/
theorem of_apply
    {sourceContext targetContext : Context} {sourceTarget targetTarget : Ty}
    (post : Subst)
    (contextEquation : sourceContext.applySubst post = targetContext)
    (targetEquation : post.apply sourceTarget = targetTarget) :
    ContextTargetInstance sourceContext sourceTarget targetContext
      targetTarget := by
  let capScope := sourceContext.fcv ++ sourceTarget.fcv
  let targetScope := sourceContext.ftv ++ sourceTarget.ftv
  let restricted := post.restrict capScope targetScope
  refine ⟨restricted,
    Subst.restrict_capSupport post capScope targetScope,
    Subst.restrict_targetSupport post capScope targetScope, ?_, ?_⟩
  · rw [Context.applySubst_restrict post capScope targetScope sourceContext
      (fun varId member => by simp [capScope, member])
      (fun varId member => by simp [targetScope, member])]
    exact contextEquation
  · rw [Subst.restrict_apply post capScope targetScope sourceTarget
      (fun varId member => by simp [capScope, member])
      (fun varId member => by simp [targetScope, member])]
    exact targetEquation

end ContextTargetInstance

namespace SourceTyping

/-- `normalizedContext` and the already-public target are the terminal view
of one audited source derivation.  This is a predicate over an existing
`SourceTyping` proof, not a second source judgment. -/
def TerminalPair
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty} (_typed : SourceTyping signature context expression target)
    (normalizedContext : Context) : Prop :=
  ∃ rawTarget finalSupply terminal,
    ∃ derived : DemandSynth signature
        (Inference.initialSupply signature context) Subst.id context expression
        rawTarget finalSupply terminal,
      ∃ ledger, ∃ origin : DemandSynthOrigin signature derived [] ledger,
        ∃ _audit : DemandSynthTerminalAudit terminal signature origin,
          normalizedContext = context.applySubst terminal ∧
          target = terminal.apply rawTarget

/-- Open the existential indices of `SourceTyping` only far enough to expose
its terminal-normalized context/target pair. -/
theorem terminalPair
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty} (typed : SourceTyping signature context expression target) :
    ∃ normalizedContext, TerminalPair typed normalizedContext := by
  rcases typed with
    ⟨rawTarget, _finalSupply, terminal, _derived, _ledger, _origin, _audit,
      published⟩
  exact ⟨context.applySubst terminal, rawTarget, _finalSupply, terminal,
    _derived, _ledger, _origin, _audit, rfl, published⟩

end SourceTyping

namespace DemandTypingRelativePrincipality

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessGlobalRecursion
open DemandTypingInferenceCompletenessGlobalRoot
open DemandTypingInferenceCompletenessGlobalCertified
open DemandTypingInferenceCompletenessPairedRoot
open DemandTypingInferenceCompletenessInitial
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessSignatureBounds
open DemandTypingInferenceCompletenessMain

/-- Every audited derivation determines a successful public inference run.
The run's resolved context/target pair and the derivation's terminal pair are
mutual instances under single substitutions. -/
theorem SourceTyping.contextTargetInstancesToInference
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typed : SourceTyping signature context expression target)
    (signatureWF : FrozenSigWF signature) :
    ∃ (result : ExprResult) (normalizedContext : Context),
      infer signature context expression = some result ∧
      SourceTyping.TerminalPair typed normalizedContext ∧
      ContextTargetInstance
        (Inference.ResolvedContext result.state.prevailing context)
        result.resolvedTarget normalizedContext target ∧
      ContextTargetInstance normalizedContext target
        (Inference.ResolvedContext result.state.prevailing context)
        result.resolvedTarget := by
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
  let root : PairedRootCertifiedSynthesis signature context expression :=
    { finalSupply := finalSupply
      terminal := terminal
      ledger := ledger
      target := rawTarget
      run := run
      history := certified.history
      validation := certified.validation }
  let normalizedContext := context.applySubst terminal
  have pair : SourceTyping.TerminalPair
      (show SourceTyping signature context expression target from
        ⟨rawTarget, finalSupply, terminal, derived, ledger, origin, audit,
          published⟩) normalizedContext :=
    ⟨rawTarget, finalSupply, terminal, derived, ledger, origin, audit, rfl,
      published⟩
  have forwardContext :
      (Inference.ResolvedContext run.result.state.prevailing context).applySubst
          run.transition.after.forward = normalizedContext := by
    change (context.applySubst run.result.state.prevailing).applySubst
        run.transition.after.forward = context.applySubst terminal
    exact (DemandTypingInferenceCompletenessContext.normalizedContext_forward
      run.transition.after context).symm
  have reverseContext : normalizedContext.applySubst
      run.transition.after.reverse =
        Inference.ResolvedContext run.result.state.prevailing context := by
    change (context.applySubst terminal).applySubst
        run.transition.after.reverse =
      context.applySubst run.result.state.prevailing
    calc
      (context.applySubst terminal).applySubst
          run.transition.after.reverse =
          context.applySubst
            (Subst.seq run.transition.after.reverse terminal) :=
        (Context.applySubst_seq run.transition.after.reverse terminal
          context).symm
      _ = context.applySubst run.result.state.prevailing := by
        rw [← run.transition.after.reverseEquation]
  have forwardTarget : run.transition.after.forward.apply
      run.result.resolvedTarget = target := by
    rw [published]
    exact run.target.forward.symm
  have reverseTarget : run.transition.after.reverse.apply target =
      run.result.resolvedTarget := by
    rw [published]
    exact run.target.reverse.symm
  refine ⟨run.result, normalizedContext,
    infer_eq_some_of_pairedRoot signatureWF root, pair,
    ContextTargetInstance.of_apply run.transition.after.forward
      forwardContext forwardTarget,
    ContextTargetInstance.of_apply run.transition.after.reverse
      reverseContext reverseTarget⟩

end DemandTypingRelativePrincipality

namespace Inference

open DemandTypingRelativePrincipality

/-- Context-relative principality of one successful public inference run.
For every audited source target, its own terminal-normalized context and
target are a simultaneous instance of the run's resolved pair.  The converse
instance is retained because the present calculus in fact proves uniqueness
modulo residual renaming. -/
theorem infer_relative_principal
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (signatureWF : FrozenSigWF signature)
    (success : infer signature context expression = some result) :
    ∀ {target}, (typed : SourceTyping signature context expression target) →
      ∃ normalizedContext,
        SourceTyping.TerminalPair typed normalizedContext ∧
        ContextTargetInstance
          (ResolvedContext result.state.prevailing context)
          result.resolvedTarget normalizedContext target ∧
        ContextTargetInstance normalizedContext target
          (ResolvedContext result.state.prevailing context)
          result.resolvedTarget := by
  intro target typed
  rcases SourceTyping.contextTargetInstancesToInference typed signatureWF with
    ⟨other, normalizedContext, otherSuccess, pair, forward, reverse⟩
  have resultEq : other = result := Option.some.inj (otherSuccess.symm.trans success)
  subst other
  exact ⟨normalizedContext, pair, forward, reverse⟩

/-- In an empty source context, the relative theorem reduces to ordinary
target principality because every normalized context is still empty. -/
theorem infer_closed_relative_principal
    {signature : FrozenSig} {expression : Expr} {result : ExprResult}
    (signatureWF : FrozenSigWF signature)
    (success : infer signature [] expression = some result) :
    ∀ {target}, SourceTyping signature [] expression target →
      TypeInstance result.resolvedTarget target := by
  intro target typed
  exact (inferType_principal signatureWF (by
    simp [inferType, success])).2 target typed

end Inference
end TypePM
