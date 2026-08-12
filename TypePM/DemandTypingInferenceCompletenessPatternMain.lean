import TypePM.DemandTypingInferenceCompletenessPatternTraversal
import TypePM.DemandTypingInferenceCompletenessFuel
import TypePM.DemandTypingTerminalAuditTree

/-!
# User-pattern completeness dispatch

User patterns recurse into expression synthesis only at value-pattern nodes.
This module therefore keeps the pattern recursion acyclic by accepting an
audited expression-synthesis motive.  The eventual root expression recursion
discharges that motive; it is not a premise of the public completeness API.

The origin and terminal-audit trees are consumed together.  In particular,
the pattern-constructor branch retains its terminal `PatternCtorFacts` for the
later validator-coverage proof instead of reconstructing those facts from the
executable trace.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternMain

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessDataBisimulation

/-- The expression budget used at the value-pattern boundary. -/
abbrev PatternSynthBudgetAdequate (fuel : Nat) (expression : Expr) : Prop :=
  8 * (exprTraversalFuel expression + 1) ≤ fuel

/-- Weighted fuel for a complete user-pattern traversal. -/
abbrev PatternBudgetAdequate (fuel : Nat) (pattern : Pattern) : Prop :=
  8 * (patternTraversalFuel pattern + 1) ≤ fuel

/-- Traversal-stable expression synthesis required by value patterns. -/
abbrev PatternSynthCompletenessMotive
    (terminal : Subst) (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext executableContext →
    declarativeContext.BoundedBy q →
    DDSynthTerminalAudit terminal signature origin →
    PatternSynthBudgetAdequate fuel expression →
    Nonempty (SynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target)

/-- Context correspondence is compositional under source-order append. -/
theorem ContextBisimulation.append
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarativeLeft declarativeRight executableLeft executableRight : Context}
    (left : ContextBisimulation relation declarativeLeft executableLeft)
    (right : ContextBisimulation relation declarativeRight executableRight) :
    ContextBisimulation relation (declarativeLeft ++ declarativeRight)
      (executableLeft ++ executableRight) := by
  constructor
  · have pairEq :
        (declarativeLeft.applySubst S,
          declarativeRight.applySubst S) =
        ((executableLeft.applySubst state.prevailing).applySubst
            relation.forward,
          (executableRight.applySubst state.prevailing).applySubst
            relation.forward) :=
        Prod.ext left.forward right.forward
    simpa [Context.applySubst, List.map_append] using
      congrArg (fun pair : Context × Context => pair.1 ++ pair.2) pairEq
  · have pairEq :
        (executableLeft.applySubst state.prevailing,
          executableRight.applySubst state.prevailing) =
        ((declarativeLeft.applySubst S).applySubst relation.reverse,
          (declarativeRight.applySubst S).applySubst relation.reverse) :=
        Prod.ext left.reverse right.reverse
    simpa [Context.applySubst, List.map_append] using
      congrArg (fun pair : Context × Context => pair.1 ++ pair.2) pairEq

/-! ## Solver-free leaves -/

def patternPVarOrigin_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (freshName : name ∉ declarativeBindings.names) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path (.pvar name) state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      (declarativeBindings ++ [(name, .var q.nextTy)]) :=
  patternVar_complete fuel signature declarativeContext executableContext
    declarativeParameters executableParameters selfEnv path name before
    declarativeBindings executableBindings bindings freshName

def patternWildOrigin_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path .wild state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ declarativeBindings :=
  patternWild_complete fuel signature declarativeContext executableContext
    declarativeParameters executableParameters selfEnv path before
    declarativeBindings executableBindings bindings

noncomputable def patternPValOrigin_complete
    {terminal : Subst} {signature : FrozenSig}
    (synthComplete : PatternSynthCompletenessMotive terminal signature)
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q₁ : InferenceBase.FreshSupply} {S S₁ : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (contextBounded : declarativeContext.BoundedBy q)
    (bindingsBounded : declarativeBindings.BoundedBy q)
    {raw : DDSynth signature q S
      (declarativeBindings.toContext ++ declarativeContext) expression target
      q₁ S₁}
    {origin : DDSynthOrigin signature raw ledger ledger₁}
    (audit : DDSynthTerminalAudit terminal signature origin)
    (adequate : PatternBudgetAdequate (fuel + 1) (.pval expression)) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path
        (.pval expression) state)
      { q₁ with nextCap := q₁.nextCap + 1 } S₁
      (DDLedger.markFreshCap ledger₁ q₁) ⟨.var ⟨q₁.nextCap⟩, target⟩
      declarativeBindings := by
  have visitedBindings : MonoCtxBisimulation
      (before.visit .patternValue path).prevailing declarativeBindings
      executableBindings :=
    BisimulationExtension.transportMonoCtx
      (before.visitExtension .patternValue path) bindings
  have visitedContexts : ContextBisimulation
      (before.visit .patternValue path).prevailing declarativeContext
      executableContext := by
    constructor
    · change declarativeContext.applySubst S =
        (executableContext.applySubst state.prevailing).applySubst
          before.prevailing.forward
      exact contexts.forward
    · change executableContext.applySubst state.prevailing =
        (declarativeContext.applySubst S).applySubst
          before.prevailing.reverse
      exact contexts.reverse
  have expressionContexts : ContextBisimulation
      (before.visit .patternValue path).prevailing
      (declarativeBindings.toContext ++ declarativeContext)
      (executableBindings.toContext ++ executableContext) :=
    ContextBisimulation.append visitedBindings.toContext visitedContexts
  have expressionContextBounded :
      (declarativeBindings.toContext ++ declarativeContext).BoundedBy q :=
    Context.BoundedBy.append bindingsBounded.toContext contextBounded
  let expressionRun := Classical.choice
    (synthComplete (selfEnv := selfEnv) (path := 0 :: path)
      (before.visit .patternValue path) expressionContexts
      expressionContextBounded audit (by
        change 8 * (exprTraversalFuel expression + 1) ≤ fuel
        change 8 * ((1 + exprTraversalFuel expression) + 1) ≤ fuel + 1
          at adequate
        omega))
  exact patternValue_complete fuel signature declarativeContext
    executableContext declarativeParameters executableParameters selfEnv path
    expression before declarativeBindings executableBindings bindings
    expressionRun

noncomputable def patternEmbedOrigin_complete
    {signature : FrozenSig} {context : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {dual : Dual}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (parameters : PatternCtxBisimulation before.prevailing
      declarativeParameters executableParameters)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (lookup : declarativeParameters.find? name = some dual) :
    PatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context executableParameters
        executableBindings selfEnv path (.embed name) state)
      q S ledger dual declarativeBindings :=
  patternEmbed_complete fuel signature context selfEnv path name before
    declarativeParameters executableParameters parameters declarativeBindings
    executableBindings bindings lookup

end DemandTypingInferenceCompletenessPatternMain
end TypePM
