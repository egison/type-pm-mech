import TypePM.DemandTypingInferenceCompletenessPatternMain

/-!
# Terminal-audited user-pattern dispatch

This module separates pattern and pattern-list recursion through strict fuel
ceilings.  Keeping the two dependent families out of one Lean `mutual` block
prevents their context and pattern-context indices from being generalized
independently by the mutual elaborator.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternDispatcher

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessPatternMain

/-- Completeness for one user pattern, available strictly below `bound`. -/
structure PatternCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop where
  complete : ∀ {fuel : Nat}, fuel < bound →
    ∀ {declarativeContext executableContext : Context}
      {declarativeParameters executableParameters : PatternCtx}
      {declarativeBindings executableBindings : MonoCtx}
      {selfEnv : SelfEnv} {path : SyntaxPath} {pattern : Pattern}
      {dual : Dual} {bindings' : MonoCtx}
      {q q' : InferenceBase.FreshSupply} {S S' : Subst}
      {ledger ledger' : CapabilityOriginLedger} {state : InferState}
      {raw : DDPattern signature q S declarativeContext declarativeParameters
        declarativeBindings pattern dual bindings' q' S'}
      {origin : DDPatternOrigin signature raw ledger ledger'},
      (before : TraversalStateCorrespondence q S ledger state) →
      ContextBisimulation before.prevailing declarativeContext
        executableContext →
      PatternCtxBisimulation before.prevailing declarativeParameters
        executableParameters →
      MonoCtxBisimulation before.prevailing declarativeBindings
        executableBindings →
      declarativeContext.BoundedBy q →
      declarativeParameters.BoundedBy q →
      declarativeBindings.BoundedBy q →
      executableContext.BoundedBy q →
      executableParameters.BoundedBy q →
      executableBindings.BoundedBy q →
      DDPatternTerminalAudit terminal signature origin →
      PatternBudgetAdequate fuel pattern →
      Nonempty (BoundedPatternRunCompletion before
        (inferPatternFuel fuel signature executableContext executableParameters
          executableBindings selfEnv path pattern state)
        q' S' ledger' dual bindings')

def PatternCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : PatternCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    PatternCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

/-- Pattern-list dispatch, parameterized only by pattern completeness at
strictly smaller fuel.  The tail remains ordinary structural recursion on
the predecessor fuel. -/
theorem patternsOrigin_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {index : Nat}
    {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (patternBelow : PatternCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (parameters : PatternCtxBisimulation before.prevailing
      declarativeParameters executableParameters)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (contextBounded : declarativeContext.BoundedBy q)
    (parametersBounded : declarativeParameters.BoundedBy q)
    (bindingsBounded : declarativeBindings.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (executableParametersBounded : executableParameters.BoundedBy q)
    (executableBindingsBounded : executableBindings.BoundedBy q)
    {raw : DDPatterns signature q S declarativeContext declarativeParameters
      declarativeBindings patterns duals bindings' q' S'}
    {origin : DDPatternsOrigin signature raw ledger ledger'}
    (audit : DDPatternsTerminalAudit terminal signature origin)
    (adequate : PatternsBudgetAdequate fuel patterns) :
    Nonempty (BoundedPatternsRunCompletion before
      (inferPatternsFuel fuel signature executableContext executableParameters
        executableBindings selfEnv path index patterns state)
      q' S' ledger' duals bindings') := by
  cases fuel with
  | zero => simp [PatternsBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil =>
          exact ⟨boundedPatternsNil_complete inner before declarativeBindings
            bindings executableBindingsBounded⟩
      | cons headAudit tailAudit =>
          rename_i pattern dual bindings₁ q₁ S₁ ledger₁ patterns duals
            headRaw tailRaw headOrigin tailOrigin
          have headAdequate : PatternBudgetAdequate inner pattern := by
            simp only [PatternsBudgetAdequate, PatternBudgetAdequate,
              patternListTraversalFuel] at adequate ⊢
            omega
          have tailAdequate : PatternsBudgetAdequate inner patterns := by
            simp only [PatternsBudgetAdequate, patternListTraversalFuel]
              at adequate ⊢
            omega
          let head := Classical.choice
            (patternBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := index :: path) before contexts
              parameters bindings contextBounded parametersBounded
              bindingsBounded executableContextBounded
              executableParametersBounded executableBindingsBounded headAudit
              headAdequate)
          let headExtends := headOrigin.erase.supplyExtends
          obtain ⟨_, _, declarativeBindings₁Bounded⟩ :=
            headOrigin.erase.boundedBy closed before.declarative_bounded
              contextBounded parametersBounded bindingsBounded
          let tail := Classical.choice
            (patternsOrigin_complete_nonempty closed (selfEnv := selfEnv)
              (path := path) (index := index + 1) inner
              (patternBelow.mono (Nat.le_succ inner)) head.run.completion
              (contexts.transport head.run.transition)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                head.run.transition parameters)
              head.run.bindings (contextBounded.mono headExtends)
              (parametersBounded.mono headExtends)
              declarativeBindings₁Bounded
              (executableContextBounded.mono headExtends)
              (executableParametersBounded.mono headExtends)
              head.rawBindingsBounded tailAudit tailAdequate)
          exact ⟨boundedPatternsCons_complete before head tail
            tailOrigin.erase.supplyExtends⟩
termination_by fuel

end DemandTypingInferenceCompletenessPatternDispatcher
end TypePM
