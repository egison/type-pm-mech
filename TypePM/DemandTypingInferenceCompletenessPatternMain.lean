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
open DemandTypingInferenceCompletenessAlignmentTraversal
open DemandTypingInferenceCompletenessAlignmentFamilies
open DemandTypingInferenceCompletenessPatternCtorCapability

/-- The expression budget used at the value-pattern boundary. -/
abbrev PatternSynthBudgetAdequate (fuel : Nat) (expression : Expr) : Prop :=
  8 * (exprTraversalFuel expression + 1) ≤ fuel

/-- Weighted fuel for a complete user-pattern traversal. -/
abbrev PatternBudgetAdequate (fuel : Nat) (pattern : Pattern) : Prop :=
  8 * (patternTraversalFuel pattern + 1) ≤ fuel

abbrev PatternsBudgetAdequate
    (fuel : Nat) (patterns : List Pattern) : Prop :=
  8 * (patternListTraversalFuel patterns + 1) ≤ fuel

/-- Raw executable outputs needed by the next sibling or alignment cut. -/
structure BoundedPatternRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  run : PatternRunCompletion before operation q' declarative ledger dual bindings
  rawDualBounded : run.result.dual.BoundedBy q'
  rawBindingsBounded : run.result.bindings.BoundedBy q'

structure BoundedPatternsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  run : PatternsRunCompletion before operation q' declarative ledger duals bindings
  rawDualsBounded : ∀ dual ∈ run.result.duals, dual.BoundedBy q'
  rawBindingsBounded : run.result.bindings.BoundedBy q'

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
    Nonempty { run : SynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target // run.result.target.BoundedBy q' }

/-- Taking capabilities pointwise from corresponding duals preserves the
same state relation. -/
theorem DualListBisimulation.capabilities
    {ledger : CapabilityOriginLedger} {S : Subst} {state : InferState}
    {relation : StateBisimulation ledger S state}
    {declarative executable : List Dual}
    (related : DualListBisimulation relation declarative executable) :
    CapListBisimulation relation (declarative.map Dual.cap)
      (executable.map Dual.cap) := by
  induction related with
  | nil => exact .nil
  | cons head tail induction => exact .cons head.cap induction

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

def boundedPatternPVarOrigin_complete
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
    (executableBindingsBounded : executableBindings.BoundedBy q)
    (freshName : name ∉ declarativeBindings.names) :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path (.pvar name) state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      (declarativeBindings ++ [(name, .var q.nextTy)]) := by
  let run := patternPVarOrigin_complete
    (signature := signature) (declarativeContext := declarativeContext)
    (executableContext := executableContext)
    (declarativeParameters := declarativeParameters)
    (executableParameters := executableParameters) (selfEnv := selfEnv)
    (path := path) fuel before bindings freshName
  have executableAbsent : name ∉ executableBindings.names := by
    rw [← bindings.names_eq]
    exact freshName
  refine ⟨run, ?_, ?_⟩
  · have dualEq :
        ⟨.var ⟨state.supply.nextCap⟩, .var state.supply.nextTy⟩ =
          run.result.dual := by
      simpa [inferPatternFuel, executableAbsent, InferState.freshCap,
        InferState.freshTy, InferenceBase.freshCapMeta,
        InferenceBase.freshTyMeta] using
        congrArg (Option.map PatternResult.dual) run.success
    rw [← dualEq]
    constructor
    · apply Cap.BoundedBy.varOf
      change state.supply.nextCap < q.nextCap + 1
      rw [before.supply_eq]
      omega
    · apply Ty.BoundedBy.varOf
      change state.supply.nextTy < q.nextTy + 1
      rw [before.supply_eq]
      omega
  · have bindingsEq :
        executableBindings ++ [(name, .var state.supply.nextTy)] =
          run.result.bindings := by
      simpa [inferPatternFuel, executableAbsent, InferState.freshCap,
        InferState.freshTy, InferenceBase.freshCapMeta,
        InferenceBase.freshTyMeta] using
        congrArg (Option.map PatternResult.bindings) run.success
    rw [← bindingsEq]
    apply MonoCtx.BoundedBy.append
    · exact executableBindingsBounded.mono (SupplyExtends.bumpBoth q 1 1)
    · exact MonoCtx.BoundedBy.cons (Ty.BoundedBy.varOf (by
        change state.supply.nextTy < q.nextTy + 1
        rw [before.supply_eq]
        omega)) (by
        intro entry membership
        exact nomatch membership)

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

def boundedPatternWildOrigin_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableBindingsBounded : executableBindings.BoundedBy q) :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path .wild state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ declarativeBindings := by
  let run := patternWildOrigin_complete
    (signature := signature) (declarativeContext := declarativeContext)
    (executableContext := executableContext)
    (declarativeParameters := declarativeParameters)
    (executableParameters := executableParameters) (selfEnv := selfEnv)
    (path := path) fuel before bindings
  refine ⟨run, ?_, ?_⟩
  · have dualEq :
        ⟨.var ⟨state.supply.nextCap⟩, .var state.supply.nextTy⟩ =
          run.result.dual := by
      simpa [inferPatternFuel, InferState.freshCap, InferState.freshTy,
        InferenceBase.freshCapMeta, InferenceBase.freshTyMeta] using
        congrArg (Option.map PatternResult.dual) run.success
    rw [← dualEq]
    constructor
    · apply Cap.BoundedBy.varOf
      change state.supply.nextCap < q.nextCap + 1
      rw [before.supply_eq]
      omega
    · apply Ty.BoundedBy.varOf
      change state.supply.nextTy < q.nextTy + 1
      rw [before.supply_eq]
      omega
  · have bindingsEq : executableBindings = run.result.bindings := by
      simpa [inferPatternFuel, InferState.freshCap, InferState.freshTy,
        InferenceBase.freshCapMeta, InferenceBase.freshTyMeta] using
        congrArg (Option.map PatternResult.bindings) run.success
    rw [← bindingsEq]
    exact executableBindingsBounded.mono (SupplyExtends.bumpBoth q 1 1)

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
  let expressionPackage := Classical.choice
    (synthComplete (selfEnv := selfEnv) (path := 0 :: path)
      (before.visit .patternValue path) expressionContexts
      expressionContextBounded audit (by
        change 8 * (exprTraversalFuel expression + 1) ≤ fuel
        change 8 * ((1 + exprTraversalFuel expression) + 1) ≤ fuel + 1
          at adequate
        omega))
  let expressionRun := expressionPackage.val
  exact patternValue_complete fuel signature declarativeContext
    executableContext declarativeParameters executableParameters selfEnv path
    expression before declarativeBindings executableBindings bindings
    expressionRun

noncomputable def boundedPatternPValOrigin_complete
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
    (executableBindingsBounded : executableBindings.BoundedBy q)
    {raw : DDSynth signature q S
      (declarativeBindings.toContext ++ declarativeContext) expression target
      q₁ S₁}
    {origin : DDSynthOrigin signature raw ledger ledger₁}
    (audit : DDSynthTerminalAudit terminal signature origin)
    (adequate : PatternBudgetAdequate (fuel + 1) (.pval expression)) :
    BoundedPatternRunCompletion before
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
    · exact contexts.forward
    · exact contexts.reverse
  have expressionContexts : ContextBisimulation
      (before.visit .patternValue path).prevailing
      (declarativeBindings.toContext ++ declarativeContext)
      (executableBindings.toContext ++ executableContext) :=
    ContextBisimulation.append visitedBindings.toContext visitedContexts
  have expressionContextBounded :
      (declarativeBindings.toContext ++ declarativeContext).BoundedBy q :=
    Context.BoundedBy.append bindingsBounded.toContext contextBounded
  let expressionPackage := Classical.choice
    (synthComplete (selfEnv := selfEnv) (path := 0 :: path)
      (before.visit .patternValue path) expressionContexts
      expressionContextBounded audit (by
        change 8 * (exprTraversalFuel expression + 1) ≤ fuel
        change 8 * ((1 + exprTraversalFuel expression) + 1) ≤ fuel + 1
          at adequate
        omega))
  let run := patternValue_complete fuel signature declarativeContext
    executableContext declarativeParameters executableParameters selfEnv path
    expression before declarativeBindings executableBindings bindings
    expressionPackage.val
  refine ⟨run, ?_, ?_⟩
  · have dualEq :
        ⟨.var ⟨expressionPackage.val.result.state.supply.nextCap⟩,
          expressionPackage.val.result.target⟩ = run.result.dual := by
      have mapped := congrArg (Option.map PatternResult.dual) run.success
      simp only [inferPatternFuel] at mapped
      rw [expressionPackage.val.success] at mapped
      simpa [InferState.freshCap, InferenceBase.freshCapMeta] using mapped
    rw [← dualEq]
    constructor
    · apply Cap.BoundedBy.varOf
      change expressionPackage.val.result.state.supply.nextCap <
        q₁.nextCap + 1
      rw [expressionPackage.val.supply_eq]
      omega
    · exact expressionPackage.property.mono (SupplyExtends.bumpCap q₁ 1)
  · have bindingsEq : executableBindings = run.result.bindings := by
      have mapped := congrArg (Option.map PatternResult.bindings) run.success
      simp only [inferPatternFuel] at mapped
      rw [expressionPackage.val.success] at mapped
      simpa using mapped
    rw [← bindingsEq]
    exact executableBindingsBounded.mono
      (origin.erase.supplyExtends.trans (SupplyExtends.bumpCap q₁ 1))

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

noncomputable def boundedPatternEmbedOrigin_complete
    {signature : FrozenSig} {context : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {dual : Dual}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (parameters : PatternCtxBisimulation before.prevailing
      declarativeParameters executableParameters)
    (executableParametersBounded : executableParameters.BoundedBy q)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableBindingsBounded : executableBindings.BoundedBy q)
    (lookup : declarativeParameters.find? name = some dual) :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context executableParameters
        executableBindings selfEnv path (.embed name) state)
      q S ledger dual declarativeBindings := by
  let witness := PatternCtxBisimulation.find?_complete parameters lookup
  let executableDual := Classical.choose witness
  have executableLookup := (Classical.choose_spec witness).1
  let run := patternEmbedOrigin_complete
    (signature := signature) (context := context) (selfEnv := selfEnv)
    (path := path) fuel before parameters bindings lookup
  refine ⟨run, ?_, ?_⟩
  · have dualEq : executableDual = run.result.dual := by
      have resultEq := run.success
      simp only [inferPatternFuel] at resultEq
      rw [executableLookup] at resultEq
      exact congrArg PatternResult.dual (Option.some.inj resultEq)
    rw [← dualEq]
    exact executableParametersBounded.find? executableLookup
  · have bindingsEq : executableBindings = run.result.bindings := by
      have resultEq := run.success
      simp only [inferPatternFuel] at resultEq
      rw [executableLookup] at resultEq
      exact congrArg PatternResult.bindings (Option.some.inj resultEq)
    rw [← bindingsEq]
    exact executableBindingsBounded

/-! ## Bounded list and tuple packaging -/

def boundedPatternsNil_complete
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {executableBindings : MonoCtx} {selfEnv : SelfEnv} {path : SyntaxPath}
    {index : Nat} {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (declarativeBindings : MonoCtx)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableBindingsBounded : executableBindings.BoundedBy q) :
    BoundedPatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path index [] state)
      q S ledger [] declarativeBindings := by
  let run := patternsNil_complete fuel signature context parameters selfEnv
    path index before declarativeBindings executableBindings bindings
  refine ⟨run, ?_, ?_⟩
  · intro dual membership
    have dualsEq : ([] : List Dual) = run.result.duals := by
      simpa [inferPatternsFuel] using
        congrArg (Option.map PatternsResult.duals) run.success
    rw [← dualsEq] at membership
    exact nomatch membership
  · have bindingsEq : executableBindings = run.result.bindings := by
      simpa [inferPatternsFuel] using
        congrArg (Option.map PatternsResult.bindings) run.success
    rw [← bindingsEq]
    exact executableBindingsBounded

def boundedPatternsCons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {selfEnv : SelfEnv} {parent : SyntaxPath}
    {index : Nat} {pattern : Pattern} {patterns : List Pattern}
    {executableBindings : MonoCtx}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    {dual : Dual} {duals : List Dual} {bindings₁ bindings' : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (head : BoundedPatternRunCompletion before
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (index :: parent) pattern state)
      q₁ S₁ ledger₁ dual bindings₁)
    (tail : BoundedPatternsRunCompletion head.run.completion
      (inferPatternsFuel fuel signature context parameters
        head.run.result.bindings selfEnv parent (index + 1) patterns
        head.run.result.state)
      q' S' ledger' duals bindings')
    (tailExtends : SupplyExtends q₁ q') :
    BoundedPatternsRunCompletion before
      (inferPatternsFuel (fuel + 1) signature context parameters
        executableBindings selfEnv parent index (pattern :: patterns) state)
      q' S' ledger' (dual :: duals) bindings' := by
  let run := patternsCons_complete fuel signature context parameters selfEnv
    parent index pattern patterns before head.run tail.run
  refine ⟨run, ?_, ?_⟩
  · have dualsEq : head.run.result.dual :: tail.run.result.duals =
        run.result.duals := by
      have mapped := congrArg (Option.map PatternsResult.duals) run.success
      simp only [inferPatternsFuel] at mapped
      simp only [head.run.success, tail.run.success] at mapped
      exact Option.some.inj mapped
    rw [← dualsEq]
    intro item membership
    rcases List.mem_cons.mp membership with rfl | tailMembership
    · exact head.rawDualBounded.mono tailExtends
    · exact tail.rawDualsBounded item tailMembership
  · have bindingsEq : tail.run.result.bindings = run.result.bindings := by
      have mapped := congrArg (Option.map PatternsResult.bindings) run.success
      simp only [inferPatternsFuel] at mapped
      simp only [head.run.success, tail.run.success] at mapped
      exact Option.some.inj mapped
    rw [← bindingsEq]
    exact tail.rawBindingsBounded

def boundedPatternTuple_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {patterns : List Pattern}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {duals : List Dual} {bindings : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (children : BoundedPatternsRunCompletion
      (before.visit .patternTuple path)
      (inferPatternsFuel fuel signature context parameters executableBindings
        selfEnv path 0 patterns (visit state .patternTuple path))
      q' S' ledger' duals bindings) :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.ptuple patterns) state)
      q' S' ledger'
      ⟨.prod (duals.map Dual.cap), .prod (duals.map Dual.target)⟩ bindings := by
  let run := patternTuple_complete fuel signature context parameters parameters
    selfEnv path patterns before executableBindings children.run
  refine ⟨run, ?_, ?_⟩
  · have dualEq :
        ⟨.prod (children.run.result.duals.map Dual.cap),
          .prod (children.run.result.duals.map Dual.target)⟩ =
            run.result.dual := by
      have mapped := congrArg (Option.map PatternResult.dual) run.success
      simp only [inferPatternFuel] at mapped
      rw [children.run.success] at mapped
      exact Option.some.inj mapped
    rw [← dualEq]
    constructor
    · apply Cap.BoundedBy.prodOfForall
      intro capability membership
      obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
      exact (children.rawDualsBounded dual dualMem).1
    · apply Ty.BoundedBy.prodOfForall
      intro target membership
      obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
      exact (children.rawDualsBounded dual dualMem).2
  · have bindingsEq : children.run.result.bindings = run.result.bindings := by
      have mapped := congrArg (Option.map PatternResult.bindings) run.success
      simp only [inferPatternFuel] at mapped
      rw [children.run.success] at mapped
      exact Option.some.inj mapped
    rw [← bindingsEq]
    exact children.rawBindingsBounded

noncomputable def boundedPatternAnd_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {selfEnv : SelfEnv} {path : SyntaxPath}
    {left right : Pattern} {executableBindings : MonoCtx}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger} {state : InferState}
    {leftDual rightDual : Dual} {leftBindings bindings' : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (leftRun : BoundedPatternRunCompletion (before.visit .patternAnd path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternAnd path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : BoundedPatternRunCompletion leftRun.run.completion
      (inferPatternFuel fuel signature context parameters
        leftRun.run.result.bindings selfEnv (1 :: path) right
        leftRun.run.result.state)
      q₂ S₂ ledger₂ rightDual bindings')
    (rightExtends : SupplyExtends q₁ q₂)
    (declarativeLeftBounded : leftDual.BoundedBy q₂)
    (declarativeRightBounded : rightDual.BoundedBy q₂)
    (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S') :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.pand left right) state)
      q₂ S' ledger₂ leftDual bindings' := by
  let run := patternAnd_complete fuel signature context parameters selfEnv path
    left right before executableBindings leftRun.run rightRun.run
    declarativeLeftBounded declarativeRightBounded
    (leftRun.rawDualBounded.mono rightExtends) rightRun.rawDualBounded aligned
  refine ⟨run, ?_, ?_⟩
  · change leftRun.run.result.dual.BoundedBy q₂
    exact leftRun.rawDualBounded.mono rightExtends
  · change rightRun.run.result.bindings.BoundedBy q₂
    exact rightRun.rawBindingsBounded

noncomputable def boundedPatternOr_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {selfEnv : SelfEnv} {path : SyntaxPath}
    {left right : Pattern} {executableBindings : MonoCtx}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S₃ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger} {state : InferState}
    {leftDual rightDual : Dual} {leftBindings rightBindings : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (leftRun : BoundedPatternRunCompletion (before.visit .patternOr path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternOr path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : BoundedPatternRunCompletion leftRun.run.completion
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (1 :: path) right leftRun.run.result.state)
      q₂ S₂ ledger₂ rightDual rightBindings)
    (rightExtends : SupplyExtends q₁ q₂)
    (declarativeLeftDualBounded : leftDual.BoundedBy q₂)
    (declarativeRightDualBounded : rightDual.BoundedBy q₂)
    (declarativeLeftBindingsBounded : leftBindings.BoundedBy q₂)
    (declarativeRightBindingsBounded : rightBindings.BoundedBy q₂)
    (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S₃)
    (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃ leftBindings
      rightBindings S') :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.por left right) state)
      q₂ S' ledger₂ leftDual leftBindings := by
  let run := patternOr_complete fuel signature context parameters selfEnv path
    left right before executableBindings leftRun.run rightRun.run
    declarativeLeftDualBounded declarativeRightDualBounded
    (leftRun.rawDualBounded.mono rightExtends) rightRun.rawDualBounded
    declarativeLeftBindingsBounded declarativeRightBindingsBounded
    (leftRun.rawBindingsBounded.mono rightExtends)
    rightRun.rawBindingsBounded dualsAligned bindingsAligned
  refine ⟨run, ?_, ?_⟩
  · change leftRun.run.result.dual.BoundedBy q₂
    exact leftRun.rawDualBounded.mono rightExtends
  · change leftRun.run.result.bindings.BoundedBy q₂
    exact leftRun.rawBindingsBounded.mono rightExtends

/-! ## Pattern constructors -/

structure BoundedPatternCtorCapRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option (Cap × InferState))
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (capability : Cap) : Type where
  run : PatternCtorCapRunCompletion before operation q' declarative ledger
    capability
  rawCapabilityBounded : run.result.1.BoundedBy q'

/-- Traversal-stable completeness required from the isolated
pattern-constructor capability solver.  This is deliberately a universally
quantified internal motive, rather than a caller-supplied executable success
premise.  The package includes the executable compatibility check needed by
the enclosing `pctor` branch. -/
abbrev PatternCtorCapCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {entry : PatternCtorScheme signature.observability}
    {constraintOrigin : ConstraintOrigin}
    {declarativeChildren executableChildren : List Cap}
    {capability : Cap} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {state : InferState}
    {raw : DDPatternCtorCap signature entry q S declarativeChildren capability
      q' S'}
    {rawOrigin : DDPatternCtorCapOrigin signature entry raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    CapListBisimulation before.prevailing declarativeChildren
      executableChildren →
    (∀ child ∈ declarativeChildren, child.BoundedBy q) →
    (∀ child ∈ executableChildren, child.BoundedBy q) →
    Nonempty { run : BoundedPatternCtorCapRunCompletion before
      (solvePatternCtorCapability signature entry constraintOrigin
        executableChildren state) q' S' ledger' capability //
      capCompatibleCheck entry
        (executableChildren.map fun child =>
          child.apply run.run.result.2.prevailing.cap)
        (run.run.result.1.apply run.run.result.2.prevailing.cap) = true }

noncomputable def boundedPatternCtor_complete
    {fuel : Nat} {signature : FrozenSig}
    {context : Context} {parameters : PatternCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {name : String} {patterns : List Pattern}
    {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (closed : signature.SchemesClosed)
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S₃ : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {state : InferState} {executableBindings : MonoCtx}
    {duals : List Dual} {bindings' : MonoCtx} {capability : Cap}
    (before : TraversalStateCorrespondence q S ledger state)
    (children :
      let instantiation := instantiateCtorInState_complete before entry.scheme
      BoundedPatternsRunCompletion
        (instantiation.correspondence.visit .patternCtor path)
        (inferPatternsFuel fuel signature context parameters
          executableBindings selfEnv path 0 patterns
          (visit (instantiateCtorInState state entry.scheme).2
            .patternCtor path))
        q₁ S₁ ledger₁ duals bindings')
    (childrenExtends : SupplyExtends
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply q₁)
    (declarativeDualsBounded : ∀ dual ∈ duals, dual.BoundedBy q₁)
    (targetsAligned : DDAlignTargetListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂)
    (capRun :
      let instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      let declarativeTargetsBounded : ∀ target ∈
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.1,
          target.BoundedBy q₁ := fun target membership =>
        (instBounded.1 target membership).mono childrenExtends
      let executableTargetsBounded : ∀ target ∈
          (instantiateCtorInState state entry.scheme).1.1,
          target.BoundedBy q₁ := fun target membership =>
        (by
          have argumentEq : (instantiateCtorInState state entry.scheme).1.1 =
              (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 := by
            simp [Inference.instantiateCtorInState, before.supply_eq]
          rw [argumentEq] at membership
          have atInst : target.BoundedBy
              (InferenceBase.instantiateCtorScheme q entry.scheme).supply := by
            exact instBounded.1 target membership
          exact atInst.mono childrenExtends)
      let targetAlignment := ddAlignTargetListWithLedger_complete
        (origin := freshOrigin .pattern path "pattern-constructor-fields")
        children.run.completion children.run.duals
        (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
          ((instantiateCtorInState_complete before entry.scheme).correspondence.visitExtension
            .patternCtor path |>.seq children.run.transition)
          (instantiateCtorInState_complete before entry.scheme).arguments)
        declarativeDualsBounded declarativeTargetsBounded
        children.rawDualsBounded executableTargetsBounded targetsAligned
      BoundedPatternCtorCapRunCompletion targetAlignment.completion
        (solvePatternCtorCapability signature entry
          (freshOrigin .pattern path "pattern-constructor-capability")
          (children.run.result.duals.map Dual.cap) targetAlignment.result)
        q₂ S₃ ledger₂ capability)
    (childrenToCapExtends : SupplyExtends q₁ q₂)
    (compatible : capCompatibleCheck entry
      ((children.run.result.duals.map Dual.cap).map fun child =>
        child.apply capRun.run.result.2.prevailing.cap)
      (capRun.run.result.1.apply capRun.run.result.2.prevailing.cap) = true) :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.pctor name patterns) state)
      q₂ S₃
      (DDLedger.freezeExport ledger₂ S₃
        (freshCapImages q entry.scheme.capBinders)
        (capabilityExportPayload [capability]
          ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
            bindings'.map fun binding => binding.2)))
      ⟨capability,
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2⟩
      bindings' := by
  let instBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.patternCtors lookup).boundedBy)
  have declarativeTargetsBounded : ∀ target ∈
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1,
      target.BoundedBy q₁ := by
    intro target membership
    exact (instBounded.1 target membership).mono childrenExtends
  have executableTargetsBounded : ∀ target ∈
      (instantiateCtorInState state entry.scheme).1.1,
      target.BoundedBy q₁ := by
    intro target membership
    have argumentEq : (instantiateCtorInState state entry.scheme).1.1 =
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 := by
      simp [Inference.instantiateCtorInState, before.supply_eq]
    rw [argumentEq] at membership
    have atInst : target.BoundedBy
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply := by
      exact instBounded.1 target membership
    exact atInst.mono childrenExtends
  let run := patternCtor_complete fuel signature context parameters selfEnv path
    name patterns lookup before executableBindings children.run
    declarativeDualsBounded declarativeTargetsBounded children.rawDualsBounded
    executableTargetsBounded targetsAligned capRun.run compatible
  refine ⟨run, ?_, ?_⟩
  · change (⟨capRun.run.result.1,
      (instantiateCtorInState state entry.scheme).1.2⟩ : Dual).BoundedBy q₂
    constructor
    · exact capRun.rawCapabilityBounded
    · have atInst : (instantiateCtorInState state entry.scheme).1.2.BoundedBy
          (InferenceBase.instantiateCtorScheme q entry.scheme).supply := by
        simpa [Inference.instantiateCtorInState, before.supply_eq] using
          instBounded.2
      exact atInst.mono (childrenExtends.trans childrenToCapExtends)
  · change children.run.result.bindings.BoundedBy q₂
    exact children.rawBindingsBounded.mono childrenToCapExtends

/-! ## Pattern-function applications -/

noncomputable def boundedPatternApp_complete
    {fuel : Nat} {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {patterns : List Pattern} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    (closed : signature.SchemesClosed)
    {q q₁ : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    {duals : List Dual} {bindings' : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (children :
      let instantiation := instantiateDualInState_complete before signature
        executableContext executableParameters executableBindings
        (executableContext.applySubst state.prevailing)
        (executableParameters.applySubst state.prevailing)
        (executableBindings.applySubst state.prevailing) scheme
      BoundedPatternsRunCompletion
        (instantiation.correspondence.visit .patternApp path)
        (inferPatternsFuel fuel signature executableContext
          executableParameters executableBindings selfEnv path 0 patterns
          (visit (instantiateDualInState signature executableContext
            executableParameters executableBindings
            (executableContext.applySubst state.prevailing)
            (executableParameters.applySubst state.prevailing)
            (executableBindings.applySubst state.prevailing) state scheme).2
            .patternApp path))
        q₁ S₁ ledger₁ duals bindings')
    (childrenExtends : SupplyExtends
      (InferenceBase.instantiateDualScheme q scheme).supply q₁)
    (declarativeDualsBounded : ∀ dual ∈ duals, dual.BoundedBy q₁)
    (aligned : DDAlignDualListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateDualScheme q scheme).value.1 S') :
    BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path
        (.papp name patterns) state)
      q₁ S' ledger₁
      (InferenceBase.instantiateDualScheme q scheme).value.2 bindings' := by
  let instBounded := instantiateDualScheme_boundedBy (q := q)
    ((closed.patternFuns lookup).boundedBy)
  have declarativeExpectedBounded : ∀ dual ∈
      (InferenceBase.instantiateDualScheme q scheme).value.1,
      dual.BoundedBy q₁ := by
    intro dual membership
    exact (instBounded.1 dual membership).mono childrenExtends
  have executableExpectedBounded : ∀ dual ∈
      (instantiateDualInState signature executableContext
        executableParameters executableBindings
        (executableContext.applySubst state.prevailing)
        (executableParameters.applySubst state.prevailing)
        (executableBindings.applySubst state.prevailing) state scheme).1.1,
      dual.BoundedBy q₁ := by
    intro dual membership
    have argumentEq :
        (instantiateDualInState signature executableContext
          executableParameters executableBindings
          (executableContext.applySubst state.prevailing)
          (executableParameters.applySubst state.prevailing)
          (executableBindings.applySubst state.prevailing) state scheme).1.1 =
        (InferenceBase.instantiateDualScheme q scheme).value.1 := by
      simp [Inference.instantiateDualInState, before.supply_eq]
    rw [argumentEq] at membership
    exact (instBounded.1 _ membership).mono childrenExtends
  let run := patternApp_complete fuel signature declarativeContext
    executableContext declarativeParameters executableParameters
    declarativeBindings executableBindings selfEnv path name patterns lookup
    before children.run declarativeDualsBounded children.rawDualsBounded
    declarativeExpectedBounded executableExpectedBounded aligned
  refine ⟨run, ?_, ?_⟩
  · change
      (instantiateDualInState signature executableContext
        executableParameters executableBindings
        (executableContext.applySubst state.prevailing)
        (executableParameters.applySubst state.prevailing)
        (executableBindings.applySubst state.prevailing) state scheme).1.2.BoundedBy q₁
    have targetEq :
        (instantiateDualInState signature executableContext
          executableParameters executableBindings
          (executableContext.applySubst state.prevailing)
          (executableParameters.applySubst state.prevailing)
          (executableBindings.applySubst state.prevailing) state scheme).1.2 =
        (InferenceBase.instantiateDualScheme q scheme).value.2 := by
      simp [Inference.instantiateDualInState, before.supply_eq]
    rw [targetEq]
    exact instBounded.2.mono childrenExtends
  · change children.run.result.bindings.BoundedBy q₁
    exact children.rawBindingsBounded

end DemandTypingInferenceCompletenessPatternMain
end TypePM
