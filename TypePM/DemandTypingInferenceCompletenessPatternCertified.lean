import TypePM.DemandTypingInferenceCompletenessPatternDispatcher
import TypePM.DemandTypingInferenceCompletenessValidationMain
import TypePM.DemandTypingInferenceCompletenessSignatureBounds

/-!
# Validator-certified user-pattern completeness

This module adds validator chronology to the bounded raw pattern dispatcher.
The raw proof and its event-history proof remain separate fields: clients can
project the existing bounded completion unchanged, while the root completeness
recursion retains the exact intermediate states needed to compose validation.

The constructor-sensitive `pctor` chronology is deliberately not hidden in a
generic combinator.  Its freeze/compatibility cut is supplied by
`DemandTypingInferenceCompletenessValidationMain.patternCtor` once the
capability solver's certified completion is available.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPatternCertified

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternMain
open DemandTypingInferenceCompletenessPatternDispatcher
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessSignatureBounds

/-- A bounded raw pattern completion together with validator coverage for the
same concrete executable run. -/
structure BoundedCertifiedPatternRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  bounded : BoundedPatternRunCompletion before operation q' declarative ledger
    dual bindings
  validation : ValidatorRunExtension terminal signature initial
    bounded.run.result.state

/-- The list analogue threads one shared validation history through all
siblings. -/
structure BoundedCertifiedPatternsRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  bounded : BoundedPatternsRunCompletion before operation q' declarative
    ledger duals bindings
  validation : ValidatorRunExtension terminal signature initial
    bounded.run.result.state

/-- Certified single-pattern completeness available below a strict fuel
ceiling. -/
structure CertifiedPatternCompletenessBelow
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
      SignatureVarsBelow q signature →
      ContextBisimulation before.prevailing declarativeContext
        executableContext →
      PatternCtxBisimulation before.prevailing declarativeParameters
        executableParameters →
      MonoCtxBisimulation before.prevailing declarativeBindings
        executableBindings →
      declarativeContext.BoundedBy q → declarativeParameters.BoundedBy q →
      declarativeBindings.BoundedBy q → executableContext.BoundedBy q →
      executableParameters.BoundedBy q → executableBindings.BoundedBy q →
      DDPatternTerminalAudit terminal signature origin →
      PatternBudgetAdequate fuel pattern →
      Nonempty (BoundedCertifiedPatternRunCompletion terminal signature before
        (inferPatternFuel fuel signature executableContext executableParameters
          executableBindings selfEnv path pattern state)
        q' S' ledger' dual bindings')

/-- Certified list completeness available below a strict fuel ceiling. -/
structure CertifiedPatternsCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop where
  complete : ∀ {fuel : Nat}, fuel < bound →
    ∀ {declarativeContext executableContext : Context}
      {declarativeParameters executableParameters : PatternCtx}
      {declarativeBindings executableBindings : MonoCtx}
      {selfEnv : SelfEnv} {path : SyntaxPath} {index : Nat}
      {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
      {q q' : InferenceBase.FreshSupply} {S S' : Subst}
      {ledger ledger' : CapabilityOriginLedger} {state : InferState}
      {raw : DDPatterns signature q S declarativeContext declarativeParameters
        declarativeBindings patterns duals bindings' q' S'}
      {origin : DDPatternsOrigin signature raw ledger ledger'},
      (before : TraversalStateCorrespondence q S ledger state) →
      SignatureVarsBelow q signature →
      ContextBisimulation before.prevailing declarativeContext
        executableContext →
      PatternCtxBisimulation before.prevailing declarativeParameters
        executableParameters →
      MonoCtxBisimulation before.prevailing declarativeBindings
        executableBindings →
      declarativeContext.BoundedBy q → declarativeParameters.BoundedBy q →
      declarativeBindings.BoundedBy q → executableContext.BoundedBy q →
      executableParameters.BoundedBy q → executableBindings.BoundedBy q →
      DDPatternsTerminalAudit terminal signature origin →
      PatternsBudgetAdequate fuel patterns →
      Nonempty (BoundedCertifiedPatternsRunCompletion terminal signature before
        (inferPatternsFuel fuel signature executableContext
          executableParameters executableBindings selfEnv path index patterns
          state)
        q' S' ledger' duals bindings')

def CertifiedPatternCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : CertifiedPatternCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    CertifiedPatternCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

def CertifiedPatternsCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : CertifiedPatternsCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    CertifiedPatternsCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

theorem Context.BoundedBy.capVarsBelow
    {q : InferenceBase.FreshSupply} {context : Context}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).caps varId varMem

theorem Context.BoundedBy.tyVarsBelow
    {q : InferenceBase.FreshSupply} {context : Context}
    (bounded : context.BoundedBy q) :
    InferenceBase.TyVarsBelow q context.ftv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).targets varId varMem

theorem MonoCtx.BoundedBy.capVarsBelow
    {q : InferenceBase.FreshSupply} {context : MonoCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).caps varId varMem

theorem MonoCtx.BoundedBy.tyVarsBelow
    {q : InferenceBase.FreshSupply} {context : MonoCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.TyVarsBelow q context.ftv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).targets varId varMem

theorem PatternCtx.BoundedBy.capVarsBelow
    {q : InferenceBase.FreshSupply} {context : PatternCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  rcases List.mem_append.mp varMem with capMem | targetMem
  · exact (bounded entry entryMem).1 varId capMem
  · exact (bounded entry entryMem).2.caps varId targetMem

theorem PatternCtx.BoundedBy.tyVarsBelow
    {q : InferenceBase.FreshSupply} {context : PatternCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.TyVarsBelow q context.ftv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).2.targets varId varMem

/-! ## Constructor-independent chronology -/

/-- Every solve-free leaf (and the value-pattern suffix after its certified
expression child) closes with the common inferred-pattern event. -/
theorem leaf
    {terminal : Subst} {signature : FrozenSig} {initial coreState : InferState}
    {pattern : Pattern} {dual : Dual} {bindings : MonoCtx} {path : SyntaxPath}
    (core : ValidatorRunExtension terminal signature initial coreState) :
    ValidatorRunExtension terminal signature initial
      (coreState.recordEvent (.inferredPattern pattern dual bindings path)) :=
  DemandTypingInferenceCompletenessValidationMain.finishPattern core

/-- An empty pattern list emits no events. -/
theorem patternsNil
    (terminal : Subst) (signature : FrozenSig) (state : InferState) :
    ValidatorRunExtension terminal signature state state :=
  DemandTypingInferenceCompletenessValidationMain.listNil terminal signature
    state

/-- Pattern-list chronology is head followed by tail. -/
theorem patternsCons
    {terminal : Subst} {signature : FrozenSig}
    {initial middle final : InferState}
    (head : ValidatorRunExtension terminal signature initial middle)
    (tail : ValidatorRunExtension terminal signature middle final) :
    ValidatorRunExtension terminal signature initial final :=
  DemandTypingInferenceCompletenessValidationMain.listCons head tail

/-- Tuple patterns add one visit before their certified child-list traversal
and the common result event afterward. -/
theorem tuple
    {terminal : Subst} {signature : FrozenSig} {initial final : InferState}
    {path : SyntaxPath} {patterns : List Pattern} {dual : Dual}
    {bindings : MonoCtx}
    (children : ValidatorRunExtension terminal signature
      (visit initial .patternTuple path) final) :
    ValidatorRunExtension terminal signature initial
      (final.recordEvent
        (.inferredPattern (.ptuple patterns) dual bindings path)) :=
  leaf ((ValidatorRunExtension.visit terminal signature initial .patternTuple
    path).trans children)

/-- `and` and `or` share visit/left/right chronology; their distinct
alignment suffixes are supplied as one already-certified extension. -/
theorem binary
    {terminal : Subst} {signature : FrozenSig}
    {initial leftState rightState alignedState : InferState}
    {kind : NodeKind} {path : SyntaxPath} {pattern : Pattern} {dual : Dual}
    {bindings : MonoCtx}
    (left : ValidatorRunExtension terminal signature
      (visit initial kind path) leftState)
    (right : ValidatorRunExtension terminal signature leftState rightState)
    (alignment : ValidatorRunExtension terminal signature rightState
      alignedState) :
    ValidatorRunExtension terminal signature initial
      (alignedState.recordEvent
        (.inferredPattern pattern dual bindings path)) :=
  leaf ((ValidatorRunExtension.visit terminal signature initial kind path).trans
    (left.trans (right.trans alignment)))

theorem andPattern
    {terminal : Subst} {signature : FrozenSig}
    {initial leftState rightState alignedState : InferState}
    {path : SyntaxPath} {leftPattern rightPattern : Pattern} {dual : Dual}
    {bindings : MonoCtx}
    (left : ValidatorRunExtension terminal signature
      (visit initial .patternAnd path) leftState)
    (right : ValidatorRunExtension terminal signature leftState rightState)
    (alignment : ValidatorRunExtension terminal signature rightState
      alignedState) :
    ValidatorRunExtension terminal signature initial
      (alignedState.recordEvent (.inferredPattern
        (.pand leftPattern rightPattern) dual bindings path)) :=
  binary left right alignment

theorem orPattern
    {terminal : Subst} {signature : FrozenSig}
    {initial leftState rightState alignedState : InferState}
    {path : SyntaxPath} {leftPattern rightPattern : Pattern} {dual : Dual}
    {bindings : MonoCtx}
    (left : ValidatorRunExtension terminal signature
      (visit initial .patternOr path) leftState)
    (right : ValidatorRunExtension terminal signature leftState rightState)
    (alignment : ValidatorRunExtension terminal signature rightState
      alignedState) :
    ValidatorRunExtension terminal signature initial
      (alignedState.recordEvent (.inferredPattern
        (.por leftPattern rightPattern) dual bindings path)) :=
  binary left right alignment

/-- Pattern-function application chronology includes canonical dual-scheme
instantiation, its node visit, the child list, argument alignment, and finish. -/
theorem app
    {terminal : Subst} {signature : FrozenSig}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawBindings : MonoCtx} {context : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {initial childrenState alignedState : InferState}
    {scheme : DualScheme} {path : SyntaxPath} {name : String}
    {patterns : List Pattern} {dual : Dual} {resultBindings : MonoCtx}
    (closed : scheme.Closed)
    (children : ValidatorRunExtension terminal signature
      (visit (instantiateDualInState signature rawContext rawParameters
        rawBindings context parameters bindings initial scheme).2
        .patternApp path) childrenState)
    (alignment : ValidatorRunExtension terminal signature childrenState
      alignedState) :
    ValidatorRunExtension terminal signature initial
      (alignedState.recordEvent (.inferredPattern (.papp name patterns) dual
        resultBindings path)) :=
  leaf ((ValidatorRunExtension.instantiateDualInState
      (terminal := terminal) (signature := signature) closed).trans
    ((ValidatorRunExtension.visit terminal signature _ .patternApp path).trans
      (children.trans alignment)))

/-- Constructor-pattern chronology retains the sensitive compatibility event
at the precise post-freeze cut.  The capability solver may be supplied by a
separate certified package; this wrapper fixes the surrounding order. -/
theorem ctor
    {terminal : Subst} {signature : FrozenSig}
    {initial childrenState targetAligned capSolved : InferState}
    {path : SyntaxPath} {name : String} {patterns : List Pattern}
    {entry : PatternCtorScheme signature.observability}
    {duals : List Dual} {bindings : MonoCtx} {capability : Cap}
    {capImages : List CapVar} {payload : Ty} {dual : Dual}
    (lookup : signature.findPatternCtor name = some entry)
    (closed : entry.scheme.Closed)
    (children : ValidatorRunExtension terminal signature
      (visit (instantiateCtorInState initial entry.scheme).2 .patternCtor path)
      childrenState)
    (targetAlignment : ValidatorRunExtension terminal signature childrenState
      targetAligned)
    (capabilitySolve : ValidatorRunExtension terminal signature targetAligned
      capSolved)
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
    let frozen := capSolved.freezeCapabilityExport capImages payload
    let compatible := frozen.recordEvent (.patternCtorCompatibility
      frozen.trace.solves.length name (duals.map Dual.cap) capability)
    ValidatorRunExtension terminal signature initial
      (compatible.recordEvent
        (.inferredPattern (.pctor name patterns) dual bindings path)) :=
  DemandTypingInferenceCompletenessValidationMain.patternCtor lookup closed
    children targetAlignment capabilitySolve facts

end DemandTypingInferenceCompletenessPatternCertified
end TypePM
