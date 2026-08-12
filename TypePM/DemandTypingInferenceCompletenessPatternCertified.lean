import TypePM.DemandTypingInferenceCompletenessPatternDispatcher
import TypePM.DemandTypingInferenceCompletenessValidationMain
import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
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
open DemandTypingInferenceCompletenessAlignmentFamilies
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessPatternMain
open DemandTypingInferenceCompletenessPatternDispatcher
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun
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

/-- Completeness-only wrapper whose sensitive constructor facts may retain DD
operands paired with their executable representatives. -/
structure BoundedPairedCertifiedPatternRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (dual : Dual) (bindings : MonoCtx) : Type where
  bounded : BoundedPatternRunCompletion before operation q' declarative ledger
    dual bindings
  history : initial.StateExtension bounded.run.result.state
  validation : PairedValidatorRunExtension terminal signature
    bounded.run.transition history

/-- Paired list traversal used by recursive user patterns. -/
structure BoundedPairedCertifiedPatternsRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option PatternsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (duals : List Dual) (bindings : MonoCtx) : Type where
  bounded : BoundedPatternsRunCompletion before operation q' declarative
    ledger duals bindings
  history : initial.StateExtension bounded.run.result.state
  validation : PairedValidatorRunExtension terminal signature
    bounded.run.transition history

/-- Paired expression callback required by value patterns. -/
structure BoundedPairedCertifiedPatternSynthRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  run : SynthRunCompletion before operation q' declarative ledger target
  rawTargetBounded : run.result.target.BoundedBy q'
  history : initial.StateExtension run.result.state
  validation : PairedValidatorRunExtension terminal signature run.transition
    history

/-- Exact pattern validation is a special case of paired validation. -/
def BoundedPairedCertifiedPatternRunCompletion.ofExact
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {dual : Dual} {bindings : MonoCtx}
    (exact : BoundedCertifiedPatternRunCompletion terminal signature before
      operation q' declarative ledger dual bindings) :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
      operation q' declarative ledger dual bindings where
  bounded := exact.bounded
  history := exact.validation.ordinary.history
  validation := PairedValidatorRunExtension.ofExact
    exact.bounded.run.transition exact.validation

def BoundedPairedCertifiedPatternsRunCompletion.ofExact
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option PatternsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {duals : List Dual} {bindings : MonoCtx}
    (exact : BoundedCertifiedPatternsRunCompletion terminal signature before
      operation q' declarative ledger duals bindings) :
    BoundedPairedCertifiedPatternsRunCompletion terminal signature before
      operation q' declarative ledger duals bindings where
  bounded := exact.bounded
  history := exact.validation.ordinary.history
  validation := PairedValidatorRunExtension.ofExact
    exact.bounded.run.transition exact.validation

/-- The value-pattern callback needs the raw synthesized target bound together
with the child's validator chronology. -/
structure BoundedCertifiedPatternSynthRunCompletion
    (terminal : Subst) (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  run : SynthRunCompletion before operation q' declarative ledger target
  rawTargetBounded : run.result.target.BoundedBy q'
  validation : ValidatorRunExtension terminal signature initial
    run.result.state

/-- Paired synthesis available below a strict fuel ceiling, used only by the
value-pattern branch of the user-pattern knot. -/
structure CertifiedPatternSynthCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop where
  complete : ∀ {fuel : Nat}, fuel < bound →
    ∀ {declarativeContext executableContext : Context}
      {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
      {target : Ty} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
      {ledger ledger' : CapabilityOriginLedger} {state : InferState}
      {raw : DDSynth signature q S declarativeContext expression target q' S'}
      {origin : DDSynthOrigin signature raw ledger ledger'},
      (before : TraversalStateCorrespondence q S ledger state) →
      SignatureVarsBelow q signature →
      ContextBisimulation before.prevailing declarativeContext
        executableContext →
      declarativeContext.BoundedBy q → executableContext.BoundedBy q →
      DDSynthTerminalAudit terminal signature origin →
      PatternSynthBudgetAdequate fuel expression →
      Nonempty (BoundedPairedCertifiedPatternSynthRunCompletion terminal
        signature before
        (inferExprFuel fuel signature executableContext selfEnv path expression
          state) q' S' ledger' target)

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
      Nonempty (BoundedPairedCertifiedPatternRunCompletion terminal signature before
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
      Nonempty (BoundedPairedCertifiedPatternsRunCompletion terminal signature before
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

def CertifiedPatternSynthCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : CertifiedPatternSynthCompletenessBelow terminal signature
      larger)
    (boundLe : smaller ≤ larger) :
    CertifiedPatternSynthCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

def CertifiedPatternsCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : CertifiedPatternsCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    CertifiedPatternsCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

theorem contextBounded_capVarsBelow
    {q : InferenceBase.FreshSupply} {context : Context}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).caps varId varMem

theorem contextBounded_tyVarsBelow
    {q : InferenceBase.FreshSupply} {context : Context}
    (bounded : context.BoundedBy q) :
    InferenceBase.TyVarsBelow q context.ftv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).targets varId varMem

theorem monoCtxBounded_capVarsBelow
    {q : InferenceBase.FreshSupply} {context : MonoCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).caps varId varMem

theorem monoCtxBounded_tyVarsBelow
    {q : InferenceBase.FreshSupply} {context : MonoCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.TyVarsBelow q context.ftv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  exact (bounded entry entryMem).targets varId varMem

theorem patternCtxBounded_capVarsBelow
    {q : InferenceBase.FreshSupply} {context : PatternCtx}
    (bounded : context.BoundedBy q) :
    InferenceBase.CapVarsBelow q context.fcv := by
  intro varId membership
  obtain ⟨entry, entryMem, varMem⟩ := List.mem_flatMap.mp membership
  rcases List.mem_append.mp varMem with capMem | targetMem
  · exact (bounded entry entryMem).1 varId capMem
  · exact (bounded entry entryMem).2.caps varId targetMem

theorem patternCtxBounded_tyVarsBelow
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

/-- Exact validator chronology of a variable-pattern leaf. -/
theorem variableLeaf
    {terminal : Subst} {signature : FrozenSig} {initial : InferState}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {path : SyntaxPath} {name : String}
    (signatureBelow : SignatureVarsBelow initial.supply signature)
    (contextBounded : context.BoundedBy initial.supply)
    (parametersBounded : parameters.BoundedBy initial.supply)
    (bindingsBounded : bindings.BoundedBy initial.supply) :
    let capVar : CapVar := ⟨initial.supply.nextCap⟩
    let capability := (initial.freshCap
      (freshOrigin .pattern path "pattern-variable-capability")).1
    let afterCap := (initial.freshCap
      (freshOrigin .pattern path "pattern-variable-capability")).2
    let target := (afterCap.freshTy
      (freshOrigin .pattern path "pattern-variable-target")).1
    let afterFresh := (afterCap.freshTy
      (freshOrigin .pattern path "pattern-variable-target")).2
    let resultBindings := bindings ++ [(name, target)]
    let dual := Dual.mk capability target
    let marked := afterFresh.recordEvent
      (.patternVarFresh context parameters bindings capVar
        initial.supply.nextTy)
    ValidatorRunExtension terminal signature initial
      ((visit marked .patternVar path).recordEvent
        (.inferredPattern (.pvar name) dual resultBindings path)) := by
  dsimp only
  let freshCapRun := ValidatorRunExtension.freshCap terminal signature initial
    (freshOrigin .pattern path "pattern-variable-capability")
  let afterCap := (initial.freshCap
    (freshOrigin .pattern path "pattern-variable-capability")).2
  let freshTyRun := ValidatorRunExtension.freshTy terminal signature afterCap
    (freshOrigin .pattern path "pattern-variable-target")
  let afterFresh := (afterCap.freshTy
    (freshOrigin .pattern path "pattern-variable-target")).2
  have markedRun : ValidatorRunExtension terminal signature afterFresh
      (afterFresh.recordEvent (.patternVarFresh context parameters bindings
        ⟨initial.supply.nextCap⟩ initial.supply.nextTy)) := by
    apply ValidatorRunExtension.recordOrdinaryEvent
    · intro future extension safe
      exact Inference.Reconstruction.patternVar_ordinaryValidatorEventCondition
        signatureBelow.caps
        (contextBounded_capVarsBelow contextBounded)
        (patternCtxBounded_capVarsBelow parametersBounded)
        (monoCtxBounded_capVarsBelow bindingsBounded) signatureBelow.targets
        (contextBounded_tyVarsBelow contextBounded)
        (patternCtxBounded_tyVarsBelow parametersBounded)
        (monoCtxBounded_tyVarsBelow bindingsBounded)
    · simp [Inference.Reconstruction.TerminalAuditSensitiveEvent]
  exact freshCapRun.trans (freshTyRun.trans (markedRun.trans
    ((ValidatorRunExtension.visit terminal signature _ .patternVar path).trans
      (ValidatorRunExtension.recordNeutral
        (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
          (.pvar name) _ _ path)))))

/-- Exact validator chronology of a wildcard-pattern leaf. -/
theorem wildcardLeaf
    {terminal : Subst} {signature : FrozenSig} {initial : InferState}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {path : SyntaxPath}
    (signatureBelow : SignatureVarsBelow initial.supply signature)
    (contextBounded : context.BoundedBy initial.supply)
    (parametersBounded : parameters.BoundedBy initial.supply)
    (bindingsBounded : bindings.BoundedBy initial.supply) :
    let capability := (initial.freshCap
      (freshOrigin .pattern path "pattern-wild-capability")).1
    let afterCap := (initial.freshCap
      (freshOrigin .pattern path "pattern-wild-capability")).2
    let target := (afterCap.freshTy
      (freshOrigin .pattern path "pattern-wild-target")).1
    let afterFresh := (afterCap.freshTy
      (freshOrigin .pattern path "pattern-wild-target")).2
    let dual := Dual.mk capability target
    let marked := afterFresh.recordEvent (.patternWildFresh context parameters
      bindings ⟨initial.supply.nextCap⟩ initial.supply.nextTy)
    ValidatorRunExtension terminal signature initial
      ((visit marked .patternWild path).recordEvent
        (.inferredPattern .wild dual bindings path)) := by
  dsimp only
  let freshCapRun := ValidatorRunExtension.freshCap terminal signature initial
    (freshOrigin .pattern path "pattern-wild-capability")
  let afterCap := (initial.freshCap
    (freshOrigin .pattern path "pattern-wild-capability")).2
  let freshTyRun := ValidatorRunExtension.freshTy terminal signature afterCap
    (freshOrigin .pattern path "pattern-wild-target")
  let afterFresh := (afterCap.freshTy
    (freshOrigin .pattern path "pattern-wild-target")).2
  have markedRun : ValidatorRunExtension terminal signature afterFresh
      (afterFresh.recordEvent (.patternWildFresh context parameters bindings
        ⟨initial.supply.nextCap⟩ initial.supply.nextTy)) := by
    apply ValidatorRunExtension.recordOrdinaryEvent
    · intro future extension safe
      exact Inference.Reconstruction.patternWild_ordinaryValidatorEventCondition
        signatureBelow.caps
        (contextBounded_capVarsBelow contextBounded)
        (patternCtxBounded_capVarsBelow parametersBounded)
        (monoCtxBounded_capVarsBelow bindingsBounded) signatureBelow.targets
        (contextBounded_tyVarsBelow contextBounded)
        (patternCtxBounded_tyVarsBelow parametersBounded)
        (monoCtxBounded_tyVarsBelow bindingsBounded)
    · simp [Inference.Reconstruction.TerminalAuditSensitiveEvent]
  exact freshCapRun.trans (freshTyRun.trans (markedRun.trans
    ((ValidatorRunExtension.visit terminal signature _ .patternWild path).trans
      (ValidatorRunExtension.recordNeutral
        (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
          .wild _ _ path)))))

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

/-! ## Certified raw-pattern packaging -/

/-- Package the raw variable-pattern completion with its exact chronology. -/
def certifiedPatternPVarOrigin_complete
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableContextBounded : executableContext.BoundedBy q)
    (executableParametersBounded : executableParameters.BoundedBy q)
    (executableBindingsBounded : executableBindings.BoundedBy q)
    (freshName : name ∉ declarativeBindings.names) :
    BoundedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path (.pvar name) state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩
      (declarativeBindings ++ [(name, .var q.nextTy)]) := by
  let bounded := boundedPatternPVarOrigin_complete
    (signature := signature) (declarativeContext := declarativeContext)
    (executableContext := executableContext)
    (declarativeParameters := declarativeParameters)
    (executableParameters := executableParameters) (selfEnv := selfEnv)
    (path := path) fuel before bindings executableBindingsBounded freshName
  refine ⟨bounded, ?_⟩
  have executableAbsent : name ∉ executableBindings.names := by
    rw [← bindings.names_eq]
    exact freshName
  let afterCap := (state.freshCap
    (freshOrigin .pattern path "pattern-variable-capability")).2
  let afterFresh := (afterCap.freshTy
    (freshOrigin .pattern path "pattern-variable-target")).2
  let resultDual := Dual.mk
    (state.freshCap
      (freshOrigin .pattern path "pattern-variable-capability")).1
    (afterCap.freshTy
      (freshOrigin .pattern path "pattern-variable-target")).1
  let resultBindings := executableBindings ++ [(name, resultDual.target)]
  let final := (visit (afterFresh.recordEvent (.patternVarFresh
    executableContext executableParameters executableBindings
    ⟨state.supply.nextCap⟩ state.supply.nextTy)) .patternVar path).recordEvent
      (.inferredPattern (.pvar name) resultDual resultBindings path)
  have stateEq : final = bounded.run.result.state := by
    have mapped := congrArg (Option.map PatternResult.state)
      bounded.run.success
    simpa [inferPatternFuel, executableAbsent, final, resultDual,
      resultBindings, afterFresh, afterCap, InferState.freshCap,
      InferState.freshTy, InferenceBase.freshCapMeta,
      InferenceBase.freshTyMeta] using mapped
  rw [← stateEq]
  exact
    (variableLeaf (terminal := terminal) (signature := signature)
      (initial := state) (context := executableContext)
      (parameters := executableParameters) (bindings := executableBindings)
      (path := path) (name := name) (by simpa [before.supply_eq] using
        signatureBelow) (by simpa [before.supply_eq] using
        executableContextBounded) (by simpa [before.supply_eq] using
        executableParametersBounded) (by simpa [before.supply_eq] using
        executableBindingsBounded))

/-- Package the raw wildcard-pattern completion with its exact chronology. -/
def certifiedPatternWildOrigin_complete
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableContextBounded : executableContext.BoundedBy q)
    (executableParametersBounded : executableParameters.BoundedBy q)
    (executableBindingsBounded : executableBindings.BoundedBy q) :
    BoundedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path .wild state)
      { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
      (DDLedger.markFreshCap ledger q)
      ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ declarativeBindings := by
  let bounded := boundedPatternWildOrigin_complete
    (signature := signature) (declarativeContext := declarativeContext)
    (executableContext := executableContext)
    (declarativeParameters := declarativeParameters)
    (executableParameters := executableParameters) (selfEnv := selfEnv)
    (path := path) fuel before bindings executableBindingsBounded
  refine ⟨bounded, ?_⟩
  let afterCap := (state.freshCap
    (freshOrigin .pattern path "pattern-wild-capability")).2
  let afterFresh := (afterCap.freshTy
    (freshOrigin .pattern path "pattern-wild-target")).2
  let resultDual := Dual.mk
    (state.freshCap
      (freshOrigin .pattern path "pattern-wild-capability")).1
    (afterCap.freshTy
      (freshOrigin .pattern path "pattern-wild-target")).1
  let final := (visit (afterFresh.recordEvent (.patternWildFresh
    executableContext executableParameters executableBindings
    ⟨state.supply.nextCap⟩ state.supply.nextTy)) .patternWild path).recordEvent
      (.inferredPattern .wild resultDual executableBindings path)
  have stateEq : final = bounded.run.result.state := by
    have mapped := congrArg (Option.map PatternResult.state)
      bounded.run.success
    simp only [inferPatternFuel] at mapped
    exact Option.some.inj mapped
  rw [← stateEq]
  exact
    (wildcardLeaf (terminal := terminal) (signature := signature)
      (initial := state) (context := executableContext)
      (parameters := executableParameters) (bindings := executableBindings)
      (path := path) (by simpa [before.supply_eq] using signatureBelow)
      (by simpa [before.supply_eq] using executableContextBounded)
      (by simpa [before.supply_eq] using executableParametersBounded)
      (by simpa [before.supply_eq] using executableBindingsBounded))

/-- Embedded parameters emit only their visit and common result event. -/
noncomputable def certifiedPatternEmbedOrigin_complete
    {terminal : Subst} {signature : FrozenSig} {context : Context}
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
    BoundedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature context executableParameters
        executableBindings selfEnv path (.embed name) state)
      q S ledger dual declarativeBindings := by
  let bounded := boundedPatternEmbedOrigin_complete
    (signature := signature) (context := context) (selfEnv := selfEnv)
    (path := path) fuel before parameters executableParametersBounded bindings
    executableBindingsBounded lookup
  refine ⟨bounded, ?_⟩
  exact leaf (ValidatorRunExtension.visit terminal signature state
    .patternEmbed path)

/-- A certified child-list gives a certified tuple-pattern completion without
reopening the raw tuple construction. -/
def certifiedPatternTuple_complete
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {context : Context} {parameters : PatternCtx}
    {executableBindings : MonoCtx} {selfEnv : SelfEnv} {path : SyntaxPath}
    {patterns : List Pattern} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {state : InferState} {duals : List Dual} {bindings : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (children : BoundedPairedCertifiedPatternsRunCompletion terminal signature
      (before.visit .patternTuple path)
      (inferPatternsFuel fuel signature context parameters executableBindings
        selfEnv path 0 patterns (visit state .patternTuple path))
      q' S' ledger' duals bindings) :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.ptuple patterns) state)
      q' S' ledger'
      ⟨.prod (duals.map Dual.cap), .prod (duals.map Dual.target)⟩ bindings :=
by
  let bounded := boundedPatternTuple_complete before children.bounded
  let visitExtension := before.visitExtension .patternTuple path
  let inferredEvent := TraceEvent.inferredPattern (.ptuple patterns)
    bounded.run.result.dual bounded.run.result.bindings path
  let inferredExtension := children.bounded.run.transition.after
    |>.recordEventExtension inferredEvent
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature state .patternTuple path)
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature) inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.ptuple patterns) bounded.run.result.dual
        bounded.run.result.bindings path))
  let validation := visitValidation.trans
    (children.validation.trans inferredValidation)
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-- A certified expression child, followed by one fresh capability and the
common pattern result event, gives the complete value-pattern package. -/
def certifiedPatternValue_complete
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q₁ : InferenceBase.FreshSupply} {S S₁ : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
    (bindings : MonoCtxBisimulation before.prevailing declarativeBindings
      executableBindings)
    (executableContextBounded : executableContext.BoundedBy q)
    (executableParametersBounded : executableParameters.BoundedBy q)
    (executableBindingsBounded : executableBindings.BoundedBy q)
    (synthExtends : SupplyExtends q q₁)
    (expressionRun : BoundedPairedCertifiedPatternSynthRunCompletion terminal
      signature (before.visit .patternValue path)
      (inferExprFuel fuel signature
        (executableBindings.toContext ++ executableContext) selfEnv
        (0 :: path) expression (visit state .patternValue path))
      q₁ S₁ ledger₁ target) :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path
        (.pval expression) state)
      { q₁ with nextCap := q₁.nextCap + 1 } S₁
      (DDLedger.markFreshCap ledger₁ q₁)
      ⟨.var ⟨q₁.nextCap⟩, target⟩ declarativeBindings := by
  let run := patternValue_complete fuel signature declarativeContext
    executableContext declarativeParameters executableParameters selfEnv path
    expression before declarativeBindings executableBindings bindings
    expressionRun.run
  have rawDualBounded : run.result.dual.BoundedBy
      { q₁ with nextCap := q₁.nextCap + 1 } := by
    have dualEq :
        ⟨.var ⟨expressionRun.run.result.state.supply.nextCap⟩,
          expressionRun.run.result.target⟩ = run.result.dual := by
      have mapped := congrArg (Option.map PatternResult.dual) run.success
      simp only [inferPatternFuel] at mapped
      rw [expressionRun.run.success] at mapped
      simpa [InferState.freshCap, InferenceBase.freshCapMeta] using mapped
    rw [← dualEq]
    constructor
    · apply Cap.BoundedBy.varOf
      change expressionRun.run.result.state.supply.nextCap < q₁.nextCap + 1
      rw [expressionRun.run.supply_eq]
      omega
    · exact expressionRun.rawTargetBounded.mono
        (SupplyExtends.bumpCap q₁ 1)
  have rawBindingsBounded : run.result.bindings.BoundedBy
      { q₁ with nextCap := q₁.nextCap + 1 } := by
    have bindingsEq : executableBindings = run.result.bindings := by
      have mapped := congrArg (Option.map PatternResult.bindings) run.success
      simp only [inferPatternFuel] at mapped
      rw [expressionRun.run.success] at mapped
      simpa using mapped
    rw [← bindingsEq]
    exact executableBindingsBounded.mono
      (synthExtends.trans (SupplyExtends.bumpCap q₁ 1))
  let bounded : BoundedPatternRunCompletion before
      (inferPatternFuel (fuel + 1) signature executableContext
        executableParameters executableBindings selfEnv path
        (.pval expression) state)
      { q₁ with nextCap := q₁.nextCap + 1 } S₁
      (DDLedger.markFreshCap ledger₁ q₁)
      ⟨.var ⟨q₁.nextCap⟩, target⟩ declarativeBindings :=
    ⟨run, rawDualBounded, rawBindingsBounded⟩
  let visitExtension := before.visitExtension .patternValue path
  let allocation := expressionRun.run.result.state
  let afterFresh := (allocation.freshCap
    (freshOrigin .pattern path "pattern-value-capability")).2
  have markedRun : ValidatorRunExtension terminal signature afterFresh
      (afterFresh.recordEvent (.patternValueFresh executableContext
        executableParameters executableBindings
        ⟨allocation.supply.nextCap⟩ expressionRun.run.result.target)) := by
    apply ValidatorRunExtension.recordOrdinaryEvent
    · intro future extension safe
      apply Inference.Reconstruction.patternValue_ordinaryValidatorEventCondition
      · simpa [allocation, expressionRun.run.supply_eq] using
          (signatureBelow.mono synthExtends).caps
      · simpa [allocation, expressionRun.run.supply_eq] using
          contextBounded_capVarsBelow
            (executableContextBounded.mono synthExtends)
      · simpa [allocation, expressionRun.run.supply_eq] using
          patternCtxBounded_capVarsBelow
            (executableParametersBounded.mono synthExtends)
      · simpa [allocation, expressionRun.run.supply_eq] using
          monoCtxBounded_capVarsBelow
            (executableBindingsBounded.mono synthExtends)
      · simpa [allocation, expressionRun.run.supply_eq] using
          expressionRun.rawTargetBounded
    · simp [Inference.Reconstruction.TerminalAuditSensitiveEvent]
  let freshExtension :=
    DemandTypingInferenceCompletenessPatternCtorCapability.TraversalStateCorrespondence.freshCapExtension
      expressionRun.run.completion.state
      (freshOrigin .pattern path "pattern-value-capability")
  let freshEvent := TraceEvent.patternValueFresh executableContext
    executableParameters executableBindings
    ⟨allocation.supply.nextCap⟩ expressionRun.run.result.target
  let freshEventExtension := freshExtension.after.recordEventExtension
    freshEvent
  let inferredEvent := TraceEvent.inferredPattern (.pval expression)
    bounded.run.result.dual bounded.run.result.bindings path
  let inferredExtension := freshEventExtension.after.recordEventExtension
    inferredEvent
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature state .patternValue path)
  let freshValidation := PairedValidatorRunExtension.ofExact freshExtension
    (ValidatorRunExtension.freshCap terminal signature
      expressionRun.run.result.state
      (freshOrigin .pattern path "pattern-value-capability"))
  let markedValidation := PairedValidatorRunExtension.ofExact
    freshEventExtension markedRun
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature) inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.pval expression) bounded.run.result.dual bounded.run.result.bindings
        path))
  let validation := visitValidation.trans
    (expressionRun.validation.trans (freshValidation.trans
      (markedValidation.trans inferredValidation)))
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-- Certified conjunction packaging reconstructs the same dual-alignment cut
as the raw bounded completion and certifies that executable suffix. -/
noncomputable def certifiedPatternAnd_complete
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {context : Context} {parameters : PatternCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {left right : Pattern}
    {executableBindings : MonoCtx}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger} {state : InferState}
    {leftDual rightDual : Dual} {leftBindings bindings' : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (leftRun : BoundedPairedCertifiedPatternRunCompletion terminal signature
      (before.visit .patternAnd path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternAnd path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : BoundedPairedCertifiedPatternRunCompletion terminal signature
      leftRun.bounded.run.completion
      (inferPatternFuel fuel signature context parameters
        leftRun.bounded.run.result.bindings selfEnv (1 :: path) right
        leftRun.bounded.run.result.state)
      q₂ S₂ ledger₂ rightDual bindings')
    (rightExtends : SupplyExtends q₁ q₂)
    (declarativeLeftBounded : leftDual.BoundedBy q₂)
    (declarativeRightBounded : rightDual.BoundedBy q₂)
    (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S') :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.pand left right) state)
      q₂ S' ledger₂ leftDual bindings' := by
  let leftAtRight :=
    _root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
      rightRun.bounded.run.transition leftRun.bounded.run.dual
  let alignment := ddAlignDualWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-and")
    rightRun.bounded.run.completion leftAtRight rightRun.bounded.run.dual
    declarativeLeftBounded declarativeRightBounded
    (leftRun.bounded.rawDualBounded.mono rightExtends)
    rightRun.bounded.rawDualBounded aligned
  let bounded := boundedPatternAnd_complete before leftRun.bounded
    rightRun.bounded rightExtends declarativeLeftBounded
    declarativeRightBounded aligned
  let visitExtension := before.visitExtension .patternAnd path
  let inferredEvent := TraceEvent.inferredPattern (.pand left right)
    bounded.run.result.dual bounded.run.result.bindings path
  let inferredExtension := alignment.transition.after.recordEventExtension
    inferredEvent
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature state .patternAnd path)
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    alignment.transition
    (ValidatorRunExtension.ofAlignDuals
      (terminal := terminal) (signature := signature) alignment.success)
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature) inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.pand left right) bounded.run.result.dual bounded.run.result.bindings
        path))
  let validation := visitValidation.trans
    (leftRun.validation.trans (rightRun.validation.trans
      (alignmentValidation.trans inferredValidation)))
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-- Certified disjunction additionally certifies the positional binding
alignment after the shared dual-alignment cut. -/
noncomputable def certifiedPatternOr_complete
    {terminal : Subst} {signature : FrozenSig} {fuel : Nat}
    {context : Context} {parameters : PatternCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {left right : Pattern}
    {executableBindings : MonoCtx}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S₃ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger} {state : InferState}
    {leftDual rightDual : Dual} {leftBindings rightBindings : MonoCtx}
    (before : TraversalStateCorrespondence q S ledger state)
    (leftRun : BoundedPairedCertifiedPatternRunCompletion terminal signature
      (before.visit .patternOr path)
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (0 :: path) left (visit state .patternOr path))
      q₁ S₁ ledger₁ leftDual leftBindings)
    (rightRun : BoundedPairedCertifiedPatternRunCompletion terminal signature
      leftRun.bounded.run.completion
      (inferPatternFuel fuel signature context parameters executableBindings
        selfEnv (1 :: path) right leftRun.bounded.run.result.state)
      q₂ S₂ ledger₂ rightDual rightBindings)
    (rightExtends : SupplyExtends q₁ q₂)
    (declarativeLeftDualBounded : leftDual.BoundedBy q₂)
    (declarativeRightDualBounded : rightDual.BoundedBy q₂)
    (declarativeLeftBindingsBounded : leftBindings.BoundedBy q₂)
    (declarativeRightBindingsBounded : rightBindings.BoundedBy q₂)
    (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S₃)
    (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃
      leftBindings rightBindings S') :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
      (inferPatternFuel (fuel + 1) signature context parameters
        executableBindings selfEnv path (.por left right) state)
      q₂ S' ledger₂ leftDual leftBindings := by
  let leftDualAtRight :=
    _root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
      rightRun.bounded.run.transition leftRun.bounded.run.dual
  let leftBindingsAtRight :=
    _root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      rightRun.bounded.run.transition leftRun.bounded.run.bindings
  let dualAlignment := ddAlignDualWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-or")
    rightRun.bounded.run.completion leftDualAtRight rightRun.bounded.run.dual
    declarativeLeftDualBounded declarativeRightDualBounded
    (leftRun.bounded.rawDualBounded.mono rightExtends)
    rightRun.bounded.rawDualBounded dualsAligned
  let bindingAlignment := ddAlignBindingsWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-or-bindings")
    dualAlignment.completion
    (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      dualAlignment.transition leftBindingsAtRight)
    (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      dualAlignment.transition rightRun.bounded.run.bindings)
    declarativeLeftBindingsBounded declarativeRightBindingsBounded
    (leftRun.bounded.rawBindingsBounded.mono rightExtends)
    rightRun.bounded.rawBindingsBounded bindingsAligned
  let bounded := boundedPatternOr_complete before leftRun.bounded
    rightRun.bounded rightExtends declarativeLeftDualBounded
    declarativeRightDualBounded declarativeLeftBindingsBounded
    declarativeRightBindingsBounded dualsAligned bindingsAligned
  let visitExtension := before.visitExtension .patternOr path
  let alignmentTransition := dualAlignment.transition.seq
    bindingAlignment.transition
  let inferredEvent := TraceEvent.inferredPattern (.por left right)
    bounded.run.result.dual bounded.run.result.bindings path
  let inferredExtension := bindingAlignment.transition.after
    |>.recordEventExtension inferredEvent
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature state .patternOr path)
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    alignmentTransition
    ((ValidatorRunExtension.ofAlignDuals
      (terminal := terminal) (signature := signature)
      dualAlignment.success).trans
      (ValidatorRunExtension.ofAlignBindings
        (terminal := terminal) (signature := signature)
        bindingAlignment.success))
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature) inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.por left right) bounded.run.result.dual bounded.run.result.bindings
        path))
  let validation := visitValidation.trans
    (leftRun.validation.trans (rightRun.validation.trans
      (alignmentValidation.trans inferredValidation)))
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-- Certified pattern-function application shares the raw instantiation and
dual-list alignment witnesses with its validator chronology. -/
noncomputable def certifiedPatternApp_complete
    {terminal : Subst} {fuel : Nat} {signature : FrozenSig}
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
      BoundedPairedCertifiedPatternsRunCompletion terminal signature
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
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
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
  let alignment := ddAlignDualListWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-function-arguments")
    children.bounded.run.completion children.bounded.run.duals
    (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
      ((instantiateDualInState_complete before signature executableContext
        executableParameters executableBindings
        (executableContext.applySubst state.prevailing)
        (executableParameters.applySubst state.prevailing)
        (executableBindings.applySubst state.prevailing) scheme).correspondence
          |>.visitExtension .patternApp path |>.seq
            children.bounded.run.transition)
      (instantiateDualInState_complete before signature executableContext
        executableParameters executableBindings
        (executableContext.applySubst state.prevailing)
        (executableParameters.applySubst state.prevailing)
        (executableBindings.applySubst state.prevailing) scheme).arguments)
    declarativeDualsBounded declarativeExpectedBounded
    children.bounded.rawDualsBounded executableExpectedBounded aligned
  let bounded := boundedPatternApp_complete
    (declarativeContext := declarativeContext)
    (executableContext := executableContext)
    (declarativeParameters := declarativeParameters)
    (executableParameters := executableParameters)
    (declarativeBindings := declarativeBindings)
    (executableBindings := executableBindings) lookup closed before
    children.bounded childrenExtends declarativeDualsBounded aligned
  let instantiation := instantiateDualInState_complete before signature
    executableContext executableParameters executableBindings
    (executableContext.applySubst state.prevailing)
    (executableParameters.applySubst state.prevailing)
    (executableBindings.applySubst state.prevailing) scheme
  let visitExtension := instantiation.correspondence.visitExtension
    .patternApp path
  let inferredEvent := TraceEvent.inferredPattern (.papp name patterns)
    bounded.run.result.dual bounded.run.result.bindings path
  let inferredExtension := alignment.transition.after.recordEventExtension
    inferredEvent
  let instantiationValidation := PairedValidatorRunExtension.ofExact
    instantiation.transition
    (ValidatorRunExtension.instantiateDualInState
      (terminal := terminal) (signature := signature)
      (closed.patternFuns lookup))
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature _ .patternApp path)
  let alignmentValidation := PairedValidatorRunExtension.ofExact
    alignment.transition
    (ValidatorRunExtension.ofAlignDualLists
      (terminal := terminal) (signature := signature) alignment.success)
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature) inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.papp name patterns) bounded.run.result.dual
        bounded.run.result.bindings path))
  let validation := instantiationValidation.trans
    (visitValidation.trans (children.validation.trans
      (alignmentValidation.trans inferredValidation)))
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-- Certified user pattern-constructor application.  Its raw completeness
package and validator proof share the reconstructed target alignment and
capability-solver run, so the sensitive compatibility event is certified at
the exact post-freeze cut. -/
noncomputable def certifiedPatternCtor_complete
    {terminal : Subst} {fuel : Nat} {signature : FrozenSig}
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
      BoundedPairedCertifiedPatternsRunCompletion terminal signature
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
        children.bounded.run.completion children.bounded.run.duals
        (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
          ((instantiateCtorInState_complete before entry.scheme).correspondence.visitExtension
            .patternCtor path |>.seq children.bounded.run.transition)
          (instantiateCtorInState_complete before entry.scheme).arguments)
        declarativeDualsBounded declarativeTargetsBounded
        children.bounded.rawDualsBounded executableTargetsBounded
        targetsAligned
      BoundedPatternCtorCapRunCompletion targetAlignment.completion
        (solvePatternCtorCapability signature entry
          (freshOrigin .pattern path "pattern-constructor-capability")
          (children.bounded.run.result.duals.map Dual.cap)
          targetAlignment.result)
        q₂ S₃ ledger₂ capability)
    (childrenToCapExtends : SupplyExtends q₁ q₂)
    (compatible : capCompatibleCheck entry
      ((children.bounded.run.result.duals.map Dual.cap).map fun child =>
        child.apply capRun.run.result.2.prevailing.cap)
      (capRun.run.result.1.apply capRun.run.result.2.prevailing.cap) = true)
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
    BoundedPairedCertifiedPatternRunCompletion terminal signature before
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
    exact (instBounded.1 _ membership).mono childrenExtends
  let targetAlignment := ddAlignTargetListWithLedger_complete
    (origin := freshOrigin .pattern path "pattern-constructor-fields")
    children.bounded.run.completion children.bounded.run.duals
    (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
      ((instantiateCtorInState_complete before entry.scheme).correspondence.visitExtension
        .patternCtor path |>.seq children.bounded.run.transition)
      (instantiateCtorInState_complete before entry.scheme).arguments)
    declarativeDualsBounded declarativeTargetsBounded
    children.bounded.rawDualsBounded executableTargetsBounded targetsAligned
  let bounded := boundedPatternCtor_complete lookup closed before
    children.bounded childrenExtends declarativeDualsBounded targetsAligned
    capRun childrenToCapExtends compatible
  let instantiation := instantiateCtorInState_complete before entry.scheme
  let visitExtension := instantiation.correspondence.visitExtension
    .patternCtor path
  let capExtension := capRun.run.extension
  let targetAtCap :=
    capExtension.transportTy
      (targetAlignment.transition.transportTy
        ((visitExtension.seq children.bounded.run.transition).transportTy
          instantiation.target))
  let bindingsAtCap :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
      (targetAlignment.transition.seq capExtension)
      children.bounded.run.bindings
  have capabilityAtCap : CapBisimulation capRun.run.correspondence.prevailing
      capability capRun.run.result.1 := by
    rw [capRun.run.prevailing_eq]
    exact capRun.run.capability
  let declarativePayload := capabilityExportPayload [capability]
    ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
      bindings'.map fun binding => binding.2)
  let executablePayload := capabilityExportPayload [capRun.run.result.1]
    ((instantiateCtorInState state entry.scheme).1.2 ::
      children.bounded.run.result.bindings.map fun binding => binding.2)
  have payloadRelated :
      DemandTypingInferenceCompletenessStateMutual.TyBisimulation
        capRun.run.correspondence.prevailing
      declarativePayload executablePayload := by
    unfold declarativePayload executablePayload capabilityExportPayload
    apply tyListBisimulation_prod
    exact DemandTypingInferenceCompletenessPatternTraversal.TyListBisimulation.append
      (.cons capabilityAtCap .nil)
      (.cons targetAtCap
        (DemandTypingInferenceCompletenessPatternTraversal.MonoCtxBisimulation.targets
          bindingsAtCap))
  let capImages := freshCapImages q entry.scheme.capBinders
  let freezeExtension :=
    DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.freezeCapabilityExportRelatedExtension
      capRun.run.correspondence capImages payloadRelated
  let frozen := capRun.run.result.2.freezeCapabilityExport capImages
    executablePayload
  let executableDualsAtFrozen :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
      (targetAlignment.transition.seq (capExtension.seq freezeExtension))
      children.bounded.run.duals
  let executableCapabilityAtFrozen :=
    DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
      freezeExtension capabilityAtCap
  let compatibilityEvent := TraceEvent.patternCtorCompatibility
    frozen.trace.solves.length name
    (children.bounded.run.result.duals.map Dual.cap) capRun.run.result.1
  let compatibilityExtension :=
    freezeExtension.after.recordEventExtension compatibilityEvent
  let inferredEvent := TraceEvent.inferredPattern (.pctor name patterns)
    ⟨capRun.run.result.1, (instantiateCtorInState state entry.scheme).1.2⟩
    children.bounded.run.result.bindings path
  let inferredExtension :=
    compatibilityExtension.after.recordEventExtension inferredEvent
  let instantiationValidation := PairedValidatorRunExtension.ofExact
    instantiation.transition
    (ValidatorRunExtension.instantiateCtorInState
      (terminal := terminal) (signature := signature) state entry.scheme
      (closed.patternCtors lookup))
  let visitValidation := PairedValidatorRunExtension.ofExact visitExtension
    (ValidatorRunExtension.visit terminal signature _ .patternCtor path)
  let childrenValidation := children.validation
  let targetValidation := PairedValidatorRunExtension.ofExact
    targetAlignment.transition
    (ValidatorRunExtension.ofAlignPatternTargets
      (terminal := terminal) (signature := signature) targetAlignment.success)
  let capValidation := PairedValidatorRunExtension.ofExact capExtension
    (ValidatorRunExtension.ofSolvePatternCtorCapability
      (terminal := terminal) (signature := signature) capRun.run.success)
  let freezeValidation := PairedValidatorRunExtension.ofExact freezeExtension
    (ValidatorRunExtension.freezeCapabilityExport terminal signature _
      capImages executablePayload)
  let compatibilityValidation :=
    PairedValidatorRunExtension.recordPatternCtor freezeExtension.after lookup
      executableDualsAtFrozen executableCapabilityAtFrozen facts
  let inferredValidation := PairedValidatorRunExtension.ofExact
    (terminal := terminal) (signature := signature)
    inferredExtension
    (ValidatorRunExtension.recordNeutral
      (terminal := terminal) (signature := signature)
      (Inference.Reconstruction.ValidatorNeutralEvent.inferredPattern
        (.pctor name patterns)
        ⟨capRun.run.result.1, (instantiateCtorInState state entry.scheme).1.2⟩
        children.bounded.run.result.bindings path))
  let validation := instantiationValidation.trans
    (visitValidation.trans (childrenValidation.trans
      (targetValidation.trans (capValidation.trans
        (freezeValidation.trans
          (compatibilityValidation.trans inferredValidation))))))
  exact
    { bounded := bounded
      history := validation.ordinary.history
      validation := validation }

/-! ## Paired single-pattern dispatch -/

/-- Constructor-complete certified dispatch for one user pattern.  Recursive
children retain paired constructor witnesses, while exact leaves embed into
the same chronology. -/
theorem certifiedPatternOrigin_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context}
    {declarativeParameters executableParameters : PatternCtx}
    {declarativeBindings executableBindings : MonoCtx}
    {selfEnv : SelfEnv} {path : SyntaxPath} {pattern : Pattern}
    {dual : Dual} {bindings' : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : CertifiedPatternSynthCompletenessBelow terminal signature
      fuel)
    (patternsBelow : CertifiedPatternsCompletenessBelow terminal signature
      fuel)
    (capComplete : PatternCtorCapCompletenessPackage signature)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
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
    {raw : DDPattern signature q S declarativeContext declarativeParameters
      declarativeBindings pattern dual bindings' q' S'}
    {origin : DDPatternOrigin signature raw ledger ledger'}
    (audit : DDPatternTerminalAudit terminal signature origin)
    (adequate : PatternBudgetAdequate fuel pattern) :
    Nonempty (BoundedPairedCertifiedPatternRunCompletion terminal signature
      before
      (inferPatternFuel fuel signature executableContext executableParameters
        executableBindings selfEnv path pattern state)
      q' S' ledger' dual bindings') := by
  cases audit with
  | pvar =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨BoundedPairedCertifiedPatternRunCompletion.ofExact
            (certifiedPatternPVarOrigin_complete
              (declarativeContext := declarativeContext)
              (declarativeParameters := declarativeParameters)
              inner before signatureBelow bindings executableContextBounded
              executableParametersBounded executableBindingsBounded
              (by assumption))⟩
  | wild =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨BoundedPairedCertifiedPatternRunCompletion.ofExact
            (certifiedPatternWildOrigin_complete
              (declarativeContext := declarativeContext)
              (declarativeParameters := declarativeParameters)
              inner before signatureBelow bindings executableContextBounded
              executableParametersBounded executableBindingsBounded)⟩
  | embed =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨BoundedPairedCertifiedPatternRunCompletion.ofExact
            (certifiedPatternEmbedOrigin_complete inner before parameters
              executableParametersBounded bindings executableBindingsBounded
              (by assumption))⟩
  | pval expressionAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          rename_i expression target q₁ S₁ ledger₁ expressionRaw
            expressionOrigin
          let visitExtension := before.visitExtension .patternValue path
          let expressionRun := Classical.choice
            (synthBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := 0 :: path)
              (before.visit .patternValue path)
              (signatureBelow.mono (SupplyExtends.refl q))
              (ContextBisimulation.append
                (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                  visitExtension bindings |>.toContext)
                (contexts.transport visitExtension))
              (MonoCtx.BoundedBy.toContext bindingsBounded |>.append
                contextBounded)
              (MonoCtx.BoundedBy.toContext executableBindingsBounded |>.append
                executableContextBounded)
              expressionAudit (by
                change 8 * (exprTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + exprTraversalFuel _) + 1) ≤
                  inner + 1 at adequate
                omega))
          exact ⟨certifiedPatternValue_complete
            (declarativeContext := declarativeContext)
            (declarativeParameters := declarativeParameters)
            before signatureBelow
            bindings executableContextBounded executableParametersBounded
            executableBindingsBounded expressionOrigin.erase.supplyExtends
            expressionRun⟩
  | ptuple childrenAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let extension := before.visitExtension .patternTuple path
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (before.visit .patternTuple path) signatureBelow
              (contexts.transport extension)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                extension parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                extension bindings)
              contextBounded parametersBounded bindingsBounded
              executableContextBounded executableParametersBounded
              executableBindingsBounded childrenAudit (by
                change 8 * (patternListTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternListTraversalFuel _) + 1) ≤
                  inner + 1 at adequate
                omega))
          exact ⟨certifiedPatternTuple_complete before children⟩
  | pctor childrenAudit facts =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          rename_i name patterns entry duals q₁ S₁ S₂ capability ledger₁
            ledger₂ lookup targetsAligned childrenRaw compatible capRaw
            capOrigin childrenOrigin
          let instantiation := instantiateCtorInState_complete before
            entry.scheme
          let instExtends := SupplyExtends.instantiateCtorScheme q entry.scheme
          let visitExtension := instantiation.correspondence.visitExtension
            .patternCtor path
          let totalInstantiation := instantiation.transition.seq visitExtension
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (instantiation.correspondence.visit .patternCtor path)
              (signatureBelow.mono instExtends)
              (contexts.transport totalInstantiation)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                totalInstantiation parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                totalInstantiation bindings)
              (contextBounded.mono instExtends)
              (parametersBounded.mono instExtends)
              (bindingsBounded.mono instExtends)
              (executableContextBounded.mono instExtends)
              (executableParametersBounded.mono instExtends)
              (executableBindingsBounded.mono instExtends) childrenAudit (by
                change 8 * (patternListTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternListTraversalFuel _) + 1) ≤
                  inner + 1 at adequate
                omega))
          let childrenExtends := childrenOrigin.erase.supplyExtends
          obtain ⟨_, declarativeDualsBounded, _⟩ :=
            childrenOrigin.erase.boundedBy closed
              instantiation.correspondence.declarative_bounded
              (contextBounded.mono instExtends)
              (parametersBounded.mono instExtends)
              (bindingsBounded.mono instExtends)
          let instBounded := instantiateCtorScheme_boundedBy (q := q)
            ((closed.patternCtors lookup).boundedBy)
          let declarativeTargetsBounded : ∀ target ∈
              (InferenceBase.instantiateCtorScheme q entry.scheme).value.1,
              target.BoundedBy q₁ := fun target membership =>
            (instBounded.1 target membership).mono childrenExtends
          let executableTargetsBounded : ∀ target ∈
              (instantiateCtorInState state entry.scheme).1.1,
              target.BoundedBy q₁ := fun target membership => by
            have argumentEq :
                (instantiateCtorInState state entry.scheme).1.1 =
                (InferenceBase.instantiateCtorScheme q
                  entry.scheme).value.1 := by
              simp [Inference.instantiateCtorInState, before.supply_eq]
            rw [argumentEq] at membership
            exact (instBounded.1 target membership).mono childrenExtends
          let targetAlignment := ddAlignTargetListWithLedger_complete
            (origin := freshOrigin .pattern path
              "pattern-constructor-fields") children.bounded.run.completion
            children.bounded.run.duals
            (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
              (visitExtension.seq children.bounded.run.transition)
              instantiation.arguments)
            declarativeDualsBounded declarativeTargetsBounded
            children.bounded.rawDualsBounded executableTargetsBounded
            targetsAligned
          have declarativeCapsBounded : ∀ child ∈ duals.map Dual.cap,
              child.BoundedBy q₁ := by
            intro child membership
            obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
            exact (declarativeDualsBounded dual dualMem).1
          have executableCapsBounded : ∀ child ∈
              children.bounded.run.result.duals.map Dual.cap,
              child.BoundedBy q₁ := by
            intro child membership
            obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
            exact (children.bounded.rawDualsBounded dual dualMem).1
          let dualsAtCap :=
            _root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
              targetAlignment.transition children.bounded.run.duals
          let capPackage := Classical.choice
            (capComplete.complete
              (constraintOrigin := freshOrigin .pattern path
                "pattern-constructor-capability")
              (raw := capRaw) (rawOrigin := capOrigin)
              targetAlignment.completion
              (DemandTypingInferenceCompletenessPatternMain.DualListBisimulation.capabilities
                dualsAtCap)
              declarativeCapsBounded executableCapsBounded compatible)
          exact ⟨certifiedPatternCtor_complete lookup closed before children
            childrenExtends declarativeDualsBounded targetsAligned
            capPackage.val capOrigin.erase.supplyExtends capPackage.property
            facts⟩
  | pand leftAudit rightAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let visitExtension := before.visitExtension .patternAnd path
          let leftOrigin := patternAuditOrigin leftAudit
          let left := Classical.choice
            (certifiedPatternOrigin_complete_nonempty closed inner
              (selfEnv := selfEnv) (path := 0 :: path)
              (raw := leftOrigin.erase) (origin := leftOrigin)
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete) (before.visit .patternAnd path)
              signatureBelow (contexts.transport visitExtension)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                visitExtension parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                visitExtension bindings)
              contextBounded parametersBounded bindingsBounded
              executableContextBounded executableParametersBounded
              executableBindingsBounded leftAudit (by
                change 8 * (patternTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternTraversalFuel _ +
                  patternTraversalFuel _) + 1) ≤ inner + 1 at adequate
                omega))
          let leftExtends := leftOrigin.erase.supplyExtends
          obtain ⟨_, leftDualBounded, leftBindingsBounded⟩ :=
            leftOrigin.erase.boundedBy closed before.declarative_bounded
              contextBounded parametersBounded bindingsBounded
          let rightOrigin := patternAuditOrigin rightAudit
          let right := Classical.choice
            (certifiedPatternOrigin_complete_nonempty closed inner
              (selfEnv := selfEnv) (path := 1 :: path)
              (raw := rightOrigin.erase) (origin := rightOrigin)
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete) left.bounded.run.completion
              (signatureBelow.mono leftExtends)
              (contexts.transport
                (visitExtension.seq left.bounded.run.transition))
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                (visitExtension.seq left.bounded.run.transition) parameters)
              left.bounded.run.bindings (contextBounded.mono leftExtends)
              (parametersBounded.mono leftExtends) leftBindingsBounded
              (executableContextBounded.mono leftExtends)
              (executableParametersBounded.mono leftExtends)
              left.bounded.rawBindingsBounded rightAudit (by
                change 8 * (patternTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternTraversalFuel _ +
                  patternTraversalFuel _) + 1) ≤ inner + 1 at adequate
                omega))
          let rightExtends := rightOrigin.erase.supplyExtends
          obtain ⟨_, rightDualBounded, _⟩ := rightOrigin.erase.boundedBy
            closed left.bounded.run.declarative_bounded
            (contextBounded.mono leftExtends)
            (parametersBounded.mono leftExtends) leftBindingsBounded
          exact ⟨certifiedPatternAnd_complete before left right rightExtends
            (leftDualBounded.mono rightExtends) rightDualBounded
            (by assumption)⟩
  | por leftAudit rightAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let visitExtension := before.visitExtension .patternOr path
          let leftOrigin := patternAuditOrigin leftAudit
          let left := Classical.choice
            (certifiedPatternOrigin_complete_nonempty closed inner
              (selfEnv := selfEnv) (path := 0 :: path)
              (raw := leftOrigin.erase) (origin := leftOrigin)
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete) (before.visit .patternOr path)
              signatureBelow (contexts.transport visitExtension)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                visitExtension parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                visitExtension bindings)
              contextBounded parametersBounded bindingsBounded
              executableContextBounded executableParametersBounded
              executableBindingsBounded leftAudit (by
                change 8 * (patternTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternTraversalFuel _ +
                  patternTraversalFuel _) + 1) ≤ inner + 1 at adequate
                omega))
          let leftExtends := leftOrigin.erase.supplyExtends
          obtain ⟨_, leftDualBounded, leftBindingsBounded⟩ :=
            leftOrigin.erase.boundedBy closed before.declarative_bounded
              contextBounded parametersBounded bindingsBounded
          let afterLeft := visitExtension.seq left.bounded.run.transition
          let rightOrigin := patternAuditOrigin rightAudit
          let right := Classical.choice
            (certifiedPatternOrigin_complete_nonempty closed inner
              (selfEnv := selfEnv) (path := 1 :: path)
              (raw := rightOrigin.erase) (origin := rightOrigin)
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete) left.bounded.run.completion
              (signatureBelow.mono leftExtends)
              (contexts.transport afterLeft)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                afterLeft parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                afterLeft bindings)
              (contextBounded.mono leftExtends)
              (parametersBounded.mono leftExtends)
              (bindingsBounded.mono leftExtends)
              (executableContextBounded.mono leftExtends)
              (executableParametersBounded.mono leftExtends)
              (executableBindingsBounded.mono leftExtends) rightAudit (by
                change 8 * (patternTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternTraversalFuel _ +
                  patternTraversalFuel _) + 1) ≤ inner + 1 at adequate
                omega))
          let rightExtends := rightOrigin.erase.supplyExtends
          obtain ⟨_, rightDualBounded, rightBindingsBounded⟩ :=
            rightOrigin.erase.boundedBy closed
              left.bounded.run.declarative_bounded
              (contextBounded.mono leftExtends)
              (parametersBounded.mono leftExtends)
              (bindingsBounded.mono leftExtends)
          exact ⟨certifiedPatternOr_complete before left right rightExtends
            (leftDualBounded.mono rightExtends) rightDualBounded
            (leftBindingsBounded.mono rightExtends) rightBindingsBounded
            (by assumption) (by assumption)⟩
  | papp childrenAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          rename_i scheme patterns duals S₁ name lookup childrenRaw aligned
            childrenOrigin
          let instantiation := instantiateDualInState_complete before signature
            executableContext executableParameters executableBindings
            (executableContext.applySubst state.prevailing)
            (executableParameters.applySubst state.prevailing)
            (executableBindings.applySubst state.prevailing) scheme
          let instExtends := SupplyExtends.instantiateDualScheme q scheme
          let visitExtension := instantiation.correspondence.visitExtension
            .patternApp path
          let totalInstantiation := instantiation.transition.seq visitExtension
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (instantiation.correspondence.visit .patternApp path)
              (signatureBelow.mono instExtends)
              (contexts.transport totalInstantiation)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                totalInstantiation parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                totalInstantiation bindings)
              (contextBounded.mono instExtends)
              (parametersBounded.mono instExtends)
              (bindingsBounded.mono instExtends)
              (executableContextBounded.mono instExtends)
              (executableParametersBounded.mono instExtends)
              (executableBindingsBounded.mono instExtends) childrenAudit (by
                change 8 * (patternListTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternListTraversalFuel _) + 1) ≤
                  inner + 1 at adequate
                omega))
          let childrenExtends := childrenOrigin.erase.supplyExtends
          obtain ⟨_, declarativeDualsBounded, _⟩ :=
            childrenOrigin.erase.boundedBy closed
              instantiation.correspondence.declarative_bounded
              (contextBounded.mono instExtends)
              (parametersBounded.mono instExtends)
              (bindingsBounded.mono instExtends)
          exact ⟨certifiedPatternApp_complete
            (declarativeContext := declarativeContext)
            (declarativeParameters := declarativeParameters)
            (declarativeBindings := declarativeBindings)
            lookup closed before children childrenExtends
            declarativeDualsBounded aligned⟩
termination_by fuel

/-! ## Certified list dispatch -/

/-- Pattern-list traversal preserves the exact validator chronology supplied
by each certified head.  This is the list half of the final mutually
recursive pattern dispatcher; no validator premise is exposed to callers. -/
theorem certifiedPatternsOrigin_complete_nonempty
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
    (patternBelow : CertifiedPatternCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (signatureBelow : SignatureVarsBelow q signature)
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
    Nonempty (BoundedPairedCertifiedPatternsRunCompletion terminal signature before
      (inferPatternsFuel fuel signature executableContext executableParameters
        executableBindings selfEnv path index patterns state)
      q' S' ledger' duals bindings') := by
  cases fuel with
  | zero => simp [PatternsBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil =>
          let bounded := boundedPatternsNil_complete
            (signature := signature) (context := executableContext)
            (parameters := executableParameters) (selfEnv := selfEnv)
            (path := path) (index := index) inner before
            declarativeBindings bindings executableBindingsBounded
          exact ⟨BoundedPairedCertifiedPatternsRunCompletion.ofExact
            ⟨bounded, patternsNil terminal signature state⟩⟩
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
              (selfEnv := selfEnv) (path := index :: path) before
              signatureBelow contexts parameters bindings contextBounded
              parametersBounded bindingsBounded executableContextBounded
              executableParametersBounded executableBindingsBounded headAudit
              headAdequate)
          let headExtends := headOrigin.erase.supplyExtends
          obtain ⟨_, _, declarativeBindings₁Bounded⟩ :=
            headOrigin.erase.boundedBy closed before.declarative_bounded
              contextBounded parametersBounded bindingsBounded
          let tail := Classical.choice
            (certifiedPatternsOrigin_complete_nonempty closed
              (selfEnv := selfEnv) (path := path) (index := index + 1) inner
              (patternBelow.mono (Nat.le_succ inner)) head.bounded.run.completion
              (signatureBelow.mono headExtends)
              (contexts.transport head.bounded.run.transition)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                head.bounded.run.transition parameters)
              head.bounded.run.bindings (contextBounded.mono headExtends)
              (parametersBounded.mono headExtends)
              declarativeBindings₁Bounded
              (executableContextBounded.mono headExtends)
              (executableParametersBounded.mono headExtends)
              head.bounded.rawBindingsBounded tailAudit tailAdequate)
          let bounded := boundedPatternsCons_complete before head.bounded
            tail.bounded tailOrigin.erase.supplyExtends
          let validation := head.validation.trans tail.validation
          exact ⟨⟨bounded, validation.ordinary.history, validation⟩⟩
termination_by fuel

/-- The paired single/list interfaces close by strong induction on the shared
fuel ceiling.  This is the sole pattern-family package needed by the global
certified synthesis recursion. -/
theorem certifiedPatternFamilies_complete_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (bound : Nat)
    (synthBelow : CertifiedPatternSynthCompletenessBelow terminal signature
      bound)
    (capComplete : PatternCtorCapCompletenessPackage signature) :
    CertifiedPatternCompletenessBelow terminal signature bound ∧
      CertifiedPatternsCompletenessBelow terminal signature bound := by
  induction bound using Nat.strongRecOn with
  | ind bound induction =>
      constructor
      · refine ⟨?_⟩
        intro fuel below declarativeContext executableContext
          declarativeParameters executableParameters declarativeBindings
          executableBindings selfEnv path pattern dual bindings' q q' S S'
          ledger ledger' state raw origin before signatureBelow contexts
          parameters bindings contextBounded parametersBounded bindingsBounded
          executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate
        let smaller := induction fuel below
          (synthBelow.mono (Nat.le_of_lt below))
        exact certifiedPatternOrigin_complete_nonempty closed fuel
          (synthBelow := synthBelow.mono (Nat.le_of_lt below))
          (patternsBelow := smaller.2) (capComplete := capComplete) before
          signatureBelow contexts parameters bindings contextBounded
          parametersBounded bindingsBounded executableContextBounded
          executableParametersBounded executableBindingsBounded audit adequate
      · refine ⟨?_⟩
        intro fuel below declarativeContext executableContext
          declarativeParameters executableParameters declarativeBindings
          executableBindings selfEnv path index patterns duals bindings' q q'
          S S' ledger ledger' state raw origin before signatureBelow contexts
          parameters bindings contextBounded parametersBounded bindingsBounded
          executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate
        let smaller := induction fuel below
          (synthBelow.mono (Nat.le_of_lt below))
        exact certifiedPatternsOrigin_complete_nonempty closed fuel smaller.1
          before signatureBelow contexts parameters bindings contextBounded
          parametersBounded bindingsBounded executableContextBounded
          executableParametersBounded executableBindingsBounded audit adequate

end DemandTypingInferenceCompletenessPatternCertified
end TypePM
