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
    Nonempty (BoundedCertifiedPatternsRunCompletion terminal signature before
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
          exact ⟨⟨bounded, patternsNil terminal signature state⟩⟩
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
          exact ⟨⟨bounded, patternsCons head.validation tail.validation⟩⟩
termination_by fuel

end DemandTypingInferenceCompletenessPatternCertified
end TypePM
