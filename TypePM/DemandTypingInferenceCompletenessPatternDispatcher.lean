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

/-- A named package prevents Lean from eagerly applying the higher-order
constructor-capability motive while elaborating recursive dispatcher calls. -/
structure PatternCtorCapCompletenessPackage (signature : FrozenSig) : Prop where
  complete : PatternCtorCapCompletenessMotive signature

/-- Recover the intrinsically indexed origin certificate carried by a
terminal-audit node. -/
def patternAuditOrigin
    {terminal : Subst} {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {context : Context} {parameters : PatternCtx}
    {bindingsIn bindingsOut : MonoCtx} {pattern : Pattern} {dual : Dual}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    {origin : DDPatternOrigin signature raw ledger ledger'}
    (_ : DDPatternTerminalAudit terminal signature origin) := origin

def patternsAuditOrigin
    {terminal : Subst} {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {context : Context} {parameters : PatternCtx}
    {bindingsIn bindingsOut : MonoCtx} {patterns : List Pattern}
    {duals : List Dual}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    {origin : DDPatternsOrigin signature raw ledger ledger'}
    (_ : DDPatternsTerminalAudit terminal signature origin) := origin

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

/-- Completeness for a list of user patterns, available strictly below
`bound`.  This is kept separate from `PatternCompletenessBelow`: the two
families are tied only after both structural dispatchers have been checked. -/
structure PatternsCompletenessBelow
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
      DDPatternsTerminalAudit terminal signature origin →
      PatternsBudgetAdequate fuel patterns →
      Nonempty (BoundedPatternsRunCompletion before
        (inferPatternsFuel fuel signature executableContext
          executableParameters executableBindings selfEnv path index patterns
          state)
        q' S' ledger' duals bindings')

def PatternsCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (available : PatternsCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    PatternsCompletenessBelow terminal signature smaller :=
  ⟨fun below => available.complete (Nat.lt_of_lt_of_le below boundLe)⟩

/-- Structural dispatch for one terminal-audited user pattern.  Calls into
pattern lists and expressions are supplied through strict fuel ceilings;
recursive binary-pattern calls decrease the concrete fuel directly. -/
theorem patternOrigin_complete_nonempty
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
    (synthBelow : PatternSynthCompletenessBelow terminal signature fuel)
    (patternsBelow : PatternsCompletenessBelow terminal signature fuel)
    (capComplete : PatternCtorCapCompletenessPackage signature)
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
    {raw : DDPattern signature q S declarativeContext declarativeParameters
      declarativeBindings pattern dual bindings' q' S'}
    {origin : DDPatternOrigin signature raw ledger ledger'}
    (audit : DDPatternTerminalAudit terminal signature origin)
    (adequate : PatternBudgetAdequate fuel pattern) :
    Nonempty (BoundedPatternRunCompletion before
      (inferPatternFuel fuel signature executableContext executableParameters
        executableBindings selfEnv path pattern state)
      q' S' ledger' dual bindings') := by
  cases audit with
  | pvar =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨boundedPatternPVarOrigin_complete
            (declarativeContext := declarativeContext)
            (declarativeParameters := declarativeParameters)
            inner before bindings executableBindingsBounded (by assumption)⟩
  | wild =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨boundedPatternWildOrigin_complete
            (declarativeContext := declarativeContext)
            (declarativeParameters := declarativeParameters)
            inner before bindings executableBindingsBounded⟩
  | embed =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨boundedPatternEmbedOrigin_complete inner before parameters
            executableParametersBounded bindings executableBindingsBounded
            (by assumption)⟩
  | pval expressionAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          exact ⟨boundedPatternPValOrigin_complete inner synthBelow
            (declarativeParameters := declarativeParameters) before contexts
            bindings contextBounded bindingsBounded executableContextBounded
            executableBindingsBounded expressionAudit adequate⟩
  | ptuple childrenAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let extension := before.visitExtension .patternTuple path
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (before.visit .patternTuple path)
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
          exact ⟨boundedPatternTuple_complete before children⟩
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
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (instantiation.correspondence.visit .patternCtor path)
              (contexts.transport
                (instantiation.transition.seq visitExtension))
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                (instantiation.transition.seq visitExtension) parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                (instantiation.transition.seq visitExtension) bindings)
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
          let targetAlignment :=
            _root_.TypePM.DemandTypingInferenceCompletenessAlignmentFamilies.ddAlignTargetListWithLedger_complete
            (origin := freshOrigin .pattern path
              "pattern-constructor-fields") children.run.completion
            children.run.duals
            (DemandTypingInferenceCompletenessStateMutual.BisimulationExtension.transportTyList
              (visitExtension.seq children.run.transition)
              instantiation.arguments)
            declarativeDualsBounded declarativeTargetsBounded
            children.rawDualsBounded executableTargetsBounded targetsAligned
          have declarativeCapsBounded : ∀ child ∈ duals.map Dual.cap,
              child.BoundedBy q₁ := by
            intro child membership
            obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
            exact (declarativeDualsBounded dual dualMem).1
          have executableCapsBounded : ∀ child ∈
              children.run.result.duals.map Dual.cap, child.BoundedBy q₁ := by
            intro child membership
            obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp membership
            exact (children.rawDualsBounded dual dualMem).1
          let dualsAtCap :=
            _root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDualList
              targetAlignment.transition children.run.duals
          let capPackage := Classical.choice
            (capComplete.complete
              (constraintOrigin := freshOrigin .pattern path
                "pattern-constructor-capability")
              (raw := capRaw) (rawOrigin := capOrigin)
              targetAlignment.completion
              (DemandTypingInferenceCompletenessPatternMain.DualListBisimulation.capabilities
                dualsAtCap)
              declarativeCapsBounded executableCapsBounded compatible)
          exact ⟨boundedPatternCtor_complete lookup closed before children
            childrenExtends declarativeDualsBounded targetsAligned
            capPackage.val capOrigin.erase.supplyExtends capPackage.property⟩
  | pand leftAudit rightAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let visitExtension := before.visitExtension .patternAnd path
          let leftOrigin := patternAuditOrigin leftAudit
          let left := Classical.choice
            (patternOrigin_complete_nonempty (selfEnv := selfEnv)
              (path := 0 :: path) (raw := leftOrigin.erase)
              (origin := leftOrigin) closed inner
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete)
              (before.visit .patternAnd path)
              (contexts.transport visitExtension)
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
            (patternOrigin_complete_nonempty (selfEnv := selfEnv)
              (path := 1 :: path) (raw := rightOrigin.erase)
              (origin := rightOrigin) closed inner
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete)
              left.run.completion
              (contexts.transport (visitExtension.seq left.run.transition))
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                (visitExtension.seq left.run.transition) parameters)
              left.run.bindings (contextBounded.mono leftExtends)
              (parametersBounded.mono leftExtends) leftBindingsBounded
              (executableContextBounded.mono leftExtends)
              (executableParametersBounded.mono leftExtends)
              left.rawBindingsBounded rightAudit (by
                change 8 * (patternTraversalFuel _ + 1) ≤ inner
                change 8 * ((1 + patternTraversalFuel _ +
                  patternTraversalFuel _) + 1) ≤ inner + 1 at adequate
                omega))
          let rightExtends := rightOrigin.erase.supplyExtends
          obtain ⟨_, rightDualBounded, _⟩ := rightOrigin.erase.boundedBy
            closed left.run.declarative_bounded
            (contextBounded.mono leftExtends)
            (parametersBounded.mono leftExtends) leftBindingsBounded
          exact ⟨boundedPatternAnd_complete before left right rightExtends
            (leftDualBounded.mono rightExtends) rightDualBounded
            (by assumption)⟩
  | por leftAudit rightAudit =>
      cases fuel with
      | zero => simp [PatternBudgetAdequate, patternTraversalFuel] at adequate
      | succ inner =>
          let visitExtension := before.visitExtension .patternOr path
          let leftOrigin := patternAuditOrigin leftAudit
          let left := Classical.choice
            (patternOrigin_complete_nonempty (selfEnv := selfEnv)
              (path := 0 :: path) (raw := leftOrigin.erase)
              (origin := leftOrigin) closed inner
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete)
              (before.visit .patternOr path)
              (contexts.transport visitExtension)
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
          let afterLeft := visitExtension.seq left.run.transition
          let rightOrigin := patternAuditOrigin rightAudit
          let right := Classical.choice
            (patternOrigin_complete_nonempty (selfEnv := selfEnv)
              (path := 1 :: path) (raw := rightOrigin.erase)
              (origin := rightOrigin) closed inner
              (synthBelow := synthBelow.mono (Nat.le_succ inner))
              (patternsBelow := patternsBelow.mono (Nat.le_succ inner))
              (capComplete := capComplete) left.run.completion
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
            rightOrigin.erase.boundedBy closed left.run.declarative_bounded
              (contextBounded.mono leftExtends)
              (parametersBounded.mono leftExtends)
              (bindingsBounded.mono leftExtends)
          exact ⟨boundedPatternOr_complete before left right rightExtends
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
          let children := Classical.choice
            (patternsBelow.complete (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := path) (index := 0)
              (instantiation.correspondence.visit .patternApp path)
              (contexts.transport
                (instantiation.transition.seq visitExtension))
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportPatternCtx
                (instantiation.transition.seq visitExtension) parameters)
              (_root_.TypePM.DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportMonoCtx
                (instantiation.transition.seq visitExtension) bindings)
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
          exact ⟨boundedPatternApp_complete
            (declarativeContext := declarativeContext)
            (declarativeParameters := declarativeParameters)
            (declarativeBindings := declarativeBindings)
            lookup closed before children
            childrenExtends declarativeDualsBounded aligned⟩
termination_by fuel

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

/-- The strict-ceiling pattern and pattern-list interfaces close together by
strong induction on the ceiling.  At a concrete call fuel, both dispatchers
see only the already-constructed package for strictly smaller fuel. -/
theorem patternFamilies_complete_below
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (bound : Nat)
    (synthBelow : PatternSynthCompletenessBelow terminal signature bound)
    (capComplete : PatternCtorCapCompletenessPackage signature) :
    PatternCompletenessBelow terminal signature bound ∧
      PatternsCompletenessBelow terminal signature bound := by
  induction bound using Nat.strongRecOn with
  | ind bound induction =>
      constructor
      · refine ⟨?_⟩
        intro fuel below declarativeContext executableContext
          declarativeParameters executableParameters declarativeBindings
          executableBindings selfEnv path pattern dual bindings' q q' S S'
          ledger ledger' state raw origin before contexts parameters bindings
          contextBounded parametersBounded bindingsBounded
          executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate
        let smaller := induction fuel below
          (synthBelow.mono (Nat.le_of_lt below))
        exact patternOrigin_complete_nonempty closed fuel
          (synthBelow := synthBelow.mono (Nat.le_of_lt below))
          (patternsBelow := smaller.2) (capComplete := capComplete) before
          contexts parameters bindings contextBounded parametersBounded
          bindingsBounded executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate
      · refine ⟨?_⟩
        intro fuel below declarativeContext executableContext
          declarativeParameters executableParameters declarativeBindings
          executableBindings selfEnv path index patterns duals bindings' q q'
          S S' ledger ledger' state raw origin before contexts parameters
          bindings contextBounded parametersBounded bindingsBounded
          executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate
        let smaller := induction fuel below
          (synthBelow.mono (Nat.le_of_lt below))
        exact patternsOrigin_complete_nonempty closed fuel smaller.1 before
          contexts parameters bindings contextBounded parametersBounded
          bindingsBounded executableContextBounded executableParametersBounded
          executableBindingsBounded audit adequate

end DemandTypingInferenceCompletenessPatternDispatcher
end TypePM
