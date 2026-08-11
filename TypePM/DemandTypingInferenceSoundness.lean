import TypePM.DemandTypingOrigin

/-!
# Executable traversal to demand-directed typing

This module starts the direct soundness proof from successful executable
traversals to the public demand-directed judgment.  The intermediate
`DDSynthRun` certificate deliberately retains only the pieces of `InferState`
that occur in `DDSynth` and `DDSynthOrigin`: the fresh supply, prevailing
substitution, and capability-origin ledger.  Trace events remain evidence for
constructing the certificate, rather than becoming an additional premise of
source typing.

The initial slices cover variable lookup, the two expression leaves whose
executable traversal performs no solve, and expression-list nil/cons.  Their
shape is the mutual induction invariant required by the remaining expression
constructors: executable raw targets are preserved, and the output indices of
the DD derivation are exactly the output state of the run.
-/

namespace TypePM
namespace Inference

@[simp] theorem InferState.recordEvent_supply
    (state : InferState) (event : TraceEvent) :
    (state.recordEvent event).supply = state.supply :=
  rfl

@[simp] theorem InferState.recordEvent_capabilityOrigins
    (state : InferState) (event : TraceEvent) :
    (state.recordEvent event).capabilityOrigins = state.capabilityOrigins :=
  rfl

@[simp] theorem InferState.recordSource_supply
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).supply = state.supply :=
  rfl

@[simp] theorem InferState.recordSource_prevailing
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).prevailing = state.prevailing :=
  rfl

@[simp] theorem InferState.recordSource_capabilityOrigins
    (state : InferState) (source : ProducerSource) :
    (state.recordSource source).capabilityOrigins =
      state.capabilityOrigins :=
  rfl

@[simp] theorem instantiateSchemeInState_prevailing
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.prevailing = state.prevailing :=
  rfl

@[simp] theorem instantiateSchemeInState_target
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).1 = (InferenceBase.instantiateScheme state.supply scheme).value :=
  rfl

@[simp] theorem instantiateSchemeInState_supply
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.supply =
        (InferenceBase.instantiateScheme state.supply scheme).supply :=
  rfl

@[simp] theorem instantiateSchemeInState_capabilityOrigins
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    (instantiateSchemeInState signature rawContext normalizedContext name state
      scheme).2.capabilityOrigins =
        state.capabilityOrigins.setOrigins
          (freshCapImages state.supply scheme.capBinders) .renameOnly :=
  rfl

/-- The DD certificate reconstructed from one successful executable
expression traversal.  This is an internal induction package for proving
`infer` sound with respect to `DDTyping`; it is not a second typing judgment. -/
def DDSynthRun (signature : FrozenSig) (context : Context)
    (expression : Expr) (initial : InferState) (result : ExprResult) : Prop :=
  ∃ rawTarget,
    ∃ derived : DDSynth signature initial.supply initial.prevailing context
        expression rawTarget result.state.supply result.state.prevailing,
      result.target = rawTarget ∧
        DDSynthOrigin signature derived initial.capabilityOrigins
          result.state.capabilityOrigins

/-- List form of `DDSynthRun`, retaining the executable raw target list and
the exact terminal state indices. -/
def DDSynthsRun (signature : FrozenSig) (context : Context)
    (expressions : List Expr) (initial : InferState)
    (result : ExprsResult) : Prop :=
  ∃ rawTargets,
    ∃ derived : DDSynths signature initial.supply initial.prevailing context
        expressions rawTargets result.state.supply result.state.prevailing,
      result.targets = rawTargets ∧
        DDSynthsOrigin signature derived initial.capabilityOrigins
          result.state.capabilityOrigins

/-- The empty executable expression-list result is the empty DD derivation. -/
theorem DDSynthsRun.nil
    (signature : FrozenSig) (context : Context) (initial : InferState) :
    DDSynthsRun signature context [] initial ⟨[], initial⟩ := by
  refine ⟨[], DDSynths.nil, rfl, ?_⟩
  exact DDSynthsOrigin.nil

/-- Compose exact head and tail run certificates in source order. -/
theorem DDSynthsRun.cons
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {expressions : List Expr} {initial : InferState} {head : ExprResult}
    {tail : ExprsResult}
    (headRun : DDSynthRun signature context expression initial head)
    (tailRun : DDSynthsRun signature context expressions head.state tail) :
    DDSynthsRun signature context (expression :: expressions) initial
      ⟨head.target :: tail.targets, tail.state⟩ := by
  rcases headRun with ⟨headTarget, headDerived, headEq, headOrigin⟩
  rcases tailRun with ⟨tailTargets, tailDerived, tailEq, tailOrigin⟩
  refine ⟨headTarget :: tailTargets, DDSynths.cons headDerived tailDerived,
    ?_, ?_⟩
  · simp [headEq, tailEq]
  · exact DDSynthsOrigin.cons headOrigin tailOrigin

/-- The empty branch of the executable expression-list traversal reconstructs
the empty DD list certificate. -/
theorem inferExprsFuel_nil_ddSynthsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {initial : InferState} {result : ExprsResult}
    (success : inferExprsFuel (fuel + 1) signature context selfEnv parent index
      [] initial = some result) :
    DDSynthsRun signature context [] initial result := by
  simp only [inferExprsFuel] at success
  have resultEq := Option.some.inj success
  subst result
  exact DDSynthsRun.nil signature context initial

/-- The cons branch of expression-list traversal preserves the exact
left-to-right state boundary.  The two functional premises are precisely the
head and tail induction hypotheses that the eventual mutual traversal theorem
will supply; no typing or runtime certificate is assumed. -/
theorem inferExprsFuel_cons_ddSynthsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {initial : InferState} {result : ExprsResult}
    (headSound : ∀ head : ExprResult,
      inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial = some head →
      DDSynthRun signature context expression initial head)
    (tailSound : ∀ (head : ExprResult) (tail : ExprsResult),
      inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions head.state = some tail →
      DDSynthsRun signature context expressions head.state tail)
    (success : inferExprsFuel (fuel + 1) signature context selfEnv parent index
      (expression :: expressions) initial = some result) :
    DDSynthsRun signature context (expression :: expressions) initial result := by
  simp only [inferExprsFuel] at success
  cases headEq : inferExprFuel fuel signature context selfEnv
      (index :: parent) expression initial with
  | none => simp [headEq] at success
  | some head =>
      cases tailEq : inferExprsFuel fuel signature context selfEnv parent
          (index + 1) expressions head.state with
      | none => simp [headEq, tailEq] at success
      | some tail =>
          simp only [headEq, tailEq, Option.some.injEq] at success
          subst result
          exact DDSynthsRun.cons (headSound head headEq)
            (tailSound head tail tailEq)

/-- A reconstructed run from the executable initial state is already a
public `DDTyping` derivation at the run's resolved result type. -/
theorem DDSynthRun.toDDTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (run : DDSynthRun signature context expression
      (initialState signature context) result) :
    DDTyping signature context expression result.resolvedTarget := by
  rcases run with ⟨rawTarget, derived, targetEq, origin⟩
  change DDSynth signature (initialSupply signature context) Subst.id context
    expression rawTarget result.state.supply result.state.prevailing at derived
  change DDSynthOrigin signature derived []
    result.state.capabilityOrigins at origin
  refine ⟨rawTarget, result.state.supply, result.state.prevailing, ?_,
    result.state.capabilityOrigins, ?_, ?_⟩
  · exact derived
  · exact origin
  · simp [ExprResult.resolvedTarget, targetEq]

/-- Context lookup uses the executable scheme-instantiation helper and
reconstructs the matching rename-only origin transition.  A direct-self hit
adds only trace/source evidence and therefore does not change any DD index. -/
theorem inferExprFuel_var_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.var name) initial = some result) :
    DDSynthRun signature context (.var name) initial result := by
  let entered := visit initial .exprVar path
  let normalizedContext := context.applySubst entered.prevailing
  cases lookup : normalizedContext.find? name with
  | none =>
      simp [inferExprFuel, entered, normalizedContext, lookup] at success
  | some scheme =>
      cases active : selfEnv.find? name with
      | none =>
          simp only [inferExprFuel, entered, normalizedContext, lookup,
            active] at success
          have resultEq := Option.some.inj success
          subst result
          have ddLookup :
              (context.applySubst initial.prevailing).find? name = some scheme := by
            simpa [normalizedContext, entered, visit] using lookup
          refine ⟨(InferenceBase.instantiateScheme initial.supply scheme).value,
            DDSynth.var ddLookup, ?_, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit]
          · simpa [finishExpr, visit,
              DDLedger.markSchemeInstance] using
              (DDSynthOrigin.var (signature := signature)
                (q := initial.supply) (S := initial.prevailing)
                (context := context) (ledger := initial.capabilityOrigins)
                ddLookup)
      | some placeholder =>
          simp only [inferExprFuel, entered, normalizedContext, lookup,
            active] at success
          have resultEq := Option.some.inj success
          subst result
          have ddLookup :
              (context.applySubst initial.prevailing).find? name = some scheme := by
            simpa [normalizedContext, entered, visit] using lookup
          refine ⟨(InferenceBase.instantiateScheme initial.supply scheme).value,
            DDSynth.var ddLookup, ?_, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit,
              recordSelfReference]
          · simpa [finishExpr, visit,
              recordSelfReference, DDLedger.markSchemeInstance] using
              (DDSynthOrigin.var (signature := signature)
                (q := initial.supply) (S := initial.prevailing)
                (context := context) (ledger := initial.capabilityOrigins)
                ddLookup)

/-- A successful literal traversal directly reconstructs the corresponding
DD synthesis and its unchanged origin ledger. -/
theorem inferExprFuel_lit_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {value : Int}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lit value) initial = some result) :
    DDSynthRun signature context (.lit value) initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.int, DDSynth.lit, rfl, ?_⟩
  exact DDSynthOrigin.lit

/-- A successful `something` traversal reconstructs the same one-target-meta
allocation as the DD rule, while leaving the origin ledger unchanged. -/
theorem inferExprFuel_something_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      .something initial = some result) :
    DDSynthRun signature context .something initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.matcher .any (.var initial.supply.nextTy), DDSynth.something,
    rfl, ?_⟩
  exact DDSynthOrigin.something

end Inference
end TypePM
