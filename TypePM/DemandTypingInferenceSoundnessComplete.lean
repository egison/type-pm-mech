import TypePM.DemandTypingInferenceSoundnessFixMatcher
import TypePM.DemandTypingInferenceSoundnessLet
import TypePM.DemandTypingInferenceSoundnessPatterns

/-!
# Complete executable-to-demand-directed soundness

The local reconstruction slices retain exact executable state indices.  This
module combines them with the terminal validator at one enclosing root cut.
The combined certificates contain both the chronological raw/Origin witness
and a nonempty proof-relevant terminal-audit tree.  Keeping nonemptiness in
`Prop` permits structural composition without eliminating an opaque Origin
proof into `Type`; the final public theorem chooses the already-proved audit
witness only when it packages `SourceTyping`.
-/

namespace TypePM
namespace Inference

def DemandSynthCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (expression : Expr) (initial : InferState)
    (result : ExprResult) : Prop :=
  ∃ rawTarget,
    ∃ derived : DemandSynth signature initial.supply initial.prevailing context
        expression rawTarget result.state.supply result.state.prevailing,
      result.target = rawTarget ∧
        ∃ origin : DemandSynthOrigin signature derived
            initial.capabilityOrigins result.state.capabilityOrigins,
          Nonempty (DemandSynthTerminalAudit terminal signature origin)

def DemandSynthsCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (expressions : List Expr) (initial : InferState)
    (result : ExprsResult) : Prop :=
  ∃ rawTargets,
    ∃ derived : DemandSynths signature initial.supply initial.prevailing context
        expressions rawTargets result.state.supply result.state.prevailing,
      result.targets = rawTargets ∧
        ∃ origin : DemandSynthsOrigin signature derived
            initial.capabilityOrigins result.state.capabilityOrigins,
          Nonempty (DemandSynthsTerminalAudit terminal signature origin)

def DemandCheckCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (expression : Expr) (expected : Ty)
    (initial final : InferState) : Prop :=
  ∃ derived : DemandCheck signature initial.supply initial.prevailing context
      expression expected final.supply final.prevailing,
    ∃ origin : DemandCheckOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins,
      Nonempty (DemandCheckTerminalAudit terminal signature origin)

def DemandChecksCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (expressions : List Expr) (expecteds : List Ty)
    (initial final : InferState) : Prop :=
  ∃ derived : DemandChecks signature initial.supply initial.prevailing context
      expressions expecteds final.supply final.prevailing,
    ∃ origin : DemandChecksOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins,
      Nonempty (DemandChecksTerminalAudit terminal signature origin)

def DDPatternCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (pattern : Pattern) (initial : InferState) (result : PatternResult) : Prop :=
  ∃ derived : DDPattern signature initial.supply initial.prevailing context
      parameters bindings pattern result.dual result.bindings
      result.state.supply result.state.prevailing,
    ∃ origin : DDPatternOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins,
      Nonempty (DDPatternTerminalAudit terminal signature origin)

def DDPatternsCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (patterns : List Pattern) (initial : InferState)
    (result : PatternsResult) : Prop :=
  ∃ derived : DDPatterns signature initial.supply initial.prevailing context
      parameters bindings patterns result.duals result.bindings
      result.state.supply result.state.prevailing,
    ∃ origin : DDPatternsOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins,
      Nonempty (DDPatternsTerminalAudit terminal signature origin)

def DDArmsCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (ppBindings : MonoCtx) (arms : List Arm)
    (clauseTarget bodyTarget : Ty) (initial final : InferState) : Prop :=
  ∃ derived : DDArms signature initial.supply initial.prevailing context
      ppBindings arms clauseTarget bodyTarget final.supply final.prevailing,
    ∃ origin : DDArmsOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins,
      Nonempty (DDArmsTerminalAudit terminal signature origin)

def DDClauseCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (clause : Clause) (sharedTarget : Ty)
    (initial : InferState) (result : ClauseResult) : Prop :=
  ∃ derived : DDClause signature initial.supply initial.prevailing context
      clause sharedTarget result.rawHoles result.state.supply
      result.state.prevailing,
    ∃ origin : DDClauseOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins,
      Nonempty (DDClauseTerminalAudit terminal signature origin)

def DDClausesCertifiedRun (terminal : Subst) (signature : FrozenSig)
    (context : Context) (clauses : List Clause) (sharedTarget : Ty)
    (initial : InferState) (result : ClausesResult) : Prop :=
  ∃ derived : DDClauses signature initial.supply initial.prevailing context
      clauses sharedTarget result.rawHoleLists result.state.supply
      result.state.prevailing,
    ∃ origin : DDClausesOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins,
      Nonempty (DDClausesTerminalAudit terminal signature origin)

theorem DemandSynthCertifiedRun.toRun
    (certified : DemandSynthCertifiedRun terminal signature context expression
      initial result) :
    DemandSynthRun signature context expression initial result := by
  rcases certified with
    ⟨rawTarget, derived, targetEq, origin, _audit⟩
  exact ⟨rawTarget, derived, targetEq, origin⟩

theorem DemandSynthsCertifiedRun.toRun
    (certified : DemandSynthsCertifiedRun terminal signature context expressions
      initial result) :
    DemandSynthsRun signature context expressions initial result := by
  rcases certified with
    ⟨rawTargets, derived, targetsEq, origin, _audit⟩
  exact ⟨rawTargets, derived, targetsEq, origin⟩

theorem DemandCheckCertifiedRun.toRun
    (certified : DemandCheckCertifiedRun terminal signature context expression
      expected initial final) :
    DemandCheckRun signature context expression expected initial final := by
  rcases certified with ⟨derived, origin, _audit⟩
  exact ⟨derived, origin⟩

theorem DemandChecksCertifiedRun.toRun
    (certified : DemandChecksCertifiedRun terminal signature context expressions
      expecteds initial final) :
    DemandChecksRun signature context expressions expecteds initial final := by
  rcases certified with ⟨derived, origin, _audit⟩
  exact ⟨derived, origin⟩

theorem DDPatternCertifiedRun.toRun
    (certified : DDPatternCertifiedRun terminal signature context parameters
      bindings pattern initial result) :
    DDPatternRun signature context parameters bindings pattern initial
      result := by
  rcases certified with ⟨derived, origin, _audit⟩
  exact ⟨derived, origin⟩

theorem DDPatternsCertifiedRun.toRun
    (certified : DDPatternsCertifiedRun terminal signature context parameters
      bindings patterns initial result) :
    DDPatternsRun signature context parameters bindings patterns initial
      result := by
  rcases certified with ⟨derived, origin, _audit⟩
  exact ⟨derived, origin⟩

/-- A certified run from the canonical initial state already contains every
witness required by public source acceptance. -/
theorem DemandSynthCertifiedRun.toSourceTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (certified : DemandSynthCertifiedRun result.state.prevailing signature context
      expression (initialState signature context) result) :
    SourceTyping signature context expression result.resolvedTarget := by
  rcases certified with
    ⟨rawTarget, derived, targetEq, origin, ⟨audit⟩⟩
  refine ⟨rawTarget, result.state.supply, result.state.prevailing, ?_,
    result.state.capabilityOrigins, ?_, ?_, ?_⟩
  · exact derived
  · exact origin
  · exact audit
  · simp [ExprResult.resolvedTarget, targetEq]

/-! ## Terminal facts recovered from validator events -/

theorem DDTerminalAudit.PatternCtorFacts.ofWBridgeWF
    {signature : FrozenSig} {terminal : InferState} {solveCount : Nat}
    {name : String} {entry : PatternCtorScheme signature.observability}
    {duals : List Dual} {capability : Cap}
    (bridge : Reconstruction.WBridgeWF signature terminal)
    (lookup : signature.findPatternCtor name = some entry)
    (membership : .patternCtorCompatibility solveCount name
      (duals.map Dual.cap) capability ∈ terminal.trace.events) :
    DDTerminalAudit.PatternCtorFacts terminal.prevailing entry duals
      capability := by
  refine ⟨?_⟩
  simpa only [List.map_map, Function.comp_def, Dual.applySubst,
    Dual.apply] using
    Reconstruction.tracePatternCtorCheck_final bridge.patternCtors membership
      lookup

theorem DDTerminalAudit.MatcherFacts.ofWBridgeWF
    {signature : FrozenSig} {terminal : InferState} {solveCount : Nat}
    {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {localTarget : Ty}
    {localHoleLists : List (List Cap)} {localEvidence : List Shape.Evidence}
    {localCapability : Cap}
    (bridge : Reconstruction.WBridgeWF signature terminal)
    (membership : .matcherFinalization solveCount clauses rawTarget
      rawHoleLists localTarget localHoleLists localEvidence localCapability ∈
        terminal.trace.events) :
    DDTerminalAudit.MatcherFacts terminal.prevailing signature clauses
      rawHoleLists localCapability rawTarget := by
  rcases bridge.finalizationSuffixes _ membership with
    ⟨_solveBound, _localTargetEq, _localHolesEq, finalized⟩
  dsimp only at finalized
  rcases finalized with
    ⟨evidence, collected, shaped, caps, _catchAll, _binders, exhaustive,
      coverage⟩
  exact ⟨evidence, collected, shaped, caps, exhaustive, coverage⟩

end Inference
end TypePM
