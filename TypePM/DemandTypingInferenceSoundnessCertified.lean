import TypePM.DemandTypingInferenceSoundnessComplete
import TypePM.DemandTypingInferenceSoundnessMutual
import TypePM.DemandTypingTerminalAuditBuilder

/-!
# Terminal-audited executable-to-demand-directed soundness

Successful executable traversals are reconstructed together with their
chronological Origin certificate and a proof-relevant audit at one enclosing
terminal cut.  Recursive calls share that terminal cut through
`InferState.HistoryPrefix`; the finite `WBridgeWF` certificate supplies the
three facts that are intentionally not stable under arbitrary suffixes.
-/

namespace TypePM
namespace Inference

private theorem DemandSynthTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DemandSynth signature q subst context expression target q'
      subst'}
    {originLeft : DemandSynthOrigin signature rawLeft ledger ledger'}
    {originRight : DemandSynthOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DemandSynthTerminalAudit terminal signature originLeft)) :
    Nonempty (DemandSynthTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  rcases audit with ⟨audit⟩
  exact ⟨audit.transportOrigin⟩

private theorem DemandSynthsTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DemandSynths signature q subst context expressions targets
      q' subst'}
    {originLeft : DemandSynthsOrigin signature rawLeft ledger ledger'}
    {originRight : DemandSynthsOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DemandSynthsTerminalAudit terminal signature originLeft)) :
    Nonempty (DemandSynthsTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DemandCheckTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DemandCheck signature q subst context expression expected
      q' subst'}
    {originLeft : DemandCheckOrigin signature rawLeft ledger ledger'}
    {originRight : DemandCheckOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DemandCheckTerminalAudit terminal signature originLeft)) :
    Nonempty (DemandCheckTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DemandChecksTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DemandChecks signature q subst context expressions
      expecteds q' subst'}
    {originLeft : DemandChecksOrigin signature rawLeft ledger ledger'}
    {originRight : DemandChecksOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DemandChecksTerminalAudit terminal signature originLeft)) :
    Nonempty (DemandChecksTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DDPatternTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DDPattern signature q subst context parameters bindings
      pattern dual bindings' q' subst'}
    {originLeft : DDPatternOrigin signature rawLeft ledger ledger'}
    {originRight : DDPatternOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DDPatternTerminalAudit terminal signature originLeft)) :
    Nonempty (DDPatternTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DDPatternsTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DDPatterns signature q subst context parameters bindings
      patterns duals bindings' q' subst'}
    {originLeft : DDPatternsOrigin signature rawLeft ledger ledger'}
    {originRight : DDPatternsOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DDPatternsTerminalAudit terminal signature originLeft)) :
    Nonempty (DDPatternsTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DDArmsTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DDArms signature q subst context bindings arms target
      bodyTarget q' subst'}
    {originLeft : DDArmsOrigin signature rawLeft ledger ledger'}
    {originRight : DDArmsOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DDArmsTerminalAudit terminal signature originLeft)) :
    Nonempty (DDArmsTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DDClauseTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DDClause signature q subst context clause target holes
      q' subst'}
    {originLeft : DDClauseOrigin signature rawLeft ledger ledger'}
    {originRight : DDClauseOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DDClauseTerminalAudit terminal signature originLeft)) :
    Nonempty (DDClauseTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem DDClausesTerminalAudit.transportRawOrigin
    {rawLeft rawRight : DDClauses signature q subst context clauses target holes
      q' subst'}
    {originLeft : DDClausesOrigin signature rawLeft ledger ledger'}
    {originRight : DDClausesOrigin signature rawRight ledger ledger'}
    (audit : Nonempty (DDClausesTerminalAudit terminal signature originLeft)) :
    Nonempty (DDClausesTerminalAudit terminal signature originRight) := by
  have rawEq : rawLeft = rawRight := Subsingleton.elim _ _
  cases rawEq
  have originEq : originLeft = originRight := Subsingleton.elim _ _
  cases originEq
  exact audit

private theorem inferExprFuel_var_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {initial : InferState} {result : ExprResult} {terminal : InferState}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.var name) initial = some result) :
    DemandSynthCertifiedRun terminal.prevailing signature context (.var name)
      initial result := by
  let entered := visit initial .exprVar path
  let normalizedContext := context.applySubst entered.prevailing
  cases lookup : normalizedContext.find? name with
  | none => simp [inferExprFuel, entered, normalizedContext, lookup] at success
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
            DemandSynth.var ddLookup, ?_,
            DemandSynthOrigin.var (signature := signature) (q := initial.supply)
              (S := initial.prevailing) (context := context)
              (ledger := initial.capabilityOrigins) ddLookup, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit]
          · exact ⟨DemandSynthTerminalAudit.var (lookup := ddLookup)⟩
      | some placeholder =>
          simp only [inferExprFuel, entered, normalizedContext, lookup,
            active] at success
          have resultEq := Option.some.inj success
          subst result
          have ddLookup :
              (context.applySubst initial.prevailing).find? name = some scheme := by
            simpa [normalizedContext, entered, visit] using lookup
          refine ⟨(InferenceBase.instantiateScheme initial.supply scheme).value,
            DemandSynth.var ddLookup, ?_,
            DemandSynthOrigin.var (signature := signature) (q := initial.supply)
              (S := initial.prevailing) (context := context)
              (ledger := initial.capabilityOrigins) ddLookup, ?_⟩
          · simp [finishExpr, instantiateSchemeInState, visit,
              recordSelfReference]
          · exact ⟨DemandSynthTerminalAudit.var (lookup := ddLookup)⟩

private theorem inferExprFuel_lit_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {value : Int}
    {initial : InferState} {result : ExprResult} {terminal : InferState}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lit value) initial = some result) :
    DemandSynthCertifiedRun terminal.prevailing signature context (.lit value)
      initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  exact ⟨.int, DemandSynth.lit, rfl, DemandSynthOrigin.lit,
    ⟨DemandSynthTerminalAudit.lit⟩⟩

private theorem inferExprFuel_something_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {initial : InferState}
    {result : ExprResult} {terminal : InferState}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      .something initial = some result) :
    DemandSynthCertifiedRun terminal.prevailing signature context .something
      initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  exact ⟨.matcher .any (.var initial.supply.nextTy), DemandSynth.something,
    rfl, DemandSynthOrigin.something, ⟨DemandSynthTerminalAudit.something⟩⟩

private theorem inferPatternFuel_pvar_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {initial : InferState}
    {result : PatternResult} {terminal : InferState}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pvar name) initial = some result) :
    DDPatternCertifiedRun terminal.prevailing signature context parameters
      bindings (.pvar name) initial result := by
  simp only [inferPatternFuel] at success
  split at success
  · contradiction
  · rename_i absent
    have resultEq := Option.some.inj success
    subst result
    have freshName : name ∉ bindings.names := by simpa using absent
    exact ⟨DDPattern.pvar freshName,
      DDPatternOrigin.pvar (signature := signature) (q := initial.supply)
        (S := initial.prevailing) (context := context)
        (parameters := parameters) (bindings := bindings)
        (ledger := initial.capabilityOrigins) freshName,
      ⟨DDPatternTerminalAudit.pvar (freshName := freshName)⟩⟩

private theorem inferPatternFuel_wild_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {initial : InferState} {result : PatternResult}
    {terminal : InferState}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path .wild initial = some result) :
    DDPatternCertifiedRun terminal.prevailing signature context parameters
      bindings .wild initial result := by
  simp only [inferPatternFuel, Option.some.injEq] at success
  subst result
  exact ⟨DDPattern.wild, DDPatternOrigin.wild,
    ⟨DDPatternTerminalAudit.wild⟩⟩

private theorem inferPatternFuel_embed_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {initial : InferState}
    {result : PatternResult} {terminal : InferState}
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.embed name) initial = some result) :
    DDPatternCertifiedRun terminal.prevailing signature context parameters
      bindings (.embed name) initial result := by
  cases lookup : parameters.find? name with
  | none => simp [inferPatternFuel, lookup] at success
  | some dual =>
      simp only [inferPatternFuel, lookup, Option.some.injEq] at success
      subst result
      let raw : DDPattern signature initial.supply initial.prevailing context
          parameters bindings (.embed name) dual bindings initial.supply
          initial.prevailing := DDPattern.embed lookup
      let origin : DDPatternOrigin signature raw initial.capabilityOrigins
          initial.capabilityOrigins := DDPatternOrigin.embed (signature := signature)
          (q := initial.supply)
          (S := initial.prevailing) (context := context)
          (parameters := parameters) (bindings := bindings)
          (ledger := initial.capabilityOrigins) lookup
      refine ⟨raw, origin, ⟨?_⟩⟩
      exact @DDPatternTerminalAudit.embed terminal.prevailing signature
        initial.supply initial.prevailing context bindings
        initial.capabilityOrigins initial.supply initial.prevailing context
        bindings parameters name dual lookup

set_option maxHeartbeats 4000000 in
private theorem inferExprFuel_certifiedRunAtAux
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {initial : InferState} (result : ExprResult) (terminal : InferState)
    (success : inferExprFuel fuel signature context selfEnv path expression
      initial = some result)
    (bridge : Reconstruction.WBridgeWF signature terminal)
    (history : result.state.HistoryPrefix terminal) :
    DemandSynthCertifiedRun terminal.prevailing signature context expression
      initial result := by
  revert history bridge terminal success result
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression initial =>
      ∀ result terminal,
        inferExprFuel fuel signature context selfEnv path expression initial =
            some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DemandSynthCertifiedRun terminal.prevailing signature context expression
            initial result)
    (motive2 := fun fuel signature context selfEnv path expression expected
        initial =>
      ∀ final terminal,
        checkExprFuel fuel signature context selfEnv path expression expected
            initial = some final →
        Reconstruction.WBridgeWF signature terminal →
          final.HistoryPrefix terminal →
          DemandCheckCertifiedRun terminal.prevailing signature context expression
            expected initial final)
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern initial =>
      ∀ result terminal,
        inferPatternFuel fuel signature context parameters bindings selfEnv
            path pattern initial = some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DDPatternCertifiedRun terminal.prevailing signature context
            parameters bindings pattern initial result)
    (motive4 := fun fuel signature context parameters bindings selfEnv parent
        index patterns initial =>
      ∀ result terminal,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            parent index patterns initial = some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DDPatternsCertifiedRun terminal.prevailing signature context
            parameters bindings patterns initial result)
    (motive5 := fun fuel signature context selfEnv path clauses initial =>
      ∀ result terminal,
        inferMatcherFuel fuel signature context selfEnv path clauses initial =
            some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DemandSynthCertifiedRun terminal.prevailing signature context
            (.matcher clauses) initial result)
    (motive6 := fun fuel signature context selfEnv parent index clauses target
        initial =>
      ∀ result terminal,
        inferClausesFuel fuel signature context selfEnv parent index clauses
            target initial = some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DDClausesCertifiedRun terminal.prevailing signature context clauses
            target initial result)
    (motive7 := fun fuel signature context selfEnv path clause target initial =>
      ∀ result terminal,
        inferClauseFuel fuel signature context selfEnv path clause target
            initial = some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DDClauseCertifiedRun terminal.prevailing signature context clause
            target initial result)
    (motive8 := fun fuel signature context selfEnv bindings parent index arms
        target bodyTarget initial =>
      ∀ final terminal,
        checkArmsFuel fuel signature context selfEnv bindings parent index arms
            target bodyTarget initial = some final →
        Reconstruction.WBridgeWF signature terminal →
          final.HistoryPrefix terminal →
          DDArmsCertifiedRun terminal.prevailing signature context bindings
            arms target bodyTarget initial final)
    (motive9 := fun fuel signature context selfEnv parent index expressions
        expecteds initial =>
      ∀ final terminal,
        checkExprsFuel fuel signature context selfEnv parent index expressions
            expecteds initial = some final →
        Reconstruction.WBridgeWF signature terminal →
          final.HistoryPrefix terminal →
          DemandChecksCertifiedRun terminal.prevailing signature context expressions
            expecteds initial final)
    (motive10 := fun fuel signature context selfEnv parent index expressions
        initial =>
      ∀ result terminal,
        inferExprsFuel fuel signature context selfEnv parent index expressions
            initial = some result →
        Reconstruction.WBridgeWF signature terminal →
          result.state.HistoryPrefix terminal →
          DemandSynthsCertifiedRun terminal.prevailing signature context expressions
            initial result)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferExprFuel, checkExprFuel, inferPatternFuel, inferPatternsFuel,
      inferMatcherFuel, inferClausesFuel, inferClauseFuel, checkArmsFuel,
      checkExprsFuel, inferExprsFuel, Option.some.injEq]
  all_goals try contradiction
  case case3 =>
    rename_i fuel signature context selfEnv path initial name scheme target
      instState visited normalizedContext result terminal lookup instEq resultEq
      bridge history
    apply inferExprFuel_var_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    subst result
    simp [inferExprFuel, lookup, instEq]
  case case5 =>
    rename_i fuel signature context selfEnv path initial name body domain
      bodyInitial bodyResult bodyEq visited result terminal freshEq bodyIH
      resultEq bridge history
    subst result
    have domainEq' : lambdaDomain initial path = domain :=
      congrArg Prod.fst freshEq
    have bodyInitialEq : lambdaEntryState initial path = bodyInitial :=
      congrArg Prod.snd freshEq
    subst domain
    subst bodyInitial
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.lam name body) path
        (.fn (lambdaDomain initial path) bodyResult.target)
        bodyResult.state).trans history
    rcases bodyIH bodyResult terminal rfl bridge bodyHistory with
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin, ⟨bodyAudit⟩⟩
    have bodyOrigin' : DemandSynthOrigin signature bodyRaw
        initial.capabilityOrigins bodyResult.state.capabilityOrigins := by
      simpa only [lambdaEntryState_capabilityOrigins] using bodyOrigin
    have bodyAudit' : DemandSynthTerminalAudit terminal.prevailing signature
        bodyOrigin' := DemandSynthTerminalAudit.transportBuilt
      (DemandSynthTerminalAudit.BuiltAudit.of
        (origin := bodyOrigin) bodyAudit)
    exact ⟨.fn (.var initial.supply.nextTy) bodyTarget,
      DemandSynth.lam bodyRaw, by simp [finishExpr, bodyTargetEq],
      by simpa [finishExpr, visit] using DemandSynthOrigin.lam bodyOrigin',
      by simpa [finishExpr, visit] using
        Nonempty.intro (DemandSynthTerminalAudit.lam bodyAudit')⟩
  case case9 =>
    rename_i fuel signature context selfEnv path initial self argument body gate
      domain codomain placeholderState placeholder bodyInitial shadowed
      bodySelfEnv bodyContext bodyResult aligned visited result terminal bodyEq
      alignEq placeholderEq bodyIH resultEq bridge history
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    have alignedHistory : aligned.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.fix self argument body) path
        (.fn domain codomain) aligned).trans history
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (alignTypes_historyPrefix alignEq).trans alignedHistory
    rcases bodyIH bodyResult terminal rfl bridge bodyHistory with
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin, ⟨bodyAudit⟩⟩
    let bodyRun : DemandSynthRun signature bodyContext body bodyInitial bodyResult :=
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin⟩
    let bodyCertified : DemandSynthCertifiedRun terminal.prevailing signature
        bodyContext body bodyInitial bodyResult :=
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin, ⟨bodyAudit⟩⟩
    rcases (DirectSelf.fix_gate_eq_true self argument body).mp gate with
      ⟨distinct, direct⟩
    by_cases nonMatcher : NonMatcherBody body
    · have canonical := buildFixPlaceholder_nonMatcher signature initial path
        body nonMatcher
      rw [placeholderEq] at canonical
      have tripleEq := Option.some.inj canonical
      rcases Prod.mk.inj tripleEq with ⟨domainEq, restEq⟩
      rcases Prod.mk.inj restEq with ⟨codomainEq, stateEq⟩
      subst domain
      subst codomain
      subst placeholderState
      have canonicalBodyCertified : DemandSynthCertifiedRun terminal.prevailing
          signature
          ((argument, Scheme.mono (fixDomain initial path)) ::
            (self, Scheme.mono
              (.fn (fixDomain initial path) (fixCodomain initial path))) ::
            context) body (fixBodyEntryState initial path self argument)
          bodyResult := by
        simpa [bodyCertified, bodyContext, bodyInitial, visited,
          InferState.recordEvent]
      rcases canonicalBodyCertified with
        ⟨bodyTarget', bodyRaw', bodyTargetEq', bodyOrigin', ⟨bodyAudit'⟩⟩
      subst bodyTarget'
      rcases alignTypes_ddAlignTypesRun alignEq with
        ⟨alignedSupplyEq, alignedLedgerEq, alignedDD⟩
      let fixRaw := DemandSynth.fix distinct direct nonMatcher bodyRaw'
        alignedDD.erase
      let fixOrigin := DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin'
        alignedDD
      let fixAudit : DemandSynthTerminalAudit terminal.prevailing signature
          fixOrigin := DemandSynthTerminalAudit.fix (distinct := distinct)
            (direct := direct) (nonMatcher := nonMatcher)
            (aligned := alignedDD) bodyAudit'
      have base : DemandSynthCertifiedRun terminal.prevailing signature context
          (.fix self argument body) initial
          ⟨.fn (fixDomain initial path) (fixCodomain initial path), aligned⟩ := by
        unfold DemandSynthCertifiedRun
        rw [alignedSupplyEq, alignedLedgerEq]
        exact ⟨.fn (fixDomain initial path) (fixCodomain initial path),
          fixRaw, rfl, fixOrigin, ⟨fixAudit⟩⟩
      unfold DemandSynthCertifiedRun at base ⊢
      simpa [finishExpr, InferState.recordEvent_supply,
        InferState.prevailing_recordEvent,
        InferState.recordEvent_capabilityOrigins] using base
    · cases body <;>
        simp [NonMatcherBody, matcherProducingRoot] at nonMatcher
      rename_i clauses
      rcases buildFixPlaceholder_matcher_ddRun placeholderEq with
        ⟨placeholderPure, placeholderPrevailing, placeholderLedger⟩
      have bodyPrevailing : bodyInitial.prevailing = initial.prevailing := by
        simpa only [bodyInitial, InferState.prevailing_recordEvent, visited,
          visit] using
          placeholderPrevailing
      have bodyLedger : bodyInitial.capabilityOrigins =
          DDLedger.markCapRange initial.capabilityOrigins initial.supply
            bodyInitial.supply := by
        simpa only [bodyInitial, InferState.recordEvent_capabilityOrigins,
          InferState.recordEvent_supply, visited, visit] using
          placeholderLedger
      have transported := bodyCertified
      unfold DemandSynthCertifiedRun at transported
      rw [bodyPrevailing, bodyLedger] at transported
      rcases transported with
        ⟨bodyTarget', bodyRaw', bodyTargetEq', bodyOrigin', ⟨bodyAudit'⟩⟩
      subst bodyTarget'
      have placeholderPure' : fixMatcherPlaceholderSupply signature clauses
          (visit initial .exprFix path).supply =
            some (domain, codomain, bodyInitial.supply) := by
        simpa [bodyInitial] using placeholderPure
      rcases alignTypes_ddAlignTypesRun alignEq with
        ⟨alignedSupplyEq, alignedLedgerEq, alignedDD⟩
      let fixRaw := DemandSynth.fixMatcher distinct direct placeholderPure' bodyRaw'
        alignedDD.erase
      let fixOrigin := DemandSynthOrigin.fixMatcher distinct direct placeholderPure'
        bodyOrigin' alignedDD
      let fixAudit : DemandSynthTerminalAudit terminal.prevailing signature
          fixOrigin := DemandSynthTerminalAudit.fixMatcher
            (distinct := distinct) (direct := direct)
            (placeholder := placeholderPure') (aligned := alignedDD) bodyAudit'
      have base : DemandSynthCertifiedRun terminal.prevailing signature context
          (.fix self argument (.matcher clauses)) (visit initial .exprFix path)
          ⟨.fn domain codomain, aligned⟩ := by
        unfold DemandSynthCertifiedRun
        rw [alignedSupplyEq, alignedLedgerEq]
        exact ⟨.fn domain codomain, fixRaw, rfl, fixOrigin, ⟨fixAudit⟩⟩
      unfold DemandSynthCertifiedRun at base ⊢
      simpa [finishExpr, visit] using base
  case case15 =>
    rename_i fuel signature context selfEnv path initial function argument
      functionResult domain domainState domainEq resultTarget resultState
      resultFreshEq functionAligned functionAlignEq argumentResult argumentEq
      argumentFinal argumentAlignEq visited result terminal functionEq functionIH
      argumentIH resultEq bridge history
    subst result
    have domainTargetEq : applicationDomain functionResult path = domain :=
      congrArg Prod.fst domainEq
    have domainStateEq :
        (functionResult.state.freshTy
          (freshOrigin .expression path "application-domain")).2 =
            domainState := congrArg Prod.snd domainEq
    subst domain
    subst domainState
    have resultTargetEq : applicationResultTarget functionResult path =
        resultTarget := congrArg Prod.fst resultFreshEq
    have resultStateEq : applicationFreshState functionResult path =
        resultState := congrArg Prod.snd resultFreshEq
    subst resultTarget
    subst resultState
    have argumentFinalHistory : argumentFinal.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.app function argument) path
        (applicationResultTarget functionResult path) argumentFinal).trans
        history
    have argumentResultHistory : argumentResult.state.HistoryPrefix terminal :=
      (alignExprResultAtExpected_historyPrefix argumentAlignEq).trans
        argumentFinalHistory
    rcases argumentIH argumentResult terminal rfl bridge argumentResultHistory with
      ⟨argumentTarget, argumentRaw, argumentTargetEq, argumentOrigin,
        ⟨argumentAudit⟩⟩
    rcases alignExprResultAtExpected_ddAlignRun argumentAlignEq with
      ⟨argumentSupplyEq, argumentLedgerEq, argumentAligned⟩
    subst argumentTarget
    have argumentCheckRaw := DemandCheck.mk argumentRaw argumentAligned.erase
    have argumentCheckOrigin :=
      DemandCheckOrigin.mk argumentOrigin argumentAligned
    have argumentCheckAudit : DemandCheckTerminalAudit terminal.prevailing
        signature argumentCheckOrigin :=
      DemandCheckTerminalAudit.mk (aligned := argumentAligned) argumentAudit
    let argumentCheck : DemandCheckCertifiedRun terminal.prevailing signature
        context argument (applicationDomain functionResult path)
        functionAligned argumentFinal := by
      unfold DemandCheckCertifiedRun
      rw [argumentSupplyEq, argumentLedgerEq]
      exact ⟨argumentCheckRaw, argumentCheckOrigin, ⟨argumentCheckAudit⟩⟩
    have functionAlignedHistory : functionAligned.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix argumentEq).trans argumentResultHistory
    have freshHistory : (applicationFreshState functionResult path).HistoryPrefix
        terminal := by
      exact (alignTypes_historyPrefix functionAlignEq).trans
        functionAlignedHistory
    have functionHistory : functionResult.state.HistoryPrefix terminal := by
      apply InferState.HistoryPrefix.trans
        (InferState.historyPrefix_freshTy functionResult.state
          (freshOrigin .expression path "application-domain"))
      apply InferState.HistoryPrefix.trans
        (InferState.historyPrefix_freshTy
          (functionResult.state.freshTy
            (freshOrigin .expression path "application-domain")).2
          (freshOrigin .expression path "application-result"))
      exact freshHistory
    rcases functionIH functionResult terminal rfl bridge functionHistory with
      ⟨functionTarget, functionRaw, functionTargetEq, functionOrigin,
        ⟨functionAudit⟩⟩
    subst functionTarget
    have functionAlignRun : DemandAlignTypesRun functionResult.target
        (.fn (applicationDomain functionResult path)
          (applicationResultTarget functionResult path))
        (applicationFreshState functionResult path) functionAligned := by
      exact alignTypes_ddAlignTypesRun functionAlignEq
    rcases functionAlignRun with
      ⟨functionSupplyEq, functionLedgerEq, functionAlignedDD⟩
    unfold DemandCheckCertifiedRun at argumentCheck
    rw [functionSupplyEq, functionLedgerEq] at argumentCheck
    rcases argumentCheck with
      ⟨argumentCheckRaw, argumentCheckOrigin, ⟨argumentCheckAudit⟩⟩
    change DemandSynth signature initial.supply initial.prevailing context function
      functionResult.target functionResult.state.supply
        functionResult.state.prevailing at functionRaw
    change DemandSynthOrigin signature functionRaw initial.capabilityOrigins
      functionResult.state.capabilityOrigins at functionOrigin
    simp only [applicationFreshState_capabilityOrigins,
      applicationFreshState_prevailing, applicationDomain_eq,
      applicationResultTarget_eq] at functionAlignedDD
    let appRaw :=
      DemandSynth.app functionRaw functionAlignedDD.erase argumentCheckRaw
    have appOrigin : DemandSynthOrigin signature appRaw initial.capabilityOrigins
        argumentFinal.capabilityOrigins := by
      simpa using
        DemandSynthOrigin.app functionOrigin functionAlignedDD argumentCheckOrigin
    have appAudit : Nonempty
        (DemandSynthTerminalAudit terminal.prevailing signature appOrigin) :=
      DemandSynthTerminalAudit.transportRawOrigin
        (originLeft := DemandSynthOrigin.app functionOrigin functionAlignedDD
          argumentCheckOrigin)
        (originRight := appOrigin)
        ⟨DemandSynthTerminalAudit.app (aligned := functionAlignedDD)
          functionAudit argumentCheckAudit⟩
    exact ⟨.var (functionResult.state.supply.nextTy + 1), appRaw,
      by simp [finishExpr], appOrigin, by simpa [finishExpr] using appAudit⟩
  case case16 =>
    rename_i fuel signature context selfEnv path initial value result terminal
      resultEq bridge history
    apply inferExprFuel_lit_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    subst result
    simp [inferExprFuel]
  case case18 =>
    rename_i fuel signature context selfEnv path initial expressions children
      visited result terminal childrenEq childrenIH resultEq bridge history
    subst result
    have childrenHistory : children.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.tuple expressions) path
        (.prod children.targets) children.state).trans history
    rcases childrenIH children terminal rfl bridge childrenHistory with
      ⟨childTargets, childrenRaw, targetsEq, childrenOrigin,
        ⟨childrenAudit⟩⟩
    change DemandSynths signature initial.supply initial.prevailing context
      expressions childTargets children.state.supply
        children.state.prevailing at childrenRaw
    change DemandSynthsOrigin signature childrenRaw initial.capabilityOrigins
      children.state.capabilityOrigins at childrenOrigin
    exact ⟨.prod childTargets, DemandSynth.tuple childrenRaw,
      by simp [finishExpr, targetsEq],
      by simpa [finishExpr] using DemandSynthOrigin.tuple childrenOrigin,
      ⟨DemandSynthTerminalAudit.tuple childrenAudit⟩⟩
  case case21 =>
    rename_i fuel signature context selfEnv path initial name expressions scheme
      lookup expecteds target instState final childrenEq visited result terminal
      instEq childrenIH resultEq bridge history
    subst result
    simp only [instantiateCtorInState] at instEq
    cases instEq
    have frozenHistory : final.HistoryPrefix
        (final.freezeCapabilityExport
          (freshCapImages initial.supply scheme.capBinders)
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2) :=
      InferState.historyPrefix_freezeCapabilityExport _ _ _
    have childrenHistory : final.HistoryPrefix terminal :=
      frozenHistory.trans
        ((finishExpr_historyPrefix (.ctor name expressions) path
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
          (final.freezeCapabilityExport
            (freshCapImages initial.supply scheme.capBinders)
            (InferenceBase.instantiateCtorScheme initial.supply
              scheme).value.2)).trans history)
    rcases childrenIH final terminal rfl bridge childrenHistory with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    let childrenCertified : DemandChecksCertifiedRun terminal.prevailing signature
        context expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprCtor path) scheme).2
        final := ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    unfold DemandChecksCertifiedRun at childrenCertified
    have entrySupply :
        (instantiateCtorInState (visit initial .exprCtor path)
          scheme).2.supply =
            (InferenceBase.instantiateCtorScheme initial.supply scheme).supply := by
      calc
        _ = (InferenceBase.instantiateCtorScheme
            (visit initial .exprCtor path).supply scheme).supply :=
          instantiateCtorInState_supply (visit initial .exprCtor path) scheme
        _ = _ := by simp [visit]
    have entryPrevailing :
        (instantiateCtorInState (visit initial .exprCtor path)
          scheme).2.prevailing = initial.prevailing := by
      calc
        _ = (visit initial .exprCtor path).prevailing :=
          instantiateCtorInState_prevailing (visit initial .exprCtor path)
            scheme
        _ = _ := by simp [visit]
    have entryLedger :
        (instantiateCtorInState (visit initial .exprCtor path)
          scheme).2.capabilityOrigins =
            DDLedger.markCtorInstance initial.capabilityOrigins initial.supply
              scheme := by
      calc
        _ = DDLedger.markCtorInstance
            (visit initial .exprCtor path).capabilityOrigins
            (visit initial .exprCtor path).supply scheme :=
          instantiateCtorInState_capabilityOrigins
            (visit initial .exprCtor path) scheme
        _ = _ := by simp [visit]
    rw [entrySupply, entryPrevailing, entryLedger] at childrenCertified
    rcases childrenCertified with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    let ctorOrigin := DemandSynthOrigin.ctor lookup childrenOrigin
    let ctorAudit : DemandSynthTerminalAudit terminal.prevailing signature
        ctorOrigin := DemandSynthTerminalAudit.ctor (lookup := lookup) childrenAudit
    have base : DemandSynthCertifiedRun terminal.prevailing signature context
        (.ctor name expressions) initial
        (finishExpr (.ctor name expressions) path
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
          (final.freezeCapabilityExport
            (freshCapImages initial.supply scheme.capBinders)
            (InferenceBase.instantiateCtorScheme initial.supply
              scheme).value.2)) := by
      exact ⟨(InferenceBase.instantiateCtorScheme initial.supply scheme).value.2,
        DemandSynth.ctor lookup childrenRaw, rfl,
        by simpa [finishExpr] using ctorOrigin,
        by simpa [finishExpr] using Nonempty.intro ctorAudit⟩
    simpa only [visit, InferState.recordEvent_supply,
      InferenceBase.instantiateCtorScheme] using base
  case case24 =>
    rename_i fuel signature context selfEnv path initial op expressions scheme
      lookup expecteds target instState final childrenEq visited result terminal
      instEq childrenIH resultEq bridge history
    subst result
    simp only [instantiateCtorInState] at instEq
    cases instEq
    have frozenHistory : final.HistoryPrefix
        (final.freezeCapabilityExport
          (freshCapImages initial.supply scheme.capBinders)
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2) :=
      InferState.historyPrefix_freezeCapabilityExport _ _ _
    have childrenHistory : final.HistoryPrefix terminal :=
      frozenHistory.trans
        ((finishExpr_historyPrefix (.prim op expressions) path
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
          (final.freezeCapabilityExport
            (freshCapImages initial.supply scheme.capBinders)
            (InferenceBase.instantiateCtorScheme initial.supply
              scheme).value.2)).trans history)
    rcases childrenIH final terminal rfl bridge childrenHistory with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    let childrenCertified : DemandChecksCertifiedRun terminal.prevailing signature
        context expressions
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        (instantiateCtorInState (visit initial .exprPrim path) scheme).2
        final := ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    unfold DemandChecksCertifiedRun at childrenCertified
    have entrySupply :
        (instantiateCtorInState (visit initial .exprPrim path)
          scheme).2.supply =
            (InferenceBase.instantiateCtorScheme initial.supply scheme).supply := by
      calc
        _ = (InferenceBase.instantiateCtorScheme
            (visit initial .exprPrim path).supply scheme).supply :=
          instantiateCtorInState_supply (visit initial .exprPrim path) scheme
        _ = _ := by simp [visit]
    have entryPrevailing :
        (instantiateCtorInState (visit initial .exprPrim path)
          scheme).2.prevailing = initial.prevailing := by
      calc
        _ = (visit initial .exprPrim path).prevailing :=
          instantiateCtorInState_prevailing (visit initial .exprPrim path)
            scheme
        _ = _ := by simp [visit]
    have entryLedger :
        (instantiateCtorInState (visit initial .exprPrim path)
          scheme).2.capabilityOrigins =
            DDLedger.markCtorInstance initial.capabilityOrigins initial.supply
              scheme := by
      calc
        _ = DDLedger.markCtorInstance
            (visit initial .exprPrim path).capabilityOrigins
            (visit initial .exprPrim path).supply scheme :=
          instantiateCtorInState_capabilityOrigins
            (visit initial .exprPrim path) scheme
        _ = _ := by simp [visit]
    rw [entrySupply, entryPrevailing, entryLedger] at childrenCertified
    rcases childrenCertified with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    let primOrigin := DemandSynthOrigin.prim lookup childrenOrigin
    let primAudit : DemandSynthTerminalAudit terminal.prevailing signature
        primOrigin := DemandSynthTerminalAudit.prim (lookup := lookup) childrenAudit
    have base : DemandSynthCertifiedRun terminal.prevailing signature context
        (.prim op expressions) initial
        (finishExpr (.prim op expressions) path
          (InferenceBase.instantiateCtorScheme initial.supply scheme).value.2
          (final.freezeCapabilityExport
            (freshCapImages initial.supply scheme.capBinders)
            (InferenceBase.instantiateCtorScheme initial.supply
              scheme).value.2)) := by
      exact ⟨(InferenceBase.instantiateCtorScheme initial.supply scheme).value.2,
        DemandSynth.prim lookup childrenRaw, rfl,
        by simpa [finishExpr] using primOrigin,
        by simpa [finishExpr] using Nonempty.intro primAudit⟩
    simpa only [visit, InferState.recordEvent_supply,
      InferenceBase.instantiateCtorScheme] using base
  case case27 =>
    rename_i fuel signature context selfEnv path initial name value body
      valueResult normalizedContext normalizedValue scheme bodyInitial
      bodyResult visited result terminal bodyEq valueEq valueIH bodyIH resultEq
      bridge history
    subst result
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.letE name value body) path bodyResult.target
        bodyResult.state).trans history
    have eventHistory : bodyInitial.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix bodyEq).trans bodyHistory
    have valueHistory : valueResult.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent valueResult.state
        (.letGeneralization valueResult.state.trace.solves.length name context
          valueResult.target
          (context.applySubst valueResult.state.prevailing)
          (valueResult.state.prevailing.apply valueResult.target)
          (signature.generalize
            (context.applySubst valueResult.state.prevailing)
            (valueResult.state.prevailing.apply valueResult.target)))).trans
        eventHistory
    rcases valueIH valueResult terminal rfl bridge valueHistory with
      ⟨valueTarget, valueRaw, valueTargetEq, valueOrigin, ⟨valueAudit⟩⟩
    rcases bodyIH bodyResult terminal rfl bridge bodyHistory with
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin, ⟨bodyAudit⟩⟩
    subst valueTarget
    subst bodyTarget
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at valueRaw valueOrigin valueAudit bodyRaw bodyOrigin bodyAudit
    have facts := DDTerminalAudit.LetFacts.ofWBridgeWF bridge eventHistory
    let letOrigin := DemandSynthOrigin.letE valueOrigin bodyOrigin
    let letAudit : DemandSynthTerminalAudit terminal.prevailing signature
        letOrigin := DemandSynthTerminalAudit.letE valueAudit bodyAudit facts
    exact ⟨bodyResult.target, DemandSynth.letE valueRaw bodyRaw,
      by simp [finishExpr],
      by exact letOrigin,
      by simpa [finishExpr, letOrigin, letAudit] using
        Nonempty.intro letAudit⟩
  case case28 =>
    rename_i fuel signature context selfEnv path initial target freshState
      visited result terminal freshEq resultEq bridge history
    apply inferExprFuel_something_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    subst result
    simp [inferExprFuel, freshEq]
  case case30 =>
    rename_i fuel signature context selfEnv path initial clauses matcherResult
      visited result terminal matcherEq matcherIH resultEq bridge history
    subst result
    have matcherHistory : matcherResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.matcher clauses) path matcherResult.target
        matcherResult.state).trans history
    rcases matcherIH matcherResult terminal rfl bridge matcherHistory with
      ⟨rawTarget, matcherRaw, targetEq, matcherOrigin, ⟨matcherAudit⟩⟩
    change DemandSynth signature initial.supply initial.prevailing context
      (.matcher clauses) rawTarget matcherResult.state.supply
        matcherResult.state.prevailing at matcherRaw
    change DemandSynthOrigin signature matcherRaw initial.capabilityOrigins
      matcherResult.state.capabilityOrigins at matcherOrigin
    exact ⟨rawTarget, matcherRaw, by simpa [finishExpr] using targetEq,
      matcherOrigin, ⟨matcherAudit⟩⟩
  case case36 =>
    rename_i fuel signature context selfEnv path initial target matcher pattern
      body targetResult patternResult patternEq aligned targetAlignEq
      matcherFinal matcherEq bodyContext bodyEnv bodyResult visited result
      terminal bodyEq targetEq targetIH patternIH matcherIH bodyIH resultEq
      bridge history
    subst result
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.matchAll target matcher pattern body) path
        (.listT bodyResult.target) bodyResult.state).trans history
    have matcherHistory : matcherFinal.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix bodyEq).trans bodyHistory
    have alignedHistory : aligned.HistoryPrefix terminal :=
      (checkExprFuel_historyPrefix matcherEq).trans matcherHistory
    have patternHistory : patternResult.state.HistoryPrefix terminal :=
      (alignTypes_historyPrefix targetAlignEq).trans alignedHistory
    have targetHistory : targetResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix patternEq).trans patternHistory
    rcases targetIH targetResult terminal rfl bridge targetHistory with
      ⟨targetTarget, targetRaw, targetTargetEq, targetOrigin,
        ⟨targetAudit⟩⟩
    rcases patternIH patternResult terminal rfl bridge patternHistory with
      ⟨patternRaw, patternOrigin, ⟨patternAudit⟩⟩
    rcases alignTypes_ddAlignTypesRun targetAlignEq with
      ⟨alignedSupply, alignedLedger, targetAligned⟩
    have matcherCertified :=
      matcherIH matcherFinal terminal rfl bridge matcherHistory
    unfold DemandCheckCertifiedRun at matcherCertified
    rw [alignedSupply, alignedLedger] at matcherCertified
    rcases matcherCertified with
      ⟨matcherRaw, matcherOrigin, ⟨matcherAudit⟩⟩
    rcases bodyIH bodyResult terminal rfl bridge bodyHistory with
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin, ⟨bodyAudit⟩⟩
    subst targetTarget
    change DemandSynth signature initial.supply initial.prevailing context target
      targetResult.target targetResult.state.supply
        targetResult.state.prevailing at targetRaw
    change DemandSynthOrigin signature targetRaw initial.capabilityOrigins
      targetResult.state.capabilityOrigins at targetOrigin
    exact ⟨Ty.listT bodyTarget,
      DemandSynth.matchAll targetRaw patternRaw targetAligned.erase matcherRaw
        bodyRaw,
      by simp [finishExpr, bodyTargetEq],
      by simpa [finishExpr] using
        DemandSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
          matcherOrigin bodyOrigin,
      ⟨DemandSynthTerminalAudit.matchAll (targetAligned := targetAligned)
        targetAudit patternAudit matcherAudit bodyAudit⟩⟩
  case case42 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name absent capability capState capEq target targetState targetEq result
      terminal resultEq bridge history
    have freshName : name ∉ bindings.names := by simpa using absent
    apply inferPatternFuel_pvar_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, capEq, targetEq, freshName] using resultEq
  case case43 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      capability capState capEq target targetState targetEq result terminal
      resultEq bridge history
    apply inferPatternFuel_wild_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, capEq, targetEq] using congrArg some resultEq
  case case45 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      expression expressionResult expressionEq capability capState capEq result
      terminal expressionIH resultEq bridge history
    subst result
    cases capEq
    have expressionHistory : expressionResult.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_freshCap expressionResult.state
        (freshOrigin .pattern path "pattern-value-capability")).trans
        ((InferState.historyPrefix_recordEvent _ _).trans
          ((InferState.historyPrefix_recordEvent _ _).trans history))
    rcases expressionIH expressionResult terminal rfl bridge expressionHistory with
      ⟨expressionTarget, expressionRaw, expressionTargetEq, expressionOrigin,
        ⟨expressionAudit⟩⟩
    subst expressionTarget
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at expressionRaw expressionOrigin
    let patternOrigin := @DDPatternOrigin.pval signature parameters
      initial.supply initial.prevailing context parameters bindings expression
      expressionResult.target expressionResult.state.supply
      expressionResult.state.prevailing initial.capabilityOrigins
      expressionResult.state.capabilityOrigins expressionRaw expressionOrigin
    have patternAudit : DDPatternTerminalAudit terminal.prevailing signature
        patternOrigin :=
      @DDPatternTerminalAudit.pval terminal.prevailing signature parameters
        parameters initial.supply initial.prevailing bindings context expression
        expressionResult.target expressionResult.state.supply
        expressionResult.state.prevailing expressionRaw initial.capabilityOrigins
        expressionResult.state.capabilityOrigins expressionOrigin expressionAudit
    exact ⟨DDPattern.pval expressionRaw, patternOrigin, ⟨patternAudit⟩⟩
  case case47 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name dual lookup result terminal resultEq bridge history
    apply inferPatternFuel_embed_certifiedRunAt (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, lookup] using congrArg some resultEq
  case case49 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      patterns children childrenEq result terminal childrenIH resultEq bridge
      history
    subst result
    have childrenHistory : children.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans history
    rcases childrenIH children terminal rfl bridge childrenHistory with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at childrenRaw childrenOrigin
    exact ⟨DDPattern.ptuple childrenRaw,
      DDPatternOrigin.ptuple childrenOrigin,
      ⟨DDPatternTerminalAudit.ptuple childrenAudit⟩⟩
  case case39 =>
    rename_i fuel signature context selfEnv path expression expected initial
      synthesized inferEq final terminal synthIH alignEq bridge history
    have synthHistory : synthesized.state.HistoryPrefix terminal :=
      (alignExprResultAtExpected_historyPrefix alignEq).trans history
    rcases synthIH synthesized terminal rfl bridge synthHistory with
      ⟨rawTarget, synthRaw, targetEq, synthOrigin, ⟨synthAudit⟩⟩
    rcases alignExprResultAtExpected_ddAlignRun alignEq with
      ⟨supplyEq, ledgerEq, aligned⟩
    subst rawTarget
    unfold DemandCheckCertifiedRun
    rw [supplyEq, ledgerEq]
    exact ⟨DemandCheck.mk synthRaw aligned.erase,
      DemandCheckOrigin.mk synthOrigin aligned,
      ⟨DemandCheckTerminalAudit.mk (aligned := aligned) synthAudit⟩⟩
  case case54 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name patterns entry lookup expecteds target instState instEq children
      childrenEq targetsFinal targetsEq childCaps capability solvedState
      resolvedChildren resolvedCapability result terminal capabilityEq compatible
      childrenIH resultEq bridge history
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    let resultTarget := target
    let exportPayload := capabilityExportPayload [capability]
      (resultTarget :: children.bindings.map fun binding => binding.2)
    let frozen := solvedState.freezeCapabilityExport
      (freshCapImages initial.supply entry.scheme.capBinders) exportPayload
    let compatibilityEvent := TraceEvent.patternCtorCompatibility
      frozen.trace.solves.length name childCaps capability
    let inferredEvent := TraceEvent.inferredPattern (.pctor name patterns)
      ⟨capability, resultTarget⟩ children.bindings path
    have childrenHistory : children.state.HistoryPrefix terminal :=
      (alignPatternTargets_historyPrefix targetsEq).trans
        ((solvePatternCtorCapability_historyPrefix capabilityEq).trans
          ((solvedState.historyPrefix_freezeCapabilityExport _ _).trans
            ((frozen.historyPrefix_recordEvent compatibilityEvent).trans
              (((frozen.recordEvent compatibilityEvent).historyPrefix_recordEvent
                inferredEvent).trans history))))
    rcases childrenIH children terminal rfl bridge childrenHistory with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    simp only [instantiateCtorInState] at instEq
    cases instEq
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at childrenRaw childrenOrigin
    rcases alignPatternTargets_ddAlignPatternTargetsRun targetsEq with
      ⟨targetsSupply, targetsLedger, targetsAligned⟩
    rcases solvePatternCtorCapability_ddPatternCtorCapRun capabilityEq with
      ⟨capRaw, capOrigin⟩
    have capAt :
        ∃ raw : DDPatternCtorCap signature entry children.state.supply
            targetsFinal.prevailing childCaps capability solvedState.supply
            solvedState.prevailing,
          DDPatternCtorCapOrigin signature entry raw
            children.state.capabilityOrigins
            solvedState.capabilityOrigins := by
      rw [← targetsSupply, ← targetsLedger]
      exact ⟨capRaw, capOrigin⟩
    rcases capAt with ⟨capRaw', capOrigin'⟩
    let rawDerived := DDPattern.pctor lookup childrenRaw targetsAligned.erase
      capRaw' compatible
    let rawOrigin := DDPatternOrigin.pctor lookup childrenOrigin targetsAligned
      capOrigin' compatible
    have localMembership : compatibilityEvent ∈
        ((frozen.recordEvent compatibilityEvent).recordEvent
          inferredEvent).trace.events := by
      simp [compatibilityEvent, inferredEvent, InferState.recordEvent]
    have facts := DDTerminalAudit.PatternCtorFacts.ofWBridgeWF bridge lookup
      (history.event_mem localMembership)
    have sourceAudit : Nonempty
        (DDPatternTerminalAudit terminal.prevailing signature rawOrigin) :=
      ⟨DDPatternTerminalAudit.pctor (lookup := lookup)
        (targetsAligned := targetsAligned) (capOrigin := capOrigin')
        (compatible := compatible) childrenAudit facts⟩
    simp only [DDPatternCertifiedRun, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins,
      InferState.freezeCapabilityExport_supply,
      InferState.freezeCapabilityExport_prevailing,
      InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
    refine ⟨rawDerived, rawOrigin, ?_⟩
    exact DDPatternTerminalAudit.transportRawOrigin sourceAudit
  case case59 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      left right leftResult leftEq rightResult rightEq final alignEq result
      terminal leftIH rightIH resultEq bridge history
    subst result
    have finalHistory : final.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans history
    have rightHistory : rightResult.state.HistoryPrefix terminal :=
      (alignDuals_historyPrefix alignEq).trans finalHistory
    have leftHistory : leftResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix rightEq).trans rightHistory
    rcases leftIH leftResult terminal rfl bridge leftHistory with
      ⟨leftRaw, leftOrigin, ⟨leftAudit⟩⟩
    rcases rightIH rightResult terminal rfl bridge rightHistory with
      ⟨rightRaw, rightOrigin, ⟨rightAudit⟩⟩
    rcases alignDuals_ddAlignDualRun alignEq with
      ⟨supplyEq, ledgerEq, aligned⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at leftRaw leftOrigin
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.pand left right)
        leftResult.dual rightResult.bindings final.supply final.prevailing,
      ∃ origin : DDPatternOrigin signature derived initial.capabilityOrigins
          final.capabilityOrigins,
        Nonempty (DDPatternTerminalAudit terminal.prevailing signature origin)
    rw [supplyEq, ledgerEq]
    exact ⟨DDPattern.pand leftRaw rightRaw aligned.erase,
      DDPatternOrigin.pand leftOrigin rightOrigin aligned,
      ⟨DDPatternTerminalAudit.pand (aligned := aligned)
        leftAudit rightAudit⟩⟩
  case case64 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      left right leftResult leftEq rightResult rightEq dualFinal dualEq final
      bindingsEq result terminal leftIH rightIH resultEq bridge history
    subst result
    have finalHistory : final.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans history
    have dualHistory : dualFinal.HistoryPrefix terminal :=
      (alignBindings_historyPrefix bindingsEq).trans finalHistory
    have rightHistory : rightResult.state.HistoryPrefix terminal :=
      (alignDuals_historyPrefix dualEq).trans dualHistory
    have leftHistory : leftResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix rightEq).trans rightHistory
    rcases leftIH leftResult terminal rfl bridge leftHistory with
      ⟨leftRaw, leftOrigin, ⟨leftAudit⟩⟩
    rcases rightIH rightResult terminal rfl bridge rightHistory with
      ⟨rightRaw, rightOrigin, ⟨rightAudit⟩⟩
    rcases alignDuals_ddAlignDualRun dualEq with
      ⟨dualSupply, dualLedger, dualAligned⟩
    rcases alignBindings_ddAlignBindingsRun bindingsEq with
      ⟨bindingsSupply, bindingsLedger, bindingsAligned⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at leftRaw leftOrigin
    rw [dualLedger] at bindingsAligned
    have finalSupply : final.supply = rightResult.state.supply :=
      bindingsSupply.trans dualSupply
    have finalLedger :
        final.capabilityOrigins = rightResult.state.capabilityOrigins :=
      bindingsLedger.trans dualLedger
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.por left right)
        leftResult.dual leftResult.bindings final.supply final.prevailing,
      ∃ origin : DDPatternOrigin signature derived initial.capabilityOrigins
          final.capabilityOrigins,
        Nonempty (DDPatternTerminalAudit terminal.prevailing signature origin)
    rw [finalSupply, finalLedger]
    exact ⟨DDPattern.por leftRaw rightRaw dualAligned.erase
        bindingsAligned.erase,
      DDPatternOrigin.por leftOrigin rightOrigin dualAligned bindingsAligned,
      ⟨DDPatternTerminalAudit.por (dualsAligned := dualAligned)
        (bindingsAligned := bindingsAligned) leftAudit rightAudit⟩⟩
  case case68 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name patterns scheme lookup normalizedContext normalizedParameters
      normalizedBindings expectedArgs resultDual instState children final result
      terminal instEq childrenEq alignEq childrenIH resultEq bridge history
    subst result
    have finalHistory : final.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans history
    have childrenHistory : children.state.HistoryPrefix terminal :=
      (alignDualLists_historyPrefix alignEq).trans finalHistory
    rcases childrenIH children terminal rfl bridge childrenHistory with
      ⟨childrenRaw, childrenOrigin, ⟨childrenAudit⟩⟩
    simp only [instantiateDualInState] at instEq
    cases instEq
    rcases alignDualLists_ddAlignDualListRun alignEq with
      ⟨supplyEq, ledgerEq, aligned⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at childrenRaw childrenOrigin
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.papp name patterns)
        (InferenceBase.instantiateDualScheme initial.supply scheme).value.2
        children.bindings final.supply final.prevailing,
      ∃ origin : DDPatternOrigin signature derived initial.capabilityOrigins
          final.capabilityOrigins,
        Nonempty (DDPatternTerminalAudit terminal.prevailing signature origin)
    rw [supplyEq, ledgerEq]
    exact ⟨DDPattern.papp lookup childrenRaw aligned.erase,
      DDPatternOrigin.papp lookup childrenOrigin aligned,
      ⟨DDPatternTerminalAudit.papp (lookup := lookup) (aligned := aligned)
        childrenAudit⟩⟩
  case case70 =>
    rename_i fuel signature context parameters bindings selfEnv path index
      initial result terminal resultEq bridge history
    subst result
    exact ⟨DDPatterns.nil, DDPatternsOrigin.nil,
      ⟨DDPatternsTerminalAudit.nil⟩⟩
  case case73 =>
    rename_i fuel signature context parameters bindings selfEnv parent index
      pattern patterns initial head headEq tail tailEq result terminal headIH
      tailIH resultEq bridge history
    subst result
    have tailCertified := tailIH tail terminal rfl bridge history
    have headHistory : head.state.HistoryPrefix terminal :=
      (inferPatternsFuel_historyPrefix tailEq).trans history
    have headCertified := headIH head terminal rfl bridge headHistory
    rcases headCertified with ⟨headRaw, headOrigin, ⟨headAudit⟩⟩
    rcases tailCertified with ⟨tailRaw, tailOrigin, ⟨tailAudit⟩⟩
    exact ⟨DDPatterns.cons headRaw tailRaw,
      DDPatternsOrigin.cons headOrigin tailOrigin,
      ⟨DDPatternsTerminalAudit.cons headAudit tailAudit⟩⟩
  case case78 =>
    rename_i fuel signature context selfEnv path clauses initial target
      freshState freshEq clausesResult clausesEq finalHoleLists evidences
      capability finalTarget result terminal collectEq shapeEq checks clausesIH
      resultEq bridge history
    simp only [InferState.freshTy, InferenceBase.freshTyMeta] at freshEq
    cases freshEq
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    let coverageState := clausesResult.state.recordEvent
      (.literalCoverage clauses capability)
    let finalizationEvent := TraceEvent.matcherFinalization
      coverageState.trace.solves.length clauses (.var initial.supply.nextTy)
      clausesResult.rawHoleLists
      (clausesResult.state.prevailing.apply (.var initial.supply.nextTy))
      finalHoleLists evidences capability
    let finalizedState := coverageState.recordEvent finalizationEvent
    have clausesHistory : clausesResult.state.HistoryPrefix terminal :=
      (clausesResult.state.historyPrefix_recordEvent _).trans
        ((coverageState.historyPrefix_recordEvent finalizationEvent).trans
          ((finalizedState.historyPrefix_protectMatcherCapability
            capability).trans history))
    rcases clausesIH clausesResult terminal rfl bridge clausesHistory with
      ⟨clausesRaw, clausesOrigin, ⟨clausesAudit⟩⟩
    simp only [Bool.and_eq_true] at checks
    have clauseCaps := checks.1.1.1.1
    have catchAll := checks.1.1.1.2
    have binders := checks.1.1.2
    have arms := checks.1.2
    have coverage := checks.2
    have collected : collectClauseEvidence signature.toMatcherSig clauses
        (terminalHoleCaps clausesResult.state.prevailing
          clausesResult.rawHoleLists) = some evidences := by
      simpa [terminalHoleCaps, finalHoleLists, List.map_map,
        Function.comp_def] using collectEq
    have clauseCaps' : clauseCapsListCheck signature capability clauses
        (terminalHoleCaps clausesResult.state.prevailing
          clausesResult.rawHoleLists) = true := by
      simpa [terminalHoleCaps, finalHoleLists, List.map_map,
        Function.comp_def] using clauseCaps
    let rawDerived := DemandSynth.matcher clausesRaw collected shapeEq clauseCaps'
      catchAll binders arms coverage
    let rawOrigin := DemandSynthOrigin.matcher clausesOrigin collected shapeEq
      clauseCaps' catchAll binders arms coverage
    change DemandSynth signature initial.supply initial.prevailing context
      (.matcher clauses) (.matcher capability (.var initial.supply.nextTy))
      clausesResult.state.supply clausesResult.state.prevailing at rawDerived
    change DemandSynthOrigin signature rawDerived initial.capabilityOrigins
      (DDLedger.freezeMatcherProducerExcept
        clausesResult.state.capabilityOrigins capability
        (borrowedMatcherCapVarsAt clausesResult.state.prevailing context))
        at rawOrigin
    have localMembership : finalizationEvent ∈
        (finalizedState.protectMatcherCapabilityExcept capability
          (borrowedMatcherCapVars finalizedState context)).trace.events := by
      simp [finalizedState, finalizationEvent, coverageState,
        InferState.recordEvent, InferState.protectMatcherCapabilityExcept]
    have facts := DDTerminalAudit.MatcherFacts.ofWBridgeWF bridge
      (history.event_mem localMembership)
    have sourceAudit : Nonempty
        (DemandSynthTerminalAudit terminal.prevailing signature rawOrigin) :=
      ⟨DemandSynthTerminalAudit.matcher (collected := collected)
        (inferred := shapeEq) (clauseCaps := clauseCaps')
        (catchAll := catchAll) (binders := binders) (arms := arms)
        (coverage := coverage) clausesAudit facts⟩
    refine ⟨.matcher capability (.var initial.supply.nextTy), rawDerived,
      rfl, ?_, ?_⟩
    · simpa [DDLedger.freezeMatcherProducerExcept,
        DDLedger.matcherProducerLeavesExcept,
        borrowedMatcherCapVars] using rawOrigin
    · exact DemandSynthTerminalAudit.transportRawOrigin sourceAudit
  case case81 =>
    rename_i fuel signature context selfEnv path index target initial result
      terminal resultEq bridge history
    subst result
    exact ⟨DDClauses.nil, DDClausesOrigin.nil,
      ⟨DDClausesTerminalAudit.nil⟩⟩
  case case84 =>
    rename_i fuel signature context selfEnv parent index clause clauses target
      initial head headEq tail tailEq result terminal headIH tailIH resultEq
      bridge history
    subst result
    have tailCertified := tailIH tail terminal rfl bridge history
    have headHistory : head.state.HistoryPrefix terminal :=
      (inferClausesFuel_historyPrefix tailEq).trans history
    have headCertified := headIH head terminal rfl bridge headHistory
    rcases headCertified with ⟨headRaw, headOrigin, ⟨headAudit⟩⟩
    rcases tailCertified with ⟨tailRaw, tailOrigin, ⟨tailAudit⟩⟩
    exact ⟨DDClauses.cons headRaw tailRaw,
      DDClausesOrigin.cons headOrigin tailOrigin,
      ⟨DDClausesTerminalAudit.cons headAudit tailAudit⟩⟩
  case case90 =>
    rename_i fuel signature context selfEnv path pp next arms target initial
      ppResult ppEq nextMatchers decompose slotTargets nextFinal bodyTarget
      armsFinal result terminal nextEq armsEq nextIH armsIH resultEq bridge
      history
    subst result
    have nextHistory : nextFinal.HistoryPrefix terminal :=
      (checkArmsFuel_historyPrefix armsEq).trans history
    rcases nextIH nextFinal terminal rfl bridge nextHistory with
      ⟨nextRaw, nextOrigin, ⟨nextAudit⟩⟩
    rcases armsIH armsFinal terminal rfl bridge history with
      ⟨armsRaw, armsOrigin, ⟨armsAudit⟩⟩
    rcases inferPPatFuel_ddPPatRun ppEq with
      ⟨_ppTargetEq, ppRaw, ppOrigin⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at ppRaw ppOrigin
    exact ⟨DDClause.mk ppRaw decompose nextRaw armsRaw,
      DDClauseOrigin.mk ppOrigin decompose nextOrigin armsOrigin,
      ⟨show DDClauseTerminalAudit terminal.prevailing signature
          (DDClauseOrigin.mk ppOrigin decompose nextOrigin armsOrigin) from
        DDClauseTerminalAudit.mk (ppOrigin := ppOrigin)
          (decomposed := decompose) nextAudit armsAudit⟩⟩
  case case92 =>
    rename_i fuel signature context selfEnv bindings parent index target
      bodyTarget initial final terminal resultEq bridge history
    subst final
    exact ⟨DDArms.nil, DDArmsOrigin.nil, ⟨DDArmsTerminalAudit.nil⟩⟩
  case case95 =>
    rename_i fuel signature context selfEnv ppBindings parent index pattern
      body arms target bodyTarget initial patternResult patternEq distinct
      bodyContext bodyEnv bodyFinal final terminal bodyEq bodyIH tailIH resultEq
      bridge history
    simp only [if_pos trivial] at resultEq
    have bodyHistory : bodyFinal.HistoryPrefix terminal :=
      (checkArmsFuel_historyPrefix resultEq).trans history
    rcases bodyIH bodyFinal terminal rfl bridge bodyHistory with
      ⟨bodyRaw, bodyOrigin, ⟨bodyAudit⟩⟩
    rcases tailIH final terminal resultEq bridge history with
      ⟨tailRaw, tailOrigin, ⟨tailAudit⟩⟩
    rcases inferDPatFuel_ddDPatRun patternEq with
      ⟨_patternTargetEq, patternRaw, patternOrigin⟩
    have namesDistinct :=
      (namesDisjoint_eq_true patternResult.bindings.names
        ppBindings.names).mp distinct
    have bodyRaw' : DemandCheck signature patternResult.state.supply
        patternResult.state.prevailing
        (patternResult.bindings.toContext ++ ppBindings.toContext ++ context)
        body bodyTarget bodyFinal.supply bodyFinal.prevailing := by
      simpa only [List.append_assoc] using bodyRaw
    have bodyOrigin' : DemandCheckOrigin signature bodyRaw'
        patternResult.state.capabilityOrigins
        bodyFinal.capabilityOrigins := by
      simpa only [List.append_assoc] using bodyOrigin
    have bodyAudit' : Nonempty
        (DemandCheckTerminalAudit terminal.prevailing signature bodyOrigin') :=
      DemandCheckTerminalAudit.transportRawOrigin ⟨bodyAudit⟩
    rcases bodyAudit' with ⟨bodyAudit'⟩
    let armsOrigin := DDArmsOrigin.cons patternOrigin namesDistinct
      bodyOrigin' tailOrigin
    refine ⟨DDArms.cons patternRaw namesDistinct bodyRaw' tailRaw,
      armsOrigin, ⟨?_⟩⟩
    exact DDArmsTerminalAudit.cons (patternOrigin := patternOrigin)
      (disjoint := namesDistinct) bodyAudit' tailAudit
  case case98 =>
    rename_i fuel signature context selfEnv parent index initial final terminal
      resultEq bridge history
    subst final
    exact ⟨DemandChecks.nil, DemandChecksOrigin.nil,
      ⟨DemandChecksTerminalAudit.nil⟩⟩
  case case100 =>
    rename_i fuel signature context selfEnv parent index expression expressions
      expected expecteds initial middle headEq final terminal headIH tailIH
      tailEq bridge history
    have tailCertified := tailIH final terminal rfl bridge history
    have headHistory : middle.HistoryPrefix terminal :=
      (checkExprsFuel_historyPrefix tailEq).trans history
    have headCertified := headIH middle terminal rfl bridge headHistory
    rcases headCertified with ⟨headRaw, headOrigin, ⟨headAudit⟩⟩
    rcases tailCertified with ⟨tailRaw, tailOrigin, ⟨tailAudit⟩⟩
    exact ⟨DemandChecks.cons headRaw tailRaw,
      DemandChecksOrigin.cons headOrigin tailOrigin,
      ⟨DemandChecksTerminalAudit.cons headAudit tailAudit⟩⟩
  case case103 =>
    rename_i fuel signature context selfEnv parent index initial result terminal
      resultEq bridge history
    subst result
    exact ⟨[], DemandSynths.nil, rfl, DemandSynthsOrigin.nil,
      ⟨DemandSynthsTerminalAudit.nil⟩⟩
  case case106 =>
    rename_i fuel signature context selfEnv parent index expression expressions
      initial head headEq tail tailEq result terminal headIH tailIH resultEq
      bridge history
    subst result
    have tailCertified := tailIH tail terminal rfl bridge history
    have headHistory : head.state.HistoryPrefix terminal :=
      (inferExprsFuel_historyPrefix tailEq).trans history
    have headCertified := headIH head terminal rfl bridge headHistory
    rcases headCertified with
      ⟨headTarget, headRaw, headTargetEq, headOrigin, ⟨headAudit⟩⟩
    rcases tailCertified with
      ⟨tailTargets, tailRaw, tailTargetsEq, tailOrigin, ⟨tailAudit⟩⟩
    subst headTarget
    subst tailTargets
    exact ⟨_, DemandSynths.cons headRaw tailRaw, rfl,
      DemandSynthsOrigin.cons headOrigin tailOrigin,
      ⟨DemandSynthsTerminalAudit.cons headAudit tailAudit⟩⟩

/-- Public expression projection of terminal-audited mutual soundness. -/
theorem inferExprFuel_certifiedRunAt
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {initial : InferState} {result : ExprResult} {terminal : InferState}
    (success : inferExprFuel fuel signature context selfEnv path expression
      initial = some result)
    (bridge : Reconstruction.WBridgeWF signature terminal)
    (history : result.state.HistoryPrefix terminal) :
    DemandSynthCertifiedRun terminal.prevailing signature context expression
      initial result :=
  inferExprFuel_certifiedRunAtAux result terminal success bridge history

end Inference
end TypePM
