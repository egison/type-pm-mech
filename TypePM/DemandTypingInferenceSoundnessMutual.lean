import TypePM.DemandTypingInferenceSoundnessFixMatcher
import TypePM.DemandTypingInferenceSoundnessLet
import TypePM.DemandTypingInferenceSoundnessMatcher

/-!
# Mutual executable-to-demand-directed soundness

This module closes the raw, exact-state soundness argument for the ten
mutually recursive executable traversal families.  Each induction motive
records the corresponding `demand-directed*Run` package, so recursive calls can be fed
directly to the constructor-specific reconstruction slices.
-/

namespace TypePM
namespace Inference

private theorem soundOfSome
    {α : Type} {result : α} {run : α → Prop} {operation : Option α}
    (success : operation = some result)
    (sound : ∀ candidate, result = candidate → run candidate) :
    ∀ candidate, operation = some candidate → run candidate := by
  intro candidate candidateSuccess
  have equality : result = candidate :=
    Option.some.inj (success.symm.trans candidateSuccess)
  exact sound candidate equality

mutual

/-- Successful primitive-pattern traversal reconstructs its exact demand-directed run. -/
theorem inferPPatFuel_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : PPat} {expected : Ty} {initial : InferState}
    {result : PPatResult}
    (success : inferPPatFuel fuel signature path pattern expected initial =
      some result) :
    DDPPatRun signature pattern expected initial result := by
  cases fuel with
  | zero => simp [inferPPatFuel] at success
  | succ fuel =>
      cases pattern with
      | hole => exact inferPPatFuel_hole_ddPPatRun success
      | wild => exact inferPPatFuel_wild_ddPPatRun success
      | pval name => exact inferPPatFuel_pval_ddPPatRun success
      | ctor name patterns =>
          exact inferPPatFuel_ctor_ddPPatRun
            (fun _ _ _ childrenSuccess =>
              inferPPatsFuel_ddPPatsRun childrenSuccess) success
      | tuple patterns =>
          exact inferPPatFuel_tuple_ddPPatRun
            (fun _ _ _ _ _ childrenSuccess =>
              inferPPatsFuel_ddPPatsRun childrenSuccess) success

/-- Successful primitive-pattern-list traversal reconstructs its exact demand-directed
run. -/
theorem inferPPatsFuel_ddPPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List PPat} {targets : List Ty} {initial : InferState}
    {result : PPatsResult}
    (success : inferPPatsFuel fuel signature parent index patterns targets
      initial = some result) :
    DDPPatsRun signature patterns targets initial result := by
  cases fuel with
  | zero => simp [inferPPatsFuel] at success
  | succ fuel =>
      cases patterns with
      | nil =>
          cases targets with
          | nil => exact inferPPatsFuel_nil_ddPPatsRun success
          | cons target targets => simp [inferPPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferPPatsFuel] at success
          | cons target targets =>
              exact inferPPatsFuel_cons_ddPPatsRun
                (fun head headSuccess => inferPPatFuel_ddPPatRun headSuccess)
                (fun _ tail tailSuccess =>
                  inferPPatsFuel_ddPPatsRun tailSuccess) success

/-- Successful data-pattern traversal reconstructs its exact demand-directed run. -/
theorem inferDPatFuel_ddDPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {pattern : DPat} {expected : Ty} {initial : InferState}
    {result : DPatResult}
    (success : inferDPatFuel fuel signature path pattern expected initial =
      some result) :
    DDDPatRun signature pattern expected initial result := by
  cases fuel with
  | zero => simp [inferDPatFuel] at success
  | succ fuel =>
      cases pattern with
      | var name => exact inferDPatFuel_var_ddDPatRun success
      | wild => exact inferDPatFuel_wild_ddDPatRun success
      | ctor name patterns =>
          exact inferDPatFuel_ctor_ddDPatRun
            (fun _ _ _ childrenSuccess =>
              inferDPatsFuel_ddDPatsRun childrenSuccess) success
      | tuple patterns =>
          exact inferDPatFuel_tuple_ddDPatRun
            (fun _ _ _ _ _ childrenSuccess =>
              inferDPatsFuel_ddDPatsRun childrenSuccess) success

/-- Successful data-pattern-list traversal reconstructs its exact demand-directed run. -/
theorem inferDPatsFuel_ddDPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List DPat} {targets : List Ty} {initial : InferState}
    {result : DPatsResult}
    (success : inferDPatsFuel fuel signature parent index patterns targets
      initial = some result) :
    DDDPatsRun signature patterns targets initial result := by
  cases fuel with
  | zero => simp [inferDPatsFuel] at success
  | succ fuel =>
      cases patterns with
      | nil =>
          cases targets with
          | nil => exact inferDPatsFuel_nil_ddDPatsRun success
          | cons target targets => simp [inferDPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferDPatsFuel] at success
          | cons target targets =>
              exact inferDPatsFuel_cons_ddDPatsRun
                (fun head headSuccess => inferDPatFuel_ddDPatRun headSuccess)
                (fun _ tail tailSuccess =>
                  inferDPatsFuel_ddDPatsRun tailSuccess) success

end

set_option maxHeartbeats 4000000 in
/-- Every successful expression traversal reconstructs its exact-state
demand-directed synthesis run. -/
theorem inferExprFuel_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel fuel signature context selfEnv path expression
      initial = some result) :
    DemandSynthRun signature context expression initial result := by
  revert result
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression initial =>
      ∀ result,
        inferExprFuel fuel signature context selfEnv path expression initial =
            some result →
        DemandSynthRun signature context expression initial result)
    (motive2 := fun fuel signature context selfEnv path expression expected
        initial =>
      ∀ final,
        checkExprFuel fuel signature context selfEnv path expression expected
            initial = some final →
        DemandCheckRun signature context expression expected initial final)
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern initial =>
      ∀ result,
        inferPatternFuel fuel signature context parameters bindings selfEnv
            path pattern initial = some result →
        DDPatternRun signature context parameters bindings pattern initial
          result)
    (motive4 := fun fuel signature context parameters bindings selfEnv parent
        index patterns initial =>
      ∀ result,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            parent index patterns initial = some result →
        DDPatternsRun signature context parameters bindings patterns initial
          result)
    (motive5 := fun fuel signature context selfEnv path clauses initial =>
      ∀ result,
        inferMatcherFuel fuel signature context selfEnv path clauses initial =
            some result →
        DemandSynthRun signature context (.matcher clauses) initial result)
    (motive6 := fun fuel signature context selfEnv parent index clauses target
        initial =>
      ∀ result,
        inferClausesFuel fuel signature context selfEnv parent index clauses
            target initial = some result →
        DDClausesRun signature context clauses target initial result)
    (motive7 := fun fuel signature context selfEnv path clause target initial =>
      ∀ result,
        inferClauseFuel fuel signature context selfEnv path clause target
            initial = some result →
        DDClauseRun signature context clause target initial result)
    (motive8 := fun fuel signature context selfEnv bindings parent index arms
        target bodyTarget initial =>
      ∀ final,
        checkArmsFuel fuel signature context selfEnv bindings parent index arms
            target bodyTarget initial = some final →
        DDArmsRun signature context bindings arms target bodyTarget initial
          final)
    (motive9 := fun fuel signature context selfEnv parent index expressions
        expecteds initial =>
      ∀ final,
        checkExprsFuel fuel signature context selfEnv parent index expressions
            expecteds initial = some final →
        DemandChecksRun signature context expressions expecteds initial final)
    (motive10 := fun fuel signature context selfEnv parent index expressions
        initial =>
      ∀ result,
        inferExprsFuel fuel signature context selfEnv parent index expressions
            initial = some result →
        DemandSynthsRun signature context expressions initial result)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferExprFuel, checkExprFuel, inferPatternFuel, inferPatternsFuel,
      inferMatcherFuel, inferClausesFuel, inferClauseFuel, checkArmsFuel,
      checkExprsFuel, inferExprsFuel, Option.some.injEq]
  all_goals try contradiction
  case case3 =>
    rename_i fuel signature context selfEnv path initial name scheme target
      instState visited normalizedContext result lookup instEq resultEq
    apply inferExprFuel_var_ddSynthRun (fuel := fuel) (selfEnv := selfEnv)
      (path := path)
    subst result
    simp [inferExprFuel, lookup, instEq]
  case case5 =>
    rename_i fuel signature context selfEnv path initial name body domain
      bodyInitial bodyResult bodyEq visited result freshEq bodyIH resultEq
    subst result
    have bodyRun : DemandSynthRun signature
        ((name, Scheme.mono (lambdaDomain initial path)) :: context) body
        (lambdaEntryState initial path) bodyResult := by
      simpa [lambdaDomain, lambdaEntryState, freshEq] using
        (bodyIH bodyResult rfl)
    simpa [lambdaDomain, freshEq] using DemandSynthRun.lam bodyRun
  case case9 =>
    rename_i fuel signature context selfEnv path initial self argument body gate
      domain codomain placeholderState placeholder bodyInitial shadowed
      bodySelfEnv bodyContext bodyResult aligned visited result bodyEq alignEq
      placeholderEq bodyIH resultEq
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
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
      exact DemandSynthRun.fix distinct direct nonMatcher
        (bodyIH bodyResult rfl) (alignTypes_ddAlignTypesRun alignEq)
    · cases body <;>
        simp [NonMatcherBody, matcherProducingRoot] at nonMatcher
      rename_i clauses
      rcases buildFixPlaceholder_matcher_ddRun placeholderEq with
        ⟨placeholderPure, placeholderPrevailing, placeholderLedger⟩
      apply DemandSynthRun.fixMatcher distinct direct placeholderPure
      · simpa [bodyInitial, visited, InferState.recordEvent] using
          placeholderPrevailing
      · simpa [bodyInitial, visited, InferState.recordEvent] using
          placeholderLedger
      · exact bodyIH bodyResult rfl
      · exact alignTypes_ddAlignTypesRun alignEq
  case case15 =>
    rename_i fuel signature context selfEnv path initial function argument
      functionResult domain domainState domainEq resultTarget resultState
      resultFreshEq functionAligned functionAlignEq argumentResult argumentEq
      argumentFinal argumentAlignEq visited result functionEq functionIH
      argumentIH resultEq
    subst result
    have argumentCheck : DemandCheckRun signature context argument
        (applicationDomain functionResult path) functionAligned
        argumentFinal :=
      DemandSynthRun.check (argumentIH argumentResult rfl)
        (by
          simpa [applicationDomain, domainEq] using
            alignExprResultAtExpected_ddAlignRun argumentAlignEq)
    have functionAlignRun : DemandAlignTypesRun functionResult.target
        (.fn (applicationDomain functionResult path)
          (applicationResultTarget functionResult path))
        (applicationFreshState functionResult path) functionAligned := by
      simpa [applicationDomain, applicationResultTarget,
        applicationFreshState, domainEq, resultFreshEq] using
        alignTypes_ddAlignTypesRun functionAlignEq
    have run := DemandSynthRun.app (functionIH functionResult rfl)
      functionAlignRun argumentCheck
    have resultTargetEq : applicationResultTarget functionResult path =
        resultTarget := by
      have domainStateEq :
          (functionResult.state.freshTy
            (freshOrigin .expression path "application-domain")).2 =
              domainState := congrArg Prod.snd domainEq
      rw [applicationResultTarget, domainStateEq]
      exact congrArg Prod.fst resultFreshEq
    rw [resultTargetEq] at run
    exact run
  case case16 =>
    rename_i fuel signature context selfEnv path initial value result resultEq
    subst result
    exact inferExprFuel_lit_ddSynthRun (fuel := fuel) (selfEnv := selfEnv)
      (path := path) (by simp [inferExprFuel])
  case case18 =>
    rename_i fuel signature context selfEnv path initial expressions children
      visited result childrenEq childrenIH resultEq
    subst result
    exact DemandSynthRun.tuple (childrenIH children rfl)
  case case21 =>
    rename_i fuel signature context selfEnv path initial name expressions scheme
      lookup expecteds target instState final childrenEq visited result instEq
      childrenIH resultEq
    subst result
    have childrenRun := childrenIH final rfl
    simp only [instantiateCtorInState] at instEq
    cases instEq
    exact DemandSynthRun.ctor lookup childrenRun
  case case24 =>
    rename_i fuel signature context selfEnv path initial op expressions scheme
      lookup expecteds target instState final childrenEq visited result instEq
      childrenIH resultEq
    subst result
    have childrenRun := childrenIH final rfl
    simp only [instantiateCtorInState] at instEq
    cases instEq
    exact DemandSynthRun.prim lookup childrenRun
  case case27 =>
    rename_i fuel signature context selfEnv path initial name value body
      valueResult normalizedContext normalizedValue scheme bodyInitial bodyResult
      visited result bodyEq valueEq valueIH bodyIH resultEq
    subst result
    exact DemandSynthRun.letE (valueIH valueResult rfl)
      (bodyIH bodyResult rfl)
  case case28 =>
    rename_i fuel signature context selfEnv path initial target freshState
      visited result freshEq resultEq
    subst result
    exact inferExprFuel_something_ddSynthRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
      (by simp [inferExprFuel, freshEq])
  case case30 =>
    rename_i fuel signature context selfEnv path initial clauses matcherResult
      visited result matcherEq matcherIH resultEq
    subst result
    apply inferExprFuel_matcher_ddSynthRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    · exact soundOfSome matcherEq matcherIH
    · simp [inferExprFuel, matcherEq]
  case case36 =>
    rename_i fuel signature context selfEnv path initial target matcher pattern
      body targetResult patternResult patternEq aligned targetAlignEq
      matcherFinal matcherEq bodyContext bodyEnv bodyResult visited result
      bodyEq targetEq targetIH patternIH matcherIH bodyIH resultEq
    subst result
    rcases targetIH targetResult rfl with
      ⟨targetTarget, targetRaw, targetTargetEq, targetOrigin⟩
    rcases patternIH patternResult rfl with ⟨patternRaw, patternOrigin⟩
    rcases alignTypes_ddAlignTypesRun targetAlignEq with
      ⟨alignedSupply, alignedLedger, targetAligned⟩
    have matcherRun := matcherIH matcherFinal rfl
    unfold DemandCheckRun at matcherRun
    rw [alignedSupply, alignedLedger] at matcherRun
    rcases matcherRun with ⟨matcherRaw, matcherOrigin⟩
    rcases bodyIH bodyResult rfl with
      ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin⟩
    subst targetTarget
    change DemandSynth signature initial.supply initial.prevailing context target
      targetResult.target targetResult.state.supply
        targetResult.state.prevailing at targetRaw
    change DemandSynthOrigin signature targetRaw initial.capabilityOrigins
      targetResult.state.capabilityOrigins at targetOrigin
    refine ⟨Ty.listT bodyTarget,
      DemandSynth.matchAll targetRaw patternRaw targetAligned.erase matcherRaw
        bodyRaw, ?_, ?_⟩
    · simp [finishExpr, bodyTargetEq]
    · simpa [finishExpr] using
        DemandSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
          matcherOrigin bodyOrigin
  case case39 =>
    rename_i fuel signature context selfEnv path expression expected initial
      synthesized inferEq final synthIH alignEq
    exact DemandSynthRun.check (synthIH synthesized rfl)
      (alignExprResultAtExpected_ddAlignRun alignEq)
  case case42 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name absent capability capState capEq target targetState targetEq result
      resultEq
    have freshName : name ∉ bindings.names := by
      simpa using absent
    apply inferPatternFuel_pvar_ddPatternRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, capEq, targetEq, freshName] using resultEq
  case case43 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      capability capState capEq target targetState targetEq result resultEq
    apply inferPatternFuel_wild_ddPatternRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, capEq, targetEq] using congrArg some resultEq
  case case45 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      expression expressionResult expressionEq capability capState capEq
      result expressionIH resultEq
    apply inferPatternFuel_pval_ddPatternRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    · exact soundOfSome expressionEq expressionIH
    · simpa [inferPatternFuel, expressionEq, capEq] using
        congrArg some resultEq
  case case47 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name dual lookup result resultEq
    apply inferPatternFuel_embed_ddPatternRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    simpa [inferPatternFuel, lookup] using congrArg some resultEq
  case case49 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      patterns children childrenEq result childrenIH resultEq
    apply inferPatternFuel_ptuple_ddPatternRun (fuel := fuel)
      (selfEnv := selfEnv) (path := path)
    · exact soundOfSome childrenEq childrenIH
    · simpa [inferPatternFuel, childrenEq] using congrArg some resultEq
  case case54 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name patterns entry lookup expecteds target instState instEq children
      childrenEq targetsFinal targetsEq childCaps capability solvedState
      resolvedChildren resolvedCapability result capabilityEq compatible
      childrenIH resultEq
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    simp only [instantiateCtorInState] at instEq
    cases instEq
    rcases childrenIH children rfl with ⟨childrenRaw, childrenOrigin⟩
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
    simp only [DDPatternRun, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins,
      InferState.freezeCapabilityExport_supply,
      InferState.freezeCapabilityExport_prevailing,
      InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
    exact ⟨DDPattern.pctor lookup childrenRaw targetsAligned.erase capRaw'
        compatible,
      DDPatternOrigin.pctor lookup childrenOrigin targetsAligned capOrigin'
        compatible⟩
  case case59 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      left right leftResult leftEq rightResult rightEq final alignEq result
      leftIH rightIH resultEq
    subst result
    rcases leftIH leftResult rfl with ⟨leftRaw, leftOrigin⟩
    rcases rightIH rightResult rfl with ⟨rightRaw, rightOrigin⟩
    rcases alignDuals_ddAlignDualRun alignEq with
      ⟨supplyEq, ledgerEq, aligned⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at leftRaw leftOrigin
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.pand left right)
        leftResult.dual rightResult.bindings final.supply final.prevailing,
      DDPatternOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins
    rw [supplyEq, ledgerEq]
    exact ⟨DDPattern.pand leftRaw rightRaw aligned.erase,
      DDPatternOrigin.pand leftOrigin rightOrigin aligned⟩
  case case64 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      left right leftResult leftEq rightResult rightEq dualFinal dualEq final
      bindingsEq result leftIH rightIH resultEq
    subst result
    rcases leftIH leftResult rfl with ⟨leftRaw, leftOrigin⟩
    rcases rightIH rightResult rfl with ⟨rightRaw, rightOrigin⟩
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
      DDPatternOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins
    rw [finalSupply, finalLedger]
    exact ⟨DDPattern.por leftRaw rightRaw dualAligned.erase
        bindingsAligned.erase,
      DDPatternOrigin.por leftOrigin rightOrigin dualAligned bindingsAligned⟩
  case case68 =>
    rename_i fuel signature context parameters bindings selfEnv path initial
      name patterns scheme lookup normalizedContext normalizedParameters
      normalizedBindings expectedArgs resultDual instState children final result
      instEq childrenEq alignEq childrenIH resultEq
    subst result
    simp only [instantiateDualInState] at instEq
    cases instEq
    rcases childrenIH children rfl with ⟨childrenRaw, childrenOrigin⟩
    rcases alignDualLists_ddAlignDualListRun alignEq with
      ⟨supplyEq, ledgerEq, aligned⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at childrenRaw childrenOrigin
    change ∃ derived : DDPattern signature initial.supply
        initial.prevailing context parameters bindings (.papp name patterns)
        (InferenceBase.instantiateDualScheme initial.supply scheme).value.2
        children.bindings final.supply final.prevailing,
      DDPatternOrigin signature derived initial.capabilityOrigins
        final.capabilityOrigins
    rw [supplyEq, ledgerEq]
    exact ⟨DDPattern.papp lookup childrenRaw aligned.erase,
      DDPatternOrigin.papp lookup childrenOrigin aligned⟩
  case case70 =>
    rename_i fuel signature context parameters bindings selfEnv path index
      initial result resultEq
    subst result
    exact DDPatternsRun.nil signature context parameters bindings initial
  case case73 =>
    rename_i fuel signature context parameters bindings selfEnv parent index
      pattern patterns initial head headEq tail tailEq result headIH tailIH
      resultEq
    subst result
    exact DDPatternsRun.cons (headIH head rfl) (tailIH tail rfl)
  case case78 =>
    rename_i fuel signature context selfEnv path clauses initial target
      freshState freshEq clausesResult clausesEq finalHoleLists evidences
      capability finalTarget result collectEq shapeEq checks clausesIH resultEq
    simp only [InferState.freshTy, InferenceBase.freshTyMeta] at freshEq
    cases freshEq
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    rcases clausesIH clausesResult rfl with
      ⟨clausesTarget, clausesRaw, clausesOrigin⟩
    clear clausesTarget
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
    refine ⟨.matcher capability (.var initial.supply.nextTy), ?_, rfl, ?_⟩
    · exact rawDerived
    · simpa [DDLedger.freezeMatcherProducerExcept,
        DDLedger.matcherProducerLeavesExcept,
        borrowedMatcherCapVars] using rawOrigin
  case case81 =>
    rename_i fuel signature context selfEnv path index target initial result
      resultEq
    subst result
    exact inferClausesFuel_nil_ddClausesRun (fuel := fuel)
      (selfEnv := selfEnv) (parent := path) (index := index)
      (by simp [inferClausesFuel])
  case case84 =>
    rename_i fuel signature context selfEnv parent index clause clauses target
      initial head headEq tail tailEq result headIH tailIH resultEq
    subst result
    rcases headIH head rfl with ⟨headTargetEq, headRaw, headOrigin⟩
    rcases tailIH tail rfl with ⟨tailTargetEq, tailRaw, tailOrigin⟩
    clear headTargetEq tailTargetEq
    exact ⟨rfl, DDClauses.cons headRaw tailRaw,
      DDClausesOrigin.cons headOrigin tailOrigin⟩
  case case90 =>
    rename_i fuel signature context selfEnv path pp next arms target initial
      ppResult ppEq nextMatchers decompose slotTargets nextFinal bodyTarget
      armsFinal result nextEq armsEq nextIH armsIH resultEq
    subst result
    rcases inferPPatFuel_ddPPatRun ppEq with
      ⟨ppTargetEq, ppRaw, ppOrigin⟩
    rcases nextIH nextFinal rfl with ⟨nextRaw, nextOrigin⟩
    rcases armsIH armsFinal rfl with ⟨armsRaw, armsOrigin⟩
    simp only [visit, InferState.recordEvent_supply,
      InferState.prevailing_recordEvent,
      InferState.recordEvent_capabilityOrigins] at ppRaw ppOrigin
    exact ⟨rfl, DDClause.mk ppRaw decompose nextRaw armsRaw,
      DDClauseOrigin.mk ppOrigin decompose nextOrigin armsOrigin⟩
  case case92 =>
    rename_i fuel signature context selfEnv bindings parent index target
      bodyTarget initial final resultEq
    subst final
    exact checkArmsFuel_nil_ddArmsRun (fuel := fuel) (selfEnv := selfEnv)
      (parent := parent) (index := index) (by simp [checkArmsFuel])
  case case95 =>
    rename_i fuel signature context selfEnv ppBindings parent index pattern
      body arms target bodyTarget initial patternResult patternEq distinct
      bodyContext bodyEnv bodyFinal final bodyEq bodyIH tailIH resultEq
    simp only [if_pos trivial] at resultEq
    rcases inferDPatFuel_ddDPatRun patternEq with
      ⟨patternTargetEq, patternRaw, patternOrigin⟩
    rcases bodyIH bodyFinal rfl with ⟨bodyRaw, bodyOrigin⟩
    rcases tailIH final resultEq with ⟨tailRaw, tailOrigin⟩
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
    exact ⟨DDArms.cons patternRaw namesDistinct bodyRaw' tailRaw,
      DDArmsOrigin.cons patternOrigin namesDistinct bodyOrigin' tailOrigin⟩
  case case98 =>
    rename_i fuel signature context selfEnv parent index initial final resultEq
    subst final
    exact DemandChecksRun.nil signature context initial
  case case100 =>
    rename_i fuel signature context selfEnv parent index expression expressions
      expected expecteds initial middle headEq final headIH tailIH tailEq
    exact DemandChecksRun.cons (headIH middle rfl) (tailIH final rfl)
  case case103 =>
    rename_i fuel signature context selfEnv parent index initial result resultEq
    subst result
    exact DemandSynthsRun.nil signature context initial
  case case106 =>
    rename_i fuel signature context selfEnv parent index expression expressions
      initial head headEq tail tailEq result headIH tailIH resultEq
    subst result
    exact DemandSynthsRun.cons (headIH head rfl) (tailIH tail rfl)

/-! ## Standalone projections of the mutual theorem -/

/-- Standalone checking projection of raw mutual soundness. -/
theorem checkExprFuel_ddCheckRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expression : Expr}
    {expected : Ty} {initial final : InferState}
    (success : checkExprFuel fuel signature context selfEnv path expression
      expected initial = some final) :
    DemandCheckRun signature context expression expected initial final := by
  cases fuel with
  | zero => simp [checkExprFuel] at success
  | succ fuel =>
      cases inferEq : inferExprFuel fuel signature context selfEnv path
          expression initial with
      | none => simp [checkExprFuel, inferEq] at success
      | some synthesized =>
          have alignEq : alignExprResultAtExpected path synthesized expected =
              some final := by
            simpa [checkExprFuel, inferEq] using success
          exact DemandSynthRun.check (inferExprFuel_ddSynthRun inferEq)
            (alignExprResultAtExpected_ddAlignRun alignEq)

mutual

/-- Standalone user-pattern projection of raw mutual soundness. -/
theorem inferPatternFuel_ddPatternRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {pattern : Pattern} {initial : InferState}
    {result : PatternResult}
    (success : inferPatternFuel fuel signature context parameters bindings
      selfEnv path pattern initial = some result) :
    DDPatternRun signature context parameters bindings pattern initial
      result := by
  cases fuel with
  | zero => simp [inferPatternFuel] at success
  | succ fuel =>
      cases pattern with
      | pvar name => exact inferPatternFuel_pvar_ddPatternRun success
      | wild => exact inferPatternFuel_wild_ddPatternRun success
      | pval expression =>
          exact inferPatternFuel_pval_ddPatternRun
            (fun expressionResult expressionSuccess =>
              inferExprFuel_ddSynthRun expressionSuccess) success
      | embed name => exact inferPatternFuel_embed_ddPatternRun success
      | ptuple patterns =>
          exact inferPatternFuel_ptuple_ddPatternRun
            (fun children childrenSuccess =>
              inferPatternsFuel_ddPatternsRun_mutual childrenSuccess) success
      | pctor name patterns =>
          exact inferPatternFuel_pctor_ddPatternRun
            (fun _ children childrenSuccess =>
              inferPatternsFuel_ddPatternsRun_mutual childrenSuccess) success
      | pand left right =>
          exact inferPatternFuel_pand_ddPatternRun
            (fun leftResult leftSuccess =>
              inferPatternFuel_ddPatternRun_mutual leftSuccess)
            (fun _ rightResult rightSuccess =>
              inferPatternFuel_ddPatternRun_mutual rightSuccess) success
      | por left right =>
          exact inferPatternFuel_por_ddPatternRun
            (fun leftResult leftSuccess =>
              inferPatternFuel_ddPatternRun_mutual leftSuccess)
            (fun _ rightResult rightSuccess =>
              inferPatternFuel_ddPatternRun_mutual rightSuccess) success
      | papp name patterns =>
          exact inferPatternFuel_papp_ddPatternRun
            (fun _ children childrenSuccess =>
              inferPatternsFuel_ddPatternsRun_mutual childrenSuccess) success

/-- Standalone user-pattern-list projection of raw mutual soundness. -/
theorem inferPatternsFuel_ddPatternsRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {patterns : List Pattern}
    {initial : InferState} {result : PatternsResult}
    (success : inferPatternsFuel fuel signature context parameters bindings
      selfEnv parent index patterns initial = some result) :
    DDPatternsRun signature context parameters bindings patterns initial
      result := by
  cases fuel with
  | zero => simp [inferPatternsFuel] at success
  | succ fuel =>
      cases patterns with
      | nil => exact inferPatternsFuel_nil_ddPatternsRun success
      | cons pattern patterns =>
          exact inferPatternsFuel_cons_ddPatternsRun
            (fun head headSuccess =>
              inferPatternFuel_ddPatternRun_mutual headSuccess)
            (fun _ tail tailSuccess =>
              inferPatternsFuel_ddPatternsRun_mutual tailSuccess) success

end


private theorem checkExprsFuel_ddChecksRun_pre
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {expecteds : List Ty}
    {initial final : InferState}
    (success : checkExprsFuel fuel signature context selfEnv parent index
      expressions expecteds initial = some final) :
    DemandChecksRun signature context expressions expecteds initial final := by
  induction fuel generalizing index expressions expecteds initial with
  | zero => simp [checkExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          cases expecteds with
          | nil => exact checkExprsFuel_nil_ddChecksRun success
          | cons expected expecteds => simp [checkExprsFuel] at success
      | cons expression expressions =>
          cases expecteds with
          | nil => simp [checkExprsFuel] at success
          | cons expected expecteds =>
              cases headEq : checkExprFuel fuel signature context selfEnv
                  (index :: parent) expression expected initial with
              | none => simp [checkExprsFuel, headEq] at success
              | some middle =>
                  have tailEq : checkExprsFuel fuel signature context selfEnv
                      parent (index + 1) expressions expecteds middle =
                        some final := by
                    simpa [checkExprsFuel, headEq] using success
                  exact DemandChecksRun.cons
                    (checkExprFuel_ddCheckRun_mutual headEq)
                    (induction tailEq)


mutual

/-- Standalone matcher projection of raw mutual soundness. -/
theorem inferMatcherFuel_ddSynthRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clauses : List Clause}
    {initial : InferState} {result : ExprResult}
    (success : inferMatcherFuel fuel signature context selfEnv path clauses
      initial = some result) :
    DemandSynthRun signature context (.matcher clauses) initial result := by
  cases fuel with
  | zero => simp [inferMatcherFuel] at success
  | succ fuel =>
      exact inferMatcherFuel_ddSynthRun
        (fun clausesResult clausesSuccess =>
          inferClausesFuel_ddClausesRun_mutual clausesSuccess) success

/-- Standalone clause-list projection of raw mutual soundness. -/
theorem inferClausesFuel_ddClausesRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {clauses : List Clause} {target : Ty} {initial : InferState}
    {result : ClausesResult}
    (success : inferClausesFuel fuel signature context selfEnv parent index
      clauses target initial = some result) :
    DDClausesRun signature context clauses target initial result := by
  cases fuel with
  | zero => simp [inferClausesFuel] at success
  | succ fuel =>
      cases clauses with
      | nil => exact inferClausesFuel_nil_ddClausesRun success
      | cons clause clauses =>
          exact inferClausesFuel_cons_ddClausesRun
            (fun head headSuccess =>
              inferClauseFuel_ddClauseRun_mutual headSuccess)
            (fun _ tail tailSuccess =>
              inferClausesFuel_ddClausesRun_mutual tailSuccess) success

/-- Standalone clause projection of raw mutual soundness. -/
theorem inferClauseFuel_ddClauseRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clause : Clause}
    {target : Ty} {initial : InferState} {result : ClauseResult}
    (success : inferClauseFuel fuel signature context selfEnv path clause
      target initial = some result) :
    DDClauseRun signature context clause target initial result := by
  cases fuel with
  | zero => simp [inferClauseFuel] at success
  | succ fuel =>
      cases clause with
      | mk pp next arms =>
          exact inferClauseFuel_ddClauseRun
            (fun ppResult ppSuccess => inferPPatFuel_ddPPatRun ppSuccess)
            (fun _ _ nextFinal nextSuccess =>
              checkExprsFuel_ddChecksRun_pre nextSuccess)
            (fun _ _ armsFinal armsSuccess =>
              checkArmsFuel_ddArmsRun_mutual armsSuccess) success

/-- Standalone arm-list projection of raw mutual soundness. -/
theorem checkArmsFuel_ddArmsRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {bindings : MonoCtx} {parent : SyntaxPath}
    {index : Nat} {arms : List Arm} {target bodyTarget : Ty}
    {initial final : InferState}
    (success : checkArmsFuel fuel signature context selfEnv bindings parent
      index arms target bodyTarget initial = some final) :
    DDArmsRun signature context bindings arms target bodyTarget initial
      final := by
  cases fuel with
  | zero => simp [checkArmsFuel] at success
  | succ fuel =>
      cases arms with
      | nil => exact checkArmsFuel_nil_ddArmsRun success
      | cons arm arms =>
          cases arm with
          | mk pattern body =>
              exact checkArmsFuel_cons_ddArmsRun
                (fun patternResult patternSuccess =>
                  inferDPatFuel_ddDPatRun patternSuccess)
                (fun _ bodyFinal bodySuccess =>
                  checkExprFuel_ddCheckRun_mutual bodySuccess)
                (fun _ tailFinal tailSuccess =>
                  checkArmsFuel_ddArmsRun_mutual tailSuccess) success

end


/-- Standalone checking-list projection of raw mutual soundness. -/
theorem checkExprsFuel_ddChecksRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {expecteds : List Ty}
    {initial final : InferState}
    (success : checkExprsFuel fuel signature context selfEnv parent index
      expressions expecteds initial = some final) :
    DemandChecksRun signature context expressions expecteds initial final :=
  checkExprsFuel_ddChecksRun_pre success

/-- Standalone synthesis-list projection of raw mutual soundness. -/
theorem inferExprsFuel_ddSynthsRun_mutual
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {initial : InferState} {result : ExprsResult}
    (success : inferExprsFuel fuel signature context selfEnv parent index
      expressions initial = some result) :
    DemandSynthsRun signature context expressions initial result := by
  induction fuel generalizing index expressions initial result with
  | zero => simp [inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil => exact inferExprsFuel_nil_ddSynthsRun success
      | cons expression expressions =>
          exact inferExprsFuel_cons_ddSynthsRun
            (fun head headSuccess => inferExprFuel_ddSynthRun headSuccess)
            (fun _ tail tailSuccess => induction tailSuccess) success

end Inference
end TypePM
