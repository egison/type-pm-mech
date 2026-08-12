import TypePM.DemandTypingInferenceSoundnessPatterns

/-!
# Matcher and match-all inference soundness slices

This module reconstructs exact-state demand-directed derivations for matcher
literals and `matchAll`.  Recursive traversals are supplied as induction
hypotheses, so these lemmas compose directly inside the enclosing mutual
soundness proof.
-/

namespace TypePM
namespace Inference

/-- Finalize a successful matcher traversal from its exact clause-list run. -/
theorem inferMatcherFuel_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clauses : List Clause}
    {initial : InferState} {result : ExprResult}
    (clausesSound : ∀ clausesResult : ClausesResult,
      inferClausesFuel fuel signature context selfEnv path 0 clauses
        (.var initial.supply.nextTy)
        (initial.freshTy
          (freshOrigin .matcherClause path "matcher-target")).2 =
          some clausesResult →
      DDClausesRun signature context clauses (.var initial.supply.nextTy)
        (initial.freshTy
          (freshOrigin .matcherClause path "matcher-target")).2 clausesResult)
    (success : inferMatcherFuel (fuel + 1) signature context selfEnv path
      clauses initial = some result) :
    DemandSynthRun signature context (.matcher clauses) initial result := by
  simp only [inferMatcherFuel] at success
  have freshTarget :
      (initial.freshTy
        (freshOrigin .matcherClause path "matcher-target")).1 =
          .var initial.supply.nextTy := rfl
  simp only [freshTarget] at success
  cases clausesEq : inferClausesFuel fuel signature context selfEnv path 0
      clauses (.var initial.supply.nextTy)
      (initial.freshTy
        (freshOrigin .matcherClause path "matcher-target")).2 with
  | none => simp [clausesEq] at success
  | some clausesResult =>
      simp only [clausesEq] at success
      let finalHoleLists := clausesResult.rawHoleLists.map fun holes =>
        holes.map
          (Dual.cap ∘ Dual.applySubst clausesResult.state.prevailing)
      have finalHoleListsEq : finalHoleLists =
          clausesResult.rawHoleLists.map fun holes =>
            (holes.map
              (Dual.applySubst clausesResult.state.prevailing)).map Dual.cap := by
        simp [finalHoleLists, List.map_map, Function.comp_def]
      rw [← finalHoleListsEq] at success
      cases collectedEq : collectClauseEvidence signature.toMatcherSig clauses
          finalHoleLists with
      | none => simp [collectedEq] at success
      | some evidence =>
          simp only [collectedEq] at success
          cases inferredEq : Shape.inferShape signature.observability evidence with
          | none => simp [inferredEq] at success
          | some capability =>
              simp only [inferredEq] at success
              split at success
              · rename_i checks
                simp only [Option.some.injEq] at success
                subst result
                rcases clausesSound clausesResult clausesEq with
                  ⟨clausesTarget, clausesRaw, clausesOrigin⟩
                clear clausesTarget
                simp only [Bool.and_eq_true] at checks
                have clauseCaps := checks.1.1.1.1
                have catchAll := checks.1.1.1.2
                have binders := checks.1.1.2
                have arms := checks.1.2
                have coverage := checks.2
                have collected :
                    collectClauseEvidence signature.toMatcherSig clauses
                        (terminalHoleCaps clausesResult.state.prevailing
                          clausesResult.rawHoleLists) = some evidence := by
                  simpa [terminalHoleCaps, finalHoleLists] using collectedEq
                have clauseCaps' : clauseCapsListCheck signature capability
                    clauses (terminalHoleCaps
                      clausesResult.state.prevailing
                      clausesResult.rawHoleLists) = true := by
                  simpa [terminalHoleCaps, finalHoleLists] using clauseCaps
                let rawDerived := DemandSynth.matcher clausesRaw collected
                  inferredEq clauseCaps' catchAll binders arms coverage
                let rawOrigin := DemandSynthOrigin.matcher clausesOrigin collected
                  inferredEq clauseCaps' catchAll binders arms coverage
                refine ⟨.matcher capability (.var initial.supply.nextTy),
                  ?_, rfl, ?_⟩
                · simpa using rawDerived
                · simpa [DDLedger.freezeMatcherProducer,
                    DDLedger.matcherProducerLeaves] using rawOrigin
              · simp_all

/-- The expression-level matcher branch only adds its syntax visit and result
event around the exact matcher traversal. -/
theorem inferExprFuel_matcher_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clauses : List Clause}
    {initial : InferState} {result : ExprResult}
    (matcherSound : ∀ matcherResult : ExprResult,
      inferMatcherFuel fuel signature context selfEnv path clauses
        (visit initial .exprMatcher path) = some matcherResult →
      DemandSynthRun signature context (.matcher clauses)
        (visit initial .exprMatcher path) matcherResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.matcher clauses) initial = some result) :
    DemandSynthRun signature context (.matcher clauses) initial result := by
  cases matcherEq : inferMatcherFuel fuel signature context selfEnv path clauses
      (visit initial .exprMatcher path) with
  | none => simp [inferExprFuel, matcherEq] at success
  | some matcherResult =>
      have resultEq : result = finishExpr (.matcher clauses) path
          matcherResult.target matcherResult.state := by
        simpa [inferExprFuel, matcherEq] using success.symm
      subst result
      rcases matcherSound matcherResult matcherEq with
        ⟨rawTarget, derived, targetEq, origin⟩
      change DemandSynth signature initial.supply initial.prevailing context
        (.matcher clauses) rawTarget matcherResult.state.supply
          matcherResult.state.prevailing at derived
      change DemandSynthOrigin signature derived initial.capabilityOrigins
        matcherResult.state.capabilityOrigins at origin
      exact ⟨rawTarget, derived, by simpa [finishExpr] using targetEq,
        by simpa [finishExpr] using origin⟩

/-- The `matchAll` branch composes target synthesis, pattern synthesis, target
alignment, matcher checking, and body synthesis in executable order. -/
theorem inferExprFuel_matchAll_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {target matcher : Expr}
    {pattern : Pattern} {body : Expr} {initial : InferState}
    {result : ExprResult}
    (targetSound : ∀ targetResult : ExprResult,
      inferExprFuel fuel signature context selfEnv (0 :: path) target
        (visit initial .exprMatchAll path) = some targetResult →
      DemandSynthRun signature context target (visit initial .exprMatchAll path)
        targetResult)
    (patternSound : ∀ (targetResult : ExprResult)
      (patternResult : PatternResult),
      inferPatternFuel fuel signature context [] [] selfEnv (2 :: path)
        pattern targetResult.state = some patternResult →
      DDPatternRun signature context [] [] pattern targetResult.state
        patternResult)
    (matcherSound : ∀ (targetResult : ExprResult)
      (patternResult : PatternResult) (aligned matcherFinal : InferState),
      checkExprFuel fuel signature context selfEnv (1 :: path) matcher
        (.slot patternResult.dual.cap targetResult.target) aligned =
          some matcherFinal →
      DemandCheckRun signature context matcher
        (.slot patternResult.dual.cap targetResult.target) aligned matcherFinal)
    (bodySound : ∀ (patternResult : PatternResult) (matcherFinal : InferState)
      (bodyResult : ExprResult),
      inferExprFuel fuel signature
        (patternResult.bindings.toContext ++ context)
        (selfEnv.eraseMany pattern.patVars) (3 :: path) body matcherFinal =
          some bodyResult →
      DemandSynthRun signature
        (patternResult.bindings.toContext ++ context) body matcherFinal
        bodyResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.matchAll target matcher pattern body) initial = some result) :
    DemandSynthRun signature context (.matchAll target matcher pattern body)
      initial result := by
  cases targetEq : inferExprFuel fuel signature context selfEnv (0 :: path)
      target (visit initial .exprMatchAll path) with
  | none => simp [inferExprFuel, targetEq] at success
  | some targetResult =>
      cases patternEq : inferPatternFuel fuel signature context [] [] selfEnv
          (2 :: path) pattern targetResult.state with
      | none => simp [inferExprFuel, targetEq, patternEq] at success
      | some patternResult =>
          cases alignedEq : alignTypes patternResult.state
              (freshOrigin .pattern (2 :: path) "match-target")
              patternResult.dual.target targetResult.target with
          | none =>
              simp [inferExprFuel, targetEq, patternEq, alignedEq] at success
          | some aligned =>
              cases matcherEq : checkExprFuel fuel signature context selfEnv
                  (1 :: path) matcher
                  (.slot patternResult.dual.cap targetResult.target) aligned with
              | none =>
                  simp [inferExprFuel, targetEq, patternEq, alignedEq,
                    matcherEq] at success
              | some matcherFinal =>
                  cases bodyEq : inferExprFuel fuel signature
                      (patternResult.bindings.toContext ++ context)
                      (selfEnv.eraseMany pattern.patVars) (3 :: path) body
                      matcherFinal with
                  | none =>
                      simp [inferExprFuel, targetEq, patternEq, alignedEq,
                        matcherEq, bodyEq] at success
                  | some bodyResult =>
                      have resultEq : result =
                          finishExpr (.matchAll target matcher pattern body) path
                            (Ty.listT bodyResult.target) bodyResult.state := by
                        simpa [inferExprFuel, targetEq, patternEq, alignedEq,
                          matcherEq, bodyEq] using success.symm
                      subst result
                      rcases targetSound targetResult targetEq with
                        ⟨targetTarget, targetRaw, targetTargetEq, targetOrigin⟩
                      rcases patternSound targetResult patternResult patternEq with
                        ⟨patternRaw, patternOrigin⟩
                      rcases alignTypes_ddAlignTypesRun alignedEq with
                        ⟨alignedSupply, alignedLedger, targetAligned⟩
                      have matcherRun := matcherSound targetResult patternResult
                        aligned matcherFinal matcherEq
                      unfold DemandCheckRun at matcherRun
                      rw [alignedSupply, alignedLedger] at matcherRun
                      rcases matcherRun with ⟨matcherRaw, matcherOrigin⟩
                      rcases bodySound patternResult matcherFinal bodyResult
                          bodyEq with
                        ⟨bodyTarget, bodyRaw, bodyTargetEq, bodyOrigin⟩
                      subst targetTarget
                      change DemandSynth signature initial.supply
                        initial.prevailing context target targetResult.target
                        targetResult.state.supply
                        targetResult.state.prevailing at targetRaw
                      change DemandSynthOrigin signature targetRaw
                        initial.capabilityOrigins
                        targetResult.state.capabilityOrigins at targetOrigin
                      refine ⟨Ty.listT bodyTarget,
                        DemandSynth.matchAll targetRaw patternRaw targetAligned.erase
                          matcherRaw bodyRaw, ?_, ?_⟩
                      · simp [finishExpr, bodyTargetEq]
                      · simpa [finishExpr] using
                          DemandSynthOrigin.matchAll targetOrigin patternOrigin
                            targetAligned matcherOrigin bodyOrigin

end Inference
end TypePM
