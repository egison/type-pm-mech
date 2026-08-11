import TypePM.CertifiedInference

/-!
# Algorithm W state-threading regressions

These equations pin the three call boundaries at which the prevailing
substitution is easy to apply twice or the current inference state is easy to
drop.  Each theorem unfolds the executable checker itself, so changing one of
those call boundaries invalidates the corresponding proof.
-/

namespace TypePM
namespace Inference

/-- Pattern-constructor field alignment starts from the state returned by the
entire child traversal. -/
theorem inferPatternFuel_pctor_threads_child_state
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {patterns : List Pattern}
    {state : InferState}
    {entry : PatternCtorScheme signature.observability}
    {expectedTargets : List Ty} {resultTarget : Ty}
    {instantiatedState : InferState} {results : PatternsResult}
    {alignedState : InferState} {capability : Cap} {finalState : InferState}
    (lookup : signature.findPatternCtor name = some entry)
    (instantiated : instantiateCtorInState state entry.scheme =
      ((expectedTargets, resultTarget), instantiatedState))
    (children : inferPatternsFuel fuel signature context parameters bindings
      selfEnv path 0 patterns (visit instantiatedState .patternCtor path) =
        some results)
    (aligned : alignPatternTargets results.state
      (freshOrigin .pattern path "pattern-constructor-fields")
      results.duals expectedTargets = some alignedState)
    (solved : solvePatternCtorCapability signature entry
      (freshOrigin .pattern path "pattern-constructor-capability")
      (results.duals.map Dual.cap) alignedState =
        some (capability, finalState))
    (compatible : capCompatibleCheck entry
      ((results.duals.map Dual.cap).map fun child =>
        child.apply finalState.prevailing.cap)
      (capability.apply finalState.prevailing.cap) = true) :
    inferPatternFuel (fuel + 1) signature context parameters bindings selfEnv
      path (.pctor name patterns) state =
        some
          ⟨⟨capability, resultTarget⟩, results.bindings,
            ((finalState.freezeCapabilityExport
                (freshCapImages state.supply entry.scheme.capBinders)
                (capabilityExportPayload [capability]
                  (resultTarget :: results.bindings.map fun entry =>
                    entry.2))).recordEvent
                (.patternCtorCompatibility
                  (finalState.freezeCapabilityExport
                    (freshCapImages state.supply entry.scheme.capBinders)
                    (capabilityExportPayload [capability]
                      (resultTarget :: results.bindings.map fun entry =>
                        entry.2))).trace.solves.length name
                  (results.duals.map Dual.cap) capability)).recordEvent
              (.inferredPattern (.pctor name patterns)
                ⟨capability, resultTarget⟩ results.bindings path)⟩ := by
  have compatible' : capCompatibleCheck entry
      (results.duals.map
        ((fun child => child.apply finalState.prevailing.cap) ∘ Dual.cap))
      (capability.apply finalState.prevailing.cap) = true := by
    simpa only [List.map_map] using compatible
  simp [inferPatternFuel, lookup, instantiated, children, aligned, solved,
    compatible']

/-- `matchAll` passes the raw target inferred for its target expression to the
matcher-slot check; `checkExprFuel` performs prevailing normalization exactly
once. -/
theorem inferExprFuel_matchAll_checks_raw_target_once
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {target matcher body : Expr} {pattern : Pattern} {state : InferState}
    {targetResult : ExprResult} {patternResult : PatternResult}
    {alignedState matcherState : InferState} {bodyResult : ExprResult}
    (targetSuccess : inferExprFuel fuel signature context selfEnv (0 :: path)
      target (visit state .exprMatchAll path) = some targetResult)
    (patternSuccess : inferPatternFuel fuel signature context [] [] selfEnv
      (2 :: path) pattern targetResult.state = some patternResult)
    (aligned : alignTypes patternResult.state
      (freshOrigin .pattern (2 :: path) "match-target")
      patternResult.dual.target targetResult.target = some alignedState)
    (matcherSuccess : checkExprFuel fuel signature context selfEnv (1 :: path)
      matcher (.slot patternResult.dual.cap targetResult.target) alignedState =
        some matcherState)
    (bodySuccess : inferExprFuel fuel signature
      (patternResult.bindings.toContext ++ context)
      (selfEnv.eraseMany pattern.patVars) (3 :: path) body matcherState =
        some bodyResult) :
    inferExprFuel (fuel + 1) signature context selfEnv path
      (.matchAll target matcher pattern body) state =
        some (finishExpr (.matchAll target matcher pattern body) path
          (.listT bodyResult.target) bodyResult.state) := by
  simp [inferExprFuel, targetSuccess, patternSuccess, aligned, matcherSuccess,
    bodySuccess]

/-- Clause next-matcher checks receive raw hole duals.  Their prevailing
substitution is applied exactly once inside `checkExprFuel`. -/
theorem inferClauseFuel_checks_raw_holes_once
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {primitivePattern : PPat}
    {next : Expr} {arms : List Arm} {sharedTarget : Ty}
    {state : InferState} {ppResult : PPatResult}
    {nextMatchers : List Expr} {matcherState armState : InferState}
    (primitiveSuccess : inferPPatFuel fuel signature (0 :: path)
      primitivePattern sharedTarget (visit state .clause path) = some ppResult)
    (decomposed : decomposeME next ppResult.holes.length = some nextMatchers)
    (matchersChecked : checkExprsFuel fuel signature context selfEnv (1 :: path)
      0 nextMatchers
      (ppResult.holes.map fun hole => .slot hole.cap hole.target)
      ppResult.state = some matcherState)
    (armsChecked : checkArmsFuel fuel signature context selfEnv
      ppResult.bindings (2 :: path) 0 arms sharedTarget
      (.listT (prodTy (ppResult.holes.map Dual.target))) matcherState =
        some armState) :
    inferClauseFuel (fuel + 1) signature context selfEnv path
      (.mk primitivePattern next arms) sharedTarget state =
        some ⟨sharedTarget, ppResult.holes, armState⟩ := by
  simp [inferClauseFuel, primitiveSuccess, decomposed, matchersChecked,
    armsChecked]

end Inference
end TypePM
