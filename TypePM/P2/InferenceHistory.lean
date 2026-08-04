import TypePM.P2.Inference

namespace TypePM.P2.Inference

theorem checkExprFuel_historyPrefix
    {fuel signature context selfEnv path expression expected state result}
    (success : checkExprFuel fuel signature context selfEnv path expression
      expected state = some result) : state.HistoryPrefix result := by
  cases fuel with
  | zero => simp [checkExprFuel] at success
  | succ fuel =>
      simp only [checkExprFuel] at success
      cases inferredEq : inferExprFuel fuel signature context selfEnv path
          expression state with
      | none => simp [inferredEq] at success
      | some inferred =>
          cases alignmentEq : alignAtSlot inferred.state
              (freshOrigin .expression path "expected-type") inferred.target
              expected with
          | none => simp [inferredEq, alignmentEq] at success
          | some aligned =>
              simp [inferredEq, alignmentEq] at success
              subst result
              exact (inferExprFuel_historyPrefix inferredEq).trans
                ((alignAtSlot_historyPrefix alignmentEq).trans
                  (InferState.historyPrefix_recordEvent _ _))

theorem checkExprsFuel_historyPrefix
    {fuel signature context selfEnv path index expressions expecteds state result}
    (success : checkExprsFuel fuel signature context selfEnv path index expressions
      expecteds state = some result) : state.HistoryPrefix result := by
  induction fuel generalizing index expressions expecteds state result with
  | zero => simp [checkExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          cases expecteds with
          | nil =>
              simp only [checkExprsFuel, Option.some.injEq] at success
              subst result
              exact InferState.HistoryPrefix.refl state
          | cons expected expecteds => simp [checkExprsFuel] at success
      | cons expression expressions =>
          cases expecteds with
          | nil => simp [checkExprsFuel] at success
          | cons expected expecteds =>
              simp only [checkExprsFuel] at success
              cases headEq : checkExprFuel fuel signature context selfEnv
                  (index :: path) expression expected state with
              | none => simp [headEq] at success
              | some middle =>
                  simp only [headEq] at success
                  have headHistory := checkExprFuel_historyPrefix headEq
                  have tailHistory := induction
                    (index := index + 1) (expressions := expressions)
                    (expecteds := expecteds) (state := middle)
                    (result := result) success
                  exact headHistory.trans tailHistory

theorem inferExprsFuel_historyPrefix
    {fuel signature context selfEnv path index expressions state result}
    (success : inferExprsFuel fuel signature context selfEnv path index expressions
      state = some result) : state.HistoryPrefix result.state := by
  induction fuel generalizing index expressions state result with
  | zero => simp [inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [inferExprsFuel, Option.some.injEq] at success
          subst result
          exact InferState.HistoryPrefix.refl state
      | cons expression expressions =>
          simp only [inferExprsFuel] at success
          cases headEq : inferExprFuel fuel signature context selfEnv
              (index :: path) expression state with
          | none => simp [headEq] at success
          | some head =>
              cases tailEq : inferExprsFuel fuel signature context selfEnv path
                  (index + 1) expressions head.state with
              | none => simp [headEq, tailEq] at success
              | some tail =>
                  simp [headEq, tailEq] at success
                  subst result
                  exact (inferExprFuel_historyPrefix headEq).trans
                    (induction (index := index + 1)
                      (expressions := expressions) (state := head.state)
                      (result := tail) tailEq)

private structure PatternHistoryAtFuel (fuel : Nat) : Prop where
  one : ∀ {signature context parameters bindings selfEnv path pattern state result},
    inferPatternFuel fuel signature context parameters bindings selfEnv path pattern
      state = some result → state.HistoryPrefix result.state
  many : ∀ {signature context parameters bindings selfEnv path index patterns
      state result},
    inferPatternsFuel fuel signature context parameters bindings selfEnv path index
      patterns state = some result → state.HistoryPrefix result.state

set_option maxHeartbeats 1000000 in
private theorem patternHistoryAtFuel (fuel : Nat) : PatternHistoryAtFuel fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp_all [inferPatternFuel, inferPatternsFuel]
  | succ fuel ih =>
      refine { one := ?_, many := ?_ }
      · intro signature context parameters bindings selfEnv path pattern state
          result success
        cases pattern with
        | pvar name =>
            simp only [inferPatternFuel] at success
            split at success <;> try contradiction
            simp only [Option.some.injEq] at success
            subst result
            exact ((InferState.historyPrefix_freshCap _ _).trans
              ((InferState.historyPrefix_freshTy _ _).trans
                ((InferState.historyPrefix_recordEvent _ _).trans
                  ((visit_historyPrefix _ _ _).trans
                    (InferState.historyPrefix_recordEvent _ _)))))
        | wild =>
            simp only [inferPatternFuel, Option.some.injEq] at success
            subst result
            exact ((InferState.historyPrefix_freshCap _ _).trans
              ((InferState.historyPrefix_freshTy _ _).trans
                ((InferState.historyPrefix_recordEvent _ _).trans
                  ((visit_historyPrefix _ _ _).trans
                    (InferState.historyPrefix_recordEvent _ _)))))
        | pval expression =>
            simp only [inferPatternFuel] at success
            cases bodyEq : inferExprFuel fuel signature
                (bindings.toContext ++ context) selfEnv (0 :: path) expression
                (visit state .patternValue path) with
            | none => simp [bodyEq] at success
            | some bodyResult =>
                simp [bodyEq] at success
                subst result
                exact (visit_historyPrefix state .patternValue path).trans
                  ((inferExprFuel_historyPrefix bodyEq).trans
                    ((InferState.historyPrefix_freshCap _ _).trans
                      ((InferState.historyPrefix_recordEvent _ _).trans
                        (InferState.historyPrefix_recordEvent _ _))))
        | embed name =>
            simp only [inferPatternFuel] at success
            cases lookup : parameters.find? name with
            | none => simp [lookup] at success
            | some dual =>
                simp [lookup] at success
                subst result
                exact (visit_historyPrefix state .patternEmbed path).trans
                  (InferState.historyPrefix_recordEvent _ _)
        | ptuple patterns =>
            simp only [inferPatternFuel] at success
            cases childrenEq : inferPatternsFuel fuel signature context parameters
                bindings selfEnv path 0 patterns
                (visit state .patternTuple path) with
            | none => simp [childrenEq] at success
            | some children =>
                simp [childrenEq] at success
                subst result
                exact (visit_historyPrefix state .patternTuple path).trans
                  ((ih.many childrenEq).trans
                    (InferState.historyPrefix_recordEvent _ _))
        | pctor name patterns =>
            simp only [inferPatternFuel] at success
            cases lookup : signature.findPatternCtor name with
            | none => simp [lookup] at success
            | some entry =>
                simp only [lookup] at success
                generalize instEq : instantiateCtorInState state entry.scheme =
                  instantiation at success
                rcases instantiation with ⟨⟨expectedTargets, resultTarget⟩,
                  instState⟩
                simp only [Prod.fst, Prod.snd] at success
                cases childrenEq : inferPatternsFuel fuel signature context
                    parameters bindings selfEnv path 0 patterns
                    (visit instState .patternCtor path) with
                | none => simp [childrenEq] at success
                | some children =>
                    simp only [childrenEq] at success
                    cases alignmentEq : alignPatternTargets children.state
                        (freshOrigin .pattern path
                          "pattern-constructor-fields") children.duals
                        expectedTargets with
                    | none => simp [alignmentEq] at success
                    | some aligned =>
                        simp only [alignmentEq] at success
                        cases projectionEq : Projection.projectSignature
                            entry.projection
                            (children.duals.map (Shape.ofCap ∘ Dual.cap)) with
                        | none =>
                            have projectionEq' :
                                Projection.projectSignature entry.projection
                                  ((children.duals.map Dual.cap).map
                                    Shape.ofCap) = none := by
                              simpa only [List.map_map] using projectionEq
                            rw [projectionEq'] at success <;> contradiction
                        | some projected =>
                            have projectionEq' :
                                Projection.projectSignature entry.projection
                                  ((children.duals.map Dual.cap).map
                                    Shape.ofCap) = some projected := by
                              simpa only [List.map_map] using projectionEq
                            rw [projectionEq'] at success
                            try simp only at success
                            cases freshEq : freshenSkeleton signature.observability
                                (freshOrigin .pattern path
                                  "pattern-constructor-capability") projected
                                aligned with
                            | none =>
                                rw [freshEq] at success <;> contradiction
                            | some fresh =>
                                rcases fresh with ⟨capability, freshState⟩
                                rw [freshEq] at success
                                try simp only at success
                                split at success
                                · simp only [Option.some.injEq] at success
                                  subst result
                                  exact (instantiateCtorInState_historyPrefix_of_eq
                                      instEq).trans
                                    ((visit_historyPrefix instState .patternCtor
                                      path).trans
                                      ((ih.many childrenEq).trans
                                        ((alignPatternTargets_historyPrefix
                                          alignmentEq).trans
                                          ((freshenSkeleton_historyPrefix freshEq).trans
                                            ((InferState.historyPrefix_recordEvent
                                              _ _).trans
                                              (InferState.historyPrefix_recordEvent
                                                _ _))))))
                                · contradiction
        | pand left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternAnd path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context parameters
                    leftResult.bindings selfEnv (1 :: path) right
                    leftResult.state with
                | none => simp [leftEq, rightEq] at success
                | some rightResult =>
                    cases alignmentEq : alignDuals rightResult.state
                        (freshOrigin .pattern path "pattern-and")
                        leftResult.dual rightResult.dual with
                    | none => simp [leftEq, rightEq, alignmentEq] at success
                    | some aligned =>
                        simp [leftEq, rightEq, alignmentEq] at success
                        subst result
                        exact (visit_historyPrefix state .patternAnd path).trans
                          ((ih.one leftEq).trans
                            ((ih.one rightEq).trans
                              ((alignDuals_historyPrefix alignmentEq).trans
                                (InferState.historyPrefix_recordEvent _ _))))
        | por left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternOr path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context parameters
                    bindings selfEnv (1 :: path) right leftResult.state with
                | none => simp [leftEq, rightEq] at success
                | some rightResult =>
                    by_cases same : leftResult.bindings = rightResult.bindings
                    · cases alignmentEq : alignDuals rightResult.state
                          (freshOrigin .pattern path "pattern-or")
                          leftResult.dual rightResult.dual with
                      | none =>
                          simp [leftEq, rightEq, same, alignmentEq] at success
                      | some aligned =>
                          simp [leftEq, rightEq, same, alignmentEq] at success
                          subst result
                          exact (visit_historyPrefix state .patternOr path).trans
                            ((ih.one leftEq).trans
                              ((ih.one rightEq).trans
                                ((alignDuals_historyPrefix alignmentEq).trans
                                  (InferState.historyPrefix_recordEvent _ _))))
                    · simp [leftEq, rightEq, same] at success
        | papp name patterns =>
            simp only [inferPatternFuel] at success
            cases lookup : signature.findPatternFun name with
            | none => simp [lookup] at success
            | some scheme =>
                simp only [lookup] at success
                let normalizedContext := context.applySubst state.prevailing
                let normalizedParameters := parameters.applySubst state.prevailing
                let normalizedBindings := bindings.applySubst state.prevailing
                generalize instEq : instantiateDualInState signature context
                    parameters bindings normalizedContext normalizedParameters
                    normalizedBindings state scheme = instantiation at success
                rcases instantiation with ⟨⟨expectedArgs, resultDual⟩,
                  instState⟩
                dsimp [normalizedContext, normalizedParameters,
                  normalizedBindings] at instEq
                simp only [Prod.fst, Prod.snd] at success
                cases childrenEq : inferPatternsFuel fuel signature context
                    parameters bindings selfEnv path 0 patterns
                    (visit instState .patternApp path) with
                | none => simp [childrenEq] at success
                | some children =>
                    simp only [childrenEq] at success
                    cases alignmentEq : alignDualLists children.state
                        (freshOrigin .pattern path "pattern-function-arguments")
                        children.duals expectedArgs with
                    | none => simp [alignmentEq] at success
                    | some aligned =>
                        simp only [alignmentEq] at success
                        simp only [Option.some.injEq] at success
                        subst result
                        exact (instantiateDualInState_historyPrefix_of_eq
                            instEq).trans
                          ((visit_historyPrefix instState .patternApp path).trans
                            ((ih.many childrenEq).trans
                              ((alignDualLists_historyPrefix alignmentEq).trans
                                (InferState.historyPrefix_recordEvent _ _))))
      · intro signature context parameters bindings selfEnv path index patterns
          state result success
        cases patterns with
        | nil =>
            simp only [inferPatternsFuel, Option.some.injEq] at success
            subst result
            exact InferState.HistoryPrefix.refl state
        | cons pattern patterns =>
            simp only [inferPatternsFuel] at success
            cases headEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (index :: path) pattern state with
            | none => simp [headEq] at success
            | some head =>
                cases tailEq : inferPatternsFuel fuel signature context parameters
                    head.bindings selfEnv path (index + 1) patterns head.state with
                | none => simp [headEq, tailEq] at success
                | some tail =>
                    simp [headEq, tailEq] at success
                    subst result
                    exact (ih.one headEq).trans
                      (ih.many (result := tail) tailEq)

theorem inferPatternFuel_historyPrefix
    {fuel signature context parameters bindings selfEnv path pattern state result}
    (success : inferPatternFuel fuel signature context parameters bindings selfEnv
      path pattern state = some result) : state.HistoryPrefix result.state :=
  (patternHistoryAtFuel fuel).one success

theorem inferPatternsFuel_historyPrefix
    {fuel signature context parameters bindings selfEnv path index patterns state
      result}
    (success : inferPatternsFuel fuel signature context parameters bindings selfEnv
      path index patterns state = some result) : state.HistoryPrefix result.state :=
  (patternHistoryAtFuel fuel).many success

theorem checkArmsFuel_historyPrefix
    {fuel signature context selfEnv bindings path index arms target bodyTarget
      state result}
    (success : checkArmsFuel fuel signature context selfEnv bindings path index
      arms target bodyTarget state = some result) : state.HistoryPrefix result := by
  induction fuel generalizing index arms state result with
  | zero => simp [checkArmsFuel] at success
  | succ fuel induction =>
      cases arms with
      | nil =>
          simp only [checkArmsFuel, Option.some.injEq] at success
          subst result
          exact InferState.HistoryPrefix.refl state
      | cons arm arms =>
          rcases arm with ⟨dataPattern, body⟩
          simp only [checkArmsFuel] at success
          cases dataEq : inferDPatFuel fuel signature (0 :: index :: path)
              dataPattern target state with
          | none => simp [dataEq] at success
          | some dataResult =>
              simp only [dataEq] at success
              by_cases distinct : namesDisjoint dataResult.bindings.names
                  bindings.names = true
              · rw [if_pos distinct] at success
                cases bodyEq : checkExprFuel fuel signature
                    (dataResult.bindings.toContext ++
                      (bindings.toContext ++ context))
                    (selfEnv.eraseMany
                      (bindings.names ++ dataResult.bindings.names))
                    (1 :: index :: path) body bodyTarget dataResult.state with
                | none => simp_all
                | some middle =>
                    have tailSuccess : checkArmsFuel fuel signature context
                        selfEnv bindings path (index + 1) arms target bodyTarget
                        middle = some result := by
                      simpa only [bodyEq, List.append_assoc] using success
                    exact (inferDPatFuel_historyPrefix dataEq).trans
                      ((checkExprFuel_historyPrefix bodyEq).trans
                        (induction (index := index + 1) (arms := arms)
                          (state := middle) (result := result) tailSuccess))
              · rw [if_neg distinct] at success
                contradiction

theorem inferClauseFuel_historyPrefix
    {fuel signature context selfEnv path clause target state result}
    (success : inferClauseFuel fuel signature context selfEnv path clause target
      state = some result) : state.HistoryPrefix result.state := by
  cases fuel with
  | zero => simp [inferClauseFuel] at success
  | succ fuel =>
      rcases clause with ⟨primitivePattern, next, arms⟩
      simp only [inferClauseFuel] at success
      cases ppEq : inferPPatFuel fuel signature (0 :: path) primitivePattern
          target (visit state .clause path) with
      | none => simp [ppEq] at success
      | some ppResult =>
          simp only [ppEq] at success
          cases nextEq : decomposeME next ppResult.holes.length with
          | none => simp [ppEq, nextEq] at success
          | some nextMatchers =>
              simp only [nextEq] at success
              cases nextMatchersEq : checkExprsFuel fuel signature context selfEnv
                  (1 :: path) 0 nextMatchers
                  (ppResult.holes.map fun hole => Ty.slot hole.cap hole.target)
                  ppResult.state with
              | none => simp [nextMatchersEq] at success
              | some middle =>
                  simp [nextMatchersEq] at success
                  cases armsEq : checkArmsFuel fuel signature context selfEnv
                      ppResult.bindings (2 :: path) 0 arms target
                      (Ty.listT (prodTy (ppResult.holes.map Dual.target))) middle with
                  | none => simp [armsEq] at success
                  | some final =>
                      simp only [armsEq] at success
                      have resultStateEq : final = result.state :=
                        congrArg ClauseResult.state (Option.some.inj success)
                      exact ((visit_historyPrefix state .clause path).trans
                        ((inferPPatFuel_historyPrefix ppEq).trans
                          ((checkExprsFuel_historyPrefix nextMatchersEq).trans
                            (checkArmsFuel_historyPrefix armsEq)))).right_congr
                              resultStateEq

theorem inferClausesFuel_historyPrefix
    {fuel signature context selfEnv path index clauses target state result}
    (success : inferClausesFuel fuel signature context selfEnv path index clauses
      target state = some result) : state.HistoryPrefix result.state := by
  induction fuel generalizing index clauses state result with
  | zero => simp [inferClausesFuel] at success
  | succ fuel induction =>
      cases clauses with
      | nil =>
          simp only [inferClausesFuel, Option.some.injEq] at success
          subst result
          exact InferState.HistoryPrefix.refl state
      | cons clause clauses =>
          simp only [inferClausesFuel] at success
          cases headEq : inferClauseFuel fuel signature context selfEnv
              (index :: path) clause target state with
          | none => simp [headEq] at success
          | some head =>
              cases tailEq : inferClausesFuel fuel signature context selfEnv path
                  (index + 1) clauses target head.state with
              | none => simp [headEq, tailEq] at success
              | some tail =>
                  simp [headEq, tailEq] at success
                  subst result
                  exact (inferClauseFuel_historyPrefix headEq).trans
                    (induction (index := index + 1) (clauses := clauses)
                      (state := head.state) (result := tail) tailEq)

theorem inferMatcherFuel_historyPrefix
    {fuel signature context selfEnv path clauses state result}
    (success : inferMatcherFuel fuel signature context selfEnv path clauses state =
      some result) : state.HistoryPrefix result.state := by
  cases fuel with
  | zero => simp [inferMatcherFuel] at success
  | succ fuel =>
      simp only [inferMatcherFuel] at success
      generalize freshEq : state.freshTy
          (freshOrigin .matcherClause path "matcher-target") = fresh at success
      rcases fresh with ⟨target, freshState⟩
      cases clausesEq : inferClausesFuel fuel signature context selfEnv path 0
          clauses target freshState with
      | none => simp [freshEq, clausesEq] at success
      | some clausesResult =>
          simp only [Prod.fst, Prod.snd, clausesEq] at success
          cases evidenceEq : collectClauseEvidence signature.toMatcherSig clauses
              (clausesResult.rawHoleLists.map fun holes =>
                (holes.map
                  (Dual.applySubst clausesResult.state.prevailing)).map
                    Dual.cap) with
          | none =>
              rw [evidenceEq] at success
              contradiction
          | some evidence =>
              rw [evidenceEq] at success
              cases shapeEq : Shape.inferShape signature.observability evidence with
              | none => simp [shapeEq] at success
              | some capability =>
                  try simp only [shapeEq] at success
                  split at success
                  · simp only [Option.some.injEq] at success
                    subst result
                    have freshHistory : state.HistoryPrefix freshState :=
                      InferState.HistoryPrefix.snd_of_eq
                        (InferState.historyPrefix_freshTy state
                          (freshOrigin .matcherClause path "matcher-target"))
                        freshEq
                    exact freshHistory.trans
                      ((inferClausesFuel_historyPrefix clausesEq).trans
                        ((InferState.historyPrefix_recordEvent _ _).trans
                          (InferState.historyPrefix_recordEvent _ _)))
                  · contradiction

end TypePM.P2.Inference
