import TypePM.InferenceHistory
import TypePM.InferenceStateExtension

/-!
# Monotone state extension through executable inference

This module lifts the append-only history results for the executable traversal
to `InferState.StateExtension`.  Besides retaining every earlier solver and
event, successful helpers cannot decrease either fresh counter or forget an
already protected capability.
-/

namespace TypePM.Inference

/-! ## Non-recursive traversal boundaries -/

theorem visit_stateExtension
    (state : InferState) (kind : NodeKind) (path : SyntaxPath) :
    state.StateExtension (visit state kind path) := by
  exact state.stateExtension_recordEvent _

theorem finishExpr_stateExtension
    (expression : Expr) (path : SyntaxPath) (target : Ty)
    (state : InferState) :
    state.StateExtension (finishExpr expression path target state).state := by
  exact state.stateExtension_recordEvent _

theorem recordSelfReference_stateExtension
    (state : InferState) (binder : String) (placeholder : Ty)
    (path : SyntaxPath) :
    state.StateExtension
      (recordSelfReference state binder placeholder path) := by
  exact (state.stateExtension_recordEvent _).trans
    (InferState.stateExtension_recordSource _ _)

/-! ## Alignment helpers -/

theorem alignTypesCore_stateExtension
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypesCore state origin left right = some result) :
    state.StateExtension result := by
  unfold alignTypesCore at success
  simp only at success
  split at success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_stateExtension firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      have second : middle.StateExtension result :=
        runResolvedConstraint_stateExtension restSuccess
      exact first.trans second
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_stateExtension firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      have second : middle.StateExtension result :=
        runResolvedConstraint_stateExtension restSuccess
      exact first.trans second
  · exact runResolvedConstraint_stateExtension success

theorem alignTypes_stateExtension
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some result) :
    state.StateExtension result := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, coreSuccess, finished⟩
  have coreExtension := alignTypesCore_stateExtension coreSuccess
  have resultEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (state.prevailing.apply left)
      (state.prevailing.apply right)) = result :=
    Option.some.inj finished
  exact (coreExtension.trans (aligned.stateExtension_recordEvent _)).right_congr
    resultEq

theorem alignAtSlot_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {inferred expected : Ty}
    (success : alignAtSlot state origin inferred expected = some result) :
    state.StateExtension result := by
  unfold alignAtSlot at success
  simp only at success
  split at success
  · exact runResolvedConstraint_stateExtension success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_stateExtension firstSuccess
    split at restSuccess <;> try contradiction
    have second : middle.StateExtension result :=
      runResolvedConstraint_stateExtension restSuccess
    exact first.trans second
  · exact alignTypes_stateExtension success

theorem alignResolvedProductMatcherAtSlot_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedProductMatcherAtSlot state origin duals consumerCap
      consumerTarget = some result) :
    state.StateExtension result :=
  runResolvedConstraint_stateExtension success

theorem alignResolvedSlotTupleAtSlot_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedSlotTupleAtSlot state origin duals consumerCap
      consumerTarget = some result) :
    state.StateExtension result := by
  unfold alignResolvedSlotTupleAtSlot at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨step, _, restSuccess⟩
  exact (state.stateExtension_recordSolve step).trans
    (runResolvedConstraint_stateExtension restSuccess)

theorem alignExprResultAtExpected_stateExtension
    {path : SyntaxPath} {expressionResult : ExprResult}
    {expected : Ty} {result : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some result) :
    expressionResult.state.StateExtension result := by
  unfold alignExprResultAtExpected at success
  cases planEq : expectedCoercionPlan expressionResult.state
      expressionResult.target expected with
  | productMatcherLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedProductMatcherAtSlot
          expressionResult.state (freshOrigin .expression path "expected-type")
          duals consumerCap consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst result
          exact (alignResolvedProductMatcherAtSlot_stateExtension
            alignmentEq).trans (aligned.stateExtension_recordEvent _)
  | slotTupleLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedSlotTupleAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst result
          exact (alignResolvedSlotTupleAtSlot_stateExtension alignmentEq).trans
            (aligned.stateExtension_recordEvent _)
  | raw =>
      cases alignmentEq : alignAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type") expressionResult.target
          expected with
      | none => simp [planEq, alignmentEq] at success
      | some aligned =>
          simp only [planEq, alignmentEq, Option.some.injEq] at success
          subst result
          exact (alignAtSlot_stateExtension alignmentEq).trans
            (aligned.stateExtension_recordEvent _)

theorem alignDuals_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some result) :
    state.StateExtension result := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, firstSuccess, secondSuccess⟩
  rcases Option.bind_eq_some_iff.mp secondSuccess with
    ⟨aligned, alignSuccess, finished⟩
  have resultEq : aligned.recordEvent (.dualAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (left.applySubst state.prevailing)
      (right.applySubst state.prevailing)) = result :=
    Option.some.inj finished
  exact ((runResolvedConstraint_stateExtension firstSuccess).trans
      ((alignTypes_stateExtension alignSuccess).trans
        (aligned.stateExtension_recordEvent _))).right_congr resultEq

theorem alignDualLists_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : List Dual}
    (success : alignDualLists state origin left right = some result) :
    state.StateExtension result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignDualLists] at success
      subst result
      exact InferState.StateExtension.refl state
  | cons head tail induction =>
      cases right with
      | nil => simp [alignDualLists] at success
      | cons expected expecteds =>
          simp only [alignDualLists] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignDuals_stateExtension firstSuccess).trans
            (induction restSuccess)

theorem alignPatternTargets_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some result) :
    state.StateExtension result := by
  induction duals generalizing state targets with
  | nil =>
      cases targets <;> simp [alignPatternTargets] at success
      subst result
      exact InferState.StateExtension.refl state
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignTypes_stateExtension firstSuccess).trans
            (induction restSuccess)

theorem alignBindings_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : MonoCtx}
    (success : alignBindings state origin left right = some result) :
    state.StateExtension result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignBindings] at success
      subst result
      exact InferState.StateExtension.refl state
  | cons entry entries induction =>
      cases right with
      | nil => simp [alignBindings] at success
      | cons expected expecteds =>
          simp only [alignBindings] at success
          split at success
          · rcases Option.bind_eq_some_iff.mp success with
              ⟨middle, firstSuccess, restSuccess⟩
            exact (alignTypes_stateExtension firstSuccess).trans
              (induction restSuccess)
          · exact absurd success (by simp)

/-! ## Fresh structural evidence and recursive placeholders -/

theorem freshenSkeleton_stateExtension
    {observable origin evidence state capability result}
    (success : freshenSkeleton observable origin evidence state =
      some (capability, result)) :
    state.StateExtension result := by
  apply freshenSkeleton.induct
    (motive_1 := fun evidence state => ∀ capability result,
      freshenSkeleton observable origin evidence state =
          some (capability, result) →
        state.StateExtension result)
    (motive_2 := fun evidence state => ∀ capabilities result,
      freshenSkeletonList observable origin evidence state =
          some (capabilities, result) →
        state.StateExtension result)
    (motive_3 := fun mask evidence state => ∀ capabilities result,
      freshenSkeletonMasked observable origin mask evidence state =
          some (capabilities, result) →
        state.StateExtension result)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true })
  case case10 t x state mismatchNil mismatchCons capabilities result success =>
    cases x <;> cases t <;> simp_all [freshenSkeletonMasked]
  all_goals first
    | assumption
    | exact InferState.StateExtension.refl _
    | grind [InferState.stateExtension_freshCap,
        InferState.StateExtension.refl, InferState.StateExtension.trans,
        Option.bind_eq_some_iff, freshenSkeleton,
        freshenSkeletonList, freshenSkeletonMasked]

theorem recursiveMatcherTemplate_stateExtension
    {signature path clauses state capability result}
    (success : recursiveMatcherTemplate signature path clauses state =
      some (capability, result)) :
    state.StateExtension result := by
  unfold recursiveMatcherTemplate at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨evidence, skeleton, finished⟩
  cases evidence with
  | unseen =>
      cases finished
      exact InferState.StateExtension.refl state
  | known leaf => exact freshenSkeleton_stateExtension finished
  | con name children => exact freshenSkeleton_stateExtension finished
  | prod components => exact freshenSkeleton_stateExtension finished

theorem buildFixPlaceholder_stateExtension
    {signature path body state domain codomain result}
    (success : buildFixPlaceholder signature path body state =
      some (domain, codomain, result)) :
    state.StateExtension result := by
  cases body <;> simp_all [buildFixPlaceholder]
  case matcher clauses =>
    rcases Option.bind_eq_some_iff.mp success with
      ⟨pair, recursiveSuccess, rest⟩
    rcases pair with ⟨capability, middle⟩
    have recursiveExtension :=
      recursiveMatcherTemplate_stateExtension recursiveSuccess
    simp only [Option.some.injEq, Prod.mk.injEq] at rest
    split at rest
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveExtension.trans
        ((InferState.stateExtension_freshTy _ _).trans
          (InferState.stateExtension_freshTy _ _))
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveExtension.trans
        ((InferState.stateExtension_freshCap _ _).trans
          ((InferState.stateExtension_freshTy _ _).trans
            (InferState.stateExtension_freshTy _ _)))
  all_goals
    rcases success with ⟨_, _, rfl⟩
    exact (InferState.stateExtension_freshTy _ _).trans
      (InferState.stateExtension_freshTy _ _)

/-! ## Pattern-constructor and finite fresh-list helpers -/

theorem freshPatternCtorAssignments_stateExtension
    {origin : ConstraintOrigin} {variables : List TypePM.TyVar}
    {state result : InferState} {assignments : Projection.Assignments}
    (success : freshPatternCtorAssignments origin variables state =
      (assignments, result)) :
    state.StateExtension result := by
  induction variables generalizing state assignments result with
  | nil =>
      simp only [freshPatternCtorAssignments, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact InferState.StateExtension.refl state
  | cons varId variables induction =>
      simp only [freshPatternCtorAssignments] at success
      let fresh := state.freshCap origin
      cases restEq : freshPatternCtorAssignments origin variables fresh.2 with
      | mk restAssignments restState =>
          simp only [fresh, restEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact (InferState.stateExtension_freshCap state origin).trans
            (induction restEq)

theorem alignPatternCtorCapabilities_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {children : List Cap} {demands : List (Option Cap)}
    (success : alignPatternCtorCapabilities state origin children demands =
      some result) :
    state.StateExtension result := by
  induction children generalizing state demands with
  | nil =>
      cases demands <;>
        simp [alignPatternCtorCapabilities] at success
      subst result
      exact InferState.StateExtension.refl state
  | cons child children induction =>
      cases demands with
      | nil => simp [alignPatternCtorCapabilities] at success
      | cons demand demands =>
          cases demand with
          | none =>
              simpa only [alignPatternCtorCapabilities] using
                induction success
          | some expected =>
              simp only [alignPatternCtorCapabilities] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨middle, firstSuccess, restSuccess⟩
              exact (runResolvedConstraint_stateExtension firstSuccess).trans
                (induction restSuccess)

theorem solvePatternCtorCapability_stateExtension
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {childCaps : List Cap}
    {state result : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin childCaps
      state = some (capability, result)) :
    state.StateExtension result := by
  unfold solvePatternCtorCapability at success
  simp only at success
  split at success
  · exact freshenSkeleton_stateExtension success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨resultVariables, _resultVariablesEq, rest⟩
    let uniqueVariables := resultVariables.eraseDups
    let allocated :=
      freshPatternCtorAssignments origin uniqueVariables state
    rcases allocatedEq : allocated with ⟨assignments, allocatedState⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨demands, _demandsEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨alignedState, alignmentEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨projected, _projectionEq, skeletonEq⟩
    have allocationEq :
        freshPatternCtorAssignments origin uniqueVariables state =
          (assignments, allocatedState) := by
      simpa [allocated] using allocatedEq
    rw [allocationEq] at alignmentEq
    exact (freshPatternCtorAssignments_stateExtension allocationEq).trans
      ((alignPatternCtorCapabilities_stateExtension alignmentEq).trans
        (freshenSkeleton_stateExtension skeletonEq))

theorem freshTargets_stateExtension
    {state result : InferState} {origin : ConstraintOrigin}
    {count : Nat} {targets : List Ty}
    (success : freshTargets state origin count = (targets, result)) :
    state.StateExtension result := by
  induction count generalizing state targets result with
  | zero =>
      simp only [freshTargets, Prod.mk.injEq] at success
      rcases success with ⟨_, equality⟩
      subst result
      exact InferState.StateExtension.refl state
  | succ count induction =>
      simp only [freshTargets] at success
      let fresh := state.freshTy origin
      let rest := freshTargets fresh.2 origin count
      have first : state.StateExtension fresh.2 := by
        exact InferState.stateExtension_freshTy state origin
      have restExtension : fresh.2.StateExtension rest.2 :=
        induction (state := fresh.2) (targets := rest.1)
          (result := rest.2) rfl
      have finalEq : rest.2 = result := by
        exact congrArg Prod.snd success
      subst result
      exact first.trans restExtension

/-! ## Primitive-pattern traversals -/

set_option maxHeartbeats 1000000 in
theorem inferPPatFuel_stateExtension
    {fuel signature path pattern target state result}
    (success : inferPPatFuel fuel signature path pattern target state =
      some result) :
    state.StateExtension result.state := by
  apply inferPPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferPPatFuel fuel signature path pattern target state = some result →
        state.StateExtension result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferPPatsFuel fuel signature path index patterns targets state =
            some result →
          state.StateExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferPPatFuel, inferPPatsFuel, Option.some.injEq]
  all_goals try
    have ctorExtension := instantiateCtorInState_stateExtension_of_eq
      (by assumption)
  all_goals try
    have alignmentExtension := alignTypes_stateExtension (by assumption)
  all_goals try
    have freshExtension := freshTargets_stateExtension (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.StateExtension.refl _
    | grind [InferState.StateExtension.refl,
        InferState.StateExtension.trans,
        InferState.StateExtension.snd_of_eq,
        InferState.StateExtension.right_congr,
        InferState.stateExtension_freshCap,
        instantiateCtorInState_stateExtension,
        instantiateCtorInState_stateExtension_of_eq,
        InferState.stateExtension_freezeCapabilityExport,
        alignTypes_stateExtension,
        freshTargets_stateExtension,
        visit_stateExtension,
        InferState.stateExtension_recordEvent,
        Option.bind_eq_some_iff,
        inferPPatFuel, inferPPatsFuel]

theorem inferPPatsFuel_stateExtension
    {fuel signature path index patterns targets state result}
    (success : inferPPatsFuel fuel signature path index patterns targets state =
      some result) :
    state.StateExtension result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferPPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferPPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.StateExtension.refl state
          | cons target targets => simp [inferPPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferPPatsFuel] at success
          | cons target targets =>
              simp only [inferPPatsFuel] at success
              cases headEq : inferPPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferPPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact (inferPPatFuel_stateExtension headEq).trans
                          (induction (index := index + 1)
                            (patterns := patterns) (targets := targets)
                            (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

set_option maxHeartbeats 1000000 in
theorem inferDPatFuel_stateExtension
    {fuel signature path pattern target state result}
    (success : inferDPatFuel fuel signature path pattern target state =
      some result) :
    state.StateExtension result.state := by
  apply inferDPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferDPatFuel fuel signature path pattern target state = some result →
        state.StateExtension result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferDPatsFuel fuel signature path index patterns targets state =
            some result →
          state.StateExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferDPatFuel, inferDPatsFuel, Option.some.injEq]
  all_goals try
    have ctorExtension := instantiateCtorInState_stateExtension_of_eq
      (by assumption)
  all_goals try
    have alignmentExtension := alignTypes_stateExtension (by assumption)
  all_goals try
    have freshExtension := freshTargets_stateExtension (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.StateExtension.refl _
    | grind [InferState.StateExtension.refl,
        InferState.StateExtension.trans,
        InferState.StateExtension.snd_of_eq,
        InferState.StateExtension.right_congr,
        instantiateCtorInState_stateExtension,
        instantiateCtorInState_stateExtension_of_eq,
        InferState.stateExtension_freezeCapabilityExport,
        alignTypes_stateExtension,
        freshTargets_stateExtension,
        visit_stateExtension,
        InferState.stateExtension_recordEvent,
        Option.bind_eq_some_iff,
        inferDPatFuel, inferDPatsFuel]

theorem inferDPatsFuel_stateExtension
    {fuel signature path index patterns targets state result}
    (success : inferDPatsFuel fuel signature path index patterns targets state =
      some result) :
    state.StateExtension result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferDPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferDPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.StateExtension.refl state
          | cons target targets => simp [inferDPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferDPatsFuel] at success
          | cons target targets =>
              simp only [inferDPatsFuel] at success
              cases headEq : inferDPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferDPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact (inferDPatFuel_stateExtension headEq).trans
                          (induction (index := index + 1)
                            (patterns := patterns) (targets := targets)
                            (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

/-! ## The mutually recursive expression traversal -/

set_option maxHeartbeats 1000000 in
/-- Every successful expression traversal monotonically extends the incoming
state. -/
private theorem inferExprFuel_stateExtensionCore
    {fuel signature context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result) :
    state.StateExtension result.state := by
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression state =>
      ∀ result,
        inferExprFuel fuel signature context selfEnv path expression state =
            some result →
          state.StateExtension result.state)
    (motive2 := fun fuel signature context selfEnv path expression expected
        state =>
      ∀ result,
        checkExprFuel fuel signature context selfEnv path expression expected
            state = some result →
          state.StateExtension result)
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern state =>
      ∀ result,
        inferPatternFuel fuel signature context parameters bindings selfEnv path
            pattern state = some result →
          state.StateExtension result.state)
    (motive4 := fun fuel signature context parameters bindings selfEnv path
        index patterns state =>
      ∀ result,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            path index patterns state = some result →
          state.StateExtension result.state)
    (motive5 := fun fuel signature context selfEnv path clauses state =>
      ∀ result,
        inferMatcherFuel fuel signature context selfEnv path clauses state =
            some result →
          state.StateExtension result.state)
    (motive6 := fun fuel signature context selfEnv path index clauses target
        state =>
      ∀ result,
        inferClausesFuel fuel signature context selfEnv path index clauses target
            state = some result →
          state.StateExtension result.state)
    (motive7 := fun fuel signature context selfEnv path clause target state =>
      ∀ result,
        inferClauseFuel fuel signature context selfEnv path clause target state =
            some result →
          state.StateExtension result.state)
    (motive8 := fun fuel signature context selfEnv bindings path index arms
        target bodyTarget state =>
      ∀ result,
        checkArmsFuel fuel signature context selfEnv bindings path index arms
            target bodyTarget state = some result →
          state.StateExtension result)
    (motive9 := fun fuel signature context selfEnv path index expressions
        expecteds state =>
      ∀ result,
        checkExprsFuel fuel signature context selfEnv path index expressions
            expecteds state = some result →
          state.StateExtension result)
    (motive10 := fun fuel signature context selfEnv path index expressions
        state =>
      ∀ result,
        inferExprsFuel fuel signature context selfEnv path index expressions
            state = some result →
          state.StateExtension result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [Option.some.injEq, inferExprFuel, checkExprFuel, inferPatternFuel,
      inferPatternsFuel, inferMatcherFuel, inferClausesFuel, inferClauseFuel,
      checkArmsFuel, checkExprsFuel, inferExprsFuel]
  all_goals try
    have placeholderExtension := buildFixPlaceholder_stateExtension
      (by assumption)
  all_goals try
    have dpatExtension := inferDPatFuel_stateExtension (by assumption)
  all_goals try
    have ppatExtension := inferPPatFuel_stateExtension (by assumption)
  all_goals try
    have alignmentExtension := alignTypes_stateExtension (by assumption)
  all_goals try
    have slotAlignmentExtension := alignAtSlot_stateExtension (by assumption)
  all_goals try
    have expectedAlignmentExtension :=
      alignExprResultAtExpected_stateExtension (by assumption)
  all_goals try
    have dualAlignmentExtension := alignDuals_stateExtension (by assumption)
  all_goals try
    have dualListExtension := alignDualLists_stateExtension (by assumption)
  all_goals try
    have patternTargetsExtension := alignPatternTargets_stateExtension
      (by assumption)
  all_goals try
    have bindingAlignmentExtension := alignBindings_stateExtension
      (by assumption)
  all_goals try
    have patternCtorCapabilityExtension :=
      solvePatternCtorCapability_stateExtension (by assumption)
  all_goals try
    have skeletonExtension := freshenSkeleton_stateExtension (by assumption)
  all_goals try
    have recursiveMatcherExtension :=
      recursiveMatcherTemplate_stateExtension (by assumption)
  all_goals try
    have schemeExtension := instantiateSchemeInState_stateExtension_of_eq
      (by assumption)
  all_goals try
    have ctorExtension := instantiateCtorInState_stateExtension_of_eq
      (by assumption)
  all_goals try
    have dualInstanceExtension := instantiateDualInState_stateExtension_of_eq
      (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.StateExtension.refl _
    | grind [visit_stateExtension, finishExpr_stateExtension,
        recordSelfReference_stateExtension,
        instantiateSchemeInState_stateExtension,
        instantiateCtorInState_stateExtension,
        instantiateDualInState_stateExtension,
        InferState.stateExtension_freshTy,
        InferState.stateExtension_freshCap,
        InferState.stateExtension_protectMatcherCapability,
        InferState.stateExtension_protectMatcherCapabilityExcept,
        InferState.stateExtension_freezeCapabilityExport,
        InferState.stateExtension_recordEvent,
        InferState.stateExtension_recordSource,
        alignTypes_stateExtension,
        alignAtSlot_stateExtension,
        alignExprResultAtExpected_stateExtension,
        alignDuals_stateExtension,
        alignDualLists_stateExtension,
        alignBindings_stateExtension,
        alignPatternTargets_stateExtension,
        solvePatternCtorCapability_stateExtension,
        runResolvedConstraint_stateExtension,
        freshenSkeleton_stateExtension,
        recursiveMatcherTemplate_stateExtension,
        buildFixPlaceholder_stateExtension,
        inferPPatFuel_stateExtension,
        inferDPatFuel_stateExtension,
        freshTargets_stateExtension,
        InferState.StateExtension.snd_of_eq,
        InferState.StateExtension.right_congr,
        InferState.StateExtension.refl,
        InferState.StateExtension.trans]

/-- The traversal proof uses the established append-only theorem for its
history component and the core extension induction for the remaining
monotonicity components. -/
theorem inferExprFuel_stateExtension
    {fuel signature context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result) :
    state.StateExtension result.state := by
  let extension := inferExprFuel_stateExtensionCore success
  exact { extension with history := inferExprFuel_historyPrefix success }

/-! ## Public companions of the mutual traversal -/

private theorem checkExprFuel_stateExtensionCore
    {fuel signature context selfEnv path expression expected state result}
    (success : checkExprFuel fuel signature context selfEnv path expression
      expected state = some result) :
    state.StateExtension result := by
  cases fuel with
  | zero => simp [checkExprFuel] at success
  | succ fuel =>
      simp only [checkExprFuel] at success
      cases inferredEq : inferExprFuel fuel signature context selfEnv path
          expression state with
      | none => simp [inferredEq] at success
      | some inferred =>
          simp only [inferredEq] at success
          exact (inferExprFuel_stateExtension inferredEq).trans
            (alignExprResultAtExpected_stateExtension success)

theorem checkExprFuel_stateExtension
    {fuel signature context selfEnv path expression expected state result}
    (success : checkExprFuel fuel signature context selfEnv path expression
      expected state = some result) :
    state.StateExtension result := by
  let extension := checkExprFuel_stateExtensionCore success
  exact { extension with history := checkExprFuel_historyPrefix success }

private theorem checkExprsFuel_stateExtensionCore
    {fuel signature context selfEnv path index expressions expecteds state result}
    (success : checkExprsFuel fuel signature context selfEnv path index
      expressions expecteds state = some result) :
    state.StateExtension result := by
  induction fuel generalizing index expressions expecteds state result with
  | zero => simp [checkExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          cases expecteds with
          | nil =>
              simp only [checkExprsFuel, Option.some.injEq] at success
              subst result
              exact InferState.StateExtension.refl state
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
                  have headExtension := checkExprFuel_stateExtension headEq
                  have tailExtension := induction
                    (index := index + 1) (expressions := expressions)
                    (expecteds := expecteds) (state := middle)
                    (result := result) success
                  exact headExtension.trans tailExtension

theorem checkExprsFuel_stateExtension
    {fuel signature context selfEnv path index expressions expecteds state result}
    (success : checkExprsFuel fuel signature context selfEnv path index
      expressions expecteds state = some result) :
    state.StateExtension result := by
  let extension := checkExprsFuel_stateExtensionCore success
  exact { extension with history := checkExprsFuel_historyPrefix success }

private theorem inferExprsFuel_stateExtensionCore
    {fuel signature context selfEnv path index expressions state result}
    (success : inferExprsFuel fuel signature context selfEnv path index
      expressions state = some result) :
    state.StateExtension result.state := by
  induction fuel generalizing index expressions state result with
  | zero => simp [inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [inferExprsFuel, Option.some.injEq] at success
          subst result
          exact InferState.StateExtension.refl state
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
                  exact (inferExprFuel_stateExtension headEq).trans
                    (induction (index := index + 1)
                      (expressions := expressions) (state := head.state)
                      (result := tail) tailEq)

theorem inferExprsFuel_stateExtension
    {fuel signature context selfEnv path index expressions state result}
    (success : inferExprsFuel fuel signature context selfEnv path index
      expressions state = some result) :
    state.StateExtension result.state := by
  let extension := inferExprsFuel_stateExtensionCore success
  exact { extension with history := inferExprsFuel_historyPrefix success }

private structure PatternStateExtensionAtFuel (fuel : Nat) : Prop where
  one : ∀ {signature context parameters bindings selfEnv path pattern state
      result},
    inferPatternFuel fuel signature context parameters bindings selfEnv path
      pattern state = some result →
    state.StateExtension result.state
  many : ∀ {signature context parameters bindings selfEnv path index patterns
      state result},
    inferPatternsFuel fuel signature context parameters bindings selfEnv path
      index patterns state = some result →
    state.StateExtension result.state

set_option maxHeartbeats 1000000 in
private theorem patternStateExtensionAtFuel
    (fuel : Nat) : PatternStateExtensionAtFuel fuel := by
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
            exact ((InferState.stateExtension_freshCap _ _).trans
              ((InferState.stateExtension_freshTy _ _).trans
                ((InferState.stateExtension_recordEvent _ _).trans
                  ((visit_stateExtension _ _ _).trans
                    (InferState.stateExtension_recordEvent _ _)))))
        | wild =>
            simp only [inferPatternFuel, Option.some.injEq] at success
            subst result
            exact ((InferState.stateExtension_freshCap _ _).trans
              ((InferState.stateExtension_freshTy _ _).trans
                ((InferState.stateExtension_recordEvent _ _).trans
                  ((visit_stateExtension _ _ _).trans
                    (InferState.stateExtension_recordEvent _ _)))))
        | pval expression =>
            simp only [inferPatternFuel] at success
            cases bodyEq : inferExprFuel fuel signature
                (bindings.toContext ++ context) selfEnv (0 :: path) expression
                (visit state .patternValue path) with
            | none => simp [bodyEq] at success
            | some bodyResult =>
                simp [bodyEq] at success
                subst result
                exact (visit_stateExtension state .patternValue path).trans
                  ((inferExprFuel_stateExtension bodyEq).trans
                    ((InferState.stateExtension_freshCap _ _).trans
                      ((InferState.stateExtension_recordEvent _ _).trans
                        (InferState.stateExtension_recordEvent _ _))))
        | embed name =>
            simp only [inferPatternFuel] at success
            cases lookup : parameters.find? name with
            | none => simp [lookup] at success
            | some dual =>
                simp [lookup] at success
                subst result
                exact (visit_stateExtension state .patternEmbed path).trans
                  (InferState.stateExtension_recordEvent _ _)
        | ptuple patterns =>
            simp only [inferPatternFuel] at success
            cases childrenEq : inferPatternsFuel fuel signature context
                parameters bindings selfEnv path 0 patterns
                (visit state .patternTuple path) with
            | none => simp [childrenEq] at success
            | some children =>
                simp [childrenEq] at success
                subst result
                exact (visit_stateExtension state .patternTuple path).trans
                  ((ih.many childrenEq).trans
                    (InferState.stateExtension_recordEvent _ _))
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
                dsimp only at success
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
                        cases capabilityEq : solvePatternCtorCapability
                            signature entry
                            (freshOrigin .pattern path
                              "pattern-constructor-capability")
                            (children.duals.map Dual.cap) aligned with
                        | none =>
                            rw [capabilityEq] at success <;> contradiction
                        | some solved =>
                            rcases solved with ⟨capability, solvedState⟩
                            rw [capabilityEq] at success
                            try simp only at success
                            split at success
                            · simp only [Option.some.injEq] at success
                              subst result
                              let exportPayload := capabilityExportPayload
                                [capability]
                                (resultTarget ::
                                  children.bindings.map fun entry => entry.2)
                              let frozenState :=
                                solvedState.freezeCapabilityExport
                                  (freshCapImages state.supply
                                    entry.scheme.capBinders)
                                  exportPayload
                              have frozenExtension :
                                  solvedState.StateExtension frozenState := by
                                exact
                                  InferState.stateExtension_freezeCapabilityExport
                                    solvedState
                                    (freshCapImages state.supply
                                      entry.scheme.capBinders)
                                    exportPayload
                              have finishedExtension :
                                  solvedState.StateExtension
                                    ((frozenState.recordEvent
                                      (.patternCtorCompatibility
                                        frozenState.trace.solves.length name
                                        (children.duals.map Dual.cap)
                                        capability)).recordEvent
                                      (.inferredPattern (.pctor name patterns)
                                        ⟨capability, resultTarget⟩
                                        children.bindings path)) := by
                                exact frozenExtension.trans
                                  ((InferState.stateExtension_recordEvent
                                    _ _).trans
                                    (InferState.stateExtension_recordEvent _ _))
                              exact
                                (instantiateCtorInState_stateExtension_of_eq
                                  instEq).trans
                                ((visit_stateExtension instState .patternCtor
                                  path).trans
                                  ((ih.many childrenEq).trans
                                    ((alignPatternTargets_stateExtension
                                      alignmentEq).trans
                                      ((solvePatternCtorCapability_stateExtension
                                        capabilityEq).trans
                                        finishedExtension))))
                            · contradiction
        | pand left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternAnd path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context
                    parameters leftResult.bindings selfEnv (1 :: path) right
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
                        exact (visit_stateExtension state .patternAnd path).trans
                          ((ih.one leftEq).trans
                            ((ih.one rightEq).trans
                              ((alignDuals_stateExtension alignmentEq).trans
                                (InferState.stateExtension_recordEvent _ _))))
        | por left right =>
            simp only [inferPatternFuel] at success
            cases leftEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (0 :: path) left
                (visit state .patternOr path) with
            | none => simp [leftEq] at success
            | some leftResult =>
                cases rightEq : inferPatternFuel fuel signature context
                    parameters bindings selfEnv (1 :: path) right
                    leftResult.state with
                | none => simp [leftEq, rightEq] at success
                | some rightResult =>
                    cases alignmentEq : alignDuals rightResult.state
                        (freshOrigin .pattern path "pattern-or")
                        leftResult.dual rightResult.dual with
                    | none => simp [leftEq, rightEq, alignmentEq] at success
                    | some aligned =>
                        cases bindingsEq : alignBindings aligned
                            (freshOrigin .pattern path "pattern-or-bindings")
                            leftResult.bindings rightResult.bindings with
                        | none =>
                            simp [leftEq, rightEq, alignmentEq, bindingsEq]
                              at success
                        | some alignedBindings =>
                            simp [leftEq, rightEq, alignmentEq, bindingsEq]
                              at success
                            subst result
                            exact (visit_stateExtension state .patternOr
                                path).trans
                              ((ih.one leftEq).trans
                                ((ih.one rightEq).trans
                                  ((alignDuals_stateExtension
                                      alignmentEq).trans
                                    ((alignBindings_stateExtension
                                        bindingsEq).trans
                                      (InferState.stateExtension_recordEvent
                                        _ _)))))
        | papp name patterns =>
            simp only [inferPatternFuel] at success
            cases lookup : signature.findPatternFun name with
            | none => simp [lookup] at success
            | some scheme =>
                simp only [lookup] at success
                let normalizedContext := context.applySubst state.prevailing
                let normalizedParameters :=
                  parameters.applySubst state.prevailing
                let normalizedBindings :=
                  bindings.applySubst state.prevailing
                generalize instEq : instantiateDualInState signature context
                    parameters bindings normalizedContext normalizedParameters
                    normalizedBindings state scheme = instantiation at success
                rcases instantiation with ⟨⟨expectedArgs, resultDual⟩,
                  instState⟩
                dsimp [normalizedContext, normalizedParameters,
                  normalizedBindings] at instEq
                dsimp only at success
                cases childrenEq : inferPatternsFuel fuel signature context
                    parameters bindings selfEnv path 0 patterns
                    (visit instState .patternApp path) with
                | none => simp [childrenEq] at success
                | some children =>
                    simp only [childrenEq] at success
                    cases alignmentEq : alignDualLists children.state
                        (freshOrigin .pattern path
                          "pattern-function-arguments")
                        children.duals expectedArgs with
                    | none => simp [alignmentEq] at success
                    | some aligned =>
                        simp only [alignmentEq] at success
                        simp only [Option.some.injEq] at success
                        subst result
                        exact
                          (instantiateDualInState_stateExtension_of_eq
                            instEq).trans
                          ((visit_stateExtension instState .patternApp
                            path).trans
                            ((ih.many childrenEq).trans
                              ((alignDualLists_stateExtension
                                alignmentEq).trans
                                (InferState.stateExtension_recordEvent _ _))))
      · intro signature context parameters bindings selfEnv path index patterns
          state result success
        cases patterns with
        | nil =>
            simp only [inferPatternsFuel, Option.some.injEq] at success
            subst result
            exact InferState.StateExtension.refl state
        | cons pattern patterns =>
            simp only [inferPatternsFuel] at success
            cases headEq : inferPatternFuel fuel signature context parameters
                bindings selfEnv (index :: path) pattern state with
            | none => simp [headEq] at success
            | some head =>
                cases tailEq : inferPatternsFuel fuel signature context
                    parameters head.bindings selfEnv path (index + 1) patterns
                    head.state with
                | none => simp [headEq, tailEq] at success
                | some tail =>
                    simp [headEq, tailEq] at success
                    subst result
                    exact (ih.one headEq).trans
                      (ih.many (result := tail) tailEq)

theorem inferPatternFuel_stateExtension
    {fuel signature context parameters bindings selfEnv path pattern state result}
    (success : inferPatternFuel fuel signature context parameters bindings
      selfEnv path pattern state = some result) :
    state.StateExtension result.state := by
  let extension := (patternStateExtensionAtFuel fuel).one success
  exact { extension with history := inferPatternFuel_historyPrefix success }

theorem inferPatternsFuel_stateExtension
    {fuel signature context parameters bindings selfEnv path index patterns state
      result}
    (success : inferPatternsFuel fuel signature context parameters bindings
      selfEnv path index patterns state = some result) :
    state.StateExtension result.state := by
  let extension := (patternStateExtensionAtFuel fuel).many success
  exact { extension with history := inferPatternsFuel_historyPrefix success }

private theorem checkArmsFuel_stateExtensionCore
    {fuel signature context selfEnv bindings path index arms target bodyTarget
      state result}
    (success : checkArmsFuel fuel signature context selfEnv bindings path index
      arms target bodyTarget state = some result) :
    state.StateExtension result := by
  induction fuel generalizing index arms state result with
  | zero => simp [checkArmsFuel] at success
  | succ fuel induction =>
      cases arms with
      | nil =>
          simp only [checkArmsFuel, Option.some.injEq] at success
          subst result
          exact InferState.StateExtension.refl state
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
                    exact (inferDPatFuel_stateExtension dataEq).trans
                      ((checkExprFuel_stateExtension bodyEq).trans
                        (induction (index := index + 1) (arms := arms)
                          (state := middle) (result := result) tailSuccess))
              · rw [if_neg distinct] at success
                contradiction

theorem checkArmsFuel_stateExtension
    {fuel signature context selfEnv bindings path index arms target bodyTarget
      state result}
    (success : checkArmsFuel fuel signature context selfEnv bindings path index
      arms target bodyTarget state = some result) :
    state.StateExtension result := by
  let extension := checkArmsFuel_stateExtensionCore success
  exact { extension with history := checkArmsFuel_historyPrefix success }

private theorem inferClauseFuel_stateExtensionCore
    {fuel signature context selfEnv path clause target state result}
    (success : inferClauseFuel fuel signature context selfEnv path clause target
      state = some result) :
    state.StateExtension result.state := by
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
          | none => simp [nextEq] at success
          | some nextMatchers =>
              simp only [nextEq] at success
              cases nextMatchersEq : checkExprsFuel fuel signature context
                  selfEnv (1 :: path) 0 nextMatchers
                  (ppResult.holes.map fun hole =>
                    Ty.slot hole.cap hole.target)
                  ppResult.state with
              | none => simp [nextMatchersEq] at success
              | some middle =>
                  simp [nextMatchersEq] at success
                  cases armsEq : checkArmsFuel fuel signature context selfEnv
                      ppResult.bindings (2 :: path) 0 arms target
                      (Ty.listT (prodTy (ppResult.holes.map Dual.target)))
                      middle with
                  | none => simp [armsEq] at success
                  | some final =>
                      simp only [armsEq] at success
                      have resultStateEq : final = result.state :=
                        congrArg ClauseResult.state (Option.some.inj success)
                      exact ((visit_stateExtension state .clause path).trans
                        ((inferPPatFuel_stateExtension ppEq).trans
                          ((checkExprsFuel_stateExtension
                            nextMatchersEq).trans
                            (checkArmsFuel_stateExtension armsEq)))).right_congr
                              resultStateEq

theorem inferClauseFuel_stateExtension
    {fuel signature context selfEnv path clause target state result}
    (success : inferClauseFuel fuel signature context selfEnv path clause target
      state = some result) :
    state.StateExtension result.state := by
  let extension := inferClauseFuel_stateExtensionCore success
  exact { extension with history := inferClauseFuel_historyPrefix success }

private theorem inferClausesFuel_stateExtensionCore
    {fuel signature context selfEnv path index clauses target state result}
    (success : inferClausesFuel fuel signature context selfEnv path index clauses
      target state = some result) :
    state.StateExtension result.state := by
  induction fuel generalizing index clauses state result with
  | zero => simp [inferClausesFuel] at success
  | succ fuel induction =>
      cases clauses with
      | nil =>
          simp only [inferClausesFuel, Option.some.injEq] at success
          subst result
          exact InferState.StateExtension.refl state
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
                  exact (inferClauseFuel_stateExtension headEq).trans
                    (induction (index := index + 1) (clauses := clauses)
                      (state := head.state) (result := tail) tailEq)

theorem inferClausesFuel_stateExtension
    {fuel signature context selfEnv path index clauses target state result}
    (success : inferClausesFuel fuel signature context selfEnv path index clauses
      target state = some result) :
    state.StateExtension result.state := by
  let extension := inferClausesFuel_stateExtensionCore success
  exact { extension with history := inferClausesFuel_historyPrefix success }

private theorem inferMatcherFuel_stateExtensionCore
    {fuel signature context selfEnv path clauses state result}
    (success : inferMatcherFuel fuel signature context selfEnv path clauses
      state = some result) :
    state.StateExtension result.state := by
  cases fuel with
  | zero => simp [inferMatcherFuel] at success
  | succ fuel =>
      simp only [inferMatcherFuel] at success
      generalize freshEq : state.freshTy
          (freshOrigin .matcherClause path "matcher-target") = fresh at success
      rcases fresh with ⟨target, freshState⟩
      cases clausesEq : inferClausesFuel fuel signature context selfEnv path 0
          clauses target freshState with
      | none => simp [clausesEq] at success
      | some clausesResult =>
          simp only [clausesEq] at success
          cases evidenceEq : collectClauseEvidence signature.toMatcherSig
              clauses
              (clausesResult.rawHoleLists.map fun holes =>
                (holes.map
                  (Dual.applySubst clausesResult.state.prevailing)).map
                    Dual.cap) with
          | none =>
              rw [evidenceEq] at success
              contradiction
          | some evidence =>
              rw [evidenceEq] at success
              cases shapeEq : Shape.inferShape signature.observability evidence
                  with
              | none => simp [shapeEq] at success
              | some capability =>
                  try simp only [shapeEq] at success
                  split at success
                  · simp only [Option.some.injEq] at success
                    subst result
                    have freshExtension : state.StateExtension freshState :=
                      InferState.StateExtension.snd_of_eq
                        (InferState.stateExtension_freshTy state
                          (freshOrigin .matcherClause path "matcher-target"))
                        freshEq
                    exact freshExtension.trans
                      ((inferClausesFuel_stateExtension clausesEq).trans
                        ((InferState.stateExtension_recordEvent _ _).trans
                          ((InferState.stateExtension_recordEvent _ _).trans
                            (InferState.stateExtension_protectMatcherCapabilityExcept
                              _ _ _))))
                  · contradiction

theorem inferMatcherFuel_stateExtension
    {fuel signature context selfEnv path clauses state result}
    (success : inferMatcherFuel fuel signature context selfEnv path clauses
      state = some result) :
    state.StateExtension result.state := by
  let extension := inferMatcherFuel_stateExtensionCore success
  exact { extension with history := inferMatcherFuel_historyPrefix success }

/-! ## Complete raw inference -/

/-- The terminal producer-protection audit is a filter, so a successful audit
returns the same state. -/
theorem enforceProtectedResult_stateExtension
    {input output : ExprResult}
    (success : enforceProtectedResult input = some output) :
    input.state.StateExtension output.state := by
  have equality : input = output :=
    (enforceProtectedResult_sound success).1
  exact (InferState.StateExtension.refl input.state).right_congr
    (congrArg ExprResult.state equality)

theorem inferRaw_stateExtension
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : inferRaw signature context expression = some result) :
    (initialState signature context).StateExtension result.state := by
  unfold inferRaw at success
  cases core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) with
  | none => simp [core] at success
  | some raw =>
      have guarded : enforceProtectedResult raw = some result := by
        simpa [core] using success
      exact (inferExprFuel_stateExtension core).trans
        (enforceProtectedResult_stateExtension guarded)

end TypePM.Inference
