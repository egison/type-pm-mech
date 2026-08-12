import TypePM.Reconstruction
import TypePM.SchemeEquality
import TypePM.SchemeOpeningLists

/-!
# Executable audits for reconstruction bridge conditions

The raw reconstruction theorem accepts an algebraic `WBridgeWF` certificate;
the public executable inference entry point runs this module's finite
validator and constructs that certificate internally.  The checks never
store or consume a source typing derivation.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-! ## A variable-capability declarative view of a solver suffix -/

/-- Retain a terminal capability image exactly when it is a variable; on an
unrelated structurally specialized variable, use identity.  This projection
accepts safe alpha-renaming while remaining globally variable-valued. -/
def terminalVariableCapCandidate
    (steps : List SolveStep) : CapSubst :=
  fun varId =>
    match (replay steps).cap varId with
    | .var image => .var image
    | _ => .var varId

/-- Canonical variable-valued post selected by the finite slot checker.
Target specialization is replayed completely; capability specialization is
projected to its variable-valued fragment. -/
def terminalVariableReplay (steps : List SolveStep) : Subst :=
  Subst.mk (terminalVariableCapCandidate steps) (replay steps).target

theorem terminalVariableReplay_variable (steps : List SolveStep) :
    VariablePost (terminalVariableReplay steps) := by
  constructor
  intro varId
  change ∃ image,
    terminalVariableCapCandidate steps varId = .var image
  unfold terminalVariableCapCandidate
  cases equation : (replay steps).cap varId with
  | var image => exact ⟨image, rfl⟩
  | any => exact ⟨varId, rfl⟩
  | skolem name => exact ⟨varId, rfl⟩
  | con name children => exact ⟨varId, rfl⟩
  | prod children => exact ⟨varId, rfl⟩

/-! ## Terminal fresh-instance reconstruction -/

/-- Binder-local capability candidate obtained by replaying the fresh image
allocated from an event's incoming supply. -/
def terminalCapCandidate
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List CapVar) : CapSubst :=
  fun varId =>
    if varId ∈ binders then
      state.prevailing.cap ⟨supply.nextCap + varId.id⟩
    else
      .var varId

/-- Binder-local target candidate obtained from the corresponding fresh
ordinary image. -/
def terminalTyCandidate
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List TypePM.TyVar) : TySubst :=
  fun varId =>
    if varId ∈ binders then
      state.prevailing.apply (.var (supply.nextTy + varId))
    else
      .var varId

theorem terminalCapCandidate_support
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List CapVar) :
    (terminalCapCandidate state supply binders).SupportWithin binders := by
  intro varId outside
  simp [terminalCapCandidate, outside]

theorem terminalTyCandidate_support
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List TypePM.TyVar) :
    (terminalTyCandidate state supply binders).SupportWithin binders := by
  intro varId outside
  simp [terminalTyCandidate, outside]

def capBinderImagesVariableCheck
    (binders : List CapVar) (substitution : CapSubst) : Bool :=
  binders.all fun varId =>
    match substitution varId with
    | .var _ => true
    | _ => false

theorem capBinderImagesVariableCheck_sound
    {binders : List CapVar} {substitution : CapSubst}
    (checked : capBinderImagesVariableCheck binders substitution = true) :
    ∀ varId, varId ∈ binders →
      ∃ image, substitution varId = .var image := by
  intro varId membership
  have accepted := List.all_eq_true.mp checked varId membership
  cases equation : substitution varId with
  | var image => exact ⟨image, rfl⟩
  | _ => simp [equation] at accepted

theorem capBinderImagesVariableCheck_complete
    {binders : List CapVar} {substitution : CapSubst}
    (variables : ∀ varId, varId ∈ binders ->
      ∃ image, substitution varId = .var image) :
    capBinderImagesVariableCheck binders substitution = true := by
  unfold capBinderImagesVariableCheck
  apply List.all_eq_true.mpr
  intro varId membership
  rcases variables varId membership with ⟨image, equation⟩
  simp [equation]

/-- Terminal variable selected for one canonical capability-binder position.
The surrounding executable check guarantees that the default branch is never
used by a successful certificate. -/
def terminalSchemeCapImage
    (state : InferState) (supply : InferenceBase.FreshSupply)
    {scheme : Scheme} (index : Fin scheme.capArity) : CapVar :=
  match state.prevailing.cap
      ((Scheme.canonicalFreshOpening supply scheme).capImage index) with
  | .var image => image
  | _ => (Scheme.canonicalFreshOpening supply scheme).capImage index

/-- Canonical expression-scheme opening transported to the terminal cut. -/
def terminalSchemeOpening
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) : scheme.ValueOpening where
  capImage := terminalSchemeCapImage state supply
  tyImage := fun index => state.prevailing.apply (.var
    ((Scheme.canonicalFreshOpening supply scheme).tyImage index))

private def instanceSuffixEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .schemeInstantiation solveCount supply _scheme name rawContext _context
      _fixedCaps _fixedTys _reservedCaps _reservedTys fresh _capImages
      _tyImages =>
      decide (solveCount ≤ state.trace.solves.length) &&
      match (rawContext.applySubst state.prevailing).find? name with
      | none => false
      | some terminalScheme =>
          capBinderImagesVariableCheck
            (Scheme.canonicalCapImages supply terminalScheme)
            state.prevailing.cap &&
          decide (terminalScheme.openValue
              (terminalSchemeOpening state supply terminalScheme) =
            state.prevailing.apply fresh)
  | .ctorInstantiation solveCount supply scheme args result _capImages =>
      let C := terminalCapCandidate state supply scheme.capBinders
      let T := terminalTyCandidate state supply scheme.tyBinders
      decide (solveCount ≤ state.trace.solves.length) &&
      decide (scheme.args.map (Subst.mk C T).apply =
        args.map state.prevailing.apply) &&
      decide ((Subst.mk C T).apply scheme.result =
        state.prevailing.apply result)
  | .dualInstantiation solveCount supply scheme _rawContext _rawParameters
      _rawBindings _context _parameters _bindings _fixedCaps _fixedTys
      _reservedCaps _reservedTys args result _capImages _tyImages =>
      let C := terminalCapCandidate state supply scheme.capBinders
      let T := terminalTyCandidate state supply scheme.tyBinders
      decide (solveCount ≤ state.trace.solves.length) &&
      capBinderImagesVariableCheck scheme.capBinders C &&
      decide (scheme.args.map (Dual.apply C T) =
        args.map (Dual.applySubst state.prevailing)) &&
      decide (scheme.result.apply C T = result.applySubst state.prevailing)
  | _ => true

def traceInstanceSuffixCheck (state : InferState) : Bool :=
  state.trace.events.all (instanceSuffixEventCheck state)

theorem traceInstanceSuffixCheck_sound
    {signature : FrozenSig} {state : InferState}
    (checked : traceInstanceSuffixCheck state = true) :
    TraceInstanceSuffixConditions signature state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  cases event with
  | schemeInstantiation solveCount supply scheme name rawContext context
      fixedCaps fixedTys reservedCaps reservedTys fresh capImages tyImages =>
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq] at eventChecked
      rcases eventChecked with ⟨solveBound, terminalChecked⟩
      cases lookup : (rawContext.applySubst state.prevailing).find? name with
      | none => simp [lookup] at terminalChecked
      | some terminalScheme =>
          simp only [lookup, Bool.and_eq_true, decide_eq_true_eq] at terminalChecked
          refine ⟨solveBound, terminalScheme, lookup,
            terminalSchemeOpening state supply terminalScheme, ?_⟩
          exact terminalChecked.2
  | ctorInstantiation solveCount supply scheme args result capImages =>
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq] at eventChecked
      rcases eventChecked with ⟨⟨solveBound, argsEq⟩, resultEq⟩
      let C := terminalCapCandidate state supply scheme.capBinders
      let T := terminalTyCandidate state supply scheme.tyBinders
      exact ⟨solveBound, C, T,
        terminalCapCandidate_support state supply _,
        terminalTyCandidate_support state supply _, argsEq, resultEq⟩
  | dualInstantiation solveCount supply scheme rawContext rawParameters
      rawBindings context parameters bindings fixedCaps fixedTys reservedCaps
      reservedTys args result capImages tyImages =>
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨solveBound, capVariables⟩, argsEq⟩, resultEq⟩
      let C := terminalCapCandidate state supply scheme.capBinders
      let T := terminalTyCandidate state supply scheme.tyBinders
      refine ⟨solveBound, C, T, ?_⟩
      exact
        { capSupport := terminalCapCandidate_support state supply _
          tySupport := terminalTyCandidate_support state supply _
          capBinderVariable :=
            capBinderImagesVariableCheck_sound capVariables
          argsResult := argsEq
          resultResult := resultEq }
  | _ => trivial

/-- The canonical terminal witnesses selected by
`traceInstanceSuffixCheck`.  This is intentionally stronger than
`TraceInstanceSuffixConditions`: completeness must show that the recorded
fresh opening itself, after terminal replay, is a valid witness. -/
def CanonicalTraceInstanceSuffixConditions
    (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .schemeInstantiation solveCount supply _scheme name rawContext _context
        _fixedCaps _fixedTys _reservedCaps _reservedTys fresh _capImages
        _tyImages =>
        solveCount ≤ state.trace.solves.length ∧
        ∃ terminalScheme,
          (rawContext.applySubst state.prevailing).find? name =
              some terminalScheme ∧
          (∀ varId,
            varId ∈ Scheme.canonicalCapImages supply terminalScheme ->
            ∃ image, state.prevailing.cap varId = .var image) ∧
          terminalScheme.openValue
              (terminalSchemeOpening state supply terminalScheme) =
            state.prevailing.apply fresh
    | .ctorInstantiation solveCount supply scheme args result _capImages =>
        solveCount ≤ state.trace.solves.length ∧
        let C := terminalCapCandidate state supply scheme.capBinders
        let T := terminalTyCandidate state supply scheme.tyBinders
        scheme.args.map (Subst.mk C T).apply =
            args.map state.prevailing.apply ∧
          (Subst.mk C T).apply scheme.result =
            state.prevailing.apply result
    | .dualInstantiation solveCount supply scheme _rawContext _rawParameters
        _rawBindings _context _parameters _bindings _fixedCaps _fixedTys
        _reservedCaps _reservedTys args result _capImages _tyImages =>
        solveCount ≤ state.trace.solves.length ∧
        let C := terminalCapCandidate state supply scheme.capBinders
        let T := terminalTyCandidate state supply scheme.tyBinders
        (∀ varId, varId ∈ scheme.capBinders ->
          ∃ image, C varId = .var image) ∧
        scheme.args.map (Dual.apply C T) =
            args.map (Dual.applySubst state.prevailing) ∧
          scheme.result.apply C T = result.applySubst state.prevailing
    | _ => True

theorem traceInstanceSuffixCheck_complete
    {state : InferState}
    (conditions : CanonicalTraceInstanceSuffixConditions state) :
    traceInstanceSuffixCheck state = true := by
  unfold traceInstanceSuffixCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | schemeInstantiation solveCount supply scheme name rawContext context
      fixedCaps fixedTys reservedCaps reservedTys fresh capImages tyImages =>
      rcases accepted with
        ⟨bound, terminalScheme, lookup, capVariables, terminalEq⟩
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨bound, ?_⟩
      simp only [lookup, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨capBinderImagesVariableCheck_complete capVariables,
        terminalEq⟩
  | ctorInstantiation solveCount supply scheme args result capImages =>
      dsimp only at accepted
      rcases accepted with ⟨bound, argsEq, resultEq⟩
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨bound, argsEq⟩, resultEq⟩
  | dualInstantiation solveCount supply scheme rawContext rawParameters
      rawBindings context parameters bindings fixedCaps fixedTys reservedCaps
      reservedTys args result capImages tyImages =>
      dsimp only at accepted
      rcases accepted with ⟨bound, capVariables, argsEq, resultEq⟩
      simp only [instanceSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨bound,
        capBinderImagesVariableCheck_complete capVariables⟩, argsEq⟩,
        resultEq⟩
  | _ => rfl

/-! ## Ordinary and dual terminal equalities -/

private def typeAlignmentEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .typeAlignment start stop rawLeft rawRight localLeft localRight =>
      decide (start ≤ stop) &&
      decide (stop ≤ state.trace.solves.length) &&
      decide (localLeft =
        (replay (state.trace.solves.take start)).apply rawLeft) &&
      decide (localRight =
        (replay (state.trace.solves.take start)).apply rawRight) &&
      decide (state.prevailing.apply rawLeft =
        state.prevailing.apply rawRight)
  | _ => true

def traceTypeAlignmentCheck (state : InferState) : Bool :=
  state.trace.events.all (typeAlignmentEventCheck state)

theorem traceTypeAlignmentCheck_sound
    {state : InferState} (checked : traceTypeAlignmentCheck state = true) :
    TraceTypeAlignmentConditions state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  cases event with
  | typeAlignment start stop rawLeft rawRight localLeft localRight =>
      simp only [typeAlignmentEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨⟨startStop, stopBound⟩, localLeftEq⟩, localRightEq⟩, finalEq⟩
      exact ⟨startStop, stopBound, localLeftEq, localRightEq, finalEq⟩
  | _ => trivial

/-- The semantic ordinary-alignment conditions are exactly sufficient for
the corresponding finite event check. -/
theorem traceTypeAlignmentCheck_complete
    {state : InferState}
    (conditions : TraceTypeAlignmentConditions state) :
    traceTypeAlignmentCheck state = true := by
  unfold traceTypeAlignmentCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event <;> simp_all [typeAlignmentEventCheck]

private def dualAlignmentEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .dualAlignment start stop rawLeft rawRight localLeft localRight =>
      decide (start ≤ stop) &&
      decide (stop ≤ state.trace.solves.length) &&
      decide (localLeft = rawLeft.applySubst
        (replay (state.trace.solves.take start))) &&
      decide (localRight = rawRight.applySubst
        (replay (state.trace.solves.take start))) &&
      decide (rawLeft.applySubst state.prevailing =
        rawRight.applySubst state.prevailing)
  | _ => true

def traceDualAlignmentCheck (state : InferState) : Bool :=
  state.trace.events.all (dualAlignmentEventCheck state)

theorem traceDualAlignmentCheck_sound
    {state : InferState} (checked : traceDualAlignmentCheck state = true) :
    TraceDualAlignmentConditions state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  cases event with
  | dualAlignment start stop rawLeft rawRight localLeft localRight =>
      simp only [dualAlignmentEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨⟨startStop, stopBound⟩, localLeftEq⟩, localRightEq⟩, finalEq⟩
      exact ⟨startStop, stopBound, localLeftEq, localRightEq, finalEq⟩
  | _ => trivial

/-- The semantic dual-alignment conditions are exactly sufficient for the
corresponding finite event check. -/
theorem traceDualAlignmentCheck_complete
    {state : InferState}
    (conditions : TraceDualAlignmentConditions state) :
    traceDualAlignmentCheck state = true := by
  unfold traceDualAlignmentCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event <;> simp_all [dualAlignmentEventCheck]

/-! ## Expected-type slot alignments -/

private def slotAlignmentAtTerminalCheck
    (localSteps terminalSteps : List SolveStep)
    (inferred requested : Ty) : Bool :=
  if decide
      (applyDeltas terminalSteps inferred =
        applyDeltas terminalSteps requested) then
    true
  else
    match inferred, requested, localSteps with
    | .matcher producerCap producerTarget,
        .slot consumerCap consumerTarget, [step] =>
        let suffix := terminalSteps.tail
        let post := terminalVariableReplay suffix
        match step.constraint with
        | .producerToSlot rawProducerCap rawProducerTarget rawConsumerCap
            rawConsumerTarget =>
            decide (rawProducerCap = producerCap) &&
            decide (rawProducerTarget = producerTarget) &&
            decide (rawConsumerCap = consumerCap) &&
            decide (rawConsumerTarget = consumerTarget) &&
            rangeFixedOnCheck step.delta step.targetDomain &&
            decide
              (applyDeltas terminalSteps
                  (.matcher producerCap producerTarget) =
                post.apply
                  (.matcher (producerCap.apply step.delta.cap)
                    (step.delta.apply producerTarget))) &&
            decide
              (applyDeltas terminalSteps
                  (.slot consumerCap consumerTarget) =
                post.apply
                  (.slot (consumerCap.apply step.delta.cap)
                    (step.delta.apply consumerTarget)))
        | _ => false
    | _, _, _ => false

/-- Exact terminal witness selected by the executable slot checker.  Unlike
the reconstruction-facing `SlotAlignmentAtTerminal`, the coercion branch
fixes its suffix witness to `terminalVariableReplay terminalSteps.tail`. -/
inductive CanonicalSlotAlignmentAtTerminal
    (localSteps terminalSteps : List SolveStep)
    (inferred requested : Ty) : Prop where
  | equal
      (aligned : applyDeltas terminalSteps inferred =
        applyDeltas terminalSteps requested) :
      CanonicalSlotAlignmentAtTerminal localSteps terminalSteps inferred
        requested
  | matcherToSlot
      {producerCap consumerCap : Cap}
      {producerTarget consumerTarget : Ty} {step : SolveStep}
      (inferredEq : inferred = .matcher producerCap producerTarget)
      (requestedEq : requested = .slot consumerCap consumerTarget)
      (localEq : localSteps = [step])
      (constraintEq : step.constraint = .producerToSlot producerCap
        producerTarget consumerCap consumerTarget)
      (rangeFixed : step.delta.RangeFixed)
      (producerResult :
        applyDeltas terminalSteps (.matcher producerCap producerTarget) =
          (terminalVariableReplay terminalSteps.tail).apply
            (.matcher (producerCap.apply step.delta.cap)
              (step.delta.apply producerTarget)))
      (consumerResult :
        applyDeltas terminalSteps (.slot consumerCap consumerTarget) =
          (terminalVariableReplay terminalSteps.tail).apply
            (.slot (consumerCap.apply step.delta.cap)
              (step.delta.apply consumerTarget))) :
      CanonicalSlotAlignmentAtTerminal localSteps terminalSteps inferred
        requested

theorem slotAlignmentAtTerminalCheck_complete
    {localSteps terminalSteps : List SolveStep}
    {inferred requested : Ty}
    (conditions : CanonicalSlotAlignmentAtTerminal localSteps terminalSteps
      inferred requested) :
    slotAlignmentAtTerminalCheck localSteps terminalSteps inferred requested =
      true := by
  cases conditions with
  | equal aligned =>
      simp [slotAlignmentAtTerminalCheck, aligned]
  | @matcherToSlot producerCap consumerCap producerTarget consumerTarget step
      inferredEq requestedEq localEq constraintEq rangeFixed producerResult
      consumerResult =>
      subst inferred
      subst requested
      rw [localEq]
      by_cases aligned :
          applyDeltas terminalSteps (.matcher producerCap producerTarget) =
            applyDeltas terminalSteps (.slot consumerCap consumerTarget)
      · simp [slotAlignmentAtTerminalCheck, aligned]
      · simp [slotAlignmentAtTerminalCheck, constraintEq,
          rangeFixedOnCheck_complete rangeFixed, producerResult,
          consumerResult]

private theorem solveStep_producerToSlot_raw
    {step : SolveStep} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (constraintEq : step.constraint = .producerToSlot producerCap
      producerTarget consumerCap consumerTarget)
    (rangeFixed : step.delta.RangeFixed) :
    ∃ bindings, MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings step.delta.cap step.delta.target := by
  rcases step with
    ⟨solveCount, origin, ledgerSnapshot, constraint, delta, targetDomain, targetSupport,
      certificate, locallySound⟩
  dsimp only at constraintEq rangeFixed ⊢
  subst constraint
  cases certificate with
  | producerToSlot matched unified =>
      exact ⟨_, matched, rfl, unified, rangeFixed⟩

private theorem slotAlignmentAtTerminalCheck_sound
    {localSteps terminalSteps : List SolveStep}
    {inferred requested : Ty}
    (checked : slotAlignmentAtTerminalCheck localSteps
      terminalSteps inferred requested = true) :
    SlotAlignmentAtTerminal localSteps terminalSteps inferred requested := by
  by_cases aligned :
      applyDeltas terminalSteps inferred = applyDeltas terminalSteps requested
  · exact .equal aligned
  · cases inferred <;>
      try { simp [slotAlignmentAtTerminalCheck, aligned] at checked }
    case matcher producerCap producerTarget =>
      cases requested <;>
        try { simp [slotAlignmentAtTerminalCheck, aligned] at checked }
      case slot consumerCap consumerTarget =>
        cases localSteps with
        | nil =>
            simp [slotAlignmentAtTerminalCheck, aligned] at checked
        | cons step rest =>
            cases rest with
            | cons next tail =>
                simp [slotAlignmentAtTerminalCheck, aligned] at checked
            | nil =>
                cases constraintForm : step.constraint with
                | capEq left right =>
                    simp [slotAlignmentAtTerminalCheck, aligned,
                      constraintForm] at checked
                | targetEq left right =>
                    simp [slotAlignmentAtTerminalCheck, aligned,
                      constraintForm] at checked
                | producerToSlot rawProducerCap rawProducerTarget
                    rawConsumerCap rawConsumerTarget =>
                    simp [slotAlignmentAtTerminalCheck, aligned,
                      constraintForm] at checked
                    rcases checked with
                      ⟨⟨⟨⟨⟨⟨producerCapEq, producerTargetEq⟩,
                        consumerCapEq⟩, consumerTargetEq⟩, rangeChecked⟩,
                        producerResult⟩, consumerResult⟩
                    subst rawProducerCap
                    subst rawProducerTarget
                    subst rawConsumerCap
                    subst rawConsumerTarget
                    let suffix := terminalSteps.tail
                    let post := terminalVariableReplay suffix
                    have postVariable : VariablePost post :=
                      terminalVariableReplay_variable suffix
                    have rangeFixed : step.delta.RangeFixed :=
                      rangeFixedOnCheck_sound step.targetSupport rangeChecked
                    rcases solveStep_producerToSlot_raw constraintForm
                        rangeFixed with ⟨bindings, raw⟩
                    exact .matcherToSlot rfl rfl rfl constraintForm rfl raw
                      postVariable producerResult consumerResult

private def slotAlignmentEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .slotAlignment start stop inferred requested =>
      decide (start ≤ stop) &&
      decide (stop ≤ state.trace.solves.length) &&
      slotAlignmentAtTerminalCheck
        (solveSlice state.trace start stop)
        (solveSlice state.trace start state.trace.solves.length)
        inferred requested
  | _ => true

def traceSlotAlignmentCheck (state : InferState) : Bool :=
  state.trace.events.all (slotAlignmentEventCheck state)

theorem traceSlotAlignmentCheck_sound
    {state : InferState} (checked : traceSlotAlignmentCheck state = true) :
    TraceSlotAlignmentConditions state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  cases event with
  | slotAlignment start stop inferred requested =>
      simp only [slotAlignmentEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with ⟨⟨startStop, stopBound⟩, finalChecked⟩
      refine ⟨startStop, stopBound, ?_⟩
      exact slotAlignmentAtTerminalCheck_sound
        (localSteps := solveSlice state.trace start stop)
        (terminalSteps := solveSlice state.trace start state.trace.solves.length)
        (inferred := inferred) (requested := requested) finalChecked
  | _ => trivial

/-- Every recorded expected-type cut has the canonical terminal witness used
by the finite validator. -/
def CanonicalTraceSlotAlignmentConditions (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .slotAlignment start stop inferred requested =>
        start ≤ stop ∧ stop ≤ state.trace.solves.length ∧
        CanonicalSlotAlignmentAtTerminal
          (solveSlice state.trace start stop)
          (solveSlice state.trace start state.trace.solves.length)
          inferred requested
    | _ => True

theorem traceSlotAlignmentCheck_complete
    {state : InferState}
    (conditions : CanonicalTraceSlotAlignmentConditions state) :
    traceSlotAlignmentCheck state = true := by
  unfold traceSlotAlignmentCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | slotAlignment start stop inferred requested =>
      rcases accepted with ⟨startStop, stopBound, terminal⟩
      simp only [slotAlignmentEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨startStop, stopBound⟩,
        slotAlignmentAtTerminalCheck_complete terminal⟩
  | _ => rfl

/-! ## Matcher-finalization suffixes -/

private def finalizationAtCheck
    (signature : FrozenSig) (state : InferState)
    (clauses : List Clause) (rawTarget : Ty)
    (rawHoleLists : List (List Dual)) (localCapability : Cap)
    (stop : Nat) : Bool :=
  let terminalPrevailing := replay (state.trace.solves.take stop)
  let terminalTarget := terminalPrevailing.apply rawTarget
  let terminalHoleLists := resolvedHoleCaps terminalPrevailing rawHoleLists
  let terminalCapability := localCapability.apply terminalPrevailing.cap
  match collectClauseEvidence signature.toMatcherSig clauses terminalHoleLists with
  | none => false
  | some evidence =>
      decide (Shape.inferShape signature.observability evidence =
        some terminalCapability) &&
      clauseCapsListCheck signature terminalCapability clauses
        terminalHoleLists &&
      catchAllLastCheck clauses &&
      matcherBindersCheck clauses &&
      armExhaustiveCheck signature clauses terminalTarget &&
      coverageCheck signature.toMatcherSig clauses terminalCapability

private def finalizationSuffixEventCheck
    (signature : FrozenSig) (state : InferState) : TraceEvent -> Bool
  | .matcherFinalization solveCount clauses rawTarget rawHoleLists localTarget
      localHoleLists _localEvidence localCapability =>
      decide (solveCount ≤ state.trace.solves.length) &&
      decide (localTarget =
        (replay (state.trace.solves.take solveCount)).apply rawTarget) &&
      decide (localHoleLists = resolvedHoleCaps
        (replay (state.trace.solves.take solveCount)) rawHoleLists) &&
      finalizationAtCheck signature state clauses rawTarget rawHoleLists
        localCapability state.trace.solves.length
  | _ => true

def traceFinalizationSuffixCheck
    (signature : FrozenSig) (state : InferState) : Bool :=
  state.trace.events.all (finalizationSuffixEventCheck signature state)

theorem traceFinalizationSuffixCheck_sound
    {signature : FrozenSig} {state : InferState}
    (checked : traceFinalizationSuffixCheck signature state = true) :
    TraceFinalizationSuffixConditions signature state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  cases event with
  | matcherFinalization solveCount clauses rawTarget rawHoleLists localTarget
      localHoleLists localEvidence localCapability =>
      simp only [finalizationSuffixEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨solveBound, localTargetEq⟩, localHolesEq⟩, terminalChecked⟩
      refine ⟨solveBound, localTargetEq, localHolesEq, ?_⟩
      simp only [finalizationAtCheck, List.take_length] at terminalChecked
      cases collected : collectClauseEvidence signature.toMatcherSig clauses
          (resolvedHoleCaps (replay state.trace.solves) rawHoleLists) with
      | none => simp [collected] at terminalChecked
      | some evidence =>
          refine ⟨evidence, collected, ?_⟩
          simp only [collected, Bool.and_eq_true,
            decide_eq_true_eq] at terminalChecked
          rcases terminalChecked with ⟨prior, coverage⟩
          rcases prior with ⟨prior, exhaustive⟩
          rcases prior with ⟨prior, binders⟩
          rcases prior with ⟨prior, catchAll⟩
          rcases prior with ⟨shape, caps⟩
          exact ⟨shape, caps, catchAll, binders, exhaustive, coverage⟩
  | _ => trivial

/-- Terminal matcher facts are sufficient for the exact finite
finalization check. -/
theorem traceFinalizationSuffixCheck_complete
    {signature : FrozenSig} {state : InferState}
    (conditions : TraceFinalizationSuffixConditions signature state) :
    traceFinalizationSuffixCheck signature state = true := by
  unfold traceFinalizationSuffixCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | matcherFinalization solveCount clauses rawTarget rawHoleLists localTarget
      localHoleLists localEvidence localCapability =>
      simp only [InferState.prevailing] at accepted
      rcases accepted with
        ⟨solveBound, localTargetEq, localHolesEq, evidence, collected,
          shape, caps, catchAll, binders, exhaustive, coverage⟩
      simp only [finalizationSuffixEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨⟨⟨solveBound, localTargetEq⟩, localHolesEq⟩, ?_⟩
      simp only [finalizationAtCheck, List.take_length]
      rw [collected]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨shape, caps⟩, catchAll⟩, binders⟩, exhaustive⟩,
        coverage⟩
  | _ => rfl

/-! ## Terminal let generalization -/

private def generalizationEventCheck
    (signature : FrozenSig) (state : InferState) : TraceEvent -> Bool
  | .letGeneralization solveCount _name rawContext rawTarget context target
      scheme =>
      decide (solveCount ≤ state.trace.solves.length) &&
      decide (context = rawContext.applySubst
        (replay (state.trace.solves.take solveCount))) &&
      decide (target =
        (replay (state.trace.solves.take solveCount)).apply rawTarget) &&
      decide (scheme = signature.generalize context target) &&
      decide (scheme.applyMeta state.prevailing =
        signature.generalize (rawContext.applySubst state.prevailing)
          (state.prevailing.apply rawTarget))
  | _ => true

/-- Executable terminal-cut audit for every recorded T-LET generalization. -/
def traceGeneralizationCheck
    (signature : FrozenSig) (state : InferState) : Bool :=
  state.trace.events.all (generalizationEventCheck signature state)

theorem traceGeneralizationCheck_sound
    {signature : FrozenSig} {state : InferState}
    (checked : traceGeneralizationCheck signature state = true) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have accepted := List.all_eq_true.mp checked event membership
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target
      scheme =>
      simp only [generalizationEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at accepted
      rcases accepted with
        ⟨⟨⟨⟨solveBound, contextEq⟩, targetEq⟩, schemeEq⟩, terminalEq⟩
      exact ⟨solveBound, contextEq, targetEq, schemeEq, terminalEq⟩
  | _ => trivial

/-- Terminal let facts are sufficient for the exact finite generalization
check. -/
theorem traceGeneralizationCheck_complete
    {signature : FrozenSig} {state : InferState}
    (conditions : TraceGeneralizationConditions signature state) :
    traceGeneralizationCheck signature state = true := by
  unfold traceGeneralizationCheck
  apply List.all_eq_true.mpr
  intro event membership
  have accepted := conditions event membership
  cases event with
  | letGeneralization solveCount name rawContext rawTarget context target
      scheme =>
      rcases accepted with
        ⟨solveBound, contextEq, targetEq, schemeEq, terminalEq⟩
      simp only [generalizationEventCheck, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨⟨solveBound, contextEq⟩, targetEq⟩, schemeEq⟩,
        terminalEq⟩
  | _ => rfl

/-! ## Complete public terminal audit -/

/-- Finite algebraic validator consumed by the public executable inference
entry point.  It checks no source typing judgment and stores no derivation. -/
def wBridgeCheck
    (signature : FrozenSig) (result : ExprResult) : Bool :=
  tracePrimitiveHoleCheck signature result.state.trace &&
  tracePatternLeafCheck signature result.state.trace &&
  tracePatternCtorCheck signature result.state &&
  traceInstanceSuffixCheck result.state &&
  traceSlotAlignmentCheck result.state &&
  traceTypeAlignmentCheck result.state &&
  traceDualAlignmentCheck result.state &&
  traceFinalizationSuffixCheck signature result.state &&
  traceGeneralizationCheck signature result.state

/-- A successful finite audit constructs the complete bridge certificate. -/
theorem wBridgeCheck_sound
    {signature : FrozenSig} {result : ExprResult}
    (checked : wBridgeCheck signature result = true) :
    WBridgeWF signature result.state := by
  simp only [wBridgeCheck, Bool.and_eq_true] at checked
  rcases checked with ⟨prior, generalizationChecked⟩
  rcases prior with ⟨prior, finalizationSuffixChecked⟩
  rcases prior with ⟨prior, dualAlignmentChecked⟩
  rcases prior with ⟨prior, typeAlignmentChecked⟩
  rcases prior with ⟨prior, slotAlignmentChecked⟩
  rcases prior with ⟨prior, instanceSuffixChecked⟩
  rcases prior with ⟨prior, patternCtorChecked⟩
  rcases prior with ⟨primitiveHoleChecked, patternLeafChecked⟩
  exact
    { primitiveHoles := primitiveHoleChecked
      patternLeaves := patternLeafChecked
      patternCtors := patternCtorChecked
      instanceSuffixes :=
        traceInstanceSuffixCheck_sound instanceSuffixChecked
      slotAlignments := traceSlotAlignmentCheck_sound slotAlignmentChecked
      typeAlignments := traceTypeAlignmentCheck_sound typeAlignmentChecked
      dualAlignments := traceDualAlignmentCheck_sound dualAlignmentChecked
      finalizationSuffixes :=
        traceFinalizationSuffixCheck_sound finalizationSuffixChecked
      generalization :=
        traceGeneralizationCheck_sound generalizationChecked }

end Reconstruction
end Inference
end TypePM
