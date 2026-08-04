import TypePM.P2.Reconstruction

/-!
# Executable audits for reconstruction bridge conditions

The raw reconstruction theorem accepts an algebraic `WBridgeWF` certificate;
the public executable inference entry point runs this module's finite
validator and constructs that certificate internally.  The checks never
store or consume a source typing derivation.
-/

namespace TypePM.P2
namespace Inference
namespace Reconstruction

private def boundedSuffixCheck
    (lower upper : Nat) (predicate : Nat -> Bool) : Bool :=
  (List.range (upper + 1)).all fun index =>
    if lower ≤ index then predicate index else true

private theorem boundedSuffixCheck_sound
    {lower upper : Nat} {predicate : Nat -> Bool}
    (checked : boundedSuffixCheck lower upper predicate = true)
    {index : Nat} (lowerBound : lower ≤ index)
    (upperBound : index ≤ upper) :
    predicate index = true := by
  have membership : index ∈ List.range (upper + 1) := by
    exact List.mem_range.mpr (Nat.lt_succ_iff.mpr upperBound)
  have accepted := List.all_eq_true.mp checked index membership
  simpa [boundedSuffixCheck, lowerBound] using accepted

/-! ## A target-only restricted view of a solver suffix -/

private def replayTargetDomain (steps : List SolveStep) : List TypePM.TyVar :=
  steps.flatMap fun step => step.targetDomain

private theorem replayFrom_targetSupport
    {prevailing : Subst} {initialDomain : List TypePM.TyVar}
    (support : prevailing.target.SupportWithin initialDomain) :
    ∀ steps,
      (replayFrom prevailing steps).target.SupportWithin
        (initialDomain ++ steps.flatMap fun step => step.targetDomain)
  | [] => by simpa [replayFrom] using support
  | step :: steps => by
      have composed :
          (Subst.seq step.delta prevailing).target.SupportWithin
            (initialDomain ++ step.targetDomain) :=
        by
          intro varId outside
          have outsideInitial : varId ∉ initialDomain := by
            intro membership
            exact outside (List.mem_append_left _ membership)
          have outsideStep : varId ∉ step.targetDomain := by
            intro membership
            exact outside (List.mem_append_right _ membership)
          simp only [Subst.seq]
          rw [support varId outsideInitial]
          exact step.targetSupport varId outsideStep
      have remainder := replayFrom_targetSupport composed steps
      simpa only [replayFrom, List.flatMap_cons, List.append_assoc] using
        remainder

private theorem replay_targetSupport (steps : List SolveStep) :
    (replay steps).target.SupportWithin (replayTargetDomain steps) := by
  have raw := replayFrom_targetSupport
    (prevailing := Subst.id) (initialDomain := [])
    (TySubst.id_supportWithin []) steps
  intro varId outside
  apply raw varId
  simp only [List.nil_append]
  intro membership
  apply outside
  simpa [replayTargetDomain] using membership

private def targetDomainsBelowCheck
    (bound : Nat) (steps : List SolveStep) : Bool :=
  steps.all fun step => step.targetDomain.all fun varId => varId < bound

private theorem targetDomainsBelowCheck_sound
    {bound : Nat} {steps : List SolveStep}
    (checked : targetDomainsBelowCheck bound steps = true) :
    ∀ varId, varId ∈ replayTargetDomain steps -> varId < bound := by
  intro varId membership
  simp only [replayTargetDomain, List.mem_flatMap] at membership
  rcases membership with ⟨step, stepMembership, variableMembership⟩
  have stepAccepted := List.all_eq_true.mp checked step stepMembership
  have variableAccepted :=
    List.all_eq_true.mp stepAccepted varId variableMembership
  exact of_decide_eq_true variableAccepted

private def targetOnlyReplay (steps : List SolveStep) : Subst :=
  Subst.mk CapSubst.id (replay steps).target

private theorem targetOnlyReplay_chain
    (steps : List SolveStep) (bound : Nat)
    (below : ∀ varId, varId ∈ replayTargetDomain steps -> varId < bound) :
    RestrictedPost.Chain [] [] [] [] (targetOnlyReplay steps) := by
  apply RestrictedPost.Chain.one
  apply RestrictedPost.ofVariableSubstitution
    (capDomain := []) (tyDomain := List.range bound)
    (capImages := []) CapSubst.id (replay steps).target
  · exact CapSubst.id_supportWithin []
  · intro varId outside
    apply replay_targetSupport steps varId
    intro membership
    exact outside (List.mem_range.mpr (below varId membership))
  · exact List.nodup_nil
  · exact List.nodup_range
  · rfl
  · exact List.nodup_nil
  · intros; contradiction
  · simp
  · intros; contradiction
  · intros; contradiction

/-! ## Terminal fresh-instance reconstruction -/

/-- Binder-local capability candidate obtained by replaying the fresh image
allocated from an event's incoming supply. -/
private def terminalCapCandidate
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List CapVar) : CapSubst :=
  fun varId =>
    if varId ∈ binders then
      state.prevailing.cap ⟨supply.nextCap + varId.id⟩
    else
      .var varId

/-- Binder-local target candidate obtained from the corresponding fresh
ordinary image. -/
private def terminalTyCandidate
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List TypePM.TyVar) : TySubst :=
  fun varId =>
    if varId ∈ binders then
      state.prevailing.apply (.var (supply.nextTy + varId))
    else
      .var varId

private theorem terminalCapCandidate_support
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List CapVar) :
    (terminalCapCandidate state supply binders).SupportWithin binders := by
  intro varId outside
  simp [terminalCapCandidate, outside]

private theorem terminalTyCandidate_support
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (binders : List TypePM.TyVar) :
    (terminalTyCandidate state supply binders).SupportWithin binders := by
  intro varId outside
  simp [terminalTyCandidate, outside]

private def capBinderImagesVariableCheck
    (binders : List CapVar) (substitution : CapSubst) : Bool :=
  binders.all fun varId =>
    match substitution varId with
    | .var _ => true
    | _ => false

private theorem capBinderImagesVariableCheck_sound
    {binders : List CapVar} {substitution : CapSubst}
    (checked : capBinderImagesVariableCheck binders substitution = true) :
    ∀ varId, varId ∈ binders →
      ∃ image, substitution varId = .var image := by
  intro varId membership
  have accepted := List.all_eq_true.mp checked varId membership
  cases equation : substitution varId with
  | var image => exact ⟨image, rfl⟩
  | _ => simp [equation] at accepted

private def instanceSuffixEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .schemeInstantiation solveCount supply _scheme name rawContext _context
      _fixedCaps _fixedTys _reservedCaps _reservedTys fresh _capImages
      _tyImages =>
      decide (solveCount ≤ state.trace.solves.length) &&
      match (rawContext.applySubst state.prevailing).find? name with
      | none => false
      | some terminalScheme =>
          let C := terminalCapCandidate state supply terminalScheme.capBinders
          let T := terminalTyCandidate state supply terminalScheme.tyBinders
          capBinderImagesVariableCheck terminalScheme.capBinders C &&
          decide ((Subst.mk C T).apply terminalScheme.body =
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
          let C := terminalCapCandidate state supply terminalScheme.capBinders
          let T := terminalTyCandidate state supply terminalScheme.tyBinders
          refine ⟨solveBound, terminalScheme, lookup, C, T, ?_⟩
          exact
            { capSupport := terminalCapCandidate_support state supply _
              tySupport := terminalTyCandidate_support state supply _
              capBinderVariable :=
                capBinderImagesVariableCheck_sound terminalChecked.1
              result := terminalChecked.2 }
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
      boundedSuffixCheck stop state.trace.solves.length fun terminal =>
        decide
          (applyDeltas (solveSlice state.trace start terminal) localLeft =
            applyDeltas (solveSlice state.trace start terminal) localRight) &&
        decide
          ((replay (state.trace.solves.take terminal)).apply rawLeft =
            (replay (state.trace.solves.take terminal)).apply rawRight)
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
        ⟨⟨⟨⟨startStop, stopBound⟩, localLeftEq⟩, localRightEq⟩,
          suffixChecked⟩
      refine ⟨startStop, stopBound, localLeftEq, localRightEq, ?_⟩
      intro terminal lower upper
      have accepted := boundedSuffixCheck_sound suffixChecked lower upper
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using accepted
  | _ => trivial

private def dualAlignmentEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .dualAlignment start stop rawLeft rawRight localLeft localRight =>
      decide (start ≤ stop) &&
      decide (stop ≤ state.trace.solves.length) &&
      decide (localLeft = rawLeft.applySubst
        (replay (state.trace.solves.take start))) &&
      decide (localRight = rawRight.applySubst
        (replay (state.trace.solves.take start))) &&
      boundedSuffixCheck stop state.trace.solves.length fun terminal =>
        decide
          (applyDualDeltas (solveSlice state.trace start terminal) localLeft =
            applyDualDeltas (solveSlice state.trace start terminal) localRight) &&
        decide
          (rawLeft.applySubst (replay (state.trace.solves.take terminal)) =
            rawRight.applySubst (replay (state.trace.solves.take terminal)))
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
        ⟨⟨⟨⟨startStop, stopBound⟩, localLeftEq⟩, localRightEq⟩,
          suffixChecked⟩
      refine ⟨startStop, stopBound, localLeftEq, localRightEq, ?_⟩
      intro terminal lower upper
      have accepted := boundedSuffixCheck_sound suffixChecked lower upper
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using accepted
  | _ => trivial

/-! ## Expected-type slot alignments -/

private def slotAlignmentAtTerminalCheck
    (targetBound : Nat) (localSteps terminalSteps : List SolveStep)
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
        let post := targetOnlyReplay suffix
        match step.constraint with
        | .producerToSlot rawProducerCap rawProducerTarget rawConsumerCap
            rawConsumerTarget =>
            decide (rawProducerCap = producerCap) &&
            decide (rawProducerTarget = producerTarget) &&
            decide (rawConsumerCap = consumerCap) &&
            decide (rawConsumerTarget = consumerTarget) &&
            targetDomainsBelowCheck targetBound suffix &&
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

private theorem solveStep_producerToSlot_raw
    {step : SolveStep} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (constraintEq : step.constraint = .producerToSlot producerCap
      producerTarget consumerCap consumerTarget)
    (rangeFixed : step.delta.RangeFixed) :
    ∃ bindings, MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings step.delta.cap step.delta.target := by
  rcases step with
    ⟨solveCount, origin, constraint, delta, targetDomain, targetSupport,
      certificate, locallySound⟩
  dsimp only at constraintEq rangeFixed ⊢
  subst constraint
  cases certificate with
  | producerToSlot matched unified =>
      exact ⟨_, matched, rfl, unified, rangeFixed⟩

private theorem slotAlignmentAtTerminalCheck_sound
    {targetBound : Nat} {localSteps terminalSteps : List SolveStep}
    {inferred requested : Ty}
    (checked : slotAlignmentAtTerminalCheck targetBound localSteps
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
                      ⟨⟨⟨⟨⟨⟨⟨producerCapEq, producerTargetEq⟩,
                        consumerCapEq⟩, consumerTargetEq⟩, domainsChecked⟩,
                        rangeChecked⟩, producerResult⟩, consumerResult⟩
                    subst rawProducerCap
                    subst rawProducerTarget
                    subst rawConsumerCap
                    subst rawConsumerTarget
                    let suffix := terminalSteps.tail
                    let post := targetOnlyReplay suffix
                    have postChain :
                        RestrictedPost.Chain [] [] [] [] post :=
                      targetOnlyReplay_chain suffix targetBound
                        (targetDomainsBelowCheck_sound domainsChecked)
                    have rangeFixed : step.delta.RangeFixed :=
                      rangeFixedOnCheck_sound step.targetSupport rangeChecked
                    rcases solveStep_producerToSlot_raw constraintForm
                        rangeFixed with ⟨bindings, raw⟩
                    exact .matcherToSlot rfl rfl rfl constraintForm rfl raw
                      postChain producerResult consumerResult

private def slotAlignmentEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .slotAlignment start stop inferred requested =>
      decide (start ≤ stop) &&
      decide (stop ≤ state.trace.solves.length) &&
      boundedSuffixCheck stop state.trace.solves.length fun terminal =>
        slotAlignmentAtTerminalCheck state.supply.nextTy
          (solveSlice state.trace start stop)
          (solveSlice state.trace start terminal) inferred requested
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
      rcases eventChecked with ⟨⟨startStop, stopBound⟩, suffixChecked⟩
      refine ⟨startStop, stopBound, ?_⟩
      intro terminal lower upper
      have present := boundedSuffixCheck_sound suffixChecked lower upper
      exact slotAlignmentAtTerminalCheck_sound (targetBound := state.supply.nextTy)
        (localSteps := solveSlice state.trace start stop)
        (terminalSteps := solveSlice state.trace start terminal)
        (inferred := inferred) (requested := requested) present
  | _ => trivial

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
      decide (scheme.applySubst state.prevailing =
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
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (checked : wBridgeCheck signature result = true) :
    WBridgeWF signature context expression result := by
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
    { replay := traceReplayConditions result.state.trace.solves
      primitiveHoles := primitiveHoleChecked
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
end TypePM.P2
