import TypePM.P2.Reconstruction

/-!
# Executable audits for reconstruction bridge conditions

The public reconstruction theorem intentionally accepts an algorithmic
`WBridgeWF` certificate.  This module turns the finite, recorded terminal
trace into the non-local alignment and finalization fields of that
certificate.  It never stores or consumes a source typing derivation.
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
          (Subst.comp step.delta prevailing).target.SupportWithin
            (initialDomain ++ step.targetDomain) :=
        support.comp step.targetSupport
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

/-! ## Fresh-instance suffix composition -/

private theorem schemeComposition_of_noBinders
    {external : Subst} {scheme : Scheme} {fresh : Ty}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {C : CapSubst} {T : TySubst} {capImages : List CapVar}
    {tyImages : List TypePM.TyVar}
    (capBinders : scheme.capBinders = [])
    (tyBinders : scheme.tyBinders = [])
    (original : scheme.FreshInstAt reservedCaps reservedTys C T
      capImages tyImages fresh) :
    SchemeValueFlowCompositionAt external original := by
  have capId : C = CapSubst.id := by
    funext varId
    exact original.capSupport varId (by simp [capBinders])
  have targetId : T = TySubst.id := by
    funext varId
    exact original.tySupport varId (by simp [tyBinders])
  have freshEq : scheme.body = fresh := by
    have pairIdentity : Subst.mk CapSubst.id TySubst.id = Subst.id := rfl
    simpa [capId, targetId, pairIdentity, Subst.apply_id] using original.result
  refine ⟨CapSubst.id, TySubst.id, ?_⟩
  refine
    { capSupport := ?_
      tySupport := ?_
      capBinderVariable := ?_
      result := ?_ }
  · simpa [Scheme.applySubst, capBinders] using
      (CapSubst.id_supportWithin [])
  · simpa [Scheme.applySubst, tyBinders] using
      (TySubst.id_supportWithin [])
  · intro varId membership
    simp [Scheme.applySubst, capBinders] at membership
  · have schemeBodyEq :
        (scheme.applySubst external).body = external.apply fresh := by
      simp [Scheme.applySubst, capBinders, tyBinders, freshEq]
    rw [schemeBodyEq]
    have pairIdentity : Subst.mk CapSubst.id TySubst.id = Subst.id := rfl
    rw [pairIdentity, Subst.apply_id]

private def instanceSuffixEventCheck
    (state : InferState) : TraceEvent -> Bool
  | .schemeInstantiation solveCount _ scheme name rawContext context
      _fixedCaps _fixedTys _reservedCaps _reservedTys fresh _capImages
      _tyImages =>
      decide (scheme.capBinders = []) &&
      decide (scheme.tyBinders = []) &&
      decide (context = rawContext.applySubst
        (replay (state.trace.solves.take solveCount))) &&
      decide (solveCount ≤ state.trace.solves.length) &&
      boundedSuffixCheck solveCount state.trace.solves.length fun stop =>
        let suffix := replay ((state.trace.solves.take stop).drop solveCount)
        let terminalPrevailing := replay (state.trace.solves.take stop)
        decide ((rawContext.applySubst terminalPrevailing).find? name =
          some (scheme.applySubst suffix)) &&
        decide (terminalPrevailing.apply fresh = suffix.apply fresh)
  | .ctorInstantiation solveCount _ scheme args result _capImages =>
      decide (scheme.fcv = []) &&
      decide (scheme.ftv = []) &&
      decide (solveCount ≤ state.trace.solves.length) &&
      boundedSuffixCheck solveCount state.trace.solves.length fun stop =>
        let suffix := replay ((state.trace.solves.take stop).drop solveCount)
        let terminalPrevailing := replay (state.trace.solves.take stop)
        decide (args.map terminalPrevailing.apply = args.map suffix.apply) &&
        decide (terminalPrevailing.apply result = suffix.apply result)
  | .dualInstantiation .. => false
  | _ => true

def traceInstanceSuffixCheck (state : InferState) : Bool :=
  state.trace.events.all (instanceSuffixEventCheck state)

theorem traceInstanceSuffixCheck_sound
    {signature : FrozenSig} {state : InferState}
    (instantiations : TraceInstantiationConditions state.trace)
    (checked : traceInstanceSuffixCheck state = true) :
    TraceInstanceSuffixConditions signature state := by
  intro event membership
  have eventChecked := List.all_eq_true.mp checked event membership
  have instantiation := instantiations event membership
  cases event with
  | schemeInstantiation solveCount supply scheme name rawContext context
      fixedCaps fixedTys reservedCaps reservedTys fresh capImages tyImages =>
      simp only [instanceSuffixEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨⟨capBinders, tyBinders⟩, contextEq⟩, solveBound⟩,
          suffixChecked⟩
      refine ⟨contextEq, solveBound, ?_⟩
      intro stop lower upper
      have accepted := boundedSuffixCheck_sound suffixChecked lower upper
      simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
      rcases instantiation with ⟨C, T, original⟩
      exact ⟨C, T, original, accepted.1, accepted.2,
        schemeComposition_of_noBinders capBinders tyBinders original⟩
  | ctorInstantiation solveCount supply scheme args result capImages =>
      simp only [instanceSuffixEventCheck,
        Bool.and_eq_true, decide_eq_true_eq] at eventChecked
      rcases eventChecked with
        ⟨⟨⟨capFree, targetFree⟩, solveBound⟩, suffixChecked⟩
      refine ⟨solveBound, ?_⟩
      intro stop lower upper
      have accepted := boundedSuffixCheck_sound suffixChecked lower upper
      simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
      have original : scheme.Inst args result :=
        instantiation
      have admissible : scheme.InstCompositionAdm
          (replay ((state.trace.solves.take stop).drop solveCount)) :=
        CtorScheme.instCompositionAdm_of_free_fixed
          (by simp [capFree]) (by simp [targetFree])
      exact ⟨accepted.1, accepted.2,
        CtorScheme.Inst.transport original admissible⟩
  | dualInstantiation => simp_all [traceInstanceSuffixCheck,
      instanceSuffixEventCheck]
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
      boundedSuffixCheck solveCount state.trace.solves.length fun stop =>
        finalizationAtCheck signature state clauses rawTarget rawHoleLists
          localCapability stop
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
        ⟨⟨⟨solveBound, localTargetEq⟩, localHolesEq⟩, suffixChecked⟩
      refine ⟨solveBound, localTargetEq, localHolesEq, ?_⟩
      intro stop lower upper
      have accepted := boundedSuffixCheck_sound suffixChecked lower upper
      simp only [finalizationAtCheck] at accepted
      cases collected : collectClauseEvidence signature.toMatcherSig clauses
          (resolvedHoleCaps (replay (state.trace.solves.take stop))
            rawHoleLists) with
      | none => simp [collected] at accepted
      | some evidence =>
          refine ⟨evidence, collected, ?_⟩
          simp only [collected, Bool.and_eq_true,
            decide_eq_true_eq] at accepted
          rcases accepted with ⟨prior, coverage⟩
          rcases prior with ⟨prior, exhaustive⟩
          rcases prior with ⟨prior, binders⟩
          rcases prior with ⟨prior, catchAll⟩
          rcases prior with ⟨shape, caps⟩
          exact ⟨shape, caps, catchAll, binders, exhaustive, coverage⟩
  | _ => trivial

/-! ## Traces without let generalization -/

private def noLetEventCheck : TraceEvent -> Bool
  | .letGeneralization .. => false
  | _ => true

def traceNoLetCheck (state : InferState) : Bool :=
  state.trace.events.all noLetEventCheck

theorem traceNoLetCheck_sound
    {signature : FrozenSig} {state : InferState}
    (checked : traceNoLetCheck state = true) :
    TraceGeneralizationConditions signature state := by
  intro event membership
  have accepted := List.all_eq_true.mp checked event membership
  cases event <;> simp_all [traceNoLetCheck, noLetEventCheck]

end Reconstruction
end Inference
end TypePM.P2
