import TypePM.DemandTypingInferenceCompletenessValidatorIntrinsic
import TypePM.InferenceTraversalStateExtension

/-!
# Compositional traversal facts for terminal-validator completeness

The terminal validator folds over an append-only event trace.  This module
packages the four audit-independent folds that are generated directly by the
executable traversal: primitive-hole freshness, user-pattern leaf freshness,
canonical fresh instances, and expected-slot alignments.

The central `TraversalValidatorConditions` record is deliberately independent
of a `DDTyping` derivation.  Its `recordEvent` constructor is the boundary used
by the completeness recursion: recursive calls retain the facts for their
prefix, and the code that emits one event supplies only that event's local
condition.  Solver-sensitive facts are stated at the current terminal state;
there is no caller-provided reconstruction oracle.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-- The four terminal checks whose witnesses come from ordinary traversal,
rather than from the three proof-relevant terminal audits in `DDTyping`. -/
structure TraversalValidatorConditions
    (signature : FrozenSig) (state : InferState) : Prop where
  primitiveHoles : TracePrimitiveHoleConditions signature state.trace
  patternLeaves : TracePatternLeafConditions signature state.trace
  instances : CanonicalTraceInstanceSuffixConditions state
  slots : CanonicalTraceSlotAlignmentConditions state

/-- All four traversal-side conditions are vacuous on an empty event trace. -/
theorem TraversalValidatorConditions.empty
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply) :
    TraversalValidatorConditions signature (InferState.empty supply) := by
  constructor <;> intro event membership <;>
    simp [InferState.empty] at membership

/-- Primitive-hole clause contributed by one event. -/
def PrimitiveHoleEventCondition
    (signature : FrozenSig) (event : TraceEvent) : Prop :=
  match event with
    | .inferredPPat .hole target holes bindings _path =>
        ∃ varId,
          holes = [⟨.var varId, target⟩] ∧
          bindings = [] ∧
          varId ∉ signature.capVars ∧
          varId ∉ target.fcv
    | _ => True

/-- User-pattern leaf clause contributed by one event. -/
def PatternLeafEventCondition
    (signature : FrozenSig) (event : TraceEvent) : Prop :=
  match event with
    | .patternVarFresh context parameters bindings capVar tyVar
    | .patternWildFresh context parameters bindings capVar tyVar =>
        capVar ∉ signature.capVars ∧
        capVar ∉ context.fcv ∧
        capVar ∉ parameters.fcv ∧
        capVar ∉ bindings.fcv ∧
        tyVar ∉ signature.tyVars ∧
        tyVar ∉ context.ftv ∧
        tyVar ∉ parameters.ftv ∧
        tyVar ∉ bindings.ftv
    | .patternValueFresh context parameters bindings capVar target =>
        capVar ∉ signature.capVars ∧
        capVar ∉ context.fcv ∧
        capVar ∉ parameters.fcv ∧
        capVar ∉ bindings.fcv ∧
        capVar ∉ target.fcv
    | _ => True

/-- Canonical-instance clause contributed by one event at a terminal cut. -/
def CanonicalInstanceEventCondition
    (state : InferState) (event : TraceEvent) : Prop :=
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

/-- Expected-slot clause contributed by one event at a terminal cut. -/
def CanonicalSlotEventCondition
    (state : InferState) (event : TraceEvent) : Prop :=
  match event with
    | .slotAlignment start stop inferred requested =>
        start ≤ stop ∧ stop ≤ state.trace.solves.length ∧
        CanonicalSlotAlignmentAtTerminal
          (solveSlice state.trace start stop)
          (solveSlice state.trace start state.trace.solves.length)
          inferred requested
    | _ => True

structure PrimitiveHoleEventWitness
    (signature : FrozenSig) (event : TraceEvent) : Prop where
  holds : PrimitiveHoleEventCondition signature event

structure PatternLeafEventWitness
    (signature : FrozenSig) (event : TraceEvent) : Prop where
  holds : PatternLeafEventCondition signature event

structure CanonicalInstanceEventWitness
    (state : InferState) (event : TraceEvent) : Prop where
  holds : CanonicalInstanceEventCondition state event

structure CanonicalSlotEventWitness
    (state : InferState) (event : TraceEvent) : Prop where
  holds : CanonicalSlotEventCondition state event

/-- Exact condition contributed by one newly appended event.  The two
allocation clauses are state independent.  Instance and slot clauses are
interpreted at the current terminal state, exactly as by the finite checker. -/
structure TraversalValidatorEventCondition
    (signature : FrozenSig) (state : InferState) (event : TraceEvent) : Prop where
  primitiveHole : PrimitiveHoleEventWitness signature event
  patternLeaf : PatternLeafEventWitness signature event
  canonicalInstance : CanonicalInstanceEventWitness state event
  slot : CanonicalSlotEventWitness state event

@[simp] theorem terminalCapCandidate_recordEvent
    (state : InferState) (event : TraceEvent)
    (supply : InferenceBase.FreshSupply) (binders : List CapVar) :
    terminalCapCandidate (state.recordEvent event) supply binders =
      terminalCapCandidate state supply binders := by
  rfl

@[simp] theorem terminalTyCandidate_recordEvent
    (state : InferState) (event : TraceEvent)
    (supply : InferenceBase.FreshSupply) (binders : List TypePM.TyVar) :
    terminalTyCandidate (state.recordEvent event) supply binders =
      terminalTyCandidate state supply binders := by
  rfl

@[simp] theorem terminalSchemeOpening_recordEvent
    (state : InferState) (event : TraceEvent)
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    terminalSchemeOpening (state.recordEvent event) supply scheme =
      terminalSchemeOpening state supply scheme := by
  rfl

@[simp] theorem solveSlice_recordEvent
    (state : InferState) (event : TraceEvent) (start stop : Nat) :
    solveSlice (state.recordEvent event).trace start stop =
      solveSlice state.trace start stop := by
  rfl

theorem canonicalInstanceEventCondition_recordEvent
    (state : InferState) (event candidate : TraceEvent) :
    CanonicalInstanceEventCondition (state.recordEvent event) candidate ↔
      CanonicalInstanceEventCondition state candidate := by
  cases candidate <;> rfl

theorem canonicalSlotEventCondition_recordEvent
    (state : InferState) (event candidate : TraceEvent) :
    CanonicalSlotEventCondition (state.recordEvent event) candidate ↔
      CanonicalSlotEventCondition state candidate := by
  cases candidate <;> rfl

/-- Appending a locally justified event preserves all four validator folds.
This is the common compositional step used by every syntax branch. -/
theorem TraversalValidatorConditions.recordEvent
    {signature : FrozenSig} {state : InferState} {event : TraceEvent}
    (before : TraversalValidatorConditions signature state)
    (latest : TraversalValidatorEventCondition signature
      (state.recordEvent event) event) :
    TraversalValidatorConditions signature (state.recordEvent event) := by
  constructor
  · intro candidate membership
    simp only [InferState.recordEvent, List.mem_append,
      List.mem_singleton] at membership
    rcases membership with previous | newest
    · exact before.primitiveHoles candidate previous
    · subst candidate
      exact latest.primitiveHole.holds
  · intro candidate membership
    simp only [InferState.recordEvent, List.mem_append,
      List.mem_singleton] at membership
    rcases membership with previous | newest
    · exact before.patternLeaves candidate previous
    · subst candidate
      exact latest.patternLeaf.holds
  · intro candidate membership
    simp only [InferState.recordEvent, List.mem_append,
      List.mem_singleton] at membership
    rcases membership with previous | newest
    · exact (canonicalInstanceEventCondition_recordEvent state event
        candidate).2 (before.instances candidate previous)
    · subst candidate
      exact latest.canonicalInstance.holds
  · intro candidate membership
    simp only [InferState.recordEvent, List.mem_append,
      List.mem_singleton] at membership
    rcases membership with previous | newest
    · exact (canonicalSlotEventCondition_recordEvent state event candidate).2
        (before.slots candidate previous)
    · subst candidate
      exact latest.slot.holds

/-- The packaged traversal facts discharge the corresponding four finite
terminal checks directly. -/
theorem traversalValidatorChecks_complete
    {signature : FrozenSig} {state : InferState}
    (conditions : TraversalValidatorConditions signature state) :
    tracePrimitiveHoleCheck signature state.trace = true ∧
      tracePatternLeafCheck signature state.trace = true ∧
      traceInstanceSuffixCheck state = true ∧
      traceSlotAlignmentCheck state = true :=
  ⟨tracePrimitiveHoleCheck_complete conditions.primitiveHoles,
    tracePatternLeafCheck_complete conditions.patternLeaves,
    traceInstanceSuffixCheck_complete conditions.instances,
    traceSlotAlignmentCheck_complete conditions.slots⟩

/-! ## Allocation-event constructors -/

/-- A primitive hole allocated at `supply.nextCap` satisfies its exact
validator clause whenever the signature and shared target are below that cut. -/
theorem primitiveHoleEventCondition
    {signature : FrozenSig} {state : InferState} {path : SyntaxPath}
    {target : Ty}
    (signatureBelow : InferenceBase.CapVarsBelow state.supply
      signature.capVars)
    (targetBounded : target.BoundedBy state.supply) :
    TraversalValidatorEventCondition signature state
      (.inferredPPat .hole target
        [⟨.var ⟨state.supply.nextCap⟩, target⟩] [] path) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · change ∃ varId : CapVar,
      [Dual.mk (.var ⟨state.supply.nextCap⟩) target] =
          [Dual.mk (.var varId) target] ∧
        ([] : MonoCtx) = [] ∧
        varId ∉ signature.capVars ∧ varId ∉ target.fcv
    refine ⟨⟨state.supply.nextCap⟩, rfl, rfl, ?_, ?_⟩
    · exact nextCap_not_mem_of_below signatureBelow
    · exact nextCap_not_mem_of_below targetBounded.caps
  · simp [PatternLeafEventCondition]
  · simp [CanonicalInstanceEventCondition]
  · simp [CanonicalSlotEventCondition]

/-- The paired capability/target allocation used by a pattern variable is
fresh for every ambient component bounded by the incoming supply. -/
theorem patternVarEventCondition
    {signature : FrozenSig} {state : InferState}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    (signatureCaps : InferenceBase.CapVarsBelow state.supply signature.capVars)
    (contextCaps : InferenceBase.CapVarsBelow state.supply context.fcv)
    (parameterCaps : InferenceBase.CapVarsBelow state.supply parameters.fcv)
    (bindingCaps : InferenceBase.CapVarsBelow state.supply bindings.fcv)
    (signatureTys : InferenceBase.TyVarsBelow state.supply signature.tyVars)
    (contextTys : InferenceBase.TyVarsBelow state.supply context.ftv)
    (parameterTys : InferenceBase.TyVarsBelow state.supply parameters.ftv)
    (bindingTys : InferenceBase.TyVarsBelow state.supply bindings.ftv) :
    TraversalValidatorEventCondition signature state
      (.patternVarFresh context parameters bindings
        ⟨state.supply.nextCap⟩ state.supply.nextTy) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · simp [PrimitiveHoleEventCondition]
  · simp only [PatternLeafEventCondition]
    exact ⟨nextCap_not_mem_of_below signatureCaps,
      nextCap_not_mem_of_below contextCaps,
      nextCap_not_mem_of_below parameterCaps,
      nextCap_not_mem_of_below bindingCaps,
      nextTy_not_mem_of_below signatureTys,
      nextTy_not_mem_of_below contextTys,
      nextTy_not_mem_of_below parameterTys,
      nextTy_not_mem_of_below bindingTys⟩
  · simp [CanonicalInstanceEventCondition]
  · simp [CanonicalSlotEventCondition]

/-- Wildcard leaves use exactly the same paired allocation as variables. -/
theorem patternWildEventCondition
    {signature : FrozenSig} {state : InferState}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    (signatureCaps : InferenceBase.CapVarsBelow state.supply signature.capVars)
    (contextCaps : InferenceBase.CapVarsBelow state.supply context.fcv)
    (parameterCaps : InferenceBase.CapVarsBelow state.supply parameters.fcv)
    (bindingCaps : InferenceBase.CapVarsBelow state.supply bindings.fcv)
    (signatureTys : InferenceBase.TyVarsBelow state.supply signature.tyVars)
    (contextTys : InferenceBase.TyVarsBelow state.supply context.ftv)
    (parameterTys : InferenceBase.TyVarsBelow state.supply parameters.ftv)
    (bindingTys : InferenceBase.TyVarsBelow state.supply bindings.ftv) :
    TraversalValidatorEventCondition signature state
      (.patternWildFresh context parameters bindings
        ⟨state.supply.nextCap⟩ state.supply.nextTy) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · simp [PrimitiveHoleEventCondition]
  · simp only [PatternLeafEventCondition]
    exact ⟨nextCap_not_mem_of_below signatureCaps,
      nextCap_not_mem_of_below contextCaps,
      nextCap_not_mem_of_below parameterCaps,
      nextCap_not_mem_of_below bindingCaps,
      nextTy_not_mem_of_below signatureTys,
      nextTy_not_mem_of_below contextTys,
      nextTy_not_mem_of_below parameterTys,
      nextTy_not_mem_of_below bindingTys⟩
  · simp [CanonicalInstanceEventCondition]
  · simp [CanonicalSlotEventCondition]

/-- Value-pattern leaves allocate only a capability; boundedness of the
already synthesized target supplies the required separation fact. -/
theorem patternValueEventCondition
    {signature : FrozenSig} {state : InferState}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {target : Ty}
    (signatureCaps : InferenceBase.CapVarsBelow state.supply signature.capVars)
    (contextCaps : InferenceBase.CapVarsBelow state.supply context.fcv)
    (parameterCaps : InferenceBase.CapVarsBelow state.supply parameters.fcv)
    (bindingCaps : InferenceBase.CapVarsBelow state.supply bindings.fcv)
    (targetBounded : target.BoundedBy state.supply) :
    TraversalValidatorEventCondition signature state
      (.patternValueFresh context parameters bindings
        ⟨state.supply.nextCap⟩ target) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · simp [PrimitiveHoleEventCondition]
  · simp only [PatternLeafEventCondition]
    exact ⟨nextCap_not_mem_of_below signatureCaps,
      nextCap_not_mem_of_below contextCaps,
      nextCap_not_mem_of_below parameterCaps,
      nextCap_not_mem_of_below bindingCaps,
      nextCap_not_mem_of_below targetBounded.caps⟩
  · simp [CanonicalInstanceEventCondition]
  · simp [CanonicalSlotEventCondition]

/-! ## Solver-sensitive event constructors -/

/-- A canonical instance event can be appended without reopening the whole
trace: its terminal equations are supplied at precisely the current cut. -/
theorem instanceEventCondition
    {signature : FrozenSig} {state : InferState} {event : TraceEvent}
    (primitive : PrimitiveHoleEventCondition signature event)
    (leaf : PatternLeafEventCondition signature event)
    (condition : CanonicalInstanceEventCondition state event)
    (slot : CanonicalSlotEventCondition state event) :
    TraversalValidatorEventCondition signature state event := by
  exact ⟨⟨primitive⟩, ⟨leaf⟩, ⟨condition⟩, ⟨slot⟩⟩

/-- At a bounded cut, the validator's canonical capability candidate is the
same fresh batch used by executable constructor and dual instantiation. -/
theorem terminalCapCandidate_eq_freshCapSubst_of_bounded
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (bounded : state.prevailing.BoundedBy supply)
    (binders : List CapVar) :
    terminalCapCandidate state supply binders =
      InferenceBase.freshCapSubst supply.nextCap binders := by
  funext varId
  by_cases member : varId ∈ binders
  · simp [terminalCapCandidate, InferenceBase.freshCapSubst, member,
      bounded.capFixedAbove _ (Nat.le_add_right _ _)]
  · simp [terminalCapCandidate, InferenceBase.freshCapSubst, member]

/-- Target counterpart of
`terminalCapCandidate_eq_freshCapSubst_of_bounded`. -/
theorem terminalTyCandidate_eq_freshTySubst_of_bounded
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (bounded : state.prevailing.BoundedBy supply)
    (binders : List TypePM.TyVar) :
    terminalTyCandidate state supply binders =
      InferenceBase.freshTySubst supply.nextTy binders := by
  funext varId
  by_cases member : varId ∈ binders
  · simp only [terminalTyCandidate, member, if_pos,
      InferenceBase.freshTySubst]
    apply Subst.apply_eq_self_of_fixed
    · intro candidate membership
      have candidateEq : candidate = supply.nextTy + varId := by
        simpa [Ty.ftv] using membership
      subst candidate
      exact bounded.targetFixedAbove _ (Nat.le_add_right _ _)
    · simp [Ty.fcv]
  · simp [terminalTyCandidate, InferenceBase.freshTySubst, member]

/-- On a type whose free variables are all quantified by one constructor
binder batch, the validator's terminal candidates are exactly terminal replay
after the canonical fresh opening.  Capability images may be structural here;
the result deliberately does not assert a variable-shape invariant. -/
theorem terminalCandidates_apply_of_scoped
    {state : InferState} {supply : InferenceBase.FreshSupply}
    {capBinders : List CapVar} {tyBinders : List TypePM.TyVar}
    {target : Ty}
    (capsScoped : ∀ varId, varId ∈ target.fcv → varId ∈ capBinders)
    (tysScoped : ∀ varId, varId ∈ target.ftv → varId ∈ tyBinders) :
    (Subst.mk (terminalCapCandidate state supply capBinders)
        (terminalTyCandidate state supply tyBinders)).apply target =
      state.prevailing.apply
        ((Subst.mk (InferenceBase.freshCapSubst supply.nextCap capBinders)
          (InferenceBase.freshTySubst supply.nextTy tyBinders)).apply target) := by
  rw [← Subst.seq_apply]
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    have member := capsScoped varId membership
    simp [terminalCapCandidate, InferenceBase.freshCapSubst, member,
      Subst.seq, CapSubst.comp, Cap.apply]
  · intro varId membership
    have member := tysScoped varId membership
    simp [terminalTyCandidate, InferenceBase.freshTySubst, member,
      Subst.seq]

/-- Closedness says every capability leaf of each constructor argument and
result is covered by the quantified binder batch. -/
theorem CtorScheme.Closed.cap_scoped
    {scheme : CtorScheme} (closed : scheme.Closed) :
    (∀ target, target ∈ scheme.args → ∀ varId,
      varId ∈ target.fcv → varId ∈ scheme.capBinders) ∧
    (∀ varId, varId ∈ scheme.result.fcv →
      varId ∈ scheme.capBinders) := by
  constructor
  · intro target targetMem varId varMem
    by_cases member : varId ∈ scheme.capBinders
    · exact member
    · exfalso
      have free : varId ∈ scheme.fcv := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_append.mpr (Or.inl
          (Ty.mem_fcvList_of_mem targetMem varMem)), by simpa using member⟩
      rw [closed.1] at free
      exact nomatch free
  · intro varId varMem
    by_cases member : varId ∈ scheme.capBinders
    · exact member
    · exfalso
      have free : varId ∈ scheme.fcv := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_append.mpr (Or.inr varMem), by simpa using member⟩
      rw [closed.1] at free
      exact nomatch free

/-- Target-variable counterpart of `CtorScheme.Closed.cap_scoped`. -/
theorem CtorScheme.Closed.ty_scoped
    {scheme : CtorScheme} (closed : scheme.Closed) :
    (∀ target, target ∈ scheme.args → ∀ varId,
      varId ∈ target.ftv → varId ∈ scheme.tyBinders) ∧
    (∀ varId, varId ∈ scheme.result.ftv →
      varId ∈ scheme.tyBinders) := by
  constructor
  · intro target targetMem varId varMem
    by_cases member : varId ∈ scheme.tyBinders
    · exact member
    · exfalso
      have free : varId ∈ scheme.ftv := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_append.mpr (Or.inl
          (Ty.mem_ftvList_of_mem targetMem varMem)), by simpa using member⟩
      rw [closed.2] at free
      exact nomatch free
  · intro varId varMem
    by_cases member : varId ∈ scheme.tyBinders
    · exact member
    · exfalso
      have free : varId ∈ scheme.ftv := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_append.mpr (Or.inr varMem), by simpa using member⟩
      rw [closed.2] at free
      exact nomatch free

/-- A constructor-instantiation event for a closed scheme has the canonical
terminal witness at every later solver cut.  Unlike the emission-only lemma,
this permits structural specialization of quantified capability images. -/
theorem ctorInstanceEventCondition_atTerminal
    {state : InferState} {solveCount : Nat}
    {supply : InferenceBase.FreshSupply} {scheme : CtorScheme}
    (closed : scheme.Closed)
    (solveBound : solveCount ≤ state.trace.solves.length) :
    CanonicalInstanceEventCondition state
      (.ctorInstantiation solveCount supply scheme
        (InferenceBase.instantiateCtorScheme supply scheme).value.1
        (InferenceBase.instantiateCtorScheme supply scheme).value.2
        (freshCapImages supply scheme.capBinders)) := by
  simp only [CanonicalInstanceEventCondition]
  refine ⟨solveBound, ?_, ?_⟩
  · change scheme.args.map _ =
      (scheme.args.map
        (Subst.mk (InferenceBase.freshCapSubst supply.nextCap
          scheme.capBinders)
          (InferenceBase.freshTySubst supply.nextTy
            scheme.tyBinders)).apply).map state.prevailing.apply
    rw [List.map_map]
    apply List.map_congr_left
    intro target targetMem
    exact terminalCandidates_apply_of_scoped
      ((CtorScheme.Closed.cap_scoped closed).1 target targetMem)
      ((CtorScheme.Closed.ty_scoped closed).1 target targetMem)
  · exact terminalCandidates_apply_of_scoped
      (CtorScheme.Closed.cap_scoped closed).2
      (CtorScheme.Closed.ty_scoped closed).2

/-- For a closed dual scheme, replaying the canonical fresh opening through
the terminal executable substitution is the binder-local post operation used
by `DualScheme.post_apply`. -/
theorem dualTerminalCandidates_eq_post
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (scheme : DualScheme) :
    terminalCapCandidate state supply scheme.capBinders =
        scheme.postCap state.prevailing
          (InferenceBase.freshCapSubst supply.nextCap scheme.capBinders) ∧
      terminalTyCandidate state supply scheme.tyBinders =
        scheme.postTarget state.prevailing
          (InferenceBase.freshTySubst supply.nextTy scheme.tyBinders) := by
  constructor
  · funext varId
    by_cases membership : varId ∈ scheme.capBinders <;>
      simp [terminalCapCandidate, DualScheme.postCap,
        InferenceBase.freshCapSubst, membership, Cap.apply]
  · funext varId
    by_cases membership : varId ∈ scheme.tyBinders <;>
      simp [terminalTyCandidate, DualScheme.postTarget,
        InferenceBase.freshTySubst, membership]

/-- One body dual of a closed scheme commutes with the canonical terminal
opening.  This is the dual-scheme analogue of
`terminalCandidates_apply_of_scoped`. -/
theorem DualScheme.Closed.terminal_apply
    {scheme : DualScheme} (closed : scheme.Closed)
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (dual : Dual)
    (capScope : ∀ varId, varId ∈ dual.fcv →
      varId ∈ scheme.args.flatMap Dual.fcv ++ scheme.result.fcv)
    (tyScope : ∀ varId, varId ∈ dual.ftv →
      varId ∈ scheme.args.flatMap Dual.ftv ++ scheme.result.ftv) :
    dual.apply (terminalCapCandidate state supply scheme.capBinders)
        (terminalTyCandidate state supply scheme.tyBinders) =
      (dual.apply
          (InferenceBase.freshCapSubst supply.nextCap scheme.capBinders)
          (InferenceBase.freshTySubst supply.nextTy scheme.tyBinders)
        ).applySubst state.prevailing := by
  rw [(dualTerminalCandidates_eq_post state supply scheme).1,
    (dualTerminalCandidates_eq_post state supply scheme).2]
  apply DualScheme.post_apply
  · exact InferenceBase.instantiateBinders_cap_support supply
      scheme.capBinders scheme.tyBinders
  · exact InferenceBase.instantiateBinders_ty_support supply
      scheme.capBinders scheme.tyBinders
  · intro varId membership
    rw [closed.1] at membership
    exact nomatch membership
  · intro varId membership
    rw [closed.2] at membership
    exact nomatch membership
  · exact capScope
  · exact tyScope

/-- A protected canonical capability image is variable-valued at the final
executable cut. -/
theorem terminalCapCandidate_variable_of_protected
    {state : InferState} {supply : InferenceBase.FreshSupply}
    {binders : List CapVar}
    (producerSafe : ProtectedProducerTrace state)
    (freshProtected : ∀ image, image ∈ freshCapImages supply binders →
      image ∈ state.protectedCaps)
    {binder : CapVar} (membership : binder ∈ binders) :
    ∃ image,
      terminalCapCandidate state supply binders binder = .var image := by
  let fresh : CapVar := ⟨supply.nextCap + binder.id⟩
  have freshMembership : fresh ∈ freshCapImages supply binders := by
    exact List.mem_map.mpr ⟨binder, membership, rfl⟩
  rcases producerSafe fresh (freshProtected fresh freshMembership) with
    ⟨image, equation, _safe⟩
  refine ⟨image, ?_⟩
  simpa [terminalCapCandidate, InferenceBase.freshCapSubst, membership,
    fresh, InferState.prevailing] using equation

/-- A closed dual-scheme instantiation has the validator's exact canonical
terminal witness.  The variable-image fact is derived internally from the
protected-producer invariant; callers only transport membership of the
freshly protected batch to the final state. -/
theorem dualInstanceEventCondition_atTerminal
    {state : InferState} {solveCount : Nat}
    {supply : InferenceBase.FreshSupply} {scheme : DualScheme}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {fixedCaps reservedCaps : List CapVar}
    {fixedTys reservedTys : List TypePM.TyVar}
    (closed : scheme.Closed)
    (solveBound : solveCount ≤ state.trace.solves.length)
    (producerSafe : ProtectedProducerTrace state)
    (freshProtected : ∀ image,
      image ∈ freshCapImages supply scheme.capBinders →
        image ∈ state.protectedCaps) :
    CanonicalInstanceEventCondition state
      (.dualInstantiation solveCount supply scheme rawContext rawParameters
        rawBindings context parameters bindings fixedCaps fixedTys
        reservedCaps reservedTys
        (InferenceBase.instantiateDualScheme supply scheme).value.1
        (InferenceBase.instantiateDualScheme supply scheme).value.2
        (freshCapImages supply scheme.capBinders)
        (freshTyImages supply scheme.tyBinders)) := by
  simp only [CanonicalInstanceEventCondition]
  refine ⟨solveBound, ?_, ?_, ?_⟩
  · intro varId membership
    exact terminalCapCandidate_variable_of_protected producerSafe freshProtected
      membership
  · change scheme.args.map _ =
      (scheme.args.map
        (Dual.apply
          (InferenceBase.freshCapSubst supply.nextCap scheme.capBinders)
          (InferenceBase.freshTySubst supply.nextTy scheme.tyBinders))).map
        (Dual.applySubst state.prevailing)
    rw [List.map_map]
    apply List.map_congr_left
    intro dual dualMem
    apply DualScheme.Closed.terminal_apply closed state supply dual
    · intro varId varMem
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMem, varMem⟩)
    · intro varId varMem
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMem, varMem⟩)
  · apply DualScheme.Closed.terminal_apply closed state supply scheme.result
    · intro varId varMem
      exact List.mem_append_right _ varMem
    · intro varId varMem
      exact List.mem_append_right _ varMem

/-- Constructor instantiation itself establishes the canonical instance
clause at its emission cut.  Later suffix transport is the only remaining
obligation for the surrounding completeness recursion. -/
theorem instantiateCtorInState_canonicalInstanceAtEmission
    {state : InferState} (scheme : CtorScheme)
    (bounded : state.prevailing.BoundedBy state.supply)
    (argsFixed : ∀ target, target ∈ scheme.args →
      state.prevailing.apply
          ((InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
            target) =
        (InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
          target)
    (resultFixed : state.prevailing.apply
        ((InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
          scheme.result) =
      (InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
        scheme.result) :
    let instantiated := InferenceBase.instantiateCtorScheme state.supply scheme
    let output := (instantiateCtorInState state scheme).2
    CanonicalInstanceEventCondition output
      (.ctorInstantiation state.trace.solves.length state.supply scheme
        instantiated.value.1 instantiated.value.2
        (freshCapImages state.supply scheme.capBinders)) := by
  let output := (instantiateCtorInState state scheme).2
  have outputBounded : output.prevailing.BoundedBy state.supply := by
    change state.prevailing.BoundedBy state.supply
    exact bounded
  have outputPrevailing : output.prevailing = state.prevailing := by
    rfl
  change CanonicalInstanceEventCondition output
    (.ctorInstantiation state.trace.solves.length state.supply scheme
      (InferenceBase.instantiateCtorScheme state.supply scheme).value.1
      (InferenceBase.instantiateCtorScheme state.supply scheme).value.2
      (freshCapImages state.supply scheme.capBinders))
  simp only [CanonicalInstanceEventCondition]
  constructor
  · simp [output, instantiateCtorInState, InferState.recordEvent]
  · have capEq := terminalCapCandidate_eq_freshCapSubst_of_bounded
      outputBounded scheme.capBinders
    have tyEq := terminalTyCandidate_eq_freshTySubst_of_bounded
      outputBounded scheme.tyBinders
    rw [capEq, tyEq]
    constructor
    · rw [outputPrevailing]
      change
        List.map
            (InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
            scheme.args =
          List.map state.prevailing.apply
            (List.map
              (InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
              scheme.args)
      rw [List.map_map]
      apply List.map_congr_left
      intro target membership
      exact (argsFixed target membership).symm
    · rw [outputPrevailing]
      change
        (InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
            scheme.result =
          state.prevailing.apply
            ((InferenceBase.instantiateCtorScheme state.supply scheme).subst.apply
              scheme.result)
      exact resultFixed.symm

/-- Expected-slot events use the exact canonical witness selected by the
finite checker, so adding one needs no global trace premise. -/
theorem slotEventCondition
    {signature : FrozenSig} {state : InferState}
    {start stop : Nat} {inferred requested : Ty}
    (startStop : start ≤ stop) (stopBound : stop ≤ state.trace.solves.length)
    (canonical : CanonicalSlotAlignmentAtTerminal
      (solveSlice state.trace start stop)
      (solveSlice state.trace start state.trace.solves.length)
      inferred requested) :
    TraversalValidatorEventCondition signature state
      (.slotAlignment start stop inferred requested) := by
  refine ⟨⟨by simp [PrimitiveHoleEventCondition]⟩,
    ⟨by simp [PatternLeafEventCondition]⟩,
    ⟨by simp [CanonicalInstanceEventCondition]⟩, ⟨?_⟩⟩
  exact ⟨startStop, stopBound, canonical⟩

/-! ## Direct executable leaf branches -/

/-- The executable primitive-hole branch preserves the complete hole fold.
All intermediate events are non-hole events; the final event carries exactly
the capability allocated from the incoming supply. -/
theorem inferPPatFuel_hole_primitiveHoles
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath} {target : Ty}
    {state : InferState} {result : PPatResult}
    (before : TracePrimitiveHoleConditions signature state.trace)
    (signatureBelow : InferenceBase.CapVarsBelow state.supply
      signature.capVars)
    (targetBounded : target.BoundedBy state.supply)
    (success : inferPPatFuel (fuel + 1) signature path .hole target state =
      some result) :
    TracePrimitiveHoleConditions signature result.state.trace := by
  simp only [inferPPatFuel, Option.some.injEq] at success
  subst result
  intro event membership
  simp only [InferState.freshCap, InferenceBase.freshCapMeta, visit,
    InferState.recordEvent, List.mem_append, List.mem_singleton] at membership
  rcases membership with (((previous | fresh) | visited) | inferred)
  · exact before event previous
  · subst event
    trivial
  · subst event
    trivial
  · subst event
    change ∃ varId : CapVar,
      [Dual.mk (.var ⟨state.supply.nextCap⟩) target] =
          [Dual.mk (.var varId) target] ∧
        ([] : MonoCtx) = [] ∧
        varId ∉ signature.capVars ∧ varId ∉ target.fcv
    exact ⟨⟨state.supply.nextCap⟩, rfl, rfl,
      nextCap_not_mem_of_below signatureBelow,
      nextCap_not_mem_of_below targetBounded.caps⟩

/-- The executable pattern-variable branch preserves the user-leaf fold and
adds the exact paired fresh-allocation event. -/
theorem inferPatternFuel_var_patternLeaves
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {state : InferState}
    {result : PatternResult}
    (before : TracePatternLeafConditions signature state.trace)
    (signatureCaps : InferenceBase.CapVarsBelow state.supply signature.capVars)
    (contextCaps : InferenceBase.CapVarsBelow state.supply context.fcv)
    (parameterCaps : InferenceBase.CapVarsBelow state.supply parameters.fcv)
    (bindingCaps : InferenceBase.CapVarsBelow state.supply bindings.fcv)
    (signatureTys : InferenceBase.TyVarsBelow state.supply signature.tyVars)
    (contextTys : InferenceBase.TyVarsBelow state.supply context.ftv)
    (parameterTys : InferenceBase.TyVarsBelow state.supply parameters.ftv)
    (bindingTys : InferenceBase.TyVarsBelow state.supply bindings.ftv)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pvar name) state = some result) :
    TracePatternLeafConditions signature result.state.trace := by
  simp only [inferPatternFuel] at success
  split at success
  · contradiction
  · simp only [Option.some.injEq] at success
    subst result
    intro event membership
    simp only [InferState.freshCap, InferState.freshTy,
      InferenceBase.freshCapMeta, InferenceBase.freshTyMeta, visit,
      InferState.recordEvent, List.mem_append, List.mem_singleton] at membership
    rcases membership with (((((previous | freshCap) | freshTy) | leaf) |
      visited) | inferred)
    · exact before event previous
    · subst event
      trivial
    · subst event
      trivial
    · subst event
      exact ⟨nextCap_not_mem_of_below signatureCaps,
        nextCap_not_mem_of_below contextCaps,
        nextCap_not_mem_of_below parameterCaps,
        nextCap_not_mem_of_below bindingCaps,
        nextTy_not_mem_of_below signatureTys,
        nextTy_not_mem_of_below contextTys,
        nextTy_not_mem_of_below parameterTys,
        nextTy_not_mem_of_below bindingTys⟩
    · subst event
      trivial
    · subst event
      trivial

/-- Wildcard traversal has the same paired allocation boundary as a named
pattern variable. -/
theorem inferPatternFuel_wild_patternLeaves
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {state : InferState} {result : PatternResult}
    (before : TracePatternLeafConditions signature state.trace)
    (signatureCaps : InferenceBase.CapVarsBelow state.supply signature.capVars)
    (contextCaps : InferenceBase.CapVarsBelow state.supply context.fcv)
    (parameterCaps : InferenceBase.CapVarsBelow state.supply parameters.fcv)
    (bindingCaps : InferenceBase.CapVarsBelow state.supply bindings.fcv)
    (signatureTys : InferenceBase.TyVarsBelow state.supply signature.tyVars)
    (contextTys : InferenceBase.TyVarsBelow state.supply context.ftv)
    (parameterTys : InferenceBase.TyVarsBelow state.supply parameters.ftv)
    (bindingTys : InferenceBase.TyVarsBelow state.supply bindings.ftv)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path .wild state = some result) :
    TracePatternLeafConditions signature result.state.trace := by
  simp only [inferPatternFuel, Option.some.injEq] at success
  subst result
  intro event membership
  simp only [InferState.freshCap, InferState.freshTy,
    InferenceBase.freshCapMeta, InferenceBase.freshTyMeta, visit,
    InferState.recordEvent, List.mem_append, List.mem_singleton] at membership
  rcases membership with (((((previous | freshCap) | freshTy) | leaf) |
    visited) | inferred)
  · exact before event previous
  · subst event
    trivial
  · subst event
    trivial
  · subst event
    exact ⟨nextCap_not_mem_of_below signatureCaps,
      nextCap_not_mem_of_below contextCaps,
      nextCap_not_mem_of_below parameterCaps,
      nextCap_not_mem_of_below bindingCaps,
      nextTy_not_mem_of_below signatureTys,
      nextTy_not_mem_of_below contextTys,
      nextTy_not_mem_of_below parameterTys,
      nextTy_not_mem_of_below bindingTys⟩
  · subst event
    trivial
  · subst event
    trivial

end Reconstruction
end Inference
end TypePM
