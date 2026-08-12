import TypePM.DemandTypingInferenceCompletenessValidatorIntrinsic
import TypePM.InferenceTraversalStateExtension
import TypePM.PolyInstantiationTransport

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

/-- Pointwise root-trace form of the four traversal validator folds.  This is
the convenient elimination interface for a completed root run: classify one
event membership by the syntax node that emitted it, rather than maintaining
four parallel universal predicates. -/
def TraversalValidatorEventCoverage
    (signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events →
    TraversalValidatorEventCondition signature state event

/-- Pointwise root-event coverage packages directly into the four validator
folds consumed by `wBridgeCheck_complete`. -/
theorem TraversalValidatorConditions.ofEventCoverage
    {signature : FrozenSig} {state : InferState}
    (coverage : TraversalValidatorEventCoverage signature state) :
    TraversalValidatorConditions signature state := by
  constructor
  · intro event membership
    exact (coverage event membership).primitiveHole.holds
  · intro event membership
    exact (coverage event membership).patternLeaf.holds
  · intro event membership
    exact (coverage event membership).canonicalInstance.holds
  · intro event membership
    exact (coverage event membership).slot.holds

/-- Conversely, the packaged folds justify every root trace event. -/
theorem TraversalValidatorConditions.eventCoverage
    {signature : FrozenSig} {state : InferState}
    (conditions : TraversalValidatorConditions signature state) :
    TraversalValidatorEventCoverage signature state := by
  intro event membership
  exact
    { primitiveHole := ⟨conditions.primitiveHoles event membership⟩
      patternLeaf := ⟨conditions.patternLeaves event membership⟩
      canonicalInstance := ⟨conditions.instances event membership⟩
      slot := ⟨conditions.slots event membership⟩ }

theorem traversalValidatorEventCoverage_iff
    (signature : FrozenSig) (state : InferState) :
    TraversalValidatorEventCoverage signature state ↔
      TraversalValidatorConditions signature state :=
  ⟨TraversalValidatorConditions.ofEventCoverage,
    TraversalValidatorConditions.eventCoverage⟩

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

/-- Canonical expression-scheme opening commutes with the terminal executable
substitution when the protected capability images remain variables. -/
theorem schemeCanonicalOpening_atTerminal
    (state : InferState) (supply : InferenceBase.FreshSupply)
    (scheme : Scheme)
    (capVariable : ∀ index : Fin scheme.capArity,
      ∃ image, state.prevailing.cap
          ((Scheme.canonicalFreshOpening supply scheme).capImage index) =
        .var image) :
    (scheme.applyMeta state.prevailing).openValue
        (terminalSchemeOpening state supply
          (scheme.applyMeta state.prevailing)) =
      state.prevailing.apply
        (InferenceBase.instantiateScheme supply scheme).value := by
  let opening :=
    (Scheme.canonicalFreshOpening supply scheme).toValueOpening
  let post : opening.Post state.prevailing :=
    { capImage := fun index =>
        match state.prevailing.cap
            ((Scheme.canonicalFreshOpening supply scheme).capImage index) with
        | .var image => image
        | _ => (Scheme.canonicalFreshOpening supply scheme).capImage index
      capEquation := by
        intro index
        rcases capVariable index with ⟨image, equation⟩
        change state.prevailing.cap
            ((Scheme.canonicalFreshOpening supply scheme).capImage index) =
          .var (match state.prevailing.cap
              ((Scheme.canonicalFreshOpening supply scheme).capImage index) with
            | .var image => image
            | _ => (Scheme.canonicalFreshOpening supply scheme).capImage index)
        rw [equation] }
  rw [InferenceBase.instantiateScheme_value]
  rw [← Scheme.openValue_applyMeta state.prevailing opening post]
  congr

/-- The protected-producer trace supplies the local variable-image premise of
`schemeCanonicalOpening_atTerminal` for a canonical fresh opening. -/
theorem schemeCanonicalOpening_atTerminal_of_protected
    {state : InferState} {supply : InferenceBase.FreshSupply}
    {scheme : Scheme}
    (producerSafe : ProtectedProducerTrace state)
    (freshProtected : ∀ image,
      image ∈ Scheme.canonicalCapImages supply scheme →
        image ∈ state.protectedCaps) :
    (scheme.applyMeta state.prevailing).openValue
        (terminalSchemeOpening state supply
          (scheme.applyMeta state.prevailing)) =
      state.prevailing.apply
        (InferenceBase.instantiateScheme supply scheme).value := by
  apply schemeCanonicalOpening_atTerminal
  intro index
  let fresh := (Scheme.canonicalFreshOpening supply scheme).capImage index
  have freshMembership : fresh ∈ Scheme.canonicalCapImages supply scheme := by
    rw [Scheme.canonicalCapImages, Scheme.FreshOpening.capImages,
      List.mem_ofFn]
    exact ⟨index, rfl⟩
  rcases producerSafe fresh (freshProtected fresh freshMembership) with
    ⟨image, equation, _safe⟩
  exact ⟨image, by simpa [InferState.prevailing, fresh] using equation⟩

/-- A context lookup whose terminal scheme is the ambiently substituted
recorded scheme has the validator's exact canonical expression-instance
witness.  The lookup equality is deliberately exposed: the completeness
recursion obtains it from final context bisimulation, while capability-image
safety is discharged here from the protected-producer invariant. -/
theorem schemeInstanceEventCondition_atTerminal
    {state : InferState} {solveCount : Nat}
    {supply : InferenceBase.FreshSupply} {scheme : Scheme}
    {name : String} {rawContext context : Context}
    {fixedCaps reservedCaps : List CapVar}
    {fixedTys reservedTys : List TypePM.TyVar}
    (solveBound : solveCount ≤ state.trace.solves.length)
    (terminalLookup :
      (rawContext.applySubst state.prevailing).find? name =
        some (scheme.applyMeta state.prevailing))
    (producerSafe : ProtectedProducerTrace state)
    (freshProtected : ∀ image,
      image ∈ Scheme.canonicalCapImages supply scheme →
        image ∈ state.protectedCaps) :
    CanonicalInstanceEventCondition state
      (.schemeInstantiation solveCount supply scheme name rawContext context
        fixedCaps fixedTys reservedCaps reservedTys
        (InferenceBase.instantiateScheme supply scheme).value
        (Scheme.canonicalCapImages supply scheme)
        (Scheme.canonicalTyImages supply scheme)) := by
  simp only [CanonicalInstanceEventCondition]
  refine ⟨solveBound, scheme.applyMeta state.prevailing, terminalLookup, ?_, ?_⟩
  · intro varId membership
    have imagesEq :
        Scheme.canonicalCapImages supply (scheme.applyMeta state.prevailing) =
          Scheme.canonicalCapImages supply scheme := by
      cases scheme
      rfl
    rw [imagesEq] at membership
    rcases producerSafe varId (freshProtected varId membership) with
      ⟨image, equation, _safe⟩
    exact ⟨image, by simpa [InferState.prevailing] using equation⟩
  · exact schemeCanonicalOpening_atTerminal_of_protected producerSafe
      freshProtected

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

/-! ## Canonical slot suffix transport -/

/-- The canonical slot witness for a matcher-to-slot step followed by an
arbitrary solver suffix.  The witness replays the complete suffix, including
later structural specialization of capability metavariables. -/
theorem canonicalSlotAlignment_matcherToSlot_suffix
    {step : SolveStep} {suffix : List SolveStep}
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (constraintEq : step.constraint = .producerToSlot producerCap
      producerTarget consumerCap consumerTarget) :
    CanonicalSlotAlignmentAtTerminal [step] ([step] ++ suffix)
      (.matcher producerCap producerTarget)
      (.slot consumerCap consumerTarget) := by
  apply CanonicalSlotAlignmentAtTerminal.matcherToSlot
      (step := step) rfl rfl rfl constraintEq
  · simp only [List.cons_append, List.nil_append, applyDeltas,
      List.tail_cons]
    have equation := replayFrom_apply Subst.id suffix
      (step.delta.apply (.matcher producerCap producerTarget))
    rw [Subst.apply_id] at equation
    simpa only [Subst.apply_matcher, replay] using equation.symm
  · simp only [List.cons_append, List.nil_append, applyDeltas,
      List.tail_cons]
    have equation := replayFrom_apply Subst.id suffix
      (step.delta.apply (.slot consumerCap consumerTarget))
    rw [Subst.apply_id] at equation
    simpa only [Subst.apply_slot, replay] using equation.symm

/-- Package a terminal equality as the exact event condition consumed by the
slot validator. -/
theorem canonicalSlotEventCondition_equal
    {state : InferState} {start stop : Nat} {inferred requested : Ty}
    (startStop : start ≤ stop)
    (stopBound : stop ≤ state.trace.solves.length)
    (aligned : applyDeltas
        (solveSlice state.trace start state.trace.solves.length) inferred =
      applyDeltas
        (solveSlice state.trace start state.trace.solves.length) requested) :
    CanonicalSlotEventCondition state
      (.slotAlignment start stop inferred requested) := by
  exact ⟨startStop, stopBound,
    CanonicalSlotAlignmentAtTerminal.equal aligned⟩

/-- Package the one-step matcher-to-slot transport above at concrete trace
indices.  The surrounding traversal need only identify the local step and the
remaining suffix. -/
theorem canonicalSlotEventCondition_matcherToSlot
    {state : InferState} {start stop : Nat} {step : SolveStep}
    {suffix : List SolveStep} {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    (startStop : start ≤ stop)
    (stopBound : stop ≤ state.trace.solves.length)
    (localSlice : solveSlice state.trace start stop = [step])
    (terminalSlice :
      solveSlice state.trace start state.trace.solves.length =
        [step] ++ suffix)
    (constraintEq : step.constraint = .producerToSlot producerCap
      producerTarget consumerCap consumerTarget) :
    CanonicalSlotEventCondition state
      (.slotAlignment start stop (.matcher producerCap producerTarget)
        (.slot consumerCap consumerTarget)) := by
  refine ⟨startStop, stopBound, ?_⟩
  rw [localSlice, terminalSlice]
  exact canonicalSlotAlignment_matcherToSlot_suffix constraintEq

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

/-! ## Expected-alignment emitter -/

/-- If an expected-type alignment has made its raw endpoints equal at the
local output cut, the emitted resolved views satisfy the canonical equality
branch after every later traversal suffix. -/
theorem alignedEqual_canonicalSlotEventCondition
    {state aligned terminal : InferState} {raw expected : Ty}
    (alignmentHistory : state.HistoryPrefix aligned)
    (equal : aligned.prevailing.apply raw = aligned.prevailing.apply expected)
    (history : (aligned.recordEvent (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (state.prevailing.apply raw)
      (state.prevailing.apply expected))).HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (state.prevailing.apply raw)
      (state.prevailing.apply expected)) := by
  have alignedToTerminal : aligned.HistoryPrefix terminal :=
    (InferState.historyPrefix_recordEvent aligned _).trans history
  have totalHistory := alignmentHistory.trans alignedToTerminal
  have terminalEqual : terminal.prevailing.apply raw =
      terminal.prevailing.apply expected :=
    HistoryPrefix.final_type_eq alignedToTerminal equal
  have rawReplay := history_terminal_apply_eq totalHistory raw
  have expectedReplay := history_terminal_apply_eq totalHistory expected
  apply canonicalSlotEventCondition_equal alignmentHistory.solve_length_le
    alignedToTerminal.solve_length_le
  rw [← rawReplay, ← expectedReplay]
  exact terminalEqual

/-- A DD alignment whose input views are both slots has equal output
endpoints.  Other DD constructors are excluded by their resolved-head
premises. -/
theorem DDAlignWithLedger.output_equal_of_slotViews
    {ledger : CapabilityOriginLedger} {S S' : Subst} {raw expected : Ty}
    {sourceCap requestedCap : Cap} {sourceTarget requestedTarget : Ty}
    (aligned : DDAlignWithLedger ledger S raw expected S')
    (rawView : S.apply raw = .slot sourceCap sourceTarget)
    (expectedView : S.apply expected = .slot requestedCap requestedTarget) :
    S'.apply raw = S'.apply expected := by
  cases aligned with
  | productMatcherLift matcherView _ _ =>
      simp [rawView, productMatcherDuals?] at matcherView
  | slotTupleLift _ slotView _ _ _ =>
      simp [rawView, productSlotDuals?] at slotView
  | matcherToSlot matcherView _ _ => simp [rawView] at matcherView
  | slotToSlot actualRaw actualExpected capSafe targetSafe =>
      simp only [Subst.seq_apply]
      rw [actualRaw, actualExpected]
      have capEquality := capSafe.exact.1.1
      have targetEquality := targetSafe.exact.1.1
      simp only [Subst.apply] at targetEquality
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.applyTarget_id]
      rw [capEquality, targetEquality]
  | ordinary demand _ =>
      simp [demandClass, rawView, expectedView, productMatcherDuals?,
        productSlotDuals?] at demand

/-- The ordinary DD alignment constructor exposes its output equality without
passing through runtime erasure. -/
theorem DDAlignWithLedger.output_equal_of_ordinary
    {ledger : CapabilityOriginLedger} {S S' : Subst} {raw expected : Ty}
    (aligned : DDAlignWithLedger ledger S raw expected S')
    (ordinary : demandClass (S.apply raw) (S.apply expected) = .ordinary) :
    S'.apply raw = S'.apply expected := by
  cases aligned with
  | productMatcherLift rawView expectedView _ =>
      simp [demandClass, rawView, expectedView] at ordinary
  | slotTupleLift demand _ _ _ _ => simp [demand] at ordinary
  | matcherToSlot rawView expectedView _ =>
      simp [demandClass, rawView, expectedView, productMatcherDuals?,
        productSlotDuals?] at ordinary
  | slotToSlot rawView expectedView _ _ =>
      simp [demandClass, rawView, expectedView, productMatcherDuals?,
        productSlotDuals?] at ordinary
  | ordinary _ aligned => exact aligned.output_equal

/-- A successful resolved producer-to-slot solve, followed by any later
solver suffix, supplies the exact canonical witness for the slot event emitted
at that checking cut. -/
theorem runResolvedConstraint_producerToSlot_canonicalSlotEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    (success : runResolvedConstraint state origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) =
        some aligned)
    (history : (aligned.recordEvent (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (.matcher producerCap producerTarget)
      (.slot consumerCap consumerTarget))).HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (.matcher producerCap producerTarget)
      (.slot consumerCap consumerTarget)) := by
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      dsimp at success
      split at success
      · have alignedEq := Option.some.inj success
        subst aligned
        rcases history with ⟨suffix, eventSuffix, solves, events⟩
        have solves' : terminal.trace.solves =
            (state.trace.solves ++ [step]) ++ suffix := by
          simpa [InferState.recordEvent, InferState.recordSolve] using solves
        have startStop : state.trace.solves.length ≤
            (state.recordSolve step).trace.solves.length := by
          simp [InferState.recordSolve]
        have stopBound : (state.recordSolve step).trace.solves.length ≤
            terminal.trace.solves.length := by
          rw [solves', List.length_append]
          simp only [InferState.recordSolve, List.length_append,
            List.length_singleton]
          exact Nat.le_add_right _ _
        have localSlice : solveSlice terminal.trace
            state.trace.solves.length
            (state.recordSolve step).trace.solves.length = [step] := by
          have stopEq : (state.recordSolve step).trace.solves.length =
              (state.trace.solves ++ [step]).length := by
            rfl
          rw [solveSlice, stopEq, solves',
            List.take_append_of_le_length (Nat.le_refl _),
            List.take_length,
            List.drop_append_length]
        have terminalSlice : solveSlice terminal.trace
            state.trace.solves.length terminal.trace.solves.length =
              [step] ++ suffix := by
          simp only [solveSlice]
          rw [List.take_length, solves', List.append_assoc,
            List.drop_append_length]
        have constraintEq : step.constraint = .producerToSlot producerCap
            producerTarget consumerCap consumerTarget := by
          change solveProducerToSlotWithLedger state.capabilityOrigins
            state.trace.solves.length origin producerCap producerTarget
            consumerCap consumerTarget = some step at stepEq
          unfold solveProducerToSlotWithLedger at stepEq
          split at stepEq
          · contradiction
          · simp only at stepEq
            split at stepEq
            · split at stepEq
              · contradiction
              · exact (congrArg SolveStep.constraint
                  (Option.some.inj stepEq)).symm
            · contradiction
        exact canonicalSlotEventCondition_matcherToSlot startStop stopBound
          localSlice terminalSlice constraintEq
      · contradiction

/-- Direct canonical-slot emitter for the raw expected-type alignment.  Its
three executable branches reduce respectively to one-way matcher coercion,
slot equality, and ordinary type equality. -/
theorem alignAtSlot_canonicalSlotEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {raw expected : Ty}
    (success : alignAtSlot state origin raw expected = some aligned)
    (history : (aligned.recordEvent (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (state.prevailing.apply raw)
      (state.prevailing.apply expected))).HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (state.prevailing.apply raw)
      (state.prevailing.apply expected)) := by
  have original := success
  have alignmentHistory := alignAtSlot_historyPrefix original
  unfold alignAtSlot at success
  simp only at success
  split at success
  · rename_i producerCap producerTarget consumerCap consumerTarget rawView
      expectedView
    rw [rawView, expectedView] at history ⊢
    exact runResolvedConstraint_producerToSlot_canonicalSlotEventCondition
      success history
  · rename_i sourceCap sourceTarget requestedCap requestedTarget rawView
      expectedView
    rcases alignAtSlot_slotToSlot_ddAlignRun rawView expectedView original with
      ⟨_supplyEq, _ledgerEq, alignedDD⟩
    exact alignedEqual_canonicalSlotEventCondition alignmentHistory
      (DDAlignWithLedger.output_equal_of_slotViews alignedDD rawView
        expectedView) history
  · rcases alignTypes_ddAlignTypesRun success with
      ⟨_supplyEq, _ledgerEq, alignedDD⟩
    exact alignedEqual_canonicalSlotEventCondition alignmentHistory
      alignedDD.output_equal history

/-- The explicit product-matcher lift emits the same one-way solver event,
with the lifted unary matcher as its source. -/
theorem alignResolvedProductMatcherAtSlot_canonicalSlotEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedProductMatcherAtSlot state origin duals consumerCap
      consumerTarget = some aligned)
    (history : (aligned.recordEvent (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (productMatcherTarget duals)
      (.slot consumerCap consumerTarget))).HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (productMatcherTarget duals) (.slot consumerCap consumerTarget)) := by
  unfold alignResolvedProductMatcherAtSlot at success
  exact runResolvedConstraint_producerToSlot_canonicalSlotEventCondition
    success history

/-- The two-step slot-tuple lift first equates capabilities and then equates
the capability-adjusted targets.  Replaying those two exact deltas therefore
makes the two slot endpoints equal; every later suffix preserves that
equality. -/
theorem alignResolvedSlotTupleAtSlot_canonicalSlotEventCondition
    {state aligned terminal : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedSlotTupleAtSlot state origin duals consumerCap
      consumerTarget = some aligned)
    (history : (aligned.recordEvent (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (slotTupleTarget duals)
      (.slot consumerCap consumerTarget))).HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      state.trace.solves.length aligned.trace.solves.length
      (slotTupleTarget duals) (.slot consumerCap consumerTarget)) := by
  unfold alignResolvedSlotTupleAtSlot at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨capStep, capSuccess, targetSuccess⟩
  unfold runResolvedConstraint at targetSuccess
  rcases Option.bind_eq_some_iff.mp targetSuccess with
    ⟨targetStep, targetEq, finalEq⟩
  have alignedEq : (state.recordSolve capStep).recordSolve targetStep =
      aligned := Option.some.inj finalEq
  subst aligned
  ·
      have capExact :=
        (solveResolvedWithLedger_capEq_originSafeExactCapMGU capSuccess).2.exact.1.1
      have targetExact :=
        (solveResolvedWithLedger_targetEq_originSafeExactPairedMGU
          targetEq).exact.1.1
      have localEqual :
          applyDeltas [capStep, targetStep] (slotTupleTarget duals) =
            applyDeltas [capStep, targetStep]
              (.slot consumerCap consumerTarget) := by
        simp only [applyDeltas, slotTupleTarget, Subst.apply_slot]
        rw [capExact, targetExact]
      rcases history with ⟨suffix, eventSuffix, solves, events⟩
      have solves' : terminal.trace.solves =
          (state.trace.solves ++ [capStep, targetStep]) ++ suffix := by
        simpa [InferState.recordEvent, InferState.recordSolve,
          List.append_assoc] using solves
      have startStop : state.trace.solves.length ≤
          ((state.recordSolve capStep).recordSolve targetStep).trace.solves.length := by
        simp [InferState.recordSolve]
      have stopBound :
          ((state.recordSolve capStep).recordSolve targetStep).trace.solves.length ≤
            terminal.trace.solves.length := by
        rw [solves', List.length_append]
        simp [InferState.recordSolve]
      have terminalSlice : solveSlice terminal.trace
          state.trace.solves.length terminal.trace.solves.length =
            [capStep, targetStep] ++ suffix := by
        simp only [solveSlice]
        rw [List.take_length, solves']
        simp [List.append_assoc]
      have applyDeltas_append
          (firstSteps tailSteps : List SolveStep) (target : Ty) :
          applyDeltas (firstSteps ++ tailSteps) target =
            applyDeltas tailSteps (applyDeltas firstSteps target) := by
        induction firstSteps generalizing target with
        | nil => rfl
        | cons step steps induction =>
            simp only [List.cons_append, applyDeltas]
            exact induction (step.delta.apply target)
      apply canonicalSlotEventCondition_equal startStop stopBound
      rw [terminalSlice]
      rw [applyDeltas_append, applyDeltas_append]
      rw [localEqual]

/-- Every successful expected-type alignment emits a canonical slot event.
The proof follows the executable selector: product matchers use the one-way
rule, slot tuples use the exact two-step equality above, and the raw branch
delegates to `alignAtSlot`. -/
theorem alignExprResultAtExpected_canonicalSlotEventCondition
    {path : SyntaxPath} {expressionResult : ExprResult} {expected : Ty}
    {final terminal : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some final)
    (history : final.HistoryPrefix terminal) :
    CanonicalSlotEventCondition terminal (.slotAlignment
      expressionResult.state.trace.solves.length final.trace.solves.length
      (match expectedCoercionPlan expressionResult.state
          expressionResult.target expected with
        | .productMatcherLift duals => productMatcherTarget duals
        | .slotTupleLift duals => slotTupleTarget duals
        | .raw => expressionResult.state.prevailing.apply
            expressionResult.target)
      (expressionResult.state.prevailing.apply expected)) := by
  unfold alignExprResultAtExpected at success
  cases planEq : expectedCoercionPlan expressionResult.state
      expressionResult.target expected with
  | productMatcherLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success ⊢
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedProductMatcherAtSlot
          expressionResult.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst final
          have canonical :=
            alignResolvedProductMatcherAtSlot_canonicalSlotEventCondition
              (aligned := aligned) alignmentEq history
          simpa [InferState.recordEvent] using canonical
  | slotTupleLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success ⊢
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedSlotTupleAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst final
          have canonical :=
            alignResolvedSlotTupleAtSlot_canonicalSlotEventCondition
              (aligned := aligned) alignmentEq history
          simpa [InferState.recordEvent] using canonical
  | raw =>
      cases alignmentEq : alignAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type")
          expressionResult.target expected with
      | none => simp [planEq, alignmentEq] at success
      | some aligned =>
          simp only [planEq, alignmentEq, Option.some.injEq] at success ⊢
          subst final
          have canonical := alignAtSlot_canonicalSlotEventCondition
            (aligned := aligned) alignmentEq history
          simpa [InferState.recordEvent] using canonical

end Reconstruction
end Inference
end TypePM
