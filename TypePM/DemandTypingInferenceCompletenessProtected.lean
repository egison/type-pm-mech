import TypePM.DemandTypingLedgerMetatheory

/-!
# Terminal protected-producer completeness boundary

The public raw inference filter asks whether the final prevailing capability
substitution maps every protected producer leaf to a non-structural variable.
This module separates that Boolean obligation into the two semantic facts a
traversal-completeness proof must retain: final-ledger admissibility of the
prevailing post and non-structural origin of every protected leaf.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessProtected

open Inference

/-- Every producer leaf retained by the executable state is frozen in the
current ledger (either rigid or rename-only). -/
def ProtectedCapOrigins (state : InferState) : Prop :=
  ∀ varId, varId ∈ state.protectedCaps →
    state.capabilityOrigins.originOf varId ≠ .structuralFlexible

/-- Protected variables have already been allocated below the current fresh
capability cut.  This is the exact freshness side invariant needed when a new
structurally flexible capability variable is allocated. -/
def ProtectedCapsBelowSupply (state : InferState) : Prop :=
  ∀ varId, varId ∈ state.protectedCaps →
    varId.id < state.supply.nextCap

/-- Overriding an appended batch with `renameOnly` preserves all earlier
protected origins and freezes every newly protected variable. -/
theorem protectedCapOrigins_setOrigins_renameOnly
    {ledger : CapabilityOriginLedger} {oldIds newIds : List CapVar}
    (oldFrozen : ∀ varId, varId ∈ oldIds →
      ledger.originOf varId ≠ .structuralFlexible) :
    ∀ varId, varId ∈ oldIds ++ newIds →
      (ledger.setOrigins newIds .renameOnly).originOf varId ≠
        .structuralFlexible := by
  intro varId membership
  rw [CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases newMembership : varId ∈ newIds
  · simp [newMembership]
  · rw [if_neg newMembership]
    rcases List.mem_append.mp membership with oldMembership | impossible
    · exact oldFrozen varId oldMembership
    · exact absurd impossible newMembership

/-- A structural allocation batch preserves protected origins exactly when it
is disjoint from the already protected variables. -/
theorem protectedCapOrigins_setOrigins_structural
    {ledger : CapabilityOriginLedger} {protectedIds freshIds : List CapVar}
    (oldFrozen : ∀ varId, varId ∈ protectedIds →
      ledger.originOf varId ≠ .structuralFlexible)
    (disjoint : ∀ varId, varId ∈ protectedIds → varId ∉ freshIds) :
    ∀ varId, varId ∈ protectedIds →
      (ledger.setOrigins freshIds .structuralFlexible).originOf varId ≠
        .structuralFlexible := by
  intro varId membership
  rw [CapabilityOriginLedger.originOf_setOrigins_eq,
    if_neg (disjoint varId membership)]
  exact oldFrozen varId membership

theorem initialState_protectedCapOrigins
    (signature : FrozenSig) (context : Context) :
    ProtectedCapOrigins (initialState signature context) := by
  simp [ProtectedCapOrigins, initialState, InferState.empty]

theorem initialState_protectedCapsBelowSupply
    (signature : FrozenSig) (context : Context) :
    ProtectedCapsBelowSupply (initialState signature context) := by
  simp [ProtectedCapsBelowSupply, initialState, InferState.empty]

theorem ProtectedCapOrigins.recordEvent
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (event : TraceEvent) : ProtectedCapOrigins (state.recordEvent event) := by
  simpa [ProtectedCapOrigins, InferState.recordEvent] using frozen

theorem ProtectedCapOrigins.recordSolve
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (step : SolveStep) : ProtectedCapOrigins (state.recordSolve step) := by
  simpa [ProtectedCapOrigins, InferState.recordSolve] using frozen

theorem ProtectedCapOrigins.recordSource
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (source : ProducerSource) :
    ProtectedCapOrigins (state.recordSource source) := by
  simpa [ProtectedCapOrigins, InferState.recordSource] using frozen

theorem ProtectedCapOrigins.freshTy
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (origin : ConstraintOrigin) :
    ProtectedCapOrigins (state.freshTy origin).2 := by
  simpa [InferState.freshTy, InferState.recordEvent, ProtectedCapOrigins] using
    frozen

/-- Fresh capability allocation needs only the fact that the allocated ID is
not already protected. -/
theorem ProtectedCapOrigins.freshCap_of_not_mem
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (origin : ConstraintOrigin)
    (fresh : ⟨state.supply.nextCap⟩ ∉ state.protectedCaps) :
    ProtectedCapOrigins (state.freshCap origin).2 := by
  intro varId membership
  have different : ⟨state.supply.nextCap⟩ ≠ varId := by
    intro equality
    subst varId
    exact fresh membership
  simpa [InferState.freshCap, InferState.recordEvent, ProtectedCapOrigins,
    CapabilityOriginLedger.originOf_setOrigin_of_ne _ _ _ different] using
      frozen varId membership

theorem ProtectedCapOrigins.freshCap
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (below : ProtectedCapsBelowSupply state)
    (origin : ConstraintOrigin) :
    ProtectedCapOrigins (state.freshCap origin).2 := by
  apply frozen.freshCap_of_not_mem origin
  intro membership
  exact Nat.lt_irrefl _ (below ⟨state.supply.nextCap⟩ membership)

theorem ProtectedCapOrigins.freezeCapabilityExport
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    ProtectedCapOrigins
      (state.freezeCapabilityExport capImages exportedPayload) := by
  simpa [ProtectedCapOrigins, InferState.freezeCapabilityExport,
    InferState.recordEvent] using
    (protectedCapOrigins_setOrigins_renameOnly frozen)

private theorem originOf_eq_structural_mem_keys
    {ledger : CapabilityOriginLedger} {varId : CapVar}
    (origin : ledger.originOf varId = .structuralFlexible) :
    varId ∈ ledger.map Prod.fst := by
  induction ledger with
  | nil => simp [CapabilityOriginLedger.originOf] at origin
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨candidate, candidateOrigin⟩
      by_cases same : candidate = varId
      · subst candidate
        simp
      · simp only [CapabilityOriginLedger.originOf, same, if_false] at origin
        simp [inductionHypothesis origin]

theorem ProtectedCapOrigins.protectMatcherCapability
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (capability : Cap) :
    ProtectedCapOrigins (state.protectMatcherCapability capability) := by
  intro varId membership
  rw [InferState.mem_protectMatcherCapability_protectedCaps] at membership
  simp only [InferState.protectMatcherCapability_capabilityOrigins,
    CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases selected : varId ∈
      matcherProducerLedgerLeaves state.capabilityOrigins capability
  · simp [selected]
  · rw [if_neg selected]
    rcases membership with oldMembership | ⟨capabilityMembership, _⟩
    · exact frozen varId oldMembership
    · intro structural
      apply selected
      simp [matcherProducerLedgerLeaves, capabilityMembership,
        originOf_eq_structural_mem_keys structural, structural]

/-- Borrowed matcher-demand variables are omitted from both the protected
list and the origin freeze, so the ordinary matcher-finalization argument
restricts to the remaining producer-owned variables. -/
theorem ProtectedCapOrigins.protectMatcherCapabilityExcept
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (capability : Cap) (borrowed : List CapVar) :
    ProtectedCapOrigins
      (state.protectMatcherCapabilityExcept capability borrowed) := by
  intro varId membership
  simp only [InferState.protectMatcherCapabilityExcept_protectedCaps,
    List.mem_append, matcherProducerVarsExcept, List.mem_filter,
    mem_matcherProducerVars] at membership
  simp only [InferState.protectMatcherCapabilityExcept_capabilityOrigins,
    CapabilityOriginLedger.originOf_setOrigins_eq]
  by_cases selected : varId ∈
      matcherProducerLedgerLeavesExcept state.capabilityOrigins capability
        borrowed
  · simp [selected]
  · rw [if_neg selected]
    rcases membership with oldMembership |
      ⟨⟨capabilityMembership, _⟩, notBorrowed⟩
    · exact frozen varId oldMembership
    · intro structural
      have notBorrowed' : varId ∉ borrowed := of_decide_eq_true notBorrowed
      apply selected
      simp [matcherProducerLedgerLeavesExcept, matcherProducerLedgerLeaves,
        capabilityMembership, originOf_eq_structural_mem_keys structural,
        structural, notBorrowed']

/-! ## Fresh-cut preservation -/

/-- Trace ownership is the convenient sufficient hypothesis for matcher
finalization: all variables selected by `matcherProducerVars` are trace-owned. -/
def AllocatedCapsBelowSupply (state : InferState) : Prop :=
  ∀ varId, varId ∈ state.trace.allocatedCapVars →
    varId.id < state.supply.nextCap

/-- Every trace-owned capability allocation has a corresponding executable
ledger entry.  Together with `DDLedger.LedgerBelow`, this discharges the
fresh-cut obligation without inspecting chronological events again. -/
def AllocatedCapsRecorded (state : InferState) : Prop :=
  ∀ varId, varId ∈ state.trace.allocatedCapVars →
    varId ∈ state.capabilityOrigins.map Prod.fst

private theorem mem_keys_setOrigins
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (origin : CapabilityOrigin) (varId : CapVar) :
    varId ∈ (ledger.setOrigins varIds origin).map Prod.fst ↔
      varId ∈ varIds ∨ varId ∈ ledger.map Prod.fst := by
  induction varIds generalizing ledger with
  | nil => simp [CapabilityOriginLedger.setOrigins]
  | cons head rest inductionHypothesis =>
      simp only [CapabilityOriginLedger.setOrigins,
        CapabilityOriginLedger.setOrigin, List.map_cons, List.mem_cons]
      rw [inductionHypothesis]
      simp [or_assoc]

theorem initialState_allocatedCapsRecorded
    (signature : FrozenSig) (context : Context) :
    AllocatedCapsRecorded (initialState signature context) := by
  simp [AllocatedCapsRecorded, initialState, InferState.empty,
    InferTrace.allocatedCapVars]

theorem AllocatedCapsRecorded.recordEvent
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (event : TraceEvent)
    (eventRecorded : ∀ varId, varId ∈ event.allocatedCapVars →
      varId ∈ state.capabilityOrigins.map Prod.fst) :
    AllocatedCapsRecorded (state.recordEvent event) := by
  intro varId membership
  simp only [InferState.recordEvent, InferTrace.allocatedCapVars,
    List.flatMap_append, List.flatMap_singleton, List.mem_append] at membership
  rcases membership with oldMembership | eventMembership
  · exact recorded varId oldMembership
  · exact eventRecorded varId eventMembership

theorem AllocatedCapsRecorded.recordSolve
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (step : SolveStep) : AllocatedCapsRecorded (state.recordSolve step) := by
  intro varId membership
  exact recorded varId membership

theorem AllocatedCapsRecorded.recordSource
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (source : ProducerSource) :
    AllocatedCapsRecorded (state.recordSource source) := by
  simpa [AllocatedCapsRecorded, InferState.recordSource] using recorded

theorem AllocatedCapsRecorded.freshTy
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (origin : ConstraintOrigin) :
    AllocatedCapsRecorded (state.freshTy origin).2 := by
  apply recorded.recordEvent
  simp [TraceEvent.allocatedCapVars]

theorem AllocatedCapsRecorded.freshCap
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (origin : ConstraintOrigin) :
    AllocatedCapsRecorded (state.freshCap origin).2 := by
  intro varId membership
  simp only [InferState.freshCap, InferState.recordEvent,
    InferTrace.allocatedCapVars, List.flatMap_append, List.flatMap_singleton,
    TraceEvent.allocatedCapVars, List.mem_append, List.mem_singleton]
    at membership
  rcases membership with oldMembership | same
  · change varId ∈
      ((⟨state.supply.nextCap⟩, .structuralFlexible) ::
        state.capabilityOrigins).map Prod.fst
    simp only [List.map_cons, List.mem_cons]
    exact Or.inr (recorded varId oldMembership)
  · subst varId
    change ⟨state.supply.nextCap⟩ ∈
      ((⟨state.supply.nextCap⟩, .structuralFlexible) ::
        state.capabilityOrigins).map Prod.fst
    simp

theorem AllocatedCapsRecorded.protectMatcherCapability
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (capability : Cap) :
    AllocatedCapsRecorded (state.protectMatcherCapability capability) := by
  intro varId membership
  change varId ∈
    (state.capabilityOrigins.setOrigins
      (matcherProducerLedgerLeaves state.capabilityOrigins capability)
      .renameOnly).map Prod.fst
  exact (mem_keys_setOrigins _ _ _ _).2
    (Or.inr (recorded varId membership))

theorem AllocatedCapsRecorded.protectMatcherCapabilityExcept
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (capability : Cap) (borrowed : List CapVar) :
    AllocatedCapsRecorded
      (state.protectMatcherCapabilityExcept capability borrowed) := by
  intro varId membership
  change varId ∈
    (state.capabilityOrigins.setOrigins
      (matcherProducerLedgerLeavesExcept state.capabilityOrigins capability
        borrowed) .renameOnly).map Prod.fst
  exact (mem_keys_setOrigins _ _ _ _).2
    (Or.inr (recorded varId membership))

theorem AllocatedCapsRecorded.freezeCapabilityExport
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (capImages : List CapVar) (exportedPayload : Ty) :
    AllocatedCapsRecorded
      (state.freezeCapabilityExport capImages exportedPayload) := by
  intro varId membership
  have oldMembership : varId ∈ state.trace.allocatedCapVars := by
    simpa [InferState.freezeCapabilityExport, InferState.recordEvent,
      InferTrace.allocatedCapVars, TraceEvent.allocatedCapVars] using membership
  change varId ∈
    (state.capabilityOrigins.setOrigins
      (capabilityExportLeaves state capImages exportedPayload)
      .renameOnly).map Prod.fst
  exact (mem_keys_setOrigins _ _ _ _).2
    (Or.inr (recorded varId oldMembership))

/-- Common preservation step for every quantified-binder batch: the state
update records exactly the IDs appended by the allocation event. -/
theorem AllocatedCapsRecorded.recordBatch
    {initial middle : InferState} (recorded : AllocatedCapsRecorded initial)
    (event : TraceEvent) (ids : List CapVar) (origin : CapabilityOrigin)
    (sameTrace : middle.trace = initial.trace)
    (ledgerUpdate : middle.capabilityOrigins =
      initial.capabilityOrigins.setOrigins ids origin)
    (eventIds : event.allocatedCapVars = ids) :
    AllocatedCapsRecorded (middle.recordEvent event) := by
  intro varId membership
  simp only [InferState.recordEvent, InferTrace.allocatedCapVars,
    List.flatMap_append, List.flatMap_singleton, List.mem_append] at membership
  change varId ∈ middle.capabilityOrigins.map Prod.fst
  rw [ledgerUpdate, mem_keys_setOrigins]
  rcases membership with oldMembership | newMembership
  · right
    apply recorded varId
    simpa only [InferTrace.allocatedCapVars, sameTrace] using oldMembership
  · left
    simpa only [eventIds] using newMembership

theorem AllocatedCapsRecorded.instantiateSchemeInState
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (scheme : Scheme) :
    AllocatedCapsRecorded
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  unfold Inference.instantiateSchemeInState
  apply recorded.recordBatch
  · rfl
  · rfl
  · rfl

theorem AllocatedCapsRecorded.instantiateCtorInState
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (scheme : CtorScheme) :
    AllocatedCapsRecorded (instantiateCtorInState state scheme).2 := by
  unfold Inference.instantiateCtorInState
  apply recorded.recordBatch
  · rfl
  · rfl
  · rfl

theorem AllocatedCapsRecorded.instantiateDualInState
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (scheme : DualScheme) :
    AllocatedCapsRecorded
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  unfold Inference.instantiateDualInState
  apply recorded.recordBatch
  · rfl
  · rfl
  · rfl

private theorem capabilityOrigin_eq_structural_of_beq
    (origin : CapabilityOrigin)
    (checked : (origin == .structuralFlexible) = true) :
    origin = .structuralFlexible := by
  cases origin with
  | rigid =>
      change false = true at checked
      contradiction
  | renameOnly =>
      change false = true at checked
      contradiction
  | structuralFlexible => rfl

theorem allocatedCapsBelowSupply_of_recorded
    {state : InferState} (recorded : AllocatedCapsRecorded state)
    (ledgerBelow : DDLedger.LedgerBelow state.supply
      state.capabilityOrigins) :
    AllocatedCapsBelowSupply state := by
  intro varId membership
  exact ledgerBelow varId (recorded varId membership)

/-- Export leaves are selected only when their origin is structural, hence
they must occur in the explicit ledger and are below any well-formed supply. -/
theorem capabilityExportLeaves_below
    {state : InferState}
    (ledgerBelow : DDLedger.LedgerBelow state.supply
      state.capabilityOrigins)
    (capImages : List CapVar) (exportedPayload : Ty) :
    ∀ varId,
      varId ∈ capabilityExportLeaves state capImages exportedPayload →
        varId.id < state.supply.nextCap := by
  intro varId membership
  have structural : state.capabilityOrigins.originOf varId =
      .structuralFlexible := by
    exact capabilityOrigin_eq_structural_of_beq _
      (List.mem_filter.mp membership).2
  exact ledgerBelow varId (originOf_eq_structural_mem_keys structural)

theorem ProtectedCapsBelowSupply.recordEvent_of_allocated
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (event : TraceEvent) :
    ProtectedCapsBelowSupply (state.recordEvent event) := by
  simpa [ProtectedCapsBelowSupply, InferState.recordEvent] using below

theorem ProtectedCapsBelowSupply.recordSolve
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (step : SolveStep) :
    ProtectedCapsBelowSupply (state.recordSolve step) := by
  simpa [ProtectedCapsBelowSupply, InferState.recordSolve] using below

theorem ProtectedCapsBelowSupply.recordSource
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (source : ProducerSource) :
    ProtectedCapsBelowSupply (state.recordSource source) := by
  simpa [ProtectedCapsBelowSupply, InferState.recordSource] using below

theorem ProtectedCapsBelowSupply.freshTy
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (origin : ConstraintOrigin) :
    ProtectedCapsBelowSupply (state.freshTy origin).2 := by
  simpa [ProtectedCapsBelowSupply, InferState.freshTy,
    InferState.recordEvent] using below

theorem ProtectedCapsBelowSupply.freshCap
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (origin : ConstraintOrigin) :
    ProtectedCapsBelowSupply (state.freshCap origin).2 := by
  intro varId membership
  exact Nat.lt_succ_of_lt (below varId membership)

theorem ProtectedCapsBelowSupply.protectMatcherCapability
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (allocatedBelow : AllocatedCapsBelowSupply state)
    (capability : Cap) :
    ProtectedCapsBelowSupply (state.protectMatcherCapability capability) := by
  intro varId membership
  rw [InferState.mem_protectMatcherCapability_protectedCaps] at membership
  rcases membership with oldMembership | ⟨_, allocatedMembership⟩
  · exact below varId oldMembership
  · exact allocatedBelow varId allocatedMembership

theorem ProtectedCapsBelowSupply.protectMatcherCapabilityExcept
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (allocatedBelow : AllocatedCapsBelowSupply state)
    (capability : Cap) (borrowed : List CapVar) :
    ProtectedCapsBelowSupply
      (state.protectMatcherCapabilityExcept capability borrowed) := by
  intro varId membership
  simp only [InferState.protectMatcherCapabilityExcept_protectedCaps,
    List.mem_append, matcherProducerVarsExcept, List.mem_filter,
    mem_matcherProducerVars] at membership
  rcases membership with oldMembership | ⟨⟨_, allocatedMembership⟩, _⟩
  · exact below varId oldMembership
  · exact allocatedBelow varId allocatedMembership

theorem ProtectedCapsBelowSupply.freezeCapabilityExport
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (capImages : List CapVar) (exportedPayload : Ty)
    (leavesBelow : ∀ varId,
      varId ∈ capabilityExportLeaves state capImages exportedPayload →
        varId.id < state.supply.nextCap) :
    ProtectedCapsBelowSupply
      (state.freezeCapabilityExport capImages exportedPayload) := by
  intro varId membership
  rw [InferState.freezeCapabilityExport_protectedCaps,
    List.mem_append] at membership
  rcases membership with oldMembership | leafMembership
  · exact below varId oldMembership
  · exact leavesBelow varId leafMembership

theorem ProtectedCapsBelowSupply.freezeCapabilityExport_of_ledgerBelow
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (ledgerBelow : DDLedger.LedgerBelow state.supply
      state.capabilityOrigins)
    (capImages : List CapVar) (exportedPayload : Ty) :
    ProtectedCapsBelowSupply
      (state.freezeCapabilityExport capImages exportedPayload) :=
  below.freezeCapabilityExport capImages exportedPayload
    (capabilityExportLeaves_below ledgerBelow capImages exportedPayload)

/-! ## Batched instantiation updates -/

private theorem freshCapImages_ge
    (supply : InferenceBase.FreshSupply) (binders : List CapVar)
    (varId : CapVar) (membership : varId ∈ freshCapImages supply binders) :
    supply.nextCap ≤ varId.id := by
  simp only [freshCapImages] at membership
  rcases List.mem_map.mp membership with ⟨binder, _, rfl⟩
  exact Nat.le_add_right supply.nextCap binder.id

private theorem freshCapImages_lt
    (supply : InferenceBase.FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) (varId : CapVar)
    (membership : varId ∈ freshCapImages supply capBinders) :
    varId.id <
      (InferenceBase.instantiateBinders supply capBinders tyBinders).supply.nextCap := by
  simp only [freshCapImages] at membership
  rcases List.mem_map.mp membership with ⟨binder, binderMembership, rfl⟩
  have binderBelow : binder.id <
      InferenceBase.binderSpan (capBinders.map CapVar.id) :=
    InferenceBase.mem_lt_binderSpan
      (List.mem_map.mpr ⟨binder, binderMembership, rfl⟩)
  exact Nat.add_lt_add_left binderBelow supply.nextCap

private theorem protectedCapsBelow_append
    {oldIds newIds : List CapVar} {oldCut newCut : Nat}
    (oldBelow : ∀ varId, varId ∈ oldIds → varId.id < oldCut)
    (cutMonotone : oldCut ≤ newCut)
    (newBelow : ∀ varId, varId ∈ newIds → varId.id < newCut) :
    ∀ varId, varId ∈ oldIds ++ newIds → varId.id < newCut := by
  intro varId membership
  rcases List.mem_append.mp membership with oldMembership | newMembership
  · exact Nat.lt_of_lt_of_le (oldBelow varId oldMembership) cutMonotone
  · exact newBelow varId newMembership

theorem ProtectedCapOrigins.instantiateSchemeInState
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (scheme : Scheme) :
    ProtectedCapOrigins
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  simpa [Inference.instantiateSchemeInState, ProtectedCapOrigins,
    InferState.recordEvent] using
      (protectedCapOrigins_setOrigins_renameOnly
        (newIds := Scheme.canonicalCapImages state.supply scheme) frozen)

theorem ProtectedCapOrigins.instantiateDualInState
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (scheme : DualScheme) :
    ProtectedCapOrigins
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  simpa [Inference.instantiateDualInState, ProtectedCapOrigins,
    InferState.recordEvent] using
      (protectedCapOrigins_setOrigins_renameOnly
        (newIds := freshCapImages state.supply scheme.capBinders) frozen)

theorem ProtectedCapOrigins.instantiateCtorInState
    {state : InferState} (frozen : ProtectedCapOrigins state)
    (below : ProtectedCapsBelowSupply state) (scheme : CtorScheme) :
    ProtectedCapOrigins (instantiateCtorInState state scheme).2 := by
  have disjoint : ∀ varId, varId ∈ state.protectedCaps →
      varId ∉ freshCapImages state.supply scheme.capBinders := by
    intro varId oldMembership newMembership
    exact Nat.not_le_of_lt (below varId oldMembership)
      (freshCapImages_ge state.supply scheme.capBinders varId newMembership)
  simpa [Inference.instantiateCtorInState, ProtectedCapOrigins,
    InferState.recordEvent] using
      (protectedCapOrigins_setOrigins_structural frozen disjoint)

theorem ProtectedCapsBelowSupply.instantiateSchemeInState
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (scheme : Scheme) :
    ProtectedCapsBelowSupply
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  have cutMonotone : state.supply.nextCap ≤
      (InferenceBase.instantiateScheme state.supply scheme).supply.nextCap := by
    simp
  have newBelow : ∀ varId,
      varId ∈ Scheme.canonicalCapImages state.supply scheme →
      varId.id <
        (InferenceBase.instantiateScheme state.supply scheme).supply.nextCap := by
    intro varId membership
    exact (Scheme.mem_canonicalCapImages_bounds membership).2
  simpa [Inference.instantiateSchemeInState, ProtectedCapsBelowSupply,
    InferState.recordEvent] using
      (protectedCapsBelow_append below cutMonotone newBelow)

theorem ProtectedCapsBelowSupply.instantiateDualInState
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (scheme : DualScheme) :
    ProtectedCapsBelowSupply
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  have cutMonotone : state.supply.nextCap ≤
      (InferenceBase.instantiateDualScheme state.supply scheme).supply.nextCap := by
    simp [InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders]
  have newBelow : ∀ varId,
      varId ∈ freshCapImages state.supply scheme.capBinders →
      varId.id <
        (InferenceBase.instantiateDualScheme state.supply scheme).supply.nextCap := by
    intro varId membership
    simpa [InferenceBase.instantiateDualScheme] using
      freshCapImages_lt state.supply scheme.capBinders scheme.tyBinders
        varId membership
  simpa [Inference.instantiateDualInState, ProtectedCapsBelowSupply,
    InferState.recordEvent] using
      (protectedCapsBelow_append below cutMonotone newBelow)

theorem ProtectedCapsBelowSupply.instantiateCtorInState
    {state : InferState} (below : ProtectedCapsBelowSupply state)
    (scheme : CtorScheme) :
    ProtectedCapsBelowSupply (instantiateCtorInState state scheme).2 := by
  intro varId membership
  have oldBelow := below varId membership
  apply Nat.lt_of_lt_of_le oldBelow
  change state.supply.nextCap ≤ state.supply.nextCap +
    InferenceBase.binderSpan (scheme.capBinders.map CapVar.id)
  exact Nat.le_add_right _ _

/-- Ledger admissibility sends every non-structural input variable to a
non-structural variable image. -/
theorem safeCapVars_of_admissible
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {varIds : List CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (frozen : ∀ varId, varId ∈ varIds →
      ledger.originOf varId ≠ .structuralFlexible) :
    SafeCapVars ledger post varIds := by
  intro varId membership
  have nonStructural := frozen varId membership
  cases origin : ledger.originOf varId with
  | rigid =>
      refine ⟨varId, admissible.rigid origin, ?_⟩
      simp [origin]
  | renameOnly =>
      exact admissible.renameOnly origin
  | structuralFlexible =>
      exact (nonStructural origin).elim

/-- The semantic facts sufficient for the terminal producer filter. -/
theorem protectedProducerTrace_of_admissible
    (state : InferState)
    (admissible : AdmissiblePost state.capabilityOrigins state.prevailing)
    (frozen : ProtectedCapOrigins state) :
    ProtectedProducerTrace state := by
  exact safeCapVars_of_admissible admissible.cap frozen

/-- Executable form consumed directly by `enforceProtectedResult`. -/
theorem protectedProducerTraceCheck_complete
    (state : InferState)
    (admissible : AdmissiblePost state.capabilityOrigins state.prevailing)
    (frozen : ProtectedCapOrigins state) :
    protectedProducerTraceCheck state = true := by
  exact (protectedProducerTraceCheck_eq_true state).2
    (protectedProducerTrace_of_admissible state admissible frozen)

end DemandTypingInferenceCompletenessProtected
end TypePM
