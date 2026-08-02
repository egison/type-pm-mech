import TypePM.P2.Relation

/-!
# P2 rigid annotation checking

Explicitly quantified capability and target variables are checked as rigid
skolems, not instantiated as flexible inference variables.  This module
isolates that boundary.  `ChecksRigid` is the low-level compatibility kernel;
`ChecksScheme` additionally enforces fresh numeric ranges for the two
already-distinct skolem sorts and separation between locally solvable and
environment-owned inference variables.
-/

namespace TypePM.P2
namespace Annotation

mutual

/-- Capability-skolem identifiers occurring in one capability. -/
def capSkolemIds : Cap → List Nat
  | .none        => []
  | .var _       => []
  | .skolem id   => [id]
  | .con _ caps  => capSkolemIdsList caps
  | .prod caps   => capSkolemIdsList caps

/-- List form of `capSkolemIds`. -/
def capSkolemIdsList : List Cap → List Nat
  | []          => []
  | cap :: caps => capSkolemIds cap ++ capSkolemIdsList caps

end

mutual

/-- Capability-skolem identifiers occurring anywhere in a P2 type. -/
def typeCapSkolemIds : Ty → List Nat
  | .var _         => []
  | .skolem _      => []
  | .int           => []
  | .bool          => []
  | .data _ tys    => typeCapSkolemIdsList tys
  | .prod tys      => typeCapSkolemIdsList tys
  | .fn dom cod    => typeCapSkolemIds dom ++ typeCapSkolemIds cod
  | .matcher cap τ => capSkolemIds cap ++ typeCapSkolemIds τ
  | .slot cap τ    => capSkolemIds cap ++ typeCapSkolemIds τ

/-- List form of `typeCapSkolemIds`. -/
def typeCapSkolemIdsList : List Ty → List Nat
  | []        => []
  | τ :: tys  => typeCapSkolemIds τ ++ typeCapSkolemIdsList tys

end

mutual

/-- Ordinary target-skolem identifiers occurring anywhere in a P2 type. -/
def targetSkolemIds : Ty → List Nat
  | .var _        => []
  | .skolem id    => [id]
  | .int          => []
  | .bool         => []
  | .data _ tys   => targetSkolemIdsList tys
  | .prod tys     => targetSkolemIdsList tys
  | .fn dom cod   => targetSkolemIds dom ++ targetSkolemIds cod
  | .matcher _ τ  => targetSkolemIds τ
  | .slot _ τ     => targetSkolemIds τ

/-- List form of `targetSkolemIds`. -/
def targetSkolemIdsList : List Ty → List Nat
  | []        => []
  | τ :: tys  => targetSkolemIds τ ++ targetSkolemIdsList tys

end

/--
Ambient ownership information needed by a sound annotation check.

The variable lists describe environment-owned flexible metas.  The skolem
lists describe rigid identifiers already live in the surrounding inference
problem.  A caller constructing this boundary must supply the complete live
sets; unlike the earlier implicit side condition, they are then consumed by
the formal `ChecksScheme` premises.
-/
structure CheckScope where
  environmentCaps : List CapVar
  environmentTargets : List TypePM.TyVar
  capabilitySkolems : List Nat
  targetSkolems : List Nat
deriving Repr

/-- The empty annotation-checking scope. -/
def CheckScope.empty : CheckScope :=
  ⟨[], [], [], []⟩

/-- Consecutive skolem identifiers allocated for one explicit binder list. -/
def generatedSkolemIds (base count : Nat) : List Nat :=
  (List.range count).map (base + ·)

/-- Extensional disjointness for the finite ownership lists used here. -/
def ListsDisjoint {α : Type} [DecidableEq α]
    (left right : List α) : Prop :=
  ∀ value, value ∈ left → value ∉ right

/-- Replace exactly the listed capability binders by rigid skolems. -/
def capSkolemSubst (binders : List CapVar) (base : Nat) : CapSubst :=
  fun candidate =>
    match List.idxOf? candidate binders with
    | some index => .skolem (base + index)
    | none => .var candidate

/-- Replace exactly the listed ordinary type binders by rigid skolems. -/
def targetSkolemSubst
    (binders : List TypePM.TyVar) (base : Nat) : TySubst :=
  fun candidate =>
    match List.idxOf? candidate binders with
    | some index => .skolem (base + index)
    | none => .var candidate

/--
Skolemize both binder sorts in an explicit scheme.

Freshness of `capBase` and `targetBase` with respect to the surrounding
inference problem is a side condition of the caller, exactly as in the usual
declarative presentation of skolemization.
-/
def skolemizeScheme
    (scheme : Scheme) (capBase targetBase : Nat) : Ty :=
  (Subst.mk
      (capSkolemSubst scheme.capBinders capBase)
      (targetSkolemSubst scheme.tyBinders targetBase)).apply scheme.body

/--
An inferred monotype can check a rigid body only by instantiating flexible
variables explicitly designated as local to this check.  Skolems in the
expected body remain rigid because neither substitution acts on skolem
constructors.

At this low level the caller must omit variables owned by the surrounding
environment from `localCaps` and `localTargets`.  The public high-level
`ChecksScheme` relation below records that locality and skolem freshness as
formal premises.
-/
def ChecksRigid
    (localCaps : List CapVar)
    (localTargets : List TypePM.TyVar)
    (inferred expectedRigid : Ty) : Prop :=
  ∃ C T,
    C.SupportWithin localCaps ∧
    T.SupportWithin localTargets ∧
    (Subst.mk C T).apply inferred = expectedRigid

/--
Freshness of the skolems generated for one explicit scheme.

Generated identifiers must be disjoint from both the surrounding rigid scope
and every rigid identifier already occurring in the inferred monotype.  This
rules out accidental acceptance caused by reusing an outer skolem ID.
-/
def FreshSkolemsFor
    (scope : CheckScope) (inferred : Ty)
    (scheme : Scheme) (capBase targetBase : Nat) : Prop :=
  ListsDisjoint
      (generatedSkolemIds capBase scheme.capBinders.length)
      (scope.capabilitySkolems ++ typeCapSkolemIds inferred ++
        typeCapSkolemIds scheme.body) ∧
    ListsDisjoint
      (generatedSkolemIds targetBase scheme.tyBinders.length)
      (scope.targetSkolems ++ targetSkolemIds inferred ++
        targetSkolemIds scheme.body)

/--
High-level explicit-scheme check with locality and freshness made formal.

Locally solvable metas must be disjoint from environment-owned metas, and the
new skolem ranges must be fresh for the ambient scope and inferred monotype.
`ChecksRigid` remains the lower-level compatibility kernel used after these
scope checks have been established.
-/
def ChecksScheme
    (scope : CheckScope)
    (localCaps : List CapVar)
    (localTargets : List TypePM.TyVar)
    (inferred : Ty) (scheme : Scheme)
    (capBase targetBase : Nat) : Prop :=
  ListsDisjoint localCaps scope.environmentCaps ∧
    ListsDisjoint localTargets scope.environmentTargets ∧
    FreshSkolemsFor scope inferred scheme capBase targetBase ∧
    ChecksRigid localCaps localTargets inferred
      (skolemizeScheme scheme capBase targetBase)

/-- A successful high-level check exposes its low-level rigid compatibility. -/
theorem ChecksScheme.rigid
    {scope : CheckScope}
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {inferred : Ty} {scheme : Scheme}
    {capBase targetBase : Nat}
    (h :
      ChecksScheme scope localCaps localTargets inferred scheme
        capBase targetBase) :
    ChecksRigid localCaps localTargets inferred
      (skolemizeScheme scheme capBase targetBase) :=
  h.2.2.2

/-- A successful high-level check exposes freshness of its generated skolems. -/
theorem ChecksScheme.fresh
    {scope : CheckScope}
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {inferred : Ty} {scheme : Scheme}
    {capBase targetBase : Nat}
    (h :
      ChecksScheme scope localCaps localTargets inferred scheme
        capBase targetBase) :
    FreshSkolemsFor scope inferred scheme capBase targetBase :=
  h.2.2.1

/-- A `none` producer cannot be strengthened to a rigid capability skolem. -/
theorem none_producer_rejects_capability_skolem
    (localCaps : List CapVar)
    (localTargets : List TypePM.TyVar)
    (inferredTarget expectedTarget : Ty) (skolemId : Nat) :
    ¬ ChecksRigid localCaps localTargets
      (.matcher .none inferredTarget)
      (.matcher (.skolem skolemId) expectedTarget) := by
  rintro ⟨C, T, _, _, equality⟩
  simp [Subst.apply, Ty.applyTarget, Ty.applyCapability, Cap.apply] at equality

/--
An environment-owned ordinary type variable is unchanged by a rigid check.

The hypothesis expresses ownership negatively: the variable is absent from
the caller-supplied set of locally solvable target metas.
-/
theorem ChecksRigid.environment_target_preserved
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {varId : TypePM.TyVar}
    {expectedRigid : Ty}
    (notLocal : varId ∉ localTargets)
    (checks :
      ChecksRigid localCaps localTargets (.var varId) expectedRigid) :
    expectedRigid = .var varId := by
  rcases checks with ⟨C, T, _, targetSupport, equality⟩
  have fixed : T varId = .var varId :=
    targetSupport varId notLocal
  simpa [Subst.apply, Ty.applyTarget, fixed, Ty.applyCapability] using
    equality.symm

/--
An environment-owned capability variable remains the root capability of a
matcher throughout a rigid check.
-/
theorem ChecksRigid.environment_capability_preserved
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {varId : CapVar}
    {inferredTarget expectedRigid : Ty}
    (notLocal : varId ∉ localCaps)
    (checks :
      ChecksRigid localCaps localTargets
        (.matcher (.var varId) inferredTarget) expectedRigid) :
    ∃ expectedTarget,
      expectedRigid = .matcher (.var varId) expectedTarget := by
  rcases checks with ⟨C, T, capabilitySupport, _, equality⟩
  have fixed : C varId = .var varId :=
    capabilitySupport varId notLocal
  refine
    ⟨(inferredTarget.applyTarget T).applyCapability C, ?_⟩
  simpa [Subst.apply, Ty.applyTarget, Ty.applyCapability, Cap.apply, fixed]
    using equality.symm

/--
Regression: an environment-owned ordinary meta cannot be unified with a fresh
annotation skolem.
-/
theorem environment_target_meta_rejects_skolem
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {varId : TypePM.TyVar}
    (notLocal : varId ∉ localTargets)
    (skolemId : Nat) :
    ¬ ChecksRigid localCaps localTargets
      (.var varId) (.skolem skolemId) := by
  intro checks
  have preserved :
      Ty.skolem skolemId = .var varId :=
    ChecksRigid.environment_target_preserved notLocal checks
  cases preserved

/--
Regression: an environment-owned capability meta cannot be unified with a
fresh capability skolem.
-/
theorem environment_capability_meta_rejects_skolem
    {localCaps : List CapVar}
    {localTargets : List TypePM.TyVar}
    {varId : CapVar}
    (notLocal : varId ∉ localCaps)
    (inferredTarget expectedTarget : Ty)
    (skolemId : Nat) :
    ¬ ChecksRigid localCaps localTargets
      (.matcher (.var varId) inferredTarget)
      (.matcher (.skolem skolemId) expectedTarget) := by
  intro checks
  obtain ⟨target, impossible⟩ :=
    ChecksRigid.environment_capability_preserved notLocal checks
  cases impossible

/-- The rejected annotation from P2: `forall p a. Matcher p a`. -/
def badCapabilityScheme : Scheme :=
  ⟨[0], [0], .matcher (.var 0) (.var 0)⟩

@[simp] theorem badCapabilityScheme_skolemize :
    skolemizeScheme badCapabilityScheme 0 0 =
      Ty.matcher (.skolem 0) (.skolem 0) := by
  rfl

/--
The principal `something` monotype cannot check the explicitly polymorphic
capability annotation, although its ordinary target variable may specialize.
-/
theorem something_rejects_badCapabilityScheme :
    ¬ ChecksRigid [] [1]
      (.matcher .none (.var 1))
      (skolemizeScheme badCapabilityScheme 0 0) := by
  rw [badCapabilityScheme_skolemize]
  exact
    none_producer_rejects_capability_skolem
      [] [1] (.var 1) (.skolem 0) 0

/--
High-level form of the rejected annotation, now also carrying explicit
environment-locality and skolem-freshness checks.
-/
theorem something_rejects_badCapabilityAnnotation :
    ¬ ChecksScheme CheckScope.empty [] [1]
      (.matcher .none (.var 1)) badCapabilityScheme 0 0 := by
  intro checks
  exact something_rejects_badCapabilityScheme checks.rigid

/-- A parametric producer identity type used for the positive regression. -/
def producerIdentityTy : Ty :=
  .fn
    (.matcher (.var 0) (.var 0))
    (.matcher (.var 0) (.var 0))

/-- Its explicit two-sort annotation. -/
def producerIdentityScheme : Scheme :=
  ⟨[0], [0],
    .fn
      (.matcher (.var 0) (.var 0))
      (.matcher (.var 0) (.var 0))⟩

/--
Genuine parametric sharing checks: the same flexible capability and target
variables are instantiated to the corresponding rigid skolems everywhere.
-/
theorem producerIdentity_checks_rigid_annotation :
    ChecksRigid [0] [0] producerIdentityTy
      (skolemizeScheme producerIdentityScheme 0 0) := by
  let C : CapSubst :=
    fun candidate => if candidate = 0 then .skolem 0 else .var candidate
  let T : TySubst :=
    fun candidate => if candidate = 0 then .skolem 0 else .var candidate
  refine ⟨C, T, ?_, ?_, ?_⟩
  · intro candidate hfree
    have hne : candidate ≠ 0 := by
      simpa using hfree
    simp [C, hne]
  · intro candidate hfree
    have hne : candidate ≠ 0 := by
      simpa using hfree
    simp [T, hne]
  · simp [producerIdentityTy, producerIdentityScheme, skolemizeScheme,
      capSkolemSubst, targetSkolemSubst, Subst.apply, C, T,
      Ty.applyTarget, Ty.applyCapability, Cap.apply]

/--
The positive parametric identity also passes the high-level scope and
freshness boundary in an empty ambient context.
-/
theorem producerIdentity_checks_annotation :
    ChecksScheme CheckScope.empty [0] [0]
      producerIdentityTy producerIdentityScheme 0 0 := by
  refine ⟨?_, ?_, ?_, producerIdentity_checks_rigid_annotation⟩
  · simp [CheckScope.empty, ListsDisjoint]
  · simp [CheckScope.empty, ListsDisjoint]
  · simp [FreshSkolemsFor, CheckScope.empty, generatedSkolemIds,
      ListsDisjoint, producerIdentityTy, producerIdentityScheme,
      typeCapSkolemIds, capSkolemIds, targetSkolemIds]

/-! ## Freshness-collision regression -/

/-- An explicit capability-polymorphic annotation used to expose ID collision. -/
def collidingCapabilityScheme : Scheme :=
  ⟨[0], [], .matcher (.var 0) .int⟩

@[simp] theorem collidingCapabilityScheme_skolemize :
    skolemizeScheme collidingCapabilityScheme 0 0 =
      .matcher (.skolem 0) .int := by
  rfl

/--
The low-level compatibility kernel alone cannot distinguish a pre-existing
outer skolem from a newly generated skolem with the same numeric ID.
-/
theorem colliding_skolem_passes_lowLevel_kernel :
    ChecksRigid [] []
      (.matcher (.skolem 0) .int)
      (skolemizeScheme collidingCapabilityScheme 0 0) := by
  refine ⟨CapSubst.id, TySubst.id,
    CapSubst.id_supportWithin [],
    TySubst.id_supportWithin [], ?_⟩
  simp [collidingCapabilityScheme_skolemize, Subst.apply,
    Ty.applyTarget, Ty.applyCapability, Cap.apply]

/--
The high-level annotation API rejects that collision because the generated
capability skolem is required to be fresh for the inferred monotype.
-/
theorem colliding_skolem_rejected_by_freshness :
    ¬ ChecksScheme CheckScope.empty [] []
      (.matcher (.skolem 0) .int)
      collidingCapabilityScheme 0 0 := by
  intro checks
  have fresh := checks.fresh
  exact fresh.1 0 (by simp [generatedSkolemIds, collidingCapabilityScheme])
    (by simp [CheckScope.empty, typeCapSkolemIds, capSkolemIds])

end Annotation
end TypePM.P2
