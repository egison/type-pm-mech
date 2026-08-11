import TypePM.Relation
import TypePM.PolyScheme

/-!
# Rigid annotation checking

Explicitly quantified capability and target variables are checked as rigid
skolems, not instantiated as flexible inference variables.  This module
isolates that boundary.  `ChecksRigid` is the low-level compatibility kernel;
`ChecksScheme` additionally enforces fresh numeric ranges for the two
already-distinct skolem sorts and separation between locally solvable and
environment-owned inference variables.
-/

namespace TypePM
namespace Annotation

mutual

/-- Capability-skolem identifiers occurring in one capability. -/
def capSkolemIds : Cap → List Nat
  | .any         => []
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

/-- Capability-skolem identifiers occurring in a polymorphic capability. -/
def polyCapSkolemIds {capArity : Nat} : PolyCap capArity → List Nat
  | .any          => []
  | .mvar _       => []
  | .bound _      => []
  | .skolem id    => [id]
  | .con _ caps   => polyCapSkolemIdsList caps
  | .prod caps    => polyCapSkolemIdsList caps

/-- List form of `polyCapSkolemIds`. -/
def polyCapSkolemIdsList {capArity : Nat} :
    List (PolyCap capArity) → List Nat
  | []          => []
  | cap :: caps => polyCapSkolemIds cap ++ polyCapSkolemIdsList caps

end

mutual

/-- Capability-skolem identifiers occurring in a polymorphic type. -/
def polyTypeCapSkolemIds {capArity tyArity : Nat} :
    PolyTy capArity tyArity → List Nat
  | .mvar _         => []
  | .bound _        => []
  | .skolem _       => []
  | .unit            => []
  | .int             => []
  | .bool            => []
  | .data _ tys      => polyTypeCapSkolemIdsList tys
  | .prod tys        => polyTypeCapSkolemIdsList tys
  | .fn dom cod      => polyTypeCapSkolemIds dom ++ polyTypeCapSkolemIds cod
  | .matcher cap τ   => polyCapSkolemIds cap ++ polyTypeCapSkolemIds τ
  | .slot cap τ      => polyCapSkolemIds cap ++ polyTypeCapSkolemIds τ

/-- List form of `polyTypeCapSkolemIds`. -/
def polyTypeCapSkolemIdsList {capArity tyArity : Nat} :
    List (PolyTy capArity tyArity) → List Nat
  | []        => []
  | τ :: tys  => polyTypeCapSkolemIds τ ++ polyTypeCapSkolemIdsList tys

end


mutual

/-- Target-skolem identifiers occurring in a polymorphic type. -/
def polyTargetSkolemIds {capArity tyArity : Nat} :
    PolyTy capArity tyArity → List Nat
  | .mvar _        => []
  | .bound _       => []
  | .skolem id     => [id]
  | .unit           => []
  | .int            => []
  | .bool           => []
  | .data _ tys     => polyTargetSkolemIdsList tys
  | .prod tys       => polyTargetSkolemIdsList tys
  | .fn dom cod     => polyTargetSkolemIds dom ++ polyTargetSkolemIds cod
  | .matcher _ τ    => polyTargetSkolemIds τ
  | .slot _ τ       => polyTargetSkolemIds τ

/-- List form of `polyTargetSkolemIds`. -/
def polyTargetSkolemIdsList {capArity tyArity : Nat} :
    List (PolyTy capArity tyArity) → List Nat
  | []        => []
  | τ :: tys  => polyTargetSkolemIds τ ++ polyTargetSkolemIdsList tys

end

mutual

/-- Capability-skolem identifiers occurring anywhere in a two-sorted type. -/
def typeCapSkolemIds : Ty → List Nat
  | .var _         => []
  | .skolem _      => []
  | .unit          => []
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

/-- Ordinary target-skolem identifiers occurring anywhere in a two-sorted type. -/
def targetSkolemIds : Ty → List Nat
  | .var _        => []
  | .skolem id    => [id]
  | .unit         => []
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

/--
Skolemize both binder sorts in an explicit scheme.

Freshness of `capBase` and `targetBase` with respect to the surrounding
inference problem is a side condition of the caller, exactly as in the usual
declarative presentation of skolemization.
-/
def skolemizeScheme
    (scheme : Scheme) (capBase targetBase : Nat) : Ty :=
  scheme.instantiate
    (fun index => .skolem (capBase + index.val))
    (fun index => .skolem (targetBase + index.val))

/--
An inferred monotype can check a rigid body only by instantiating flexible
variables explicitly designated as local to this check.  Skolems in the
expected body remain rigid because neither substitution acts on skolem
constructors.

At this low level the caller must omit variables owned by the surrounding
environment from `localCaps` and `localTargets`.  The public high-level
`ChecksScheme` relation below records that locality and skolem freshness as
formal premises.  The solving pair is range-fixed, so its action is the
paper's `T (C τ)` action without a latent capability rewrite in the target
range.
-/
def ChecksRigid
    (localCaps : List CapVar)
    (localTargets : List TypePM.TyVar)
    (inferred expectedRigid : Ty) : Prop :=
  ∃ C T,
    C.SupportWithin localCaps ∧
    T.SupportWithin localTargets ∧
    (Subst.mk C T).RangeFixed ∧
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
      (generatedSkolemIds capBase scheme.capArity)
      (scope.capabilitySkolems ++ typeCapSkolemIds inferred ++
        polyTypeCapSkolemIds scheme.body) ∧
    ListsDisjoint
      (generatedSkolemIds targetBase scheme.tyArity)
      (scope.targetSkolems ++ targetSkolemIds inferred ++
        polyTargetSkolemIds scheme.body)

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

/-- An `Any` producer cannot be strengthened to a rigid capability skolem. -/
theorem none_producer_rejects_capability_skolem
    (localCaps : List CapVar)
    (localTargets : List TypePM.TyVar)
    (inferredTarget expectedTarget : Ty) (skolemId : Nat) :
    ¬ ChecksRigid localCaps localTargets
      (.matcher .any inferredTarget)
      (.matcher (.skolem skolemId) expectedTarget) := by
  rintro ⟨C, T, _, _, _, equality⟩
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
  rcases checks with ⟨C, T, _, targetSupport, _, equality⟩
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
  rcases checks with ⟨C, T, capabilitySupport, _, _, equality⟩
  have fixed : C varId = .var varId :=
    capabilitySupport varId notLocal
  refine
    ⟨(inferredTarget.applyCapability C).applyTarget T, ?_⟩
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

/-- The annotation rejected by the two-sorted core: `forall p a. Matcher p a`. -/
def badCapabilityScheme : Scheme :=
  { capArity := 1
    tyArity := 1
    body := .matcher (.bound 0) (.bound 0) }

@[simp] theorem badCapabilityScheme_skolemize :
    skolemizeScheme badCapabilityScheme 0 0 =
      Ty.matcher (.skolem 0) (.skolem 0) := by
  simp [skolemizeScheme, badCapabilityScheme, Scheme.instantiate,
    PolyTy.instantiate, PolyCap.instantiate]

/--
The principal `something` monotype cannot check the explicitly polymorphic
capability annotation, although its ordinary target variable may specialize.
-/
theorem something_rejects_badCapabilityScheme :
    ¬ ChecksRigid [] [1]
      (.matcher .any (.var 1))
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
      (.matcher .any (.var 1)) badCapabilityScheme 0 0 := by
  intro checks
  exact something_rejects_badCapabilityScheme checks.rigid

/-- A parametric producer identity type used for the positive regression. -/
def producerIdentityTy : Ty :=
  .fn
    (.matcher (.var 0) (.var 0))
    (.matcher (.var 0) (.var 0))

/-- Its explicit two-sort annotation. -/
def producerIdentityScheme : Scheme :=
  { capArity := 1
    tyArity := 1
    body :=
      .fn
        (.matcher (.bound 0) (.bound 0))
        (.matcher (.bound 0) (.bound 0)) }

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
  refine ⟨C, T, ?_, ?_, ?_, ?_⟩
  · intro candidate hfree
    have hne : candidate ≠ 0 := by
      simpa using hfree
    simp [C, hne]
  · intro candidate hfree
    have hne : candidate ≠ 0 := by
      simpa using hfree
    simp [T, hne]
  · intro candidate
    by_cases heq : candidate = 0 <;>
      simp [C, T, heq, Ty.applyCapability]
  · simp [producerIdentityTy, producerIdentityScheme, skolemizeScheme,
      Scheme.instantiate, PolyTy.instantiate, PolyCap.instantiate,
      Subst.apply, C, T, Ty.applyTarget, Ty.applyCapability, Cap.apply]

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
      typeCapSkolemIds, capSkolemIds, targetSkolemIds,
      polyTypeCapSkolemIds, polyCapSkolemIds, polyTargetSkolemIds]

/-! ## Freshness-collision regression -/

/-- An explicit capability-polymorphic annotation used to expose ID collision. -/
def collidingCapabilityScheme : Scheme :=
  { capArity := 1
    tyArity := 0
    body := .matcher (.bound 0) .int }

@[simp] theorem collidingCapabilityScheme_skolemize :
    skolemizeScheme collidingCapabilityScheme 0 0 =
      .matcher (.skolem 0) .int := by
  simp [skolemizeScheme, collidingCapabilityScheme, Scheme.instantiate,
    PolyTy.instantiate, PolyCap.instantiate]

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
    TySubst.id_supportWithin [], Subst.id_rangeFixed, ?_⟩
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

/-! ## Bound-index capture regression -/

/-- A bound capability and an ambient metavariable may share the same numeric
payload because they inhabit different constructors in canonical syntax. -/
def boundAndFreeCapabilityScheme : Scheme :=
  { capArity := 1
    tyArity := 0
    body := .prod
      [.matcher (.bound 0) .int, .matcher (.mvar 0) .int] }

/-- Skolemization opens only the finite bound index.  The ambient
metavariable with numeric identifier zero remains flexible, so binder-name
capture is structurally impossible. -/
@[simp] theorem bound_index_skolemization_cannot_capture_free_meta :
    skolemizeScheme boundAndFreeCapabilityScheme 7 0 =
      .prod [.matcher (.skolem 7) .int, .matcher (.var 0) .int] := by
  simp [skolemizeScheme, boundAndFreeCapabilityScheme, Scheme.instantiate,
    PolyTy.instantiate, PolyCap.instantiate]

end Annotation
end TypePM
