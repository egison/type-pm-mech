import TypePM.DamasMilnerWLetGenerative

/-!
# Structural transport of generative old-free provenance

`ProtectedOldFreeAt` records old-free provenance pointwise on a continuation
frontier.  The accompanying image condition is the precise solver-side fact
needed to transport provenance through an ordinary substitution: every old
variable occurring in an image of a source visible in the target is already
owned by the final active environment.
-/

namespace TypePM
namespace DM

def ProtectedOldFreeAt (entrySupply : InferenceBase.FreshSupply)
    (active : Context) (frontier : List (Ty × STy)) : Prop :=
  ∀ pair ∈ frontier, OldFreeInContextAt entrySupply active pair.1

/-- Below the fixed provenance floor, every variable exposed by the current
active context is already owned by the independent provenance context.  This
is the context analogue needed by variable lookup under lambda-local heads. -/
structure OldContextCoveredAt (entrySupply : InferenceBase.FreshSupply)
    (owner active : Context) : Prop where
  caps : ∀ varId, varId ∈ active.fcv →
    varId.id < entrySupply.nextCap → varId ∈ owner.fcv
  targets : ∀ varId, varId ∈ active.ftv →
    varId < entrySupply.nextTy → varId ∈ owner.ftv

/-- Every variable owned by the fixed provenance environment remains visible
in the current active environment.  This is the forward inclusion needed at
let generalization: variables classified as owner-owned cannot be selected as
new binders by generalization over the active environment. -/
structure ProvenanceContextIncluded (owner active : Context) : Prop where
  caps : ∀ varId, varId ∈ owner.fcv → varId ∈ active.fcv
  targets : ∀ varId, varId ∈ owner.ftv → varId ∈ active.ftv

/-- Raw chronological relation between the fixed provenance owner and the
current active context.  Unlike a free-variable inclusion certificate, this
survives arbitrary future scheme substitution by construction. -/
def ProvenanceContextSuffix (owner active : Context) : Prop :=
  owner <:+ active

theorem ProvenanceContextSuffix.refl (context : Context) :
    ProvenanceContextSuffix context context :=
  ⟨[], rfl⟩

theorem ProvenanceContextSuffix.consActive
    {owner active : Context} (suffix : ProvenanceContextSuffix owner active)
    (name : String) (scheme : Scheme) :
    ProvenanceContextSuffix owner ((name, scheme) :: active) := by
  rcases suffix with ⟨pre, equality⟩
  exact ⟨(name, scheme) :: pre, by simp [equality]⟩

theorem ProvenanceContextSuffix.toIncluded
    {owner active : Context} (suffix : ProvenanceContextSuffix owner active)
    (current : Subst) :
    ProvenanceContextIncluded (owner.applySubst current)
      (active.applySubst current) := by
  rcases suffix with ⟨pre, equality⟩
  constructor
  · intro varId free
    rw [← equality, Context.applySubst, List.map_append,
      Context.fcv, List.flatMap_append, List.mem_append]
    exact Or.inr free
  · intro varId free
    rw [← equality, Context.applySubst, List.map_append,
      Context.ftv, List.flatMap_append, List.mem_append]
    exact Or.inr free

theorem ProvenanceContextIncluded.refl (context : Context) :
    ProvenanceContextIncluded context context :=
  ⟨fun _ member => member, fun _ member => member⟩

theorem ProvenanceContextIncluded.trans
    {first second third : Context}
    (left : ProvenanceContextIncluded first second)
    (right : ProvenanceContextIncluded second third) :
    ProvenanceContextIncluded first third :=
  ⟨fun varId member => right.caps varId (left.caps varId member),
    fun varId member => right.targets varId (left.targets varId member)⟩

/-- Raw chronological ownership for protected contexts.  Keeping this as a
list-suffix fact avoids all scheme-binder questions during later solver cuts:
the same substitution is applied to both the protected context and owner. -/
def ProtectedContextsSuffix (owner : Context)
    (frames : List (Context × SCtx)) : Prop :=
  ∀ pair ∈ frames, pair.1 <:+ owner

/-- Residual scope for every protected raw/selected context frame.  This is
the scope counterpart of `WContextFrames`: recursive shadowing may hide the
outer selected context, so its scope must be transported pointwise rather
than recovered by dropping a head. -/
def ProtectedResidualScopes (residual : SSubst) (prevailing : Subst)
    (frames : List (Context × SCtx)) : Prop :=
  ∀ pair ∈ frames,
    ResidualContextScope residual (pair.1.applySubst prevailing) pair.2

theorem ProtectedResidualScopes.singleton
    {residual : SSubst} {prevailing : Subst}
    {rawContext : Context} {selectedContext : SCtx}
    (scope : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext) :
    ProtectedResidualScopes residual prevailing
      [(rawContext, selectedContext)] := by
  intro pair member
  have equality : pair = (rawContext, selectedContext) :=
    List.mem_singleton.mp member
  subst pair
  intro algorithmVar selectedVar algorithmFree imageFree
  exact scope algorithmFree imageFree

theorem ProtectedResidualScopes.cons
    {residual : SSubst} {prevailing : Subst}
    {rawContext : Context} {selectedContext : SCtx}
    {frames : List (Context × SCtx)}
    (head : ResidualContextScope residual
      (rawContext.applySubst prevailing) selectedContext)
    (tail : ProtectedResidualScopes residual prevailing frames) :
    ProtectedResidualScopes residual prevailing
      ((rawContext, selectedContext) :: frames) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | old
  · exact head
  · exact tail pair old

theorem ProtectedResidualScopes.of_frames_subset
    {residual : SSubst} {prevailing : Subst}
    {larger smaller : List (Context × SCtx)}
    (scopes : ProtectedResidualScopes residual prevailing larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ProtectedResidualScopes residual prevailing smaller := by
  intro pair member
  exact scopes pair (subset pair member)

theorem ProtectedResidualScopes.applyAbsorbed
    {residual : SSubst} {prevailing delta : Subst}
    {frames : List (Context × SCtx)}
    (scopes : ProtectedResidualScopes residual prevailing frames)
    (factor : SSubst.paired residual =
      Subst.seq (SSubst.paired residual) delta) :
    ProtectedResidualScopes residual (Subst.seq delta prevailing) frames := by
  intro pair member
  rw [Context.applySubst_seq]
  exact ResidualContextScope.applyAbsorbed (scopes pair member) factor

theorem ProtectedContextsSuffix.singleton (owner : Context)
    (selected : SCtx) : ProtectedContextsSuffix owner [(owner, selected)] := by
  intro pair member
  have equality : pair = (owner, selected) := List.mem_singleton.mp member
  subst pair
  exact ⟨[], rfl⟩

theorem ProtectedContextsSuffix.of_frames_subset
    {owner : Context} {larger smaller : List (Context × SCtx)}
    (suffixes : ProtectedContextsSuffix owner larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ProtectedContextsSuffix owner smaller := by
  intro pair member
  exact suffixes pair (subset pair member)

/-- Extending the active owner at the head and protecting that new active
context preserves suffix chronology for every older protected frame. -/
theorem ProtectedContextsSuffix.consActive
    {owner : Context} {frames : List (Context × SCtx)}
    (suffixes : ProtectedContextsSuffix owner frames)
    (name : String) (scheme : Scheme) (selected : SCtx) :
    ProtectedContextsSuffix ((name, scheme) :: owner)
      ((((name, scheme) :: owner), selected) :: frames) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨[], rfl⟩
  · rcases suffixes pair old with ⟨pre, equality⟩
    exact ⟨(name, scheme) :: pre, by simp [equality]⟩

/-- Raw suffix chronology regenerates protected free-variable coverage after
any substitution, including substitutions that act below scheme binders. -/
theorem ProtectedContextsSuffix.toProtectedFreeCovered
    {owner : Context} {frames : List (Context × SCtx)}
    (suffixes : ProtectedContextsSuffix owner frames) (current : Subst) :
    ProtectedFreeCovered (owner.applySubst current) frames current := by
  constructor
  · intro pair member varId free
    rcases suffixes pair member with ⟨pre, equality⟩
    rw [← equality, Context.applySubst, List.map_append,
      Context.fcv, List.flatMap_append, List.mem_append]
    exact Or.inr free
  · intro pair member varId free
    rcases suffixes pair member with ⟨pre, equality⟩
    rw [← equality, Context.applySubst, List.map_append,
      Context.ftv, List.flatMap_append, List.mem_append]
    exact Or.inr free

/-- Adding a local binder to the active environment preserves ownership of
the fixed outer provenance context. -/
theorem ProvenanceContextIncluded.consActive
    {owner active : Context} (included : ProvenanceContextIncluded owner active)
    (name : String) (scheme : Scheme) :
    ProvenanceContextIncluded owner ((name, scheme) :: active) := by
  constructor
  · intro varId member
    rw [Context.fcv, List.flatMap_cons, List.mem_append]
    exact Or.inr (included.caps varId member)
  · intro varId member
    rw [Context.ftv, List.flatMap_cons, List.mem_append]
    exact Or.inr (included.targets varId member)

/-- Extending owner and active by the same raw binding preserves both
directions of provenance comparison. -/
theorem ProvenanceContextIncluded.consBoth
    {owner active : Context} (included : ProvenanceContextIncluded owner active)
    (name : String) (scheme : Scheme) :
    ProvenanceContextIncluded ((name, scheme) :: owner)
      ((name, scheme) :: active) := by
  constructor
  · intro varId member
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at member ⊢
    exact member.elim Or.inl (fun outer => Or.inr (included.caps varId outer))
  · intro varId member
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at member ⊢
    exact member.elim Or.inl
      (fun outer => Or.inr (included.targets varId outer))

/-- Fixed-owner provenance suffices for let freshness when the owner remains
included in the actual environment used by generalization. -/
theorem RetainedOldOrContextAt.avoidsGeneralized_of_included
    {signature : FrozenSig} {entrySupply : InferenceBase.FreshSupply}
    {owner active : Context} {target : Ty} {suffix current : Subst}
    {rawContext : Context} {rawTarget : Ty}
    {frontier : List (Ty × STy)}
    (covered : RetainedOldOrContextAt entrySupply owner suffix frontier)
    (old : OldFreeInContextAt entrySupply owner target)
    (included : ProvenanceContextIncluded owner active)
    (activeEq : rawContext.applySubst current = active)
    (targetEq : current.apply rawTarget = target) :
    ∀ pair ∈ frontier,
      (PendingLetCut.mk rawContext rawTarget current).AvoidsTy signature current
        (suffix.apply pair.1) := by
  intro pair member
  constructor
  · intro varId generalized free
    rw [activeEq, targetEq] at generalized
    rcases covered.caps pair member varId free with below | inOwner
    · have targetFree : varId ∈ target.fcv := by
        unfold FrozenSig.generalizedCapVars at generalized
        exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1
      have ownerFree := old.caps varId targetFree below
      exact mem_generalizedCapVars_not_env generalized
        (List.mem_append_right _ (included.caps varId ownerFree))
    · exact mem_generalizedCapVars_not_env generalized
        (List.mem_append_right _ (included.caps varId inOwner))
  · intro varId generalized free
    rw [activeEq, targetEq] at generalized
    rcases covered.targets pair member varId free with below | inOwner
    · have targetFree : varId ∈ target.ftv := by
        unfold FrozenSig.generalizedTyVars at generalized
        exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1
      have ownerFree := old.targets varId targetFree below
      exact mem_generalizedTyVars_not_env generalized
        (List.mem_append_right _ (included.targets varId ownerFree))
    · exact mem_generalizedTyVars_not_env generalized
        (List.mem_append_right _ (included.targets varId inOwner))

theorem OldContextCoveredAt.refl
    (supply : InferenceBase.FreshSupply) (context : Context) :
    OldContextCoveredAt supply context context := by
  exact ⟨fun _ member _ => member, fun _ member _ => member⟩

theorem OldContextCoveredAt.of_supply_le
    {smaller larger : InferenceBase.FreshSupply} {owner active : Context}
    (covered : OldContextCoveredAt larger owner active)
    (caps : smaller.nextCap ≤ larger.nextCap)
    (targets : smaller.nextTy ≤ larger.nextTy) :
    OldContextCoveredAt smaller owner active := by
  constructor
  · intro varId free below
    exact covered.caps varId free (Nat.lt_of_lt_of_le below caps)
  · intro varId free below
    exact covered.targets varId free (Nat.lt_of_lt_of_le below targets)

theorem OldContextCoveredAt.consFreshTarget
    {supply : InferenceBase.FreshSupply} {owner active : Context}
    {name : String}
    (covered : OldContextCoveredAt supply owner active) :
    OldContextCoveredAt supply owner
      ((name, Scheme.mono (.var supply.nextTy)) :: active) := by
  constructor
  · intro varId free below
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at free
    rcases free with head | outer
    · simp [Scheme.mono, Scheme.fcv, PolyTy.lift, PolyTy.fcv] at head
    · exact covered.caps varId outer below
  · intro varId free below
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at free
    rcases free with head | outer
    · have equal : varId = supply.nextTy := by
        simpa [Scheme.mono, Scheme.ftv, PolyTy.lift, PolyTy.ftv] using head
      subst varId
      exact False.elim (Nat.lt_irrefl _ below)
    · exact covered.targets varId outer below

/-- Adding a target variable allocated no earlier than the ownership floor
does not create a new old variable in the active context. -/
theorem OldContextCoveredAt.consFreshTargetAbove
    {floor : InferenceBase.FreshSupply} {owner active : Context}
    {name : String} {fresh : TyVar}
    (covered : OldContextCoveredAt floor owner active)
    (above : floor.nextTy ≤ fresh) :
    OldContextCoveredAt floor owner
      ((name, Scheme.mono (.var fresh)) :: active) := by
  constructor
  · intro varId free below
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at free
    rcases free with head | outer
    · simp [Scheme.mono, Scheme.fcv, PolyTy.lift, PolyTy.fcv] at head
    · exact covered.caps varId outer below
  · intro varId free below
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at free
    rcases free with head | outer
    · have equal : varId = fresh := by
        simpa [Scheme.mono, Scheme.ftv, PolyTy.lift, PolyTy.ftv] using head
      subst varId
      exact False.elim (Nat.not_lt_of_ge above below)
    · exact covered.targets varId outer below

theorem OldContextCoveredAt.consBoth
    {supply : InferenceBase.FreshSupply} {owner active : Context}
    (covered : OldContextCoveredAt supply owner active)
    (name : String) (scheme : Scheme) :
    OldContextCoveredAt supply ((name, scheme) :: owner)
      ((name, scheme) :: active) := by
  constructor
  · intro varId member below
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at member ⊢
    exact member.elim Or.inl
      (fun outer => Or.inr (covered.caps varId outer below))
  · intro varId member below
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at member ⊢
    exact member.elim Or.inl
      (fun outer => Or.inr (covered.targets varId outer below))

/-- Forgetting a local active binding preserves coverage of the remaining
outer active context. -/
theorem OldContextCoveredAt.dropActiveHead
    {supply : InferenceBase.FreshSupply} {owner active : Context}
    {name : String} {scheme : Scheme}
    (covered : OldContextCoveredAt supply owner ((name, scheme) :: active)) :
    OldContextCoveredAt supply owner active := by
  constructor
  · intro varId free below
    apply covered.caps varId
    · rw [Context.fcv, List.flatMap_cons, List.mem_append]
      exact Or.inr free
    · exact below
  · intro varId free below
    apply covered.targets varId
    · rw [Context.ftv, List.flatMap_cons, List.mem_append]
      exact Or.inr free
    · exact below

theorem ProtectedOldFreeAt.nil
    (supply : InferenceBase.FreshSupply) (active : Context) :
    ProtectedOldFreeAt supply active [] := by
  simp [ProtectedOldFreeAt]

theorem ProtectedOldFreeAt.cons
    {supply : InferenceBase.FreshSupply} {active : Context}
    {algorithm : Ty} {selected : STy} {frontier : List (Ty × STy)}
    (head : OldFreeInContextAt supply active algorithm)
    (tail : ProtectedOldFreeAt supply active frontier) :
    ProtectedOldFreeAt supply active ((algorithm, selected) :: frontier) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | old
  · exact head
  · exact tail pair old

theorem ProtectedOldFreeAt.consFreshTarget
    {supply : InferenceBase.FreshSupply} {active : Context}
    {selected : STy} {frontier : List (Ty × STy)}
    (tail : ProtectedOldFreeAt supply active frontier) :
    ProtectedOldFreeAt supply active
      ((.var supply.nextTy, selected) :: frontier) :=
  tail.cons (OldFreeInContextAt.var supply active supply.nextTy
    (Nat.le_refl _))

theorem ProtectedOldFreeAt.consFn
    {supply : InferenceBase.FreshSupply} {active : Context}
    {domain codomain : Ty} {selected : STy}
    {frontier : List (Ty × STy)}
    (domainOld : OldFreeInContextAt supply active domain)
    (codomainOld : OldFreeInContextAt supply active codomain)
    (tail : ProtectedOldFreeAt supply active frontier) :
    ProtectedOldFreeAt supply active
      ((.fn domain codomain, selected) :: frontier) :=
  tail.cons (OldFreeInContextAt.fn domainOld codomainOld)

theorem ProtectedOldFreeAt.consProd
    {supply : InferenceBase.FreshSupply} {active : Context}
    {components : List Ty} {selected : STy}
    {frontier : List (Ty × STy)}
    (componentsOld : ∀ component ∈ components,
      OldFreeInContextAt supply active component)
    (tail : ProtectedOldFreeAt supply active frontier) :
    ProtectedOldFreeAt supply active
      ((.prod components, selected) :: frontier) :=
  tail.cons (OldFreeInContextAt.prod componentsOld)

theorem ProtectedOldFreeAt.of_subset
    {supply : InferenceBase.FreshSupply} {active : Context}
    {larger smaller : List (Ty × STy)}
    (old : ProtectedOldFreeAt supply active larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ProtectedOldFreeAt supply active smaller := by
  intro pair member
  exact old pair (subset pair member)

theorem OldFreeInContextAt.contextMono
    {supply : InferenceBase.FreshSupply} {smaller larger : Context}
    {target : Ty} (old : OldFreeInContextAt supply smaller target)
    (caps : ∀ varId, varId ∈ smaller.fcv → varId ∈ larger.fcv)
    (targets : ∀ varId, varId ∈ smaller.ftv → varId ∈ larger.ftv) :
    OldFreeInContextAt supply larger target := by
  exact
    { caps := fun varId free below => caps varId (old.caps varId free below)
      targets := fun varId free below =>
        targets varId (old.targets varId free below) }

theorem ProtectedOldFreeAt.contextMono
    {supply : InferenceBase.FreshSupply} {smaller larger : Context}
    {frontier : List (Ty × STy)}
    (old : ProtectedOldFreeAt supply smaller frontier)
    (caps : ∀ varId, varId ∈ smaller.fcv → varId ∈ larger.fcv)
    (targets : ∀ varId, varId ∈ smaller.ftv → varId ∈ larger.ftv) :
    ProtectedOldFreeAt supply larger frontier := by
  intro pair member
  exact (old pair member).contextMono caps targets

theorem RetainedOldOrContextAt.contextMono
    {supply : InferenceBase.FreshSupply} {smaller larger : Context}
    {suffix : Subst} {frontier : List (Ty × STy)}
    (retained : RetainedOldOrContextAt supply smaller suffix frontier)
    (caps : ∀ varId, varId ∈ smaller.fcv → varId ∈ larger.fcv)
    (targets : ∀ varId, varId ∈ smaller.ftv → varId ∈ larger.ftv) :
    RetainedOldOrContextAt supply larger suffix frontier := by
  constructor
  · intro pair member varId free
    rcases retained.caps pair member varId free with below | owned
    · exact Or.inl below
    · exact Or.inr (caps varId owned)
  · intro pair member varId free
    rcases retained.targets pair member varId free with below | owned
    · exact Or.inl below
    · exact Or.inr (targets varId owned)

/-- The lambda-domain frontier entry is retained by extending the provenance
owner with the same fresh monomorphic binding used by the recursive body. -/
theorem RetainedOldOrContextAt.consFreshTargetOwned
    {floor supply : InferenceBase.FreshSupply} {owner : Context}
    {frontier : List (Ty × STy)} {selected : STy} {name : String}
    (retained : RetainedOldOrContextAt floor owner Subst.id frontier) :
    RetainedOldOrContextAt floor
      ((name, Scheme.mono (.var supply.nextTy)) :: owner) Subst.id
      ((.var supply.nextTy, selected) :: frontier) := by
  constructor
  · intro pair member varId free
    rcases List.mem_cons.mp member with rfl | old
    · simp [Subst.apply_id, Ty.fcv] at free
    · rcases retained.caps pair old varId free with below | owned
      · exact Or.inl below
      · rw [Context.fcv, List.flatMap_cons, List.mem_append]
        exact Or.inr (Or.inr owned)
  · intro pair member varId free
    rcases List.mem_cons.mp member with rfl | old
    · have equality : varId = supply.nextTy := by
        simpa [Subst.apply_id, Ty.ftv] using free
      subst varId
      right
      rw [Context.ftv, List.flatMap_cons, List.mem_append]
      left
      simp [Scheme.mono, Scheme.ftv, PolyTy.lift, PolyTy.ftv]
    · rcases retained.targets pair old varId free with below | owned
      · exact Or.inl below
      · rw [Context.ftv, List.flatMap_cons, List.mem_append]
        exact Or.inr (Or.inr owned)

/-- Raising the entry supply strengthens old-free provenance; therefore a
fact at the raised supply can always be viewed at the earlier supply. -/
theorem OldFreeInContextAt.of_supply_le
    {smaller larger : InferenceBase.FreshSupply} {active : Context}
    {target : Ty} (old : OldFreeInContextAt larger active target)
    (caps : smaller.nextCap ≤ larger.nextCap)
    (targets : smaller.nextTy ≤ larger.nextTy) :
    OldFreeInContextAt smaller active target := by
  constructor
  · intro varId free below
    exact old.caps varId free (Nat.lt_of_lt_of_le below caps)
  · intro varId free below
    exact old.targets varId free (Nat.lt_of_lt_of_le below targets)

theorem ProtectedOldFreeAt.of_supply_le
    {smaller larger : InferenceBase.FreshSupply} {active : Context}
    {frontier : List (Ty × STy)}
    (old : ProtectedOldFreeAt larger active frontier)
    (caps : smaller.nextCap ≤ larger.nextCap)
    (targets : smaller.nextTy ≤ larger.nextTy) :
    ProtectedOldFreeAt smaller active frontier := by
  intro pair member
  exact (old pair member).of_supply_le caps targets

/-- Exact image condition used by generative solver transport.  It is local
to one source target and distinguishes the three image paths in `Ty.apply`.-/
structure OldImagesCoveredOn (entrySupply : InferenceBase.FreshSupply)
    (active : Context) (delta : Subst) (target : Ty) : Prop where
  caps : ∀ source, source ∈ target.fcv → ∀ image,
    image ∈ (delta.cap source).fcv →
    image.id < entrySupply.nextCap → image ∈ active.fcv
  targetCaps : ∀ source, source ∈ target.ftv → ∀ image,
    image ∈ (delta.target source).fcv →
    image.id < entrySupply.nextCap → image ∈ active.fcv
  targets : ∀ source, source ∈ target.ftv → ∀ image,
    image ∈ (delta.target source).ftv →
    image < entrySupply.nextTy → image ∈ active.ftv

def ProtectedOldImagesCoveredOn (entrySupply : InferenceBase.FreshSupply)
    (active : Context) (delta : Subst)
    (frontier : List (Ty × STy)) : Prop :=
  ∀ pair ∈ frontier, OldImagesCoveredOn entrySupply active delta pair.1

/-- Exact-MGU support/range confinement constructs the image condition.
Constraint variables are covered by the final active context; sources outside
the constraint are fixed and fall back to the old-free premise. -/
theorem OldImagesCoveredOn.ofOriginSafeExactPairedMGU
    {supply : InferenceBase.FreshSupply}
    {oldActive finalActive : Context} {target left right : Ty} {delta : Subst}
    (old : OldFreeInContextAt supply oldActive target)
    (oldCaps : ∀ varId, varId ∈ oldActive.fcv →
      varId ∉ left.fcv ++ right.fcv → varId ∈ finalActive.fcv)
    (oldTargets : ∀ varId, varId ∈ oldActive.ftv →
      varId ∉ left.ftv ++ right.ftv → varId ∈ finalActive.ftv)
    (endpointCaps : ∀ varId, varId ∈ left.fcv ++ right.fcv →
      varId.id < supply.nextCap → varId ∈ finalActive.fcv)
    (endpointTargets : ∀ varId, varId ∈ left.ftv ++ right.ftv →
      varId < supply.nextTy → varId ∈ finalActive.ftv)
    (exact : OriginSafeExactPairedMGU [] left right delta) :
    OldImagesCoveredOn supply finalActive delta target := by
  constructor
  · intro source sourceFree image imageFree below
    by_cases sourceConstraint : source ∈ left.fcv ++ right.fcv
    · exact endpointCaps image
        (exact.exact.2.2.2.1 source sourceConstraint image imageFree) below
    · rw [exact.exact.2.1 source sourceConstraint] at imageFree
      have imageEq : image = source := by simpa [Cap.fcv] using imageFree
      subst image
      exact oldCaps source (old.caps source sourceFree below) sourceConstraint
  · intro source sourceFree image imageFree _below
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact endpointCaps image
        (exact.exact.2.2.2.2.2.1 source sourceConstraint image imageFree) _below
    · rw [exact.exact.2.2.1 source sourceConstraint] at imageFree
      simp [Ty.fcv] at imageFree
  · intro source sourceFree image imageFree below
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact endpointTargets image
        (exact.exact.2.2.2.2.1 source sourceConstraint image imageFree) below
    · rw [exact.exact.2.2.1 source sourceConstraint] at imageFree
      have imageEq : image = source := by simpa [Ty.ftv] using imageFree
      subst image
      exact oldTargets source (old.targets source sourceFree below)
        sourceConstraint

theorem ProtectedOldImagesCoveredOn.ofOriginSafeExactPairedMGU
    {supply : InferenceBase.FreshSupply}
    {oldActive finalActive : Context} {frontier : List (Ty × STy)}
    {left right : Ty} {delta : Subst}
    (old : ProtectedOldFreeAt supply oldActive frontier)
    (oldCaps : ∀ varId, varId ∈ oldActive.fcv →
      varId ∉ left.fcv ++ right.fcv → varId ∈ finalActive.fcv)
    (oldTargets : ∀ varId, varId ∈ oldActive.ftv →
      varId ∉ left.ftv ++ right.ftv → varId ∈ finalActive.ftv)
    (endpointCaps : ∀ varId, varId ∈ left.fcv ++ right.fcv →
      varId.id < supply.nextCap → varId ∈ finalActive.fcv)
    (endpointTargets : ∀ varId, varId ∈ left.ftv ++ right.ftv →
      varId < supply.nextTy → varId ∈ finalActive.ftv)
    (exact : OriginSafeExactPairedMGU [] left right delta) :
    ProtectedOldImagesCoveredOn supply finalActive delta frontier := by
  intro pair member
  exact OldImagesCoveredOn.ofOriginSafeExactPairedMGU (old pair member)
    oldCaps oldTargets endpointCaps endpointTargets exact

theorem OldFreeInContextAt.apply
    {supply : InferenceBase.FreshSupply} {active : Context}
    {delta : Subst} {target : Ty}
    (images : OldImagesCoveredOn supply active delta target) :
    OldFreeInContextAt supply active (delta.apply target) := by
  constructor
  · intro image free below
    unfold Subst.apply at free
    rcases Unification.Ty.mem_fcv_applyTarget _ _ _ free with own | introduced
    · rw [Unification.Ty.fcv_applyCapability] at own
      rcases List.mem_flatMap.mp own with ⟨source, sourceFree, imageFree⟩
      exact images.caps source sourceFree image imageFree below
    · rcases introduced with ⟨source, sourceFree, imageFree⟩
      rw [Unification.Ty.ftv_applyCapability] at sourceFree
      exact images.targetCaps source sourceFree image imageFree below
  · intro image free below
    unfold Subst.apply at free
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability] at free
    rcases List.mem_flatMap.mp free with ⟨source, sourceFree, imageFree⟩
    exact images.targets source sourceFree image imageFree below

theorem ProtectedOldFreeAt.map_apply
    {supply : InferenceBase.FreshSupply} {active : Context}
    {delta : Subst} {frontier : List (Ty × STy)}
    (images : ProtectedOldImagesCoveredOn supply active delta frontier) :
    ProtectedOldFreeAt supply active
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  intro pair member
  rcases List.mem_map.mp member with ⟨oldPair, oldMember, rfl⟩
  exact OldFreeInContextAt.apply (images oldPair oldMember)

/-- Transport context provenance through the capability-free exact cuts used
by the DM fragment.  Constraint-range variables are owned by the final owner
context; sources outside the constraint are fixed by exactness. -/
theorem OldContextCoveredAt.applyOriginSafeExactPairedMGU
    {floor : InferenceBase.FreshSupply} {owner active : Context}
    {left right : Ty} {delta : Subst}
    (covered : OldContextCoveredAt floor owner active)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (endpointTargets : ∀ image, image ∈ left.ftv ++ right.ftv →
      image < floor.nextTy → image ∈ (owner.applySubst delta).ftv) :
    OldContextCoveredAt floor (owner.applySubst delta)
      (active.applySubst delta) := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree exact
      leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
      leftCapFree rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  constructor
  · intro varId free below
    rw [deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree] at free ⊢
    exact covered.caps varId free below
  · intro image free below
    rw [Context.ftv_applySubst_flatMap] at free
    rcases List.mem_flatMap.mp free with ⟨source, sourceFree, imageFree⟩
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact endpointTargets image
        (exact.exact.2.2.2.2.1 source sourceConstraint image imageFree) below
    · rw [exact.exact.2.2.1 source sourceConstraint] at imageFree
      have imageEq : image = source := by simpa [Ty.ftv] using imageFree
      subst image
      have ownerFree := covered.targets source sourceFree below
      rw [Context.ftv_applySubst_flatMap]
      apply List.mem_flatMap.mpr
      refine ⟨source, ownerFree, ?_⟩
      rw [exact.exact.2.2.1 source sourceConstraint]
      simp [Ty.ftv]

/-- Forward owner inclusion is functorial under the same capability-free
exact cut on both contexts. -/
theorem ProvenanceContextIncluded.applyOriginSafeExactPairedMGU
    {owner active : Context} {left right : Ty} {delta : Subst}
    (included : ProvenanceContextIncluded owner active)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    ProvenanceContextIncluded (owner.applySubst delta)
      (active.applySubst delta) := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree exact
      leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
      leftCapFree rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  constructor
  · intro varId free
    rw [deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree] at free ⊢
    exact included.caps varId free
  · intro image free
    rw [Context.ftv_applySubst_flatMap] at free ⊢
    rcases List.mem_flatMap.mp free with ⟨source, sourceFree, imageFree⟩
    exact List.mem_flatMap.mpr
      ⟨source, included.targets source sourceFree, imageFree⟩

/-- Simultaneous exact-cut transport for the fixed provenance context and a
protected continuation frontier.  Endpoint old-freeness is enough: exact
range confinement puts every introduced image back in an endpoint, while
idempotence fixes every variable occurring in such an image. -/
theorem OldContextCoveredAt.applyOriginSafeExactPairedMGU_and_protected
    {floor : InferenceBase.FreshSupply} {owner active : Context}
    {frontier : List (Ty × STy)} {left right : Ty} {delta : Subst}
    (covered : OldContextCoveredAt floor owner active)
    (frontierOld : ProtectedOldFreeAt floor active frontier)
    (leftOld : OldFreeInContextAt floor owner left)
    (rightOld : OldFreeInContextAt floor owner right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    OldContextCoveredAt floor (owner.applySubst delta)
        (active.applySubst delta) ∧
      ProtectedOldFreeAt floor (owner.applySubst delta)
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree exact
      leftCapFree rightCapFree
  have targetCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
      leftCapFree rightCapFree
  have endpointOld : ∀ varId, varId ∈ left.ftv ++ right.ftv →
      varId < floor.nextTy → varId ∈ owner.ftv := by
    intro varId member below
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact leftOld.targets varId leftMember below
    · exact rightOld.targets varId rightMember below
  have imageFixed : ∀ source image,
      image ∈ (delta.target source).ftv → delta.target image = .var image := by
    intro source image imageFree
    apply exact.exact.2.2.2.2.2.2.image_target_fixed (.var source) image
    simpa [Subst.apply, Ty.applyCapability, Ty.applyTarget] using imageFree
  have ownerTargetApplied : ∀ source image,
      source ∈ owner.ftv → delta.target source = .var image →
        image ∈ (owner.applySubst delta).ftv := by
    intro source image sourceFree equation
    rw [Context.ftv_applySubst_flatMap]
    exact List.mem_flatMap.mpr
      ⟨source, sourceFree, by rw [equation]; simp [Ty.ftv]⟩
  have ownerCapApplied : ∀ varId, varId ∈ owner.fcv →
      varId ∈ (owner.applySubst delta).fcv := by
    intro varId sourceFree
    have deltaEq : delta =
        ({ cap := CapSubst.id, target := delta.target } : Subst) := by
      apply PhasedPost.subst_ext
      · exact capEq
      · rfl
    rw [deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target targetCapFree]
    exact sourceFree
  have contextFinal : OldContextCoveredAt floor (owner.applySubst delta)
      (active.applySubst delta) := by
    constructor
    · intro varId free below
      have deltaEq : delta =
          ({ cap := CapSubst.id, target := delta.target } : Subst) := by
        apply PhasedPost.subst_ext
        · exact capEq
        · rfl
      rw [deltaEq,
        Context.fcv_applySubst_targetOnly_eq delta.target targetCapFree] at free
      exact ownerCapApplied varId (covered.caps varId free below)
    · intro image free below
      rw [Context.ftv_applySubst_flatMap] at free
      rcases List.mem_flatMap.mp free with ⟨source, sourceFree, freeInImage⟩
      by_cases constrained : source ∈ left.ftv ++ right.ftv
      · have imageEndpoint :=
          exact.exact.2.2.2.2.1 source constrained image freeInImage
        exact ownerTargetApplied image image
          (endpointOld image imageEndpoint below)
          (imageFixed source image freeInImage)
      · have fixed := exact.exact.2.2.1 source constrained
        have imageEq : image = source := by
          rw [fixed] at freeInImage
          simpa [Ty.ftv] using freeInImage
        subst image
        exact ownerTargetApplied source source
          (covered.targets source sourceFree below) fixed
  have protectedImages : ProtectedOldImagesCoveredOn floor
      (owner.applySubst delta) delta frontier := by
    intro pair pairMember
    have old := frontierOld pair pairMember
    constructor
    · intro source sourceFree image freeInImage below
      rw [capEq] at freeInImage
      have imageEq : image = source := by
        simpa [CapSubst.id, Cap.fcv] using freeInImage
      subst image
      exact ownerCapApplied source
        (covered.caps source (old.caps source sourceFree below) below)
    · intro source _sourceFree image freeInImage _below
      rw [targetCapFree source] at freeInImage
      exact False.elim (List.not_mem_nil freeInImage)
    · intro source sourceFree image freeInImage below
      by_cases constrained : source ∈ left.ftv ++ right.ftv
      · have imageEndpoint :=
          exact.exact.2.2.2.2.1 source constrained image freeInImage
        exact ownerTargetApplied image image
          (endpointOld image imageEndpoint below)
          (imageFixed source image freeInImage)
      · have fixed := exact.exact.2.2.1 source constrained
        have imageEq : image = source := by
          rw [fixed] at freeInImage
          simpa [Ty.ftv] using freeInImage
        subst image
        exact ownerTargetApplied source source
          (covered.targets source (old.targets source sourceFree below) below)
          fixed
  exact ⟨contextFinal, ProtectedOldFreeAt.map_apply protectedImages⟩

/-- Transport a fixed input frontier through an exact DM cut.  The endpoint
premises state precisely that every variable visible to the solver is either
still below the provenance floor or owned by the final context.  Exact range
confinement propagates that disjunction to every substitution image. -/
theorem RetainedOldOrContextAt.applyOriginSafeExactPairedMGU
    {floor : InferenceBase.FreshSupply} {oldOwner finalOwner : Context}
    {suffix delta : Subst} {frontier : List (Ty × STy)}
    {left right : Ty}
    (retained : RetainedOldOrContextAt floor oldOwner suffix frontier)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (oldCaps : ∀ source, source ∈ oldOwner.fcv →
      source ∈ finalOwner.fcv)
    (oldTargets : ∀ source, source ∈ oldOwner.ftv →
      source ∉ left.ftv ++ right.ftv → source ∈ finalOwner.ftv)
    (endpointTargets : ∀ image, image ∈ left.ftv ++ right.ftv →
      image < floor.nextTy ∨ image ∈ finalOwner.ftv) :
    RetainedOldOrContextAt floor finalOwner
      (Subst.seq delta suffix) frontier := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree exact
      leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
      leftCapFree rightCapFree
  constructor
  · intro pair member image free
    rw [Subst.seq_apply] at free
    unfold Subst.apply at free
    rcases Unification.Ty.mem_fcv_applyTarget _ _ _ free with own | introduced
    · rw [Unification.Ty.fcv_applyCapability, capEq] at own
      rcases List.mem_flatMap.mp own with ⟨source, sourceFree, imageFree⟩
      have imageEq : image = source := by
        simpa [CapSubst.id, Cap.fcv] using imageFree
      subst image
      rcases retained.caps pair member source sourceFree with below | owned
      · exact Or.inl below
      · exact Or.inr (oldCaps source owned)
    · rcases introduced with ⟨source, _sourceFree, imageFree⟩
      rw [imagesCapFree source] at imageFree
      exact False.elim (List.not_mem_nil imageFree)
  · intro pair member image free
    rw [Subst.seq_apply] at free
    unfold Subst.apply at free
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability] at free
    rcases List.mem_flatMap.mp free with ⟨source, sourceFree, imageFree⟩
    by_cases sourceConstraint : source ∈ left.ftv ++ right.ftv
    · exact endpointTargets image
        (exact.exact.2.2.2.2.1 source sourceConstraint image imageFree)
    · rw [exact.exact.2.2.1 source sourceConstraint] at imageFree
      have imageEq : image = source := by simpa [Ty.ftv] using imageFree
      subst image
      rcases retained.targets pair member source sourceFree with below | owned
      · exact Or.inl below
      · exact Or.inr (oldTargets source owned sourceConstraint)

/-- Two-way retained provenance is solver-stable when both exact-cut
endpoints are themselves old-free in the fixed owner.  This is the
constructor-facing form: unlike the lower-level range theorem above it asks
for no pointwise endpoint-image oracle. -/
theorem RetainedOldOrContextAt.applyOriginSafeExactPairedMGU_of_endpointsOld
    {floor : InferenceBase.FreshSupply} {owner : Context}
    {suffix delta : Subst} {frontier : List (Ty × STy)}
    {left right : Ty}
    (retained : RetainedOldOrContextAt floor owner suffix frontier)
    (leftOld : OldFreeInContextAt floor owner left)
    (rightOld : OldFreeInContextAt floor owner right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    RetainedOldOrContextAt floor (owner.applySubst delta)
      (Subst.seq delta suffix) frontier := by
  have capEq : delta.cap = CapSubst.id :=
    OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree exact
      leftCapFree rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree exact
      leftCapFree rightCapFree
  have ownerCapApplied : ∀ varId, varId ∈ owner.fcv →
      varId ∈ (owner.applySubst delta).fcv := by
    intro varId sourceFree
    have deltaEq : delta =
        ({ cap := CapSubst.id, target := delta.target } : Subst) := by
      apply PhasedPost.subst_ext
      · exact capEq
      · rfl
    rw [deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree]
    exact sourceFree
  have ownerImageApplied : ∀ source image,
      source ∈ owner.ftv → image ∈ (delta.target source).ftv →
        image ∈ (owner.applySubst delta).ftv := by
    intro source image sourceFree imageFree
    rw [Context.ftv_applySubst_flatMap]
    exact List.mem_flatMap.mpr ⟨source, sourceFree, imageFree⟩
  have endpointOwner : ∀ source, source ∈ left.ftv ++ right.ftv →
      source < floor.nextTy → source ∈ owner.ftv := by
    intro source endpoint below
    rcases List.mem_append.mp endpoint with leftMember | rightMember
    · exact leftOld.targets source leftMember below
    · exact rightOld.targets source rightMember below
  constructor
  · intro pair member image free
    rw [Subst.seq_apply] at free
    unfold Subst.apply at free
    rcases Unification.Ty.mem_fcv_applyTarget _ _ _ free with own | introduced
    · rw [Unification.Ty.fcv_applyCapability, capEq] at own
      rcases List.mem_flatMap.mp own with ⟨source, sourceFree, imageFree⟩
      have imageEq : image = source := by
        simpa [CapSubst.id, Cap.fcv] using imageFree
      subst image
      rcases retained.caps pair member source sourceFree with below | owned
      · exact Or.inl below
      · exact Or.inr (ownerCapApplied source owned)
    · rcases introduced with ⟨source, _sourceFree, imageFree⟩
      rw [imagesCapFree source] at imageFree
      exact False.elim (List.not_mem_nil imageFree)
  · intro pair member image free
    rw [Subst.seq_apply] at free
    unfold Subst.apply at free
    rw [Unification.Ty.ftv_applyTarget,
      Unification.Ty.ftv_applyCapability] at free
    rcases List.mem_flatMap.mp free with ⟨source, sourceFree, imageFree⟩
    by_cases constrained : source ∈ left.ftv ++ right.ftv
    · rcases retained.targets pair member source sourceFree with below | owned
      · exact Or.inr
          (ownerImageApplied source image
            (endpointOwner source constrained below) imageFree)
      · exact Or.inr (ownerImageApplied source image owned imageFree)
    · rw [exact.exact.2.2.1 source constrained] at imageFree
      have imageEq : image = source := by simpa [Ty.ftv] using imageFree
      subst image
      rcases retained.targets pair member source sourceFree with below | owned
      · exact Or.inl below
      · exact Or.inr (ownerImageApplied source source owned (by
          rw [exact.exact.2.2.1 source constrained]
          simp [Ty.ftv]))

/-- Boundedness closes initialization when the active environment is known
to cover every free variable of the frontier.  Boundedness alone is
insufficient, so ownership is intentionally a separate premise. -/
theorem ProtectedOldFreeAt.of_bounded_covered
    {supply : InferenceBase.FreshSupply} {active : Context}
    {frontier : List (Ty × STy)}
    (_bounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply)
    (caps : ∀ pair ∈ frontier, ∀ varId,
      varId ∈ pair.1.fcv → varId ∈ active.fcv)
    (targets : ∀ pair ∈ frontier, ∀ varId,
      varId ∈ pair.1.ftv → varId ∈ active.ftv) :
    ProtectedOldFreeAt supply active frontier := by
  intro pair member
  exact
    { caps := fun varId free _ => caps pair member varId free
      targets := fun varId free _ => targets pair member varId free }

end DM
end TypePM
