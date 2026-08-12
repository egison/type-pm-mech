import TypePM.SourceSubstitution

/-!
# Scoped two-sorted type instances

An instance witness is a paired substitution whose finite support is
explicit.  Capability and ordinary target metavariables have separate
scopes.  The unscoped public relation uses exactly the free variables of the
source type as its scope; consequently a witness cannot change an unrelated
ambient metavariable.

Composition is followed by restriction back to the original source scope.
This is important because the first substitution may introduce variables
outside that scope which the second substitution subsequently changes.
-/

namespace TypePM

/-- Restrict a paired substitution to two finite, sort-separated scopes. -/
def Subst.restrict (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) (post : Subst) : Subst :=
  { cap := fun varId =>
      if varId ∈ capScope then post.cap varId else .var varId
    target := fun varId =>
      if varId ∈ targetScope then post.target varId else .var varId }

@[simp] theorem Subst.restrict_cap_of_mem
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (post : Subst) {varId : CapVar} (member : varId ∈ capScope) :
    (post.restrict capScope targetScope).cap varId = post.cap varId := by
  simp [Subst.restrict, member]

@[simp] theorem Subst.restrict_target_of_mem
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    (post : Subst) {varId : TypePM.TyVar} (member : varId ∈ targetScope) :
    (post.restrict capScope targetScope).target varId = post.target varId := by
  simp [Subst.restrict, member]

theorem Subst.restrict_capSupport
    (post : Subst) (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) :
    (post.restrict capScope targetScope).cap.SupportWithin capScope := by
  intro varId outside
  simp [Subst.restrict, outside]

theorem Subst.restrict_targetSupport
    (post : Subst) (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) :
    (post.restrict capScope targetScope).target.SupportWithin targetScope := by
  intro varId outside
  simp [Subst.restrict, outside]

/-- Restriction is observationally invisible on a type whose free variables
are contained in the selected scopes. -/
theorem Subst.restrict_apply
    (post : Subst) (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) (source : Ty)
    (caps : ∀ varId, varId ∈ source.fcv → varId ∈ capScope)
    (targets : ∀ varId, varId ∈ source.ftv → varId ∈ targetScope) :
    (post.restrict capScope targetScope).apply source = post.apply source := by
  apply Subst.apply_eq_of_free_agree
  · intro varId member
    exact Subst.restrict_cap_of_mem post (caps varId member)
  · intro varId member
    exact Subst.restrict_target_of_mem post (targets varId member)

/-- `target` is an instance of `source` under a substitution allowed to
change only the displayed finite scopes. -/
def ScopedTypeInstance (capScope : List CapVar)
    (targetScope : List TypePM.TyVar) (source target : Ty) : Prop :=
  ∃ post : Subst,
    post.cap.SupportWithin capScope ∧
    post.target.SupportWithin targetScope ∧
    post.apply source = target

/-- Public two-sorted instance preorder.  Its mutable scope is precisely the
finite set of capability and target metavariables occurring in the source. -/
def TypeInstance (source target : Ty) : Prop :=
  ScopedTypeInstance source.fcv source.ftv source target

namespace ScopedTypeInstance

theorem refl (capScope : List CapVar) (targetScope : List TypePM.TyVar)
    (source : Ty) : ScopedTypeInstance capScope targetScope source source := by
  exact ⟨Subst.id, CapSubst.id_supportWithin capScope,
    TySubst.id_supportWithin targetScope, Subst.apply_id source⟩

/-- Scoped instances compose.  The chronological composite is restricted
back to the original finite scope before it is exposed. -/
theorem trans
    {capScope : List CapVar} {targetScope : List TypePM.TyVar}
    {source middle target : Ty}
    (first : ScopedTypeInstance capScope targetScope source middle)
    (second : ScopedTypeInstance middle.fcv middle.ftv middle target) :
    (∀ varId, varId ∈ source.fcv → varId ∈ capScope) →
    (∀ varId, varId ∈ source.ftv → varId ∈ targetScope) →
    ScopedTypeInstance capScope targetScope source target := by
  intro sourceCaps sourceTargets
  rcases first with ⟨earlier, _earlierCaps, _earlierTargets, sourceEq⟩
  rcases second with ⟨later, _laterCaps, _laterTargets, middleEq⟩
  let composite := Subst.seq later earlier
  let restricted := composite.restrict capScope targetScope
  refine ⟨restricted, Subst.restrict_capSupport composite capScope targetScope,
    Subst.restrict_targetSupport composite capScope targetScope, ?_⟩
  calc
    restricted.apply source = composite.apply source := by
      exact Subst.restrict_apply composite capScope targetScope source
        sourceCaps sourceTargets
    _ = later.apply (earlier.apply source) :=
      Subst.seq_apply later earlier source
    _ = target := by rw [sourceEq, middleEq]

end ScopedTypeInstance

namespace TypeInstance

theorem refl (source : Ty) : TypeInstance source source :=
  ScopedTypeInstance.refl source.fcv source.ftv source

theorem trans {source middle target : Ty}
    (first : TypeInstance source middle)
    (second : TypeInstance middle target) :
    TypeInstance source target :=
  ScopedTypeInstance.trans first second
    (fun _ member => member) (fun _ member => member)

/-- Any paired substitution gives an instance after restriction to the
source's actual free-variable scope. -/
theorem of_apply {source target : Ty} (post : Subst)
    (equation : post.apply source = target) : TypeInstance source target := by
  let restricted := post.restrict source.fcv source.ftv
  refine ⟨restricted,
    Subst.restrict_capSupport post source.fcv source.ftv,
    Subst.restrict_targetSupport post source.fcv source.ftv, ?_⟩
  rw [Subst.restrict_apply post source.fcv source.ftv source
    (fun _ member => member) (fun _ member => member)]
  exact equation

end TypeInstance

end TypePM
