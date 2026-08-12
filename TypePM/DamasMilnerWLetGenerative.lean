import TypePM.DamasMilnerWErasedLetBridge

/-!
# Generative invariants for Damas--Milner let registration

These invariants record provenance rather than the desired registration
conclusion.  `OldFreeInContextAt` says an inferred value introduces no old
free variable not already owned by its environment.  `ProtectedFreeCovered`
says every protected context is scoped by the active context.  Together they
are the finite support facts needed when a completed value is generalized.
-/

namespace TypePM
namespace DM

/-- Below the entry supply, every free variable of the value target is
already free in its normalized environment. -/
structure OldFreeInContextAt (entrySupply : InferenceBase.FreshSupply)
    (normalizedContext : Context) (normalizedTarget : Ty) : Prop where
  caps : ∀ varId, varId ∈ normalizedTarget.fcv →
    varId.id < entrySupply.nextCap → varId ∈ normalizedContext.fcv
  targets : ∀ varId, varId ∈ normalizedTarget.ftv →
    varId < entrySupply.nextTy → varId ∈ normalizedContext.ftv

theorem OldFreeInContextAt.int (supply : InferenceBase.FreshSupply)
    (context : Context) : OldFreeInContextAt supply context .int := by
  constructor <;> intros <;> simp_all [Ty.fcv, Ty.ftv]

theorem OldFreeInContextAt.var
    (supply : InferenceBase.FreshSupply) (context : Context)
    (varId : TypePM.TyVar) (fresh : supply.nextTy ≤ varId) :
    OldFreeInContextAt supply context (.var varId) := by
  constructor
  · intros
    simp_all [Ty.fcv]
  · intro candidate member below
    simp only [Ty.ftv, List.mem_singleton] at member
    subst candidate
    exact (Nat.not_lt_of_ge fresh below).elim

theorem OldFreeInContextAt.fn
    {supply : InferenceBase.FreshSupply} {context : Context}
    {domain codomain : Ty}
    (domainOld : OldFreeInContextAt supply context domain)
    (codomainOld : OldFreeInContextAt supply context codomain) :
    OldFreeInContextAt supply context (.fn domain codomain) := by
  constructor
  · intro varId member below
    rcases List.mem_append.mp member with member | member
    · exact domainOld.caps varId member below
    · exact codomainOld.caps varId member below
  · intro varId member below
    rcases List.mem_append.mp member with member | member
    · exact domainOld.targets varId member below
    · exact codomainOld.targets varId member below

theorem OldFreeInContextAt.prod
    {supply : InferenceBase.FreshSupply} {context : Context}
    {components : List Ty}
    (old : ∀ component ∈ components,
      OldFreeInContextAt supply context component) :
    OldFreeInContextAt supply context (.prod components) := by
  constructor
  · intro varId member below
    obtain ⟨component, componentMember, free⟩ :=
      Ty.mem_fcvList_split member
    exact (old component componentMember).caps varId free below
  · intro varId member below
    obtain ⟨component, componentMember, free⟩ :=
      Ty.mem_ftvList_split member
    exact (old component componentMember).targets varId free below

/-- Every solver-visible variable of a protected normalized context is also
owned by the displayed active normalized context. -/
structure ProtectedFreeCovered (active : Context)
    (frames : List (Context × SCtx)) (current : Subst) : Prop where
  caps : ∀ pair ∈ frames, ∀ varId,
    varId ∈ (pair.1.applySubst current).fcv → varId ∈ active.fcv
  targets : ∀ pair ∈ frames, ∀ varId,
    varId ∈ (pair.1.applySubst current).ftv → varId ∈ active.ftv

/-- Every free variable on the retained continuation surface is either older
than the traversal entry or already visible in the final active context.
This is stable under generative solver steps and is strictly weaker than
requiring the whole continuation frontier to be environment-owned. -/
structure RetainedOldOrContextAt (entrySupply : InferenceBase.FreshSupply)
    (active : Context) (suffix : Subst)
    (frontier : List (Ty × STy)) : Prop where
  caps : ∀ pair ∈ frontier, ∀ varId,
    varId ∈ (suffix.apply pair.1).fcv →
      varId.id < entrySupply.nextCap ∨ varId ∈ active.fcv
  targets : ∀ pair ∈ frontier, ∀ varId,
    varId ∈ (suffix.apply pair.1).ftv →
      varId < entrySupply.nextTy ∨ varId ∈ active.ftv

theorem RetainedOldOrContextAt.identity_of_bounded
    {supply : InferenceBase.FreshSupply} {active : Context}
    {frontier : List (Ty × STy)}
    (bounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply) :
    RetainedOldOrContextAt supply active Subst.id frontier := by
  constructor <;> intro pair member varId free
  · left
    rw [Subst.apply_id] at free
    exact (bounded pair member).caps varId free
  · left
    rw [Subst.apply_id] at free
    exact (bounded pair member).targets varId free

theorem RetainedOldOrContextAt.nil
    (supply : InferenceBase.FreshSupply) (active : Context) (suffix : Subst) :
    RetainedOldOrContextAt supply active suffix [] := by
  constructor <;> simp

theorem RetainedOldOrContextAt.of_subset
    {supply : InferenceBase.FreshSupply} {active : Context} {suffix : Subst}
    {larger smaller : List (Ty × STy)}
    (covered : RetainedOldOrContextAt supply active suffix larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    RetainedOldOrContextAt supply active suffix smaller := by
  exact
    { caps := fun pair member => covered.caps pair (subset pair member)
      targets := fun pair member => covered.targets pair (subset pair member) }

/-- A variable generalized from a target satisfying old-free provenance is
necessarily new with respect to the entry supply. -/
theorem OldFreeInContextAt.generalized_not_old
    {signature : FrozenSig} {entrySupply : InferenceBase.FreshSupply}
    {active : Context} {target : Ty}
    (old : OldFreeInContextAt entrySupply active target) :
    (∀ varId, varId ∈ signature.generalizedCapVars active target →
      ¬ varId.id < entrySupply.nextCap) ∧
    (∀ varId, varId ∈ signature.generalizedTyVars active target →
      ¬ varId < entrySupply.nextTy) := by
  constructor
  · intro varId generalized below
    have free : varId ∈ target.fcv := by
      unfold FrozenSig.generalizedCapVars at generalized
      exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1
    have inActive := old.caps varId free below
    exact mem_generalizedCapVars_not_env generalized
      (List.mem_append_right _ inActive)
  · intro varId generalized below
    have free : varId ∈ target.ftv := by
      unfold FrozenSig.generalizedTyVars at generalized
      exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1
    have inActive := old.targets varId free below
    exact mem_generalizedTyVars_not_env generalized
      (List.mem_append_right _ inActive)

/-- Old-or-environment coverage of the evolved input frontier gives exactly
the new let cut's frontier freshness premise. -/
theorem RetainedOldOrContextAt.avoidsGeneralized
    {signature : FrozenSig} {entrySupply : InferenceBase.FreshSupply}
    {active : Context} {target : Ty} {suffix current : Subst}
    {rawContext : Context} {rawTarget : Ty}
    {frontier : List (Ty × STy)}
    (covered : RetainedOldOrContextAt entrySupply active suffix frontier)
    (old : OldFreeInContextAt entrySupply active target)
    (activeEq : rawContext.applySubst current = active)
    (targetEq : current.apply rawTarget = target) :
    ∀ pair ∈ frontier,
      (PendingLetCut.mk rawContext rawTarget current).AvoidsTy signature current
        (suffix.apply pair.1) := by
  have notOld := old.generalized_not_old (signature := signature)
  intro pair member
  constructor
  · intro varId generalized free
    rw [activeEq, targetEq] at generalized
    rcases covered.caps pair member varId free with below | inActive
    · exact notOld.1 varId generalized below
    · exact mem_generalizedCapVars_not_env
        generalized
        (List.mem_append_right _ inActive)
  · intro varId generalized free
    rw [activeEq, targetEq] at generalized
    rcases covered.targets pair member varId free with below | inActive
    · exact notOld.2 varId generalized below
    · exact mem_generalizedTyVars_not_env
        generalized
        (List.mem_append_right _ inActive)

theorem ProtectedFreeCovered.initial (context : SCtx) :
    ProtectedFreeCovered context.emb [(context.emb, context)] Subst.id := by
  constructor <;> intro pair member varId free
  all_goals
    rcases List.mem_singleton.mp member with rfl
    simpa using free

theorem ProtectedFreeCovered.of_context_eq
    {left right : Context} {frames : List (Context × SCtx)} {current : Subst}
    (covered : ProtectedFreeCovered left frames current)
    (equality : right = left) : ProtectedFreeCovered right frames current := by
  subst right
  exact covered

theorem ProtectedFreeCovered.of_frames_subset
    {active : Context} {larger smaller : List (Context × SCtx)}
    {current : Subst} (covered : ProtectedFreeCovered active larger current)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ProtectedFreeCovered active smaller current := by
  exact
    { caps := fun pair member => covered.caps pair (subset pair member)
      targets := fun pair member => covered.targets pair (subset pair member) }

/-- If a newly protected context has the same free-variable sets as the
active context, it can be added without weakening coverage. -/
theorem ProtectedFreeCovered.cons
    {active head : Context} {headSelected : SCtx}
    {frames : List (Context × SCtx)} {current : Subst}
    (covered : ProtectedFreeCovered active frames current)
    (caps : (head.applySubst current).fcv = active.fcv)
    (targets : (head.applySubst current).ftv = active.ftv) :
    ProtectedFreeCovered active ((head, headSelected) :: frames) current := by
  constructor <;> intro pair member varId free
  · rcases List.mem_cons.mp member with rfl | old
    · rwa [caps] at free
    · exact covered.caps pair old varId free
  · rcases List.mem_cons.mp member with rfl | old
    · rwa [targets] at free
    · exact covered.targets pair old varId free

/-- Context coverage turns avoidance of the active context into avoidance of
every protected context, exactly the premise consumed by let registration. -/
theorem ProtectedFreeCovered.avoidsContexts
    {signature : FrozenSig} {active : Context}
    {frames : List (Context × SCtx)} {current : Subst}
    {cut : PendingLetCut} (covered : ProtectedFreeCovered active frames current)
    (fresh : cut.AvoidsContext signature current active) :
    ∀ pair ∈ frames,
      cut.AvoidsContext signature current (pair.1.applySubst current) := by
  intro pair member
  constructor
  · intro varId generalized free
    exact fresh.caps varId generalized (covered.caps pair member varId free)
  · intro varId generalized free
    exact fresh.targets varId generalized
      (covered.targets pair member varId free)

/-- The active context trivially avoids variables selected by generalization;
selected variables are defined to be outside that environment. -/
theorem PendingLetCut.avoidsOwnContext
    {signature : FrozenSig} {rawContext : Context} {rawTarget : Ty}
    {current : Subst} :
    (PendingLetCut.mk rawContext rawTarget current).AvoidsContext signature
      current (rawContext.applySubst current) := by
  constructor
  · intro varId generalized
    exact fun free => mem_generalizedCapVars_not_env generalized
      (List.mem_append_right _ free)
  · intro varId generalized
    exact fun free => mem_generalizedTyVars_not_env generalized
      (List.mem_append_right _ free)

/-- Protecting a let body introduces the generalized value scheme at the
context head.  Closing can only remove free metavariables from the value
target, so freshness of the outer context and value target implies freshness
of the whole generalized body context. -/
theorem PendingLetCut.AvoidsContext.consGeneralized
    {signature : FrozenSig} {current : Subst} {cut : PendingLetCut}
    {active : Context} {target : Ty} {name : String}
    (contextFresh : cut.AvoidsContext signature current active)
    (targetFresh : cut.AvoidsTy signature current target) :
    cut.AvoidsContext signature current
      ((name, signature.generalize active target) :: active) := by
  constructor
  · intro varId generalized free
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at free
    rcases free with headFree | outerFree
    · apply targetFresh.caps varId generalized
      unfold FrozenSig.generalize Scheme.generalize Scheme.close Scheme.fcv at headFree
      exact (PolyTy.abstract_free_subset _ _ target).1 varId headFree
    · exact contextFresh.caps varId generalized outerFree
  · intro varId generalized free
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at free
    rcases free with headFree | outerFree
    · apply targetFresh.targets varId generalized
      unfold FrozenSig.generalize Scheme.generalize Scheme.close Scheme.ftv at headFree
      exact (PolyTy.abstract_free_subset _ _ target).2 varId headFree
    · exact contextFresh.targets varId generalized outerFree

/-- The cut introduced at a let boundary avoids its own generalized body
context.  Variables selected by that cut become bound nodes in the scheme;
the remaining free scheme variables are outside the selected binder lists. -/
theorem PendingLetCut.avoidsOwnGeneralizedContext
    {signature : FrozenSig} {current : Subst}
    {rawContext : Context} {rawTarget : Ty} {name : String} :
    let active := rawContext.applySubst current
    let target := current.apply rawTarget
    (PendingLetCut.mk rawContext rawTarget current).AvoidsContext signature
      current ((name, signature.generalize active target) :: active) := by
  dsimp
  constructor
  · intro varId generalized free
    rw [Context.fcv, List.flatMap_cons, List.mem_append] at free
    rcases free with headFree | outerFree
    · unfold FrozenSig.generalize Scheme.generalize Scheme.close Scheme.fcv at headFree
      have closingNone :=
        (PolyTy.closing_none_of_abstract_free
          (fun candidate =>
            (signature.generalizedCapVars
              (rawContext.applySubst current) (current.apply rawTarget)).finIdxOf?
              candidate)
          (fun candidate =>
            (signature.generalizedTyVars
              (rawContext.applySubst current) (current.apply rawTarget)).finIdxOf?
              candidate)
          (current.apply rawTarget)).1 varId headFree
      exact (List.finIdxOf?_eq_none_iff.mp closingNone generalized).elim
    · exact mem_generalizedCapVars_not_env generalized
        (List.mem_append_right _ outerFree)
  · intro varId generalized free
    rw [Context.ftv, List.flatMap_cons, List.mem_append] at free
    rcases free with headFree | outerFree
    · unfold FrozenSig.generalize Scheme.generalize Scheme.close Scheme.ftv at headFree
      have closingNone :=
        (PolyTy.closing_none_of_abstract_free
          (fun candidate =>
            (signature.generalizedCapVars
              (rawContext.applySubst current) (current.apply rawTarget)).finIdxOf?
              candidate)
          (fun candidate =>
            (signature.generalizedTyVars
              (rawContext.applySubst current) (current.apply rawTarget)).finIdxOf?
              candidate)
          (current.apply rawTarget)).2 varId headFree
      exact (List.finIdxOf?_eq_none_iff.mp closingNone generalized).elim
    · exact mem_generalizedTyVars_not_env generalized
        (List.mem_append_right _ outerFree)

end DM
end TypePM
