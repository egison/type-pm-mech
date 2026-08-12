import TypePM.DamasMilnerWRetired
import TypePM.DamasMilnerWNormalized

/-!
# Capability-inert pending lets in the Damas--Milner W simulation

Every pending DM let boundary is represented by an exactly one-sort context
and target.  Ordinary target-only exact cuts preserve that fact.  This small
invariant supplies the final non-oracle premises of generalization naturality
without coupling them to the protected/retired frame implementation.
-/

namespace TypePM
namespace DM

/-- Every pending let cut is capability-free at the displayed prevailing
substitution. -/
structure PendingLetsCapFree (current : Subst)
    (pending : List PendingLetCut) : Prop where
  contexts : ∀ cut ∈ pending, (cut.context.applySubst current).fcv = []
  targets : ∀ cut ∈ pending, (current.apply cut.target).fcv = []

theorem PendingLetsCapFree.nil (current : Subst) :
    PendingLetsCapFree current [] := by
  constructor <;> simp

/-- Restrict to any retained subset of pending cuts. -/
theorem PendingLetsCapFree.of_subset
    {current : Subst} {larger smaller : List PendingLetCut}
    (free : PendingLetsCapFree current larger)
    (subset : ∀ cut, cut ∈ smaller → cut ∈ larger) :
    PendingLetsCapFree current smaller := by
  exact
    { contexts := fun cut member => free.contexts cut (subset cut member)
      targets := fun cut member => free.targets cut (subset cut member) }

theorem PendingLetsCapFree.cons
    {current : Subst} {pending : List PendingLetCut} {cut : PendingLetCut}
    (older : PendingLetsCapFree current pending)
    (contextCapFree : (cut.context.applySubst current).fcv = [])
    (targetCapFree : (current.apply cut.target).fcv = []) :
    PendingLetsCapFree current (cut :: pending) := by
  constructor
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact contextCapFree
    · exact older.contexts candidate oldMember
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact targetCapFree
    · exact older.targets candidate oldMember

/-- Register a newly completed value whose normalized context and target have
explicit one-sort decodings. -/
theorem PendingLetsCapFree.registerNormalized
    {current : Subst} {pending : List PendingLetCut}
    {residual : SSubst} {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    {rawContext : Context} {rawTarget : Ty}
    (older : PendingLetsCapFree current pending)
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget (rawContext.applySubst current)
      (current.apply rawTarget)) :
    PendingLetsCapFree current
      (PendingLetCut.mk rawContext rawTarget current :: pending) := by
  apply older.cons
  · rw [view.context.normalized_eq, SCtx.emb_fcv]
  · rw [view.target.normalized_eq, STy.emb_fcv]

/-- Assemble the exact stable-cut certificate from solver exactness,
frontier separation, and this invariant's two projections. -/
theorem PendingLetsCapFree.letStableExactPairedCut
    {signature : FrozenSig} {current delta : Subst}
    {pending : List PendingLetCut} {left right : Ty}
    (free : PendingLetsCapFree current pending)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (separated : ∀ cut ∈ pending,
      LetCutConstraintSeparated signature current cut left right) :
    LetStableExactPairedCut signature current pending left right delta :=
  { exact := exact
    leftCapFree := leftCapFree
    rightCapFree := rightCapFree
    separated := separated
    contextsCapFree := free.contexts
    targetsCapFree := free.targets }

/-- A capability-free exact cut preserves capability-inertness of all pending
contexts and targets. -/
theorem PendingLetsCapFree.applyLetStableExactPairedCut
    {signature : FrozenSig} {current delta : Subst}
    {pending : List PendingLetCut} {left right : Ty}
    (free : PendingLetsCapFree current pending)
    (solverCut : LetStableExactPairedCut signature current pending left right
      delta) :
    PendingLetsCapFree (Subst.seq delta current) pending := by
  have capEq : delta.cap = CapSubst.id :=
    TypePM.DM.OriginSafeExactPairedMGU.cap_eq_id_of_constraint_capFree
      solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
  have imagesCapFree : ∀ source, (delta.target source).fcv = [] :=
    TypePM.DM.OriginSafeExactPairedMGU.target_images_capFree_of_constraint_capFree
      solverCut.exact solverCut.leftCapFree solverCut.rightCapFree
  have deltaEq : delta =
      ({ cap := CapSubst.id, target := delta.target } : Subst) := by
    apply PhasedPost.subst_ext
    · exact capEq
    · rfl
  constructor
  · intro cut member
    rw [Context.applySubst_seq, deltaEq,
      Context.fcv_applySubst_targetOnly_eq delta.target imagesCapFree,
      free.contexts cut member]
  · intro cut member
    rw [Subst.seq_apply, deltaEq]
    unfold Subst.apply
    rw [Ty.applyCapability_id]
    exact Ty.fcv_applyTarget_eq_nil_of_capFree _ delta.target
      (free.targets cut member) imagesCapFree

/-- Scheme opening changes only the residual competitor, not the prevailing
substitution or pending cuts. -/
theorem PendingLetsCapFree.extendSchemeOpening
    {current : Subst} {pending : List PendingLetCut}
    (free : PendingLetsCapFree current pending) :
    PendingLetsCapFree current pending := free

/-- Fresh monomorphic lambda allocation leaves the pending cut data and
prevailing substitution unchanged. -/
theorem PendingLetsCapFree.prepareLamBody
    {current : Subst} {pending : List PendingLetCut}
    (free : PendingLetsCapFree current pending) :
    PendingLetsCapFree current pending := free

/-- Fresh application/fix allocation likewise changes only supply and the
residual competitor. -/
theorem PendingLetsCapFree.prepareAppOrFixBody
    {current : Subst} {pending : List PendingLetCut}
    (free : PendingLetsCapFree current pending) :
    PendingLetsCapFree current pending := free

end DM
end TypePM
