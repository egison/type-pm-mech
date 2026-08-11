import TypePM.DemandTypingErasureTransport

/-!
# Audit of generalized-scheme transport

This module records the smallest collision showing why the residual scheme
algebra in `DDSynthOrigin.runtimeVar_afterPost_of_admissible` is not implied by
boundedness, solved form, and capability-origin admissibility alone.

The quantified capability identifier `0` is also available as an ambient
identifier.  The prevailing substitution sends free capability `1` to `0`,
which binder-masking scheme application subsequently treats as bound.  A later
admissible post sends ambient `0` back to `1`.  Applying the composite to the
raw scheme and applying the two substitutions successively to schemes then
produce different bodies.
-/

namespace TypePM.DemandTypingErasureSchemeAudit

def rawScheme : NamedScheme :=
  { capBinders := [⟨0⟩]
    tyBinders := []
    body := .prod
      [.matcher (.var ⟨0⟩) .int, .matcher (.var ⟨1⟩) .int] }

def inputSupply : InferenceBase.FreshSupply := ⟨2, 0⟩

def prevailing : Subst :=
  ⟨Unification.CapSubst.single ⟨1⟩ (.var ⟨0⟩), TySubst.id⟩

def post : Subst :=
  ⟨Unification.CapSubst.single ⟨0⟩ (.var ⟨1⟩), TySubst.id⟩

def sourceScheme : NamedScheme := rawScheme.applySubst prevailing

def lookupSupply : InferenceBase.FreshSupply :=
  (InferenceBase.instantiateNamedScheme inputSupply sourceScheme).supply

def beforeLedger : CapabilityOriginLedger :=
  CapabilityOriginLedger.markStructuralFlexible
    (CapabilityOriginLedger.markStructuralFlexible [] ⟨0⟩) ⟨1⟩

def lookupLedger : CapabilityOriginLedger :=
  DDLedger.markSchemeInstance beforeLedger inputSupply sourceScheme

@[simp] theorem sourceScheme_shape : sourceScheme =
    { capBinders := [⟨0⟩]
      tyBinders := []
      body := .prod
        [.matcher (.var ⟨0⟩) .int, .matcher (.var ⟨0⟩) .int] } := by
  decide

@[simp] theorem lookupSupply_shape : lookupSupply = ⟨3, 0⟩ := by
  decide

theorem rawScheme_bounded : rawScheme.BoundedBy inputSupply := by
  constructor
  · intro varId membership
    have equality : varId = ⟨1⟩ := by
      simpa [rawScheme, NamedScheme.fcv, Ty.fcv, Ty.fcvList, Cap.fcv] using
        membership
    subst varId
    decide
  · intro varId membership
    simp [rawScheme, NamedScheme.ftv, Ty.ftv, Ty.ftvList] at membership

theorem inputContext_bounded :
    NamedContext.BoundedBy inputSupply [("f", rawScheme)] := by
  intro entry membership
  simp only [List.mem_singleton] at membership
  subst entry
  exact rawScheme_bounded

theorem prevailing_bounded : prevailing.BoundedBy inputSupply := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    by_cases equal : ⟨1⟩ = varId
    · subst varId
      simp [inputSupply] at above
    · simp [prevailing, Unification.CapSubst.single, equal]
  · intro varId below image imageMem
    by_cases equal : ⟨1⟩ = varId
    · subst varId
      simp [prevailing, Unification.CapSubst.single, Cap.fcv] at imageMem
      subst image
      decide
    · simp [prevailing, Unification.CapSubst.single, equal, Cap.fcv]
        at imageMem
      subst image
      simpa [inputSupply] using below
  · intro varId above
    rfl
  · intro varId below
    exact Ty.BoundedBy.varOf below

theorem prevailing_idempotent : prevailing.Idempotent := by
  unfold Subst.Idempotent prevailing
  intro target
  let C := Unification.CapSubst.single ⟨1⟩ (.var ⟨0⟩)
  have capIdem : C.Idempotent :=
    Unification.capSingle_idempotent (by decide)
  simp only [Subst.apply, Ty.applyTarget_id]
  change (target.applyCapability C).applyCapability C =
    target.applyCapability C
  rw [← Ty.applyCapability_comp]
  congr 1
  funext varId
  simpa [CapSubst.comp, Cap.apply] using capIdem (.var varId)

theorem sourceScheme_bounded : sourceScheme.BoundedBy inputSupply :=
  rawScheme_bounded.applySubst prevailing_bounded

/-- The prefix collision is itself permitted by the current chronological
post invariant: both affected ambient identifiers are structural. -/
theorem prevailing_admissible : DDErasure.AdmissiblePostBetween
    inputSupply inputSupply beforeLedger beforeLedger prevailing := by
  refine
    { supplyExtends := SupplyExtends.refl inputSupply
      bounded := prevailing_bounded
      refines := DDLedger.RefinesBelow.refl inputSupply beforeLedger
      cap := ?_ }
  rintro ⟨varId⟩ below
  change varId < 2 at below
  have cases : varId = 0 ∨ varId = 1 := by omega
  rcases cases with zero | one
  · subst varId
    simp [beforeLedger]
  · subst varId
    simp [beforeLedger]

theorem collision_prefix_stateFactorization : DDErasure.StateFactorization
    inputSupply Subst.id beforeLedger inputSupply prevailing beforeLedger := by
  refine ⟨prevailing, ?_, prevailing_admissible⟩
  rw [Subst.seq_id_right]

theorem post_bounded : post.BoundedBy lookupSupply := by
  rw [lookupSupply_shape]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    by_cases equal : ⟨0⟩ = varId
    · subst varId
      simp at above
    · simp [post, Unification.CapSubst.single, equal]
  · intro varId below image imageMem
    by_cases equal : ⟨0⟩ = varId
    · subst varId
      simp [post, Unification.CapSubst.single, Cap.fcv] at imageMem
      subst image
      decide
    · simp [post, Unification.CapSubst.single, equal, Cap.fcv] at imageMem
      subst image
      simpa using below
  · intro varId above
    rfl
  · intro varId below
    exact Ty.BoundedBy.varOf below

theorem post_idempotent : post.Idempotent := by
  unfold Subst.Idempotent post
  intro target
  let C := Unification.CapSubst.single ⟨0⟩ (.var ⟨1⟩)
  have capIdem : C.Idempotent :=
    Unification.capSingle_idempotent (by decide)
  simp only [Subst.apply, Ty.applyTarget_id]
  change (target.applyCapability C).applyCapability C =
    target.applyCapability C
  rw [← Ty.applyCapability_comp]
  congr 1
  funext varId
  simpa [CapSubst.comp, Cap.apply] using capIdem (.var varId)

/-- All capability identifiers below the lookup output are either structural
or the freshly marked rename-only identifier, so the collision post is origin
admissible at exactly the variable leaf's output cut. -/
theorem post_admissible : DDErasure.AdmissiblePostBetween
    lookupSupply lookupSupply lookupLedger lookupLedger post := by
  refine
    { supplyExtends := SupplyExtends.refl lookupSupply
      bounded := post_bounded
      refines := DDLedger.RefinesBelow.refl lookupSupply lookupLedger
      cap := ?_ }
  rintro ⟨varId⟩ below
  rw [lookupSupply_shape] at below
  change varId < 3 at below
  have cases : varId = 0 ∨ varId = 1 ∨ varId = 2 := by omega
  rcases cases with zero | one | two
  · subst varId
    simp [lookupLedger, beforeLedger, DDLedger.markSchemeInstance,
      sourceScheme, rawScheme, inputSupply, Inference.freshCapImages,
      CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf]
  · subst varId
    simp [lookupLedger, beforeLedger, DDLedger.markSchemeInstance,
      sourceScheme, rawScheme, inputSupply, Inference.freshCapImages,
      CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf]
  · subst varId
    simp [lookupLedger, beforeLedger, DDLedger.markSchemeInstance,
      sourceScheme, rawScheme, inputSupply, Inference.freshCapImages,
      CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf,
      post, Unification.CapSubst.single]

theorem collision_stateFactorization : DDErasure.StateFactorization
    lookupSupply prevailing lookupLedger lookupSupply
      (Subst.seq post prevailing) lookupLedger :=
  ⟨post, rfl, post_admissible⟩

/-- The residual terminal-scheme equation fails although both substitutions
are bounded and solved, and the later post is origin-admissible. -/
theorem terminalSchemeEquation_fails :
    rawScheme.applySubst (Subst.seq post prevailing) ≠
      sourceScheme.applySubst post := by
  decide

end TypePM.DemandTypingErasureSchemeAudit
