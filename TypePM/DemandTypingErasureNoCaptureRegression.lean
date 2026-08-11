import TypePM.DemandTypingErasureNoCapture
import TypePM.DemandTypingErasureSchemeAudit

/-!
# No-capture regressions for scheme erasure

The first audit substitution violates the range-hygiene condition directly.
The second regression starts capture-free and shows that a later
origin-admissible suffix can still capture a scheme free variable.  Hence a
lookup-local fact is insufficient: avoidance has to be preserved through the
future DD state.
-/

namespace TypePM.DemandTypingErasureSchemeAudit

/-- The prefix audit collision violates exactly the capability-range clause. -/
theorem prevailing_not_noCapture :
    ¬ rawScheme.NoCapture prevailing := by
  intro hygiene
  have free : ⟨1⟩ ∈ rawScheme.fcv := by decide
  have bound : ⟨0⟩ ∈ rawScheme.capBinders := by decide
  exact hygiene.capRange ⟨1⟩ free ⟨0⟩ bound (by decide)

/-- At the lookup cut, identity is perfectly capture-free for the raw
scheme. -/
theorem rawScheme_identity_noCapture : rawScheme.NoCapture Subst.id :=
  NamedScheme.NoCapture.id rawScheme

/-- Nevertheless, the later suffix `1 ↦ 0` is admitted after canonical
instantiation: ambient identifiers `0` and `1` are structural, while the
fresh canonical binder `2` remains a rename-only variable. -/
theorem suffixCapture_admissible : DDErasure.AdmissiblePostBetween
    lookupSupply lookupSupply
      (DDLedger.markSchemeInstance beforeLedger inputSupply rawScheme)
      (DDLedger.markSchemeInstance beforeLedger inputSupply rawScheme)
      prevailing := by
  refine
    { supplyExtends := SupplyExtends.refl lookupSupply
      bounded := prevailing_bounded.mono (by
        rw [lookupSupply_shape]
        exact ⟨by decide, by decide⟩)
      refines := DDLedger.RefinesBelow.refl lookupSupply
        (DDLedger.markSchemeInstance beforeLedger inputSupply rawScheme)
      cap := ?_ }
  rintro ⟨varId⟩ below
  rw [lookupSupply_shape] at below
  change varId < 3 at below
  have cases : varId = 0 ∨ varId = 1 ∨ varId = 2 := by omega
  rcases cases with zero | one | two
  · subst varId
    simp [beforeLedger, DDLedger.markSchemeInstance, rawScheme, inputSupply,
      Inference.freshCapImages, CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf]
  · subst varId
    simp [beforeLedger, DDLedger.markSchemeInstance, rawScheme, inputSupply,
      Inference.freshCapImages, CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf]
  · subst varId
    simp [beforeLedger, DDLedger.markSchemeInstance, rawScheme, inputSupply,
      Inference.freshCapImages, CapabilityOriginLedger.setOrigins,
      CapabilityOriginLedger.setOrigin, CapabilityOriginLedger.originOf,
      prevailing, Unification.CapSubst.single]

/-- With identity at the lookup cut, the terminal scheme equation itself is
not the obstruction. -/
theorem suffixCapture_terminalSchemeEquation :
    rawScheme.applySubst (Subst.seq prevailing Subst.id) =
      (rawScheme.applySubst Subst.id).applySubst prevailing := by
  rw [Subst.seq_id_right, NamedScheme.applySubst_id]

/-- The real obstruction is future capture.  The target scheme turns both
occurrences into its one bound identifier, so every value-flow instance gives
them the same variable.  The post-image of the canonical source instance has
distinct capabilities `2` and `0`, and therefore cannot be such an instance. -/
theorem suffixCapture_not_valueFlowInst :
    ¬ (rawScheme.applySubst prevailing).ValueFlowInst
      (prevailing.apply
        (InferenceBase.instantiateNamedScheme inputSupply rawScheme).value) := by
  rintro ⟨C, T, instantiation⟩
  have result := instantiation.result
  simp [rawScheme, prevailing, inputSupply, NamedScheme.applySubst,
    InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] at result
  rcases result with ⟨first, second⟩
  simp [Cap.apply, CapSubst.mask, Unification.CapSubst.single,
    InferenceBase.freshCapSubst] at first second
  have impossible : Cap.var ⟨2⟩ = Cap.var ⟨0⟩ := by
    rw [← first, second]
  exact (by cases impossible)

end TypePM.DemandTypingErasureSchemeAudit
