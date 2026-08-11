import TypePM.Source
import TypePM.FreshSupply

/-!
# Fresh supplies and executable instantiation

This module supplies the terminating fresh-variable layer used by two-sorted
inference.  Capability and target counters are independent.  Batch
instantiation maps every quantified binder to a flexible meta at or above the
corresponding incoming counter, advances the counter past every allocated
identifier, and leaves all variables outside the binder lists unchanged.

The executable functions return their substitutions explicitly.  Their
soundness theorems connect the results to `Scheme.InstAt`,
`DualScheme.Inst`, and `CtorScheme.Inst`, including support and the paper's
range-fixed side condition.
-/

namespace TypePM
namespace InferenceBase

/-! ## Batch allocation -/

/-- One plus the greatest identifier in a finite list, or zero when empty. -/
def binderSpan : List Nat → Nat
  | [] => 0
  | varId :: varIds => max (varId + 1) (binderSpan varIds)

/-- Every listed identifier lies strictly below its span. -/
theorem mem_lt_binderSpan :
    ∀ {varIds : List Nat} {varId : Nat},
      varId ∈ varIds → varId < binderSpan varIds
  | [], _, hmem => by
      cases hmem
  | head :: tail, varId, hmem => by
      simp only [List.mem_cons] at hmem
      simp only [binderSpan]
      rcases hmem with heq | htail
      · subst varId
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (mem_lt_binderSpan htail)
          (Nat.le_max_right _ _)

/--
Identity-defaulting capability substitution for one binder batch.

The source binder identifier is used only as an offset inside the fresh region;
the incoming supply must already exceed all surrounding identifiers.
-/
def freshCapSubst
    (next : Nat) (binders : List CapVar) : CapSubst :=
  fun candidate =>
    if candidate ∈ binders then
      .var ⟨next + candidate.id⟩
    else
      .var candidate

/-- Identity-defaulting target substitution for one binder batch. -/
def freshTySubst
    (next : Nat) (binders : List TypePM.TyVar) : TySubst :=
  fun candidate =>
    if candidate ∈ binders then
      .var (next + candidate)
    else
      .var candidate

/-- The substitutions and successor supply allocated for two binder lists. -/
structure FreshAssignment where
  subst : Subst
  supply : FreshSupply

/-- Allocate both binder sorts simultaneously from independent counters. -/
def instantiateBinders
    (supply : FreshSupply)
    (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) : FreshAssignment :=
  { subst :=
      ⟨freshCapSubst supply.nextCap capBinders,
        freshTySubst supply.nextTy tyBinders⟩
    supply :=
      ⟨supply.nextCap + binderSpan (capBinders.map CapVar.id),
        supply.nextTy + binderSpan tyBinders⟩ }

/-- Batch capability allocation changes only quantified binders. -/
theorem freshCapSubst_support
    (next : Nat) (binders : List CapVar) :
    (freshCapSubst next binders).SupportWithin binders := by
  intro candidate hnotmem
  simp [freshCapSubst, hnotmem]

/-- Batch target allocation changes only quantified binders. -/
theorem freshTySubst_support
    (next : Nat) (binders : List TypePM.TyVar) :
    (freshTySubst next binders).SupportWithin binders := by
  intro candidate hnotmem
  simp [freshTySubst, hnotmem]

/-- Every batch target image is itself a flexible target variable. -/
theorem freshTySubst_is_var
    (next : Nat) (binders : List TypePM.TyVar)
    (candidate : TypePM.TyVar) :
    ∃ freshId, freshTySubst next binders candidate = .var freshId := by
  by_cases hmem : candidate ∈ binders
  · exact ⟨next + candidate, by simp [freshTySubst, hmem]⟩
  · exact ⟨candidate, by simp [freshTySubst, hmem]⟩

/-- A freshly allocated capability/target batch is range-fixed. -/
theorem freshSubsts_rangeFixed
    (capNext tyNext : Nat)
    (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (Subst.mk
      (freshCapSubst capNext capBinders)
      (freshTySubst tyNext tyBinders)).RangeFixed := by
  intro candidate
  rcases freshTySubst_is_var tyNext tyBinders candidate with
    ⟨freshId, hfresh⟩
  change
    (freshTySubst tyNext tyBinders candidate).applyCapability
        (freshCapSubst capNext capBinders) =
      freshTySubst tyNext tyBinders candidate
  rw [hfresh]
  rfl

/-- The returned capability substitution has exactly binder support. -/
theorem instantiateBinders_cap_support
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (instantiateBinders supply capBinders tyBinders).subst.cap.SupportWithin
      capBinders :=
  freshCapSubst_support supply.nextCap capBinders

/-- The returned target substitution has exactly binder support. -/
theorem instantiateBinders_ty_support
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (instantiateBinders supply capBinders tyBinders).subst.target.SupportWithin
      tyBinders :=
  freshTySubst_support supply.nextTy tyBinders

/-- The returned substitution pair is range-fixed. -/
theorem instantiateBinders_rangeFixed
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (instantiateBinders supply capBinders tyBinders).subst.RangeFixed :=
  freshSubsts_rangeFixed supply.nextCap supply.nextTy capBinders tyBinders

@[simp] theorem instantiateBinders_nextCap
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (instantiateBinders supply capBinders tyBinders).supply.nextCap =
      supply.nextCap + binderSpan (capBinders.map CapVar.id) :=
  rfl

@[simp] theorem instantiateBinders_nextTy
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) :
    (instantiateBinders supply capBinders tyBinders).supply.nextTy =
      supply.nextTy + binderSpan tyBinders :=
  rfl

/-! ## Distinctness and ambient freshness -/

/-- Distinct bound capability variables receive distinct fresh metas. -/
theorem freshCapSubst_injective_on
    (next : Nat) {binders : List CapVar}
    {left right : CapVar}
    (hleft : left ∈ binders) (hright : right ∈ binders)
    (heq : freshCapSubst next binders left =
      freshCapSubst next binders right) :
    left = right := by
  have hvars :
      Cap.var ⟨next + left.id⟩ = Cap.var ⟨next + right.id⟩ := by
    simpa [freshCapSubst, hleft, hright] using heq
  cases left with
  | mk leftId =>
      cases right with
      | mk rightId =>
          have hadd : next + leftId = next + rightId :=
            CapVar.mk.inj (Cap.var.inj hvars)
          have hid : leftId = rightId := Nat.add_left_cancel hadd
          subst rightId
          rfl

/-- Distinct bound target variables receive distinct fresh metas. -/
theorem freshTySubst_injective_on
    (next : Nat) {binders : List TypePM.TyVar}
    {left right : TypePM.TyVar}
    (hleft : left ∈ binders) (hright : right ∈ binders)
    (heq : freshTySubst next binders left =
      freshTySubst next binders right) :
    left = right := by
  have hvars : Ty.var (next + left) = Ty.var (next + right) := by
    simpa [freshTySubst, hleft, hright] using heq
  exact Nat.add_left_cancel (Ty.var.inj hvars)

/-- Mapping a duplicate-free capability binder list yields distinct metas. -/
theorem freshCapSubst_mapped_nodup
    (next : Nat) {binders : List CapVar}
    (hnodup : binders.Nodup) :
    (binders.map (freshCapSubst next binders)).Nodup := by
  induction binders with
  | nil =>
      exact List.nodup_nil
  | cons head tail ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.map]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨candidate, hcand, heq⟩
        have hsame : candidate = head :=
          freshCapSubst_injective_on next
            (List.mem_cons_of_mem head hcand) (by simp) heq
        subst candidate
        exact hparts.1 hcand
      · have hmap :
            tail.map (freshCapSubst next (head :: tail)) =
              tail.map (freshCapSubst next tail) := by
          apply List.map_congr_left
          intro candidate hcand
          simp [freshCapSubst, hcand]
        rw [hmap]
        exact ih hparts.2

/-- Mapping a duplicate-free target binder list yields distinct metas. -/
theorem freshTySubst_mapped_nodup
    (next : Nat) {binders : List TypePM.TyVar}
    (hnodup : binders.Nodup) :
    (binders.map (freshTySubst next binders)).Nodup := by
  induction binders with
  | nil =>
      exact List.nodup_nil
  | cons head tail ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.map]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨candidate, hcand, heq⟩
        have hsame : candidate = head :=
          freshTySubst_injective_on next
            (List.mem_cons_of_mem head hcand) (by simp) heq
        subst candidate
        exact hparts.1 hcand
      · have hmap :
            tail.map (freshTySubst next (head :: tail)) =
              tail.map (freshTySubst next tail) := by
          apply List.map_congr_left
          intro candidate hcand
          simp [freshTySubst, hcand]
        rw [hmap]
        exact ih hparts.2

/-- Every allocated capability meta lies inside the consumed supply interval. -/
theorem instantiateBinders_cap_bounds
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar)
    {binder : CapVar} (hmem : binder ∈ capBinders) :
    ∃ freshId,
      (instantiateBinders supply capBinders tyBinders).subst.cap binder =
        .var freshId ∧
      supply.nextCap ≤ freshId.id ∧
      freshId.id <
        (instantiateBinders supply capBinders tyBinders).supply.nextCap := by
  refine ⟨⟨supply.nextCap + binder.id⟩, ?_, ?_, ?_⟩
  · simp [instantiateBinders, freshCapSubst, hmem]
  · simp
  · have hspan :
        binder.id < binderSpan (capBinders.map CapVar.id) :=
      mem_lt_binderSpan (List.mem_map.mpr ⟨binder, hmem, rfl⟩)
    change
      supply.nextCap + binder.id <
        supply.nextCap + binderSpan (capBinders.map CapVar.id)
    exact Nat.add_lt_add_left hspan supply.nextCap

/-- Every allocated target meta lies inside the consumed supply interval. -/
theorem instantiateBinders_ty_bounds
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar)
    {binder : TypePM.TyVar} (hmem : binder ∈ tyBinders) :
    ∃ freshId,
      (instantiateBinders supply capBinders tyBinders).subst.target binder =
        .var freshId ∧
      supply.nextTy ≤ freshId ∧
      freshId <
        (instantiateBinders supply capBinders tyBinders).supply.nextTy := by
  refine ⟨supply.nextTy + binder, ?_, ?_, ?_⟩
  · simp [instantiateBinders, freshTySubst, hmem]
  · omega
  · have hspan : binder < binderSpan tyBinders :=
      mem_lt_binderSpan hmem
    change supply.nextTy + binder < supply.nextTy + binderSpan tyBinders
    exact Nat.add_lt_add_left hspan supply.nextTy

/--
Under the incoming lower-bound invariant and binder `Nodup`, capability
binders receive mutually distinct metas fresh for every ambient variable.
-/
theorem instantiateBinders_cap_fresh
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) (ambient : List CapVar)
    (hnodup : capBinders.Nodup)
    (hbelow : CapVarsBelow supply ambient) :
    (capBinders.map
      (instantiateBinders supply capBinders tyBinders).subst.cap).Nodup ∧
    ∀ binder, binder ∈ capBinders →
      ∀ ambientVar, ambientVar ∈ ambient →
        (instantiateBinders supply capBinders tyBinders).subst.cap binder ≠
          .var ambientVar := by
  constructor
  · exact freshCapSubst_mapped_nodup supply.nextCap hnodup
  · intro binder hbinder ambientVar hambient heq
    rcases instantiateBinders_cap_bounds supply capBinders tyBinders hbinder with
      ⟨freshId, hmap, hlower, _⟩
    rw [hmap] at heq
    have hid : freshId = ambientVar := Cap.var.inj heq
    subst freshId
    exact (Nat.not_le_of_lt (hbelow ambientVar hambient)) hlower

/--
Under the incoming lower-bound invariant and binder `Nodup`, target binders
receive mutually distinct metas fresh for every ambient variable.
-/
theorem instantiateBinders_ty_fresh
    (supply : FreshSupply) (capBinders : List CapVar)
    (tyBinders : List TypePM.TyVar) (ambient : List TypePM.TyVar)
    (hnodup : tyBinders.Nodup)
    (hbelow : TyVarsBelow supply ambient) :
    (tyBinders.map
      (instantiateBinders supply capBinders tyBinders).subst.target).Nodup ∧
    ∀ binder, binder ∈ tyBinders →
      ∀ ambientVar, ambientVar ∈ ambient →
        (instantiateBinders supply capBinders tyBinders).subst.target binder ≠
          .var ambientVar := by
  constructor
  · exact freshTySubst_mapped_nodup supply.nextTy hnodup
  · intro binder hbinder ambientVar hambient heq
    rcases instantiateBinders_ty_bounds supply capBinders tyBinders hbinder with
      ⟨freshId, hmap, hlower, _⟩
    rw [hmap] at heq
    have hid : freshId = ambientVar := Ty.var.inj heq
    subst freshId
    exact (Nat.not_le_of_lt (hbelow ambientVar hambient)) hlower

/-! ## Executable scheme instantiation -/

/-- A substitution, instantiated payload, and successor fresh supply. -/
structure InstanceResult (Payload : Type) where
  subst : Subst
  value : Payload
  supply : FreshSupply

/-- Instantiate every binder of an expression scheme simultaneously. -/
def instantiateScheme
    (supply : FreshSupply) (scheme : Scheme) : InstanceResult Ty :=
  let assignment :=
    instantiateBinders supply scheme.capBinders scheme.tyBinders
  { subst := assignment.subst
    value := assignment.subst.apply scheme.body
    supply := assignment.supply }

/-- Instantiate every binder of a pattern-function dual scheme. -/
def instantiateDualScheme
    (supply : FreshSupply) (scheme : DualScheme) :
    InstanceResult (List Dual × Dual) :=
  let assignment :=
    instantiateBinders supply scheme.capBinders scheme.tyBinders
  { subst := assignment.subst
    value :=
      (scheme.args.map
          (Dual.apply assignment.subst.cap assignment.subst.target),
        scheme.result.apply assignment.subst.cap assignment.subst.target)
    supply := assignment.supply }

/-- Instantiate every binder of a constructor or primitive scheme. -/
def instantiateCtorScheme
    (supply : FreshSupply) (scheme : CtorScheme) :
    InstanceResult (List Ty × Ty) :=
  let assignment :=
    instantiateBinders supply scheme.capBinders scheme.tyBinders
  { subst := assignment.subst
    value :=
      (scheme.args.map assignment.subst.apply,
        assignment.subst.apply scheme.result)
    supply := assignment.supply }

/-- Executable expression-scheme instantiation satisfies `Scheme.InstAt`. -/
theorem instantiateScheme_sound
    (supply : FreshSupply) (scheme : Scheme) :
    scheme.InstAt
      (instantiateScheme supply scheme).subst.cap
      (instantiateScheme supply scheme).subst.target
      (instantiateScheme supply scheme).value := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact instantiateBinders_cap_support supply
      scheme.capBinders scheme.tyBinders
  · exact instantiateBinders_ty_support supply
      scheme.capBinders scheme.tyBinders
  · exact instantiateBinders_rangeFixed supply
      scheme.capBinders scheme.tyBinders

/-- Executable dual-scheme instantiation satisfies `DualScheme.Inst`. -/
theorem instantiateDualScheme_sound
    (supply : FreshSupply) (scheme : DualScheme) :
    scheme.Inst
      (instantiateDualScheme supply scheme).value.1
      (instantiateDualScheme supply scheme).value.2 := by
  refine ⟨(instantiateDualScheme supply scheme).subst.cap,
    (instantiateDualScheme supply scheme).subst.target,
    ?_, ?_, rfl, rfl⟩
  · exact instantiateBinders_cap_support supply
      scheme.capBinders scheme.tyBinders
  · exact instantiateBinders_ty_support supply
      scheme.capBinders scheme.tyBinders

/-- Executable constructor-scheme instantiation satisfies `CtorScheme.Inst`. -/
theorem instantiateCtorScheme_sound
    (supply : FreshSupply) (scheme : CtorScheme) :
    scheme.Inst
      (instantiateCtorScheme supply scheme).value.1
      (instantiateCtorScheme supply scheme).value.2 := by
  refine ⟨(instantiateCtorScheme supply scheme).subst.cap,
    (instantiateCtorScheme supply scheme).subst.target,
    ?_, ?_, rfl, rfl⟩
  · exact instantiateBinders_cap_support supply
      scheme.capBinders scheme.tyBinders
  · exact instantiateBinders_ty_support supply
      scheme.capBinders scheme.tyBinders

/-! ## Monomorphic lookup regression -/

/-- Looking up a monomorphic scheme allocates no substitutions. -/
@[simp] theorem instantiateScheme_mono_subst
    (supply : FreshSupply) (target : Ty) :
    (instantiateScheme supply (Scheme.mono target)).subst = Subst.id := by
  rfl

/-- Looking up a monomorphic scheme does not advance either fresh counter. -/
@[simp] theorem instantiateScheme_mono_supply
    (supply : FreshSupply) (target : Ty) :
    (instantiateScheme supply (Scheme.mono target)).supply = supply := by
  cases supply
  rfl

/-- Looking up a monomorphic scheme returns the identical body. -/
@[simp] theorem instantiateScheme_mono_value
    (supply : FreshSupply) (target : Ty) :
    (instantiateScheme supply (Scheme.mono target)).value = target := by
  change
    (instantiateScheme supply (Scheme.mono target)).subst.apply target = target
  rw [instantiateScheme_mono_subst]
  exact Subst.apply_id target

end InferenceBase
end TypePM
