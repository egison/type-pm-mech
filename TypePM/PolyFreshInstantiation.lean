import TypePM.FreshSupply
import TypePM.PolyInstantiation

/-!
# Canonical fresh opening of capture-free schemes

Inference allocates one ordinary solver metavariable for each finite binder
position.  This module deliberately exposes no `Subst`: the allocation is a
`PolyScheme.FreshOpening`, and the only result passed to later inference is
the ordinary type computed by opening the scheme body.
-/

namespace TypePM
namespace PolyScheme

/-- Advance both independent supplies past every binder of one scheme. -/
def advanceSupply (supply : InferenceBase.FreshSupply)
    (scheme : PolyScheme) : InferenceBase.FreshSupply :=
  { nextCap := supply.nextCap + scheme.capArity
    nextTy := supply.nextTy + scheme.tyArity }

/-- The canonical fresh assignment maps each finite binder position to the
corresponding offset from the incoming supply. -/
def canonicalFreshOpening (supply : InferenceBase.FreshSupply)
    (scheme : PolyScheme) : scheme.FreshOpening where
  capImage := fun index => ⟨supply.nextCap + index.val⟩
  tyImage := fun index => supply.nextTy + index.val
  capInjective := by
    intro left right equality
    apply Fin.ext
    have identifiers := congrArg CapVar.id equality
    exact Nat.add_left_cancel identifiers
  tyInjective := by
    intro left right equality
    apply Fin.ext
    exact Nat.add_left_cancel equality

/-- The executable result of canonical fresh instantiation. -/
structure FreshResult (scheme : PolyScheme) where
  opening : scheme.FreshOpening
  supply : InferenceBase.FreshSupply

/-- The instantiated value is determined by the recorded opening; it is not
an independently constructible result field. -/
def FreshResult.value {scheme : PolyScheme}
    (result : FreshResult scheme) : Ty :=
  scheme.openValue result.opening.toValueOpening

/-- Allocate all binders, open the body, and return the successor supply. -/
def freshInstantiate (supply : InferenceBase.FreshSupply)
    (scheme : PolyScheme) : FreshResult scheme :=
  let opening := canonicalFreshOpening supply scheme
  { opening := opening
    supply := advanceSupply supply scheme }

/-! ## Exact allocation equations -/

@[simp] theorem canonicalFreshOpening_capImage
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.capArity) :
    (canonicalFreshOpening supply scheme).capImage index =
      ⟨supply.nextCap + index.val⟩ := by
  rfl

@[simp] theorem canonicalFreshOpening_tyImage
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.tyArity) :
    (canonicalFreshOpening supply scheme).tyImage index =
      supply.nextTy + index.val := by
  rfl

theorem canonicalFreshOpening_cap_injective
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    Function.Injective
      (canonicalFreshOpening supply scheme).capImage :=
  (canonicalFreshOpening supply scheme).capInjective

theorem canonicalFreshOpening_ty_injective
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    Function.Injective
      (canonicalFreshOpening supply scheme).tyImage :=
  (canonicalFreshOpening supply scheme).tyInjective

@[simp] theorem freshInstantiate_opening
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    (freshInstantiate supply scheme).opening =
      canonicalFreshOpening supply scheme := by
  rfl

@[simp] theorem freshInstantiate_value
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    (freshInstantiate supply scheme).value =
      scheme.openValue
        (canonicalFreshOpening supply scheme).toValueOpening := by
  rfl

@[simp] theorem freshInstantiate_nextCap
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    (freshInstantiate supply scheme).supply.nextCap =
      supply.nextCap + scheme.capArity := by
  rfl

@[simp] theorem freshInstantiate_nextTy
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme) :
    (freshInstantiate supply scheme).supply.nextTy =
      supply.nextTy + scheme.tyArity := by
  rfl

/-! ## Monomorphic boundary -/

@[simp] theorem freshInstantiate_mono_value
    (supply : InferenceBase.FreshSupply) (target : Ty) :
    (freshInstantiate supply (mono target)).value = target := by
  simp only [freshInstantiate_value, openValue, FreshOpening.toValueOpening,
    mono]
  exact PolyTy.instantiate_lift
    (fun index : Fin 0 => .var
      ((canonicalFreshOpening supply (mono target)).capImage index))
    (fun index : Fin 0 => .var
      ((canonicalFreshOpening supply (mono target)).tyImage index))
    target

@[simp] theorem freshInstantiate_mono_supply
    (supply : InferenceBase.FreshSupply) (target : Ty) :
    (freshInstantiate supply (mono target)).supply = supply := by
  cases supply
  simp [freshInstantiate, advanceSupply, mono]

/-! ## Allocation bounds and ambient freshness -/

theorem canonicalFreshOpening_cap_lower
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.capArity) :
    supply.nextCap ≤
      ((canonicalFreshOpening supply scheme).capImage index).id := by
  simp

theorem canonicalFreshOpening_cap_upper
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.capArity) :
    ((canonicalFreshOpening supply scheme).capImage index).id <
      (freshInstantiate supply scheme).supply.nextCap := by
  simp only [canonicalFreshOpening_capImage, freshInstantiate_nextCap]
  exact Nat.add_lt_add_left index.isLt supply.nextCap

theorem canonicalFreshOpening_ty_lower
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.tyArity) :
    supply.nextTy ≤
      (canonicalFreshOpening supply scheme).tyImage index := by
  simp

theorem canonicalFreshOpening_ty_upper
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (index : Fin scheme.tyArity) :
    (canonicalFreshOpening supply scheme).tyImage index <
      (freshInstantiate supply scheme).supply.nextTy := by
  simp only [canonicalFreshOpening_tyImage, freshInstantiate_nextTy]
  exact Nat.add_lt_add_left index.isLt supply.nextTy

/-- A supply above every reserved identifier makes the canonical allocation
fresh for that ambient scope. -/
theorem canonicalFreshOpening_freshFor
    (supply : InferenceBase.FreshSupply) (scheme : PolyScheme)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (capsBelow : InferenceBase.CapVarsBelow supply reservedCaps)
    (tysBelow : InferenceBase.TyVarsBelow supply reservedTys) :
    FreshFor (canonicalFreshOpening supply scheme)
      reservedCaps reservedTys := by
  constructor
  · intro index membership
    exact (Nat.not_lt_of_ge
      (canonicalFreshOpening_cap_lower supply scheme index))
      (capsBelow _ membership)
  · intro index membership
    exact (Nat.not_lt_of_ge
      (canonicalFreshOpening_ty_lower supply scheme index))
      (tysBelow _ membership)

end PolyScheme
end TypePM
