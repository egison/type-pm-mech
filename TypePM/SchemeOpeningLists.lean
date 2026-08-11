import TypePM.PolyFreshInstantiation

/-!
# Finite image lists for capture-free scheme openings

Trace and ledger code consume finite lists, while the canonical scheme
opening is represented by functions out of `Fin`.  These projections preserve
the positional allocation order and do not reintroduce binder names.
-/

namespace TypePM

namespace Scheme

/-- Capability images in finite binder-position order. -/
def FreshOpening.capImages {scheme : Scheme}
    (opening : scheme.FreshOpening) : List CapVar :=
  List.ofFn opening.capImage

/-- Target images in finite binder-position order. -/
def FreshOpening.tyImages {scheme : Scheme}
    (opening : scheme.FreshOpening) : List TypePM.TyVar :=
  List.ofFn opening.tyImage

@[simp] theorem FreshOpening.capImages_length {scheme : Scheme}
    (opening : scheme.FreshOpening) :
    opening.capImages.length = scheme.capArity := by
  simp [FreshOpening.capImages]

@[simp] theorem FreshOpening.tyImages_length {scheme : Scheme}
    (opening : scheme.FreshOpening) :
    opening.tyImages.length = scheme.tyArity := by
  simp [FreshOpening.tyImages]

private theorem nodup_ofFn_of_injective {alpha : Type} {n : Nat}
    (f : Fin n → alpha) (injective : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro membership
        rw [List.mem_ofFn] at membership
        obtain ⟨index, equality⟩ := membership
        have impossible : index.succ = (0 : Fin (n + 1)) :=
          injective equality
        have impossibleValue := congrArg Fin.val impossible
        simp at impossibleValue
      · exact ih (fun index => f index.succ) (fun left right equality =>
          Fin.succ_inj.mp (injective equality))

theorem FreshOpening.capImages_nodup {scheme : Scheme}
    (opening : scheme.FreshOpening) : opening.capImages.Nodup := by
  exact nodup_ofFn_of_injective opening.capImage opening.capInjective

theorem FreshOpening.tyImages_nodup {scheme : Scheme}
    (opening : scheme.FreshOpening) : opening.tyImages.Nodup := by
  exact nodup_ofFn_of_injective opening.tyImage opening.tyInjective

/-- Canonical capability images allocated for one scheme instance. -/
def canonicalCapImages (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) : List CapVar :=
  (canonicalFreshOpening supply scheme).capImages

/-- Canonical target images allocated for one scheme instance. -/
def canonicalTyImages (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) : List TypePM.TyVar :=
  (canonicalFreshOpening supply scheme).tyImages

@[simp] theorem canonicalCapImages_length
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    (canonicalCapImages supply scheme).length = scheme.capArity := by
  simp [canonicalCapImages]

@[simp] theorem canonicalTyImages_length
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    (canonicalTyImages supply scheme).length = scheme.tyArity := by
  simp [canonicalTyImages]

theorem canonicalCapImages_nodup
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    (canonicalCapImages supply scheme).Nodup :=
  (canonicalFreshOpening supply scheme).capImages_nodup

theorem canonicalTyImages_nodup
    (supply : InferenceBase.FreshSupply) (scheme : Scheme) :
    (canonicalTyImages supply scheme).Nodup :=
  (canonicalFreshOpening supply scheme).tyImages_nodup

/-- Every canonical capability image lies in the consumed supply interval. -/
theorem mem_canonicalCapImages_bounds
    {supply : InferenceBase.FreshSupply} {scheme : Scheme} {image : CapVar}
    (membership : image ∈ canonicalCapImages supply scheme) :
    supply.nextCap ≤ image.id ∧
      image.id < (freshInstantiate supply scheme).supply.nextCap := by
  rw [canonicalCapImages, FreshOpening.capImages, List.mem_ofFn] at membership
  obtain ⟨index, equality⟩ := membership
  rw [← equality]
  exact ⟨canonicalFreshOpening_cap_lower supply scheme index,
    canonicalFreshOpening_cap_upper supply scheme index⟩

/-- Every canonical target image lies in the consumed supply interval. -/
theorem mem_canonicalTyImages_bounds
    {supply : InferenceBase.FreshSupply} {scheme : Scheme}
    {image : TypePM.TyVar}
    (membership : image ∈ canonicalTyImages supply scheme) :
    supply.nextTy ≤ image ∧
      image < (freshInstantiate supply scheme).supply.nextTy := by
  rw [canonicalTyImages, FreshOpening.tyImages, List.mem_ofFn] at membership
  obtain ⟨index, equality⟩ := membership
  rw [← equality]
  exact ⟨canonicalFreshOpening_ty_lower supply scheme index,
    canonicalFreshOpening_ty_upper supply scheme index⟩

end Scheme
end TypePM
