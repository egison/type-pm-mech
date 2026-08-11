import TypePM.PolyInstantiation

/-!
# Transport of capture-free expression-scheme openings

An ambient solver substitution acts on the free metavariables of a scheme and
on the result of opening it.  The only extra fact needed to retain the source
calculus's variable-only capability policy is local to the capability images
selected by that opening: each such image must remain a capability variable.
-/

namespace TypePM

namespace Scheme

/-! ## Local post-opening witness -/

/-- The variable images obtained by transporting one declarative opening
through a later solver substitution. -/
structure ValueOpening.Post {scheme : Scheme}
    (opening : scheme.ValueOpening) (substitution : Subst) where
  capImage : Fin scheme.capArity → CapVar
  capEquation : ∀ index,
    substitution.cap (opening.capImage index) = .var (capImage index)

/-- Repackage the transported images as an opening of the substituted scheme.
Target images may be structural and therefore use the complete ordered paired
action. -/
def ValueOpening.Post.toOpening {scheme : Scheme}
    {opening : scheme.ValueOpening} {substitution : Subst}
    (post : opening.Post substitution) :
    (scheme.applyMeta substitution).ValueOpening where
  capImage := post.capImage
  tyImage := fun index => substitution.apply (opening.tyImage index)

end Scheme

/-! ## Structural transport through polymorphic payloads -/

mutual

/-- Instantiating a capability payload after rewriting its free metas agrees
with rewriting the instantiated capability. -/
theorem PolyCap.instantiate_applyMeta
    {capArity : Nat} (substitution : CapSubst)
    (oldImage newImage : Fin capArity → CapVar)
    (imageEquation : ∀ index,
      substitution (oldImage index) = .var (newImage index)) :
    ∀ capability : PolyCap capArity,
      (capability.applyMeta substitution).instantiate
          (fun index => .var (newImage index)) =
        (capability.instantiate
          (fun index => .var (oldImage index))).apply substitution
  | .any => by simp [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply]
  | .mvar varId => by
      simp only [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply]
      exact PolyCap.instantiate_lift
        (fun index => .var (newImage index)) (substitution varId)
  | .bound index => by
      simpa [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply] using
        (imageEquation index).symm
  | .skolem _ => by simp [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply]
  | .con name children => by
      simp only [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply]
      congr 1
      exact PolyCap.instantiate_applyMeta_list substitution oldImage newImage
        imageEquation children
  | .prod components => by
      simp only [PolyCap.applyMeta, PolyCap.instantiate, Cap.apply]
      congr 1
      exact PolyCap.instantiate_applyMeta_list substitution oldImage newImage
        imageEquation components

/-- List form of `PolyCap.instantiate_applyMeta`. -/
theorem PolyCap.instantiate_applyMeta_list
    {capArity : Nat} (substitution : CapSubst)
    (oldImage newImage : Fin capArity → CapVar)
    (imageEquation : ∀ index,
      substitution (oldImage index) = .var (newImage index)) :
    ∀ capabilities : List (PolyCap capArity),
      (capabilities.map (PolyCap.applyMeta substitution)).map
          (PolyCap.instantiate (fun index => .var (newImage index))) =
        Cap.applyList substitution
          (capabilities.map
            (PolyCap.instantiate (fun index => .var (oldImage index))))
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons, Cap.applyList]
      congr
      · exact PolyCap.instantiate_applyMeta substitution oldImage newImage
          imageEquation capability
      · exact PolyCap.instantiate_applyMeta_list substitution oldImage newImage
          imageEquation capabilities

end

mutual

/-- Instantiating a type payload after ambient meta substitution agrees with
applying that substitution to the instantiated ordinary type. -/
theorem PolyTy.instantiate_applyMeta
    {capArity tyArity : Nat} (substitution : Subst)
    (oldCapImage newCapImage : Fin capArity → CapVar)
    (oldTyImage : Fin tyArity → Ty)
    (capEquation : ∀ index,
      substitution.cap (oldCapImage index) = .var (newCapImage index)) :
    ∀ target : PolyTy capArity tyArity,
      (target.applyMeta substitution).instantiate
          (fun index => .var (newCapImage index))
          (fun index => substitution.apply (oldTyImage index)) =
        substitution.apply
          (target.instantiate (fun index => .var (oldCapImage index))
            oldTyImage)
  | .mvar varId => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      exact PolyTy.instantiate_lift
        (fun index => .var (newCapImage index))
        (fun index => substitution.apply (oldTyImage index))
        (substitution.target varId)
  | .bound index => by
      simp [PolyTy.applyMeta, PolyTy.instantiate]
  | .skolem _ => by
      simp [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .unit => by
      simp [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .int => by
      simp [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .bool => by
      simp [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
  | .data name children => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr 1
      exact PolyTy.instantiate_applyMeta_list substitution oldCapImage
        newCapImage oldTyImage capEquation children
  | .prod components => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr 1
      exact PolyTy.instantiate_applyMeta_list substitution oldCapImage
        newCapImage oldTyImage capEquation components
  | .fn domain codomain => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr
      · exact PolyTy.instantiate_applyMeta substitution oldCapImage
          newCapImage oldTyImage capEquation domain
      · exact PolyTy.instantiate_applyMeta substitution oldCapImage
          newCapImage oldTyImage capEquation codomain
  | .matcher capability target => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr
      · exact PolyCap.instantiate_applyMeta substitution.cap oldCapImage
          newCapImage capEquation capability
      · exact PolyTy.instantiate_applyMeta substitution oldCapImage
          newCapImage oldTyImage capEquation target
  | .slot capability target => by
      simp only [PolyTy.applyMeta, PolyTy.instantiate, Subst.apply,
        Ty.applyCapability, Ty.applyTarget]
      congr
      · exact PolyCap.instantiate_applyMeta substitution.cap oldCapImage
          newCapImage capEquation capability
      · exact PolyTy.instantiate_applyMeta substitution oldCapImage
          newCapImage oldTyImage capEquation target

/-- List form of `PolyTy.instantiate_applyMeta`. -/
theorem PolyTy.instantiate_applyMeta_list
    {capArity tyArity : Nat} (substitution : Subst)
    (oldCapImage newCapImage : Fin capArity → CapVar)
    (oldTyImage : Fin tyArity → Ty)
    (capEquation : ∀ index,
      substitution.cap (oldCapImage index) = .var (newCapImage index)) :
    ∀ targets : List (PolyTy capArity tyArity),
      (targets.map (PolyTy.applyMeta substitution)).map
          (PolyTy.instantiate (fun index => .var (newCapImage index))
            (fun index => substitution.apply (oldTyImage index))) =
        Ty.applyTargetList substitution.target
          (Ty.applyCapabilityList substitution.cap
            (targets.map
              (PolyTy.instantiate (fun index => .var (oldCapImage index))
                oldTyImage)))
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons, Ty.applyCapabilityList, Ty.applyTargetList]
      congr
      · exact PolyTy.instantiate_applyMeta substitution oldCapImage
          newCapImage oldTyImage capEquation target
      · exact PolyTy.instantiate_applyMeta_list substitution oldCapImage
          newCapImage oldTyImage capEquation targets

end

namespace Scheme

/-! ## Scheme transport -/

/-- Capture-free opening commutes with ambient substitution.  The post witness
contains exactly the local variable-image equations needed by the capability
part of the result. -/
theorem openValue_applyMeta {scheme : Scheme}
    (substitution : Subst) (opening : scheme.ValueOpening)
    (post : opening.Post substitution) :
    (scheme.applyMeta substitution).openValue post.toOpening =
      substitution.apply (scheme.openValue opening) := by
  exact PolyTy.instantiate_applyMeta substitution opening.capImage
    post.capImage opening.tyImage post.capEquation scheme.body

/-- Declarative value flow is transported to the ambiently substituted scheme
whenever the selected capability images remain variables. -/
theorem ValueFlowInst.transportApplyMeta {scheme : Scheme} {target : Ty}
    (substitution : Subst) (instantiation : scheme.ValueFlowInst target)
    (postOf : ∀ opening : scheme.ValueOpening,
      scheme.openValue opening = target → Nonempty (opening.Post substitution)) :
    (scheme.applyMeta substitution).ValueFlowInst
      (substitution.apply target) := by
  rcases instantiation with ⟨opening, result⟩
  obtain ⟨post⟩ := postOf opening result
  refine ⟨post.toOpening, ?_⟩
  rw [openValue_applyMeta substitution opening post, result]

/-- Pointed form of value-flow transport when the caller already retains the
opening and its result equation. -/
theorem ValueOpening.transportApplyMeta {scheme : Scheme} {target : Ty}
    (substitution : Subst) (opening : scheme.ValueOpening)
    (result : scheme.openValue opening = target)
    (post : opening.Post substitution) :
    (scheme.applyMeta substitution).ValueFlowInst
      (substitution.apply target) := by
  refine ⟨post.toOpening, ?_⟩
  rw [openValue_applyMeta substitution opening post, result]

end Scheme
end TypePM
