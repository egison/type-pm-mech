import TypePM.PolyScheme

/-!
# Declarative opening of capture-free expression schemes

This module separates scheme-local opening assignments from ordinary solver
substitutions.  Capability binders have variable-only images by construction,
while target binders may be opened by arbitrary ordinary types.  The stronger
fresh opening used by inference records injective variable assignments; its
ambient freshness condition is kept as a separate predicate.
-/

namespace TypePM

/-! ## Opening lifted monotypes -/

mutual

/-- Opening cannot change an ordinary capability embedded in polymorphic
syntax, because `lift` contains no bound nodes. -/
theorem PolyCap.instantiate_lift {capArity : Nat}
    (openCap : Fin capArity → Cap) : ∀ capability : Cap,
    (PolyCap.lift capability).instantiate openCap = capability
  | .any => by simp [PolyCap.lift, PolyCap.instantiate]
  | .var _ => by simp [PolyCap.lift, PolyCap.instantiate]
  | .skolem _ => by simp [PolyCap.lift, PolyCap.instantiate]
  | .con name children => by
      simp only [PolyCap.lift, PolyCap.instantiate]
      congr 1
      exact PolyCap.instantiate_lift_list openCap children
  | .prod components => by
      simp only [PolyCap.lift, PolyCap.instantiate]
      congr 1
      exact PolyCap.instantiate_lift_list openCap components

/-- List form of `PolyCap.instantiate_lift`. -/
theorem PolyCap.instantiate_lift_list {capArity : Nat}
    (openCap : Fin capArity → Cap) : ∀ capabilities : List Cap,
    (capabilities.map PolyCap.lift).map
        (PolyCap.instantiate openCap) = capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons]
      rw [PolyCap.instantiate_lift openCap capability,
        PolyCap.instantiate_lift_list openCap capabilities]

end

mutual

/-- Opening cannot change an ordinary type embedded in polymorphic syntax,
independently of the chosen assignments. -/
theorem PolyTy.instantiate_lift {capArity tyArity : Nat}
    (openCap : Fin capArity → Cap) (openTy : Fin tyArity → Ty) :
    ∀ target : Ty,
      (PolyTy.lift target).instantiate openCap openTy = target
  | .var _ => by simp [PolyTy.lift, PolyTy.instantiate]
  | .skolem _ => by simp [PolyTy.lift, PolyTy.instantiate]
  | .unit => by simp [PolyTy.lift, PolyTy.instantiate]
  | .int => by simp [PolyTy.lift, PolyTy.instantiate]
  | .bool => by simp [PolyTy.lift, PolyTy.instantiate]
  | .data name children => by
      simp only [PolyTy.lift, PolyTy.instantiate]
      congr 1
      exact PolyTy.instantiate_lift_list openCap openTy children
  | .prod components => by
      simp only [PolyTy.lift, PolyTy.instantiate]
      congr 1
      exact PolyTy.instantiate_lift_list openCap openTy components
  | .fn domain codomain => by
      simp only [PolyTy.lift, PolyTy.instantiate]
      rw [PolyTy.instantiate_lift openCap openTy domain,
        PolyTy.instantiate_lift openCap openTy codomain]
  | .matcher capability target => by
      simp only [PolyTy.lift, PolyTy.instantiate]
      rw [PolyCap.instantiate_lift openCap capability,
        PolyTy.instantiate_lift openCap openTy target]
  | .slot capability target => by
      simp only [PolyTy.lift, PolyTy.instantiate]
      rw [PolyCap.instantiate_lift openCap capability,
        PolyTy.instantiate_lift openCap openTy target]

/-- List form of `PolyTy.instantiate_lift`. -/
theorem PolyTy.instantiate_lift_list {capArity tyArity : Nat}
    (openCap : Fin capArity → Cap) (openTy : Fin tyArity → Ty) :
    ∀ targets : List Ty,
      (targets.map PolyTy.lift).map
          (PolyTy.instantiate openCap openTy) = targets
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons]
      rw [PolyTy.instantiate_lift openCap openTy target,
        PolyTy.instantiate_lift_list openCap openTy targets]

end

namespace PolyScheme

/-! ## Declarative value-flow opening -/

/-- A declarative expression-scheme opening.

The codomain of `capImage` makes the source calculus's variable-only
capability policy structural: a capability binder cannot be opened directly
by a constructor or product capability.  Target binders retain ordinary
structural specialization. -/
structure ValueOpening (scheme : PolyScheme) where
  capImage : Fin scheme.capArity → CapVar
  tyImage : Fin scheme.tyArity → Ty

/-- Open a scheme using a declarative variable-only assignment. -/
def openValue (scheme : PolyScheme) (opening : scheme.ValueOpening) : Ty :=
  scheme.instantiate (fun index => .var (opening.capImage index))
    opening.tyImage

/-- Declarative value flow used by expression-variable lookup. -/
def ValueFlowInst (scheme : PolyScheme) (target : Ty) : Prop :=
  ∃ opening : scheme.ValueOpening, scheme.openValue opening = target

/-! ## Fresh inference opening -/

/-- A fresh variable assignment for both binder sorts.

The finite domains are the scheme's binder arities, so no binder lists or
support predicates are needed.  Injectivity records pairwise distinct
allocation independently of freshness for a particular ambient scope. -/
structure FreshOpening (scheme : PolyScheme) where
  capImage : Fin scheme.capArity → CapVar
  tyImage : Fin scheme.tyArity → TypePM.TyVar
  capInjective : Function.Injective capImage
  tyInjective : Function.Injective tyImage

/-- Forget fresh-allocation facts at the declarative boundary. -/
def FreshOpening.toValueOpening {scheme : PolyScheme}
    (opening : scheme.FreshOpening) : scheme.ValueOpening where
  capImage := opening.capImage
  tyImage := fun index => .var (opening.tyImage index)

/-- A fresh opening avoids the variables reserved by one ambient scope. -/
structure FreshFor {scheme : PolyScheme} (opening : scheme.FreshOpening)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar) : Prop where
  capFresh : ∀ index, opening.capImage index ∉ reservedCaps
  tyFresh : ∀ index, opening.tyImage index ∉ reservedTys

/-! ## Declarative boundary laws -/

/-- Every monomorphic scheme has its declared type as a value-flow instance. -/
theorem mono_valueFlowInst (target : Ty) :
    (mono target).ValueFlowInst target := by
  let opening : (mono target).ValueOpening :=
    { capImage := fun index => Fin.elim0 index
      tyImage := fun index => Fin.elim0 index }
  refine ⟨opening, ?_⟩
  exact PolyTy.instantiate_lift
    (fun index : Fin (mono target).capArity => .var (opening.capImage index))
    opening.tyImage target

/-- A monomorphic scheme has no opening choice, so every value-flow instance
is its declared type. -/
theorem ValueFlowInst.mono_eq {declared actual : Ty}
    (instantiation : (mono declared).ValueFlowInst actual) :
    actual = declared := by
  rcases instantiation with ⟨opening, result⟩
  rw [← result]
  exact PolyTy.instantiate_lift
    (fun index : Fin (mono declared).capArity =>
      .var (opening.capImage index)) opening.tyImage declared

/-- Every fresh opening is already a safe declarative value-flow instance of
its computed opened type. -/
theorem FreshOpening.toValueFlowInst {scheme : PolyScheme}
    (opening : scheme.FreshOpening) :
    scheme.ValueFlowInst (scheme.openValue opening.toValueOpening) := by
  exact ⟨opening.toValueOpening, rfl⟩

end PolyScheme
end TypePM
