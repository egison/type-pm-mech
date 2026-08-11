import Std

/-!
# Capability and target syntax

This file defines the two-sorted type syntax used by the matcher
foundation.  Structural capabilities and ordinary target types have distinct
variables and binders.
-/

namespace TypePM

/-- Ordinary target-type variables are natural-number names. -/
abbrev TyVar := Nat

/--
Capability variables are nominally distinct from ordinary type variables.

The wrapper makes the separation hold at Lean's type level as well as at the
AST-constructor level; a capability variable cannot be passed accidentally to
an ordinary target substitution.
-/
structure CapVar where
  id : Nat
deriving Repr, DecidableEq

instance : BEq CapVar where
  beq left right := decide (left = right)

instance : LawfulBEq CapVar where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp

instance (n : Nat) : OfNat CapVar n where
  ofNat := ⟨n⟩

/-- Structural capabilities carried by matcher producers and consumer slots. -/
inductive Cap where
  /-- Minimal consumer demand.  It is rigid for symmetric equality and
  accepts every producer only in the producer-to-consumer relation. -/
  | any
  | var    : CapVar → Cap
  | skolem : Nat → Cap
  | con    : String → List Cap → Cap
  | prod   : List Cap → Cap
deriving Repr

mutual

/-- Executable structural equality for capabilities. -/
def Cap.eqb : Cap → Cap → Bool
  | .any,         .any          => true
  | .var a,       .var b        => a == b
  | .skolem a,    .skolem b     => a == b
  | .con n caps,  .con m caps'  => n == m && Cap.eqbList caps caps'
  | .prod caps,   .prod caps'   => Cap.eqbList caps caps'
  | _,            _             => false

/-- Executable structural equality for capability lists. -/
def Cap.eqbList : List Cap → List Cap → Bool
  | [],          []            => true
  | cap :: caps, cap' :: caps' => Cap.eqb cap cap' && Cap.eqbList caps caps'
  | _,           _             => false

end

mutual

theorem Cap.eqb_eq_true : ∀ c c', Cap.eqb c c' = true ↔ c = c'
  | .any, c' => by
      cases c' <;> simp [Cap.eqb]
  | .var a, c' => by
      cases c' <;> simp [Cap.eqb]
  | .skolem a, c' => by
      cases c' <;> simp [Cap.eqb]
  | .con n caps, c' => by
      cases c' <;> simp [Cap.eqb, Cap.eqbList_eq_true]
  | .prod caps, c' => by
      cases c' <;> simp [Cap.eqb, Cap.eqbList_eq_true]

theorem Cap.eqbList_eq_true :
    ∀ caps caps', Cap.eqbList caps caps' = true ↔ caps = caps'
  | [], caps' => by
      cases caps' <;> simp [Cap.eqbList]
  | cap :: caps, caps' => by
      cases caps' <;>
        simp [Cap.eqbList, Cap.eqb_eq_true, Cap.eqbList_eq_true]

end

instance : BEq Cap :=
  ⟨Cap.eqb⟩

instance : LawfulBEq Cap where
  eq_of_beq h := (Cap.eqb_eq_true _ _).mp h
  rfl := (Cap.eqb_eq_true _ _).mpr rfl

instance : DecidableEq Cap :=
  instDecidableEqOfLawfulBEq

/-- Types with separate capability and target indices on matchers. -/
inductive Ty where
  | var     : TypePM.TyVar → Ty
  | skolem  : Nat → Ty
  | unit
  | int
  | bool
  | data    : String → List Ty → Ty
  | prod    : List Ty → Ty
  | fn      : Ty → Ty → Ty
  | matcher : Cap → Ty → Ty
  | slot    : Cap → Ty → Ty
deriving Repr

mutual

/-- Executable structural equality for types. -/
def Ty.eqb : Ty → Ty → Bool
  | .var a,         .var b          => a == b
  | .skolem a,      .skolem b       => a == b
  | .unit,          .unit           => true
  | .int,           .int            => true
  | .bool,          .bool           => true
  | .data n tys,    .data m tys'    => n == m && Ty.eqbList tys tys'
  | .prod tys,      .prod tys'      => Ty.eqbList tys tys'
  | .fn dom cod,    .fn dom' cod'   => Ty.eqb dom dom' && Ty.eqb cod cod'
  | .matcher c τ,   .matcher c' τ'  => Cap.eqb c c' && Ty.eqb τ τ'
  | .slot c τ,      .slot c' τ'     => Cap.eqb c c' && Ty.eqb τ τ'
  | _,              _               => false

/-- Executable structural equality for type lists. -/
def Ty.eqbList : List Ty → List Ty → Bool
  | [],      []          => true
  | τ :: tys, τ' :: tys' => Ty.eqb τ τ' && Ty.eqbList tys tys'
  | _,       _           => false

end

mutual

theorem Ty.eqb_eq_true : ∀ τ τ', Ty.eqb τ τ' = true ↔ τ = τ'
  | .var a, τ' => by
      cases τ' <;> simp [Ty.eqb]
  | .skolem a, τ' => by
      cases τ' <;> simp [Ty.eqb]
  | .unit, τ' => by
      cases τ' <;> simp [Ty.eqb]
  | .int, τ' => by
      cases τ' <;> simp [Ty.eqb]
  | .bool, τ' => by
      cases τ' <;> simp [Ty.eqb]
  | .data n tys, τ' => by
      cases τ' <;> simp [Ty.eqb, Ty.eqbList_eq_true]
  | .prod tys, τ' => by
      cases τ' <;> simp [Ty.eqb, Ty.eqbList_eq_true]
  | .fn dom cod, τ' => by
      cases τ' <;> simp [Ty.eqb, Ty.eqb_eq_true]
  | .matcher c τ, τ' => by
      cases τ' <;> simp [Ty.eqb, Cap.eqb_eq_true, Ty.eqb_eq_true]
  | .slot c τ, τ' => by
      cases τ' <;> simp [Ty.eqb, Cap.eqb_eq_true, Ty.eqb_eq_true]

theorem Ty.eqbList_eq_true :
    ∀ tys tys', Ty.eqbList tys tys' = true ↔ tys = tys'
  | [], tys' => by
      cases tys' <;> simp [Ty.eqbList]
  | τ :: tys, tys' => by
      cases tys' <;>
        simp [Ty.eqbList, Ty.eqb_eq_true, Ty.eqbList_eq_true]

end

instance : BEq Ty :=
  ⟨Ty.eqb⟩

instance : LawfulBEq Ty where
  eq_of_beq h := (Ty.eqb_eq_true _ _).mp h
  rfl := (Ty.eqb_eq_true _ _).mpr rfl

instance : DecidableEq Ty :=
  instDecidableEqOfLawfulBEq

/-- The ordinary list type used by matcher decomposition results. -/
def Ty.listT (τ : Ty) : Ty :=
  .data "List" [τ]

/-! ## Capture-free scheme payload syntax

Runtime and solver types contain metavariables only.  NamedScheme payloads use a
separate syntax whose bound variables are finite de Bruijn indices.  Thus a
bound variable cannot be passed to a unification substitution, and every
payload is already in a canonical alpha-normal form. -/

/-- Capabilities inside a scheme with `capArity` bound capability variables. -/
inductive PolyCap (capArity : Nat) where
  | any
  | mvar    : CapVar → PolyCap capArity
  | bound   : Fin capArity → PolyCap capArity
  | skolem  : Nat → PolyCap capArity
  | con     : String → List (PolyCap capArity) → PolyCap capArity
  | prod    : List (PolyCap capArity) → PolyCap capArity
deriving Repr

/-- Types inside a scheme with separate capability and target binder arities. -/
inductive PolyTy (capArity tyArity : Nat) where
  | mvar    : TypePM.TyVar → PolyTy capArity tyArity
  | bound   : Fin tyArity → PolyTy capArity tyArity
  | skolem  : Nat → PolyTy capArity tyArity
  | unit
  | int
  | bool
  | data    : String → List (PolyTy capArity tyArity) →
      PolyTy capArity tyArity
  | prod    : List (PolyTy capArity tyArity) → PolyTy capArity tyArity
  | fn      : PolyTy capArity tyArity → PolyTy capArity tyArity →
      PolyTy capArity tyArity
  | matcher : PolyCap capArity → PolyTy capArity tyArity →
      PolyTy capArity tyArity
  | slot    : PolyCap capArity → PolyTy capArity tyArity →
      PolyTy capArity tyArity
deriving Repr

/-- Type schemes quantify capability and ordinary type variables separately. -/
structure NamedScheme where
  capBinders : List CapVar
  tyBinders  : List TypePM.TyVar
  body       : Ty
deriving Repr, DecidableEq, BEq

/-- A monomorphic scheme. -/
def NamedScheme.mono (τ : Ty) : NamedScheme :=
  ⟨[], [], τ⟩

end TypePM
