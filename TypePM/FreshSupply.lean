import TypePM.Syntax

/-!
# Independent fresh-variable supplies

The two inference sorts use independent lower bounds.  This module is kept
free of source schemes so capture-free scheme opening can allocate fresh
solver metavariables without importing the legacy binder-list machinery.
-/

namespace TypePM
namespace InferenceBase

/-- Independent lower bounds for the next capability and target metas. -/
structure FreshSupply where
  nextCap : Nat
  nextTy : Nat
deriving Repr, DecidableEq

/-- The initial fresh-variable supply. -/
def FreshSupply.empty : FreshSupply :=
  ⟨0, 0⟩

/-- Generate one fresh flexible capability meta. -/
def freshCapMeta (supply : FreshSupply) : Cap × FreshSupply :=
  (.var ⟨supply.nextCap⟩,
    { supply with nextCap := supply.nextCap + 1 })

/-- Generate one fresh flexible target meta. -/
def freshTyMeta (supply : FreshSupply) : Ty × FreshSupply :=
  (.var supply.nextTy,
    { supply with nextTy := supply.nextTy + 1 })

@[simp] theorem freshCapMeta_value (supply : FreshSupply) :
    (freshCapMeta supply).1 = .var ⟨supply.nextCap⟩ :=
  rfl

@[simp] theorem freshCapMeta_nextCap (supply : FreshSupply) :
    (freshCapMeta supply).2.nextCap = supply.nextCap + 1 :=
  rfl

@[simp] theorem freshCapMeta_preserves_nextTy (supply : FreshSupply) :
    (freshCapMeta supply).2.nextTy = supply.nextTy :=
  rfl

@[simp] theorem freshTyMeta_value (supply : FreshSupply) :
    (freshTyMeta supply).1 = .var supply.nextTy :=
  rfl

@[simp] theorem freshTyMeta_nextTy (supply : FreshSupply) :
    (freshTyMeta supply).2.nextTy = supply.nextTy + 1 :=
  rfl

@[simp] theorem freshTyMeta_preserves_nextCap (supply : FreshSupply) :
    (freshTyMeta supply).2.nextCap = supply.nextCap :=
  rfl

/-- All capability identifiers in `ambient` precede the capability supply. -/
def CapVarsBelow (supply : FreshSupply) (ambient : List CapVar) : Prop :=
  ∀ varId, varId ∈ ambient → varId.id < supply.nextCap

/-- All target identifiers in `ambient` precede the target supply. -/
def TyVarsBelow
    (supply : FreshSupply) (ambient : List TypePM.TyVar) : Prop :=
  ∀ varId, varId ∈ ambient → varId < supply.nextTy

end InferenceBase
end TypePM
