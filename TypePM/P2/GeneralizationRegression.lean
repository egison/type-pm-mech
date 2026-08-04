import TypePM.P2.SourceGeneralization

/-!
# Ordered generalization regression

This module records a positive case of ordered binder-local instantiation.
A constructor may bind the same numeric capability and target variable
locally: capability substitution is applied first, then the target image is
installed without replaying that capability substitution inside the image.
Let-generalization can therefore specialize the target image to a type
containing the constructor's capability binder.
-/

namespace TypePM.P2.GeneralizationRegression

def collisionCtorScheme : CtorScheme where
  capBinders := [0]
  tyBinders := [0]
  args := []
  result := .matcher (.var 0) (.var 0)

def collisionSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("C", collisionCtorScheme)]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

def sourceTy : Ty := .matcher (.var 1) (.var 1)

def requestedTy : Ty :=
  .matcher (.var 2) (.matcher (.var 0) .int)

def sourceCtorCap : CapSubst :=
  fun varId => if varId = 0 then .var 1 else .var varId

def sourceCtorTarget : TySubst :=
  fun varId => if varId = 0 then .var 1 else .var varId

theorem sourceCtorInstance : collisionCtorScheme.Inst [] sourceTy := by
  refine ⟨sourceCtorCap, sourceCtorTarget, ?_, ?_, rfl, rfl⟩
  · intro varId outside
    change varId ∉ [0] at outside
    simp only [List.mem_singleton] at outside
    simp [sourceCtorCap, outside]
  · intro varId outside
    change varId ∉ [0] at outside
    simp only [List.mem_singleton] at outside
    simp [sourceCtorTarget, outside]

theorem sourceTyping :
    HasTy collisionSignature [] (.ctor "C" []) sourceTy := by
  exact HasTy.ctor (by rfl) sourceCtorInstance ExprsTy.nil

def generalized : Scheme := collisionSignature.generalize [] sourceTy

theorem generalized_shape :
    generalized = ⟨[1], [1], sourceTy⟩ := by
  rfl

def rootCap : CapSubst :=
  fun varId => if varId = 1 then .var 2 else .var varId

def requestedFlowTarget : TySubst :=
  fun varId =>
    if varId = 1 then .matcher (.var 0) .int else .var varId

theorem requestedValueFlow :
    generalized.ValueFlowInst requestedTy := by
  refine ⟨rootCap, requestedFlowTarget, ?_⟩
  refine
    { capSupport := ?_
      tySupport := ?_
      capBinderVariable := ?_
      result := rfl }
  · intro varId outside
    rw [generalized_shape] at outside
    simp only [List.mem_singleton] at outside
    simp [rootCap, outside]
  · intro varId outside
    rw [generalized_shape] at outside
    simp only [List.mem_singleton] at outside
    simp [requestedFlowTarget, outside]
  · intro varId membership
    rw [generalized_shape] at membership
    simp only [List.mem_singleton] at membership
    subst varId
    exact ⟨2, by simp [rootCap]⟩

/-- Let-generalization transports the original derivation to the requested
ordered binder-local instance through the public source endpoint. -/
theorem collision_generalization_succeeds :
    HasTy collisionSignature [] (.ctor "C" []) requestedTy := by
  exact sourceTyping.generalizedValueFlow (by rfl) requestedValueFlow

end TypePM.P2.GeneralizationRegression
