import TypePM.SourceGeneralization

/-!
# Ordered generalization regression

This module records a positive case of ordered binder-local instantiation.
A constructor may bind the same numeric capability and target variable
locally: capability substitution is applied first, then the target image is
installed without replaying that capability substitution inside the image.
Let-generalization can therefore specialize the target image to a type
containing the constructor's capability binder.
-/

namespace TypePM.GeneralizationRegression

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
    RuntimeTyping collisionSignature [] (.ctor "C" []) sourceTy := by
  exact RuntimeTyping.ctor (by rfl) sourceCtorInstance ExprsTy.nil

def generalized : NamedScheme := collisionSignature.generalize [] sourceTy

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
    RuntimeTyping collisionSignature [] (.ctor "C" []) requestedTy := by
  exact sourceTyping.generalizedValueFlow (by rfl) requestedValueFlow

/-! ## Pattern-function capability defaulting -/

def singletonDualGeneralized : DualScheme :=
  collisionSignature.generalizeDual [] [⟨.var 10, .int⟩] ⟨.var 11, .int⟩

/-- Independent leaf capabilities carry no sharing information and therefore
canonicalize to `Any` instead of becoming vacuous quantifiers. -/
theorem singletonDualGeneralized_shape :
    singletonDualGeneralized =
      { capBinders := []
        tyBinders := []
        args := [⟨.any, .int⟩]
        result := ⟨.any, .int⟩ } := by
  rfl

def sharedDualGeneralized : DualScheme :=
  collisionSignature.generalizeDual [] [⟨.var 20, .int⟩] ⟨.var 20, .int⟩

/-- A capability occurring in both an argument and the result is quantified
once and keeps the same variable at both positions. -/
theorem sharedDualGeneralized_shape :
    sharedDualGeneralized =
      { capBinders := [20]
        tyBinders := []
        args := [⟨.var 20, .int⟩]
        result := ⟨.var 20, .int⟩ } := by
  rfl

def mixedDualGeneralized : DualScheme :=
  collisionSignature.generalizeDual []
    [⟨.var 30, .int⟩, ⟨.var 31, .int⟩] ⟨.var 30, .int⟩

/-- Defaulting is occurrence-sensitive across the complete payload: the
shared variable survives while the independent sibling becomes `Any`. -/
theorem mixedDualGeneralized_shape :
    mixedDualGeneralized =
      { capBinders := [30]
        tyBinders := []
        args := [⟨.var 30, .int⟩, ⟨.any, .int⟩]
        result := ⟨.var 30, .int⟩ } := by
  rfl

def ambientDualContext : NamedContext :=
  [("ambient", NamedScheme.mono (.matcher (.var 40) .int))]

def ambientDualGeneralized : DualScheme :=
  collisionSignature.generalizeDual ambientDualContext
    [⟨.var 40, .int⟩] ⟨.var 41, .int⟩

/-- Ambient capabilities stay free even when they occur only once; only the
non-ambient singleton is defaulted. -/
theorem ambientDualGeneralized_shape :
    ambientDualGeneralized =
      { capBinders := []
        tyBinders := []
        args := [⟨.var 40, .int⟩]
        result := ⟨.any, .int⟩ } := by
  rfl

def signatureAmbientScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := ⟨.var 42, .int⟩

def signatureAmbient : FrozenSig :=
  { collisionSignature with
    patternFuns := [("ambient", signatureAmbientScheme)] }

def signatureAmbientGeneralized : DualScheme :=
  signatureAmbient.generalizeDual [] [] ⟨.var 42, .int⟩

/-- A signature-free capability is ambient just like a context-free one: it
is neither defaulted nor quantified even at one payload occurrence. -/
theorem signatureAmbientGeneralized_shape :
    signatureAmbientGeneralized =
      { capBinders := []
        tyBinders := []
        args := []
        result := ⟨.var 42, .int⟩ } := by
  rfl

def nestedSingletonGeneralized : DualScheme :=
  collisionSignature.generalizeDual []
    [⟨.any, .matcher (.var 50) .int⟩] ⟨.any, .unit⟩

/-- Occurrence counting includes capabilities nested inside target types. -/
theorem nestedSingletonGeneralized_shape :
    nestedSingletonGeneralized =
      { capBinders := []
        tyBinders := []
        args := [⟨.any, .matcher .any .int⟩]
        result := ⟨.any, .unit⟩ } := by
  rfl

def nestedSharedGeneralized : DualScheme :=
  collisionSignature.generalizeDual []
    [⟨.var 51, .matcher (.var 51) .int⟩] ⟨.any, .unit⟩

/-- A capability shared between a dual's outer component and its nested target
remains one quantified variable. -/
theorem nestedSharedGeneralized_shape :
    nestedSharedGeneralized =
      { capBinders := [51]
        tyBinders := []
        args := [⟨.var 51, .matcher (.var 51) .int⟩]
        result := ⟨.any, .unit⟩ } := by
  rfl

end TypePM.GeneralizationRegression
