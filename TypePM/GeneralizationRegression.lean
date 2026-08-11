import TypePM.CoreTyping
import TypePM.PatternFunction
import TypePM.PolyGeneralization
import TypePM.PolyInstantiation

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

/-- Empty environment used to isolate generalization from constructor
declaration details. -/
def generalizationSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := []
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

def generalized : Scheme :=
  { capArity := 1
    tyArity := 1
    body := .matcher (.bound 0) (.bound 0) }

theorem generalized_shape :
    generalized =
      { capArity := 1
        tyArity := 1
        body := .matcher (.bound 0) (.bound 0) } := by
  rfl

def rootCap : CapSubst :=
  fun varId => if varId = 1 then .var 2 else .var varId

def requestedFlowTarget : TySubst :=
  fun varId =>
    if varId = 1 then .matcher (.var 0) .int else .var varId

theorem requestedValueFlow :
    generalized.ValueFlowInst requestedTy := by
  rw [generalized_shape]
  refine ⟨
    { capImage := fun _ => 2
      tyImage := fun _ => .matcher (.var 0) .int }, ?_⟩
  simp [Scheme.openValue, Scheme.instantiate, requestedTy,
    PolyTy.instantiate, PolyCap.instantiate]

def requestedCtorCap : CapSubst :=
  fun varId => if varId = 0 then .var 2 else .var varId

def requestedCtorTarget : TySubst :=
  fun varId =>
    if varId = 0 then .matcher (.var 0) .int else .var varId

theorem requestedCtorInstance :
    collisionCtorScheme.Inst [] requestedTy := by
  refine ⟨requestedCtorCap, requestedCtorTarget, ?_, ?_, rfl, ?_⟩
  · intro varId outside
    change varId ∉ [0] at outside
    simp only [List.mem_singleton] at outside
    simp [requestedCtorCap, outside]
  · intro varId outside
    change varId ∉ [0] at outside
    simp only [List.mem_singleton] at outside
    simp [requestedCtorTarget, outside]
  · simp [collisionCtorScheme, requestedTy, requestedCtorCap,
      requestedCtorTarget, Subst.apply,
      Ty.applyCapability, Ty.applyTarget, Cap.apply]

/-- Let-generalization transports the original derivation to the requested
ordered binder-local instance through the public source endpoint. -/
theorem collision_generalization_succeeds :
    RuntimeTyping collisionSignature [] (.ctor "C" []) requestedTy := by
  exact RuntimeTyping.ctor (by rfl) requestedCtorInstance ExprsTy.nil

/-! ## Pattern-function capability defaulting -/

def singletonDualGeneralized : DualScheme :=
  generalizationSignature.generalizeDual [] [⟨.var 10, .int⟩]
    ⟨.var 11, .int⟩

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
  generalizationSignature.generalizeDual [] [⟨.var 20, .int⟩]
    ⟨.var 20, .int⟩

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
  generalizationSignature.generalizeDual []
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

def ambientDualContext : Context :=
  [("ambient", Scheme.mono (.matcher (.var 40) .int))]

def ambientDualGeneralized : DualScheme :=
  generalizationSignature.generalizeDual ambientDualContext
    [⟨.var 40, .int⟩] ⟨.var 41, .int⟩

/-- Ambient capabilities stay free even when they occur only once; only the
non-ambient singleton is defaulted. -/
theorem ambientDualGeneralized_shape :
    ambientDualGeneralized =
      { capBinders := []
        tyBinders := []
        args := [⟨.var 40, .int⟩]
        result := ⟨.any, .int⟩ } := by
  have distinct : (41 : CapVar) ≠ 40 := by decide
  have reverseDistinct : (40 : CapVar) ≠ 41 := by decide
  have singleton : List.count (41 : CapVar) [40, 41] = 1 := by decide
  have ambientCount : List.count (40 : CapVar) [40, 41] = 1 := by decide
  simp [ambientDualGeneralized, ambientDualContext, generalizationSignature,
    FrozenSig.generalizeDual, FrozenSig.fcv, FrozenSig.ftv, Context.fcv,
    Context.ftv, Scheme.mono, Scheme.fcv, Scheme.ftv, PolyTy.fcv,
    PolyTy.ftv, PolyTy.lift, PolyCap.fcv, PolyCap.lift,
    Dual.fcv, Dual.ftv, Dual.apply, Ty.fcv, Ty.ftv, Cap.fcv, CtorScheme.fcv,
    CtorScheme.ftv, normalizeDualSingletons,
    singletonDefaultSubst, dualSingletonCaps, dualSharedCaps,
    dualCapOccurrences, uniqueVars, Cap.apply, Subst.apply, distinct,
    reverseDistinct,
    singleton, ambientCount,
    Ty.applyCapability, Ty.applyTarget]

def signatureAmbientScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := ⟨.var 42, .int⟩

def signatureAmbient : FrozenSig :=
  { generalizationSignature with
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
  generalizationSignature.generalizeDual []
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
  generalizationSignature.generalizeDual []
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
