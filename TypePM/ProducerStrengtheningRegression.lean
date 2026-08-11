import TypePM.CertifiedInference

/-!
# Public producer non-strengthening regression

The negative and positive programs share the same constructor consumer.  They
differ only in whether the producer scheme exposes a fresh capability variable
or the concrete capability requested by the consumer.  This fixes the intended
failure cause at the public certified-inference boundary.
-/

namespace TypePM
namespace ProducerStrengtheningRegression

/-- One consumer that requires a concrete list-shaped matcher producer. -/
def protectionSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("consumeProducer", {
    capBinders := []
    tyBinders := []
    args := [.matcher (.con "List" [.any]) .int]
    result := .int })]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

/-- Instantiation exposes a fresh producer capability leaf. -/
def polymorphicProducer : Scheme :=
  Scheme.close [⟨0⟩] [] (.matcher (.var ⟨0⟩) .int)

/-- The control producer already has the capability required by the consumer. -/
def concreteProducer : Scheme :=
  Scheme.mono (.matcher (.con "List" [.any]) .int)

def consumerExpression : Expr :=
  .ctor "consumeProducer" [.var "producer"]

def polymorphicContext : Context :=
  [("producer", polymorphicProducer)]

def concreteContext : Context :=
  [("producer", concreteProducer)]

/-- The public, terminally certified entry point rejects producer strengthening. -/
theorem polymorphicProducer_public_rejected :
    Inference.infer protectionSignature polymorphicContext
      consumerExpression = none := by
  native_decide

def concreteProducerResult : Inference.ExprResult :=
  (Inference.infer protectionSignature concreteContext consumerExpression).get
    (by native_decide)

/-- The otherwise identical program succeeds with a concrete producer. -/
theorem concreteProducer_public_succeeds :
    Inference.infer protectionSignature concreteContext consumerExpression =
      some concreteProducerResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- The consumer's declared result pins the successful public result to `Int`. -/
theorem concreteProducer_result_type :
    concreteProducerResult.resolvedTarget = .int := by
  native_decide

/-- Public success reconstructs the corresponding semantic safety typing. -/
theorem concreteProducer_typed :
    RuntimeTyping protectionSignature
      (Inference.ResolvedContext concreteProducerResult.state.prevailing
        concreteContext)
      consumerExpression concreteProducerResult.resolvedTarget :=
  Inference.infer_success_runtimeTyping concreteProducer_public_succeeds

/-! ## Safe producer renaming

Two independently instantiated constructor results export distinct frozen
capability variables.  Applying the first result to the second requires only
renaming the argument producer variable to the function-domain producer
variable.  This is the positive boundary paired with structural strengthening:
freeze preserves variable shape, not the accidental fresh-variable name. -/

def safeRenameSignature : FrozenSig where
  observability := fun _ => none
  dataCtors :=
    [("makeF", {
        capBinders := [⟨0⟩]
        tyBinders := []
        args := []
        result := .fn (.matcher (.var ⟨0⟩) .int) .int }),
      ("makeM", {
        capBinders := [⟨0⟩]
        tyBinders := []
        args := []
        result := .matcher (.var ⟨0⟩) .int })]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

def safeRenameExpression : Expr :=
  .app (.ctor "makeF" []) (.ctor "makeM" [])

def safeRenameResult : Inference.ExprResult :=
  (Inference.infer safeRenameSignature [] safeRenameExpression).get
    (by native_decide)

/-- A frozen producer may be renamed to another frozen producer variable. -/
theorem safeRename_public_succeeds :
    Inference.infer safeRenameSignature [] safeRenameExpression =
      some safeRenameResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

theorem safeRename_result_type :
    safeRenameResult.resolvedTarget = .int := by
  native_decide

end ProducerStrengtheningRegression
end TypePM
