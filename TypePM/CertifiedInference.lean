import TypePM.BridgeChecks

/-!
# Certified executable inference

The public entry point combines the raw terminating W traversal with the
finite terminal trace validator.  The validator checks only recorded
terminal instances, alignments, generalization, and matcher evidence;
cross-sort-aware solver replay follows from sequential composition itself.  It
does not invoke or store a source typing judgment.  Consequently successful
public inference carries enough algebraic evidence for reconstruction while
remaining executable.

No completeness or principality claim is made for the terminal validator.
-/

namespace TypePM
namespace Inference

/-- Retain exactly the raw results whose finite trace reconstructs. -/
private def enforceWBridgeResult
    (signature : FrozenSig) (result : ExprResult) : Option ExprResult :=
  if Reconstruction.wBridgeCheck signature result then
    some result
  else
    none

/-- Public executable Algorithm W with terminal certification. -/
def infer
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    Option ExprResult :=
  (inferRaw signature context expression).bind
    (enforceWBridgeResult signature)

/-- Eliminating the terminal filter exposes its exact finite audit. -/
private theorem enforceWBridgeResult_sound
    {signature : FrozenSig} {input output : ExprResult}
    (success : enforceWBridgeResult signature input = some output) :
    input = output ∧
      Reconstruction.wBridgeCheck signature output = true := by
  unfold enforceWBridgeResult at success
  split at success
  · rename_i checked
    have equality := Option.some.inj success
    subst output
    exact ⟨rfl, checked⟩
  · contradiction

/-- Public success contains both the raw W result and its successful audit. -/
private theorem infer_success_raw_and_checked
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    inferRaw signature context expression = some result ∧
      Reconstruction.wBridgeCheck signature result = true := by
  unfold infer at success
  cases rawEq : inferRaw signature context expression with
  | none => simp [rawEq] at success
  | some raw =>
      have guarded : enforceWBridgeResult signature raw =
          some result := by
        simpa [rawEq] using success
      rcases enforceWBridgeResult_sound guarded with ⟨equality, checked⟩
      subst raw
      exact ⟨rfl, checked⟩

/-- Every successful public run preserves all protected producer variables. -/
theorem infer_protected
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    ProtectedProducerTrace result.state :=
  inferRaw_protected (infer_success_raw_and_checked success).1

/-- A successful public run constructs the complete algebraic bridge checked by
the terminal validator. -/
private theorem infer_success_bridge
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    Reconstruction.WBridgeWF signature result.state :=
  Reconstruction.wBridgeCheck_sound
    (infer_success_raw_and_checked success).2

/-- Successful executable inference reconstructs a structured source-typing certificate. -/
theorem infer_success_reconstruct
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    Reconstruction.ExprDeriv signature
      (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  inferRaw_success_reconstruct
    (infer_success_raw_and_checked success).1
    (infer_success_bridge success)

/-- Soundness of executable type inference for the Egison core.

The theorem is stronger than the intended well-formed-input interface: the
public terminal validator fails closed, so no separate caller premise is
needed to eliminate a successful result. -/
theorem infer_success_sound
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    SemanticTyping signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  (infer_success_reconstruct success).toHasTy

/-- Public result type after certified replay. -/
def inferType
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    Option Ty := do
  let result <- infer signature context expression
  pure result.resolvedTarget

/-- Executable success/failure of certified inference. -/
def inferenceSucceeds
    (signature : FrozenSig) (context : Context) (expression : Expr) : Bool :=
  (infer signature context expression).isSome

/-- Recover the exact `some` equation witnessed by an executable `isSome`
check.  Concrete inference regressions share this small elimination lemma. -/
theorem option_eq_some_get_of_isSome {α : Type} (value : Option α)
    (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => simp at present
  | some result => rfl

end Inference
end TypePM
