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

The terminal validator alone has no unconstrained completeness claim.  The
separate DD acceptance-completeness proof establishes that traces reconstructed
from terminal-audited `DDTyping` derivations pass this validator.  No
principality claim is made here.
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

/-- A successful finite terminal audit is sufficient for the public result
filter.  Completeness uses this direction only after reconstructing every
validator condition from the DD derivation and the raw traversal. -/
theorem enforceWBridgeResult_complete
    {signature : FrozenSig} {result : ExprResult}
    (checked : Reconstruction.wBridgeCheck signature result = true) :
    enforceWBridgeResult signature result = some result := by
  simp [enforceWBridgeResult, checked]

/-- Compose raw traversal acceptance with terminal-validator acceptance.
This is the final executable step of inference completeness; all semantic
work remains in the two premises constructed internally by that proof. -/
theorem infer_complete_of_raw_and_checked
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (raw : inferRaw signature context expression = some result)
    (checked : Reconstruction.wBridgeCheck signature result = true) :
    infer signature context expression = some result := by
  simp [infer, raw, enforceWBridgeResult_complete checked]

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

/-- Public inference success exposes the successful raw traversal needed by
the direct `infer -> DDTyping` reconstruction.  The terminal bridge remains a
separate, internal audit; reconstructing DD follows the traversal itself and
therefore needs no runtime-typing oracle. -/
theorem infer_success_inferRaw
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    inferRaw signature context expression = some result :=
  (infer_success_raw_and_checked success).1

/-- Public success exposes the exact fuelled traversal at the canonical
initial state.  The producer-protection filter never changes the result. -/
theorem infer_success_inferExprFuel
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    inferExprFuel (inferenceFuel expression) signature context [] [] expression
      (initialState signature context) = some result := by
  have rawSuccess := infer_success_inferRaw success
  unfold inferRaw at rawSuccess
  cases core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) with
  | none => simp [core] at rawSuccess
  | some raw =>
      have guarded : enforceProtectedResult raw = some result := by
        simpa [core] using rawSuccess
      have equality := (enforceProtectedResult_sound guarded).1
      subst raw
      rfl

/-- Every successful public run preserves all protected producer variables. -/
theorem infer_protected
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    ProtectedProducerTrace result.state :=
  inferRaw_protected (infer_success_inferRaw success)

/-- A successful public run constructs the complete algebraic bridge checked by
the terminal validator.  This remains an internal proof certificate rather
than an additional caller premise. -/
theorem infer_success_wBridgeWF
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
    (infer_success_wBridgeWF success)

/-- State erasure for a successful executable inference run.

The theorem is stronger than the intended well-formed-input interface: the
public terminal validator fails closed, so no separate caller premise is
needed to construct the internal runtime certificate. -/
theorem infer_success_runtimeTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : infer signature context expression = some result) :
    RuntimeTyping signature (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  (infer_success_reconstruct success).toRuntimeTyping

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
