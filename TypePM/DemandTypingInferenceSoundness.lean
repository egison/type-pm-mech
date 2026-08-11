import TypePM.DemandTypingOrigin

/-!
# Executable traversal to demand-directed typing

This module starts the direct soundness proof from successful executable
traversals to the public demand-directed judgment.  The intermediate
`DDSynthRun` certificate deliberately retains only the pieces of `InferState`
that occur in `DDSynth` and `DDSynthOrigin`: the fresh supply, prevailing
substitution, and capability-origin ledger.  Trace events remain evidence for
constructing the certificate, rather than becoming an additional premise of
source typing.

The first slice covers the two expression leaves whose executable traversal
performs no solve.  Its shape is the induction invariant required by the
remaining expression constructors: the executable raw target is preserved,
and the output indices of the DD derivation are exactly the output state of
the run.
-/

namespace TypePM
namespace Inference

/-- The DD certificate reconstructed from one successful executable
expression traversal.  This is an internal induction package for proving
`infer` sound with respect to `DDTyping`; it is not a second typing judgment. -/
def DDSynthRun (signature : FrozenSig) (context : Context)
    (expression : Expr) (initial : InferState) (result : ExprResult) : Prop :=
  ∃ rawTarget,
    ∃ derived : DDSynth signature initial.supply initial.prevailing context
        expression rawTarget result.state.supply result.state.prevailing,
      result.target = rawTarget ∧
        DDSynthOrigin signature derived initial.capabilityOrigins
          result.state.capabilityOrigins

/-- A reconstructed run from the executable initial state is already a
public `DDTyping` derivation at the run's resolved result type. -/
theorem DDSynthRun.toDDTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (run : DDSynthRun signature context expression
      (initialState signature context) result) :
    DDTyping signature context expression result.resolvedTarget := by
  rcases run with ⟨rawTarget, derived, targetEq, origin⟩
  change DDSynth signature (initialSupply signature context) Subst.id context
    expression rawTarget result.state.supply result.state.prevailing at derived
  change DDSynthOrigin signature derived []
    result.state.capabilityOrigins at origin
  refine ⟨rawTarget, result.state.supply, result.state.prevailing, ?_,
    result.state.capabilityOrigins, ?_, ?_⟩
  · exact derived
  · exact origin
  · simp [ExprResult.resolvedTarget, targetEq]

/-- A successful literal traversal directly reconstructs the corresponding
DD synthesis and its unchanged origin ledger. -/
theorem inferExprFuel_lit_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {value : Int}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.lit value) initial = some result) :
    DDSynthRun signature context (.lit value) initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.int, DDSynth.lit, rfl, ?_⟩
  exact DDSynthOrigin.lit

/-- A successful `something` traversal reconstructs the same one-target-meta
allocation as the DD rule, while leaving the origin ledger unchanged. -/
theorem inferExprFuel_something_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath}
    {initial : InferState} {result : ExprResult}
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      .something initial = some result) :
    DDSynthRun signature context .something initial result := by
  simp only [inferExprFuel, finishExpr, visit] at success
  have resultEq := Option.some.inj success
  subst result
  refine ⟨.matcher .any (.var initial.supply.nextTy), DDSynth.something,
    rfl, ?_⟩
  exact DDSynthOrigin.something

end Inference
end TypePM
