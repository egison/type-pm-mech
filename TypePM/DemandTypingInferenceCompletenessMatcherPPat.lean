import TypePM.DemandTypingInferenceCompletenessMain

/-!
# Heterogeneous primitive matcher-pattern completeness

Matcher clauses pass a raw DD target and a possibly renamed executable target.
This module generalizes primitive matcher-pattern traversal over that pair.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMatcherPPat

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessDataBisimulation
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessMatcherMain

def ppatWild_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .wild executableTarget state)
      q S ledger target [] [] := by
  let run := ppatWild_complete fuel signature path before executableTarget
  exact { run with
    target := (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .ppatWild path
      (.inferredPPat .wild executableTarget [] [] path)).transportTy related }

def ppatValue_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath) (name : String)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path (.pval name) executableTarget state)
      q S ledger target [] [(name, target)] := by
  let run := ppatValue_complete fuel signature path name before executableTarget
  exact { run with
    target := (DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
      before .ppatValue path
      (.inferredPPat (.pval name) executableTarget []
        [(name, executableTarget)] path)).transportTy related
    bindings := .cons
      ((DemandTypingInferenceCompletenessPatternTraversal.TraversalStateCorrespondence.visitThenRecordExtension
        before .ppatValue path
        (.inferredPPat (.pval name) executableTarget []
          [(name, executableTarget)] path)).transportTy related) .nil }

def ppatHole_complete_related
    (fuel : Nat) (signature : FrozenSig) (path : SyntaxPath)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    {target executableTarget : Ty}
    (related : TyBisimulation before.prevailing target executableTarget) :
    PPatRunCompletion before
      (inferPPatFuel (fuel + 1) signature path .hole executableTarget state)
      { q with nextCap := q.nextCap + 1 } S
      (DDLedger.markFreshCap ledger q) target
      [⟨.var ⟨q.nextCap⟩, target⟩] [] := by
  let run := ppatHole_complete fuel signature path before executableTarget
  let transported := run.transition.transportTy related
  have capabilityEq :
      (state.freshCap
        (freshOrigin .primitivePattern path "primitive-hole")).1 =
        .var ⟨q.nextCap⟩ := by
    change Cap.var ⟨state.supply.nextCap⟩ = Cap.var ⟨q.nextCap⟩
    rw [before.supply_eq]
  exact { run with
    target := transported
    holes := .cons
      ⟨by rw [capabilityEq]
          exact CapBisimulation.same run.transition.after (.var ⟨q.nextCap⟩),
        transported⟩ .nil }

end DemandTypingInferenceCompletenessMatcherPPat
end TypePM
