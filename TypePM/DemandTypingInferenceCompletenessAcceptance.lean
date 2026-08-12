import TypePM.CertifiedInference
import TypePM.DemandTypingInferenceCompletenessValidatorTrace

/-!
# Final executable acceptance composition

The completeness recursion reconstructs one concrete fuelled traversal and
all semantic conditions inspected by the two public filters.  This module
contains the small executable composition step which turns those internally
derived facts into success of `Inference.infer`.

These lemmas are intentionally not the public completeness theorem: their
premises are implementation-facing certificates produced inside the direct
`SourceTyping` recursion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessAcceptance

open Inference
open Inference.Reconstruction

/-- A successful canonical traversal passes `inferRaw` once its reconstructed
producer trace is known to be safe. -/
theorem inferRaw_complete_of_core_and_protected
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) = some result)
    (producerSafe : ProtectedProducerTrace result.state) :
    inferRaw signature context expression = some result := by
  have checked : protectedProducerTraceCheck result.state = true :=
    (protectedProducerTraceCheck_eq_true result.state).2 producerSafe
  simp [inferRaw, core, enforceProtectedResult, checked]

/-- Assemble the nine terminal conditions into the public certified result.
The root completeness proof supplies every premise from the reconstructed run
and terminal audit; no premise is exposed by the public theorem. -/
theorem infer_complete_of_core_and_conditions
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) = some result)
    (producerSafe : ProtectedProducerTrace result.state)
    (primitiveHoles :
      TracePrimitiveHoleConditions signature result.state.trace)
    (patternLeaves :
      TracePatternLeafConditions signature result.state.trace)
    (patternCtors : TracePatternCtorConditions signature result.state)
    (instances : CanonicalTraceInstanceSuffixConditions result.state)
    (slots : CanonicalTraceSlotAlignmentConditions result.state)
    (types : TraceTypeAlignmentConditions result.state)
    (duals : TraceDualAlignmentConditions result.state)
    (finalization :
      TraceFinalizationSuffixConditions signature result.state)
    (generalization : TraceGeneralizationConditions signature result.state) :
    infer signature context expression = some result := by
  apply infer_complete_of_raw_and_checked
  · exact inferRaw_complete_of_core_and_protected core producerSafe
  · exact wBridgeCheck_complete primitiveHoles patternLeaves patternCtors
      instances slots types duals finalization generalization

end DemandTypingInferenceCompletenessAcceptance
end TypePM
