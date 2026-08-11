import TypePM.BridgeChecks

/-!
# Terminal-validator completeness lemmas

The public validator deliberately chooses concrete witnesses for instance and
slot checks, so a generic `WBridgeWF -> wBridgeCheck = true` theorem is not
valid.  The four checks below are different: their semantic conditions are
exactly the propositions tested by the corresponding Boolean folds.  These
reverse lemmas isolate that reusable part of milestone 5.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

/-- The four checks whose semantic and executable forms coincide can be
recovered together without choosing the validator's canonical instance or
slot witnesses. -/
theorem stableTerminalChecks_complete
    {signature : FrozenSig} {state : InferState}
    (types : TraceTypeAlignmentConditions state)
    (duals : TraceDualAlignmentConditions state)
    (finalization : TraceFinalizationSuffixConditions signature state)
    (generalization : TraceGeneralizationConditions signature state) :
    traceTypeAlignmentCheck state = true ∧
      traceDualAlignmentCheck state = true ∧
      traceFinalizationSuffixCheck signature state = true ∧
      traceGeneralizationCheck signature state = true :=
  ⟨traceTypeAlignmentCheck_complete types,
    traceDualAlignmentCheck_complete duals,
    traceFinalizationSuffixCheck_complete finalization,
    traceGeneralizationCheck_complete generalization⟩

end Reconstruction
end Inference
end TypePM
