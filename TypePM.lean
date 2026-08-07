import TypePM.Syntax
import TypePM.Term
import TypePM.Substitution
import TypePM.Relation
import TypePM.Annotation
import TypePM.CapMatch
import TypePM.Observability
import TypePM.Shape
import TypePM.Projection
import TypePM.Canonical
import TypePM.CapTarget
import TypePM.Recursion
import TypePM.ClauseEvidence
import TypePM.ClauseEvidenceExamples
import TypePM.DirectSelf
import TypePM.Unification
import TypePM.Source
import TypePM.CapabilityOrigin
import TypePM.PairedUnification
import TypePM.Elaboration
import TypePM.CanonicalCoercion
import TypePM.DamasMilner
import TypePM.PrincipalityCounterexample
import TypePM.ElaborationRegression
import TypePM.SourceSubstitution
import TypePM.SourceMetatheory
import TypePM.Semantics
import TypePM.PatternFunction
import TypePM.SourceGeneralization
import TypePM.GeneralizationRegression
import TypePM.Dynamic
import TypePM.Preservation
import TypePM.SignatureChecker
import TypePM.DynamicMetatheory
import TypePM.Reachability
import TypePM.Safety
import TypePM.RuntimeAgreementBridge
import TypePM.InferenceBase
import TypePM.Inference
import TypePM.InferenceLedgerAdmissibility
import TypePM.InferenceLocalFactorization
import TypePM.InferenceTraversalLocalFactorization
import TypePM.InferenceTraceFactorization
import TypePM.InferenceFreezeTransport
import TypePM.InferenceAdmissibleTrace
import TypePM.InferenceInput
import TypePM.InferenceHistory
import TypePM.InferenceStateExtension
import TypePM.InferenceTraversalStateExtension
import TypePM.InferenceTraversalAdmissibleTrace
import TypePM.InferenceRunInvariants
import TypePM.Reconstruction
import TypePM.CoherentSurface
import TypePM.BridgeChecks
import TypePM.CertifiedInference
import TypePM.DMTerminalAcceptance
import TypePM.CoreTyping
import TypePM.CoherentTyping
import TypePM.CertifiedInferenceRegression
import TypePM.AcceptanceGapRegression
import TypePM.ApplicationCoercionRegression
import TypePM.DynamicSafetyRegression
import TypePM.DynamicCaptureRegression
import TypePM.DynamicDispatchRegression
import TypePM.PatternFunctionSafetyRegression
import TypePM.ProducerStrengtheningRegression
import TypePM.InferenceRegression
import TypePM.Soundness
import TypePM.RecursiveExamples
import TypePM.PatternCtorCapabilityRegression

/-!
# Egison core with two-index matcher types

This is the public import surface of the current formalization.  Every dynamic
theorem is stated over the concrete source and runtime judgments in
`TypePM`.
-/
