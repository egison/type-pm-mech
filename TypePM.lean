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
import TypePM.DamasMilner
import TypePM.PrincipalityCounterexample
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
import TypePM.InferenceInput
import TypePM.InferenceHistory
import TypePM.Reconstruction
import TypePM.BridgeChecks
import TypePM.CertifiedInference
import TypePM.CertifiedInferenceRegression
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
