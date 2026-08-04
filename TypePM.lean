import TypePM.P2.Syntax
import TypePM.P2.Term
import TypePM.P2.Substitution
import TypePM.P2.Relation
import TypePM.P2.Annotation
import TypePM.P2.CapMatch
import TypePM.P2.Observability
import TypePM.P2.Shape
import TypePM.P2.Projection
import TypePM.P2.Canonical
import TypePM.P2.CapTarget
import TypePM.P2.Recursion
import TypePM.P2.ClauseEvidence
import TypePM.P2.ClauseEvidenceExamples
import TypePM.P2.DirectSelf
import TypePM.P2.Unification
import TypePM.P2.Source
import TypePM.P2.SourceSubstitution
import TypePM.P2.SourceMetatheory
import TypePM.P2.Semantics
import TypePM.P2.PatternFunction
import TypePM.P2.SourceGeneralization
import TypePM.P2.GeneralizationRegression
import TypePM.P2.Dynamic
import TypePM.P2.Preservation
import TypePM.P2.DynamicMetatheory
import TypePM.P2.Reachability
import TypePM.P2.Safety
import TypePM.P2.InferenceBase
import TypePM.P2.Inference
import TypePM.P2.InferenceRegression
import TypePM.P2.InferenceHistory
import TypePM.P2.Reconstruction
import TypePM.P2.Soundness
import TypePM.P2.BridgeChecks
import TypePM.P2.RecursiveExamples

/-!
# Egison core with two-index matcher types

This is the public import surface of the current formalization.  Every dynamic
theorem is stated over the concrete source and runtime judgments in
`TypePM.P2`.
-/
