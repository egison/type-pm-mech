import TypePM.Syntax
import TypePM.Term
import TypePM.Substitution
import TypePM.PolySyntax
import TypePM.PolyScheme
import TypePM.SchemeEquality
import TypePM.PolyCloseLaws
import TypePM.PolyFreeVars
import TypePM.PolyGeneralization
import TypePM.PolyInstantiation
import TypePM.PolyInstantiationTransport
import TypePM.PolySubstitutionLaws
import TypePM.PolyFreshInstantiation
import TypePM.SchemeOpeningLists
import TypePM.SchemeContext
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
import TypePM.DamasMilnerAcceptance
import TypePM.DamasMilnerConservativity
import TypePM.DamasMilnerAcceptanceMutual
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
import TypePM.Readiness
import TypePM.Interpreter
import TypePM.InterpreterAdequacy
import TypePM.RuntimeAgreementBridge
import TypePM.InferenceBase
import TypePM.Bounds
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
import TypePM.ReadinessRegression
import TypePM.InterpreterRegression
import TypePM.DynamicCaptureRegression
import TypePM.DynamicDispatchRegression
import TypePM.PatternFunctionSafetyRegression
import TypePM.ProducerStrengtheningRegression
import TypePM.InferenceRegression
import TypePM.Soundness
import TypePM.DemandTypingSafetyRegression
import TypePM.RecursiveExamples
import TypePM.PatternCtorCapabilityRegression
import TypePM.DemandTyping
import TypePM.DemandTypingIdempotence
import TypePM.SchemeBoundedness
import TypePM.DemandTypingLedgerMetatheory
import TypePM.DemandTypingOrigin
import TypePM.DemandTypingOriginMetatheory
import TypePM.DemandTypingInferenceSoundnessPublic
import TypePM.DemandTypingInferenceSoundnessRegression
import TypePM.DemandTypingInferenceCompletenessPublic
import TypePM.DemandTypingInferenceCompletenessRegression
import TypePM.DemandTypingInferenceEquivalence
import TypePM.DemandTypingInferenceEquivalenceRegression
import TypePM.DemandTypingTargetUniqueness
import TypePM.DemandTypingTargetUniquenessRegression
import TypePM.TypeInstance
import TypePM.SourcePrincipality
import TypePM.RelativePrincipality
import TypePM.DemandTypingErasure
import TypePM.DemandTypingTerminalAuditBuilder
import TypePM.DemandTypingRegression
import TypePM.DemandTypingTerminalAuditErasureRegression
import TypePM.PublicTheorems
import TypePM.AxiomAudit

/-!
# Egison core with two-index matcher types

This is the public import surface of the current formalization.  `SourceTyping` is
the only source-language typing judgment. `TypingInvariant` is an internal,
state-free invariant used after inference state has been erased; it supports
value typing and the dynamic metatheory but does not define source acceptance.
`DemandTypingErasure` is the facade for scoped state factorization,
idempotence preservation, the terminal-audit tree, full fixed-terminal
erasure, and the closed-program bridge to that internal judgment.
`DemandTypingInferenceSoundnessPublic` exposes the converse-facing soundness
boundary from successful executable inference to `SourceTyping`.  `Soundness`
exposes `SourceTyping.safe`, which obtains signature closedness from the single
public `FrozenSigWF` condition and packages state erasure with the concrete
dynamic safety interface.  `DemandTypingInferenceCompletenessPublic` exposes
the premise-free acceptance-completeness boundary from `SourceTyping` back to
successful executable inference.  `DemandTypingInferenceEquivalence` composes
the two directions into decidable source typability, closed-program
annotation-freeness, and soundness of the type reported by `inferType`.
`DemandTypingTargetUniqueness` strengthens this result: every two audited
`SourceTyping` targets for the same source have one common representative under local
two-sort variable renamings of all residual metavariables.
-/
