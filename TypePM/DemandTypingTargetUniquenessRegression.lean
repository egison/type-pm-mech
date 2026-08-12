import TypePM.DemandTypingTargetUniqueness
import TypePM.DemandTypingTerminalAuditBuilder
import TypePM.RecursiveExamples

/-!
# Open-context target-uniqueness boundary

Exact solved-form MGUs need not choose the same orientation when an
application equates two metavariables already present in the source context.
This regression gives two fully audited `DDTyping` derivations of the same
open term whose published targets are the two distinct input metavariables.
It rules out target uniqueness modulo renamings that must fix the complete
initial source scope; a uniqueness theorem must allow residual source
metavariables to be renamed as well.
-/

namespace TypePM
namespace DemandTypingTargetUniquenessRegression

abbrev regressionSignature : FrozenSig := RecursiveExamples.listSignature

theorem DDSynthOrigin.transportRaw
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw raw' : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger') :
    DDSynthOrigin signature raw' ledger ledger' := by
  have proofEq : raw = raw' := Subsingleton.elim _ _
  cases proofEq
  exact origin

theorem DDSynthOrigin.transportSome
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw' : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (source : ∃ raw : DDSynth signature q S context expression target q' S',
      DDSynthOrigin signature raw ledger ledger') :
    DDSynthOrigin signature raw' ledger ledger' := by
  rcases source with ⟨raw, origin⟩
  exact DDSynthOrigin.transportRaw origin

def originSafePairedCapId (ledger : CapabilityOriginLedger)
    {left right : Ty} {targetSubst : TySubst}
    (exact : ExactPairedMGU left right ⟨CapSubst.id, targetSubst⟩) :
    OriginSafeExactPairedMGU ledger left right
      ⟨CapSubst.id, targetSubst⟩ :=
  ⟨exact, ⟨AdmissibleCapPost.id ledger⟩⟩

/-- Two monomorphic source metavariables are deliberately kept distinct in
the input context. -/
def orientationContext : Context :=
  [("f", Scheme.mono (.fn (.var 0) (.var 0))),
    ("x", Scheme.mono (.var 1))]

def orientationExpr : Expr := .app (.var "f") (.var "x")

theorem orientation_initialSupply :
    Inference.initialSupply regressionSignature orientationContext = ⟨0, 2⟩ := by
  native_decide

/-- Align `?0 -> ?0` with the application's fresh `?2 -> ?3`. -/
def orientationFunctionDelta : Subst :=
  ⟨CapSubst.id, fnFreshDelta (.var 0) (.var 0) 2 3⟩

theorem orientationFunctionDelta_exact :
    ExactPairedMGU (.fn (.var 0) (.var 0))
      (.fn (.var 2) (.var 3)) orientationFunctionDelta := by
  exact ExactPairedMGU.fnFresh (.var 0) (.var 0) 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)

def orientationFunctionSubst : Subst :=
  Subst.seq orientationFunctionDelta Subst.id

/-- First legal orientation of the argument equality: `?1 := ?0`. -/
def orientationLeftTerminal : Subst :=
  Subst.seq
    ⟨CapSubst.id, Unification.TySubst.single 1 (.var 0)⟩
    orientationFunctionSubst

/-- Second legal orientation of the same equality: `?0 := ?1`. -/
def orientationRightTerminal : Subst :=
  Subst.seq
    ⟨CapSubst.id, Unification.TySubst.single 0 (.var 1)⟩
    orientationFunctionSubst

def orientationFunction_ddSynth :
    DDSynth regressionSignature ⟨0, 2⟩ Subst.id orientationContext
      (.var "f") (.fn (.var 0) (.var 0)) ⟨0, 2⟩ Subst.id := by
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := regressionSignature) (q := ⟨0, 2⟩)
      (S := Subst.id) (Γ := orientationContext) (name := "f")
      (scheme := Scheme.mono (.fn (.var 0) (.var 0))) (by
        simp [orientationContext, Context.applySubst, Context.find?]))

def orientationArgument_ddSynth :
    DDSynth regressionSignature ⟨0, 4⟩ orientationFunctionSubst
      orientationContext (.var "x") (.var 1) ⟨0, 4⟩
      orientationFunctionSubst := by
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := regressionSignature) (q := ⟨0, 4⟩)
      (S := orientationFunctionSubst) (Γ := orientationContext)
      (name := "x") (scheme := Scheme.mono (.var 1)) (by
        simp [orientationContext, Context.applySubst, Context.find?,
          Scheme.applyMeta_mono, orientationFunctionSubst,
          orientationFunctionDelta, Subst.seq, Subst.apply, Subst.id,
          CapSubst.id, TySubst.id, Ty.applyCapability,
          Ty.applyTarget, fnFreshDelta]))

theorem orientationLeftArgument_ddCheck :
    DDCheck regressionSignature ⟨0, 4⟩ orientationFunctionSubst
      orientationContext (.var "x") (.var 2) ⟨0, 4⟩
      orientationLeftTerminal := by
  exact .mk orientationArgument_ddSynth
    (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varLeft 1 (.var 0) (by decide))))

theorem orientationRightArgument_ddCheck :
    DDCheck regressionSignature ⟨0, 4⟩ orientationFunctionSubst
      orientationContext (.var "x") (.var 2) ⟨0, 4⟩
      orientationRightTerminal := by
  exact .mk orientationArgument_ddSynth
    (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight (.var 1) 0 (by decide))))

def orientationLeft_ddSynth :
    DDSynth regressionSignature ⟨0, 2⟩ Subst.id orientationContext
      orientationExpr (.var 3) ⟨0, 4⟩ orientationLeftTerminal := by
  exact .app orientationFunction_ddSynth
    (.ordinary rfl orientationFunctionDelta_exact)
    orientationLeftArgument_ddCheck

def orientationRight_ddSynth :
    DDSynth regressionSignature ⟨0, 2⟩ Subst.id orientationContext
      orientationExpr (.var 3) ⟨0, 4⟩ orientationRightTerminal := by
  exact .app orientationFunction_ddSynth
    (.ordinary rfl orientationFunctionDelta_exact)
    orientationRightArgument_ddCheck

def orientationFunction_ddSynthOrigin :
    DDSynthOrigin regressionSignature orientationFunction_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst Subst.id orientationContext).find? "f" =
      some (Scheme.mono (.fn (.var 0) (.var 0))) := by
    simp [orientationContext, Context.applySubst, Context.find?]
  let raw₀ := DDSynth.var (signature := regressionSignature) (q := ⟨0, 2⟩)
    lookup
  have origin₀ : DDSynthOrigin regressionSignature raw₀ [] [] := by
    simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins,
      Scheme.canonicalCapImages, Scheme.mono] using
      (DDSynthOrigin.var (signature := regressionSignature) (q := ⟨0, 2⟩)
        (ledger := []) lookup)
  have source₀ : ∃ raw, DDSynthOrigin regressionSignature raw [] [] :=
    ⟨raw₀, origin₀⟩
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using source₀

def orientationArgument_ddSynthOrigin :
    DDSynthOrigin regressionSignature orientationArgument_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup :
      (Context.applySubst orientationFunctionSubst orientationContext).find?
        "x" = some (Scheme.mono (.var 1)) := by
    simp [orientationContext, Context.applySubst, Context.find?,
      Scheme.applyMeta_mono, orientationFunctionSubst,
      orientationFunctionDelta, Subst.seq, Subst.apply, Subst.id,
      CapSubst.id, TySubst.id, Ty.applyCapability,
      Ty.applyTarget, fnFreshDelta]
  let raw₀ := DDSynth.var (signature := regressionSignature) (q := ⟨0, 4⟩)
    lookup
  have origin₀ : DDSynthOrigin regressionSignature raw₀ [] [] := by
    simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins,
      Scheme.canonicalCapImages, Scheme.mono] using
      (DDSynthOrigin.var (signature := regressionSignature) (q := ⟨0, 4⟩)
        (ledger := []) lookup)
  have source₀ : ∃ raw, DDSynthOrigin regressionSignature raw [] [] :=
    ⟨raw₀, origin₀⟩
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using source₀

def orientationLeftArgument_ddCheckOrigin :
    DDCheckOrigin regressionSignature orientationLeftArgument_ddCheck [] [] := by
  exact .mk orientationArgument_ddSynthOrigin
    (.ordinary (S := orientationFunctionSubst) (raw := .var 1)
      (expected := .var 2) rfl
      (.ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.varLeft 1 (.var 0) (by decide)))))

def orientationRightArgument_ddCheckOrigin :
    DDCheckOrigin regressionSignature orientationRightArgument_ddCheck [] [] := by
  exact .mk orientationArgument_ddSynthOrigin
    (.ordinary (S := orientationFunctionSubst) (raw := .var 1)
      (expected := .var 2) rfl
      (.ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.varRight (.var 1) 0 (by decide)))))

def orientationLeft_ddSynthOrigin :
    DDSynthOrigin regressionSignature orientationLeft_ddSynth [] [] := by
  exact .app orientationFunction_ddSynthOrigin
    (.ordinary rfl
      (originSafePairedCapId [] orientationFunctionDelta_exact))
    orientationLeftArgument_ddCheckOrigin

def orientationRight_ddSynthOrigin :
    DDSynthOrigin regressionSignature orientationRight_ddSynth [] [] := by
  exact .app orientationFunction_ddSynthOrigin
    (.ordinary rfl
      (originSafePairedCapId [] orientationFunctionDelta_exact))
    orientationRightArgument_ddCheckOrigin

def orientationFunction_terminalAudit (terminal : Subst) :
    DDSynthTerminalAudit terminal regressionSignature
      orientationFunction_ddSynthOrigin := by
  let lookup : (Context.applySubst Subst.id orientationContext).find? "f" =
      some (Scheme.mono (.fn (.var 0) (.var 0))) := by
    simp [orientationContext, Context.applySubst, Context.find?]
  let origin₀ := DDSynthOrigin.var (signature := regressionSignature)
    (q := ⟨0, 2⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit terminal regressionSignature origin₀ :=
    DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
    Scheme.FreshOpening.capImages, Scheme.mono] using source₀

def orientationArgument_terminalAudit (terminal : Subst) :
    DDSynthTerminalAudit terminal regressionSignature
      orientationArgument_ddSynthOrigin := by
  let lookup :
      (Context.applySubst orientationFunctionSubst orientationContext).find?
        "x" = some (Scheme.mono (.var 1)) := by
    simp [orientationContext, Context.applySubst, Context.find?,
      Scheme.applyMeta_mono, orientationFunctionSubst,
      orientationFunctionDelta, Subst.seq, Subst.apply, Subst.id,
      CapSubst.id, TySubst.id, Ty.applyCapability,
      Ty.applyTarget, fnFreshDelta]
  let origin₀ := DDSynthOrigin.var (signature := regressionSignature)
    (q := ⟨0, 4⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit terminal regressionSignature origin₀ :=
    DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
    Scheme.FreshOpening.capImages, Scheme.mono] using source₀

def orientationLeft_terminalAudit :
    DDSynthTerminalAudit orientationLeftTerminal regressionSignature
      orientationLeft_ddSynthOrigin := by
  let argumentAligned : DDAlignWithLedger [] orientationFunctionSubst
      (.var 1) (.var 2) orientationLeftTerminal :=
    .ordinary rfl (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varLeft 1 (.var 0) (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    (orientationArgument_terminalAudit orientationLeftTerminal)
  let functionAligned : DDAlignTypesWithLedger [] Subst.id
      (.fn (.var 0) (.var 0)) (.fn (.var 2) (.var 3))
      orientationFunctionSubst :=
    .ordinary rfl
      (originSafePairedCapId [] orientationFunctionDelta_exact)
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        (orientationFunction_terminalAudit orientationLeftTerminal)
        argumentAudit))

def orientationRight_terminalAudit :
    DDSynthTerminalAudit orientationRightTerminal regressionSignature
      orientationRight_ddSynthOrigin := by
  let argumentAligned : DDAlignWithLedger [] orientationFunctionSubst
      (.var 1) (.var 2) orientationRightTerminal :=
    .ordinary rfl (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight (.var 1) 0 (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    (orientationArgument_terminalAudit orientationRightTerminal)
  let functionAligned : DDAlignTypesWithLedger [] Subst.id
      (.fn (.var 0) (.var 0)) (.fn (.var 2) (.var 3))
      orientationFunctionSubst :=
    .ordinary rfl
      (originSafePairedCapId [] orientationFunctionDelta_exact)
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        (orientationFunction_terminalAudit orientationRightTerminal)
        argumentAudit))

/-- The first exact-MGU orientation publishes the first source metavariable. -/
theorem orientation_ddTyping_left :
    DDTyping regressionSignature orientationContext orientationExpr (.var 0) := by
  unfold DDTyping
  rw [orientation_initialSupply]
  refine ⟨.var 3, ⟨0, 4⟩, orientationLeftTerminal,
    orientationLeft_ddSynth, [], orientationLeft_ddSynthOrigin,
    orientationLeft_terminalAudit, ?_⟩
  native_decide

/-- The symmetric exact-MGU orientation publishes the second source
metavariable for the same signature, context, and expression. -/
theorem orientation_ddTyping_right :
    DDTyping regressionSignature orientationContext orientationExpr (.var 1) := by
  unfold DDTyping
  rw [orientation_initialSupply]
  refine ⟨.var 3, ⟨0, 4⟩, orientationRightTerminal,
    orientationRight_ddSynth, [], orientationRight_ddSynthOrigin,
    orientationRight_terminalAudit, ?_⟩
  native_decide

/-- The two published targets are syntactically distinct, so no renaming that
fixes both input metavariables can identify them. -/
theorem orientation_targets_distinct : (Ty.var 0) ≠ .var 1 := by decide

/-- Any paired renaming that fixes the complete initial target scope also
fixes both published targets, so it cannot identify the two derivations. -/
theorem orientation_not_equal_under_initially_fixed_subst
    (post : Subst)
    (fixZero : post.target 0 = .var 0)
    (fixOne : post.target 1 = .var 1) :
    post.apply (.var 0) ≠ post.apply (.var 1) := by
  intro equal
  change post.target 0 = post.target 1 at equal
  rw [fixZero, fixOne] at equal
  exact orientation_targets_distinct equal

/-- The strongest valid theorem applies to the same pair once the input
signature is known well formed: the two distinct source variables rename to
one common deterministic executable target. -/
theorem orientation_targets_unique_modulo_renaming :
    DemandTypingTargetUniqueness.TargetRenamingEquivalent (.var 0) (.var 1) :=
  DemandTypingTargetUniqueness.DDTyping.target_unique_modulo_renaming
    orientation_ddTyping_left orientation_ddTyping_right
      RecursiveExamples.listSignature_wf

end DemandTypingTargetUniquenessRegression
end TypePM
