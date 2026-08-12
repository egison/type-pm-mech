import TypePM.CertifiedInference
import TypePM.CoherentSurface
import TypePM.DamasMilner

/-!
# Internal coherent reconstruction

The reconstruction certificate `Reconstruction.ExprDeriv` is itself the
mutual coherent certificate: its value-pattern, arm, and clause premises
recurse into the certificate rather than a `TypingInvariant` oracle, its pattern
layer keeps one threaded raw provenance, and its product-lift constructors
carry raw-source provenance indices.  The inference reconstruction motive
fills those indices faithfully — the recorded raw source is the type whose
head the selector actually inspected — while plan replay supplies the
always-available identity witness.

Following the `CoreTyping` precedent, this module names that certificate
`Coherent.CoherentExpr` by definitional abbreviation instead of maintaining a
mirrored copy.  On top of the aliases it proves the internal projections:
coherent reconstruction yields `TypingInvariant`, successful public inference
yields coherent reconstruction, and every Damas–Milner typing embeds directly
into the coherent certificate.  The standalone pattern-local boundaries and their
projections remain in `TypePM.CoherentSurface`
(`PatternResolutionDeriv.toThreadedSurface` and onward).

This module does not define source typability.  That role belongs exclusively
to `SourceTyping`; coherence and `TypingInvariant` occur only downstream of a
successful reconstruction or a future demand-directed state-erasure theorem.
-/

namespace TypePM
namespace Coherent

open Inference.Reconstruction

/-! ## The coherent judgment, by definitional abbreviation -/

/-- Coherent expression typing is the reconstruction certificate itself. -/
abbrev CoherentExpr := Inference.Reconstruction.ExprDeriv

/-- Coherent expression-list typing. -/
abbrev CoherentExprs := Inference.Reconstruction.ExprsDeriv

/-- Coherent threaded user-pattern resolution. -/
abbrev CoherentPattern := Inference.Reconstruction.PatternResolutionDeriv

/-- Coherent threaded user-pattern list resolution. -/
abbrev CoherentPatterns := Inference.Reconstruction.PatternResolutionsDeriv

/-- Coherent resolved user pattern under one occurrence-wide substitution. -/
abbrev CoherentResolvedPattern :=
  Inference.Reconstruction.ResolvedPatternDeriv

/-- Coherent matcher arm. -/
abbrev CoherentArm := Inference.Reconstruction.ArmDeriv

/-- Coherent matcher arm list. -/
abbrev CoherentArms := Inference.Reconstruction.ArmsDeriv

/-- Coherent actual clause under its shared prevailing substitution. -/
abbrev CoherentClause := Inference.Reconstruction.ClauseDeriv

/-- Coherent clause list with one shared prevailing substitution. -/
abbrev CoherentClauses := Inference.Reconstruction.ClausesDeriv

/-- Existential package of the shared coherent clause substitution. -/
abbrev CoherentResolvedClauses :=
  Inference.Reconstruction.ResolvedClausesDeriv

/-! ## Typing-invariant projection and inference corollaries -/

/-- Coherent reconstruction yields the state-free typing invariant. -/
theorem CoherentExpr.toTypingInvariant
    {signature context expression target}
    (derivation : CoherentExpr signature context expression target) :
    TypingInvariant signature context expression target :=
  ExprDeriv.toTypingInvariant derivation

/-- Successful public inference lands in the coherent judgment. -/
theorem infer_success_coherent
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : Inference.ExprResult}
    (success : Inference.infer signature context expression = some result) :
    CoherentExpr signature
      (Inference.ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  Inference.infer_success_reconstruct success

mutual

/-- Every Damas–Milner typing embeds directly into coherent reconstruction. -/
theorem dm_coherent {signature : FrozenSig} (sigFtv : signature.ftv = []) :
    ∀ {context : DM.SCtx} {expression : Expr} {target : DM.STy},
      DM.Typing context expression target →
      CoherentExpr signature (DM.SCtx.emb context) expression target.emb
  | _, _, _, .var found instantiation =>
      .var (DM.SCtx.find?_emb found)
        (DM.SScheme.emb_valueFlowInst instantiation)
  | _, _, _, .lam bodyTyping => by
      have body := dm_coherent sigFtv bodyTyping
      simp only [DM.SCtx.emb, List.map_cons, DM.SScheme.emb_mono] at body
      exact ExprDeriv.lam body
  | _, _, _, .app functionTyping argumentTyping =>
      .app (dm_coherent sigFtv functionTyping)
        (dm_coherent sigFtv argumentTyping)
  | _, _, _, .letE valueTyping bodyTyping => by
      refine .letE (dm_coherent sigFtv valueTyping) ?_
      rw [DM.generalize_emb sigFtv]
      exact dm_coherent sigFtv bodyTyping
  | _, _, _, .fixE distinct direct bodyTyping =>
      by
        have body := dm_coherent sigFtv bodyTyping
        simp only [DM.SCtx.emb, List.map_cons, DM.SScheme.emb_mono,
          DM.STy.emb] at body
        exact ExprDeriv.fixE distinct direct body
  | _, _, _, .lit => .lit
  | _, _, _, .tuple componentTypings =>
      .tuple (dm_coherents sigFtv componentTypings)

/-- List form of `dm_coherent`. -/
theorem dm_coherents {signature : FrozenSig} (sigFtv : signature.ftv = []) :
    ∀ {context : DM.SCtx} {expressions : List Expr}
      {targets : List DM.STy},
      DM.Typings context expressions targets →
      CoherentExprs signature (DM.SCtx.emb context) expressions
        (DM.STy.embList targets)
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail =>
      .cons (dm_coherent sigFtv head) (dm_coherents sigFtv tail)

end

/-- The polymorphic-identity witness is coherent over any closed signature. -/
theorem idProgram_coherent {signature : FrozenSig}
    (sigFtv : signature.ftv = []) :
    CoherentExpr signature [] DM.idProgram .int :=
  dm_coherent sigFtv DM.idProgram_dm_typed

end Coherent
end TypePM
