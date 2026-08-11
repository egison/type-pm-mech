import TypePM.CertifiedInference
import TypePM.CoherentSurface
import TypePM.DamasMilner

/-!
# Internal coherent reconstruction

The reconstruction certificate `Reconstruction.ExprDeriv` is itself the
mutual coherent certificate: its value-pattern, arm, and clause premises
recurse into the certificate rather than a `RuntimeTyping` oracle, its pattern
layer keeps one threaded raw provenance, and its product-lift constructors
carry raw-source provenance indices.  The inference reconstruction motive
fills those indices faithfully — the recorded raw source is the type whose
head the selector actually inspected — while plan replay and the match-free
embedding below supply the always-available identity witness.

Following the `CoreTyping` precedent, this module names that certificate
`Coherent.CoherentExpr` by definitional abbreviation instead of maintaining a
mirrored copy.  On top of the aliases it proves the internal projections:
coherent reconstruction yields `RuntimeTyping`, successful public inference
yields coherent reconstruction, and every Damas–Milner typing embeds into the
coherent certificate.  The standalone pattern-local boundaries and their
projections remain in `TypePM.CoherentSurface`
(`PatternResolutionDeriv.toThreadedSurface` and onward).

This module does not define source typability.  That role belongs exclusively
to `DDTyping`; coherence and `RuntimeTyping` occur only downstream of a
successful reconstruction or a future DD state-erasure theorem.
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

/-! ## Runtime-certificate projection and inference corollaries -/

/-- Coherent reconstruction yields the state-free runtime certificate. -/
theorem CoherentExpr.toRuntimeTyping
    {signature context expression target}
    (derivation : CoherentExpr signature context expression target) :
    RuntimeTyping signature context expression target :=
  ExprDeriv.toRuntimeTyping derivation

/-- Successful public inference lands in the coherent judgment. -/
theorem infer_success_coherent
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : Inference.ExprResult}
    (success : Inference.infer signature context expression = some result) :
    CoherentExpr signature
      (Inference.ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  Inference.infer_success_reconstruct success

/-! ## The match-free runtime-certificate fragment is coherent

Coherence restricts only pattern provenance, so runtime certificates for
expressions without `matchAll` and matcher literals are all coherent: their
typing constructors mirror the reconstruction certificate one to one.  This
shows that every DM typing embeds into a recursive runtime certificate. -/

mutual

/-- Expressions that contain no `matchAll` and no matcher literal. -/
def matchFree : Expr → Bool
  | .var _ => true
  | .lam _ body => matchFree body
  | .fix _ _ body => matchFree body
  | .app function argument => matchFree function && matchFree argument
  | .lit _ => true
  | .tuple expressions => matchFreeList expressions
  | .ctor _ expressions => matchFreeList expressions
  | .prim _ expressions => matchFreeList expressions
  | .letE _ value body => matchFree value && matchFree body
  | .something => true
  | .matcher _ => false
  | .matchAll _ _ _ _ => false

/-- List form of `matchFree`. -/
def matchFreeList : List Expr → Bool
  | [] => true
  | expression :: expressions =>
      matchFree expression && matchFreeList expressions

end

mutual

/-- Every runtime certificate for a match-free expression is coherent. -/
theorem coherent_of_matchFree {signature : FrozenSig} :
    ∀ {context : Context} {expression : Expr} {target : Ty},
      RuntimeTyping signature context expression target →
      matchFree expression = true →
      CoherentExpr signature context expression target
  | _, _, _, .var lookup flow, _ => .var lookup flow
  | _, _, _, .lam bodyTyping, hfree =>
      .lam (coherent_of_matchFree bodyTyping hfree)
  | _, _, _, .app functionTyping argumentTyping, hfree => by
      simp only [matchFree, Bool.and_eq_true] at hfree
      exact .app (coherent_of_matchFree functionTyping hfree.1)
        (coherent_of_matchFree argumentTyping hfree.2)
  | _, _, _, .letE valueTyping bodyTyping, hfree => by
      simp only [matchFree, Bool.and_eq_true] at hfree
      exact .letE (coherent_of_matchFree valueTyping hfree.1)
        (coherent_of_matchFree bodyTyping hfree.2)
  | _, _, _, .fixE distinct direct bodyTyping, hfree =>
      .fixE distinct direct (coherent_of_matchFree bodyTyping hfree)
  | _, _, _, .lit, _ => .lit
  | _, _, _, .tuple typings, hfree =>
      .tuple (coherents_of_matchFree typings hfree)
  | _, _, _, .ctor lookup instanceTyping typings, hfree =>
      .ctor lookup instanceTyping (coherents_of_matchFree typings hfree)
  | _, _, _, .prim lookup instanceTyping typings, hfree =>
      .prim lookup instanceTyping (coherents_of_matchFree typings hfree)
  | _, _, _, .something, _ => .something
  | _, _, _, .matchAll _ _ _ _, hfree => by
      simp [matchFree] at hfree
  | _, _, _, .matcher _ _ _ _ _ _ _, hfree => by
      simp [matchFree] at hfree
  | _, _, _, .coerceMatcherToSlot premise certificate post, hfree =>
      .coerceMatcherToSlot (coherent_of_matchFree premise hfree)
        certificate post
  | _, _, _, .checkSlotToSlot premise certificate post, hfree =>
      .checkSlotToSlot (coherent_of_matchFree premise hfree) certificate post
  | _, _, _, .coerceProductMatcher premise, hfree =>
      .coerceProductMatcher (coherent_of_matchFree premise hfree)
        (Subst.apply_id _)
  | _, _, _, .coerceSlotTuple premise, hfree =>
      .coerceSlotTuple (coherent_of_matchFree premise hfree)
        (Subst.apply_id _)

/-- List form of `coherent_of_matchFree`. -/
theorem coherents_of_matchFree {signature : FrozenSig} :
    ∀ {context : Context} {expressions : List Expr} {targets : List Ty},
      ExprsTy signature context expressions targets →
      matchFreeList expressions = true →
      CoherentExprs signature context expressions targets
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons head tail, hfree => by
      simp only [matchFreeList, Bool.and_eq_true] at hfree
      exact .cons (coherent_of_matchFree head hfree.1)
        (coherents_of_matchFree tail hfree.2)

end

mutual

/-- Damas–Milner typable expressions never contain match constructs. -/
theorem matchFree_of_dm :
    ∀ {context : DM.SCtx} {expression : Expr} {target : DM.STy},
      DM.Typing context expression target → matchFree expression = true
  | _, _, _, .var _ _ => rfl
  | _, _, _, .lam bodyTyping => by
      simp only [matchFree]
      exact matchFree_of_dm bodyTyping
  | _, _, _, .app functionTyping argumentTyping => by
      simp only [matchFree, Bool.and_eq_true]
      exact ⟨matchFree_of_dm functionTyping, matchFree_of_dm argumentTyping⟩
  | _, _, _, .letE valueTyping bodyTyping => by
      simp only [matchFree, Bool.and_eq_true]
      exact ⟨matchFree_of_dm valueTyping, matchFree_of_dm bodyTyping⟩
  | _, _, _, .fixE _ _ bodyTyping => by
      simp only [matchFree]
      exact matchFree_of_dm bodyTyping
  | _, _, _, .lit => rfl
  | _, _, _, .tuple typings => by
      simp only [matchFree]
      exact matchFreeList_of_dm typings

/-- List form of `matchFree_of_dm`. -/
theorem matchFreeList_of_dm :
    ∀ {context : DM.SCtx} {expressions : List Expr} {targets : List DM.STy},
      DM.Typings context expressions targets →
        matchFreeList expressions = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons head tail => by
      simp only [matchFreeList, Bool.and_eq_true]
      exact ⟨matchFree_of_dm head, matchFreeList_of_dm tail⟩

end

/-- Every Damas–Milner typing embeds into the coherent runtime certificate. -/
theorem dm_coherent {signature : FrozenSig} (sigFtv : signature.ftv = [])
    {context : DM.SCtx} {expression : Expr} {target : DM.STy}
    (typing : DM.Typing context expression target) :
    CoherentExpr signature (DM.SCtx.emb context) expression target.emb :=
  coherent_of_matchFree (DM.Typing.emb sigFtv typing)
    (matchFree_of_dm typing)

/-- The polymorphic-identity witness is coherent over any closed signature. -/
theorem idProgram_coherent {signature : FrozenSig}
    (sigFtv : signature.ftv = []) :
    CoherentExpr signature [] DM.idProgram .int :=
  dm_coherent sigFtv DM.idProgram_dm_typed

end Coherent
end TypePM
