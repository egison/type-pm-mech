import TypePM.DemandTypingRuntimeErasureUserPatterns

/-!
# Combined runtime erasure for `matchAll`

This module is deliberately downstream of both expression and user-pattern
erasure, avoiding an import cycle between their mutually referenced
judgments.
-/

namespace TypePM
namespace DDSynthOrigin

/-- `matchAll` transports each child through exactly the chronological
suffix following that child, then applies the state-free runtime constructor
at the common final cut. -/
theorem runtimeErasureUnder_matchAll
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {target matcher : Expr} {pattern : Pattern}
    {body : Expr} {targetTarget : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 : Subst}
    {dual : Dual} {bindings : MonoCtx} {q2 : InferenceBase.FreshSupply}
    {S2 S3 : Subst} {q3 : InferenceBase.FreshSupply} {S4 : Subst}
    {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 ledger2 ledger3 ledger' : CapabilityOriginLedger}
    {targetRaw : DDSynth signature q S context target targetTarget q1 S1}
    (targetOrigin : DDSynthOrigin signature targetRaw ledger ledger1)
    {patternRaw : DDPattern signature q1 S1 context [] [] pattern dual
      bindings q2 S2}
    (patternOrigin : DDPatternOrigin signature patternRaw ledger1 ledger2)
    (targetAligned : DDAlignTypesWithLedger ledger2 S2 dual.target
      targetTarget S3)
    {matcherRaw : DDCheck signature q2 S3 context matcher
      (.slot dual.cap targetTarget) q3 S4}
    (matcherOrigin : DDCheckOrigin signature matcherRaw ledger2 ledger3)
    {bodyRaw : DDSynth signature q3 S4
      (bindings.toContext ++ context) body bodyTarget q' S'}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger3 ledger')
    (targetUnder : RuntimeErasureUnder targetOrigin)
    (patternUnder : DDPatternOrigin.RuntimeErasureUnder patternOrigin)
    (matcherUnder : DDCheckOrigin.RuntimeErasureUnder matcherOrigin)
    (bodyUnder : RuntimeErasureUnder bodyOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : NamedContext.BoundedBy q context) :
    RuntimeErasureUnder
      (DDSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
        matcherOrigin bodyOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  obtain ⟨S1b, targetB⟩ := targetOrigin.erase.boundedBy closed Sb
    contextBounded
  have ext1 := targetOrigin.erase.supplyExtends
  obtain ⟨S2b, dualB, bindingsB⟩ := patternOrigin.erase.boundedBy
    closed S1b (contextBounded.mono ext1)
    (fun entry membership => nomatch membership)
    (fun entry membership => nomatch membership)
  have ext2 := patternOrigin.erase.supplyExtends
  have S3b := targetAligned.erase.boundedBy S2b dualB.2
    (targetB.mono ext2)
  have matcherExpectedB := Ty.BoundedBy.slotOf dualB.1
    (targetB.mono ext2)
  have S4b := matcherOrigin.erase.boundedBy closed S3b
    (contextBounded.mono (ext1.trans ext2)) matcherExpectedB
  have ext3 := matcherOrigin.erase.supplyExtends
  have patternFactor := DDPatternOrigin.factorize patternOrigin closed S1b
    (contextBounded.mono ext1)
    (fun entry membership => nomatch membership)
    (fun entry membership => nomatch membership)
  have alignmentFactor := DDErasure.StateFactorization.ofAlignTypes
    targetAligned S2b dualB.2 (targetB.mono ext2)
  have matcherFactor := DDCheckOrigin.factorize matcherOrigin closed S3b
    (contextBounded.mono (ext1.trans ext2)) matcherExpectedB
  have bodyFactor := DDSynthOrigin.factorize bodyOrigin closed S4b
    (NamedContext.BoundedBy.append ((bindingsB.mono ext3).toContext)
      (contextBounded.mono ((ext1.trans ext2).trans ext3)))
  have afterAlignmentFactor := matcherFactor.trans bodyFactor
  have afterPatternFactor :=
    (alignmentFactor.trans matcherFactor).trans bodyFactor
  have afterTargetFactor := patternFactor.trans afterPatternFactor
  rcases bodyFactor with ⟨bodyPost, bodyEquation, bodyAdmissible⟩
  rcases afterAlignmentFactor with
    ⟨afterAlignmentPost, afterAlignmentEquation, afterAlignmentAdmissible⟩
  rcases afterPatternFactor with
    ⟨afterPatternPost, afterPatternEquation, afterPatternAdmissible⟩
  rcases afterTargetFactor with
    ⟨afterTargetPost, afterTargetEquation, afterTargetAdmissible⟩
  have targetEquation : finalSubst =
      Subst.seq (Subst.seq post afterTargetPost) S1 := by
    rw [terminalEquation, afterTargetEquation]
    exact PhasedPost.seq_assoc post afterTargetPost S1
  have patternEquation : finalSubst =
      Subst.seq (Subst.seq post afterPatternPost) S2 := by
    rw [terminalEquation, afterPatternEquation]
    exact PhasedPost.seq_assoc post afterPatternPost S2
  have matcherEquation : finalSubst =
      Subst.seq (Subst.seq post bodyPost) S4 := by
    rw [terminalEquation, bodyEquation]
    exact PhasedPost.seq_assoc post bodyPost S4
  have targetAtFinal := targetUnder targetEquation
    (afterTargetAdmissible.seq admissible)
  have patternAtFinal := patternUnder patternEquation
    (afterPatternAdmissible.seq admissible)
  have matcherAtFinal := matcherUnder matcherEquation
    (bodyAdmissible.seq admissible)
  have bodyAtFinal := bodyUnder terminalEquation admissible
  have finalTargetEquality : finalSubst.apply dual.target =
      finalSubst.apply targetTarget := by
    rw [terminalEquation, afterAlignmentEquation,
      Subst.seq_apply, Subst.seq_apply, Subst.seq_apply, Subst.seq_apply]
    exact congrArg post.apply
      (congrArg afterAlignmentPost.apply targetAligned.output_equal)
  rw [finalTargetEquality] at patternAtFinal
  have matcherAtFinal' : RuntimeTyping signature
      (context.applySubst finalSubst) matcher
      (.slot (dual.cap.apply finalSubst.cap)
        (finalSubst.apply targetTarget)) := by
    simpa only [Subst.apply_slot] using matcherAtFinal
  have bodyAtFinal' : RuntimeTyping signature
      ((bindings.applySubst finalSubst).toContext ++
        context.applySubst finalSubst)
      body (finalSubst.apply bodyTarget) := by
    simpa only [NamedContext.applySubst_append,
      MonoCtx.toContext_applySubst] using bodyAtFinal
  simpa only [Subst.apply_listT] using
    RuntimeTyping.matchAll targetAtFinal (.ofTerminal patternAtFinal)
      matcherAtFinal' bodyAtFinal'

end DDSynthOrigin
end TypePM
