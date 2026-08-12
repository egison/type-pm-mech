import TypePM.DemandTypingInvariantErasurePatterns
import TypePM.DemandTypingInvariantErasurePurePatterns
import TypePM.DemandTypingInvariantErasureExpr

/-! # Later-cut erasure for expression-independent user-pattern fragments -/

namespace TypePM

theorem DemandAlignDualWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : Dual}
    (aligned : DemandAlignDualWithLedger ledger S left right S') :
    left.applySubst S' = right.applySubst S' := by
  cases aligned with
  | mk capSafe targetsAligned =>
      rename_i capDelta
      have capAtMiddle :
          (Subst.seq ⟨capDelta, TySubst.id⟩ S).apply
              (.matcher left.cap .unit) =
            (Subst.seq ⟨capDelta, TySubst.id⟩ S).apply
              (.matcher right.cap .unit) := by
        simp only [Subst.apply_matcher, Subst.apply_unit]
        change Ty.matcher (left.cap.apply (CapSubst.comp capDelta S.cap))
            .unit =
          Ty.matcher (right.cap.apply (CapSubst.comp capDelta S.cap)) .unit
        rw [Cap.apply_comp, Cap.apply_comp]
        exact congrArg (fun capability => Ty.matcher capability .unit)
          capSafe.exact.1.1
      have capAtFinal := targetsAligned.erase.replayExtends.apply_eq capAtMiddle
      have capEquality : left.cap.apply S'.cap = right.cap.apply S'.cap := by
        exact (Ty.matcher.inj capAtFinal).1
      have targetEquality := targetsAligned.output_equal
      cases left
      cases right
      simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality ⊢
      rw [capEquality, targetEquality]

theorem DemandAlignBindingsWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : MonoCtx}
    (aligned : DemandAlignBindingsWithLedger ledger S left right S') :
    left.applySubst S' = right.applySubst S' := by
  induction aligned with
  | nil => rfl
  | @cons S leftEntry rightEntry lefts rights S₁ S' names head tail ih =>
      have headAtFinal := tail.erase.replayExtends.apply_eq head.output_equal
      simp only [MonoCtx.applySubst, List.map_cons]
      have entryEquality :
          (leftEntry.1, S'.apply leftEntry.2) =
            (rightEntry.1, S'.apply rightEntry.2) := by
        exact Prod.ext names headAtFinal
      rw [entryEquality]
      congr 1

theorem ReplayExtends.applyDual_eq
    {earlier later : Subst} {left right : Dual}
    (extension : ReplayExtends earlier later)
    (equality : left.applySubst earlier = right.applySubst earlier) :
    left.applySubst later = right.applySubst later := by
  have capAtEarlier := congrArg Dual.cap equality
  have targetAtEarlier := congrArg Dual.target equality
  simp only [Dual.applySubst, Dual.apply] at capAtEarlier targetAtEarlier
  have capAtLaterTy := extension.apply_eq
    (left := Ty.matcher left.cap .unit) (right := Ty.matcher right.cap .unit)
    (by simpa only [Subst.apply_matcher, Subst.apply_unit] using
      congrArg (fun capability => Ty.matcher capability .unit) capAtEarlier)
  have capAtLater : left.cap.apply later.cap = right.cap.apply later.cap :=
    (Ty.matcher.inj capAtLaterTy).1
  have targetAtLater := extension.apply_eq targetAtEarlier
  cases left
  cases right
  simp only [Dual.applySubst, Dual.apply] at capAtLater targetAtLater ⊢
  rw [capAtLater, targetAtLater]

theorem DemandAlignDualListWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : List Dual}
    (aligned : DemandAlignDualListWithLedger ledger S left right S') :
    left.map (Dual.applySubst S') = right.map (Dual.applySubst S') := by
  induction aligned with
  | nil => rfl
  | cons head tail ih =>
      have headAtFinal := tail.erase.replayExtends.applyDual_eq
        head.output_equal
      simp only [List.map_cons]
      rw [headAtFinal, ih]

theorem DemandAlignTargetListWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {duals : List Dual} {targets : List Ty}
    (aligned : DemandAlignTargetListWithLedger ledger S duals targets S') :
    (duals.map Dual.target).map S'.apply = targets.map S'.apply := by
  induction aligned with
  | nil => rfl
  | cons head tail ih =>
      have headAtFinal := tail.erase.replayExtends.apply_eq head.output_equal
      simp only [List.map_cons]
      rw [headAtFinal, ih]

private theorem liftDualEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : Dual}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.applySubst S = right.applySubst S) :
    left.applySubst S' = right.applySubst S' := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Dual.applySubst_seq] using
    congrArg (Dual.applySubst post) equality

private theorem liftDualListEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : List Dual}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.map (Dual.applySubst S) =
      right.map (Dual.applySubst S)) :
    left.map (Dual.applySubst S') = right.map (Dual.applySubst S') := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Dual.map_applySubst_seq] using
    congrArg (List.map (Dual.applySubst post)) equality

private theorem liftTyListEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : List Ty}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.map S.apply = right.map S.apply) :
    left.map S'.apply = right.map S'.apply := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Subst.map_apply_seq] using
    congrArg (List.map post.apply) equality

private theorem liftBindingsEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : MonoCtx}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.applySubst S = right.applySubst S) :
    left.applySubst S' = right.applySubst S' := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [MonoCtx.applySubst_seq] using
    congrArg (MonoCtx.applySubst post) equality

private theorem admissible_before_markFreshCap
    {q final : InferenceBase.FreshSupply} {post : Subst}
    {ledger finalLedger : CapabilityOriginLedger}
    (admissible : DDErasure.AdmissiblePostBetween
      { q with nextCap := q.nextCap + 1 } final
      (DDLedger.markFreshCap ledger q) finalLedger post) :
    DDErasure.AdmissiblePostBetween q final ledger finalLedger post := by
  have allocation := DDErasure.AdmissiblePostBetween.ofTransition
    (SupplyExtends.bumpCap q 1)
    (DDLedger.RefinesBelow.markFreshCap q ledger)
  simpa only [Subst.seq_id_right] using allocation.seq admissible

private theorem freezeExportFactorization
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} (capImages : List CapVar)
    (payload : Ty) :
    DDErasure.StateFactorization q S ledger q S
      (DDLedger.freezeExport ledger S capImages payload) :=
  DDErasure.StateFactorization.ofTransition
    (SupplyExtends.refl q)
    (DDLedger.RefinesBelow.freezeExport q ledger S capImages payload)

private theorem closedDualSchemeInstanceUnder
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    {q : InferenceBase.FreshSupply} {S : Subst}
    (Sb : S.BoundedBy q)
    {final : InferenceBase.FreshSupply} {finalSubst : Subst}
    {ledger finalLedger : CapabilityOriginLedger}
    (factorization : DDErasure.StateFactorization
      (InferenceBase.instantiateDualScheme q scheme).supply S
      (DDLedger.markDualInstance ledger q scheme)
      final finalSubst finalLedger) :
    scheme.ValueFlowInst
      ((InferenceBase.instantiateDualScheme q scheme).value.1.map
        (Dual.applySubst finalSubst))
      ((InferenceBase.instantiateDualScheme q scheme).value.2.applySubst
        finalSubst) := by
  rcases factorization with ⟨post, terminalEquation, admissible⟩
  apply (DualScheme.instantiateVariableInstAt q scheme).transportResult
  · intro varId membership
    rw [(closed.patternFuns lookup).1] at membership
    contradiction
  · intro varId membership
    rw [(closed.patternFuns lookup).2] at membership
    contradiction
  · intro binder binderMem image imageEquation
    have canonicalEquation :
        (InferenceBase.instantiateDualScheme q scheme).subst.cap binder =
          .var ⟨q.nextCap + binder.id⟩ := by
      simp [InferenceBase.instantiateDualScheme,
        InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
        binderMem]
    have imageEquality : image = ⟨q.nextCap + binder.id⟩ := by
      rw [canonicalEquation] at imageEquation
      exact Cap.var.inj imageEquation.symm
    subst image
    rcases admissible.dualInstanceImageVariable binderMem with
      ⟨finalImage, postEquation⟩
    refine ⟨finalImage, ?_⟩
    rw [terminalEquation]
    change (S.cap ⟨q.nextCap + binder.id⟩).apply post.cap =
      .var finalImage
    rw [Sb.capFixedAbove ⟨q.nextCap + binder.id⟩
      (Nat.le_add_right q.nextCap binder.id)]
    simpa only [Cap.apply] using postEquation

private theorem closedPatternCtorInstance
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String}
    {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (q : InferenceBase.FreshSupply) (post : Subst) :
    entry.Inst
      ((InferenceBase.instantiateCtorScheme q entry.scheme).value.1.map
        post.apply)
      (post.apply
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2) := by
  apply CtorScheme.Inst.transport
    (InferenceBase.instantiateCtorScheme_sound q entry.scheme)
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    rw [(closed.patternCtors lookup).1] at membership
    contradiction
  · intro varId membership
    rw [(closed.patternCtors lookup).2] at membership
    contradiction

namespace DDPatternOrigin

def TypingInvariantErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    TerminalPatternResolution signature finalSubst
      (context.applySubst finalSubst) (parameters.applySubst finalSubst)
      (bindingsIn.applySubst finalSubst) pattern
      (dual.cap.apply finalSubst.cap) (finalSubst.apply dual.target)
      (bindingsOut.applySubst finalSubst)

theorem typingInvariantErasureUnder_pvar
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {ledger : CapabilityOriginLedger}
    (missing : name ∉ bindings.names)
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    TypingInvariantErasureUnder
      (@DDPatternOrigin.pvar signature q S context parameters bindings name
        ledger missing) := by
  intro final finalSubst post finalLedger equation admissible
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.pvar (prevailing := finalSubst)
      (actualContext := context.applySubst finalSubst)
      missing freshCap freshTy)

theorem typingInvariantErasureUnder_wild
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {ledger : CapabilityOriginLedger}
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    TypingInvariantErasureUnder
      (DDPatternOrigin.wild (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.wild (prevailing := finalSubst)
      (actualContext := context.applySubst finalSubst) freshCap freshTy)

theorem typingInvariantErasureUnder_embed
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {dual : Dual} {ledger : CapabilityOriginLedger}
    (lookup : parameters.find? name = some dual) :
    TypingInvariantErasureUnder
      (@DDPatternOrigin.embed signature q S context bindings q S context
        parameters bindings name dual ledger lookup) := by
  intro final finalSubst post finalLedger equation admissible
  apply TerminalPatternResolution.embed
    (rawContext := context) (rawParameters := parameters)
    (rawBindings := bindings) (actualContext := context.applySubst finalSubst)
    (prevailing := finalSubst) lookup
  rw [PatternCtx.find?_applySubst, lookup]
  rfl

theorem typingInvariantErasureUnder_pval_of_expression
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {expression : Expr} {target : Ty} {q₁ : InferenceBase.FreshSupply}
    {S₁ : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {expressionRaw : DemandSynth signature q S
      (bindings.toContext ++ context) expression target q₁ S₁}
    (expressionOrigin : DemandSynthOrigin signature expressionRaw ledger ledger₁)
    (expressionUnder : DemandSynthOrigin.TypingInvariantErasureUnder expressionOrigin)
    (freshCap : FreshCap signature context parameters bindings
      ⟨q₁.nextCap⟩)
    (separate : ⟨q₁.nextCap⟩ ∉ target.fcv) :
    TypingInvariantErasureUnder
      (@DDPatternOrigin.pval signature parameters q S context parameters
        bindings expression target q₁ S₁ ledger ledger₁ expressionRaw
        expressionOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have expressionAdmissible := admissible_before_markFreshCap admissible
  have expressionAtFinal := expressionUnder terminalEquation
    expressionAdmissible
  have expressionAtFinal' : TypingInvariant signature
      ((bindings.applySubst finalSubst).toContext ++
        context.applySubst finalSubst)
      expression (finalSubst.apply target) := by
    simpa only [Context.applySubst_append,
      MonoCtx.toContext_applySubst] using expressionAtFinal
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.pval (prevailing := finalSubst)
      (actualContext := context.applySubst finalSubst) freshCap separate
      expressionAtFinal')

end DDPatternOrigin

namespace DDPatternsOrigin

def TypingInvariantErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternsOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    TerminalPatternResolutions signature finalSubst
      (context.applySubst finalSubst) (parameters.applySubst finalSubst)
      (bindingsIn.applySubst finalSubst) patterns
      (duals.map (Dual.applySubst finalSubst))
      (bindingsOut.applySubst finalSubst)

theorem typingInvariantErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (ledger : CapabilityOriginLedger) :
    TypingInvariantErasureUnder
      (DDPatternsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  exact TerminalPatternResolutions.nil

theorem typingInvariantErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {pattern : Pattern} {patterns : List Pattern} {dual : Dual}
    {duals : List Dual} {bindings₁ : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {bindings' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDPattern signature q S context parameters bindings pattern dual
      bindings₁ q₁ S₁}
    {tail : DDPatterns signature q₁ S₁ context parameters bindings₁
      patterns duals bindings' q' S'}
    (headOrigin : DDPatternOrigin signature head ledger ledger₁)
    (tailOrigin : DDPatternsOrigin signature tail ledger₁ ledger')
    (headUnder : DDPatternOrigin.TypingInvariantErasureUnder headOrigin)
    (tailUnder : TypingInvariantErasureUnder tailOrigin)
    (tailFactor : DDErasure.StateFactorization q₁ S₁ ledger₁ q' S'
      ledger') :
    TypingInvariantErasureUnder (DDPatternsOrigin.cons headOrigin tailOrigin) := by
  intro final finalSubst post finalLedger equation admissible
  rcases tailFactor with ⟨tailPost, tailEquation, tailAdmissible⟩
  have combinedEquation : finalSubst =
      Subst.seq (Subst.seq post tailPost) S₁ := by
    rw [equation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S₁
  have headFinal := headUnder combinedEquation (tailAdmissible.seq admissible)
  have tailFinal := tailUnder equation admissible
  simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
    TerminalPatternResolutions.cons headFinal tailFinal

end DDPatternsOrigin

namespace DDPatternOrigin

theorem typingInvariantErasureUnder_ptuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DDPatterns signature q S context parameters bindings patterns
      duals bindings' q' S'}
    (childrenOrigin : DDPatternsOrigin signature children ledger ledger')
    (childrenUnder : DDPatternsOrigin.TypingInvariantErasureUnder childrenOrigin) :
    TypingInvariantErasureUnder (DDPatternOrigin.ptuple childrenOrigin) := by
  intro final finalSubst post finalLedger equation admissible
  have childrenAtFinal := childrenUnder equation admissible
  simpa only [Dual.map_cap_applySubst, Dual.map_target_applySubst,
    Cap.apply_prod, Cap.applyList_eq_map, Subst.apply_prod] using
    TerminalPatternResolution.tuple childrenAtFinal

theorem typingInvariantErasureUnder_pand_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {left right : Pattern} {leftDual : Dual} {leftBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {rightDual : Dual}
    {bindings' : MonoCtx} {q₂ : InferenceBase.FreshSupply} {S₂ S' : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {leftRaw : DDPattern signature q S context parameters bindings left
      leftDual leftBindings q₁ S₁}
    (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
    {rightRaw : DDPattern signature q₁ S₁ context parameters leftBindings
      right rightDual bindings' q₂ S₂}
    (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
    (aligned : DemandAlignDualWithLedger ledger₂ S₂ leftDual rightDual S')
    (leftUnder : TypingInvariantErasureUnder leftOrigin)
    (rightUnder : TypingInvariantErasureUnder rightOrigin)
    (rightFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₂ S₂ ledger₂)
    (alignmentFactorization : DDErasure.StateFactorization q₂ S₂ ledger₂
      q₂ S' ledger₂) :
    TypingInvariantErasureUnder
      (DDPatternOrigin.pand leftOrigin rightOrigin aligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  let later : DDErasure.StateFactorization q₂ S' ledger₂ final
      finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  rcases (rightFactorization.trans alignmentFactorization).trans later with
    ⟨leftPost, leftEquation, leftAdmissible⟩
  have leftAtFinal := leftUnder leftEquation leftAdmissible
  rcases alignmentFactorization.trans later with
    ⟨rightPost, rightEquation, rightAdmissible⟩
  have rightAtFinal := rightUnder rightEquation rightAdmissible
  have dualEquality := liftDualEquality later aligned.output_equal
  have capEquality := congrArg Dual.cap dualEquality
  have targetEquality := congrArg Dual.target dualEquality
  simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality
  rw [← capEquality, ← targetEquality] at rightAtFinal
  exact TerminalPatternResolution.and leftAtFinal rightAtFinal

theorem typingInvariantErasureUnder_por_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {left right : Pattern} {leftDual : Dual} {leftBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {rightDual : Dual}
    {rightBindings : MonoCtx} {q₂ : InferenceBase.FreshSupply}
    {S₂ S₃ S' : Subst} {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    {leftRaw : DDPattern signature q S context parameters bindings left
      leftDual leftBindings q₁ S₁}
    (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
    {rightRaw : DDPattern signature q₁ S₁ context parameters bindings
      right rightDual rightBindings q₂ S₂}
    (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
    (dualsAligned : DemandAlignDualWithLedger ledger₂ S₂ leftDual rightDual S₃)
    (bindingsAligned : DemandAlignBindingsWithLedger ledger₂ S₃
      leftBindings rightBindings S')
    (leftUnder : TypingInvariantErasureUnder leftOrigin)
    (rightUnder : TypingInvariantErasureUnder rightOrigin)
    (rightFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₂ S₂ ledger₂)
    (dualsFactorization : DDErasure.StateFactorization q₂ S₂ ledger₂
      q₂ S₃ ledger₂)
    (bindingsFactorization : DDErasure.StateFactorization q₂ S₃ ledger₂
      q₂ S' ledger₂) :
    TypingInvariantErasureUnder
      (DDPatternOrigin.por leftOrigin rightOrigin dualsAligned
        bindingsAligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  let later : DDErasure.StateFactorization q₂ S' ledger₂ final
      finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  rcases (((rightFactorization.trans dualsFactorization).trans
      bindingsFactorization).trans later) with
    ⟨leftPost, leftEquation, leftAdmissible⟩
  have leftAtFinal := leftUnder leftEquation leftAdmissible
  rcases ((dualsFactorization.trans bindingsFactorization).trans later) with
    ⟨rightPost, rightEquation, rightAdmissible⟩
  have rightAtFinal := rightUnder rightEquation rightAdmissible
  have dualEquality := liftDualEquality
    (bindingsFactorization.trans later) dualsAligned.output_equal
  have bindingsEquality := liftBindingsEquality later
    bindingsAligned.output_equal
  have capEquality := congrArg Dual.cap dualEquality
  have targetEquality := congrArg Dual.target dualEquality
  simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality
  rw [← capEquality, ← targetEquality, ← bindingsEquality] at rightAtFinal
  exact TerminalPatternResolution.or leftAtFinal rightAtFinal

theorem typingInvariantErasureUnder_papp_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {patterns : List Pattern} {scheme : DualScheme}
    {duals : List Dual} {bindings' : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    (lookup : signature.findPatternFun name = some scheme)
    {children : DDPatterns signature
      (InferenceBase.instantiateDualScheme q scheme).supply S context
      parameters bindings patterns duals bindings' q₁ S₁}
    (childrenOrigin : DDPatternsOrigin signature children
      (DDLedger.markDualInstance ledger q scheme) ledger₁)
    (aligned : DemandAlignDualListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateDualScheme q scheme).value.1 S')
    (childrenUnder : DDPatternsOrigin.TypingInvariantErasureUnder childrenOrigin)
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateDualScheme q scheme).supply S
      (DDLedger.markDualInstance ledger q scheme) q₁ S₁ ledger₁)
    (alignmentFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₁ S' ledger₁)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q) :
    TypingInvariantErasureUnder
      (DDPatternOrigin.papp lookup childrenOrigin aligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  let later : DDErasure.StateFactorization q₁ S' ledger₁ final
      finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  rcases alignmentFactorization.trans later with
    ⟨childrenPost, childrenEquation, childrenAdmissible⟩
  have childrenAtFinal := childrenUnder childrenEquation childrenAdmissible
  have dualEquality := liftDualListEquality later aligned.output_equal
  have instanceAtFinal := closedDualSchemeInstanceUnder closed lookup Sb
    ((childrenFactorization.trans alignmentFactorization).trans later)
  rw [← dualEquality] at instanceAtFinal
  exact TerminalPatternResolution.app lookup childrenAtFinal instanceAtFinal

theorem typingInvariantErasureUnder_pctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {patterns : List Pattern}
    {entry : PatternCtorScheme signature.observability}
    {duals : List Dual} {bindings' : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
    {capability : Cap} {q₂ : InferenceBase.FreshSupply} {S₃ : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findPatternCtor name = some entry)
    {children : DDPatterns signature
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S context
      parameters bindings patterns duals bindings' q₁ S₁}
    (childrenOrigin : DDPatternsOrigin signature children
      (DDLedger.markCtorInstance ledger q entry.scheme) ledger₁)
    (targetsAligned : DemandAlignTargetListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂)
    {capRaw : DDPatternCtorCap signature entry q₁ S₂
      (duals.map Dual.cap) capability q₂ S₃}
    (capOrigin : DDPatternCtorCapOrigin signature entry capRaw ledger₁ ledger₂)
    (compatibleCheck : Inference.capCompatibleCheck entry
      ((duals.map Dual.cap).map fun child => child.apply S₃.cap)
      (capability.apply S₃.cap) = true)
    (childrenUnder : DDPatternsOrigin.TypingInvariantErasureUnder childrenOrigin)
    (targetsFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₁ S₂ ledger₁)
    (capFactorization : DDErasure.StateFactorization q₁ S₂ ledger₁
      q₂ S₃ ledger₂)
    (closed : signature.SchemesClosed)
    (compatibleUnder :
      ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
          {finalLedger : CapabilityOriginLedger},
        finalSubst = Subst.seq post S₃ →
        DDErasure.AdmissiblePostBetween q₂ final
          (DDLedger.freezeExport ledger₂ S₃
            (Inference.freshCapImages q entry.scheme.capBinders)
            (Inference.capabilityExportPayload [capability]
              ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
                bindings'.map fun binding => binding.2)))
          finalLedger post →
        entry.CapCompatible
          ((duals.map (Dual.applySubst finalSubst)).map Dual.cap)
          (capability.apply finalSubst.cap)) :
    TypingInvariantErasureUnder
      (DDPatternOrigin.pctor lookup childrenOrigin targetsAligned capOrigin
        compatibleCheck) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have freezing := freezeExportFactorization
    (q := q₂) (S := S₃) (ledger := ledger₂)
    (Inference.freshCapImages q entry.scheme.capBinders)
    (Inference.capabilityExportPayload [capability]
      ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
        bindings'.map fun binding => binding.2))
  let later : DDErasure.StateFactorization q₂ S₃
      (DDLedger.freezeExport ledger₂ S₃
        (Inference.freshCapImages q entry.scheme.capBinders)
        (Inference.capabilityExportPayload [capability]
          ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
            bindings'.map fun binding => binding.2)))
      final finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  rcases (((targetsFactorization.trans capFactorization).trans freezing).trans
      later) with ⟨childrenPost, childrenEquation, childrenAdmissible⟩
  have childrenAtFinal := childrenUnder childrenEquation childrenAdmissible
  have targetEquality := liftTyListEquality
    ((capFactorization.trans freezing).trans later)
    targetsAligned.output_equal
  have instanceAtFinal := closedPatternCtorInstance closed lookup q finalSubst
  rw [← targetEquality] at instanceAtFinal
  have compatibleAtFinal := compatibleUnder terminalEquation admissible
  change TerminalPatternResolution signature finalSubst
    (context.applySubst finalSubst) (parameters.applySubst finalSubst)
    (bindings.applySubst finalSubst) (.pctor name patterns)
    (capability.apply finalSubst.cap)
    (finalSubst.apply
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2)
    (bindings'.applySubst finalSubst)
  exact TerminalPatternResolution.ctor
    (result := ⟨capability.apply finalSubst.cap,
      finalSubst.apply
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2⟩)
    lookup childrenAtFinal compatibleAtFinal
      (by simpa only [Dual.map_target_applySubst] using instanceAtFinal)

end DDPatternOrigin

namespace DDArmsOrigin

def TypingInvariantErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDArms signature q S context ppBindings arms
      clauseTarget bodyTarget q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDArmsOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    ArmsTy signature (context.applySubst finalSubst)
      (finalSubst.apply clauseTarget) (ppBindings.applySubst finalSubst)
      (finalSubst.apply bodyTarget) arms

theorem typingInvariantErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ppBindings : MonoCtx) (clauseTarget bodyTarget : Ty)
    (ledger : CapabilityOriginLedger) :
    TypingInvariantErasureUnder
      (DDArmsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ppBindings := ppBindings)
        (clauseTarget := clauseTarget) (bodyTarget := bodyTarget)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  exact ArmsTy.nil

theorem typingInvariantErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {dataPattern : DPat}
    {body : Expr} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {armBindings : MonoCtx} {q₁ q₂ q' : InferenceBase.FreshSupply}
    {S₁ S₂ S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {patternRaw : DDDPat signature q S dataPattern clauseTarget armBindings
      q₁ S₁}
    (patternOrigin : DDDPatOrigin signature patternRaw ledger ledger₁)
    (disjoint : ∀ name, name ∈ armBindings.names →
      name ∉ ppBindings.names)
    {bodyRaw : DemandCheck signature q₁ S₁
      (armBindings.toContext ++ ppBindings.toContext ++ context) body
      bodyTarget q₂ S₂}
    (bodyOrigin : DemandCheckOrigin signature bodyRaw ledger₁ ledger₂)
    {tailRaw : DDArms signature q₂ S₂ context ppBindings arms
      clauseTarget bodyTarget q' S'}
    (tailOrigin : DDArmsOrigin signature tailRaw ledger₂ ledger')
    (patternUnder : DDDPatOrigin.TypingInvariantErasureUnder patternOrigin)
    (bodyUnder : DemandCheckOrigin.TypingInvariantErasureUnder bodyOrigin)
    (tailUnder : TypingInvariantErasureUnder tailOrigin)
    (bodyFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₂ S₂ ledger₂)
    (tailFactorization : DDErasure.StateFactorization q₂ S₂ ledger₂
      q' S' ledger') :
    TypingInvariantErasureUnder
      (DDArmsOrigin.cons patternOrigin disjoint bodyOrigin tailOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  rcases tailFactorization with ⟨tailPost, tailEquation, tailAdmissible⟩
  have bodyEquation : finalSubst =
      Subst.seq (Subst.seq post tailPost) S₂ := by
    rw [terminalEquation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S₂
  have bodyAtFinal := bodyUnder bodyEquation
    (tailAdmissible.seq admissible)
  rcases bodyFactorization with ⟨bodyPost, bodyFactorEquation,
    bodyFactorAdmissible⟩
  have patternEquation : finalSubst =
      Subst.seq (Subst.seq (Subst.seq post tailPost) bodyPost) S₁ := by
    rw [bodyEquation, bodyFactorEquation]
    exact PhasedPost.seq_assoc (Subst.seq post tailPost) bodyPost S₁
  have patternAtFinal := patternUnder patternEquation
    (bodyFactorAdmissible.seq (tailAdmissible.seq admissible))
  have tailAtFinal := tailUnder terminalEquation admissible
  have bodyAtFinal' : TypingInvariant signature
      ((armBindings.applySubst finalSubst).toContext ++
        (ppBindings.applySubst finalSubst).toContext ++
        context.applySubst finalSubst)
      body (finalSubst.apply bodyTarget) := by
    simpa only [Context.applySubst_append,
      MonoCtx.toContext_applySubst] using bodyAtFinal
  exact ArmsTy.cons (ArmTy.mk patternAtFinal bodyAtFinal') tailAtFinal

end DDArmsOrigin

private theorem subst_eq_seq_id (S : Subst) :
    S = Subst.seq Subst.id S := by
  apply PhasedPost.subst_ext
  · funext varId
    exact (Cap.apply_id (S.cap varId)).symm
  · funext varId
    exact (Subst.apply_id (S.target varId)).symm

namespace DDClauseOrigin

/-- Later-cut erasure for one clause, parameterized by the two pieces of
matcher-finalization evidence that are deliberately absent from `DDClause`:
the selected matcher capability and the clause shape evidence. -/
def TypingInvariantErasureUnderAt
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClauseOrigin signature raw ledger ledger')
    (capability : Cap) (evidence : Shape.Evidence) : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    PPatCapsAt signature true clause.pp
      ((holes.map (Dual.applySubst finalSubst)).map Dual.cap) capability →
    clauseEvidence signature.toMatcherSig clause.pp
      ((holes.map (Dual.applySubst finalSubst)).map Dual.cap) = some evidence →
    ClauseTy signature finalSubst (context.applySubst finalSubst) clause
      capability (finalSubst.apply sharedTarget) evidence

/-- Specialize the later-cut invariant to the clause's own terminal cut. -/
theorem typingInvariantErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    {capability : Cap} {evidence : Shape.Evidence}
    (under : TypingInvariantErasureUnderAt origin capability evidence)
    (caps : PPatCapsAt signature true clause.pp
      ((holes.map (Dual.applySubst S')).map Dual.cap) capability)
    (shape : clauseEvidence signature.toMatcherSig clause.pp
      ((holes.map (Dual.applySubst S')).map Dual.cap) = some evidence) :
    DDClauseOrigin.TypingInvariantErasureAt origin capability evidence := by
  exact under (final := q') (post := Subst.id) (finalLedger := ledger')
    (subst_eq_seq_id S') (DDErasure.AdmissiblePostBetween.id q' ledger')
    caps shape

/-- A clause transports its primitive pattern and next-matchers across the
chronological suffixes ending at the arms cut.  Final capability and shape
evidence enter only at that common terminal cut. -/
theorem typingInvariantErasureUnder_mk
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {pp : PPat} {next : Expr} {arms : List Arm}
    {sharedTarget : Ty} {holes : List Dual} {ppBindings : MonoCtx}
    {nextMatchers : List Expr} {q₁ : InferenceBase.FreshSupply}
    {S₁ : Subst} {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {ppRaw : DDPPat signature q S pp sharedTarget holes ppBindings q₁ S₁}
    (ppOrigin : DDPPatOrigin signature ppRaw ledger ledger₁)
    (decomposed : decomposeME next holes.length = some nextMatchers)
    {nextRaw : DemandChecks signature q₁ S₁ context nextMatchers
      (holes.map fun hole => .slot hole.cap hole.target) q₂ S₂}
    (nextOrigin : DemandChecksOrigin signature nextRaw ledger₁ ledger₂)
    {armsRaw : DDArms signature q₂ S₂ context ppBindings arms
      sharedTarget (Ty.listT (prodTy (holes.map Dual.target))) q' S'}
    (armsOrigin : DDArmsOrigin signature armsRaw ledger₂ ledger')
    (ppUnder : DDPPatOrigin.TypingInvariantErasureUnder ppOrigin)
    (nextUnder : DemandChecksOrigin.TypingInvariantErasureUnder nextOrigin)
    (armsUnder : DDArmsOrigin.TypingInvariantErasureUnder armsOrigin)
    (nextFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₂ S₂ ledger₂)
    (armsFactorization : DDErasure.StateFactorization q₂ S₂ ledger₂
      q' S' ledger')
    {capability : Cap} {evidence : Shape.Evidence} :
    TypingInvariantErasureUnderAt
      (DDClauseOrigin.mk ppOrigin decomposed nextOrigin armsOrigin)
      capability evidence := by
  intro final finalSubst post finalLedger terminalEquation admissible
    capsAtFinal evidenceAtFinal
  rcases armsFactorization with ⟨armsPost, armsEquation, armsAdmissible⟩
  have nextEquation : finalSubst =
      Subst.seq (Subst.seq post armsPost) S₂ := by
    rw [terminalEquation, armsEquation]
    exact PhasedPost.seq_assoc post armsPost S₂
  have nextAtFinal := nextUnder nextEquation
    (armsAdmissible.seq admissible)
  rcases nextFactorization with
    ⟨nextPost, nextFactorEquation, nextFactorAdmissible⟩
  have ppEquation : finalSubst =
      Subst.seq (Subst.seq (Subst.seq post armsPost) nextPost) S₁ := by
    rw [nextEquation, nextFactorEquation]
    exact PhasedPost.seq_assoc (Subst.seq post armsPost) nextPost S₁
  have ppAtFinal := ppUnder ppEquation
    (nextFactorAdmissible.seq (armsAdmissible.seq admissible))
  have armsAtFinal := armsUnder terminalEquation admissible
  exact ClauseTy.mk (clauseEvidence_coreOrder evidenceAtFinal)
    (.ofTerminal ppAtFinal) capsAtFinal
    (by simpa using decomposed) (by
      simpa only [List.map_map, Function.comp_def, Subst.apply_slot,
        Dual.applySubst, Dual.apply]
        using nextAtFinal)
    (by simpa only [Subst.apply_listT, Subst.apply_prodTy,
      Dual.map_target_applySubst] using armsAtFinal)
    evidenceAtFinal

end DDClauseOrigin

namespace DDClausesOrigin

/-- Clause-list erasure consumes the capability/evidence audit performed by
matcher finalization at the same later cut. -/
def TypingInvariantErasureUnderAt
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDClauses signature q S context clauses sharedTarget
      holeLists q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClausesOrigin signature raw ledger ledger')
    (capability : Cap) (evidences : List Shape.Evidence) : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    Inference.ClauseCapsList signature clauses
      (terminalHoleCaps finalSubst holeLists) capability →
    Inference.ClauseEvidenceList signature.toMatcherSig clauses
      (terminalHoleCaps finalSubst holeLists) evidences →
    ClausesTy signature finalSubst (context.applySubst finalSubst) clauses
      capability (finalSubst.apply sharedTarget) evidences

/-- Specialize clause-list erasure to its own terminal finalization audit. -/
theorem typingInvariantErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDClauses signature q S context clauses sharedTarget
      holeLists q' S'} {ledger ledger' : CapabilityOriginLedger}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    {capability : Cap} {evidences : List Shape.Evidence}
    (under : TypingInvariantErasureUnderAt origin capability evidences)
    (caps : Inference.ClauseCapsList signature clauses
      (terminalHoleCaps S' holeLists) capability)
    (shape : Inference.ClauseEvidenceList signature.toMatcherSig clauses
      (terminalHoleCaps S' holeLists) evidences) :
    DDClausesOrigin.TypingInvariantErasureAt origin capability evidences := by
  exact under (final := q') (post := Subst.id) (finalLedger := ledger')
    (subst_eq_seq_id S') (DDErasure.AdmissiblePostBetween.id q' ledger')
    caps shape

theorem typingInvariantErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (sharedTarget : Ty) (ledger : CapabilityOriginLedger)
    (capability : Cap) :
    TypingInvariantErasureUnderAt
      (DDClausesOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (sharedTarget := sharedTarget) (ledger := ledger))
      capability [] := by
  intro final finalSubst post finalLedger equation admissible caps evidence
  cases caps
  cases evidence
  exact ClausesTy.nil

/-- A nonempty clause list transports the head across the tail traversal and
then consumes the matching head/tail finalization witnesses structurally. -/
theorem typingInvariantErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {clauses : List Clause}
    {sharedTarget : Ty} {holes : List Dual} {holeLists : List (List Dual)}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDClause signature q S context clause sharedTarget holes q₁ S₁}
    {tail : DDClauses signature q₁ S₁ context clauses sharedTarget
      holeLists q' S'}
    (headOrigin : DDClauseOrigin signature head ledger ledger₁)
    (tailOrigin : DDClausesOrigin signature tail ledger₁ ledger')
    (headUnder : DDClauseOrigin.TypingInvariantErasureUnderAt headOrigin capability
      evidence)
    (tailUnder : TypingInvariantErasureUnderAt tailOrigin capability evidences)
    (tailFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q' S' ledger') :
    TypingInvariantErasureUnderAt (DDClausesOrigin.cons headOrigin tailOrigin)
      capability (evidence :: evidences) := by
  intro final finalSubst post finalLedger terminalEquation admissible caps evs
  cases caps with
  | cons headCaps tailCaps =>
      cases evs with
      | cons headEvidence tailEvidence =>
          rcases tailFactorization with
            ⟨tailPost, tailEquation, tailAdmissible⟩
          have headEquation : finalSubst =
              Subst.seq (Subst.seq post tailPost) S₁ := by
            rw [terminalEquation, tailEquation]
            exact PhasedPost.seq_assoc post tailPost S₁
          have headAtFinal := headUnder headEquation
            (tailAdmissible.seq admissible) headCaps headEvidence
          have tailAtFinal := tailUnder terminalEquation admissible
            tailCaps tailEvidence
          exact ClausesTy.cons headAtFinal tailAtFinal

end DDClausesOrigin

namespace DemandSynthOrigin

/-- Matcher finalization obtains its shared clause certificate directly from
the later-cut clause invariant and the two executable finalization audits.
The only remaining matcher-local algebraic premise is fixedness of the
already-finalized producer capability. -/
theorem typingInvariantErasure_matcher_of_clause_invariant
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause}
    {rawHoleLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {evidence : List Shape.Evidence} {capability : Cap}
    {ledger ledger₁ : CapabilityOriginLedger}
    {clausesRaw : DDClauses signature
      { q with nextTy := q.nextTy + 1 } S context clauses
      (.var q.nextTy) rawHoleLists q' S'}
    (clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁)
    (collected : Inference.collectClauseEvidence signature.toMatcherSig
      clauses (terminalHoleCaps S' rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability)
    (clauseCaps : Inference.clauseCapsListCheck signature capability clauses
      (terminalHoleCaps S' rawHoleLists) = true)
    (catchAll : Inference.catchAllLastCheck clauses = true)
    (binders : Inference.matcherBindersCheck clauses = true)
    (arms : Inference.armExhaustiveCheck signature clauses
      (S'.apply (.var q.nextTy)) = true)
    (coverage : Inference.coverageCheck signature.toMatcherSig clauses
      capability = true)
    (clausesUnder : DDClausesOrigin.TypingInvariantErasureUnderAt clausesOrigin
      capability evidence)
    (capabilityFixed : capability.apply S'.cap = capability) :
    TypingInvariantErasure
      (DemandSynthOrigin.matcher clausesOrigin collected inferred clauseCaps
        catchAll binders arms coverage) := by
  have clausesAtTerminal : DDClausesOrigin.TypingInvariantErasureAt clausesOrigin
      capability evidence :=
    DDClausesOrigin.typingInvariantErasure_of_under (origin := clausesOrigin)
      clausesUnder (Inference.clauseCapsListCheck_sound clauseCaps)
      (Inference.collectClauseEvidence_sound collected)
  exact typingInvariantErasure_matcher_of_clauses clausesOrigin collected inferred
    clauseCaps catchAll binders arms coverage
    (ResolvedClausesTy.ofShared clausesAtTerminal) capabilityFixed

end DemandSynthOrigin

end TypePM
