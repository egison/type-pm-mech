import TypePM.DemandTypingRuntimeErasurePatterns
import TypePM.DemandTypingRuntimeErasurePurePatterns
import TypePM.DemandTypingRuntimeErasureExpr

/-! # Later-cut erasure for expression-independent user-pattern fragments -/

namespace TypePM

theorem DDAlignDualWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : Dual}
    (aligned : DDAlignDualWithLedger ledger S left right S') :
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

theorem DDAlignBindingsWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S S' : Subst}
    {left right : MonoCtx}
    (aligned : DDAlignBindingsWithLedger ledger S left right S') :
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

private theorem liftDualEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : Dual}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.applySubst S = right.applySubst S) :
    left.applySubst S' = right.applySubst S' := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Dual.applySubst_seq] using
    congrArg (Dual.applySubst post) equality

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

namespace DDPatternOrigin

def RuntimeErasureUnder
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

theorem runtimeErasureUnder_pvar
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {ledger : CapabilityOriginLedger}
    (missing : name ∉ bindings.names)
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    RuntimeErasureUnder
      (@DDPatternOrigin.pvar signature S context parameters q S context
        parameters bindings name ledger missing) := by
  intro final finalSubst post finalLedger equation admissible
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.pvar (prevailing := finalSubst)
      (actualContext := context.applySubst finalSubst)
      missing freshCap freshTy)

theorem runtimeErasureUnder_wild
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {ledger : CapabilityOriginLedger}
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    RuntimeErasureUnder
      (DDPatternOrigin.wild (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.wild (prevailing := finalSubst)
      (actualContext := context.applySubst finalSubst) freshCap freshTy)

theorem runtimeErasureUnder_embed
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {dual : Dual} {ledger : CapabilityOriginLedger}
    (lookup : parameters.find? name = some dual) :
    RuntimeErasureUnder
      (@DDPatternOrigin.embed signature q S context bindings q S context
        parameters bindings name dual ledger lookup) := by
  intro final finalSubst post finalLedger equation admissible
  apply TerminalPatternResolution.embed
    (rawContext := context) (rawParameters := parameters)
    (rawBindings := bindings) (actualContext := context.applySubst finalSubst)
    (prevailing := finalSubst) lookup
  rw [PatternCtx.find?_applySubst, lookup]
  rfl

theorem runtimeErasureUnder_pval_of_expression
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {expression : Expr} {target : Ty} {q₁ : InferenceBase.FreshSupply}
    {S₁ : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {expressionRaw : DDSynth signature q S
      (bindings.toContext ++ context) expression target q₁ S₁}
    (expressionOrigin : DDSynthOrigin signature expressionRaw ledger ledger₁)
    (expressionUnder : DDSynthOrigin.RuntimeErasureUnder expressionOrigin)
    (freshCap : FreshCap signature context parameters bindings
      ⟨q₁.nextCap⟩)
    (separate : ⟨q₁.nextCap⟩ ∉ target.fcv) :
    RuntimeErasureUnder
      (@DDPatternOrigin.pval signature parameters q S context parameters
        bindings expression target q₁ S₁ ledger ledger₁ expressionRaw
        expressionOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have expressionAdmissible := admissible_before_markFreshCap admissible
  have expressionAtFinal := expressionUnder terminalEquation
    expressionAdmissible
  have expressionAtFinal' : RuntimeTyping signature
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

def RuntimeErasureUnder
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

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDPatternsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  exact TerminalPatternResolutions.nil

theorem runtimeErasureUnder_cons
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
    (headUnder : DDPatternOrigin.RuntimeErasureUnder headOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (tailFactor : DDErasure.StateFactorization q₁ S₁ ledger₁ q' S'
      ledger') :
    RuntimeErasureUnder (DDPatternsOrigin.cons headOrigin tailOrigin) := by
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

theorem runtimeErasureUnder_ptuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DDPatterns signature q S context parameters bindings patterns
      duals bindings' q' S'}
    (childrenOrigin : DDPatternsOrigin signature children ledger ledger')
    (childrenUnder : DDPatternsOrigin.RuntimeErasureUnder childrenOrigin) :
    RuntimeErasureUnder (DDPatternOrigin.ptuple childrenOrigin) := by
  intro final finalSubst post finalLedger equation admissible
  have childrenAtFinal := childrenUnder equation admissible
  simpa only [Dual.map_cap_applySubst, Dual.map_target_applySubst,
    Cap.apply_prod, Cap.applyList_eq_map, Subst.apply_prod] using
    TerminalPatternResolution.tuple childrenAtFinal

end DDPatternOrigin

namespace DDArmsOrigin

def RuntimeErasureUnder
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

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ppBindings : MonoCtx) (clauseTarget bodyTarget : Ty)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDArmsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ppBindings := ppBindings)
        (clauseTarget := clauseTarget) (bodyTarget := bodyTarget)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger equation admissible
  exact ArmsTy.nil

theorem runtimeErasureUnder_cons
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
    {bodyRaw : DDCheck signature q₁ S₁
      (armBindings.toContext ++ ppBindings.toContext ++ context) body
      bodyTarget q₂ S₂}
    (bodyOrigin : DDCheckOrigin signature bodyRaw ledger₁ ledger₂)
    {tailRaw : DDArms signature q₂ S₂ context ppBindings arms
      clauseTarget bodyTarget q' S'}
    (tailOrigin : DDArmsOrigin signature tailRaw ledger₂ ledger')
    (patternUnder : DDDPatOrigin.RuntimeErasureUnder patternOrigin)
    (bodyUnder : DDCheckOrigin.RuntimeErasureUnder bodyOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (bodyFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q₂ S₂ ledger₂)
    (tailFactorization : DDErasure.StateFactorization q₂ S₂ ledger₂
      q' S' ledger') :
    RuntimeErasureUnder
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
  have bodyAtFinal' : RuntimeTyping signature
      ((armBindings.applySubst finalSubst).toContext ++
        (ppBindings.applySubst finalSubst).toContext ++
        context.applySubst finalSubst)
      body (finalSubst.apply bodyTarget) := by
    simpa only [Context.applySubst_append,
      MonoCtx.toContext_applySubst] using bodyAtFinal
  exact ArmsTy.cons (ArmTy.mk patternAtFinal bodyAtFinal') tailAtFinal

end DDArmsOrigin

namespace DDClausesOrigin

def RuntimeErasureUnderAt
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
    ClausesTy signature finalSubst (context.applySubst finalSubst) clauses
      capability (finalSubst.apply sharedTarget) evidences

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (sharedTarget : Ty) (ledger : CapabilityOriginLedger)
    (capability : Cap) :
    RuntimeErasureUnderAt
      (DDClausesOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (sharedTarget := sharedTarget) (ledger := ledger))
      capability [] := by
  intro final finalSubst post finalLedger equation admissible
  exact ClausesTy.nil

end DDClausesOrigin

end TypePM
