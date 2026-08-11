import TypePM.DemandTypingOrigin
import TypePM.DemandTypingLedgerMetatheory

/-!
# Ledger evolution of intrinsic demand-typing certificates

Every origin certificate starts with a ledger whose explicit keys precede
the input supply.  Its constructors only allocate keys from fresh supply
ranges or freeze an already-recorded structural key.  Consequently the
output ledger is bounded by the output supply and refines the input policy
below the original cut.
-/

namespace TypePM
namespace DDLedger

/-- The two ledger invariants carried through an origin certificate. -/
def Evolution (q q' : InferenceBase.FreshSupply)
    (ledger ledger' : CapabilityOriginLedger) : Prop :=
  LedgerBelow q' ledger' ∧ RefinesBelow q ledger ledger'

theorem Evolution.ledgerBelow {q q' : InferenceBase.FreshSupply}
    {ledger ledger' : CapabilityOriginLedger}
    (evolution : Evolution q q' ledger ledger') : LedgerBelow q' ledger' :=
  evolution.1

theorem Evolution.refinesBelow {q q' : InferenceBase.FreshSupply}
    {ledger ledger' : CapabilityOriginLedger}
    (evolution : Evolution q q' ledger ledger') :
    RefinesBelow q ledger ledger' :=
  evolution.2

theorem LedgerBelow.mono {q q' : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger} (below : LedgerBelow q ledger)
    (extension : SupplyExtends q q') : LedgerBelow q' ledger := by
  intro varId membership
  exact Nat.lt_of_lt_of_le (below varId membership) extension.1

theorem RefinesBelow.restrict {q q' : InferenceBase.FreshSupply}
    {earlier later : CapabilityOriginLedger}
    (extension : SupplyExtends q q')
    (refines : RefinesBelow q' earlier later) :
    RefinesBelow q earlier later := by
  intro varId below
  exact refines varId (Nat.lt_of_lt_of_le below extension.1)

theorem Evolution.trans {q q₁ q₂ : InferenceBase.FreshSupply}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
    (extension : SupplyExtends q q₁)
    (first : Evolution q q₁ ledger ledger₁)
    (second : Evolution q₁ q₂ ledger₁ ledger₂) :
    Evolution q q₂ ledger ledger₂ :=
  ⟨second.1, first.2.trans (second.2.restrict extension)⟩

theorem Evolution.refl {q q' : InferenceBase.FreshSupply}
    {ledger : CapabilityOriginLedger}
    (below : LedgerBelow q ledger) (extension : SupplyExtends q q') :
    Evolution q q' ledger ledger :=
  ⟨below.mono extension, RefinesBelow.refl q ledger⟩

end DDLedger

open DDLedger

/-! ## Pattern-constructor capability projection -/

theorem DDPatternCtorCapOrigin.ledgerEvolution
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatternCtorCap signature entry q S childCaps capability q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternCtorCapOrigin signature entry raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | @DDPatternCtorCapOrigin.project _ _ _ _ _ _ _ _ _ projection
      freshened =>
      have extension := SupplyExtends.freshenSkeleton freshened
      ⟨LedgerBelow.markCapRange below extension.1,
        RefinesBelow.markCapRange _ _ _⟩
  | @DDPatternCtorCapOrigin.fallback _ _ _ _ _ resultVariables _ _ _ _ _ _
      _ _ _ aligned projectionHit freshened =>
      have firstExtends :=
        SupplyExtends.patternCtorAssignments resultVariables.eraseDups q
      have secondExtends :=
        SupplyExtends.freshenSkeleton freshened
      have firstBelow :=
        LedgerBelow.markCapRange below firstExtends.1
      ⟨LedgerBelow.markCapRange firstBelow secondExtends.1,
        (RefinesBelow.markCapRange q _ ledger).trans
          ((RefinesBelow.markCapRange _ q' _).restrict firstExtends)⟩

/-! ## Primitive data patterns -/

mutual

theorem DDDPatOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expectedTarget : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expectedTarget bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .var => Evolution.refl below (SupplyExtends.refl _)
  | .wild => Evolution.refl below (SupplyExtends.refl _)
  | .ctor lookup aligned childrenOrigin =>
      have instantiated := LedgerBelow.markCtorInstance _ below
      have childrenEvolution :=
        DDDPatsOrigin.ledgerEvolution childrenOrigin instantiated
      have extension := SupplyExtends.instantiateCtorScheme q _
      ⟨LedgerBelow.freezeExport _ _ _ childrenEvolution.1,
        (RefinesBelow.markCtorInstance q ledger _).trans
          ((childrenEvolution.2.trans
            ((RefinesBelow.freezeExport q' _ _ _ _).restrict
              childrenOrigin.erase.supplyExtends)).restrict extension)⟩
  | @DDDPatOrigin.tuple _ q _ patterns _ _ _ _ _ _ _ aligned _
      childrenOrigin =>
      have extension := SupplyExtends.freshTargets patterns.length q
      (Evolution.refl below extension).trans extension
        (DDDPatsOrigin.ledgerEvolution
          (q := (freshTargetsSupply patterns.length q).2) childrenOrigin
          (below.mono extension))

theorem DDDPatsOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin disjoint =>
      have headEvolution := DDDPatOrigin.ledgerEvolution headOrigin below
      have tailEvolution :=
        DDDPatsOrigin.ledgerEvolution tailOrigin headEvolution.1
      headEvolution.trans headOrigin.erase.supplyExtends tailEvolution

end

/-! ## Primitive-pattern patterns -/

mutual

theorem DDPPatOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expectedTarget : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expectedTarget holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .hole => ⟨LedgerBelow.markFreshCap below,
      RefinesBelow.markFreshCap q ledger⟩
  | .wild => Evolution.refl below (SupplyExtends.refl _)
  | .pval => Evolution.refl below (SupplyExtends.refl _)
  | .ctor lookup aligned childrenOrigin =>
      have instantiated := LedgerBelow.markCtorInstance _ below
      have childrenEvolution :=
        DDPPatsOrigin.ledgerEvolution childrenOrigin instantiated
      have extension := SupplyExtends.instantiateCtorScheme q _
      ⟨LedgerBelow.freezeExport _ _ _ childrenEvolution.1,
        (RefinesBelow.markCtorInstance q ledger _).trans
          ((childrenEvolution.2.trans
            ((RefinesBelow.freezeExport q' _ _ _ _).restrict
              childrenOrigin.erase.supplyExtends)).restrict extension)⟩
  | @DDPPatOrigin.tuple _ q _ patterns _ _ _ _ _ _ _ _ aligned _
      childrenOrigin =>
      have extension := SupplyExtends.freshTargets patterns.length q
      (Evolution.refl below extension).trans extension
        (DDPPatsOrigin.ledgerEvolution
          (q := (freshTargetsSupply patterns.length q).2) childrenOrigin
          (below.mono extension))

theorem DDPPatsOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin disjoint =>
      have headEvolution := DDPPatOrigin.ledgerEvolution headOrigin below
      have tailEvolution :=
        DDPPatsOrigin.ledgerEvolution tailOrigin headEvolution.1
      headEvolution.trans headOrigin.erase.supplyExtends tailEvolution

end

/-! ## Expressions, user patterns, arms, and clauses -/

mutual

theorem DDSynthOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | @DDSynthOrigin.var _ q _ _ _ scheme ledger lookup =>
      ⟨LedgerBelow.markSchemeInstance scheme below,
        RefinesBelow.markSchemeInstance q ledger scheme⟩
  | .lam bodyOrigin =>
      have extension := SupplyExtends.bumpTy q 1
      have preEvolution := Evolution.refl below extension
      preEvolution.trans extension
        (DDSynthOrigin.ledgerEvolution bodyOrigin (below.mono extension))
  | .fix distinct direct nonMatcher bodyOrigin aligned =>
      have extension := SupplyExtends.bumpTy q 2
      have preEvolution := Evolution.refl below extension
      preEvolution.trans extension
        (DDSynthOrigin.ledgerEvolution bodyOrigin (below.mono extension))
  | .app functionOrigin aligned argumentOrigin =>
      have functionEvolution :=
        DDSynthOrigin.ledgerEvolution functionOrigin below
      have bump := SupplyExtends.bumpTy _ 2
      have bridge := Evolution.refl functionEvolution.1 bump
      have preEvolution := functionEvolution.trans
        functionOrigin.erase.supplyExtends bridge
      preEvolution.trans
        (functionOrigin.erase.supplyExtends.trans bump)
        (DDCheckOrigin.ledgerEvolution argumentOrigin bridge.1)
  | .lit => Evolution.refl below (SupplyExtends.refl _)
  | .tuple childrenOrigin =>
      DDSynthsOrigin.ledgerEvolution childrenOrigin below
  | .ctor lookup childrenOrigin =>
      have instantiated := LedgerBelow.markCtorInstance _ below
      have childrenEvolution :=
        DDChecksOrigin.ledgerEvolution childrenOrigin instantiated
      have extension := SupplyExtends.instantiateCtorScheme q _
      ⟨LedgerBelow.freezeExport _ _ _ childrenEvolution.1,
        (RefinesBelow.markCtorInstance q ledger _).trans
          ((childrenEvolution.2.trans
            ((RefinesBelow.freezeExport q' _ _ _ _).restrict
              childrenOrigin.erase.supplyExtends)).restrict extension)⟩
  | .prim lookup childrenOrigin =>
      have instantiated := LedgerBelow.markCtorInstance _ below
      have childrenEvolution :=
        DDChecksOrigin.ledgerEvolution childrenOrigin instantiated
      have extension := SupplyExtends.instantiateCtorScheme q _
      ⟨LedgerBelow.freezeExport _ _ _ childrenEvolution.1,
        (RefinesBelow.markCtorInstance q ledger _).trans
          ((childrenEvolution.2.trans
            ((RefinesBelow.freezeExport q' _ _ _ _).restrict
              childrenOrigin.erase.supplyExtends)).restrict extension)⟩
  | .letE valueOrigin bodyOrigin stable =>
      have valueEvolution := DDSynthOrigin.ledgerEvolution valueOrigin below
      valueEvolution.trans valueOrigin.erase.supplyExtends
        (DDSynthOrigin.ledgerEvolution bodyOrigin valueEvolution.1)
  | .something => Evolution.refl below (SupplyExtends.bumpTy q 1)
  | .matcher clausesOrigin collected inferred clauseCaps catchAll binders arms
      coverage =>
      have bump := SupplyExtends.bumpTy q 1
      have preEvolution := Evolution.refl below bump
      have clausesEvolution := DDClausesOrigin.ledgerEvolution clausesOrigin
        preEvolution.1
      have traversed := preEvolution.trans bump clausesEvolution
      ⟨LedgerBelow.freezeMatcherProducer _ clausesEvolution.1,
        traversed.2.trans
          (RefinesBelow.freezeMatcherProducer q _ _)⟩
  | .matchAll targetOrigin patternOrigin targetAligned matcherOrigin
      bodyOrigin =>
      have targetEvolution := DDSynthOrigin.ledgerEvolution targetOrigin below
      have patternEvolution := DDPatternOrigin.ledgerEvolution patternOrigin
        targetEvolution.1
      have throughPattern := targetEvolution.trans
        targetOrigin.erase.supplyExtends patternEvolution
      have matcherEvolution := DDCheckOrigin.ledgerEvolution matcherOrigin
        patternEvolution.1
      have throughMatcher := throughPattern.trans
        (targetOrigin.erase.supplyExtends.trans
          patternOrigin.erase.supplyExtends) matcherEvolution
      throughMatcher.trans
        ((targetOrigin.erase.supplyExtends.trans
          patternOrigin.erase.supplyExtends).trans
            matcherOrigin.erase.supplyExtends)
        (DDSynthOrigin.ledgerEvolution bodyOrigin matcherEvolution.1)
  | .fixMatcher distinct direct placeholder bodyOrigin aligned =>
      have extension := SupplyExtends.fixMatcherPlaceholder placeholder
      have preEvolution : Evolution q _ ledger _ :=
        ⟨LedgerBelow.markCapRange below extension.1,
          RefinesBelow.markCapRange q _ ledger⟩
      preEvolution.trans extension
        (DDSynthOrigin.ledgerEvolution bodyOrigin preEvolution.1)

theorem DDSynthsOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthsOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin =>
      have headEvolution := DDSynthOrigin.ledgerEvolution headOrigin below
      headEvolution.trans headOrigin.erase.supplyExtends
        (DDSynthsOrigin.ledgerEvolution tailOrigin headEvolution.1)

theorem DDCheckOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDCheckOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .mk synthOrigin _ => DDSynthOrigin.ledgerEvolution synthOrigin below

theorem DDChecksOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDChecksOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin =>
      have headEvolution := DDCheckOrigin.ledgerEvolution headOrigin below
      headEvolution.trans headOrigin.erase.supplyExtends
        (DDChecksOrigin.ledgerEvolution tailOrigin headEvolution.1)

theorem DDPatternOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .pvar freshName =>
      ⟨(LedgerBelow.markFreshCap below).mono
          (SupplyExtends.bumpTy _ 1),
        RefinesBelow.markFreshCap q ledger⟩
  | .wild =>
      ⟨(LedgerBelow.markFreshCap below).mono
          (SupplyExtends.bumpTy _ 1),
        RefinesBelow.markFreshCap q ledger⟩
  | .pval expressionOrigin =>
      have expressionEvolution :=
        DDSynthOrigin.ledgerEvolution expressionOrigin below
      have post : Evolution _ _ _ _ :=
        ⟨LedgerBelow.markFreshCap expressionEvolution.1,
          RefinesBelow.markFreshCap _ _⟩
      expressionEvolution.trans expressionOrigin.erase.supplyExtends post
  | .embed lookup => Evolution.refl below (SupplyExtends.refl _)
  | .ptuple childrenOrigin =>
      DDPatternsOrigin.ledgerEvolution childrenOrigin below
  | .pctor lookup childrenOrigin targetsAligned capOrigin compatible =>
      have extension := SupplyExtends.instantiateCtorScheme q _
      have instantiated := LedgerBelow.markCtorInstance _ below
      have childrenEvolution :=
        DDPatternsOrigin.ledgerEvolution childrenOrigin instantiated
      have throughChildren : Evolution q _ ledger _ :=
        ⟨childrenEvolution.1,
          (RefinesBelow.markCtorInstance q ledger _).trans
            (childrenEvolution.2.restrict extension)⟩
      have capEvolution :=
        DDPatternCtorCapOrigin.ledgerEvolution capOrigin childrenEvolution.1
      have throughCap := throughChildren.trans
        (extension.trans childrenOrigin.erase.supplyExtends) capEvolution
      ⟨LedgerBelow.freezeExport _ _ _ capEvolution.1,
        throughCap.2.trans
          (RefinesBelow.freezeExport q _ _ _ _)⟩
  | .pand leftOrigin rightOrigin aligned =>
      have leftEvolution := DDPatternOrigin.ledgerEvolution leftOrigin below
      leftEvolution.trans leftOrigin.erase.supplyExtends
        (DDPatternOrigin.ledgerEvolution rightOrigin leftEvolution.1)
  | .por leftOrigin rightOrigin dualsAligned bindingsAligned =>
      have leftEvolution := DDPatternOrigin.ledgerEvolution leftOrigin below
      leftEvolution.trans leftOrigin.erase.supplyExtends
        (DDPatternOrigin.ledgerEvolution rightOrigin leftEvolution.1)
  | .papp lookup childrenOrigin aligned =>
      have extension := SupplyExtends.instantiateDualScheme q _
      have instantiated := LedgerBelow.markDualInstance _ below
      have childrenEvolution :=
        DDPatternsOrigin.ledgerEvolution childrenOrigin instantiated
      ⟨childrenEvolution.1,
        (RefinesBelow.markDualInstance q ledger _).trans
          (childrenEvolution.2.restrict extension)⟩

theorem DDPatternsOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPatternsOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin =>
      have headEvolution := DDPatternOrigin.ledgerEvolution headOrigin below
      headEvolution.trans headOrigin.erase.supplyExtends
        (DDPatternsOrigin.ledgerEvolution tailOrigin headEvolution.1)

theorem DDArmsOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDArmsOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons patternOrigin disjoint bodyOrigin tailOrigin =>
      have patternEvolution := DDDPatOrigin.ledgerEvolution patternOrigin below
      have bodyEvolution := DDCheckOrigin.ledgerEvolution bodyOrigin
        patternEvolution.1
      have throughBody := patternEvolution.trans
        patternOrigin.erase.supplyExtends bodyEvolution
      throughBody.trans
        (patternOrigin.erase.supplyExtends.trans bodyOrigin.erase.supplyExtends)
        (DDArmsOrigin.ledgerEvolution tailOrigin bodyEvolution.1)

theorem DDClauseOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDClauseOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .mk ppOrigin _ nextOrigin armsOrigin =>
      have ppEvolution := DDPPatOrigin.ledgerEvolution ppOrigin below
      have nextEvolution := DDChecksOrigin.ledgerEvolution nextOrigin
        ppEvolution.1
      have throughNext := ppEvolution.trans ppOrigin.erase.supplyExtends
        nextEvolution
      throughNext.trans
        (ppOrigin.erase.supplyExtends.trans nextOrigin.erase.supplyExtends)
        (DDArmsOrigin.ledgerEvolution armsOrigin nextEvolution.1)

theorem DDClausesOrigin.ledgerEvolution
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q'
      S'} {ledger ledger' : CapabilityOriginLedger}
    (origin : DDClausesOrigin signature raw ledger ledger')
    (below : LedgerBelow q ledger) : Evolution q q' ledger ledger' :=
  match origin with
  | .nil => Evolution.refl below (SupplyExtends.refl _)
  | .cons headOrigin tailOrigin =>
      have headEvolution := DDClauseOrigin.ledgerEvolution headOrigin below
      headEvolution.trans headOrigin.erase.supplyExtends
        (DDClausesOrigin.ledgerEvolution tailOrigin headEvolution.1)

end

/-! ## Cut-local boundedness

The global `DDSynth.boundedBy` theorem publishes the terminal bound of a
derivation.  In inversion proofs one often needs the earlier application cut:
after synthesizing the function and aligning it with the freshly allocated
function skeleton, but before synthesizing the argument.  The following
bundle keeps that intermediate supply explicit and exposes the key freshness
consequence directly. -/

/-- Origin-certified synthesis preserves substitution boundedness.  This is
the raw boundedness theorem exposed without requiring clients to erase the
certificate by hand. -/
theorem DDSynthOrigin.outputBounded
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (substBounded : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    S'.BoundedBy q' ∧ target.BoundedBy q' :=
  origin.erase.boundedBy closed substBounded contextBounded

/-- Origin-certified checking preserves boundedness at its output cut. -/
theorem DDCheckOrigin.outputBounded
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDCheckOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (substBounded : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) : S'.BoundedBy q' :=
  origin.erase.boundedBy closed substBounded contextBounded expectedBounded

/-- Ledger-aware equality alignment preserves a supplied cut bound. -/
theorem DDAlignTypesWithLedger.outputBounded
    {ledger : CapabilityOriginLedger} {q : InferenceBase.FreshSupply}
    {S : Subst} {left right : Ty} {S' : Subst}
    (aligned : DDAlignTypesWithLedger ledger S left right S')
    (substBounded : S.BoundedBy q) (leftBounded : left.BoundedBy q)
    (rightBounded : right.BoundedBy q) : S'.BoundedBy q :=
  aligned.erase.boundedBy substBounded leftBounded rightBounded

/-- Ledger-aware checking alignment preserves a supplied cut bound. -/
theorem DDAlignWithLedger.outputBounded
    {ledger : CapabilityOriginLedger} {q : InferenceBase.FreshSupply}
    {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlignWithLedger ledger S raw expected S')
    (substBounded : S.BoundedBy q) (rawBounded : raw.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) : S'.BoundedBy q :=
  aligned.erase.boundedBy substBounded rawBounded expectedBounded

/-- Boundedness facts at the two internal cuts of an application rule. -/
structure DDAppCutsBounded
    (q₁ : InferenceBase.FreshSupply) (S₁ : Subst)
    (functionTarget : Ty) (S₂ : Subst) : Prop where
  functionSubst : S₁.BoundedBy q₁
  functionType : functionTarget.BoundedBy q₁
  argumentDomain : (Ty.var q₁.nextTy).BoundedBy
    { q₁ with nextTy := q₁.nextTy + 2 }
  applicationCodomain : (Ty.var (q₁.nextTy + 1)).BoundedBy
    { q₁ with nextTy := q₁.nextTy + 2 }
  alignedSubst : S₂.BoundedBy
    { q₁ with nextTy := q₁.nextTy + 2 }
  /-- The function-alignment post cannot anticipate the capability that the
  argument traversal would allocate next. -/
  argumentFreshCapFixed :
    S₂.cap ⟨q₁.nextCap⟩ = .var ⟨q₁.nextCap⟩

/-- Project boundedness of both internal application cuts from the
origin-certified function child and the ledger-aware function alignment.

Unlike a terminal boundedness theorem, this result retains `q₁` and `S₂`
in its type, so dependent inversion clients do not need to normalize a large
whole-program supply expression merely to show that the next capability is
fresh. -/
theorem DDSynthOrigin.appCutsBounded
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {function : Expr} {functionTarget : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
    {ledger ledger₁ : CapabilityOriginLedger}
    {functionRaw : DDSynth signature q S context function functionTarget q₁ S₁}
    (functionOrigin : DDSynthOrigin signature functionRaw ledger ledger₁)
    (aligned : DDAlignTypesWithLedger ledger₁ S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂)
    (closed : signature.SchemesClosed) (substBounded : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    DDAppCutsBounded q₁ S₁ functionTarget S₂ := by
  obtain ⟨S₁b, functionTargetB⟩ :=
    functionOrigin.erase.boundedBy closed substBounded contextBounded
  let argumentSupply : InferenceBase.FreshSupply :=
    { q₁ with nextTy := q₁.nextTy + 2 }
  have extension : SupplyExtends q₁ argumentSupply :=
    SupplyExtends.bumpTy q₁ 2
  have domainB : Ty.BoundedBy argumentSupply (.var q₁.nextTy) :=
    Ty.BoundedBy.varOf (show q₁.nextTy < q₁.nextTy + 2 by omega)
  have codomainB : Ty.BoundedBy argumentSupply
      (.var (q₁.nextTy + 1)) :=
    Ty.BoundedBy.varOf
      (show q₁.nextTy + 1 < q₁.nextTy + 2 by omega)
  have S₂b : S₂.BoundedBy argumentSupply :=
    aligned.erase.boundedBy (S₁b.mono extension)
      (functionTargetB.mono extension) (Ty.BoundedBy.fnOf domainB codomainB)
  exact ⟨S₁b, functionTargetB, domainB, codomainB, S₂b,
    S₂b.freshCapFixed⟩

end TypePM
