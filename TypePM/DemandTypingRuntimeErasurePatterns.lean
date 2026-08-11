import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport

/-!
# State-free runtime erasure for patterns and matcher clauses

This module gives the pattern-side target propositions for demand-typing
state erasure.  Each proposition applies the terminal substitution uniformly
to the raw indices and asks for the corresponding state-free source
certificate.  Constructor lemmas deliberately expose the remaining
occurrence-local obligations: child erasures, terminal alignment equalities,
constructor instances, and terminal expression typings.

No definition below stores a demand-typing derivation in the target
certificate.  In particular, expression leaves take a concrete terminal
`RuntimeTyping` premise rather than using the source derivation as an oracle.
-/

namespace TypePM

namespace DDErasure.StateFactorization

/-- Any equality established at the input substitution remains true at the
terminal substitution factored through it.  This is the small algebraic step
needed to turn an alignment's local equality into a parent constructor's
terminal equality. -/
theorem liftTyEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : Ty}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : S.apply left = S.apply right) :
    S'.apply left = S'.apply right := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Subst.seq_apply] using congrArg post.apply equality

end DDErasure.StateFactorization

namespace CtorScheme

/-- The canonical supply-indexed constructor instance can be specialized by
an algebraically admissible terminal substitution. -/
theorem instantiateInstUnder
    (q : InferenceBase.FreshSupply) (scheme : CtorScheme) {post : Subst}
    (composition : scheme.InstCompositionAdm post) :
    scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map post.apply)
      (post.apply
        (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  exact CtorScheme.Inst.transport
    (InferenceBase.instantiateCtorScheme_sound q scheme) composition

end CtorScheme

namespace DDDPatOrigin

/-- Terminal state-free conclusion for one primitive data pattern. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatOrigin signature raw ledger ledger') : Prop :=
  DPatTy signature pattern (S'.apply expected) (bindings.applySubst S')

theorem runtimeErasure_var
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDDPatOrigin.var (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) := by
  exact DPatTy.var

theorem runtimeErasure_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDDPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  exact DPatTy.wild

end DDDPatOrigin

namespace DDDPatsOrigin

/-- Terminal state-free conclusion for a primitive data-pattern list. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatsOrigin signature raw ledger ledger') : Prop :=
  DPatTys signature patterns (targets.map S'.apply)
    (bindings.applySubst S')

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDDPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) := by
  exact DPatTys.nil

end DDDPatsOrigin

namespace DDDPatOrigin

/-- A data constructor is structural once its children, terminal result
equality, and terminal constructor instance have been supplied. -/
theorem runtimeErasure_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List DPat} {expected : Ty}
    {scheme : CtorScheme} {S₁ : Subst} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q scheme) S
      (InferenceBase.instantiateCtorScheme q scheme).value.2 expected S₁)
    {children : DDDPats signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger₂)
    (childrenErasure : DDDPatsOrigin.RuntimeErasure childrenOrigin)
    (resultEquality :
      S'.apply (InferenceBase.instantiateCtorScheme q scheme).value.2 =
        S'.apply expected)
    (instantiation : scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map S'.apply)
      (S'.apply (InferenceBase.instantiateCtorScheme q scheme).value.2)) :
    RuntimeErasure
      (DDDPatOrigin.ctor lookup aligned childrenOrigin) := by
  change DPatTy signature (.ctor name patterns) (S'.apply expected)
    (bindings.applySubst S')
  rw [← resultEquality]
  exact DPatTy.ctor lookup childrenErasure instantiation

/-- Tuple construction has the same terminal-equality boundary as ordinary
constructor construction. -/
theorem runtimeErasure_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {expected : Ty} {S₁ : Subst}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDDPats signature
      (freshTargetsSupply patterns.length q).2 S₁ patterns
      (freshTargetsSupply patterns.length q).1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children ledger ledger')
    (childrenErasure : DDDPatsOrigin.RuntimeErasure childrenOrigin)
    (resultEquality :
      S'.apply (.prod (freshTargetsSupply patterns.length q).1) =
        S'.apply expected) :
    RuntimeErasure (DDDPatOrigin.tuple aligned childrenOrigin) := by
  change DPatTy signature (.tuple patterns) (S'.apply expected)
    (bindings.applySubst S')
  rw [← resultEquality]
  simpa only [Subst.apply_prod] using DPatTy.tuple childrenErasure

end DDDPatOrigin

namespace DDDPatsOrigin

theorem runtimeErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {patterns : List DPat} {target : Ty}
    {targets : List Ty} {bindings restBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDDPat signature q S pattern target bindings q₁ S₁}
    {tail : DDDPats signature q₁ S₁ patterns targets restBindings q' S'}
    (headOrigin : DDDPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDDPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headAtTerminal : DPatTy signature pattern (S'.apply target)
      (bindings.applySubst S'))
    (tailErasure : RuntimeErasure tailOrigin) :
    RuntimeErasure
      (DDDPatsOrigin.cons headOrigin tailOrigin disjoint) := by
  change DPatTys signature (pattern :: patterns)
    ((target :: targets).map S'.apply)
    ((bindings ++ restBindings).applySubst S')
  have movedDistinct : ∀ name,
      name ∈ (bindings.applySubst S').names →
      name ∉ (restBindings.applySubst S').names := by
    simpa only [MonoCtx.names_applySubst] using disjoint
  simpa only [List.map_cons, MonoCtx.applySubst, List.map_append] using
    DPatTys.cons headAtTerminal tailErasure movedDistinct

end DDDPatsOrigin

namespace DDPPatOrigin

/-- Terminal state-free conclusion for one primitive-pattern pattern. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatOrigin signature raw ledger ledger') : Prop :=
  TerminalPPatResolution signature S' pattern (S'.apply expected)
    (holes.map (Dual.applySubst S')) (bindings.applySubst S')

theorem runtimeErasure_hole
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {expected : Ty} {ledger : CapabilityOriginLedger}
    (fresh : signature.FreshCapFor ⟨q.nextCap⟩ expected) :
    RuntimeErasure
      (DDPPatOrigin.hole (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  exact TerminalPPatResolution.hole fresh

theorem runtimeErasure_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDPPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  exact TerminalPPatResolution.wild

theorem runtimeErasure_pval
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDPPatOrigin.pval (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) := by
  exact TerminalPPatResolution.pval

end DDPPatOrigin

namespace DDPPatsOrigin

/-- Terminal state-free conclusion for a primitive-pattern list. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatsOrigin signature raw ledger ledger') : Prop :=
  TerminalPPatResolutions signature S' patterns (targets.map S'.apply)
    (holes.map (Dual.applySubst S')) (bindings.applySubst S')

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDPPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) := by
  exact TerminalPPatResolutions.nil

end DDPPatsOrigin

namespace DDPPatOrigin

theorem runtimeErasure_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List PPat} {expected : Ty}
    {entry : PatternCtorScheme signature.observability} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findPatternCtor name = some entry)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q entry.scheme) S
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2 expected S₁)
    {children : DDPPats signature
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 holes bindings
      q' S'}
    (childrenOrigin : DDPPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q entry.scheme) ledger₂)
    (childrenErasure : DDPPatsOrigin.RuntimeErasure childrenOrigin)
    (resultEquality :
      S'.apply (InferenceBase.instantiateCtorScheme q entry.scheme).value.2 =
        S'.apply expected)
    (instantiation : entry.Inst
      ((InferenceBase.instantiateCtorScheme q entry.scheme).value.1.map S'.apply)
      (S'.apply (InferenceBase.instantiateCtorScheme q entry.scheme).value.2)) :
    RuntimeErasure
      (DDPPatOrigin.ctor lookup aligned childrenOrigin) := by
  change TerminalPPatResolution signature S' (.ctor name patterns)
    (S'.apply expected) (holes.map (Dual.applySubst S'))
    (bindings.applySubst S')
  rw [← resultEquality]
  exact TerminalPPatResolution.ctor lookup childrenErasure instantiation

theorem runtimeErasure_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {expected : Ty} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDPPats signature
      (freshTargetsSupply patterns.length q).2 S₁ patterns
      (freshTargetsSupply patterns.length q).1 holes bindings q' S'}
    (childrenOrigin : DDPPatsOrigin signature children ledger ledger')
    (childrenErasure : DDPPatsOrigin.RuntimeErasure childrenOrigin)
    (resultEquality :
      S'.apply (.prod (freshTargetsSupply patterns.length q).1) =
        S'.apply expected) :
    RuntimeErasure (DDPPatOrigin.tuple aligned childrenOrigin) := by
  change TerminalPPatResolution signature S' (.tuple patterns)
    (S'.apply expected) (holes.map (Dual.applySubst S'))
    (bindings.applySubst S')
  rw [← resultEquality]
  simpa only [Subst.apply_prod] using
    TerminalPPatResolution.tuple childrenErasure

end DDPPatOrigin

namespace DDPPatsOrigin

theorem runtimeErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {patterns : List PPat} {target : Ty}
    {targets : List Ty} {holes restHoles : List Dual}
    {bindings restBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDPPat signature q S pattern target holes bindings q₁ S₁}
    {tail : DDPPats signature q₁ S₁ patterns targets restHoles
      restBindings q' S'}
    (headOrigin : DDPPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDPPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headAtTerminal : TerminalPPatResolution signature S' pattern
      (S'.apply target) (holes.map (Dual.applySubst S'))
      (bindings.applySubst S'))
    (tailErasure : RuntimeErasure tailOrigin) :
    RuntimeErasure
      (DDPPatsOrigin.cons headOrigin tailOrigin disjoint) := by
  change TerminalPPatResolutions signature S' (pattern :: patterns)
    ((target :: targets).map S'.apply)
    ((holes ++ restHoles).map (Dual.applySubst S'))
    ((bindings ++ restBindings).applySubst S')
  have movedDistinct : ∀ name,
      name ∈ (bindings.applySubst S').names →
      name ∉ (restBindings.applySubst S').names := by
    simpa only [MonoCtx.names_applySubst] using disjoint
  simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
    TerminalPPatResolutions.cons headAtTerminal tailErasure movedDistinct

end DDPPatsOrigin

namespace DDPatternOrigin

/-- Terminal actual-indexed resolution for one user pattern. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternOrigin signature raw ledger ledger') : Prop :=
  TerminalPatternResolution signature S' (context.applySubst S')
    (parameters.applySubst S') (bindingsIn.applySubst S') pattern
    (dual.cap.apply S'.cap) (S'.apply dual.target)
    (bindingsOut.applySubst S')

end DDPatternOrigin

namespace DDPatternsOrigin

/-- Terminal actual-indexed resolution for a user-pattern list. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPatternsOrigin signature raw ledger ledger') : Prop :=
  TerminalPatternResolutions signature S' (context.applySubst S')
    (parameters.applySubst S') (bindingsIn.applySubst S') patterns
    (duals.map (Dual.applySubst S')) (bindingsOut.applySubst S')

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : NamedContext) (parameters : PatternCtx) (bindings : MonoCtx)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDPatternsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  exact TerminalPatternResolutions.nil

end DDPatternsOrigin

namespace DDPatternOrigin

theorem runtimeErasure_pvar
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {ledger : CapabilityOriginLedger}
    (missing : name ∉ bindings.names)
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    RuntimeErasure
      (@DDPatternOrigin.pvar signature S context parameters q S context
        parameters bindings name ledger missing) := by
  change TerminalPatternResolution signature S (context.applySubst S)
    (parameters.applySubst S) (bindings.applySubst S) (.pvar name)
    ((Cap.var ⟨q.nextCap⟩).apply S.cap) (S.apply (Ty.var q.nextTy))
    ((bindings ++ [(name, Ty.var q.nextTy)]).applySubst S)
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.pvar (prevailing := S)
      (actualContext := context.applySubst S) missing freshCap freshTy)

theorem runtimeErasure_wild
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
    {ledger : CapabilityOriginLedger}
    (freshCap : FreshCap signature context parameters bindings ⟨q.nextCap⟩)
    (freshTy : FreshTy signature context parameters bindings q.nextTy) :
    RuntimeErasure
      (DDPatternOrigin.wild (signature := signature) (q := q) (S := S)
        (context := context) (parameters := parameters) (bindings := bindings)
        (ledger := ledger)) := by
  change TerminalPatternResolution signature S (context.applySubst S)
    (parameters.applySubst S) (bindings.applySubst S) .wild
    ((Cap.var ⟨q.nextCap⟩).apply S.cap) (S.apply (Ty.var q.nextTy))
    (bindings.applySubst S)
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.wild (prevailing := S)
      (actualContext := context.applySubst S) freshCap freshTy)

theorem runtimeErasure_pval_of_expression
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
    {expression : Expr} {target : Ty} {q₁ : InferenceBase.FreshSupply}
    {S₁ : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {expressionRaw : DDSynth signature q S
      (bindings.toContext ++ context) expression target q₁ S₁}
    (expressionOrigin : DDSynthOrigin signature expressionRaw ledger ledger₁)
    (freshCap : FreshCap signature context parameters bindings
      ⟨q₁.nextCap⟩)
    (separate : ⟨q₁.nextCap⟩ ∉ target.fcv)
    (expressionAtTerminal : RuntimeTyping signature
      ((bindings.applySubst S₁).toContext ++ context.applySubst S₁)
      expression (S₁.apply target)) :
    RuntimeErasure
      (@DDPatternOrigin.pval signature parameters q S context parameters
        bindings expression target q₁ S₁ ledger ledger₁ expressionRaw
        expressionOrigin) := by
  change TerminalPatternResolution signature S₁ (context.applySubst S₁)
    (parameters.applySubst S₁) (bindings.applySubst S₁)
    (.pval expression) ((Cap.var ⟨q₁.nextCap⟩).apply S₁.cap)
    (S₁.apply target) (bindings.applySubst S₁)
  simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
    (TerminalPatternResolution.pval (prevailing := S₁)
      (actualContext := context.applySubst S₁) freshCap separate
      expressionAtTerminal)

theorem runtimeErasure_embed
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
    {name : String} {dual : Dual} {ledger : CapabilityOriginLedger}
    (lookup : parameters.find? name = some dual) :
    RuntimeErasure
      (@DDPatternOrigin.embed signature q S context bindings q S context
        parameters bindings name dual ledger lookup) := by
  change TerminalPatternResolution signature S (context.applySubst S)
    (parameters.applySubst S) (bindings.applySubst S) (.embed name)
    (dual.cap.apply S.cap) (S.apply dual.target) (bindings.applySubst S)
  apply TerminalPatternResolution.embed
    (rawContext := context) (rawParameters := parameters)
    (rawBindings := bindings) (actualContext := context.applySubst S)
    (prevailing := S) lookup
  rw [PatternCtx.find?_applySubst, lookup]
  rfl

theorem runtimeErasure_ptuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DDPatterns signature q S context parameters bindings patterns
      duals bindings' q' S'}
    (childrenOrigin : DDPatternsOrigin signature children ledger ledger')
    (childrenErasure : DDPatternsOrigin.RuntimeErasure childrenOrigin) :
    RuntimeErasure (DDPatternOrigin.ptuple childrenOrigin) := by
  change TerminalPatternResolution signature S' (context.applySubst S')
    (parameters.applySubst S') (bindings.applySubst S')
    (.ptuple patterns) ((Cap.prod (duals.map Dual.cap)).apply S'.cap)
    (S'.apply (.prod (duals.map Dual.target)))
    (bindings'.applySubst S')
  simpa only [Dual.map_cap_applySubst, Dual.map_target_applySubst,
    Cap.apply_prod, Cap.applyList_eq_map, Subst.apply_prod] using
    TerminalPatternResolution.tuple childrenErasure

/-- User-pattern constructor erasure is structural after child traversal,
target alignment, and capability projection have all been observed at the
same terminal cut. -/
theorem runtimeErasure_pctor_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
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
    (targetsAligned : DDAlignTargetListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂)
    {capRaw : DDPatternCtorCap signature entry q₁ S₂
      (duals.map Dual.cap) capability q₂ S₃}
    (capOrigin : DDPatternCtorCapOrigin signature entry capRaw ledger₁ ledger₂)
    (compatibleCheck : Inference.capCompatibleCheck entry
      ((duals.map Dual.cap).map fun child => child.apply S₃.cap)
      (capability.apply S₃.cap) = true)
    (childrenErasure : TerminalPatternResolutions signature S₃
      (context.applySubst S₃) (parameters.applySubst S₃)
      (bindings.applySubst S₃) patterns
      (duals.map (Dual.applySubst S₃)) (bindings'.applySubst S₃))
    (instanceAtTerminal : entry.Inst
      ((duals.map (Dual.applySubst S₃)).map Dual.target)
      (S₃.apply
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2)) :
    RuntimeErasure
      (DDPatternOrigin.pctor lookup childrenOrigin targetsAligned capOrigin
        compatibleCheck) := by
  change TerminalPatternResolution signature S₃
    (context.applySubst S₃) (parameters.applySubst S₃)
    (bindings.applySubst S₃) (.pctor name patterns)
    (capability.apply S₃.cap)
    (S₃.apply (InferenceBase.instantiateCtorScheme q entry.scheme).value.2)
    (bindings'.applySubst S₃)
  exact TerminalPatternResolution.ctor
    (result := ⟨capability.apply S₃.cap,
      S₃.apply (InferenceBase.instantiateCtorScheme q entry.scheme).value.2⟩)
    lookup childrenErasure
      (by
        simpa only [Dual.map_cap_applySubst, Cap.applyList_eq_map] using
          Inference.capCompatibleCheck_sound compatibleCheck)
      instanceAtTerminal

/-- Pattern-function application has no residual work once its canonical
value-flow instance and all argument patterns are available at the terminal
cut. -/
theorem runtimeErasure_papp_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
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
    (aligned : DDAlignDualListWithLedger ledger₁ S₁ duals
      (InferenceBase.instantiateDualScheme q scheme).value.1 S')
    (childrenErasure : TerminalPatternResolutions signature S'
      (context.applySubst S') (parameters.applySubst S')
      (bindings.applySubst S') patterns
      (duals.map (Dual.applySubst S')) (bindings'.applySubst S'))
    (instanceAtTerminal : scheme.ValueFlowInst
      (duals.map (Dual.applySubst S'))
      ((InferenceBase.instantiateDualScheme q scheme).value.2.applySubst S')) :
    RuntimeErasure
      (DDPatternOrigin.papp lookup childrenOrigin aligned) := by
  change TerminalPatternResolution signature S' (context.applySubst S')
    (parameters.applySubst S') (bindings.applySubst S')
    (.papp name patterns)
    ((InferenceBase.instantiateDualScheme q scheme).value.2.cap.apply S'.cap)
    (S'.apply (InferenceBase.instantiateDualScheme q scheme).value.2.target)
    (bindings'.applySubst S')
  exact TerminalPatternResolution.app lookup childrenErasure
    instanceAtTerminal

theorem runtimeErasure_pand_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
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
    (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S')
    (leftAtTerminal : TerminalPatternResolution signature S'
      (context.applySubst S') (parameters.applySubst S')
      (bindings.applySubst S') left (leftDual.cap.apply S'.cap)
      (S'.apply leftDual.target) (leftBindings.applySubst S'))
    (rightAtTerminal : TerminalPatternResolution signature S'
      (context.applySubst S') (parameters.applySubst S')
      (leftBindings.applySubst S') right (leftDual.cap.apply S'.cap)
      (S'.apply leftDual.target) (bindings'.applySubst S')) :
    RuntimeErasure (DDPatternOrigin.pand leftOrigin rightOrigin aligned) := by
  exact TerminalPatternResolution.and leftAtTerminal rightAtTerminal

theorem runtimeErasure_por_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
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
    (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual
      rightDual S₃)
    (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃
      leftBindings rightBindings S')
    (leftAtTerminal : TerminalPatternResolution signature S'
      (context.applySubst S') (parameters.applySubst S')
      (bindings.applySubst S') left (leftDual.cap.apply S'.cap)
      (S'.apply leftDual.target) (leftBindings.applySubst S'))
    (rightAtTerminal : TerminalPatternResolution signature S'
      (context.applySubst S') (parameters.applySubst S')
      (bindings.applySubst S') right (leftDual.cap.apply S'.cap)
      (S'.apply leftDual.target) (leftBindings.applySubst S')) :
    RuntimeErasure
      (DDPatternOrigin.por leftOrigin rightOrigin dualsAligned
        bindingsAligned) := by
  exact TerminalPatternResolution.or leftAtTerminal rightAtTerminal

end DDPatternOrigin

namespace DDPatternsOrigin

theorem runtimeErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindings : MonoCtx}
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
    (headAtTerminal : TerminalPatternResolution signature S'
      (context.applySubst S') (parameters.applySubst S')
      (bindings.applySubst S') pattern (dual.cap.apply S'.cap)
      (S'.apply dual.target) (bindings₁.applySubst S'))
    (tailErasure : RuntimeErasure tailOrigin) :
    RuntimeErasure (DDPatternsOrigin.cons headOrigin tailOrigin) := by
  change TerminalPatternResolutions signature S' (context.applySubst S')
    (parameters.applySubst S') (bindings.applySubst S')
    (pattern :: patterns) ((dual :: duals).map (Dual.applySubst S'))
    (bindings'.applySubst S')
  simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
    TerminalPatternResolutions.cons headAtTerminal tailErasure

end DDPatternsOrigin

namespace DDArmsOrigin

/-- Terminal state-free conclusion for a matcher-clause arm list. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDArmsOrigin signature raw ledger ledger') : Prop :=
  ArmsTy signature (context.applySubst S') (S'.apply clauseTarget)
    (ppBindings.applySubst S') (S'.apply bodyTarget) arms

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : NamedContext) (ppBindings : MonoCtx) (clauseTarget bodyTarget : Ty)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDArmsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ppBindings := ppBindings)
        (clauseTarget := clauseTarget) (bodyTarget := bodyTarget)
        (ledger := ledger)) := by
  exact ArmsTy.nil

theorem runtimeErasure_cons_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {ppBindings : MonoCtx} {dataPattern : DPat}
    {body : Expr} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {armBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {patternRaw : DDDPat signature q S dataPattern clauseTarget armBindings q₁ S₁}
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
    (patternAtTerminal : DPatTy signature dataPattern (S'.apply clauseTarget)
      (armBindings.applySubst S'))
    (bodyAtTerminal : RuntimeTyping signature
      ((armBindings.applySubst S').toContext ++
        (ppBindings.applySubst S').toContext ++ context.applySubst S')
      body (S'.apply bodyTarget))
    (tailErasure : RuntimeErasure tailOrigin) :
    RuntimeErasure
      (DDArmsOrigin.cons patternOrigin disjoint bodyOrigin tailOrigin) := by
  exact ArmsTy.cons (ArmTy.mk patternAtTerminal bodyAtTerminal) tailErasure

end DDArmsOrigin

namespace DDClauseOrigin

/-- One clause erased at a selected matcher capability and evidence.  These
two indices are chosen by matcher finalization, not by `DDClause` itself. -/
def RuntimeErasureAt
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClauseOrigin signature raw ledger ledger')
    (capability : Cap) (evidence : Shape.Evidence) : Prop :=
  ClauseTy signature S' (context.applySubst S') clause capability
    (S'.apply sharedTarget) evidence

theorem runtimeErasure_mk_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {pp : PPat} {next : Expr} {arms : List Arm}
    {sharedTarget : Ty} {holes : List Dual} {ppBindings : MonoCtx}
    {nextMatchers : List Expr} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
    {ppRaw : DDPPat signature q S pp sharedTarget holes ppBindings q₁ S₁}
    (ppOrigin : DDPPatOrigin signature ppRaw ledger ledger₁)
    (decomposed : decomposeME next holes.length = some nextMatchers)
    {nextRaw : DDChecks signature q₁ S₁ context nextMatchers
      (holes.map fun hole => .slot hole.cap hole.target) q₂ S₂}
    (nextOrigin : DDChecksOrigin signature nextRaw ledger₁ ledger₂)
    {armsRaw : DDArms signature q₂ S₂ context ppBindings arms
      sharedTarget (Ty.listT (prodTy (holes.map Dual.target))) q' S'}
    (armsOrigin : DDArmsOrigin signature armsRaw ledger₂ ledger')
    {capability : Cap} {evidence : Shape.Evidence}
    (coreOrder : PPatCoreOrder pp)
    (ppAtTerminal : TerminalPPatResolution signature S' pp
      (S'.apply sharedTarget) (holes.map (Dual.applySubst S'))
      (ppBindings.applySubst S'))
    (capsAtTerminal : PPatCapsAt signature true pp
      ((holes.map (Dual.applySubst S')).map Dual.cap) capability)
    (nextAtTerminal : ExprsTy signature (context.applySubst S') nextMatchers
      ((holes.map (Dual.applySubst S')).map
        fun hole => .slot hole.cap hole.target))
    (armsAtTerminal : ArmsTy signature (context.applySubst S')
      (S'.apply sharedTarget) (ppBindings.applySubst S')
      (S'.apply (Ty.listT (prodTy (holes.map Dual.target)))) arms)
    (evidenceAtTerminal : clauseEvidence signature.toMatcherSig pp
      ((holes.map (Dual.applySubst S')).map Dual.cap) = some evidence) :
    RuntimeErasureAt
      (DDClauseOrigin.mk ppOrigin decomposed nextOrigin armsOrigin)
      capability evidence := by
  exact ClauseTy.mk coreOrder (.ofTerminal ppAtTerminal) capsAtTerminal
    (by simpa using decomposed) nextAtTerminal (by
      simpa only [Subst.apply_listT, Subst.apply_prodTy,
        Dual.map_target_applySubst] using armsAtTerminal)
    evidenceAtTerminal

end DDClauseOrigin

namespace DDClausesOrigin

/-- Clause-list erasure at the capability and evidence list selected by
matcher finalization. -/
def RuntimeErasureAt
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q'
      S'} {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDClausesOrigin signature raw ledger ledger')
    (capability : Cap) (evidences : List Shape.Evidence) : Prop :=
  ClausesTy signature S' (context.applySubst S') clauses capability
    (S'.apply sharedTarget) evidences

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : NamedContext) (sharedTarget : Ty) (ledger : CapabilityOriginLedger)
    (capability : Cap) :
    RuntimeErasureAt
      (DDClausesOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (sharedTarget := sharedTarget) (ledger := ledger))
      capability [] := by
  exact ClausesTy.nil

theorem runtimeErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {clause : Clause} {clauses : List Clause}
    {sharedTarget : Ty} {holes : List Dual} {holeLists : List (List Dual)}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDClause signature q S context clause sharedTarget holes q₁ S₁}
    {tail : DDClauses signature q₁ S₁ context clauses sharedTarget
      holeLists q' S'}
    (headOrigin : DDClauseOrigin signature head ledger ledger₁)
    (tailOrigin : DDClausesOrigin signature tail ledger₁ ledger')
    {capability : Cap} {evidence : Shape.Evidence}
    {evidences : List Shape.Evidence}
    (headAtTerminal : ClauseTy signature S' (context.applySubst S') clause
      capability (S'.apply sharedTarget) evidence)
    (tailErasure : RuntimeErasureAt tailOrigin capability evidences) :
    RuntimeErasureAt (DDClausesOrigin.cons headOrigin tailOrigin) capability
      (evidence :: evidences) := by
  exact ClausesTy.cons headAtTerminal tailErasure

end DDClausesOrigin

end TypePM
