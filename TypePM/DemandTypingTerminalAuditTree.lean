import TypePM.DemandTypingTerminalAudit

/-!
# Recursive terminal-audit certificate

These mutually inductive certificate types mirror precisely the origin
families that can contain a matcher producer or a pattern constructor.
Ordinary constructors expose only their recursively audited children.  The
three terminal-sensitive constructors additionally require `LetFacts`,
`MatcherFacts`, or `PatternCtorFacts`.

The primitive data- and primitive-pattern families need no audit judgment:
they contain no terminal-sensitive node.  Keeping them out of this family
makes the certificate smaller than a mechanical fourteen-family mirror.
-/

namespace TypePM

mutual

inductive DDSynthTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {target : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDSynth signature q S context expression target q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDSynthOrigin signature raw ledger ledger' -> Type where
  | var : DDSynthTerminalAudit terminal signature
      (DDSynthOrigin.var lookup)
  | lam (body : DDSynthTerminalAudit terminal signature bodyOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.lam bodyOrigin)
  | fix (body : DDSynthTerminalAudit terminal signature bodyOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned)
  | app
      (function : DDSynthTerminalAudit terminal signature functionOrigin)
      (argument : DDCheckTerminalAudit terminal signature argumentOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.app functionOrigin aligned argumentOrigin)
  | lit : DDSynthTerminalAudit terminal signature DDSynthOrigin.lit
  | tuple (children : DDSynthsTerminalAudit terminal signature childrenOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.tuple childrenOrigin)
  | ctor (children : DDChecksTerminalAudit terminal signature childrenOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.ctor lookup childrenOrigin)
  | prim (children : DDChecksTerminalAudit terminal signature childrenOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.prim lookup childrenOrigin)
  | letE
      {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
      {name : String} {valueExpr bodyExpr : Expr} {valueTarget : Ty}
      {q1 : InferenceBase.FreshSupply} {valueSubst : Subst}
      {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger1 ledger' : CapabilityOriginLedger}
      {valueRaw : DDSynth signature q S context valueExpr valueTarget q1
        valueSubst}
      {valueOrigin : DDSynthOrigin signature valueRaw ledger ledger1}
      {bodyRaw : DDSynth signature q1 valueSubst
        ((name, signature.generalize (context.applySubst valueSubst)
          (valueSubst.apply valueTarget)) :: context)
        bodyExpr bodyTarget q' S'}
      {bodyOrigin : DDSynthOrigin signature bodyRaw ledger1 ledger'}
      {stable :
        (signature.generalize (context.applySubst valueSubst)
          (valueSubst.apply valueTarget)).applyMeta S' =
        signature.generalize (context.applySubst S')
          (S'.apply valueTarget)}
      (value : DDSynthTerminalAudit terminal signature valueOrigin)
      (body : DDSynthTerminalAudit terminal signature bodyOrigin)
      (facts : DDTerminalAudit.LetFacts terminal signature context valueTarget
        valueSubst) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.letE valueOrigin bodyOrigin stable)
  | something :
      DDSynthTerminalAudit terminal signature DDSynthOrigin.something
  | matcher
      {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
      {clauses : List Clause} {rawHoleLists : List (List Dual)}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {evidence : List Shape.Evidence} {capability : Cap}
      {ledger ledger1 : CapabilityOriginLedger}
      {clausesRaw : DDClauses signature
        { q with nextTy := q.nextTy + 1 } S context clauses
        (.var q.nextTy) rawHoleLists q' S'}
      {clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger1}
      {collected : Inference.collectClauseEvidence signature.toMatcherSig
        clauses (terminalHoleCaps S' rawHoleLists) = some evidence}
      {inferred : Shape.inferShape signature.observability evidence =
        some capability}
      {clauseCaps : Inference.clauseCapsListCheck signature capability clauses
        (terminalHoleCaps S' rawHoleLists) = true}
      {catchAll : Inference.catchAllLastCheck clauses = true}
      {binders : Inference.matcherBindersCheck clauses = true}
      {arms : Inference.armExhaustiveCheck signature clauses
        (S'.apply (.var q.nextTy)) = true}
      {coverage : Inference.coverageCheck signature.toMatcherSig clauses
        capability = true}
      (clausesAudit : DDClausesTerminalAudit terminal signature clausesOrigin)
      (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
        rawHoleLists capability (.var q.nextTy)) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.matcher clausesOrigin collected inferred clauseCaps
          catchAll binders arms coverage)
  | matchAll
      (target : DDSynthTerminalAudit terminal signature targetOrigin)
      (pattern : DDPatternTerminalAudit terminal signature patternOrigin)
      (matcher : DDCheckTerminalAudit terminal signature matcherOrigin)
      (body : DDSynthTerminalAudit terminal signature bodyOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
          matcherOrigin bodyOrigin)
  | fixMatcher
      (body : DDSynthTerminalAudit terminal signature bodyOrigin) :
      DDSynthTerminalAudit terminal signature
        (DDSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin
          aligned)

inductive DDSynthsTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expressions : List Expr} -> {targets : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDSynths signature q S context expressions targets q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDSynthsOrigin signature raw ledger ledger' -> Type where
  | nil : DDSynthsTerminalAudit terminal signature DDSynthsOrigin.nil
  | cons
      (head : DDSynthTerminalAudit terminal signature headOrigin)
      (tail : DDSynthsTerminalAudit terminal signature tailOrigin) :
      DDSynthsTerminalAudit terminal signature
        (DDSynthsOrigin.cons headOrigin tailOrigin)

inductive DDCheckTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {expected : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDCheck signature q S context expression expected q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDCheckOrigin signature raw ledger ledger' -> Type where
  | mk (synth : DDSynthTerminalAudit terminal signature synthOrigin) :
      DDCheckTerminalAudit terminal signature
        (DDCheckOrigin.mk synthOrigin aligned)

inductive DDChecksTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expressions : List Expr} -> {expecteds : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDChecks signature q S context expressions expecteds q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDChecksOrigin signature raw ledger ledger' -> Type where
  | nil : DDChecksTerminalAudit terminal signature DDChecksOrigin.nil
  | cons
      (head : DDCheckTerminalAudit terminal signature headOrigin)
      (tail : DDChecksTerminalAudit terminal signature tailOrigin) :
      DDChecksTerminalAudit terminal signature
        (DDChecksOrigin.cons headOrigin tailOrigin)

inductive DDPatternTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {parameters : PatternCtx} -> {bindingsIn : MonoCtx} ->
    {pattern : Pattern} -> {dual : Dual} -> {bindingsOut : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} -> {ledger ledger' : CapabilityOriginLedger} ->
    DDPatternOrigin signature raw ledger ledger' -> Type where
  | pvar : DDPatternTerminalAudit terminal signature
      (DDPatternOrigin.pvar freshName)
  | wild : DDPatternTerminalAudit terminal signature DDPatternOrigin.wild
  | pval (expression : DDSynthTerminalAudit terminal signature origin) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.pval origin)
  | embed : DDPatternTerminalAudit terminal signature
      (DDPatternOrigin.embed lookup)
  | ptuple
      (children : DDPatternsTerminalAudit terminal signature childrenOrigin) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.ptuple childrenOrigin)
  | pctor
      {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
      {parameters : PatternCtx} {bindings : MonoCtx} {name : String}
      {patterns : List Pattern}
      {entry : PatternCtorScheme signature.observability}
      {duals : List Dual} {bindings' : MonoCtx}
      {q1 : InferenceBase.FreshSupply} {S1 S2 : Subst}
      {capability : Cap} {q2 : InferenceBase.FreshSupply} {S3 : Subst}
      {ledger ledger1 ledger2 : CapabilityOriginLedger}
      {lookup : signature.findPatternCtor name = some entry}
      {childrenRaw : DDPatterns signature
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply S context
        parameters bindings patterns duals bindings' q1 S1}
      {childrenOrigin : DDPatternsOrigin signature childrenRaw
        (DDLedger.markCtorInstance ledger q entry.scheme) ledger1}
      {targetsAligned : DDAlignTargetListWithLedger ledger1 S1 duals
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S2}
      {capRaw : DDPatternCtorCap signature entry q1 S2
        (duals.map Dual.cap) capability q2 S3}
      {capOrigin : DDPatternCtorCapOrigin signature entry capRaw ledger1 ledger2}
      {compatible : Inference.capCompatibleCheck entry
        ((duals.map Dual.cap).map fun child => child.apply S3.cap)
        (capability.apply S3.cap) = true}
      (children : DDPatternsTerminalAudit terminal signature childrenOrigin)
      (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals
        capability) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.pctor lookup childrenOrigin targetsAligned capOrigin
          compatible)
  | pand
      (left : DDPatternTerminalAudit terminal signature leftOrigin)
      (right : DDPatternTerminalAudit terminal signature rightOrigin) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.pand leftOrigin rightOrigin aligned)
  | por
      (left : DDPatternTerminalAudit terminal signature leftOrigin)
      (right : DDPatternTerminalAudit terminal signature rightOrigin) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.por leftOrigin rightOrigin dualsAligned
          bindingsAligned)
  | papp
      (children : DDPatternsTerminalAudit terminal signature childrenOrigin) :
      DDPatternTerminalAudit terminal signature
        (DDPatternOrigin.papp lookup childrenOrigin aligned)

inductive DDPatternsTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {parameters : PatternCtx} -> {bindingsIn : MonoCtx} ->
    {patterns : List Pattern} -> {duals : List Dual} ->
    {bindingsOut : MonoCtx} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} -> {ledger ledger' : CapabilityOriginLedger} ->
    DDPatternsOrigin signature raw ledger ledger' -> Type where
  | nil : DDPatternsTerminalAudit terminal signature DDPatternsOrigin.nil
  | cons
      (head : DDPatternTerminalAudit terminal signature headOrigin)
      (tail : DDPatternsTerminalAudit terminal signature tailOrigin) :
      DDPatternsTerminalAudit terminal signature
        (DDPatternsOrigin.cons headOrigin tailOrigin)

inductive DDArmsTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {ppBindings : MonoCtx} -> {arms : List Arm} ->
    {clauseTarget bodyTarget : Ty} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    {raw : DDArms signature q S context ppBindings arms clauseTarget bodyTarget
      q' S'} -> {ledger ledger' : CapabilityOriginLedger} ->
    DDArmsOrigin signature raw ledger ledger' -> Type where
  | nil : DDArmsTerminalAudit terminal signature DDArmsOrigin.nil
  | cons
      (body : DDCheckTerminalAudit terminal signature bodyOrigin)
      (tail : DDArmsTerminalAudit terminal signature tailOrigin) :
      DDArmsTerminalAudit terminal signature
        (DDArmsOrigin.cons patternOrigin disjoint bodyOrigin tailOrigin)

inductive DDClauseTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {clause : Clause} -> {sharedTarget : Ty} -> {holes : List Dual} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDClause signature q S context clause sharedTarget holes q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDClauseOrigin signature raw ledger ledger' -> Type where
  | mk
      (next : DDChecksTerminalAudit terminal signature nextOrigin)
      (arms : DDArmsTerminalAudit terminal signature armsOrigin) :
      DDClauseTerminalAudit terminal signature
        (DDClauseOrigin.mk ppOrigin decomposed nextOrigin armsOrigin)

inductive DDClausesTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {clauses : List Clause} -> {sharedTarget : Ty} ->
    {holeLists : List (List Dual)} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q'
      S'} -> {ledger ledger' : CapabilityOriginLedger} ->
    DDClausesOrigin signature raw ledger ledger' -> Type where
  | nil : DDClausesTerminalAudit terminal signature DDClausesOrigin.nil
  | cons
      (head : DDClauseTerminalAudit terminal signature headOrigin)
      (tail : DDClausesTerminalAudit terminal signature tailOrigin) :
      DDClausesTerminalAudit terminal signature
        (DDClausesOrigin.cons headOrigin tailOrigin)

end

/-! ## Structural height

The erasure proof recurses over this proof-relevant tree.  A dedicated height
ignores every dependent index and terminal fact, keeping termination checking
independent of the much larger raw-derivation telescope.
-/

mutual

def DDSynthTerminalAudit.depth
    (audit : DDSynthTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .var => 1
  | .lam body => body.depth + 1
  | .fix body => body.depth + 1
  | .app function argument => max function.depth argument.depth + 1
  | .lit => 1
  | .tuple children => children.depth + 1
  | .ctor children => children.depth + 1
  | .prim children => children.depth + 1
  | .letE value body _ => max value.depth body.depth + 1
  | .something => 1
  | .matcher clauses _ => clauses.depth + 1
  | .matchAll target pattern matcher body =>
      max target.depth (max pattern.depth (max matcher.depth body.depth)) + 1
  | .fixMatcher body => body.depth + 1

def DDSynthsTerminalAudit.depth
    (audit : DDSynthsTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons head tail => max head.depth tail.depth + 1

def DDCheckTerminalAudit.depth
    (audit : DDCheckTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .mk synth => synth.depth + 1

def DDChecksTerminalAudit.depth
    (audit : DDChecksTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons head tail => max head.depth tail.depth + 1

def DDPatternTerminalAudit.depth
    (audit : DDPatternTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .pvar => 1
  | .wild => 1
  | .pval expression => expression.depth + 1
  | .embed => 1
  | .ptuple children => children.depth + 1
  | .pctor children _ => children.depth + 1
  | .pand left right => max left.depth right.depth + 1
  | .por left right => max left.depth right.depth + 1
  | .papp children => children.depth + 1

def DDPatternsTerminalAudit.depth
    (audit : DDPatternsTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons head tail => max head.depth tail.depth + 1

def DDArmsTerminalAudit.depth
    (audit : DDArmsTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons body tail => max body.depth tail.depth + 1

def DDClauseTerminalAudit.depth
    (audit : DDClauseTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .mk next arms => max next.depth arms.depth + 1

def DDClausesTerminalAudit.depth
    (audit : DDClausesTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons head tail => max head.depth tail.depth + 1

end

/-- Origin certificates are propositions, so an audit built against one
proof of the same indexed origin judgment can be reused with any other proof.
-/
def DDSynthTerminalAudit.transportOrigin
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {left right : DDSynthOrigin signature raw ledger ledger'}
    (audit : DDSynthTerminalAudit terminal signature left) :
    DDSynthTerminalAudit terminal signature right := by
  have equality : left = right := Subsingleton.elim _ _
  exact equality ▸ audit

/-! ## Public audited source typing -/

/-- Public source acceptance consists of chronological DD reconstruction and
a terminal audit of every nested producer boundary. -/
def DDTyping (signature : FrozenSig) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ raw q' S',
    ∃ derived : DDSynth signature (Inference.initialSupply signature context)
        Subst.id context expression raw q' S',
      ∃ ledger', ∃ origin : DDSynthOrigin signature derived [] ledger',
        ∃ _audit : DDSynthTerminalAudit S' signature origin,
          target = S'.apply raw

/-- Every audited published type is bounded by the terminal supply. -/
theorem DDTyping.published_boundedBy {signature : FrozenSig}
    {context : Context} {expression : Expr} {target : Ty}
    (typed : DDTyping signature context expression target)
    (closed : signature.SchemesClosed) :
    ∃ q', SupplyExtends (Inference.initialSupply signature context) q' ∧
      Ty.BoundedBy q' target := by
  obtain ⟨raw, q', S', derived, _ledger', _origin, _audit, published⟩ :=
    typed
  obtain ⟨S'b, rawB⟩ := derived.boundedBy closed
    (Subst.boundedBy_id _)
    (initialSupply_context_boundedBy signature context)
  exact ⟨q', derived.supplyExtends, published ▸ S'b.apply rawB⟩

end TypePM
