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

inductive DemandSynthTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {target : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DemandSynth signature q S context expression target q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DemandSynthOrigin signature raw ledger ledger' -> Type where
  | var : DemandSynthTerminalAudit terminal signature
      (DemandSynthOrigin.var lookup)
  | lam (body : DemandSynthTerminalAudit terminal signature bodyOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.lam bodyOrigin)
  | fix (body : DemandSynthTerminalAudit terminal signature bodyOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned)
  | app
      (function : DemandSynthTerminalAudit terminal signature functionOrigin)
      (argument : DemandCheckTerminalAudit terminal signature argumentOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.app functionOrigin aligned argumentOrigin)
  | lit : DemandSynthTerminalAudit terminal signature DemandSynthOrigin.lit
  | tuple (children : DemandSynthsTerminalAudit terminal signature childrenOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.tuple childrenOrigin)
  | ctor (children : DemandChecksTerminalAudit terminal signature childrenOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.ctor lookup childrenOrigin)
  | prim (children : DemandChecksTerminalAudit terminal signature childrenOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.prim lookup childrenOrigin)
  | letE
      {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
      {name : String} {valueExpr bodyExpr : Expr} {valueTarget : Ty}
      {q1 : InferenceBase.FreshSupply} {valueSubst : Subst}
      {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger1 ledger' : CapabilityOriginLedger}
      {valueRaw : DemandSynth signature q S context valueExpr valueTarget q1
        valueSubst}
      {valueOrigin : DemandSynthOrigin signature valueRaw ledger ledger1}
      {bodyRaw : DemandSynth signature q1 valueSubst
        ((name, signature.generalize (context.applySubst valueSubst)
          (valueSubst.apply valueTarget)) :: context)
        bodyExpr bodyTarget q' S'}
      {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger1 ledger'}
      (value : DemandSynthTerminalAudit terminal signature valueOrigin)
      (body : DemandSynthTerminalAudit terminal signature bodyOrigin)
      (facts : DDTerminalAudit.LetFacts terminal signature context valueTarget
        valueSubst) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.letE valueOrigin bodyOrigin)
  | something :
      DemandSynthTerminalAudit terminal signature DemandSynthOrigin.something
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
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.matcher clausesOrigin collected inferred clauseCaps
          catchAll binders arms coverage)
  | matchAll
      (target : DemandSynthTerminalAudit terminal signature targetOrigin)
      (pattern : DDPatternTerminalAudit terminal signature patternOrigin)
      (matcher : DemandCheckTerminalAudit terminal signature matcherOrigin)
      (body : DemandSynthTerminalAudit terminal signature bodyOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
          matcherOrigin bodyOrigin)
  | fixMatcher
      (body : DemandSynthTerminalAudit terminal signature bodyOrigin) :
      DemandSynthTerminalAudit terminal signature
        (DemandSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin
          aligned)

inductive DemandSynthsTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expressions : List Expr} -> {targets : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DemandSynths signature q S context expressions targets q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DemandSynthsOrigin signature raw ledger ledger' -> Type where
  | nil : DemandSynthsTerminalAudit terminal signature DemandSynthsOrigin.nil
  | cons
      (head : DemandSynthTerminalAudit terminal signature headOrigin)
      (tail : DemandSynthsTerminalAudit terminal signature tailOrigin) :
      DemandSynthsTerminalAudit terminal signature
        (DemandSynthsOrigin.cons headOrigin tailOrigin)

inductive DemandCheckTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {expected : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DemandCheck signature q S context expression expected q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DemandCheckOrigin signature raw ledger ledger' -> Type where
  | mk (synth : DemandSynthTerminalAudit terminal signature synthOrigin) :
      DemandCheckTerminalAudit terminal signature
        (DemandCheckOrigin.mk synthOrigin aligned)

inductive DemandChecksTerminalAudit (terminal : Subst) (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expressions : List Expr} -> {expecteds : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DemandChecks signature q S context expressions expecteds q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DemandChecksOrigin signature raw ledger ledger' -> Type where
  | nil : DemandChecksTerminalAudit terminal signature DemandChecksOrigin.nil
  | cons
      (head : DemandCheckTerminalAudit terminal signature headOrigin)
      (tail : DemandChecksTerminalAudit terminal signature tailOrigin) :
      DemandChecksTerminalAudit terminal signature
        (DemandChecksOrigin.cons headOrigin tailOrigin)

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
  | pval (expression : DemandSynthTerminalAudit terminal signature origin) :
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
      {targetsAligned : DemandAlignTargetListWithLedger ledger1 S1 duals
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
      (body : DemandCheckTerminalAudit terminal signature bodyOrigin)
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
      (next : DemandChecksTerminalAudit terminal signature nextOrigin)
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

def DemandSynthTerminalAudit.depth
    (audit : DemandSynthTerminalAudit terminal signature origin) : Nat :=
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

def DemandSynthsTerminalAudit.depth
    (audit : DemandSynthsTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .nil => 1
  | .cons head tail => max head.depth tail.depth + 1

def DemandCheckTerminalAudit.depth
    (audit : DemandCheckTerminalAudit terminal signature origin) : Nat :=
  match audit with
  | .mk synth => synth.depth + 1

def DemandChecksTerminalAudit.depth
    (audit : DemandChecksTerminalAudit terminal signature origin) : Nat :=
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
def DemandSynthTerminalAudit.transportOrigin
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DemandSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {left right : DemandSynthOrigin signature raw ledger ledger'}
    (audit : DemandSynthTerminalAudit terminal signature left) :
    DemandSynthTerminalAudit terminal signature right := by
  have equality : left = right := Subsingleton.elim _ _
  exact equality ▸ audit

/-! ## Public audited source typing -/

/-- Public source acceptance consists of chronological demand-directed reconstruction and
a terminal audit of every nested producer boundary. -/
def SourceTyping (signature : FrozenSig) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ raw q' S',
    ∃ derived : DemandSynth signature (Inference.initialSupply signature context)
        Subst.id context expression raw q' S',
      ∃ ledger', ∃ origin : DemandSynthOrigin signature derived [] ledger',
        ∃ _audit : DemandSynthTerminalAudit S' signature origin,
          target = S'.apply raw

/-- Every audited published type is bounded by the terminal supply. -/
theorem SourceTyping.published_boundedBy {signature : FrozenSig}
    {context : Context} {expression : Expr} {target : Ty}
    (typed : SourceTyping signature context expression target)
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
