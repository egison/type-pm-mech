import TypePM.DemandTypingTerminalAuditTree

/-!
# Terminal-audit builder

Origin certificates live in `Prop`, whereas recursive audits are
proof-relevant `Type` witnesses.  Lean therefore cannot compute an audit by
eliminating an opaque origin proof.  This module instead packages an explicit
structural audit together with the raw derivation and origin proofs inferred
from that audit term, then transports the package to the opaque proof exposed
by a reconstruction result.

Clients normally write

```lean
have audit : DemandSynthTerminalAudit terminal signature origin :=
  DemandSynthTerminalAudit.transportBuilt
    (DemandSynthTerminalAudit.BuiltAudit.of explicitAuditTree)
```

The explicit tree mirrors only the source program's structural constructors.
At a `let`, matcher, or pattern constructor it additionally contains the
corresponding `LetFacts`, `MatcherFacts`, or `PatternCtorFacts` proof.
-/

namespace TypePM

/-- A proof-relevant package hiding the raw derivation and origin proof that
index a structurally built audit. -/
structure DemandSynthTerminalAudit.BuiltAudit
    (terminal : Subst) (signature : FrozenSig)
    (q : InferenceBase.FreshSupply) (S : Subst) (context : Context)
    (expression : Expr) (target : Ty) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger ledger' : CapabilityOriginLedger) : Type where
  raw : DemandSynth signature q S context expression target q' S'
  origin : DemandSynthOrigin signature raw ledger ledger'
  audit : DemandSynthTerminalAudit terminal signature origin

/-- Package an audit while inferring its hidden raw and origin witnesses from
the certificate term. -/
def DemandSynthTerminalAudit.BuiltAudit.of
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {raw : DemandSynth signature q S context expression target q' S'}
    {origin : DemandSynthOrigin signature raw ledger ledger'}
    (audit : DemandSynthTerminalAudit terminal signature origin) :
    DemandSynthTerminalAudit.BuiltAudit terminal signature q S context expression
      target q' S' ledger ledger' :=
  ⟨raw, origin, audit⟩

/-- Proof-term-insensitive transport across both the raw derivation proof and
the origin proof indexed by it. -/
def DemandSynthTerminalAudit.transportBuilt
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DemandSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {right : DemandSynthOrigin signature raw ledger ledger'}
    (source : DemandSynthTerminalAudit.BuiltAudit terminal signature q S context
      expression target q' S' ledger ledger') :
    DemandSynthTerminalAudit terminal signature right := by
  rcases source with ⟨raw', left, audit⟩
  have proofEq : raw' = raw := Subsingleton.elim _ _
  cases proofEq
  exact audit.transportOrigin

end TypePM
