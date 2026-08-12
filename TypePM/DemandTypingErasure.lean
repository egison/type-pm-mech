import TypePM.DemandTypingErasureCore
import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport
import TypePM.DemandTypingScopedPost
import TypePM.DemandTypingInvariantErasureExpr
import TypePM.DemandTypingInvariantErasurePatterns
import TypePM.DemandTypingInvariantErasurePurePatterns
import TypePM.DemandTypingInvariantErasureUserPatterns
import TypePM.DemandTypingInvariantErasureMatchAll
import TypePM.DemandTypingTerminalAuditTree
import TypePM.DemandTypingTerminalErasure
import TypePM.DemandTypingTerminalAuditErasure

/-!
# Demand-typing state erasure

This is the public facade for the state-erasure development:

- `DemandTypingErasureCore` defines scoped residual posts, state
  factorization, and the initial typing-invariant projections.
- `DemandTypingErasureFactorization` proves premise-free state factorization
  for all 14 origin-aware demand-typing families.
- `DemandTypingErasureTransport` delegates capture-free expression-scheme
  transport to finite openings and retains the dual-scheme boundary used by
  user-pattern erasure.
- `DemandTypingScopedPost` totalizes a variable-only post below one supply
  cut without imposing a false global post condition.
- `DemandTypingInvariantErasureExpr` and
  `DemandTypingInvariantErasurePatterns` define the terminal state-free
  conclusions and constructor-wise projections for every demand-directed family.
- `DemandTypingInvariantErasurePurePatterns` closes later-cut erasure mutually
  for the data- and primitive-pattern families that contain no expressions.
- `DemandTypingInvariantErasureUserPatterns` extends the invariant through the
  expression-independent user-pattern fragment and matcher arms.
- `DemandTypingInvariantErasureMatchAll` composes target, user-pattern,
  matcher, and body invariants at the common final cut.

The terminal erasure theorem closes expression-side `TypingInvariantErasureUnder`
mutually with user patterns, arms, and clauses.  Expression scheme transport
uses finite openings directly.
-/

namespace TypePM

/-- A closed audited `SourceTyping` derivation yields the internal typing
invariant at exactly its published type. -/
theorem SourceTyping.typingInvariant
    {signature : FrozenSig} {expression : Expr} {target : Ty}
    (closed : signature.SchemesClosed)
    (typed : SourceTyping signature [] expression target) :
    TypingInvariant signature [] expression target := by
  obtain ⟨raw, q', terminal, derived, ledger', origin, audit, published⟩ :=
    typed
  have erased := DemandSynthTerminalAudit.typingInvariantErasure audit
    (DDErasure.StateFactorization.refl q' terminal ledger') closed
    Subst.id_idempotent
    (Subst.boundedBy_id (Inference.initialSupply signature []))
    (initialSupply_context_boundedBy signature [])
  rw [published]
  simpa only [Context.applySubst, List.map] using erased

end TypePM
