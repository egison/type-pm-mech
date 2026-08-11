import TypePM.DemandTypingErasureCore
import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport
import TypePM.DemandTypingErasureSchemeAudit
import TypePM.DemandTypingRuntimeErasureExpr
import TypePM.DemandTypingRuntimeErasurePatterns
import TypePM.DemandTypingRuntimeErasurePurePatterns
import TypePM.DemandTypingRuntimeErasureUserPatterns

/-!
# Demand-typing state erasure

This is the public facade for the state-erasure development:

- `DemandTypingErasureCore` defines scoped residual posts, state
  factorization, and the initial runtime-erasure projections.
- `DemandTypingErasureFactorization` proves premise-free state factorization
  for all 14 origin-aware demand-typing families.
- `DemandTypingErasureTransport` supplies canonical-instance-directed
  transport across later state cuts.
- `DemandTypingErasureSchemeAudit` fixes the bounded, solved, origin-safe
  binder-capture counterexample that delimits that transport.
- `DemandTypingRuntimeErasureExpr` and
  `DemandTypingRuntimeErasurePatterns` define the terminal state-free
  conclusions and constructor-wise projections for every DD family.
- `DemandTypingRuntimeErasurePurePatterns` closes later-cut erasure mutually
  for the data- and primitive-pattern families that contain no expressions.
- `DemandTypingRuntimeErasureUserPatterns` extends the invariant through the
  expression-independent user-pattern fragment and matcher arms.

The remaining roadmap theorem closes expression-side `RuntimeErasureUnder`
mutually with user patterns, arms, and clauses.  Its variable and `let`
cases share the residual scheme-composition boundary isolated by the
transport module.
-/
