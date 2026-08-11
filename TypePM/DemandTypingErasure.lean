import TypePM.DemandTypingErasureCore
import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport
import TypePM.DemandTypingRuntimeErasureExpr
import TypePM.DemandTypingRuntimeErasurePatterns

/-!
# Demand-typing state erasure

This is the public facade for the state-erasure development:

- `DemandTypingErasureCore` defines scoped residual posts, state
  factorization, and the initial runtime-erasure projections.
- `DemandTypingErasureFactorization` proves premise-free state factorization
  for all 14 origin-aware demand-typing families.
- `DemandTypingErasureTransport` supplies canonical-instance-directed
  transport across later state cuts.
- `DemandTypingRuntimeErasureExpr` and
  `DemandTypingRuntimeErasurePatterns` define the terminal state-free
  conclusions and constructor-wise projections for every DD family.

The remaining roadmap theorem extends the expression-side
`RuntimeErasureUnder` invariant mutually through recursive expressions,
patterns, arms, and clauses.
-/
