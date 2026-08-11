import TypePM.DemandTypingErasureCore
import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport
import TypePM.DemandTypingErasureNoCapture
import TypePM.DemandTypingErasureSchemeAudit
import TypePM.DemandTypingErasureNoCaptureRegression
import TypePM.DemandTypingScopedPost
import TypePM.DemandTypingRuntimeErasureExpr
import TypePM.DemandTypingRuntimeErasurePatterns
import TypePM.DemandTypingRuntimeErasurePurePatterns
import TypePM.DemandTypingRuntimeErasureUserPatterns
import TypePM.DemandTypingRuntimeErasureMatchAll

/-!
# Demand-typing state erasure

This is the public facade for the state-erasure development:

- `DemandTypingErasureCore` defines scoped residual posts, state
  factorization, and the initial runtime-erasure projections.
- `DemandTypingErasureFactorization` proves premise-free state factorization
  for all 14 origin-aware demand-typing families.
- `DemandTypingErasureTransport` supplies canonical-instance-directed
  transport across later state cuts.
- `DemandTypingErasureNoCapture` isolates the exact range-hygiene condition
  under which masked scheme substitution composes.
- `DemandTypingErasureSchemeAudit` and its no-capture regression fix both the
  prefix- and suffix-capture counterexamples that delimit that transport.
- `DemandTypingScopedPost` totalizes a variable-only post below one supply
  cut without imposing a false global post condition.
- `DemandTypingRuntimeErasureExpr` and
  `DemandTypingRuntimeErasurePatterns` define the terminal state-free
  conclusions and constructor-wise projections for every DD family.
- `DemandTypingRuntimeErasurePurePatterns` closes later-cut erasure mutually
  for the data- and primitive-pattern families that contain no expressions.
- `DemandTypingRuntimeErasureUserPatterns` extends the invariant through the
  expression-independent user-pattern fragment and matcher arms.
- `DemandTypingRuntimeErasureMatchAll` composes target, user-pattern,
  matcher, and body invariants at the common final cut.

The remaining roadmap theorem closes expression-side `RuntimeErasureUnder`
mutually with user patterns, arms, and clauses.  Its variable and `let`
cases share the residual scheme-composition boundary isolated by the
transport module.
-/
