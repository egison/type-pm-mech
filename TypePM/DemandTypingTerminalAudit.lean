import TypePM.DemandTypingOrigin

/-!
# Terminal audit of origin-aware demand typing

Origin certificates describe chronological reconstruction, while runtime
erasure is performed at one chosen terminal substitution.  Conditions that
are not stable under an arbitrary structural suffix are therefore audited at
that terminal cut.

Only three nodes need extra terminal facts.  Ordinary nodes continue to use the
existing structural erasure recursion:

* a `let` records that its generalized binding is stable at the terminal cut;
* a pattern constructor records compatibility after terminal substitution;
* a matcher recomputes evidence and validation for its normalized terminal
  capability.

These certificates contain no inference state and add nothing to
`TypingInvariant`.  Reconstruction creates them after it knows the root terminal
substitution; erasure consumes them at the corresponding origin nodes.
-/

namespace TypePM
namespace DDTerminalAudit

/-- Final stability of the generalized binding introduced by one `let`.
Local stability at the end of the let body does not in general survive an
enclosing suffix, because that suffix may identify or specialize free
metavariables and thereby change the generalized set. -/
structure LetFacts
    (terminal : Subst) (signature : FrozenSig) (context : Context)
    (valueTarget : Ty) (valueSubst : Subst) : Prop where
  stable :
    (signature.generalize (context.applySubst valueSubst)
      (valueSubst.apply valueTarget)).applyMeta terminal =
    signature.generalize (context.applySubst terminal)
      (terminal.apply valueTarget)

/-- Final compatibility of one pattern-constructor result. -/
structure PatternCtorFacts
    (terminal : Subst) {observable : Shape.Observability}
    (entry : PatternCtorScheme observable) (duals : List Dual)
    (capability : Cap) : Prop where
  compatible : entry.CapCompatible
    ((duals.map (Dual.applySubst terminal)).map Dual.cap)
    (capability.apply terminal.cap)

/-- Executable pattern-constructor compatibility at the terminal cut. -/
def patternCtorCompatibleCheck
    {observable : Shape.Observability}
    (terminal : Subst) (entry : PatternCtorScheme observable)
    (duals : List Dual) (capability : Cap) : Bool :=
  Inference.capCompatibleCheck entry
    ((duals.map (Dual.applySubst terminal)).map Dual.cap)
    (capability.apply terminal.cap)

theorem PatternCtorFacts.ofCheck
    {observable : Shape.Observability} {terminal : Subst}
    {entry : PatternCtorScheme observable} {duals : List Dual}
    {capability : Cap}
    (checked : patternCtorCompatibleCheck terminal entry duals capability =
      true) :
    PatternCtorFacts terminal entry duals capability :=
  ⟨Inference.capCompatibleCheck_sound checked⟩

/--
Normalized finalization facts for one matcher producer.

The capability is `rawCapability.apply terminal.cap`; it is intentionally not
required to equal `rawCapability`.  A safe rename-only suffix may rename the
raw producer while preserving the normalized matcher typing.
-/
structure MatcherFacts
    (terminal : Subst) (signature : FrozenSig) (clauses : List Clause)
    (rawHoleLists : List (List Dual)) (rawCapability : Cap)
    (rawTarget : Ty) : Prop where
  valid : ∃ evidence,
    Inference.collectClauseEvidence signature.toMatcherSig clauses
        (terminalHoleCaps terminal rawHoleLists) = some evidence ∧
    Shape.inferShape signature.observability evidence =
        some (rawCapability.apply terminal.cap) ∧
    Inference.clauseCapsListCheck signature
        (rawCapability.apply terminal.cap) clauses
        (terminalHoleCaps terminal rawHoleLists) = true ∧
    Inference.armExhaustiveCheck signature clauses
        (terminal.apply rawTarget) = true ∧
    Inference.coverageCheck signature.toMatcherSig clauses
        (rawCapability.apply terminal.cap) = true

/-- Solved form fixes the already-normalized terminal capability. -/
theorem normalizedCapability_fixed
    {terminal : Subst} (solved : terminal.Idempotent)
    (capability : Cap) :
    (capability.apply terminal.cap).apply terminal.cap =
      capability.apply terminal.cap := by
  have fixed :
      Ty.matcher ((capability.apply terminal.cap).apply terminal.cap) .unit =
        Ty.matcher (capability.apply terminal.cap) .unit := by
    simpa only [Subst.apply_matcher, Subst.apply_unit] using
      solved (.matcher capability .unit)
  exact (Ty.matcher.inj fixed).1

end DDTerminalAudit
end TypePM
