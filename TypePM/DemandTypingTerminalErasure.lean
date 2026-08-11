import TypePM.DemandTypingTerminalAudit
import TypePM.DemandTypingRuntimeErasureUserPatterns

/-! # Consuming terminal audits during state erasure -/

namespace TypePM
namespace DDTerminalAudit

/--
Erase a matcher at an arbitrary enclosing terminal cut by using the evidence
and capability selected by the terminal audit.  In particular, this theorem
does not require the matcher's local raw capability to remain unchanged by a
later rename-only suffix.
-/
theorem MatcherFacts.runtimeTyping_matcher
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List TypePM.Clause}
    {rawHoleLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' terminal : Subst} {capability : Cap}
    {ledger ledger₁ : CapabilityOriginLedger}
    {clausesRaw : DDClauses signature
      { q with nextTy := q.nextTy + 1 } S context clauses
      (.var q.nextTy) rawHoleLists q' S'}
    (_clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁)
    (catchAll : Inference.catchAllLastCheck clauses = true)
    (binders : Inference.matcherBindersCheck clauses = true)
    (audit : MatcherFacts terminal signature clauses rawHoleLists capability
      (.var q.nextTy))
    (clausesAtTerminal : ∀ terminalEvidence,
      Inference.ClauseCapsList signature clauses
        (terminalHoleCaps terminal rawHoleLists)
        (capability.apply terminal.cap) →
      Inference.ClauseEvidenceList signature.toMatcherSig clauses
        (terminalHoleCaps terminal rawHoleLists) terminalEvidence →
      ClausesTy signature terminal (context.applySubst terminal) clauses
        (capability.apply terminal.cap) (terminal.apply (.var q.nextTy))
        terminalEvidence) :
    RuntimeTyping signature (context.applySubst terminal) (.matcher clauses)
      (terminal.apply (.matcher capability (.var q.nextTy))) := by
  rcases audit.valid with
    ⟨terminalEvidence, collectedAtTerminal, inferredAtTerminal,
      clauseCapsAtTerminal, armsAtTerminal, coverageAtTerminal⟩
  have clausesTyping := clausesAtTerminal terminalEvidence
    (Inference.clauseCapsListCheck_sound clauseCapsAtTerminal)
    (Inference.collectClauseEvidence_sound collectedAtTerminal)
  have binderWitness := Inference.matcherBindersCheck_sound binders
  simpa only [Subst.apply_matcher] using
    RuntimeTyping.matcher
      (ResolvedClausesTy.ofShared clausesTyping)
      inferredAtTerminal
      (Inference.catchAllLastCheck_sound catchAll)
      (Inference.armExhaustiveCheck_sound armsAtTerminal)
      binderWitness.1 binderWitness.2
      (Inference.coverageCheck_sound coverageAtTerminal)

end DDTerminalAudit
end TypePM
