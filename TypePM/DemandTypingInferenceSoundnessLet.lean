import TypePM.BridgeChecks
import TypePM.DemandTypingInferenceSoundness

/-!
# Let reconstruction for direct inference soundness

This module isolates the two generalization obligations attached to an
executable `let` traversal.

* `DemandSynthOrigin.letE` records only chronological traversal and ledger flow.
* `DemandSynthTerminalAudit.letE` asks for generalization stability at the chosen
  root terminal cut.

The first theorem below therefore composes the two recursive demand-directed runs without
a generalization premise.  The second theorem recovers the one required
terminal equation directly from the finite `WBridgeWF` validator certificate
and chronological event membership.
-/

namespace TypePM
namespace Inference

/-- Compose the value and body runs of one executable let.  Recording the
generalization event changes neither demand-directed state index nor the capability-origin
ledger, so the recursive runs meet at exactly the declarative let boundary. -/
theorem DemandSynthRun.letE
    {signature : FrozenSig} {context : Context} {name : String}
    {value body : Expr} {initial : InferState} {path : SyntaxPath}
    {valueResult bodyResult : ExprResult}
    (valueRun : DemandSynthRun signature context value initial valueResult)
    (bodyRun : DemandSynthRun signature
      ((name, signature.generalize
        (context.applySubst valueResult.state.prevailing)
        (valueResult.state.prevailing.apply valueResult.target)) :: context)
      body
      (valueResult.state.recordEvent
        (.letGeneralization valueResult.state.trace.solves.length name context
          valueResult.target
          (context.applySubst valueResult.state.prevailing)
          (valueResult.state.prevailing.apply valueResult.target)
          (signature.generalize
            (context.applySubst valueResult.state.prevailing)
            (valueResult.state.prevailing.apply valueResult.target))))
      bodyResult) :
    DemandSynthRun signature context (.letE name value body) initial
      (finishExpr (.letE name value body) path bodyResult.target
        bodyResult.state) := by
  rcases valueRun with
    ⟨valueTarget, valueDerived, valueTargetEq, valueOrigin⟩
  subst valueTarget
  rcases bodyRun with
    ⟨bodyTarget, bodyDerived, bodyTargetEq, bodyOrigin⟩
  change DemandSynth signature initial.supply initial.prevailing context value
    valueResult.target valueResult.state.supply
      valueResult.state.prevailing at valueDerived
  change DemandSynthOrigin signature valueDerived initial.capabilityOrigins
    valueResult.state.capabilityOrigins at valueOrigin
  simp only [InferState.recordEvent_supply,
    InferState.prevailing_recordEvent,
    InferState.recordEvent_capabilityOrigins] at bodyDerived bodyOrigin
  refine ⟨bodyTarget, DemandSynth.letE valueDerived bodyDerived, ?_, ?_⟩
  · simpa [finishExpr] using bodyTargetEq
  · simpa [finishExpr] using
      DemandSynthOrigin.letE valueOrigin bodyOrigin

/-- The terminal generalization event checked by `WBridgeWF` is exactly the
`LetFacts` payload required by the terminal audit tree. -/
theorem DDTerminalAudit.LetFacts.ofWBridgeWF
    {signature : FrozenSig} {context : Context} {name : String}
    {valueResult : ExprResult} {terminal : InferState}
    (bridge : Reconstruction.WBridgeWF signature terminal)
    (history : InferState.HistoryPrefix
      (valueResult.state.recordEvent
        (.letGeneralization valueResult.state.trace.solves.length name context
          valueResult.target
          (context.applySubst valueResult.state.prevailing)
          (valueResult.state.prevailing.apply valueResult.target)
          (signature.generalize
            (context.applySubst valueResult.state.prevailing)
            (valueResult.state.prevailing.apply valueResult.target))))
      terminal) :
    DDTerminalAudit.LetFacts terminal.prevailing signature context
      valueResult.target valueResult.state.prevailing := by
  let event := TraceEvent.letGeneralization
    valueResult.state.trace.solves.length name context valueResult.target
    (context.applySubst valueResult.state.prevailing)
    (valueResult.state.prevailing.apply valueResult.target)
    (signature.generalize
      (context.applySubst valueResult.state.prevailing)
      (valueResult.state.prevailing.apply valueResult.target))
  have localMembership : event ∈
      (valueResult.state.recordEvent event).trace.events := by
    simp [event, InferState.recordEvent]
  have finalMembership : event ∈ terminal.trace.events :=
    history.event_mem localMembership
  rcases bridge.generalization event finalMembership with
    ⟨_solveBound, _contextEq, _targetEq, _schemeEq, terminalEq⟩
  exact ⟨by simpa [event] using terminalEq⟩

/-- At a root let boundary, the public terminal bridge supplies the terminal
audit fact while the two recursive runs independently supply chronological
origin evidence. -/
theorem DemandSynthRun.letEAtValidatedRoot
    {signature : FrozenSig} {context : Context} {name : String}
    {value body : Expr} {initial : InferState} {path : SyntaxPath}
    {valueResult bodyResult : ExprResult} {fuel : Nat} {selfEnv : SelfEnv}
    (valueRun : DemandSynthRun signature context value initial valueResult)
    (bodyRun : DemandSynthRun signature
      ((name, signature.generalize
        (context.applySubst valueResult.state.prevailing)
        (valueResult.state.prevailing.apply valueResult.target)) :: context)
      body
      (valueResult.state.recordEvent
        (.letGeneralization valueResult.state.trace.solves.length name context
          valueResult.target
          (context.applySubst valueResult.state.prevailing)
          (valueResult.state.prevailing.apply valueResult.target)
          (signature.generalize
            (context.applySubst valueResult.state.prevailing)
            (valueResult.state.prevailing.apply valueResult.target))))
      bodyResult)
    (bodySuccess : inferExprFuel fuel signature
      ((name, signature.generalize
        (context.applySubst valueResult.state.prevailing)
        (valueResult.state.prevailing.apply valueResult.target)) :: context)
      (selfEnv.erase name) (1 :: path) body
      (valueResult.state.recordEvent
        (.letGeneralization valueResult.state.trace.solves.length name context
          valueResult.target
          (context.applySubst valueResult.state.prevailing)
          (valueResult.state.prevailing.apply valueResult.target)
          (signature.generalize
            (context.applySubst valueResult.state.prevailing)
            (valueResult.state.prevailing.apply valueResult.target)))) =
        some bodyResult)
    (bridge : Reconstruction.WBridgeWF signature
      (finishExpr (.letE name value body) path bodyResult.target
        bodyResult.state).state) :
    DemandSynthRun signature context (.letE name value body) initial
        (finishExpr (.letE name value body) path bodyResult.target
          bodyResult.state) ∧
      DDTerminalAudit.LetFacts
        (finishExpr (.letE name value body) path bodyResult.target
          bodyResult.state).state.prevailing
        signature context valueResult.target valueResult.state.prevailing := by
  let event := TraceEvent.letGeneralization
    valueResult.state.trace.solves.length name context valueResult.target
    (context.applySubst valueResult.state.prevailing)
    (valueResult.state.prevailing.apply valueResult.target)
    (signature.generalize
      (context.applySubst valueResult.state.prevailing)
      (valueResult.state.prevailing.apply valueResult.target))
  have history :
      (valueResult.state.recordEvent event).HistoryPrefix
        (finishExpr (.letE name value body) path bodyResult.target
          bodyResult.state).state :=
    (inferExprFuel_historyPrefix bodySuccess).trans
      (finishExpr_historyPrefix (.letE name value body) path
        bodyResult.target bodyResult.state)
  exact ⟨DemandSynthRun.letE valueRun bodyRun,
    DDTerminalAudit.LetFacts.ofWBridgeWF bridge history⟩

end Inference
end TypePM
