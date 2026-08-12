import TypePM.DemandTypingInferenceCompletenessTraversal
import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal

/-!
# Structural expression-branch completeness

This module packages expression branches whose recursive calls and alignment
runs are supplied by the outer mutual induction.  The wrappers contain no
caller-selected solver result: an alignment premise is itself a completed
state traversal.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessExprTraversal

open Inference
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation

/-- Finish an expression after an already completed synthesized sub-run. -/
def SynthRunCompletion.finish
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger' : CapabilityOriginLedger} {target : Ty}
    (run : SynthRunCompletion before operation q' S' ledger' target)
    (expression : Expr) (path : SyntaxPath) :
    SynthRunCompletion before
      (do
        let inner ← operation
        pure (finishExpr expression path inner.target inner.state))
      q' S' ledger' target := by
  let event := TraceEvent.inferredExpr expression run.result.target path
  let extension := run.transition.after.recordEventExtension event
  let finalRelation := run.completion.state.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  exact
    { result := finishExpr expression path run.result.target run.result.state
      success := by
        calc
          (do
              let inner ← operation
              pure (finishExpr expression path inner.target inner.state)) =
              (do
                let inner ← some run.result
                pure (finishExpr expression path inner.target inner.state)) :=
            congrArg (fun candidate => do
              let inner ← candidate
              pure (finishExpr expression path inner.target inner.state))
              run.success
          _ = some (finishExpr expression path run.result.target
              run.result.state) := rfl
      supply_eq := run.supply_eq
      transition := run.transition.seq extension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := extension.transportTy run.target }

/-- Finish an expression after an already completed state-only cut. -/
def StateRunCompletion.finishExpr
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger' : CapabilityOriginLedger}
    (run : StateRunCompletion before operation q' S' ledger')
    (expression : Expr) (path : SyntaxPath)
    (declarativeTarget executableTarget : Ty)
    (targetRelation : TyBisimulation run.transition.after declarativeTarget
      executableTarget) :
    SynthRunCompletion before
      (do
        let state ← operation
        pure (Inference.finishExpr expression path executableTarget state))
      q' S' ledger' declarativeTarget := by
  let event := TraceEvent.inferredExpr expression executableTarget path
  let extension := run.transition.after.recordEventExtension event
  let finalRelation := run.completion.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  refine
    { result := Inference.finishExpr expression path executableTarget run.result
      success := ?_
      supply_eq := run.supply_eq
      transition := run.transition.seq extension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      executable_ledger_below := finalRelation.executable_ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := extension.transportTy targetRelation }
  calc
    _ = (some run.result).bind (fun state =>
        some (Inference.finishExpr expression path executableTarget state)) :=
      congrArg (fun candidate : Option InferState => candidate.bind (fun state =>
        some (Inference.finishExpr expression path executableTarget state)))
        run.success
    _ = some (Inference.finishExpr expression path executableTarget run.result) := rfl

/-- `let` is structural after value and body traversal.  Signature closedness
is consumed exactly where the two generalized context entries are related. -/
def inferExprFuel_letE_complete
    {fuel : Nat} {signature : FrozenSig} (signatureClosed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {value body : Expr}
    {valueTarget bodyTarget : Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (valueComplete : SynthRunCompletion (relation.visit .exprLet path)
      (inferExprFuel fuel signature context selfEnv (0 :: path) value
        (visit initial .exprLet path)) q₁ S₁ ledger₁ valueTarget)
    (bodyComplete :
      let executableScheme := signature.generalize
        (context.applySubst valueComplete.result.state.prevailing)
        (valueComplete.result.state.prevailing.apply valueComplete.result.target)
      let generalizationEvent := TraceEvent.letGeneralization
        valueComplete.result.state.trace.solves.length name context
        valueComplete.result.target
        (context.applySubst valueComplete.result.state.prevailing)
        (valueComplete.result.state.prevailing.apply valueComplete.result.target)
        executableScheme
      let valueRelation := valueComplete.completion.state
      let recordedRelation := valueRelation.recordEvent generalizationEvent
        (by simp [generalizationEvent, TraceEvent.allocatedCapVars])
      SynthRunCompletion recordedRelation
        (inferExprFuel fuel signature
          ((name, executableScheme) :: context)
          (selfEnv.erase name) (1 :: path) body
          (valueComplete.result.state.recordEvent generalizationEvent))
        q' S' ledger' bodyTarget) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.letE name value body) initial) q' S' ledger' bodyTarget := by
  let enteredRelation := relation.visit .exprLet path
  let valueRelation := valueComplete.completion.state
  let executableScheme := signature.generalize
    (context.applySubst valueComplete.result.state.prevailing)
    (valueComplete.result.state.prevailing.apply valueComplete.result.target)
  have contextsAtValue := ContextBisimulation.same
    valueComplete.transition.after context
  have generalizedContexts := contextsAtValue.consGeneralized_complete signature
    signatureClosed name valueComplete.target
  let generalizationEvent := TraceEvent.letGeneralization
    valueComplete.result.state.trace.solves.length name context
    valueComplete.result.target
    (context.applySubst valueComplete.result.state.prevailing)
    (valueComplete.result.state.prevailing.apply valueComplete.result.target)
    executableScheme
  let eventExtension :=
    valueComplete.transition.after.recordEventExtension generalizationEvent
  let prefixTransition : BisimulationExtension relation.prevailing ledger₁ S₁
      (valueComplete.result.state.recordEvent generalizationEvent) :=
    (relation.visitExtension .exprLet path).seq valueComplete.transition |>.seq
      eventExtension
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finish
      bodyComplete (.letE name value body) path
  refine { finished with
    transition := (prefixTransition.seq bodyComplete.transition).seq
      (bodyComplete.transition.after.recordEventExtension
        (.inferredExpr (.letE name value body) bodyComplete.result.target path))
    success := ?_ }
  simp only [inferExprFuel]
  let continueValue : Option ExprResult → Option ExprResult := fun candidate =>
    match candidate with
    | none => none
    | some valueResult =>
        let normalizedContext := context.applySubst valueResult.state.prevailing
        let normalizedValue := valueResult.state.prevailing.apply valueResult.target
        let scheme := signature.generalize normalizedContext normalizedValue
        let state := valueResult.state.recordEvent
          (.letGeneralization valueResult.state.trace.solves.length name context
            valueResult.target normalizedContext normalizedValue scheme)
        match inferExprFuel fuel signature ((name, scheme) :: context)
            (selfEnv.erase name) (1 :: path) body state with
        | none => none
        | some bodyResult => some (finishExpr (.letE name value body) path
            bodyResult.target bodyResult.state)
  change continueValue (inferExprFuel fuel signature context selfEnv
      (0 :: path) value (visit initial .exprLet path)) = some finished.result
  calc
    _ = continueValue (some valueComplete.result) :=
      congrArg continueValue valueComplete.success
    _ = some finished.result := by
      dsimp [continueValue]
      let continueBody : Option ExprResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some bodyResult => some (finishExpr (.letE name value body) path
            bodyResult.target bodyResult.state)
      calc
        _ = continueBody (some bodyComplete.result) := congrArg continueBody
          bodyComplete.success
        _ = some finished.result := rfl

/-- Application is structural once both recursive syntheses and the two
alignment cuts have been completed.  The two fresh target allocations are
reconstructed directly from the shared supply, so neither an allocation
equality nor solver success is exposed as a premise. -/
def inferExprFuel_app_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {function argument : Expr} {functionTarget argumentTarget : Ty}
    {q q₁ q₂ q₃ q₄ : InferenceBase.FreshSupply}
    {S S₁ S₂ S₃ S₄ : Subst}
    {ledger ledger₁ ledger₂ ledger₃ ledger₄ : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (functionComplete : SynthRunCompletion (relation.visit .exprApp path)
      (inferExprFuel fuel signature context selfEnv (0 :: path) function
        (visit initial .exprApp path)) q₁ S₁ ledger₁ functionTarget)
    (alignmentComplete :
      let domainAllocation := functionComplete.completion.state.freshTy
        (freshOrigin .expression path "application-domain")
      let resultAllocation := domainAllocation.state.freshTy
        (freshOrigin .expression path "application-result")
      StateRunCompletion resultAllocation.state
        (alignTypes
          ((functionComplete.result.state.freshTy
            (freshOrigin .expression path "application-domain")).2.freshTy
              (freshOrigin .expression path "application-result")).2
          (freshOrigin .expression path "application-function")
          functionComplete.result.target
          (.fn (functionComplete.result.state.freshTy
              (freshOrigin .expression path "application-domain")).1
            ((functionComplete.result.state.freshTy
              (freshOrigin .expression path "application-domain")).2.freshTy
                (freshOrigin .expression path "application-result")).1))
        q₂ S₂ ledger₂)
    (argumentComplete :
      let domainAllocation := functionComplete.completion.state.freshTy
        (freshOrigin .expression path "application-domain")
      let resultAllocation := domainAllocation.state.freshTy
        (freshOrigin .expression path "application-result")
      SynthRunCompletion alignmentComplete.completion
        (inferExprFuel fuel signature context selfEnv (1 :: path) argument
          alignmentComplete.result) q₃ S₃ ledger₃ argumentTarget)
    (expectedComplete :
      let executableDomain := (functionComplete.result.state.freshTy
        (freshOrigin .expression path "application-domain")).1
      StateRunCompletion argumentComplete.completion.state
        (alignExprResultAtExpected (1 :: path) argumentComplete.result
          executableDomain) q₄ S₄ ledger₄) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.app function argument) initial)
      q₄ S₄ ledger₄ (.var (q₁.nextTy + 1)) := by
  let domainOrigin := freshOrigin .expression path "application-domain"
  let resultOrigin := freshOrigin .expression path "application-result"
  let functionOrigin := freshOrigin .expression path "application-function"
  let domainAllocation := functionComplete.completion.state.freshTy domainOrigin
  let resultAllocation := domainAllocation.state.freshTy resultOrigin
  let executableDomain := (functionComplete.result.state.freshTy domainOrigin).1
  let executableResult :=
    ((functionComplete.result.state.freshTy domainOrigin).2.freshTy resultOrigin).1
  have resultAtAllocation : TyBisimulation resultAllocation.state.prevailing
      (.var (q₁.nextTy + 1)) executableResult := by
    have resultEq := resultAllocation.target_eq
    change executableResult = .var (q₁.nextTy + 1) at resultEq
    rw [resultEq]
    exact resultAllocation.state.prevailing.sameTarget _
  let resultAfterAlignment := alignmentComplete.transition.transportTy
    resultAtAllocation
  let resultAfterArgument := argumentComplete.transition.transportTy
    resultAfterAlignment
  let resultAfterExpected := expectedComplete.transition.transportTy
    resultAfterArgument
  let expression := Expr.app function argument
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.StateRunCompletion.finishExpr
      expectedComplete expression path (.var (q₁.nextTy + 1)) executableResult
      resultAfterExpected
  let domainExtension := functionComplete.completion.state.freshTyExtension
    domainOrigin
  let resultExtension := domainAllocation.state.freshTyExtension resultOrigin
  let prefixTransition :=
    ((((((relation.visitExtension .exprApp path).seq functionComplete.transition).seq
      domainExtension).seq resultExtension).seq alignmentComplete.transition).seq
      argumentComplete.transition).seq expectedComplete.transition
  let finishExtension := expectedComplete.transition.after.recordEventExtension
    (.inferredExpr expression executableResult path)
  refine { finished with
    transition := prefixTransition.seq finishExtension
    success := ?_ }
  simp only [inferExprFuel]
  let continueFunction : Option ExprResult → Option ExprResult := fun candidate =>
    match candidate with
    | none => none
    | some functionResult =>
        let (domain, state) := functionResult.state.freshTy domainOrigin
        let (resultTarget, state) := state.freshTy resultOrigin
        match alignTypes state functionOrigin functionResult.target
            (.fn domain resultTarget) with
        | none => none
        | some state =>
            match inferExprFuel fuel signature context selfEnv (1 :: path)
                argument state with
            | none => none
            | some argumentResult =>
                match alignExprResultAtExpected (1 :: path) argumentResult domain with
                | none => none
                | some state => some (Inference.finishExpr expression path
                    resultTarget state)
  change continueFunction (inferExprFuel fuel signature context selfEnv
    (0 :: path) function (visit initial .exprApp path)) = some finished.result
  calc
    _ = continueFunction (some functionComplete.result) :=
      congrArg continueFunction functionComplete.success
    _ = (match alignTypes
          ((functionComplete.result.state.freshTy domainOrigin).2.freshTy
            resultOrigin).2
          functionOrigin functionComplete.result.target
          (.fn executableDomain executableResult) with
        | none => none
        | some state =>
            match inferExprFuel fuel signature context selfEnv (1 :: path)
                argument state with
            | none => none
            | some argumentResult =>
                match alignExprResultAtExpected (1 :: path) argumentResult
                    executableDomain with
                | none => none
                | some state => some (Inference.finishExpr expression path
                    executableResult state)) := by
      rfl
    _ = (match inferExprFuel fuel signature context selfEnv (1 :: path)
          argument alignmentComplete.result with
        | none => none
        | some argumentResult =>
            match alignExprResultAtExpected (1 :: path) argumentResult
                executableDomain with
            | none => none
            | some state => some (Inference.finishExpr expression path
                executableResult state)) := by
      let continueAlignment : Option InferState → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some state =>
            match inferExprFuel fuel signature context selfEnv (1 :: path)
                argument state with
            | none => none
            | some argumentResult =>
                match alignExprResultAtExpected (1 :: path) argumentResult
                    executableDomain with
                | none => none
                | some state => some (Inference.finishExpr expression path
                    executableResult state)
      exact congrArg continueAlignment alignmentComplete.success
    _ = (match alignExprResultAtExpected (1 :: path) argumentComplete.result
          executableDomain with
        | none => none
        | some state => some (Inference.finishExpr expression path
            executableResult state)) := by
      let continueArgument : Option ExprResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some argumentResult =>
            match alignExprResultAtExpected (1 :: path) argumentResult
                executableDomain with
            | none => none
            | some state => some (Inference.finishExpr expression path
                executableResult state)
      exact congrArg continueArgument argumentComplete.success
    _ = some (Inference.finishExpr expression path executableResult
          expectedComplete.result) := by
      let continueExpected : Option InferState → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some state => some (Inference.finishExpr expression path
            executableResult state)
      exact congrArg continueExpected expectedComplete.success
    _ = some finished.result := rfl

end DemandTypingInferenceCompletenessExprTraversal
end TypePM
