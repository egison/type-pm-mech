import TypePM.DemandTypingInferenceCompletenessTraversal
import TypePM.DemandTypingInferenceCompletenessAlignmentTraversal
import TypePM.DemandTypingInferenceCompletenessPatternTraversal

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
open DemandTypingInferenceCompletenessPatternTraversal

/-- Type constructors preserve the residual equations pointwise. -/
def TyBisimulation.listT
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {relation : StateBisimulation ledger declarative executable}
    {declarativeTarget executableTarget : Ty}
    (related : TyBisimulation relation declarativeTarget executableTarget) :
    TyBisimulation relation (.listT declarativeTarget) (.listT executableTarget) := by
  constructor
  · simpa only [Subst.apply_listT] using congrArg Ty.listT related.forward
  · simpa only [Subst.apply_listT] using congrArg Ty.listT related.reverse

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
      protected_safe := finalRelation.protected_safe
      target := extension.transportTy run.target }

/-- Finish a synthesized run at a fixed constructor-built result target. -/
def SynthRunCompletion.finishAs
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {ledger' : CapabilityOriginLedger} {innerTarget : Ty}
    (run : SynthRunCompletion before operation q' S' ledger' innerTarget)
    (expression : Expr) (path : SyntaxPath)
    (declarativeTarget executableTarget : Ty)
    (targetRelation : TyBisimulation run.transition.after declarativeTarget
      executableTarget) :
    SynthRunCompletion before
      (do
        let inner ← operation
        pure (Inference.finishExpr expression path executableTarget inner.state))
      q' S' ledger' declarativeTarget := by
  let event := TraceEvent.inferredExpr expression executableTarget path
  let extension := run.transition.after.recordEventExtension event
  let finalRelation := run.completion.state.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  refine
    { result := Inference.finishExpr expression path executableTarget run.result.state
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
      protected_safe := finalRelation.protected_safe
      target := extension.transportTy targetRelation }
  calc
    _ = (some run.result).bind (fun inner => some
        (Inference.finishExpr expression path executableTarget inner.state)) :=
      congrArg (fun candidate : Option ExprResult => candidate.bind (fun inner =>
        some (Inference.finishExpr expression path executableTarget inner.state)))
        run.success
    _ = some (Inference.finishExpr expression path executableTarget
        run.result.state) := rfl

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
      protected_safe := finalRelation.protected_safe
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

/-- Ordinary (non-matcher-body) recursion is structural after reconstructing
the canonical two-fresh placeholder, traversing the body, and completing the
result alignment. -/
def inferExprFuel_fix_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {self argument : String} {body : Expr} {bodyTarget : Ty}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ : Subst}
    {ledger ledger₁ ledger₂ : CapabilityOriginLedger} {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (bodyComplete :
      let visited := relation.visit .exprFix path
      let domainAllocation := visited.freshTy
        (freshOrigin .recursiveBinder path "fix-domain")
      let codomainAllocation := domainAllocation.state.freshTy
        (freshOrigin .recursiveBinder path "fix-codomain")
      let executablePlaceholder := Ty.fn (fixDomain initial path)
        (fixCodomain initial path)
      let placeholderEvent := TraceEvent.fixPlaceholder self argument
        executablePlaceholder path
      let directEvent := TraceEvent.directSelfAccepted self executablePlaceholder path
      let bodyRelation := (codomainAllocation.state.recordEvent placeholderEvent
        (by simp [placeholderEvent, TraceEvent.allocatedCapVars])).recordEvent
          directEvent (by simp [directEvent, TraceEvent.allocatedCapVars])
      let insideContext :=
        (argument, Scheme.mono (fixDomain initial path)) ::
          (self, Scheme.mono executablePlaceholder) :: context
      let insideSelf := (self, executablePlaceholder) ::
        (selfEnv.eraseMany [self, argument])
      SynthRunCompletion bodyRelation
        (inferExprFuel fuel signature insideContext insideSelf (0 :: path) body
          (fixBodyEntryState initial path self argument)) q₁ S₁ ledger₁
        bodyTarget)
    (alignmentComplete : StateRunCompletion bodyComplete.completion.state
      (alignTypes bodyComplete.result.state
        (freshOrigin .recursiveBinder path "fix-result")
        bodyComplete.result.target (fixCodomain initial path))
      q₂ S₂ ledger₂) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.fix self argument body) initial)
      q₂ S₂ ledger₂
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) := by
  let visited := relation.visit .exprFix path
  let domainOrigin := freshOrigin .recursiveBinder path "fix-domain"
  let codomainOrigin := freshOrigin .recursiveBinder path "fix-codomain"
  let resultOrigin := freshOrigin .recursiveBinder path "fix-result"
  let domainAllocation := visited.freshTy domainOrigin
  let codomainAllocation := domainAllocation.state.freshTy codomainOrigin
  let executablePlaceholder := Ty.fn (fixDomain initial path)
    (fixCodomain initial path)
  let declarativePlaceholder := Ty.fn (.var q.nextTy) (.var (q.nextTy + 1))
  have placeholderAtAllocation : TyBisimulation
      codomainAllocation.state.prevailing declarativePlaceholder
      executablePlaceholder := by
    have domainEq := domainAllocation.target_eq
    have codomainEq := codomainAllocation.target_eq
    change fixDomain initial path = .var q.nextTy at domainEq
    change fixCodomain initial path = .var (q.nextTy + 1) at codomainEq
    dsimp [declarativePlaceholder, executablePlaceholder]
    rw [relation.supply_eq]
    exact codomainAllocation.state.prevailing.sameTarget _
  let placeholderEvent := TraceEvent.fixPlaceholder self argument
    executablePlaceholder path
  let directEvent := TraceEvent.directSelfAccepted self executablePlaceholder path
  let placeholderExtension := codomainAllocation.state.prevailing.recordEventExtension
    placeholderEvent
  let directExtension := placeholderExtension.after.recordEventExtension directEvent
  let placeholderAtBody := directExtension.transportTy
    (placeholderExtension.transportTy placeholderAtAllocation)
  let placeholderAfterBody := bodyComplete.transition.transportTy placeholderAtBody
  let placeholderAfterAlignment := alignmentComplete.transition.transportTy
    placeholderAfterBody
  let expression := Expr.fix self argument body
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.StateRunCompletion.finishExpr
      alignmentComplete expression path declarativePlaceholder
      executablePlaceholder placeholderAfterAlignment
  let domainExtension := visited.freshTyExtension domainOrigin
  let codomainExtension := domainAllocation.state.freshTyExtension codomainOrigin
  let prefixTransition :=
    (((((((relation.visitExtension .exprFix path).seq domainExtension).seq
      codomainExtension).seq placeholderExtension).seq directExtension).seq
      bodyComplete.transition).seq alignmentComplete.transition)
  let finishExtension := alignmentComplete.transition.after.recordEventExtension
    (.inferredExpr expression executablePlaceholder path)
  refine { finished with
    transition := prefixTransition.seq finishExtension
    success := ?_ }
  simp only [inferExprFuel]
  have gate : (self != argument && DirectSelf.check self body) = true :=
    (DirectSelf.fix_gate_eq_true self argument body).2 ⟨distinct, direct⟩
  rw [gate]
  let continuePlaceholder : Option (Ty × Ty × InferState) → Option ExprResult :=
    fun candidate =>
      match candidate with
      | none => none
      | some (domain, codomain, state) =>
          let placeholder := Ty.fn domain codomain
          let state := (state.recordEvent
            (.fixPlaceholder self argument placeholder path)).recordEvent
            (.directSelfAccepted self placeholder path)
          let shadowed := selfEnv.eraseMany [self, argument]
          let insideSelf := (self, placeholder) :: shadowed
          let insideContext :=
            (argument, Scheme.mono domain) ::
              (self, Scheme.mono placeholder) :: context
          match inferExprFuel fuel signature insideContext insideSelf
              (0 :: path) body state with
          | none => none
          | some bodyResult =>
              match alignTypes bodyResult.state resultOrigin bodyResult.target
                  codomain with
              | none => none
              | some state => some (Inference.finishExpr expression path
                  placeholder state)
  change continuePlaceholder
    (buildFixPlaceholder signature path body (visit initial .exprFix path)) =
      some finished.result
  calc
    _ = continuePlaceholder (some (fixDomain initial path,
        fixCodomain initial path, fixFreshState initial path)) :=
      congrArg continuePlaceholder
        (buildFixPlaceholder_nonMatcher signature initial path body nonMatcher)
    _ = (match inferExprFuel fuel signature
          ((argument, Scheme.mono (fixDomain initial path)) ::
            (self, Scheme.mono executablePlaceholder) :: context)
          ((self, executablePlaceholder) :: selfEnv.eraseMany [self, argument])
          (0 :: path) body (fixBodyEntryState initial path self argument) with
        | none => none
        | some bodyResult =>
            match alignTypes bodyResult.state resultOrigin bodyResult.target
                (fixCodomain initial path) with
            | none => none
            | some state => some (Inference.finishExpr expression path
                executablePlaceholder state)) := rfl
    _ = (match alignTypes bodyComplete.result.state resultOrigin
          bodyComplete.result.target (fixCodomain initial path) with
        | none => none
        | some state => some (Inference.finishExpr expression path
            executablePlaceholder state)) := by
      let continueBody : Option ExprResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some bodyResult =>
            match alignTypes bodyResult.state resultOrigin bodyResult.target
                (fixCodomain initial path) with
            | none => none
            | some state => some (Inference.finishExpr expression path
                executablePlaceholder state)
      exact congrArg continueBody bodyComplete.success
    _ = some (Inference.finishExpr expression path executablePlaceholder
          alignmentComplete.result) := by
      let continueAlignment : Option InferState → Option ExprResult :=
        fun candidate =>
          match candidate with
          | none => none
          | some state => some (Inference.finishExpr expression path
              executablePlaceholder state)
      exact congrArg continueAlignment alignmentComplete.success
    _ = some finished.result := rfl

/-- `matchAll` is structural once its target and pattern syntheses, target
alignment, matcher check, and body synthesis have completed in source order. -/
def inferExprFuel_matchAll_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {target matcher : Expr} {pattern : Pattern} {body : Expr}
    {targetTarget : Ty} {dual : Dual} {bindings : MonoCtx} {bodyTarget : Ty}
    {q q₁ q₂ q₃ q₄ q₅ : InferenceBase.FreshSupply}
    {S S₁ S₂ S₃ S₄ S₅ : Subst}
    {ledger ledger₁ ledger₂ ledger₃ ledger₄ ledger₅ :
      CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (targetComplete : SynthRunCompletion (relation.visit .exprMatchAll path)
      (inferExprFuel fuel signature context selfEnv (0 :: path) target
        (visit initial .exprMatchAll path)) q₁ S₁ ledger₁ targetTarget)
    (patternComplete : PatternRunCompletion targetComplete.completion.state
      (inferPatternFuel fuel signature context [] [] selfEnv (2 :: path) pattern
        targetComplete.result.state) q₂ S₂ ledger₂ dual bindings)
    (targetAlignmentComplete : StateRunCompletion patternComplete.completion
      (alignTypes patternComplete.result.state
        (freshOrigin .pattern (2 :: path) "match-target")
        patternComplete.result.dual.target targetComplete.result.target)
      q₃ S₃ ledger₃)
    (matcherComplete : StateRunCompletion targetAlignmentComplete.completion
      (checkExprFuel fuel signature context selfEnv (1 :: path) matcher
        (.slot patternComplete.result.dual.cap targetComplete.result.target)
        targetAlignmentComplete.result) q₄ S₄ ledger₄)
    (bodyComplete : SynthRunCompletion matcherComplete.completion
      (inferExprFuel fuel signature
        (patternComplete.result.bindings.toContext ++ context)
        (selfEnv.eraseMany pattern.patVars) (3 :: path) body
        matcherComplete.result) q₅ S₅ ledger₅ bodyTarget) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.matchAll target matcher pattern body) initial)
      q₅ S₅ ledger₅ (.listT bodyTarget) := by
  let expression := Expr.matchAll target matcher pattern body
  let resultRelation :=
    DemandTypingInferenceCompletenessExprTraversal.TyBisimulation.listT
      bodyComplete.target
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finishAs
      bodyComplete expression path (.listT bodyTarget)
      (.listT bodyComplete.result.target) resultRelation
  let prefixTransition :=
    (((((relation.visitExtension .exprMatchAll path).seq
      targetComplete.transition).seq patternComplete.transition).seq
      targetAlignmentComplete.transition).seq matcherComplete.transition).seq
      bodyComplete.transition
  let finishExtension := bodyComplete.transition.after.recordEventExtension
    (.inferredExpr expression (.listT bodyComplete.result.target) path)
  refine
    { result := finished.result
      success := ?_
      supply_eq := finished.supply_eq
      transition := prefixTransition.seq finishExtension
      declarative_bounded := finished.declarative_bounded
      executable_bounded := finished.executable_bounded
      forward_bounded := finished.forward_bounded
      reverse_bounded := finished.reverse_bounded
      ledger_below := finished.ledger_below
      executable_ledger_below := finished.executable_ledger_below
      protected_origins := finished.protected_origins
      protected_below := finished.protected_below
      allocated_recorded := finished.allocated_recorded
      protected_safe := finished.protected_safe
      target := finishExtension.transportTy resultRelation }
  simp only [inferExprFuel]
  let continueTarget : Option ExprResult → Option ExprResult := fun candidate =>
    match candidate with
    | none => none
    | some targetResult =>
        match inferPatternFuel fuel signature context [] [] selfEnv (2 :: path)
            pattern targetResult.state with
        | none => none
        | some patternResult =>
            match alignTypes patternResult.state
                (freshOrigin .pattern (2 :: path) "match-target")
                patternResult.dual.target targetResult.target with
            | none => none
            | some state =>
                match checkExprFuel fuel signature context selfEnv (1 :: path)
                    matcher (.slot patternResult.dual.cap targetResult.target)
                    state with
                | none => none
                | some state =>
                    let bodyContext := patternResult.bindings.toContext ++ context
                    let bodyEnv := selfEnv.eraseMany pattern.patVars
                    match inferExprFuel fuel signature bodyContext bodyEnv
                        (3 :: path) body state with
                    | none => none
                    | some bodyResult => some (Inference.finishExpr expression path
                        (.listT bodyResult.target) bodyResult.state)
  change continueTarget (inferExprFuel fuel signature context selfEnv
    (0 :: path) target (visit initial .exprMatchAll path)) = some finished.result
  calc
    _ = continueTarget (some targetComplete.result) :=
      congrArg continueTarget targetComplete.success
    _ = (match inferPatternFuel fuel signature context [] [] selfEnv
          (2 :: path) pattern targetComplete.result.state with
        | none => none
        | some patternResult =>
            match alignTypes patternResult.state
                (freshOrigin .pattern (2 :: path) "match-target")
                patternResult.dual.target targetComplete.result.target with
            | none => none
            | some state =>
                match checkExprFuel fuel signature context selfEnv (1 :: path)
                    matcher (.slot patternResult.dual.cap
                      targetComplete.result.target) state with
                | none => none
                | some state =>
                    match inferExprFuel fuel signature
                        (patternResult.bindings.toContext ++ context)
                        (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
                    | none => none
                    | some bodyResult => some (Inference.finishExpr expression path
                        (.listT bodyResult.target) bodyResult.state)) := rfl
    _ = (match alignTypes patternComplete.result.state
          (freshOrigin .pattern (2 :: path) "match-target")
          patternComplete.result.dual.target targetComplete.result.target with
        | none => none
        | some state =>
            match checkExprFuel fuel signature context selfEnv (1 :: path)
                matcher (.slot patternComplete.result.dual.cap
                  targetComplete.result.target) state with
            | none => none
            | some state =>
                match inferExprFuel fuel signature
                    (patternComplete.result.bindings.toContext ++ context)
                    (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
                | none => none
                | some bodyResult => some (Inference.finishExpr expression path
                    (.listT bodyResult.target) bodyResult.state)) := by
      let continuePattern : Option PatternResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some patternResult =>
            match alignTypes patternResult.state
                (freshOrigin .pattern (2 :: path) "match-target")
                patternResult.dual.target targetComplete.result.target with
            | none => none
            | some state =>
                match checkExprFuel fuel signature context selfEnv (1 :: path)
                    matcher (.slot patternResult.dual.cap
                      targetComplete.result.target) state with
                | none => none
                | some state =>
                    match inferExprFuel fuel signature
                        (patternResult.bindings.toContext ++ context)
                        (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
                    | none => none
                    | some bodyResult => some (Inference.finishExpr expression path
                        (.listT bodyResult.target) bodyResult.state)
      exact congrArg continuePattern patternComplete.success
    _ = (match checkExprFuel fuel signature context selfEnv (1 :: path) matcher
          (.slot patternComplete.result.dual.cap targetComplete.result.target)
          targetAlignmentComplete.result with
        | none => none
        | some state =>
            match inferExprFuel fuel signature
                (patternComplete.result.bindings.toContext ++ context)
                (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
            | none => none
            | some bodyResult => some (Inference.finishExpr expression path
                (.listT bodyResult.target) bodyResult.state)) := by
      let continueAlignment : Option InferState → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some state =>
            match checkExprFuel fuel signature context selfEnv (1 :: path) matcher
                (.slot patternComplete.result.dual.cap
                  targetComplete.result.target) state with
            | none => none
            | some state =>
                match inferExprFuel fuel signature
                    (patternComplete.result.bindings.toContext ++ context)
                    (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
                | none => none
                | some bodyResult => some (Inference.finishExpr expression path
                    (.listT bodyResult.target) bodyResult.state)
      exact congrArg continueAlignment targetAlignmentComplete.success
    _ = (match inferExprFuel fuel signature
          (patternComplete.result.bindings.toContext ++ context)
          (selfEnv.eraseMany pattern.patVars) (3 :: path) body
          matcherComplete.result with
        | none => none
        | some bodyResult => some (Inference.finishExpr expression path
            (.listT bodyResult.target) bodyResult.state)) := by
      let continueMatcher : Option InferState → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some state =>
            match inferExprFuel fuel signature
                (patternComplete.result.bindings.toContext ++ context)
                (selfEnv.eraseMany pattern.patVars) (3 :: path) body state with
            | none => none
            | some bodyResult => some (Inference.finishExpr expression path
                (.listT bodyResult.target) bodyResult.state)
      exact congrArg continueMatcher matcherComplete.success
    _ = some (Inference.finishExpr expression path
          (.listT bodyComplete.result.target) bodyComplete.result.state) := by
      let continueBody : Option ExprResult → Option ExprResult := fun candidate =>
        match candidate with
        | none => none
        | some bodyResult => some (Inference.finishExpr expression path
            (.listT bodyResult.target) bodyResult.state)
      exact congrArg continueBody bodyComplete.success
    _ = some finished.result := rfl

end DemandTypingInferenceCompletenessExprTraversal
end TypePM
