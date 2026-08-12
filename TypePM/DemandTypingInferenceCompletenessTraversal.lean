import TypePM.DemandTypingInferenceCompletenessStateMutual

/-!
# Raw traversal completeness

This module is the traversal-facing half of inference completeness.  The DD
and executable solvers may choose different orientations for the same MGU, so
the induction invariant does not identify their prevailing substitutions.
Instead it threads mutual factorization together with the pieces of mutable
state that syntax-directed allocation determines literally: the fresh supply
and capability-origin ledger.

The result packages below deliberately stop before terminal validation.  They
are the common motives for the mutually recursive raw traversal proof.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessTraversal

open Inference
open DemandTypingInferenceCompletenessStateMutual

/-- State relation used at every recursive traversal boundary.  History,
protected producer leaves, and provenance sources are append-only evidence
owned by the executable run; the DD indices determine only supply, prevailing
substitution up to mutual MGU factorization, and the chronological origin
ledger. -/
structure TraversalStateCorrespondence
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (executable : InferState) : Type where
  supply_eq : executable.supply = q
  ledger_eq : executable.capabilityOrigins = ledger
  prevailing : StateBisimulation ledger declarative executable

/-- Trace-only events preserve a traversal boundary. -/
def TraversalStateCorrespondence.recordEvent
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (event : TraceEvent) :
    TraversalStateCorrespondence q declarative ledger
      (state.recordEvent event) := by
  let extension := relation.prevailing.recordEventExtension event
  exact ⟨relation.supply_eq, relation.ledger_eq, extension.after⟩

/-- Visiting one syntax node is trace-only. -/
def TraversalStateCorrespondence.visit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) := by
  exact relation.recordEvent (.visit kind path)

def TraversalStateCorrespondence.visitExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    BisimulationExtension relation.prevailing ledger declarative
      (Inference.visit state kind path) :=
  relation.prevailing.recordEventExtension (.visit kind path)

def TraversalStateCorrespondence.afterVisit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) :=
  ⟨relation.supply_eq, relation.ledger_eq,
    (relation.visitExtension kind path).after⟩

def stateBisimulationFreshTyExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (before : StateBisimulation ledger declarative state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before ledger declarative
      (state.freshTy origin).2 where
  after :=
    { forward := before.forward
      forwardEquation := by
        change declarative = Subst.seq before.forward state.prevailing
        exact before.forwardEquation
      forwardAdmissible := before.forwardAdmissible
      reverse := before.reverse
      reverseEquation := by
        change state.prevailing = Subst.seq before.reverse declarative
        exact before.reverseEquation }
  transportTy := by
    intro declarativeTarget executableTarget related
    refine ⟨?_, ?_⟩
    · change declarative.apply declarativeTarget =
        before.forward.apply (state.prevailing.apply executableTarget)
      exact related.forward
    · change state.prevailing.apply executableTarget =
        before.reverse.apply (declarative.apply declarativeTarget)
      exact related.reverse

def TraversalStateCorrespondence.afterVisitFreshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (origin : ConstraintOrigin) :
    TraversalStateCorrespondence { q with nextTy := q.nextTy + 1 }
      declarative ledger ((Inference.visit state kind path).freshTy origin).2 :=
  let visitExtension := relation.visitExtension kind path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    origin
  ⟨by
      have supplyEq := relation.supply_eq
      subst q
      rfl,
    relation.ledger_eq, freshExtension.after⟩

def bisimulationExtensionChain3
    {ledger₀ ledger₁ ledger₂ ledger₃ : CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ : Subst} {s₀ s₁ s₂ s₃ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃) :
    BisimulationExtension before ledger₃ S₃ s₃ where
  after := third.after
  transportTy := fun related =>
    third.transportTy (second.transportTy (first.transportTy related))

def bisimulationExtensionChain4
    {ledger₀ ledger₁ ledger₂ ledger₃ ledger₄ :
      CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ S₄ : Subst}
    {s₀ s₁ s₂ s₃ s₄ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃)
    (fourth : BisimulationExtension third.after ledger₄ S₄ s₄) :
    BisimulationExtension before ledger₄ S₄ s₄ where
  after := fourth.after
  transportTy := fun related => fourth.transportTy
    (third.transportTy (second.transportTy (first.transportTy related)))

structure FreshTyCompletion
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (state : InferState)
    (origin : ConstraintOrigin) : Type where
  target_eq : (state.freshTy origin).1 = .var q.nextTy
  state : TraversalStateCorrespondence
    { q with nextTy := q.nextTy + 1 } declarative ledger
    (state.freshTy origin).2

/-- One target allocation agrees literally with the supply-indexed DD
allocation and leaves the prevailing substitution and origin ledger alone. -/
def TraversalStateCorrespondence.freshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    FreshTyCompletion q declarative ledger state origin := by
  have supplyEq := relation.supply_eq
  subst q
  constructor
  · rfl
  · refine ⟨rfl, relation.ledger_eq, ?_⟩
    exact (stateBisimulationFreshTyExtension relation.prevailing origin).after

def TraversalStateCorrespondence.freshTyExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension relation.prevailing ledger declarative
      (state.freshTy origin).2 :=
  stateBisimulationFreshTyExtension relation.prevailing origin

/-- Exact-state initialization is the diagonal of the traversal relation. -/
def TraversalStateCorrespondence.refl
    (state : InferState) :
    TraversalStateCorrespondence state.supply state.prevailing
      state.capabilityOrigins state :=
  ⟨rfl, rfl, StateBisimulation.refl _ _⟩

/-- Output relation for one raw synthesized type.  The two raw types need not
be syntactically equal (context instantiation may see differently oriented
prevailing MGUs), but their resolved forms are mutual instances through the
same residuals that relate the two prevailing states. -/
structure TypedTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTarget : Ty)
    (executable : InferState) (executableTarget : Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  target : TyBisimulation state.prevailing declarativeTarget executableTarget

/-- Output relation for a left-to-right list of synthesized types. -/
structure TypedListTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTargets : List Ty)
    (executable : InferState) (executableTargets : List Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  targets : TyListBisimulation state.prevailing declarativeTargets
    executableTargets

/-- A common raw type on both sides automatically gives a typed relation. -/
def TypedTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedTraversalStateCorrespondence q' declarative ledger target executable
      target := by
  exact ⟨relation, relation.prevailing.sameTarget target⟩

/-- A common raw list gives the pointwise list relation. -/
def TypedListTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {targets : List Ty}
    {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedListTraversalStateCorrespondence q' declarative ledger targets
      executable targets := by
  refine ⟨relation, ?_⟩
  induction targets with
  | nil => exact .nil
  | cons target targets induction =>
      exact .cons (relation.prevailing.sameTarget target) induction

/-- Pointwise mutual type correspondence is closed under product formation. -/
theorem tyListBisimulation_prod
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeTargets executableTargets : List Ty}
    (relation : TyListBisimulation state declarativeTargets executableTargets) :
    TyBisimulation state (.prod declarativeTargets)
      (.prod executableTargets) := by
  constructor
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).forward
    | cons head tail induction =>
        have headForward := head.forward
        unfold Subst.apply at headForward
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headForward]
        injection induction with tailEquality
        rw [tailEquality]
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).reverse
    | cons head tail induction =>
        have headReverse := head.reverse
        unfold Subst.apply at headReverse
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headReverse]
        injection induction with tailEquality
        rw [tailEquality]

/-- Mutual type correspondence is compositional for function types. -/
theorem tyBisimulation_fn
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeDomain declarativeBody executableDomain executableBody : Ty}
    (domain : TyBisimulation state declarativeDomain executableDomain)
    (body : TyBisimulation state declarativeBody executableBody) :
    TyBisimulation state (.fn declarativeDomain declarativeBody)
      (.fn executableDomain executableBody) := by
  constructor
  · have domainForward := domain.forward
    have bodyForward := body.forward
    unfold Subst.apply at domainForward bodyForward ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainForward, bodyForward]
  · have domainReverse := domain.reverse
    have bodyReverse := body.reverse
    unfold Subst.apply at domainReverse bodyReverse ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainReverse, bodyReverse]

/-- Output package for expression synthesis. -/
def SynthCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (target : Ty)
    (result : ExprResult) : Type :=
  TypedTraversalStateCorrespondence q' declarative ledger target result.state
    result.target

/-- Output package for expression-list synthesis. -/
def SynthsCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (targets : List Ty)
    (result : ExprsResult) : Type :=
  TypedListTraversalStateCorrespondence q' declarative ledger targets
    result.state result.targets

/-- A successful executable expression run paired with its typed output
correspondence.  The package lives in `Type` because the state bisimulation
retains the concrete residual substitutions used by later cuts. -/
structure SynthRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  result : ExprResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  ledger_eq : result.state.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  target : TyBisimulation transition.after target result.target

/-- List counterpart of `SynthRunCompletion`. -/
structure SynthsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) : Type where
  result : ExprsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  ledger_eq : result.state.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  targets : TyListBisimulation transition.after targets result.targets

/-- Repackage a run's proof-relevant transition as the output-only relation. -/
def SynthRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger} {target : Ty}
    (run : SynthRunCompletion before operation q' declarative ledger target) :
    SynthCompletion q' declarative ledger target run.result :=
  ⟨⟨run.supply_eq, run.ledger_eq, run.transition.after⟩, run.target⟩

def SynthsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty}
    (run : SynthsRunCompletion before operation q' declarative ledger targets) :
    SynthsCompletion q' declarative ledger targets run.result :=
  ⟨⟨run.supply_eq, run.ledger_eq, run.transition.after⟩, run.targets⟩

/-- State-only run package used by alignment cuts. -/
structure StateRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  result : InferState
  success : operation = some result
  supply_eq : result.supply = q'
  ledger_eq : result.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result

def StateRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    (run : StateRunCompletion before operation q' declarative ledger) :
    TraversalStateCorrespondence q' declarative ledger run.result :=
  ⟨run.supply_eq, run.ledger_eq, run.transition.after⟩

/-! ## Ordinary paired alignment -/

/-- Once solver completeness supplies the concrete target-equality step, one
resolved equality cut preserves the proof-relevant traversal invariant.  This
lemma isolates the traversal algebra from the executable solver's fuel proof. -/
noncomputable def runResolvedTargetEq_complete_of_step
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin} {step : SolveStep}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta)
    (solver : PairedUnification.PairedResult ledger
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
    (stepSuccess : solveResolvedWithLedger ledger initial.trace.solves.length
      origin (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step)
    (stepDelta : step.delta = solver.subst) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.targetEq (initial.prevailing.apply executableLeft)
          (initial.prevailing.apply executableRight))) q
      (Subst.seq delta S) ledger := by
  let result := initial.recordSolve step
  refine ⟨result, ?_, relation.supply_eq, relation.ledger_eq, ?_⟩
  · unfold runResolvedConstraint
    rw [relation.ledger_eq, stepSuccess]
    rfl
  · exact relation.prevailing.pairedCut_recordSolve left right dd solver
      stepDelta

/-- The ordinary branch of `alignTypes` is complete once the paired solver
step has been constructed.  Matcher/slot two-stage branches are added by the
same state-cut lemma after capability-solver completeness is connected. -/
noncomputable def alignTypes_ordinary_complete_of_step
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin} {step : SolveStep}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (_declarativeClass :
      alignPairClass (S.apply declarativeLeft) (S.apply declarativeRight) =
        .ordinary)
    (executableClass :
      alignPairClass (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight) = .ordinary)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta)
    (solver : PairedUnification.PairedResult ledger
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
    (stepSuccess : solveResolvedWithLedger ledger initial.trace.solves.length
      origin (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step)
    (stepDelta : step.delta = solver.subst) :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q
      (Subst.seq delta S) ledger := by
  have core := runResolvedTargetEq_complete_of_step relation left right dd
    solver stepSuccess stepDelta
  let aligned := core.result
  let result := aligned.recordEvent (.typeAlignment
    initial.trace.solves.length aligned.trace.solves.length executableLeft
    executableRight (initial.prevailing.apply executableLeft)
    (initial.prevailing.apply executableRight))
  let finishExtension := core.transition.after.recordEventExtension
    (.typeAlignment initial.trace.solves.length aligned.trace.solves.length
      executableLeft executableRight
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
  refine ⟨result, ?_, core.supply_eq, core.ledger_eq,
    core.transition.seq finishExtension⟩
  · have coreEq : alignTypesCore initial origin executableLeft
        executableRight =
        runResolvedConstraint initial origin
          (.targetEq (initial.prevailing.apply executableLeft)
            (initial.prevailing.apply executableRight)) := by
      generalize leftEq : initial.prevailing.apply executableLeft = leftView
      generalize rightEq : initial.prevailing.apply executableRight = rightView
      cases leftView <;> cases rightView <;>
        simp_all [alignTypesCore, alignPairClass]
    unfold alignTypes
    rw [coreEq, core.success]
    rfl

/-- Finishing an expression changes only the trace and retains its raw target. -/
def synthCompletion_finishExpr
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {state : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger state)
    (expression : Expr) (path : SyntaxPath) :
    SynthCompletion q' declarative ledger target
      (finishExpr expression path target state) := by
  exact TypedTraversalStateCorrespondence.of_sameRaw
    (relation.recordEvent (.inferredExpr expression target path))

/-! ## Solver-independent expression constructors -/

/-- Integer literals always complete at any positive fuel. -/
def inferExprFuel_lit_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {value : Int} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path (.lit value)
        initial) q declarative ledger .int := by
  let entered := visit initial .exprLit path
  let result := finishExpr (.lit value) path .int entered
  let visitExtension := relation.visitExtension .exprLit path
  let finishExtension := visitExtension.after.recordEventExtension
    (.inferredExpr (.lit value) .int path)
  refine ⟨result, ?_, relation.supply_eq, relation.ledger_eq,
    visitExtension.seq finishExtension, ?_⟩
  · simp [inferExprFuel, result, entered, finishExpr, visit]
  exact (visitExtension.seq finishExtension).after.sameTarget .int

/-- `something` performs exactly one deterministic target allocation. -/
def inferExprFuel_something_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path .something
        initial) { q with nextTy := q.nextTy + 1 } declarative ledger
          (.matcher .any (.var q.nextTy)) := by
  let entered := visit initial .exprSomething path
  have enteredRelation := relation.visit .exprSomething path
  let allocated := entered.freshTy
    (freshOrigin .expression path "something-target")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "something-target")
  let result := finishExpr .something path (.matcher .any (.var q.nextTy))
    allocated.2
  let visitExtension := relation.visitExtension .exprSomething path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "something-target")
  let finishExtension := freshExtension.after.recordEventExtension
    (.inferredExpr .something (.matcher .any (.var q.nextTy)) path)
  refine ⟨result, ?_, allocatedRelation.state.supply_eq,
    allocatedRelation.state.ledger_eq,
    bisimulationExtensionChain3 visitExtension freshExtension finishExtension,
    ?_⟩
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by
      exact allocatedRelation.target_eq]
  exact finishExtension.after.sameTarget _

/-- Lambda synthesis is structural once the recursive body run has been
constructed from the deterministically allocated domain metavariable. -/
def inferExprFuel_lam_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {body : Expr}
    {bodyTarget : Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (bodyComplete : SynthRunCompletion
      (relation.afterVisitFreshTy .exprLam path
        (freshOrigin .expression path "lambda-domain"))
      (inferExprFuel fuel signature
        ((name, Scheme.mono (.var q.nextTy)) :: context)
        (selfEnv.erase name) (0 :: path) body
        ((visit initial .exprLam path).freshTy
          (freshOrigin .expression path "lambda-domain")).2)
      q' S' ledger' bodyTarget) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.lam name body) initial) q' S' ledger'
        (.fn (.var q.nextTy) bodyTarget) := by
  let entered := visit initial .exprLam path
  have enteredRelation := relation.visit .exprLam path
  let allocated := entered.freshTy
    (freshOrigin .expression path "lambda-domain")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "lambda-domain")
  let bodyResult := bodyComplete.result
  let result := finishExpr (.lam name body) path
    (.fn (.var q.nextTy) bodyResult.target) bodyResult.state
  let visitExtension := relation.visitExtension .exprLam path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "lambda-domain")
  let finishExtension := bodyComplete.transition.after.recordEventExtension
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyResult.target) path)
  refine ⟨result, ?_, bodyComplete.supply_eq, bodyComplete.ledger_eq,
    bisimulationExtensionChain4 visitExtension freshExtension
      bodyComplete.transition finishExtension, ?_⟩
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by exact allocatedRelation.target_eq]
    rw [bodyComplete.success]
  · have domainAtFinal : TyBisimulation
        bodyComplete.transition.after
        (.var q.nextTy) (.var q.nextTy) :=
      bodyComplete.transition.after.sameTarget _
    exact finishExtension.transportTy
      (tyBisimulation_fn domainAtFinal bodyComplete.target)

/-! ## List and tuple constructor slices

These lemmas expose the recursive hypotheses expected by the eventual mutual
induction.  Their fuel parameter is the predecessor passed uniformly to all
children by `inferExprFuel`.
-/

/-- The empty expression list succeeds without inspecting solver state. -/
def inferExprsFuel_nil_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index []
        initial) q declarative ledger [] := by
  refine ⟨⟨[], initial⟩, ?_, relation.supply_eq, relation.ledger_eq,
    .refl relation.prevailing, .nil⟩
  simp [inferExprsFuel]

/-- One expression-list cell composes the head and tail completion packages. -/
def inferExprsFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (headComplete : SynthRunCompletion relation
      (inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial) q₁ S₁ ledger₁ target)
    (tailComplete : SynthsRunCompletion headComplete.completion.state
      (inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions headComplete.result.state) q' S' ledger' targets)
    :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) initial) q' S' ledger'
        (target :: targets) := by
  let head := headComplete.result
  let tail := tailComplete.result
  have headSuccess := headComplete.success
  have tailSuccess := tailComplete.success
  refine ⟨⟨head.target :: tail.targets, tail.state⟩, ?_,
    tailComplete.supply_eq, tailComplete.ledger_eq,
    headComplete.transition.seq tailComplete.transition, ?_⟩
  · simp [inferExprsFuel, headSuccess, tailSuccess, head, tail]
  · exact .cons (tailComplete.transition.transportTy headComplete.target)
      tailComplete.targets

/-- Tuple synthesis is immediate once its list traversal completes. -/
def inferExprFuel_tuple_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expressions : List Expr}
    {targets : List Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (childrenComplete : SynthsRunCompletion
      (relation.afterVisit .exprTuple path)
      (inferExprsFuel fuel signature context selfEnv path 0 expressions
        (visit initial .exprTuple path)) q' S' ledger' targets) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.tuple expressions) initial) q' S' ledger' (.prod targets) := by
  let children := childrenComplete.result
  have childrenSuccess := childrenComplete.success
  let result := finishExpr (.tuple expressions) path (.prod children.targets)
    children.state
  let visitExtension := relation.visitExtension .exprTuple path
  let finishExtension := childrenComplete.transition.after.recordEventExtension
    (.inferredExpr (.tuple expressions) (.prod children.targets) path)
  refine ⟨result, ?_, childrenComplete.supply_eq,
    childrenComplete.ledger_eq,
    bisimulationExtensionChain3 visitExtension childrenComplete.transition
      finishExtension, ?_⟩
  · simp [inferExprFuel, childrenSuccess, result, children]
  · exact finishExtension.transportTy
      (tyListBisimulation_prod childrenComplete.targets)

end DemandTypingInferenceCompletenessTraversal
end TypePM
