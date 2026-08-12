import TypePM.DemandTypingInferenceCompletenessMatcherTraversal
import TypePM.DemandTypingInferenceCompletenessCheckingAlignment
import TypePM.DemandTypingInferenceCompletenessFuel

/-!
# Main demand-typing inference completeness recursion

The origin judgments live in `Prop`, whereas traversal completions retain
concrete residual substitutions and therefore live in `Type`.  Consequently
the main recursion first proves `Nonempty` completion in `Prop`, then projects
the witness noncomputably.  This is the same proof-erasure boundary used by
the generic alignment completeness theorem.

This initial closed fragment covers expression leaves and the expression-free
primitive-pattern leaves, including their fuel-decreasing list traversals.
Its fragment certificates contain no executable-success equation and no
caller-selected solver result.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessMain

open Inference
open DemandTypingInferenceCompletenessFuel
open DemandTypingInferenceCompletenessTraversal
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessPatternTraversal
open DemandTypingInferenceCompletenessCheckingAlignment
open DemandTypingInferenceCompletenessMatcherTraversal

/-! ## Global recursion packages -/

/-- The executable checking cut consumes the raw synthesized type before
normalization.  Its boundedness is therefore an independent invariant: it
cannot be recovered from boundedness of the prevailing substitution after
that substitution has erased a raw metavariable. -/
structure BoundedSynthRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  run : SynthRunCompletion before operation q' declarative ledger target
  rawTargetBounded : run.result.target.BoundedBy q'

structure BoundedSynthsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) : Type where
  run : SynthsRunCompletion before operation q' declarative ledger targets
  rawTargetsBounded : ∀ target ∈ run.result.targets, target.BoundedBy q'

/-! The executable uses one fuel unit not only for a syntax node but also for
administrative traversals such as checking.  The public `inferenceFuel`
already reserves eight units per syntax-measure unit.  These predicates make
that reserve explicit in the global recursion instead of silently treating
checking as a zero-cost edge. -/

abbrev SynthBudgetAdequate (fuel : Nat) (expression : Expr) : Prop :=
  8 * (exprTraversalFuel expression + 1) ≤ fuel

abbrev CheckBudgetAdequate (fuel : Nat) (expression : Expr) : Prop :=
  8 * (exprTraversalFuel expression + 1) + 1 ≤ fuel

abbrev SynthsBudgetAdequate (fuel : Nat) (expressions : List Expr) : Prop :=
  8 * (exprListTraversalFuel expressions + 1) ≤ fuel

/-- A synthesis-completeness hypothesis which is stable under traversal:
unlike a hypothesis specialized to the initial call, it may be instantiated
at the state, supply, substitution, context, and path produced by any earlier
sibling.  The global mutual recursion will discharge this interface with its
own synthesis component. -/
abbrev SynthCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDSynth signature q S context expression target q' S'},
    (before : TraversalStateCorrespondence q S ledger state) →
    context.BoundedBy q →
    DDSynthOrigin signature raw ledger ledger' →
    SynthBudgetAdequate fuel expression →
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression state)
      q' S' ledger' target)

/-- Traversal-stable checking counterpart of `SynthCompletenessMotive`. -/
abbrev CheckCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {expected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDCheck signature q S context expression expected q' S'},
    (before : TraversalStateCorrespondence q S ledger state) →
    context.BoundedBy q → expected.BoundedBy q →
    DDCheckOrigin signature raw ledger ledger' →
    CheckBudgetAdequate fuel expression →
    Nonempty (StateRunCompletion before
      (checkExprFuel fuel signature context selfEnv path expression expected
        state) q' S' ledger')

def boundedSynthsNil_complete
    (fuel : Nat) (signature : FrozenSig) (context : Context)
    (selfEnv : SelfEnv) (parent : SyntaxPath) (index : Nat)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) :
    BoundedSynthsRunCompletion before
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index [] state)
      q S ledger [] := by
  refine ⟨inferExprsFuel_nil_complete before fuel, ?_⟩
  intro target membership
  change target ∈ [] at membership
  exact nomatch membership

def boundedSynthsCons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (head : BoundedSynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv (index :: parent)
        expression state) q₁ S₁ ledger₁ target)
    (tail : BoundedSynthsRunCompletion head.run.completion.state
      (inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions head.run.result.state) q' S' ledger' targets)
    (tailSupplyExtends : SupplyExtends q₁ q') :
    BoundedSynthsRunCompletion before
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) state) q' S' ledger'
      (target :: targets) := by
  let run := inferExprsFuel_cons_complete before head.run tail.run
  refine ⟨run, ?_⟩
  intro item membership
  change item ∈ head.run.result.target :: tail.run.result.targets at membership
  rcases List.mem_cons.mp membership with equality | tailMembership
  · subst item
    exact head.rawTargetBounded.mono tailSupplyExtends
  · exact tail.rawTargetsBounded item tailMembership

/-- Actual origin-tree dispatcher for expression lists, parameterized only by
the synthesis component of the later global mutual recursion.  In
particular, the motive is quantified over every intermediate state, so the
tail is proved at the concrete state returned by the head rather than at the
initial call site. -/
theorem synthsOrigin_complete_nonempty_from_synth
    {signature : FrozenSig} (synthComplete : SynthCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    {raw : DDSynths signature q S context expressions targets q' S'}
    (origin : DDSynthsOrigin signature raw ledger ledger')
    (adequate : SynthsBudgetAdequate fuel expressions) :
    Nonempty (BoundedSynthsRunCompletion before
      (inferExprsFuel fuel signature context selfEnv parent index expressions
        state) q' S' ledger' targets) := by
  cases fuel with
  | zero => simp [SynthsBudgetAdequate] at adequate
  | succ fuel =>
    cases origin with
    | nil => exact ⟨boundedSynthsNil_complete fuel signature context selfEnv
        parent index before⟩
    | @cons q S context expression expressions target targets q₁ S₁ q' S'
        ledger ledger₁ ledger' headRaw tailRaw headOrigin tailOrigin =>
        have headAdequate : SynthBudgetAdequate fuel expression := by
          simp only [SynthsBudgetAdequate, SynthBudgetAdequate,
            exprListTraversalFuel] at adequate ⊢
          omega
        have tailAdequate : SynthsBudgetAdequate fuel expressions := by
          simp only [SynthsBudgetAdequate, exprListTraversalFuel]
            at adequate ⊢
          omega
        let headRun := Classical.choice
          (synthComplete (selfEnv := selfEnv) (path := index :: parent)
            before contextBounded headOrigin headAdequate)
        have tailContextBounded : context.BoundedBy q₁ :=
          contextBounded.mono headOrigin.erase.supplyExtends
        let tailRun := Classical.choice
          (synthsOrigin_complete_nonempty_from_synth
            (selfEnv := selfEnv) (parent := parent) (index := index + 1)
            synthComplete fuel headRun.run.completion.state tailContextBounded
            tailOrigin tailAdequate)
        exact ⟨boundedSynthsCons_complete before headRun tailRun
          tailOrigin.erase.supplyExtends⟩
termination_by fuel

def boundedSynthLit_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {value : Int} {q : InferenceBase.FreshSupply}
    {S : Subst} {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) (fuel : Nat) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path (.lit value)
        state) q S ledger .int :=
  ⟨inferExprFuel_lit_complete before fuel, Ty.BoundedBy.int⟩

def boundedSynthSomething_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {q : InferenceBase.FreshSupply}
    {S : Subst} {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state) (fuel : Nat) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path .something state)
      { q with nextTy := q.nextTy + 1 } S ledger
      (.matcher .any (.var q.nextTy)) := by
  refine ⟨inferExprFuel_something_complete before fuel,
    Ty.BoundedBy.matcherOf ?_ ?_⟩
  · intro varId membership
    simp [Cap.fcv] at membership
  · exact Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)

def boundedSynthLam_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {bodyExpr : Expr}
    {bodyTarget : Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (bodyRun : BoundedSynthRunCompletion
      (before.afterVisitFreshTy .exprLam path
        (freshOrigin .expression path "lambda-domain"))
      (inferExprFuel fuel signature
        ((name, Scheme.mono (.var q.nextTy)) :: context)
        (selfEnv.erase name) (0 :: path) bodyExpr
        ((visit state .exprLam path).freshTy
          (freshOrigin .expression path "lambda-domain")).2)
      q' S' ledger' bodyTarget)
    (domainBounded : Ty.BoundedBy q' (.var q.nextTy)) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.lam name bodyExpr) state) q' S' ledger'
      (.fn (.var q.nextTy) bodyTarget) :=
  ⟨inferExprFuel_lam_complete before bodyRun.run,
    Ty.BoundedBy.fnOf domainBounded bodyRun.rawTargetBounded⟩

def boundedSynthTuple_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expressions : List Expr}
    {targets : List Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (children : BoundedSynthsRunCompletion
      (before.afterVisit .exprTuple path)
      (inferExprsFuel fuel signature context selfEnv path 0 expressions
        (visit state .exprTuple path)) q' S' ledger' targets) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.tuple expressions) state) q' S' ledger' (.prod targets) :=
  ⟨inferExprFuel_tuple_complete before children.run,
    Ty.BoundedBy.prodOfForall children.rawTargetsBounded⟩

def boundedSynthCtor_complete
    {fuel : Nat} {signature : FrozenSig} (closed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {name : String} {expressions : List Expr} {scheme : CtorScheme}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (lookup : signature.findDataCtor name = some scheme)
    (checks : StateRunCompletion
      (instantiateCtorInState_complete (before.visit .exprCtor path)
        scheme).correspondence
      (checkExprsFuel fuel signature context selfEnv path 0 expressions
        (instantiateCtorInState (visit state .exprCtor path) scheme).1.1
        (instantiateCtorInState (visit state .exprCtor path) scheme).2)
      q' S' ledger')
    (supplyExtension : SupplyExtends
      (InferenceBase.instantiateCtorScheme q scheme).supply q') :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.ctor name expressions) state) q' S'
      (DDLedger.freezeExport ledger' S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  refine ⟨inferExprFuel_ctor_complete before lookup checks, ?_⟩
  exact (instantiateCtorScheme_boundedBy
    ((closed.dataCtors lookup).boundedBy)).2.mono supplyExtension

def boundedSynthPrim_complete
    {fuel : Nat} {signature : FrozenSig} (closed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {op : PrimOp} {expressions : List Expr} {scheme : CtorScheme}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (lookup : signature.findPrimitive op = some scheme)
    (checks : StateRunCompletion
      (instantiateCtorInState_complete (before.visit .exprPrim path)
        scheme).correspondence
      (checkExprsFuel fuel signature context selfEnv path 0 expressions
        (instantiateCtorInState (visit state .exprPrim path) scheme).1.1
        (instantiateCtorInState (visit state .exprPrim path) scheme).2)
      q' S' ledger')
    (supplyExtension : SupplyExtends
      (InferenceBase.instantiateCtorScheme q scheme).supply q') :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.prim op expressions) state) q' S'
      (DDLedger.freezeExport ledger' S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  refine ⟨inferExprFuel_prim_complete before lookup checks, ?_⟩
  exact (instantiateCtorScheme_boundedBy
    ((closed.primitives lookup).boundedBy)).2.mono supplyExtension

def boundedSynthLet_complete
    {fuel : Nat} {signature : FrozenSig} (closed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {name : String} {value body : Expr} {valueTarget bodyTarget : Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (valueRun : BoundedSynthRunCompletion (before.visit .exprLet path)
      (inferExprFuel fuel signature context selfEnv (0 :: path) value
        (visit state .exprLet path)) q₁ S₁ ledger₁ valueTarget)
    (bodyRun :
      let executableScheme := signature.generalize
        (context.applySubst valueRun.run.result.state.prevailing)
        (valueRun.run.result.state.prevailing.apply valueRun.run.result.target)
      let event := TraceEvent.letGeneralization
        valueRun.run.result.state.trace.solves.length name context
        valueRun.run.result.target
        (context.applySubst valueRun.run.result.state.prevailing)
        (valueRun.run.result.state.prevailing.apply valueRun.run.result.target)
        executableScheme
      BoundedSynthRunCompletion
        (valueRun.run.completion.state.recordEvent event
          (by simp [event, TraceEvent.allocatedCapVars]))
        (inferExprFuel fuel signature ((name, executableScheme) :: context)
          (selfEnv.erase name) (1 :: path) body
          (valueRun.run.result.state.recordEvent event))
        q' S' ledger' bodyTarget) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.letE name value body) state) q' S' ledger' bodyTarget :=
  ⟨DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_letE_complete
    closed before valueRun.run bodyRun.run,
    bodyRun.rawTargetBounded⟩

def boundedSynthApp_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {function argument : Expr}
    {functionTarget argumentTarget : Ty}
    {q q₁ q₂ q₃ q₄ : InferenceBase.FreshSupply}
    {S S₁ S₂ S₃ S₄ : Subst}
    {ledger ledger₁ ledger₂ ledger₃ ledger₄ : CapabilityOriginLedger}
    {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (functionRun : BoundedSynthRunCompletion (before.visit .exprApp path)
      (inferExprFuel fuel signature context selfEnv (0 :: path) function
        (visit state .exprApp path)) q₁ S₁ ledger₁ functionTarget)
    (functionAlignment :
      let domainAllocation := functionRun.run.completion.state.freshTy
        (freshOrigin .expression path "application-domain")
      let resultAllocation := domainAllocation.state.freshTy
        (freshOrigin .expression path "application-result")
      StateRunCompletion resultAllocation.state
        (alignTypes
          ((functionRun.run.result.state.freshTy
            (freshOrigin .expression path "application-domain")).2.freshTy
              (freshOrigin .expression path "application-result")).2
          (freshOrigin .expression path "application-function")
          functionRun.run.result.target
          (.fn (functionRun.run.result.state.freshTy
              (freshOrigin .expression path "application-domain")).1
            ((functionRun.run.result.state.freshTy
              (freshOrigin .expression path "application-domain")).2.freshTy
                (freshOrigin .expression path "application-result")).1))
        q₂ S₂ ledger₂)
    (argumentRun : BoundedSynthRunCompletion functionAlignment.completion
      (inferExprFuel fuel signature context selfEnv (1 :: path) argument
        functionAlignment.result) q₃ S₃ ledger₃ argumentTarget)
    (expectedAlignment :
      let executableDomain := (functionRun.run.result.state.freshTy
        (freshOrigin .expression path "application-domain")).1
      StateRunCompletion argumentRun.run.completion.state
        (alignExprResultAtExpected (1 :: path) argumentRun.run.result
          executableDomain) q₄ S₄ ledger₄)
    (resultBounded :
      let run :=
        DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_app_complete
          before functionRun.run functionAlignment argumentRun.run
          expectedAlignment
      run.result.target.BoundedBy q₄) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.app function argument) state)
      q₄ S₄ ledger₄ (.var (q₁.nextTy + 1)) :=
  ⟨DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_app_complete
    before functionRun.run functionAlignment argumentRun.run expectedAlignment,
    resultBounded⟩

/-- Compose the `DDCheckOrigin.mk` boundary once the recursive synthesis run
has supplied its raw executable target and its syntactic bound.  Solver
success and expected-coercion selection remain internal to the generic
checking-alignment completeness theorem. -/
theorem checkOrigin_complete_nonempty_of_synth
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {expression : Expr} {expected rawTarget : Ty}
    {q q₁ : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedBounded : expected.BoundedBy q)
    {synthesized : DDSynth signature q S context expression rawTarget q₁ S₁}
    (synth : BoundedSynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression state)
      q₁ S₁ ledger₁ rawTarget)
    (aligned : DDAlignWithLedger ledger₁ S₁ rawTarget expected S') :
    Nonempty (StateRunCompletion before
      (checkExprFuel (fuel + 1) signature context selfEnv path expression
        expected state) q₁ S' ledger₁) := by
  have declarativeRawBounded :=
    (synthesized.boundedBy closed before.declarative_bounded contextBounded).2
  have expectedAtCut := expectedBounded.mono synthesized.supplyExtends
  let alignedRun := ddAlignWithLedger_complete (path := path)
    synth.run.completion.state
    synth.run.target (synth.run.completion.state.prevailing.sameTarget expected)
    declarativeRawBounded expectedAtCut synth.rawTargetBounded expectedAtCut
    aligned
  exact ⟨checkExprFuel_complete before synth.run alignedRun⟩

theorem checkOrigin_complete_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {expression : Expr} {expected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedBounded : expected.BoundedBy q)
    {raw : DDCheck signature q S context expression expected q' S'}
    (origin : DDCheckOrigin signature raw ledger ledger')
    (synthComplete : ∀ {rawTarget q₁ S₁ ledger₁}
      {synthesized : DDSynth signature q S context expression rawTarget q₁ S₁},
      DDSynthOrigin signature synthesized ledger ledger₁ →
      Nonempty (BoundedSynthRunCompletion before
        (inferExprFuel fuel signature context selfEnv path expression state)
        q₁ S₁ ledger₁ rawTarget)) :
    Nonempty (StateRunCompletion before
      (checkExprFuel (fuel + 1) signature context selfEnv path expression
        expected state) q' S' ledger') := by
  cases origin with
  | mk synthOrigin aligned =>
      let synth := Classical.choice (synthComplete synthOrigin)
      exact checkOrigin_complete_nonempty_of_synth
        (synthesized := synthOrigin.erase) closed fuel before
        contextBounded expectedBounded synth aligned

/-- The checking component generated from a traversal-stable synthesis
motive.  `CheckBudgetAdequate` pays exactly the extra unit consumed by
`checkExprFuel` before synthesis starts. -/
theorem checkOrigin_complete_nonempty_from_synth
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    (synthComplete : SynthCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {expression : Expr} {expected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedBounded : expected.BoundedBy q)
    {raw : DDCheck signature q S context expression expected q' S'}
    (origin : DDCheckOrigin signature raw ledger ledger')
    (adequate : CheckBudgetAdequate fuel expression) :
    Nonempty (StateRunCompletion before
      (checkExprFuel fuel signature context selfEnv path expression expected
        state) q' S' ledger') := by
  cases fuel with
  | zero => simp [CheckBudgetAdequate] at adequate
  | succ fuel =>
      have synthAdequate : SynthBudgetAdequate fuel expression := by
        simp only [CheckBudgetAdequate, SynthBudgetAdequate] at adequate ⊢
        omega
      cases origin with
      | mk synthOrigin aligned =>
          let synth := Classical.choice
            (synthComplete (selfEnv := selfEnv) (path := path)
              before contextBounded synthOrigin synthAdequate)
          exact checkOrigin_complete_nonempty_of_synth
            (synthesized := synthOrigin.erase) closed fuel before
            contextBounded expectedBounded synth aligned

theorem checkCompletenessMotive_of_synth
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    (synthComplete : SynthCompletenessMotive signature) :
    CheckCompletenessMotive signature := by
  intro fuel context selfEnv path expression expected q q' S S' ledger
    ledger' state raw before contextBounded expectedBounded origin adequate
  exact checkOrigin_complete_nonempty_from_synth closed synthComplete fuel
    before contextBounded expectedBounded origin adequate

def checksOrigin_nil_complete
    {signature : FrozenSig}
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state) :
    StateRunCompletion before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index [] []
        state) q S ledger :=
  checkExprsFuel_nil_complete fuel signature context selfEnv parent index before

def checksOrigin_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (head : StateRunCompletion before
      (checkExprFuel fuel signature context selfEnv (index :: parent)
        expression expected state) q₁ S₁ ledger₁)
    (tail : StateRunCompletion head.completion
      (checkExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions expecteds head.result) q' S' ledger') :
    StateRunCompletion before
      (checkExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) (expected :: expecteds) state)
      q' S' ledger' :=
  checkExprsFuel_cons_complete before head tail

/-- Actual origin-tree dispatcher for checking lists.  The recursive head
motive is traversal-stable, and the tail is recursively reconstructed from
the head's concrete completion state. -/
theorem checksOrigin_complete_nonempty_from_check
    {signature : FrozenSig} (checkComplete : CheckCompletenessMotive signature)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {expecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ expecteds, expected.BoundedBy q)
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    (origin : DDChecksOrigin signature raw ledger ledger')
    (adequate : SynthsBudgetAdequate fuel expressions) :
    Nonempty (StateRunCompletion before
      (checkExprsFuel fuel signature context selfEnv parent index expressions
        expecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [SynthsBudgetAdequate] at adequate
  | succ fuel =>
    cases origin with
    | nil => exact ⟨checksOrigin_nil_complete fuel before⟩
    | @cons q S context expression expressions expected expecteds q₁ S₁ q' S'
        ledger ledger₁ ledger' headRaw tailRaw headOrigin tailOrigin =>
        have headAdequate : CheckBudgetAdequate fuel expression := by
          simp only [SynthsBudgetAdequate, CheckBudgetAdequate,
            exprListTraversalFuel] at adequate ⊢
          omega
        have tailAdequate : SynthsBudgetAdequate fuel expressions := by
          simp only [SynthsBudgetAdequate, exprListTraversalFuel]
            at adequate ⊢
          omega
        have expectedBounded := expectedsBounded expected (by simp)
        let headRun := Classical.choice
          (checkComplete (selfEnv := selfEnv) (path := index :: parent)
            before contextBounded expectedBounded headOrigin headAdequate)
        have tailContextBounded : context.BoundedBy q₁ :=
          contextBounded.mono headOrigin.erase.supplyExtends
        have tailExpectedsBounded :
            ∀ item ∈ expecteds, item.BoundedBy q₁ := by
          intro item membership
          exact (expectedsBounded item (by simp [membership])).mono
            headOrigin.erase.supplyExtends
        let tailRun := Classical.choice
          (checksOrigin_complete_nonempty_from_check
            (selfEnv := selfEnv) (parent := parent) (index := index + 1)
            checkComplete fuel headRun.completion tailContextBounded
            tailExpectedsBounded tailOrigin tailAdequate)
        exact ⟨checksOrigin_cons_complete before headRun tailRun⟩
termination_by fuel

/-! ## Structural leaf certificates -/

inductive DDSynthLeafOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {target : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDSynth signature q S context expression target q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDSynthOrigin signature raw ledger ledger' -> Prop where
  | var
      {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
      {name : String} {scheme : Scheme} {ledger : CapabilityOriginLedger}
      (lookup : (context.applySubst S).find? name = some scheme) :
      DDSynthLeafOrigin signature (DDSynthOrigin.var lookup)
  | lit : DDSynthLeafOrigin signature DDSynthOrigin.lit
  | something : DDSynthLeafOrigin signature DDSynthOrigin.something

inductive DDDPatLeafOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {pattern : DPat} ->
    {target : Ty} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDDPat signature q S pattern target bindings q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDDPatOrigin signature raw ledger ledger' -> Prop where
  | var
      {q : InferenceBase.FreshSupply} {S : Subst}
      (name : String) {expectedTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDDPatLeafOrigin signature
        (DDDPatOrigin.var (name := name) (expectedTarget := expectedTarget))
  | wild : DDDPatLeafOrigin signature DDDPatOrigin.wild

inductive DDDPatsLeafOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} ->
    {patterns : List DPat} -> {targets : List Ty} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDDPats signature q S patterns targets bindings q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDDPatsOrigin signature raw ledger ledger' -> Prop where
  | nil : DDDPatsLeafOrigin signature DDDPatsOrigin.nil
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
      {patterns : List DPat} {target : Ty} {targets : List Ty}
      {bindings restBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ : Subst} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {headRaw : DDDPat signature q S pattern target bindings q₁ S₁}
      {tailRaw : DDDPats signature q₁ S₁ patterns targets restBindings q' S'}
      {headOrigin : DDDPatOrigin signature headRaw ledger ledger₁}
      {tailOrigin : DDDPatsOrigin signature tailRaw ledger₁ ledger'}
      (head : DDDPatLeafOrigin signature headOrigin)
      (tail : DDDPatsLeafOrigin signature tailOrigin)
      (disjoint :
        ∀ name, name ∈ bindings.names -> name ∉ restBindings.names) :
      DDDPatsLeafOrigin signature
        (DDDPatsOrigin.cons headOrigin tailOrigin disjoint)

inductive DDPPatLeafOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {pattern : PPat} ->
    {target : Ty} -> {holes : List Dual} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDPPat signature q S pattern target holes bindings q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDPPatOrigin signature raw ledger ledger' -> Prop where
  | hole : DDPPatLeafOrigin signature DDPPatOrigin.hole
  | wild : DDPPatLeafOrigin signature DDPPatOrigin.wild
  | pval
      {q : InferenceBase.FreshSupply} {S : Subst}
      (name : String) {expectedTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDPPatLeafOrigin signature
        (DDPPatOrigin.pval (name := name) (expectedTarget := expectedTarget))

inductive DDPPatsLeafOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} ->
    {patterns : List PPat} -> {targets : List Ty} -> {holes : List Dual} ->
    {bindings : MonoCtx} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    {raw : DDPPats signature q S patterns targets holes bindings q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDPPatsOrigin signature raw ledger ledger' -> Prop where
  | nil : DDPPatsLeafOrigin signature DDPPatsOrigin.nil
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
      {patterns : List PPat} {target : Ty} {targets : List Ty}
      {holes restHoles : List Dual} {bindings restBindings : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {headRaw : DDPPat signature q S pattern target holes bindings q₁ S₁}
      {tailRaw : DDPPats signature q₁ S₁ patterns targets restHoles
        restBindings q' S'}
      {headOrigin : DDPPatOrigin signature headRaw ledger ledger₁}
      {tailOrigin : DDPPatsOrigin signature tailRaw ledger₁ ledger'}
      (head : DDPPatLeafOrigin signature headOrigin)
      (tail : DDPPatsLeafOrigin signature tailOrigin)
      (disjoint :
        ∀ name, name ∈ bindings.names -> name ∉ restBindings.names) :
      DDPPatsLeafOrigin signature
        (DDPPatsOrigin.cons headOrigin tailOrigin disjoint)

/-! ## Expression leaves -/

theorem synthLeafOrigin_complete_nonempty
    {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (leaf : DDSynthLeafOrigin signature origin)
    (adequate : ExprAdequate fuel expression) :
    Nonempty (SynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases leaf with
  | var lookup =>
      exact ⟨inferExprFuel_var_complete before contexts lookup fuel⟩
  | lit => exact ⟨inferExprFuel_lit_complete before fuel⟩
  | something => exact ⟨inferExprFuel_something_complete before fuel⟩

noncomputable def synthLeafOrigin_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (leaf : DDSynthLeafOrigin signature origin)
    (adequate : ExprAdequate fuel expression) :
    SynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target :=
  Classical.choice
    (synthLeafOrigin_complete_nonempty fuel before contexts leaf adequate)

/-! ## Primitive data-pattern leaves and lists -/

theorem dpatLeafOrigin_complete_nonempty
    {signature : FrozenSig} {path : SyntaxPath} {pattern : DPat} {target : Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPat signature q S pattern target bindings q' S'}
    {origin : DDDPatOrigin signature raw ledger ledger'}
    (leaf : DDDPatLeafOrigin signature origin)
    (adequate : DPatAdequate fuel pattern) :
    Nonempty (DPatRunCompletion before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases leaf with
  | var name => exact ⟨dpatVar_complete fuel signature path name before target⟩
  | wild => exact ⟨dpatWild_complete fuel signature path before _⟩

noncomputable def dpatLeafOrigin_complete
    {signature : FrozenSig} {path : SyntaxPath} {pattern : DPat} {target : Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPat signature q S pattern target bindings q' S'}
    {origin : DDDPatOrigin signature raw ledger ledger'}
    (leaf : DDDPatLeafOrigin signature origin)
    (adequate : DPatAdequate fuel pattern) :
    DPatRunCompletion before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings :=
  Classical.choice
    (dpatLeafOrigin_complete_nonempty fuel before leaf adequate)

theorem dpatsLeafOrigin_complete_nonempty
    {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {origin : DDDPatsOrigin signature raw ledger ledger'}
    (leaf : DDDPatsLeafOrigin signature origin)
    (adequate : DPatListAdequate fuel patterns) :
    Nonempty (DPatsRunCompletion before
      (inferDPatsFuel fuel signature parent index patterns targets state)
      q' S' ledger' targets bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases leaf with
  | nil => exact ⟨dpatsNil_complete fuel signature parent index before⟩
  | cons head tail disjoint =>
      have childFuel := dpatList_cons (fuel := fuel) adequate
      let headRun := dpatLeafOrigin_complete (path := index :: parent) fuel
        before head childFuel.1
      let tailRun := Classical.choice
        (dpatsLeafOrigin_complete_nonempty (parent := parent)
          (index := index + 1) fuel headRun.completion tail childFuel.2)
      exact ⟨dpatsCons_complete fuel signature parent index _ _ before
        headRun tailRun disjoint⟩
termination_by fuel

noncomputable def dpatsLeafOrigin_complete
    {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {origin : DDDPatsOrigin signature raw ledger ledger'}
    (leaf : DDDPatsLeafOrigin signature origin)
    (adequate : DPatListAdequate fuel patterns) :
    DPatsRunCompletion before
      (inferDPatsFuel fuel signature parent index patterns targets state)
      q' S' ledger' targets bindings :=
  Classical.choice
    (dpatsLeafOrigin_complete_nonempty fuel before leaf adequate)

/-! ## Primitive matcher-pattern leaves and lists -/

theorem ppatLeafOrigin_complete_nonempty
    {signature : FrozenSig} {path : SyntaxPath} {pattern : PPat} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPat signature q S pattern target holes bindings q' S'}
    {origin : DDPPatOrigin signature raw ledger ledger'}
    (leaf : DDPPatLeafOrigin signature origin)
    (adequate : PPatAdequate fuel pattern) :
    Nonempty (PPatRunCompletion before
      (inferPPatFuel fuel signature path pattern target state)
      q' S' ledger' target holes bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases leaf with
  | hole => exact ⟨ppatHole_complete fuel signature path before target⟩
  | wild => exact ⟨ppatWild_complete fuel signature path before _⟩
  | pval name => exact ⟨ppatValue_complete fuel signature path name before target⟩

noncomputable def ppatLeafOrigin_complete
    {signature : FrozenSig} {path : SyntaxPath} {pattern : PPat} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPat signature q S pattern target holes bindings q' S'}
    {origin : DDPPatOrigin signature raw ledger ledger'}
    (leaf : DDPPatLeafOrigin signature origin)
    (adequate : PPatAdequate fuel pattern) :
    PPatRunCompletion before
      (inferPPatFuel fuel signature path pattern target state)
      q' S' ledger' target holes bindings :=
  Classical.choice
    (ppatLeafOrigin_complete_nonempty fuel before leaf adequate)

theorem ppatsLeafOrigin_complete_nonempty
    {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {origin : DDPPatsOrigin signature raw ledger ledger'}
    (leaf : DDPPatsLeafOrigin signature origin)
    (adequate : PPatListAdequate fuel patterns) :
    Nonempty (PPatsRunCompletion before
      (inferPPatsFuel fuel signature parent index patterns targets state)
      q' S' ledger' targets holes bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases leaf with
  | nil => exact ⟨ppatsNil_complete fuel signature parent index before⟩
  | cons head tail disjoint =>
      have childFuel := ppatList_cons (fuel := fuel) adequate
      let headRun := ppatLeafOrigin_complete (path := index :: parent) fuel
        before head childFuel.1
      let tailRun := Classical.choice
        (ppatsLeafOrigin_complete_nonempty (parent := parent)
          (index := index + 1) fuel headRun.completion tail childFuel.2)
      exact ⟨ppatsCons_complete fuel signature parent index _ _ before
        headRun tailRun disjoint⟩
termination_by fuel

noncomputable def ppatsLeafOrigin_complete
    {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {origin : DDPPatsOrigin signature raw ledger ledger'}
    (leaf : DDPPatsLeafOrigin signature origin)
    (adequate : PPatListAdequate fuel patterns) :
    PPatsRunCompletion before
      (inferPPatsFuel fuel signature parent index patterns targets state)
      q' S' ledger' targets holes bindings :=
  Classical.choice
    (ppatsLeafOrigin_complete_nonempty fuel before leaf adequate)

/-! ## Full primitive-pattern recursion

Unlike the leaf adapters above, these theorems recurse over the actual origin
trees.  Constructor instantiation and tuple-field allocation produce the same
raw target lists on the DD and executable sides; the surrounding state
correspondence records how their interpretations differ.
-/

mutual

theorem dpatOrigin_complete_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : DPat} {target : Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPat signature q S pattern target bindings q' S'}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (targetBounded : target.BoundedBy q)
    (adequate : DPatAdequate fuel pattern) :
    Nonempty (DPatRunCompletion before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | var =>
      exact ⟨dpatVar_complete fuel signature path _ before target⟩
  | wild =>
      exact ⟨dpatWild_complete fuel signature path before target⟩
  | @ctor q S name patterns expectedTarget scheme S₁ bindings q' S'
      ledger ledger₂ lookup aligned childrenRaw childrenOrigin =>
      have childAdequate := dpat_ctor (fuel := fuel) adequate
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      refine ⟨dpatCtor_complete fuel signature path name patterns lookup closed
        before target targetBounded aligned (children := ?_)⟩
      dsimp
      intro alignment
      have executableTargetsEq :
          (InferenceBase.instantiateCtorScheme state.supply scheme).value.1 =
            (InferenceBase.instantiateCtorScheme q scheme).value.1 := by
        rw [before.supply_eq]
      exact Classical.choice
        (dpatsOrigin_complete_nonempty (parent := path) (index := 0) closed
          fuel alignment.completion childrenOrigin executableTargetsEq instBounded.1
          childAdequate)
  | @tuple q S patterns expectedTarget S₁ bindings q' S' ledger ledger'
      aligned childrenRaw childrenOrigin =>
      have childAdequate := dpat_tuple (fuel := fuel) adequate
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      refine ⟨dpatTuple_complete fuel signature path patterns before
        target targetBounded aligned (children := ?_)⟩
      dsimp
      intro alignment
      have executableTargetsEq := (freshTargets_complete before
        (freshOrigin .dataPattern path "dp-tuple-field")
        patterns.length).targets_eq
      exact Classical.choice
        (dpatsOrigin_complete_nonempty (parent := path) (index := 0) closed
          fuel alignment.completion childrenOrigin executableTargetsEq targetsBounded
          childAdequate)
termination_by fuel

theorem dpatsOrigin_complete_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat}
    {patterns : List DPat} {targets executableTargets : List Ty}
    {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (targetsEq : executableTargets = targets)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q)
    (adequate : DPatListAdequate fuel patterns) :
    Nonempty (DPatsRunCompletion before
      (inferDPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' targets bindings) := by
  subst executableTargets
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | nil =>
      exact ⟨dpatsNil_complete fuel signature parent index before⟩
  | @cons q S pattern patterns target targets bindings restBindings q₁ S₁
      q' S' ledger ledger₁ ledger' headRaw tailRaw headOrigin tailOrigin
      disjoint =>
      have childAdequate := dpatList_cons (fuel := fuel) adequate
      have headBounded := targetsBounded target (by simp)
      let headRun := Classical.choice
        (dpatOrigin_complete_nonempty (path := index :: parent) closed fuel
          before headOrigin headBounded childAdequate.1)
      have tailBounded : ∀ item ∈ targets, item.BoundedBy q₁ := by
        intro item membership
        exact (targetsBounded item (by simp [membership])).mono
          headOrigin.erase.supplyExtends
      let tailRun := Classical.choice
        (dpatsOrigin_complete_nonempty (parent := parent) (index := index + 1)
          closed fuel headRun.completion tailOrigin rfl tailBounded
          childAdequate.2)
      exact ⟨dpatsCons_complete fuel signature parent index pattern patterns
        before headRun tailRun disjoint⟩
termination_by fuel

end

noncomputable def dpatOrigin_complete
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : DPat} {target : Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPat signature q S pattern target bindings q' S'}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (targetBounded : target.BoundedBy q)
    (adequate : DPatAdequate fuel pattern) :
    DPatRunCompletion before
      (inferDPatFuel fuel signature path pattern target state)
      q' S' ledger' target bindings :=
  Classical.choice
    (dpatOrigin_complete_nonempty closed fuel before origin targetBounded
      adequate)

noncomputable def dpatsOrigin_complete
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat}
    {patterns : List DPat} {targets executableTargets : List Ty}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (targetsEq : executableTargets = targets)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q)
    (adequate : DPatListAdequate fuel patterns) :
    DPatsRunCompletion before
      (inferDPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' targets bindings :=
  Classical.choice
    (dpatsOrigin_complete_nonempty closed fuel before origin targetsEq
      targetsBounded adequate)

mutual

theorem ppatOrigin_complete_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : PPat} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPat signature q S pattern target holes bindings q' S'}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (targetBounded : target.BoundedBy q)
    (adequate : PPatAdequate fuel pattern) :
    Nonempty (PPatRunCompletion before
      (inferPPatFuel fuel signature path pattern target state)
      q' S' ledger' target holes bindings) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | hole => exact ⟨ppatHole_complete fuel signature path before target⟩
  | wild => exact ⟨ppatWild_complete fuel signature path before target⟩
  | pval => exact ⟨ppatValue_complete fuel signature path _ before target⟩
  | @ctor q S name patterns expectedTarget entry S₁ holes bindings q' S'
      ledger ledger₂ lookup aligned childrenRaw childrenOrigin =>
      have childAdequate := ppat_ctor (fuel := fuel) adequate
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      refine ⟨ppatCtor_complete fuel signature path name patterns lookup closed
        before target targetBounded aligned (children := ?_)⟩
      dsimp
      intro alignment
      have executableTargetsEq :
          (InferenceBase.instantiateCtorScheme state.supply entry.scheme).value.1 =
            (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 := by
        rw [before.supply_eq]
      exact Classical.choice
        (ppatsOrigin_complete_nonempty (parent := path) (index := 0) closed
          fuel alignment.completion childrenOrigin executableTargetsEq instBounded.1
          childAdequate)
  | @tuple q S patterns expectedTarget S₁ holes bindings q' S' ledger ledger'
      aligned childrenRaw childrenOrigin =>
      have childAdequate := ppat_tuple (fuel := fuel) adequate
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      refine ⟨ppatTuple_complete fuel signature path patterns before
        target targetBounded aligned (children := ?_)⟩
      dsimp
      intro alignment
      have executableTargetsEq := (freshTargets_complete before
        (freshOrigin .primitivePattern path "pp-tuple-field")
        patterns.length).targets_eq
      exact Classical.choice
        (ppatsOrigin_complete_nonempty (parent := path) (index := 0) closed
          fuel alignment.completion childrenOrigin executableTargetsEq targetsBounded
          childAdequate)
termination_by fuel

theorem ppatsOrigin_complete_nonempty
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat}
    {patterns : List PPat} {targets executableTargets : List Ty}
    {holes : List Dual}
    {bindings : MonoCtx} {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (targetsEq : executableTargets = targets)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q)
    (adequate : PPatListAdequate fuel patterns) :
    Nonempty (PPatsRunCompletion before
      (inferPPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' targets holes bindings) := by
  subst executableTargets
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases origin with
  | nil => exact ⟨ppatsNil_complete fuel signature parent index before⟩
  | @cons q S pattern patterns target targets holes restHoles bindings
      restBindings q₁ S₁ q' S' ledger ledger₁ ledger' headRaw tailRaw
      headOrigin tailOrigin disjoint =>
      have childAdequate := ppatList_cons (fuel := fuel) adequate
      have headBounded := targetsBounded target (by simp)
      let headRun := Classical.choice
        (ppatOrigin_complete_nonempty (path := index :: parent) closed fuel
          before headOrigin headBounded childAdequate.1)
      have tailBounded : ∀ item ∈ targets, item.BoundedBy q₁ := by
        intro item membership
        exact (targetsBounded item (by simp [membership])).mono
          headOrigin.erase.supplyExtends
      let tailRun := Classical.choice
        (ppatsOrigin_complete_nonempty (parent := parent) (index := index + 1)
          closed fuel headRun.completion tailOrigin rfl tailBounded
          childAdequate.2)
      exact ⟨ppatsCons_complete fuel signature parent index pattern patterns
        before headRun tailRun disjoint⟩
termination_by fuel

end

noncomputable def ppatOrigin_complete
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {path : SyntaxPath} {pattern : PPat} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPat signature q S pattern target holes bindings q' S'}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (targetBounded : target.BoundedBy q)
    (adequate : PPatAdequate fuel pattern) :
    PPatRunCompletion before
      (inferPPatFuel fuel signature path pattern target state)
      q' S' ledger' target holes bindings :=
  Classical.choice
    (ppatOrigin_complete_nonempty closed fuel before origin targetBounded
      adequate)

noncomputable def ppatsOrigin_complete
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {parent : SyntaxPath} {index : Nat}
    {patterns : List PPat} {targets executableTargets : List Ty}
    {holes : List Dual} {bindings : MonoCtx}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (targetsEq : executableTargets = targets)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q)
    (adequate : PPatListAdequate fuel patterns) :
    PPatsRunCompletion before
      (inferPPatsFuel fuel signature parent index patterns executableTargets state)
      q' S' ledger' targets holes bindings :=
  Classical.choice
    (ppatsOrigin_complete_nonempty closed fuel before origin targetsEq
      targetsBounded adequate)

/-! ## Structural synthesis fragment

This certificate isolates the synthesis constructors whose recursive edges
remain entirely inside synthesis: leaves, lambdas, tuples, and expression
lists.  Application and matching enter the checking and user-pattern
families, so they are connected by the later global mutual recursion.
-/

mutual

inductive DDSynthStructuralOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expression : Expr} -> {target : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDSynth signature q S context expression target q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDSynthOrigin signature raw ledger ledger' -> Prop where
  | leaf (certificate : DDSynthLeafOrigin signature origin) :
      DDSynthStructuralOrigin signature origin
  | lam
      (body : DDSynthStructuralOrigin signature bodyOrigin) :
      DDSynthStructuralOrigin signature (DDSynthOrigin.lam bodyOrigin)
  | tuple
      (children : DDSynthsStructuralOrigin signature childrenOrigin) :
      DDSynthStructuralOrigin signature (DDSynthOrigin.tuple childrenOrigin)

inductive DDSynthsStructuralOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : Context} ->
    {expressions : List Expr} -> {targets : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    {raw : DDSynths signature q S context expressions targets q' S'} ->
    {ledger ledger' : CapabilityOriginLedger} ->
    DDSynthsOrigin signature raw ledger ledger' -> Prop where
  | nil : DDSynthsStructuralOrigin signature DDSynthsOrigin.nil
  | cons
      (head : DDSynthStructuralOrigin signature headOrigin)
      (tail : DDSynthsStructuralOrigin signature tailOrigin) :
      DDSynthsStructuralOrigin signature
        (DDSynthsOrigin.cons headOrigin tailOrigin)

end

mutual

theorem synthStructuralOrigin_complete_nonempty
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDSynth signature q S context expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (certificate : DDSynthStructuralOrigin signature origin)
    (adequate : ExprAdequate fuel expression) :
    Nonempty (SynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression state)
      q' S' ledger' target) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases certificate with
  | leaf leaf =>
      exact synthLeafOrigin_complete_nonempty (fuel + 1) before
        (ContextBisimulation.same before.prevailing context) leaf adequate
  | @lam _ _ binderName _ _ _ _ _ _ _ _ _ bodyCertificate =>
      have bodyAdequate := expr_lam (fuel := fuel) adequate
      let bodyBefore := before.afterVisitFreshTy .exprLam path
        (freshOrigin .expression path "lambda-domain")
      let bodyRun := Classical.choice
        (synthStructuralOrigin_complete_nonempty
          (selfEnv := selfEnv.erase binderName)
          (path := 0 :: path) fuel bodyBefore bodyCertificate bodyAdequate)
      exact ⟨inferExprFuel_lam_complete before bodyRun⟩
  | tuple children =>
      have childrenAdequate := expr_tuple (fuel := fuel) adequate
      let childrenBefore := before.afterVisit .exprTuple path
      let childrenRun := Classical.choice
        (synthsStructuralOrigin_complete_nonempty (parent := path) (index := 0)
          (selfEnv := selfEnv) fuel childrenBefore children childrenAdequate)
      exact ⟨inferExprFuel_tuple_complete before childrenRun⟩
termination_by fuel

theorem synthsStructuralOrigin_complete_nonempty
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    {raw : DDSynths signature q S context expressions targets q' S'}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (certificate : DDSynthsStructuralOrigin signature origin)
    (adequate : ExprListAdequate fuel expressions) :
    Nonempty (SynthsRunCompletion before
      (inferExprsFuel fuel signature context selfEnv parent index expressions
        state) q' S' ledger' targets) := by
  obtain ⟨fuel, rfl⟩ := positive_of_lt adequate
  cases certificate with
  | nil => exact ⟨inferExprsFuel_nil_complete before fuel⟩
  | cons head tail =>
      have childAdequate := exprList_cons (fuel := fuel) adequate
      let headRun := Classical.choice
        (synthStructuralOrigin_complete_nonempty (path := index :: parent)
          (selfEnv := selfEnv) fuel before head childAdequate.1)
      let tailRun := Classical.choice
        (synthsStructuralOrigin_complete_nonempty (parent := parent)
          (index := index + 1) (selfEnv := selfEnv) fuel
          headRun.completion.state tail
          childAdequate.2)
      exact ⟨inferExprsFuel_cons_complete before headRun tailRun⟩
termination_by fuel

end

end DemandTypingInferenceCompletenessMain
end TypePM
