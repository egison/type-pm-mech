import TypePM.DemandTypingInferenceCompletenessMatcherMain
import TypePM.DemandTypingInferenceCompletenessMatcherExprTraversal
import TypePM.DemandTypingInferenceCompletenessPatternMain
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
open DemandTypingInferenceCompletenessMatcherMain
open DemandTypingInferenceCompletenessPatternMain

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
abbrev SynthCompletenessAt (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {context : Context} {selfEnv : SelfEnv}
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

abbrev SynthCompletenessBelow (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound → SynthCompletenessAt signature fuel

abbrev SynthCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat}, SynthCompletenessAt signature fuel

/-- Full motive used across `let` and pattern binders.  The DD and executable
contexts need not be syntactically identical after generalization; their
normalized schemes are instead related by the current residual
substitutions. -/
abbrev PairedSynthCompletenessAt
    (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDSynth signature q S declarativeContext expression target q' S'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext
      executableContext →
    declarativeContext.BoundedBy q →
    DDSynthOrigin signature raw ledger ledger' →
    SynthBudgetAdequate fuel expression →
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target)

abbrev PairedSynthCompletenessBelow
    (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound → PairedSynthCompletenessAt signature fuel

abbrev PairedSynthCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat}, PairedSynthCompletenessAt signature fuel

/-! Terminal-audited motives used by the final global recursion.  These match
the already established pattern and matcher dispatch modules; the bounded
result refinement is retained only on synthesis, where checking alignment
needs the raw executable target's syntactic bound. -/

abbrev AuditedSynthCompletenessAt
    (terminal : Subst) (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'},
    (before : TraversalStateCorrespondence q S ledger state) →
    ContextBisimulation before.prevailing declarativeContext
      executableContext →
    declarativeContext.BoundedBy q →
    executableContext.BoundedBy q →
    DDSynthTerminalAudit terminal signature origin →
    SynthBudgetAdequate fuel expression →
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target)

abbrev AuditedSynthCompletenessBelow
    (terminal : Subst) (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound →
    AuditedSynthCompletenessAt terminal signature fuel

abbrev AuditedSynthCompletenessMotive
    (terminal : Subst) (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat}, AuditedSynthCompletenessAt terminal signature fuel

/-- Strict ceilings compose, which is the termination interface used when a
syntax family (patterns or matcher clauses) calls back into expression
synthesis below its caller's fuel. -/
theorem AuditedSynthCompletenessBelow.mono
    {terminal : Subst} {signature : FrozenSig} {smaller larger : Nat}
    (complete : AuditedSynthCompletenessBelow terminal signature larger)
    (boundLe : smaller ≤ larger) :
    AuditedSynthCompletenessBelow terminal signature smaller := by
  intro fuel below
  exact complete (Nat.lt_of_lt_of_le below boundLe)

/-- Proof-relevant synthesis data stored by an audited checking node.  This
package hides the constructor's dependent proof indices from later clients. -/
structure AuditedCheckComponents
    (terminal : Subst) (signature : FrozenSig)
    (q : InferenceBase.FreshSupply) (S : Subst) (context : Context)
    (expression : Expr) (expected : Ty) (q' : InferenceBase.FreshSupply)
    (S' : Subst) (ledger ledger' : CapabilityOriginLedger) : Type where
  rawTarget : Ty
  middle : Subst
  synthesized : DDSynth signature q S context expression rawTarget q' middle
  synthOrigin : DDSynthOrigin signature synthesized ledger ledger'
  aligned : DDAlignWithLedger ledger' middle rawTarget expected S'
  synthAudit : DDSynthTerminalAudit terminal signature synthOrigin

def AuditedCheckComponents.ofAudit
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {expected : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDCheckOrigin signature raw ledger ledger'}
    (audit : DDCheckTerminalAudit terminal signature origin) :
    AuditedCheckComponents terminal signature q S context expression expected
      q' S' ledger ledger' := by
  cases audit with
  | @mk _ _ _ _ _ _ _ synthesized _ _ synthOrigin _ _ aligned child =>
      exact ⟨_, _, synthesized, synthOrigin, aligned, child⟩

/-- At one fuel ceiling, audited paired synthesis closes every strictly
smaller checking call.  The expected type is transported across the synthesis
transition before reconstructing the executable coercion/alignment cut. -/
theorem auditedCheckCompletenessAt_of_synthBelow
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {fuel : Nat}
    (synthComplete : AuditedSynthCompletenessBelow terminal signature fuel) :
    MatcherCheckCompletenessAt terminal signature fuel := by
  intro declarativeContext executableContext selfEnv path expression
    declarativeExpected executableExpected q q' S S' ledger ledger' state raw
    origin before contexts expectedRelated contextBounded
    executableContextBounded expectedBounded executableExpectedBounded audit
    adequate
  cases fuel with
  | zero => simp [MatcherCheckBudgetAdequate] at adequate
  | succ fuel =>
      let components := AuditedCheckComponents.ofAudit audit
      have synthAdequate : SynthBudgetAdequate fuel expression := by
        simp only [MatcherCheckBudgetAdequate, SynthBudgetAdequate]
          at adequate ⊢
        omega
      let synth := Classical.choice
        (synthComplete (Nat.lt_succ_self fuel)
          (selfEnv := selfEnv) (path := path)
          (origin := components.synthOrigin) before contexts contextBounded
          executableContextBounded components.synthAudit synthAdequate)
      obtain ⟨_, declarativeRawBounded⟩ :=
        components.synthesized.boundedBy closed before.declarative_bounded
          contextBounded
      have expectedAtCut := expectedBounded.mono
        components.synthesized.supplyExtends
      have executableExpectedAtCut := executableExpectedBounded.mono
        components.synthesized.supplyExtends
      let alignedRun := ddAlignWithLedger_complete (path := path)
        synth.run.completion.state synth.run.target
        (synth.run.transition.transportTy expectedRelated)
        declarativeRawBounded expectedAtCut synth.rawTargetBounded
        executableExpectedAtCut components.aligned
      exact ⟨checkExprFuel_complete before synth.run alignedRun⟩

/-- Unrestricted wrapper used after the global audited synthesis recursion
has been closed. -/
theorem auditedCheckCompletenessMotive_of_synth
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    (synthComplete : AuditedSynthCompletenessMotive terminal signature) :
    MatcherCheckCompletenessMotive terminal signature := by
  intro fuel
  exact auditedCheckCompletenessAt_of_synthBelow closed
    (fun _ => synthComplete)

/-- The same raw bounded synthesis package is the subtype expected by the
user-pattern dispatcher. -/
theorem patternSynthCompletenessBelow_of_audited
    {terminal : Subst} {signature : FrozenSig} {bound : Nat}
    (complete : AuditedSynthCompletenessBelow terminal signature bound) :
    PatternSynthCompletenessBelow terminal signature bound := by
  intro fuel fuelLt declarativeContext executableContext selfEnv path
    expression target q q' S S' ledger ledger' state raw origin before
    contexts contextBounded executableContextBounded audit adequate
  let run := Classical.choice
    (complete fuelLt (selfEnv := selfEnv) (path := path) (origin := origin)
      before contexts contextBounded executableContextBounded audit adequate)
  exact ⟨⟨run.run, run.rawTargetBounded⟩⟩

/-- Audited synthesis below a ceiling also supplies all matcher checking
calls below that ceiling. -/
theorem matcherCheckCompletenessBelow_of_audited
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed) {bound : Nat}
    (complete : AuditedSynthCompletenessBelow terminal signature bound) :
    MatcherCheckCompletenessBelow terminal signature bound := by
  intro fuel fuelLt
  exact auditedCheckCompletenessAt_of_synthBelow closed
    (complete.mono (Nat.le_of_lt fuelLt))

/-- Traversal-stable checking counterpart of `SynthCompletenessMotive`. -/
abbrev CheckCompletenessAt (signature : FrozenSig) (fuel : Nat) : Prop :=
  ∀ {context : Context} {selfEnv : SelfEnv}
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

abbrev CheckCompletenessBelow (signature : FrozenSig) (bound : Nat) : Prop :=
  ∀ {fuel : Nat}, fuel < bound → CheckCompletenessAt signature fuel

abbrev CheckCompletenessMotive (signature : FrozenSig) : Prop :=
  ∀ {fuel : Nat}, CheckCompletenessAt signature fuel

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

/-- Fuel-bounded form used by the synthesis self-recursion.  Restricting the
dispatcher to smaller fuel exposes the termination argument which would be
hidden by an unrestricted higher-order motive. -/
theorem synthsOrigin_complete_nonempty_below
    {signature : FrozenSig} {fuel : Nat}
    (synthComplete : SynthCompletenessBelow signature fuel)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
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
          (synthComplete (Nat.lt_succ_self fuel)
            (selfEnv := selfEnv) (path := index :: parent)
            before contextBounded headOrigin headAdequate)
        have tailContextBounded : context.BoundedBy q₁ :=
          contextBounded.mono headOrigin.erase.supplyExtends
        have belowTail : SynthCompletenessBelow signature fuel := by
          intro childFuel childLt
          exact synthComplete (Nat.lt_trans childLt (Nat.lt_succ_self fuel))
        let tailRun := Classical.choice
          (synthsOrigin_complete_nonempty_below
            (selfEnv := selfEnv) (parent := parent) (index := index + 1)
            belowTail headRun.run.completion.state tailContextBounded
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

noncomputable def boundedSynthVar_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {scheme : Scheme}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    (lookup : (context.applySubst S).find? name = some scheme)
    (fuel : Nat) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature context selfEnv path (.var name) state)
      (InferenceBase.instantiateScheme q scheme).supply S
      (DDLedger.markSchemeInstance ledger q scheme)
      (InferenceBase.instantiateScheme q scheme).value := by
  let run := inferExprFuel_var_complete (signature := signature)
    (selfEnv := selfEnv) (path := path) before
    (ContextBisimulation.same before.prevailing context) lookup fuel
  refine ⟨run, ?_⟩
  let normalized := context.applySubst state.prevailing
  cases executableLookup : normalized.find? name with
  | none =>
      have impossible := congrArg (fun ctx : Context => ctx.find? name)
        (DemandTypingInferenceCompletenessContext.normalizedContext_forward
          before.prevailing context)
      simp [lookup, Context.find?_applySubst, normalized,
        executableLookup] at impossible
  | some executableScheme =>
      have normalizedBounded : normalized.BoundedBy q :=
        contextBounded.applySubst before.executable_bounded
      have schemeBounded := normalizedBounded.find? executableLookup
      have instantiatedBounded :=
        Scheme.freshInstantiate_value_boundedBy (supply := q) schemeBounded
      have schemeDirections :=
        (ContextBisimulation.same before.prevailing context).lookup
          lookup executableLookup
      have supplyEq :
          (InferenceBase.instantiateScheme q executableScheme).supply =
            (InferenceBase.instantiateScheme q scheme).supply := by
        rw [schemeDirections.1]
        cases executableScheme
        rfl
      have targetEq : run.result.target =
          (InferenceBase.instantiateScheme q executableScheme).value := by
        have success := run.success
        simp only [inferExprFuel] at success
        rw [show (Context.applySubst (visit state .exprVar path).prevailing
          context).find? name = some executableScheme by
            change normalized.find? name = some executableScheme
            exact executableLookup] at success
        cases selfLookup : selfEnv.find? name <;>
          simp [selfLookup, finishExpr, instantiateSchemeInState] at success
        all_goals
          have := congrArg ExprResult.target success
          simpa [visit, before.supply_eq] using this.symm
      rw [targetEq]
      rw [← supplyEq]
      exact instantiatedBounded

noncomputable def boundedSynthVarPaired_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {scheme : Scheme}
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (declarativeContextBounded : declarativeContext.BoundedBy q)
    (lookup : (declarativeContext.applySubst S).find? name = some scheme)
    (fuel : Nat) :
    BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.var name) state)
      (InferenceBase.instantiateScheme q scheme).supply S
      (DDLedger.markSchemeInstance ledger q scheme)
      (InferenceBase.instantiateScheme q scheme).value := by
  let run := inferExprFuel_var_complete (signature := signature)
    (selfEnv := selfEnv) (path := path) before contexts lookup fuel
  refine ⟨run, ?_⟩
  let normalized := executableContext.applySubst state.prevailing
  cases executableLookup : normalized.find? name with
  | none =>
      have impossible := congrArg (fun ctx : Context => ctx.find? name)
        contexts.forward
      simp [lookup, Context.find?_applySubst, normalized,
        executableLookup] at impossible
  | some executableScheme =>
      have normalizedBounded : normalized.BoundedBy q :=
        by
          change Context.BoundedBy q
            (Context.applySubst state.prevailing executableContext)
          rw [contexts.reverse]
          exact (declarativeContextBounded.applySubst
            before.declarative_bounded).applySubst before.reverse_bounded
      have schemeBounded := normalizedBounded.find? executableLookup
      have instantiatedBounded :=
        Scheme.freshInstantiate_value_boundedBy (supply := q) schemeBounded
      have schemeDirections := contexts.lookup lookup executableLookup
      have supplyEq :
          (InferenceBase.instantiateScheme q executableScheme).supply =
            (InferenceBase.instantiateScheme q scheme).supply := by
        rw [schemeDirections.1]
        cases executableScheme
        rfl
      have targetEq : run.result.target =
          (InferenceBase.instantiateScheme q executableScheme).value := by
        have success := run.success
        simp only [inferExprFuel] at success
        rw [show (Context.applySubst (visit state .exprVar path).prevailing
          executableContext).find? name = some executableScheme by
            change normalized.find? name = some executableScheme
            exact executableLookup] at success
        cases selfLookup : selfEnv.find? name <;>
          simp [selfLookup, finishExpr, instantiateSchemeInState] at success
        all_goals
          have := congrArg ExprResult.target success
          simpa [visit, before.supply_eq] using this.symm
      rw [targetEq, ← supplyEq]
      exact instantiatedBounded

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

/-- Fuel-bounded checking component used by the synthesis self-recursion. -/
theorem checkOrigin_complete_nonempty_below
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {fuel : Nat} (synthComplete : SynthCompletenessBelow signature fuel)
    {context : Context} {selfEnv : SelfEnv} {path : SyntaxPath}
    {expression : Expr} {expected : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
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
            (synthComplete (Nat.lt_succ_self fuel)
              (selfEnv := selfEnv) (path := path)
              before contextBounded synthOrigin synthAdequate)
          exact checkOrigin_complete_nonempty_of_synth
            (synthesized := synthOrigin.erase) closed fuel before
            contextBounded expectedBounded synth aligned

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

/-- Close the whole checking-list recursion directly from the synthesis
component.  This is the form consumed by constructor and primitive
synthesis; no checking premise remains at that boundary. -/
theorem checksOrigin_complete_nonempty_from_synth
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    (synthComplete : SynthCompletenessMotive signature)
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
        expecteds state) q' S' ledger') :=
  checksOrigin_complete_nonempty_from_check
    (checkCompletenessMotive_of_synth closed synthComplete)
    fuel before contextBounded expectedsBounded origin adequate

/-- Fuel-bounded checking-list form used at constructor and primitive
children.  Every checking head spends one administrative unit before using a
strictly smaller synthesis hypothesis. -/
theorem checksOrigin_complete_nonempty_below
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {fuel : Nat} (synthComplete : SynthCompletenessBelow signature fuel)
    {context : Context} {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {expecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (before : TraversalStateCorrespondence q S ledger state)
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
        have belowHead : SynthCompletenessBelow signature fuel := by
          intro childFuel childLt
          exact synthComplete (Nat.lt_trans childLt (Nat.lt_succ_self fuel))
        let headRun := Classical.choice
          (checkOrigin_complete_nonempty_below closed belowHead
            (selfEnv := selfEnv) (path := index :: parent)
            before contextBounded expectedBounded headOrigin headAdequate)
        have tailContextBounded : context.BoundedBy q₁ :=
          contextBounded.mono headOrigin.erase.supplyExtends
        have tailExpectedsBounded :
            ∀ item ∈ expecteds, item.BoundedBy q₁ := by
          intro item membership
          exact (expectedsBounded item (by simp [membership])).mono
            headOrigin.erase.supplyExtends
        let tailRun := Classical.choice
          (checksOrigin_complete_nonempty_below closed belowHead
            (selfEnv := selfEnv) (parent := parent) (index := index + 1)
            headRun.completion tailContextBounded tailExpectedsBounded
            tailOrigin tailAdequate)
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

/-! ## Bounded structural synthesis recursion

This is the first closed component of the weighted global motive.  Besides
successful traversal it proves the raw executable result boundedness needed
by every later checking cut. -/

mutual

theorem synthStructuralOrigin_bounded_complete_nonempty
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    {raw : DDSynth signature q S context expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (certificate : DDSynthStructuralOrigin signature origin)
    (adequate : SynthBudgetAdequate fuel expression) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel fuel signature context selfEnv path expression state)
      q' S' ledger' target) := by
  cases fuel with
  | zero => simp [SynthBudgetAdequate] at adequate
  | succ fuel =>
    cases certificate with
    | leaf leaf =>
        cases leaf with
        | var lookup =>
            exact ⟨boundedSynthVar_complete before contextBounded lookup fuel⟩
        | lit => exact ⟨boundedSynthLit_complete before fuel⟩
        | something => exact ⟨boundedSynthSomething_complete before fuel⟩
    | lam bodyCertificate =>
        rename_i binderName body bodyTarget bodyRaw bodyOrigin
        have bodyAdequate : SynthBudgetAdequate fuel body := by
          simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
          omega
        let bodyBefore := before.afterVisitFreshTy .exprLam path
          (freshOrigin .expression path "lambda-domain")
        have bodyContextBounded : Context.BoundedBy
            { q with nextTy := q.nextTy + 1 }
            ((binderName, Scheme.mono (.var q.nextTy)) :: context) :=
          Context.BoundedBy.cons
            (Scheme.BoundedBy.ofMono
              (Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)))
            (contextBounded.mono (SupplyExtends.bumpTy q 1))
        let bodyRun := Classical.choice
          (synthStructuralOrigin_bounded_complete_nonempty
            (selfEnv := selfEnv.erase binderName) (path := 0 :: path)
            fuel bodyBefore bodyContextBounded bodyCertificate bodyAdequate)
        exact ⟨boundedSynthLam_complete before bodyRun
          ((Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)).mono
            bodyOrigin.erase.supplyExtends)⟩
    | tuple children =>
        rename_i expressions targets childrenRaw childrenOrigin
        have childrenAdequate : SynthsBudgetAdequate fuel expressions := by
          simp only [SynthBudgetAdequate, SynthsBudgetAdequate,
            exprTraversalFuel] at adequate ⊢
          omega
        let childrenBefore := before.afterVisit .exprTuple path
        let childrenRun := Classical.choice
          (synthsStructuralOrigin_bounded_complete_nonempty
            (parent := path) (index := 0) (selfEnv := selfEnv)
            fuel childrenBefore contextBounded children childrenAdequate)
        exact ⟨boundedSynthTuple_complete before childrenRun⟩
termination_by fuel

theorem synthsStructuralOrigin_bounded_complete_nonempty
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contextBounded : context.BoundedBy q)
    {raw : DDSynths signature q S context expressions targets q' S'}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (certificate : DDSynthsStructuralOrigin signature origin)
    (adequate : SynthsBudgetAdequate fuel expressions) :
    Nonempty (BoundedSynthsRunCompletion before
      (inferExprsFuel fuel signature context selfEnv parent index expressions
        state) q' S' ledger' targets) := by
  cases fuel with
  | zero => simp [SynthsBudgetAdequate] at adequate
  | succ fuel =>
    cases certificate with
    | nil => exact ⟨boundedSynthsNil_complete fuel signature context selfEnv
        parent index before⟩
    | cons head tail =>
        rename_i expression target q₁ S₁ ledger₁ expressions targets
          headRaw tailRaw headOrigin tailOrigin
        have headAdequate : SynthBudgetAdequate fuel expression := by
          simp only [SynthsBudgetAdequate, SynthBudgetAdequate,
            exprListTraversalFuel] at adequate ⊢
          omega
        have tailAdequate : SynthsBudgetAdequate fuel expressions := by
          simp only [SynthsBudgetAdequate, exprListTraversalFuel]
            at adequate ⊢
          omega
        let headRun := Classical.choice
          (synthStructuralOrigin_bounded_complete_nonempty
            (path := index :: parent) (selfEnv := selfEnv) fuel before
            contextBounded head headAdequate)
        have tailContextBounded : context.BoundedBy _ :=
          contextBounded.mono headOrigin.erase.supplyExtends
        let tailRun := Classical.choice
          (synthsStructuralOrigin_bounded_complete_nonempty
            (parent := parent) (index := index + 1) (selfEnv := selfEnv)
            fuel headRun.run.completion.state tailContextBounded tail
            tailAdequate)
        exact ⟨boundedSynthsCons_complete before headRun tailRun
          tailOrigin.erase.supplyExtends⟩
termination_by fuel

end

/-! ## Audited global synthesis: pattern-independent constructors -/

/-- The three solver-free audited leaves already have the complete paired,
bounded reconstruction required by the global recursion. -/
theorem auditedSynthLeaf_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expression : Expr} {target : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (_executableContextBounded : executableContext.BoundedBy q)
    {raw : DDSynth signature q S declarativeContext expression target q' S'}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (audit : DDSynthTerminalAudit terminal signature origin)
    (leaf : DDSynthLeafOrigin signature origin)
    (adequate : SynthBudgetAdequate fuel expression) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel fuel signature executableContext selfEnv path expression
        state) q' S' ledger' target) := by
  cases fuel with
  | zero => simp [SynthBudgetAdequate] at adequate
  | succ inner =>
      cases leaf with
      | var lookup =>
          exact ⟨boundedSynthVarPaired_complete before contexts contextBounded
            lookup inner⟩
      | lit => exact ⟨boundedSynthLit_complete before inner⟩
      | something => exact ⟨boundedSynthSomething_complete before inner⟩

/-- Lambda is the first non-leaf global case.  Its only recursive premise is
strictly below the enclosing fuel; all context transport is local to the
fresh monomorphic binder. -/
theorem auditedSynthLam_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {body : Expr} {bodyTarget : Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger'}
    (bodyAudit : DDSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.lam name body)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.lam name body) state) q' S' ledger'
      (.fn (.var q.nextTy) bodyTarget)) := by
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let bodyBefore := before.afterVisitFreshTy .exprLam path
    (freshOrigin .expression path "lambda-domain")
  let domainRelated := bodyBefore.prevailing.sameTarget (.var q.nextTy)
  let bodyContexts :=
    (contexts.transport
      ((before.visitExtension .exprLam path).seq
        ((before.visit .exprLam path).freshTyExtension
          (freshOrigin .expression path "lambda-domain")))).consMono
      name domainRelated
  have bodyContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 1 }
      ((name, Scheme.mono (.var q.nextTy)) :: declarativeContext) :=
    Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono
        (Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)))
      (contextBounded.mono (SupplyExtends.bumpTy q 1))
  have bodyExecutableContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 1 }
      ((name, Scheme.mono (.var q.nextTy)) :: executableContext) := by
    exact Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono
        (Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)))
      (executableContextBounded.mono (SupplyExtends.bumpTy q 1))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv.erase name) (path := 0 :: path)
      bodyBefore bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  exact ⟨boundedSynthLam_complete before bodyRun
    ((Ty.BoundedBy.varOf (Nat.lt_succ_self q.nextTy)).mono
      bodyOrigin.erase.supplyExtends)⟩

/-- Audited expression lists are reconstructed left-to-right.  The head run
provides the concrete executable state and prevailing substitution used by
the tail, while the terminal audit splits along the same origin tree. -/
theorem auditedSynths_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {raw : DDSynths signature q S declarativeContext expressions targets q' S'}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (audit : DDSynthsTerminalAudit terminal signature origin)
    (adequate : SynthsBudgetAdequate fuel expressions) :
    Nonempty (BoundedSynthsRunCompletion before
      (inferExprsFuel fuel signature executableContext selfEnv parent index
        expressions state) q' S' ledger' targets) := by
  cases fuel with
  | zero => simp [SynthsBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil => exact ⟨boundedSynthsNil_complete inner signature
          executableContext selfEnv parent index before⟩
      | cons headAudit tailAudit =>
          rename_i expression target q₁ S₁ ledger₁ expressions targets
            headRaw tailRaw headOrigin tailOrigin
          have headAdequate : SynthBudgetAdequate inner expression := by
            simp only [SynthsBudgetAdequate, SynthBudgetAdequate,
              exprListTraversalFuel] at adequate ⊢
            omega
          have tailAdequate : SynthsBudgetAdequate inner expressions := by
            simp only [SynthsBudgetAdequate, exprListTraversalFuel]
              at adequate ⊢
            omega
          let headRun := Classical.choice
            (synthBelow (Nat.lt_succ_self inner)
              (selfEnv := selfEnv) (path := index :: parent)
              before contexts contextBounded executableContextBounded headAudit
              headAdequate)
          have tailContexts : ContextBisimulation
              headRun.run.completion.state.prevailing declarativeContext
              executableContext :=
            contexts.transport headRun.run.transition
          have tailContextBounded : declarativeContext.BoundedBy q₁ :=
            contextBounded.mono headOrigin.erase.supplyExtends
          have tailExecutableContextBounded : executableContext.BoundedBy q₁ :=
            executableContextBounded.mono headOrigin.erase.supplyExtends
          have belowTail : AuditedSynthCompletenessBelow terminal signature
              inner := synthBelow.mono (Nat.le_succ inner)
          let tailRun := Classical.choice
            (auditedSynths_complete_nonempty
              (selfEnv := selfEnv) (parent := parent) (index := index + 1)
              inner belowTail headRun.run.completion.state tailContexts
              tailContextBounded tailExecutableContextBounded tailAudit tailAdequate)
          exact ⟨boundedSynthsCons_complete before headRun tailRun
            tailOrigin.erase.supplyExtends⟩
termination_by fuel

/-- Tuple synthesis delegates to the audited left-to-right expression-list
dispatcher after the tuple visit event. -/
theorem auditedSynthTuple_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {expressions : List Expr} {targets : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {childrenRaw : DDSynths signature q S declarativeContext expressions
      targets q' S'}
    {childrenOrigin : DDSynthsOrigin signature childrenRaw ledger ledger'}
    (childrenAudit : DDSynthsTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.tuple expressions)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.tuple expressions) state) q' S' ledger' (.prod targets)) := by
  have childrenAdequate : SynthsBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, SynthsBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let childrenBefore := before.afterVisit .exprTuple path
  have childrenContexts : ContextBisimulation
      childrenBefore.prevailing declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprTuple path)
  have childrenBelow : AuditedSynthCompletenessBelow terminal signature fuel :=
    synthBelow.mono (Nat.le_succ fuel)
  let childrenRun := Classical.choice
    (auditedSynths_complete_nonempty
      (selfEnv := selfEnv) (parent := path) (index := 0)
      fuel childrenBelow childrenBefore childrenContexts contextBounded
      executableContextBounded childrenAudit childrenAdequate)
  exact ⟨boundedSynthTuple_complete before childrenRun⟩

/-- Context-bisimulation-aware checking-list reconstruction used by
constructor and primitive application.  This is the global counterpart of
the matcher-local list dispatcher: executable contexts need not be
syntactically identical to their DD contexts after let generalization. -/
theorem auditedChecks_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat}
    {expressions : List Expr}
    {declarativeExpecteds executableExpecteds : List Ty}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature fuel)
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (expectedsBounded : ∀ expected ∈ declarativeExpecteds,
      expected.BoundedBy q)
    (executableExpectedsBounded : ∀ expected ∈ executableExpecteds,
      expected.BoundedBy q)
    (expectedsRelated : TyListBisimulation before.prevailing
      declarativeExpecteds executableExpecteds)
    {raw : DDChecks signature q S declarativeContext expressions
      declarativeExpecteds q' S'}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (adequate : MatcherChecksBudgetAdequate fuel expressions) :
    Nonempty (StateRunCompletion before
      (checkExprsFuel fuel signature executableContext selfEnv parent index
        expressions executableExpecteds state) q' S' ledger') := by
  cases fuel with
  | zero => simp [MatcherChecksBudgetAdequate] at adequate
  | succ inner =>
      cases audit with
      | nil =>
          cases expectedsRelated
          exact ⟨checkExprsFuel_nil_complete inner signature
            executableContext selfEnv parent index before⟩
      | cons headAudit tailAudit =>
          rename_i expression expected q₁ S₁ ledger₁ expressions expecteds
            headRaw tailRaw headOrigin tailOrigin
          cases executableExpecteds with
          | nil => cases expectedsRelated
          | cons executableExpected executableExpecteds =>
              cases expectedsRelated with
              | cons expectedRelated tailRelated =>
                have headAdequate : MatcherCheckBudgetAdequate inner
                    expression := by
                  simp only [MatcherChecksBudgetAdequate,
                    MatcherCheckBudgetAdequate, exprListTraversalFuel]
                    at adequate ⊢
                  omega
                have tailAdequate : MatcherChecksBudgetAdequate inner
                    expressions := by
                  simp only [MatcherChecksBudgetAdequate,
                    exprListTraversalFuel] at adequate ⊢
                  omega
                have childBelow : AuditedSynthCompletenessBelow terminal
                    signature inner := synthBelow.mono (Nat.le_succ inner)
                let headRun := Classical.choice
                  (auditedCheckCompletenessAt_of_synthBelow closed childBelow
                    (selfEnv := selfEnv) (path := index :: parent)
                    before contexts expectedRelated contextBounded
                    executableContextBounded
                    (expectedsBounded expected (by simp))
                    (executableExpectedsBounded executableExpected (by simp))
                    headAudit headAdequate)
                have tailContexts : ContextBisimulation
                    headRun.completion.prevailing declarativeContext
                    executableContext :=
                  contexts.transport headRun.transition
                have tailContextBounded : declarativeContext.BoundedBy q₁ :=
                  contextBounded.mono headOrigin.erase.supplyExtends
                have tailExpectedsBounded : ∀ item ∈ expecteds,
                    item.BoundedBy q₁ := by
                  intro item membership
                  exact (expectedsBounded item (by simp [membership])).mono
                    headOrigin.erase.supplyExtends
                have tailExecutableExpectedsBounded :
                    ∀ item ∈ executableExpecteds, item.BoundedBy q₁ := by
                  intro item membership
                  exact (executableExpectedsBounded item
                    (by simp [membership])).mono
                    headOrigin.erase.supplyExtends
                let tailRun := Classical.choice
                  (auditedChecks_complete_nonempty closed inner childBelow
                    (selfEnv := selfEnv) (parent := parent)
                    (index := index + 1) headRun.completion tailContexts
                    tailContextBounded
                    (executableContextBounded.mono
                      headOrigin.erase.supplyExtends)
                    tailExpectedsBounded
                    tailExecutableExpectedsBounded
                    (headRun.transition.transportTyList tailRelated)
                    tailAudit tailAdequate)
                exact ⟨checkExprsFuel_cons_complete before headRun tailRun⟩
termination_by fuel

/-- Constructor synthesis instantiates the frozen signature entry once, then
checks all arguments against that single instance before freezing its export
capabilities. -/
theorem auditedSynthCtor_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (lookup : signature.findDataCtor name = some scheme)
    {childrenRaw : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      declarativeContext expressions
      (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    {childrenOrigin : DDChecksOrigin signature childrenRaw
      (DDLedger.markCtorInstance ledger q scheme) ledger₁}
    (childrenAudit : DDChecksTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.ctor name expressions)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.ctor name expressions) state) q' S'
      (DDLedger.freezeExport ledger₁ S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  have childrenAdequate : MatcherChecksBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, MatcherChecksBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let instantiated := instantiateCtorInState_complete
    (before.visit .exprCtor path) scheme
  have instanceBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.dataCtors lookup).boundedBy)
  have instanceExtension := SupplyExtends.instantiateCtorScheme q scheme
  have childrenContextBounded : declarativeContext.BoundedBy
      (InferenceBase.instantiateCtorScheme q scheme).supply :=
    contextBounded.mono instanceExtension
  have childrenContexts : ContextBisimulation
      instantiated.correspondence.prevailing declarativeContext
      executableContext :=
    (contexts.transport (before.visitExtension .exprCtor path)).transport
      instantiated.transition
  have childBelow : AuditedSynthCompletenessBelow terminal signature fuel :=
    synthBelow.mono (Nat.le_succ fuel)
  have executableArgumentsBounded : ∀ expected ∈
      (instantiateCtorInState (visit state .exprCtor path) scheme).1.1,
      expected.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply := by
    intro expected membership
    apply instanceBounded.1 expected
    simpa [Inference.instantiateCtorInState, visit, before.supply_eq] using
      membership
  let childrenRun := Classical.choice
    (auditedChecks_complete_nonempty closed fuel childBelow
      (selfEnv := selfEnv) (parent := path) (index := 0)
      instantiated.correspondence childrenContexts childrenContextBounded
      (executableContextBounded.mono instanceExtension)
      instanceBounded.1 executableArgumentsBounded
      instantiated.arguments childrenAudit childrenAdequate)
  exact ⟨boundedSynthCtor_complete closed before lookup childrenRun
    childrenOrigin.erase.supplyExtends⟩

/-- Primitive application has the same audited reconstruction shape as data
constructor application, differing only in the frozen-signature lookup and
trace event. -/
theorem auditedSynthPrim_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (lookup : signature.findPrimitive op = some scheme)
    {childrenRaw : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S
      declarativeContext expressions
      (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    {childrenOrigin : DDChecksOrigin signature childrenRaw
      (DDLedger.markCtorInstance ledger q scheme) ledger₁}
    (childrenAudit : DDChecksTerminalAudit terminal signature childrenOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.prim op expressions)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.prim op expressions) state) q' S'
      (DDLedger.freezeExport ledger₁ S'
        (freshCapImages q scheme.capBinders)
        (InferenceBase.instantiateCtorScheme q scheme).value.2)
      (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
  have childrenAdequate : MatcherChecksBudgetAdequate fuel expressions := by
    simp only [SynthBudgetAdequate, MatcherChecksBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let instantiated := instantiateCtorInState_complete
    (before.visit .exprPrim path) scheme
  have instanceBounded := instantiateCtorScheme_boundedBy (q := q)
    ((closed.primitives lookup).boundedBy)
  have instanceExtension := SupplyExtends.instantiateCtorScheme q scheme
  have childrenContextBounded : declarativeContext.BoundedBy
      (InferenceBase.instantiateCtorScheme q scheme).supply :=
    contextBounded.mono instanceExtension
  have childrenContexts : ContextBisimulation
      instantiated.correspondence.prevailing declarativeContext
      executableContext :=
    (contexts.transport (before.visitExtension .exprPrim path)).transport
      instantiated.transition
  have childBelow : AuditedSynthCompletenessBelow terminal signature fuel :=
    synthBelow.mono (Nat.le_succ fuel)
  have executableArgumentsBounded : ∀ expected ∈
      (instantiateCtorInState (visit state .exprPrim path) scheme).1.1,
      expected.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply := by
    intro expected membership
    apply instanceBounded.1 expected
    simpa [Inference.instantiateCtorInState, visit, before.supply_eq] using
      membership
  let childrenRun := Classical.choice
    (auditedChecks_complete_nonempty closed fuel childBelow
      (selfEnv := selfEnv) (parent := path) (index := 0)
      instantiated.correspondence childrenContexts childrenContextBounded
      (executableContextBounded.mono instanceExtension)
      instanceBounded.1 executableArgumentsBounded
      instantiated.arguments childrenAudit childrenAdequate)
  exact ⟨boundedSynthPrim_complete closed before lookup childrenRun
    childrenOrigin.erase.supplyExtends⟩

/-- Application reconstructs the function, the two fresh arrow endpoints,
ordinary function alignment, and finally the audited argument check in the
same chronological order as the executable. -/
theorem auditedSynthApp_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {function argument : Expr} {functionTarget : Ty}
    {q q₁ q₂ : InferenceBase.FreshSupply} {S S₁ S₂ S₃ : Subst}
    {ledger ledger₁ ledger₃ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {functionRaw : DDSynth signature q S declarativeContext function
      functionTarget q₁ S₁}
    {functionOrigin : DDSynthOrigin signature functionRaw ledger ledger₁}
    (aligned : DDAlignTypesWithLedger ledger₁ S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂)
    {argumentRaw : DDCheck signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ declarativeContext argument
      (.var q₁.nextTy) q₂ S₃}
    {argumentOrigin : DDCheckOrigin signature argumentRaw ledger₁ ledger₃}
    (functionAudit : DDSynthTerminalAudit terminal signature functionOrigin)
    (argumentAudit : DDCheckTerminalAudit terminal signature argumentOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.app function argument)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.app function argument) state) q₂ S₃ ledger₃
      (.var (q₁.nextTy + 1))) := by
  have functionAdequate : SynthBudgetAdequate fuel function := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  have argumentCheckAdequate : MatcherCheckBudgetAdequate fuel argument := by
    simp only [SynthBudgetAdequate, MatcherCheckBudgetAdequate,
      exprTraversalFuel] at adequate ⊢
    omega
  let functionBefore := before.afterVisit .exprApp path
  have functionContexts : ContextBisimulation functionBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprApp path)
  let functionRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 0 :: path)
      functionBefore functionContexts contextBounded executableContextBounded
      functionAudit
      functionAdequate)
  let domainOrigin := freshOrigin .expression path "application-domain"
  let resultOrigin := freshOrigin .expression path "application-result"
  let functionAlignOrigin := freshOrigin .expression path
    "application-function"
  let domainAllocation := functionRun.run.completion.state.freshTy domainOrigin
  let resultAllocation := domainAllocation.state.freshTy resultOrigin
  have arrowBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 }
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) :=
    Ty.BoundedBy.fnOf
      (Ty.BoundedBy.varOf (by simp))
      (Ty.BoundedBy.varOf (by simp))
  have functionDeclarativeBounded : functionTarget.BoundedBy q₁ :=
    (functionRaw.boundedBy closed before.declarative_bounded
      contextBounded).2
  have executableArrowEq :
      (Ty.fn (functionRun.run.result.state.freshTy domainOrigin).1
        ((functionRun.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) =
      (Ty.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) := by
    rw [domainAllocation.target_eq, resultAllocation.target_eq]
  have functionRelatedAtAllocation : TyBisimulation
      resultAllocation.state.prevailing functionTarget
      functionRun.run.result.target :=
    (domainAllocation.state.freshTyExtension resultOrigin).transportTy
      ((functionRun.run.completion.state.freshTyExtension
        domainOrigin).transportTy functionRun.run.target)
  have arrowRelatedAtAllocation : TyBisimulation
      resultAllocation.state.prevailing
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1)))
      (.fn (functionRun.run.result.state.freshTy domainOrigin).1
        ((functionRun.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) := by
    rw [executableArrowEq]
    exact resultAllocation.state.prevailing.sameTarget _
  have executableArrowBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 }
      (.fn (functionRun.run.result.state.freshTy domainOrigin).1
        ((functionRun.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1) := by
    rw [executableArrowEq]
    exact arrowBounded
  let functionAlignment :=
    DemandTypingInferenceCompletenessAlignmentTraversal.ddAlignTypesWithLedger_complete
    (origin := functionAlignOrigin) resultAllocation.state
    functionRelatedAtAllocation arrowRelatedAtAllocation
    (functionDeclarativeBounded.mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
    arrowBounded
    (functionRun.rawTargetBounded.mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
    executableArrowBounded aligned
  let components := AuditedCheckComponents.ofAudit argumentAudit
  have argumentContextBounded : declarativeContext.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } :=
    (contextBounded.mono functionOrigin.erase.supplyExtends).mono
      ((SupplyExtends.bumpTy q₁ 1).trans
        (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1))
  have argumentExecutableContextBounded : executableContext.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } :=
    executableContextBounded.mono
      (functionOrigin.erase.supplyExtends.trans
        ((SupplyExtends.bumpTy q₁ 1).trans
          (SupplyExtends.bumpTy { q₁ with nextTy := q₁.nextTy + 1 } 1)))
  have argumentContexts : ContextBisimulation
      functionAlignment.completion.prevailing declarativeContext
      executableContext :=
    (((functionContexts.transport functionRun.run.transition).transport
      (functionRun.run.completion.state.freshTyExtension domainOrigin)).transport
      (domainAllocation.state.freshTyExtension resultOrigin)).transport
      functionAlignment.transition
  have argumentSynthAdequate : SynthBudgetAdequate fuel argument := by
    simp only [SynthBudgetAdequate, MatcherCheckBudgetAdequate]
      at argumentCheckAdequate ⊢
    omega
  let argumentRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 1 :: path)
      functionAlignment.completion argumentContexts argumentContextBounded
      argumentExecutableContextBounded components.synthAudit
      argumentSynthAdequate)
  have expectedBounded : Ty.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } (.var q₁.nextTy) :=
    Ty.BoundedBy.varOf (by simp)
  let executableDomain := (functionRun.run.result.state.freshTy domainOrigin).1
  have expectedRelated : TyBisimulation
      functionAlignment.completion.prevailing (.var q₁.nextTy)
      executableDomain := by
    have atAllocation : TyBisimulation resultAllocation.state.prevailing
        (.var q₁.nextTy) executableDomain := by
      change TyBisimulation resultAllocation.state.prevailing
        (.var q₁.nextTy)
        (functionRun.run.result.state.freshTy domainOrigin).1
      rw [domainAllocation.target_eq]
      exact resultAllocation.state.prevailing.sameTarget _
    exact functionAlignment.transition.transportTy atAllocation
  have executableExpectedBounded : executableDomain.BoundedBy
      { q₁ with nextTy := q₁.nextTy + 2 } := by
    simpa [executableDomain, domainAllocation.target_eq] using expectedBounded
  have declarativeArgumentRawBounded :=
    (components.synthesized.boundedBy closed
      functionAlignment.completion.declarative_bounded
      argumentContextBounded).2
  let expectedAlignment := ddAlignWithLedger_complete (path := 1 :: path)
    argumentRun.run.completion.state argumentRun.run.target
    (argumentRun.run.transition.transportTy expectedRelated)
    declarativeArgumentRawBounded
    (expectedBounded.mono components.synthesized.supplyExtends)
    argumentRun.rawTargetBounded
    (executableExpectedBounded.mono components.synthesized.supplyExtends)
    components.aligned
  exact ⟨boundedSynthApp_complete before functionRun functionAlignment
    argumentRun expectedAlignment
    (by
      change Ty.BoundedBy q₂
        ((functionRun.run.result.state.freshTy domainOrigin).2.freshTy
          resultOrigin).1
      rw [resultAllocation.target_eq]
      exact Ty.BoundedBy.varOf (by
        have extension := components.synthesized.supplyExtends
        have belowStart : q₁.nextTy + 1 <
            ({ q₁ with nextTy := q₁.nextTy + 2 } :
              InferenceBase.FreshSupply).nextTy := by simp
        exact Nat.lt_of_lt_of_le belowStart extension.2))⟩

/-- Let synthesis reconstructs both recursive children around the single
generalization event.  The declarative and executable schemes are related by
context/type bisimulation, rather than assumed syntactically equal. -/
theorem auditedSynthLet_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {value body : Expr}
    {valueTarget bodyTarget : Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    {valueRaw : DDSynth signature q S declarativeContext value valueTarget
      q₁ S₁}
    {valueOrigin : DDSynthOrigin signature valueRaw ledger ledger₁}
    {bodyRaw : DDSynth signature q₁ S₁
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext)
      body bodyTarget q' S'}
    {bodyOrigin : DDSynthOrigin signature bodyRaw ledger₁ ledger'}
    (valueAudit : DDSynthTerminalAudit terminal signature valueOrigin)
    (bodyAudit : DDSynthTerminalAudit terminal signature bodyOrigin)
    (_facts : DDTerminalAudit.LetFacts terminal signature declarativeContext
      valueTarget S₁)
    (adequate : SynthBudgetAdequate (fuel + 1) (.letE name value body)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.letE name value body) state) q' S' ledger' bodyTarget) := by
  have valueAdequate : SynthBudgetAdequate fuel value := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let valueBefore := before.afterVisit .exprLet path
  have valueContexts : ContextBisimulation valueBefore.prevailing
      declarativeContext executableContext :=
    contexts.transport (before.visitExtension .exprLet path)
  let valueRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv) (path := 0 :: path)
      valueBefore valueContexts contextBounded executableContextBounded
      valueAudit valueAdequate)
  let executableScheme := signature.generalize
    (executableContext.applySubst valueRun.run.result.state.prevailing)
    (valueRun.run.result.state.prevailing.apply valueRun.run.result.target)
  let event := TraceEvent.letGeneralization
    valueRun.run.result.state.trace.solves.length name executableContext
    valueRun.run.result.target
    (executableContext.applySubst valueRun.run.result.state.prevailing)
    (valueRun.run.result.state.prevailing.apply valueRun.run.result.target)
    executableScheme
  let eventExtension :=
    valueRun.run.completion.state.prevailing.recordEventExtension event
  let bodyBefore := valueRun.run.completion.state.recordEvent event
    (by simp [event, TraceEvent.allocatedCapVars])
  have contextsAfterValue : ContextBisimulation
      valueRun.run.completion.state.prevailing declarativeContext
      executableContext :=
    valueContexts.transport valueRun.run.transition
  have generalizedContexts := contextsAfterValue.consGeneralized_complete
    signature closed name valueRun.run.target
  have bodyContexts : ContextBisimulation bodyBefore.prevailing
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext)
      ((name, executableScheme) :: executableContext) := by
    exact generalizedContexts.transport eventExtension
  have valueTargetBounded : valueTarget.BoundedBy q₁ :=
    (valueRaw.boundedBy closed before.declarative_bounded contextBounded).2
  have bodyContextBounded : Context.BoundedBy q₁
      ((name, signature.generalize (declarativeContext.applySubst S₁)
        (S₁.apply valueTarget)) :: declarativeContext) :=
    Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy
        (valueRun.run.completion.state.declarative_bounded.apply
          valueTargetBounded))
      (contextBounded.mono valueOrigin.erase.supplyExtends)
  have bodyExecutableContextBounded : Context.BoundedBy q₁
      ((name, executableScheme) :: executableContext) :=
    Context.BoundedBy.cons
      (FrozenSig.generalize_boundedBy
        (valueRun.run.completion.state.executable_bounded.apply
          valueRun.rawTargetBounded))
      (executableContextBounded.mono valueOrigin.erase.supplyExtends)
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := selfEnv.erase name) (path := 1 :: path)
      bodyBefore bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  exact ⟨boundedSynthLet_complete closed before valueRun bodyRun⟩

/-- Ordinary recursive functions use the canonical two-target placeholder;
the matcher-bodied specialization is handled separately because its
placeholder additionally freshens matcher skeleton capabilities. -/
theorem auditedSynthFix_complete_nonempty
    {terminal : Subst} {signature : FrozenSig}
    (closed : signature.SchemesClosed)
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {self argument : String} {body : Expr}
    {bodyTarget : Ty} {q q₁ : InferenceBase.FreshSupply}
    {S S₁ S' : Subst} {ledger ledger₁ : CapabilityOriginLedger}
    {state : InferState}
    (fuel : Nat)
    (synthBelow : AuditedSynthCompletenessBelow terminal signature (fuel + 1))
    (before : TraversalStateCorrespondence q S ledger state)
    (contexts : ContextBisimulation before.prevailing declarativeContext
      executableContext)
    (contextBounded : declarativeContext.BoundedBy q)
    (executableContextBounded : executableContext.BoundedBy q)
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext)
      body bodyTarget q₁ S₁}
    {bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger₁}
    (aligned : DDAlignTypesWithLedger ledger₁ S₁ bodyTarget
      (.var (q.nextTy + 1)) S')
    (bodyAudit : DDSynthTerminalAudit terminal signature bodyOrigin)
    (adequate : SynthBudgetAdequate (fuel + 1) (.fix self argument body)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.fix self argument body) state)
      q₁ S' ledger₁ (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) := by
  have bodyAdequate : SynthBudgetAdequate fuel body := by
    simp only [SynthBudgetAdequate, exprTraversalFuel] at adequate ⊢
    omega
  let visited := before.afterVisit .exprFix path
  let domainOrigin := freshOrigin .recursiveBinder path "fix-domain"
  let codomainOrigin := freshOrigin .recursiveBinder path "fix-codomain"
  let resultOrigin := freshOrigin .recursiveBinder path "fix-result"
  let domainAllocation := visited.freshTy domainOrigin
  let codomainAllocation := domainAllocation.state.freshTy codomainOrigin
  let executablePlaceholder := Ty.fn (fixDomain state path)
    (fixCodomain state path)
  let placeholderEvent := TraceEvent.fixPlaceholder self argument
    executablePlaceholder path
  let directEvent := TraceEvent.directSelfAccepted self executablePlaceholder path
  let placeholderExtension :=
    codomainAllocation.state.prevailing.recordEventExtension placeholderEvent
  let directExtension := placeholderExtension.after.recordEventExtension directEvent
  let bodyBefore :=
    (codomainAllocation.state.recordEvent placeholderEvent
      (by simp [placeholderEvent, TraceEvent.allocatedCapVars])).recordEvent
      directEvent (by simp [directEvent, TraceEvent.allocatedCapVars])
  have domainRelated : TyBisimulation bodyBefore.prevailing
      (.var q.nextTy) (fixDomain state path) := by
    have atAllocation : TyBisimulation codomainAllocation.state.prevailing
        (.var q.nextTy) (fixDomain state path) := by
      change TyBisimulation codomainAllocation.state.prevailing
        (.var q.nextTy) (visit state .exprFix path |>.freshTy domainOrigin).1
      rw [domainAllocation.target_eq]
      exact codomainAllocation.state.prevailing.sameTarget _
    exact directExtension.transportTy
      (placeholderExtension.transportTy atAllocation)
  have placeholderRelated : TyBisimulation bodyBefore.prevailing
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) executablePlaceholder := by
    have atAllocation : TyBisimulation codomainAllocation.state.prevailing
        (.fn (.var q.nextTy) (.var (q.nextTy + 1))) executablePlaceholder := by
      change TyBisimulation codomainAllocation.state.prevailing
        (.fn (.var q.nextTy) (.var (q.nextTy + 1)))
        (.fn (visit state .exprFix path |>.freshTy domainOrigin).1
          ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
            codomainOrigin).1)
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact codomainAllocation.state.prevailing.sameTarget _
    exact directExtension.transportTy
      (placeholderExtension.transportTy atAllocation)
  have bodyContexts : ContextBisimulation bodyBefore.prevailing
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext)
      ((argument, Scheme.mono (fixDomain state path)) ::
        (self, Scheme.mono executablePlaceholder) :: executableContext) := by
    let base := (((contexts.transport (before.visitExtension .exprFix path)).transport
      (visited.freshTyExtension domainOrigin)).transport
      (domainAllocation.state.freshTyExtension codomainOrigin)).transport
      placeholderExtension |>.transport directExtension
    exact (base.consMono self placeholderRelated).consMono argument domainRelated
  have bodyContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 2 }
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        declarativeContext) :=
    Context.BoundedBy.cons
      (Scheme.BoundedBy.ofMono (Ty.BoundedBy.varOf (by simp)))
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf
          (Ty.BoundedBy.varOf (by simp))
          (Ty.BoundedBy.varOf (by simp))))
        (contextBounded.mono (SupplyExtends.bumpTy q 2)))
  have bodyExecutableContextBounded : Context.BoundedBy
      { q with nextTy := q.nextTy + 2 }
      ((argument, Scheme.mono (fixDomain state path)) ::
        (self, Scheme.mono executablePlaceholder) :: executableContext) := by
    have domainBounded : (fixDomain state path).BoundedBy
        { q with nextTy := q.nextTy + 2 } := by
      change ((visit state .exprFix path |>.freshTy domainOrigin).1).BoundedBy _
      rw [domainAllocation.target_eq]
      exact Ty.BoundedBy.varOf (by simp)
    have placeholderBounded : executablePlaceholder.BoundedBy
        { q with nextTy := q.nextTy + 2 } := by
      change (Ty.fn (visit state .exprFix path |>.freshTy domainOrigin).1
        ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
          codomainOrigin).1).BoundedBy _
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact Ty.BoundedBy.fnOf (Ty.BoundedBy.varOf (by simp))
        (Ty.BoundedBy.varOf (by simp))
    exact Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainBounded)
      (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono placeholderBounded)
        (executableContextBounded.mono (SupplyExtends.bumpTy q 2)))
  let bodyRun := Classical.choice
    (synthBelow (Nat.lt_succ_self fuel)
      (selfEnv := (self, executablePlaceholder) ::
        selfEnv.eraseMany [self, argument]) (path := 0 :: path)
      bodyBefore bodyContexts bodyContextBounded bodyExecutableContextBounded
      bodyAudit bodyAdequate)
  have codomainRelatedAtBody : TyBisimulation
      bodyRun.run.completion.state.prevailing (.var (q.nextTy + 1))
      (fixCodomain state path) := by
    have atBody := bodyRun.run.transition.transportTy
      (show TyBisimulation bodyBefore.prevailing (.var (q.nextTy + 1))
          (fixCodomain state path) from by
        have atAllocation : TyBisimulation codomainAllocation.state.prevailing
            (.var (q.nextTy + 1)) (fixCodomain state path) := by
          change TyBisimulation codomainAllocation.state.prevailing
            (.var (q.nextTy + 1))
            ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
              codomainOrigin).1
          rw [codomainAllocation.target_eq]
          exact codomainAllocation.state.prevailing.sameTarget _
        exact directExtension.transportTy
          (placeholderExtension.transportTy atAllocation))
    exact atBody
  have bodyDeclarativeBounded : bodyTarget.BoundedBy q₁ :=
    (bodyRaw.boundedBy closed
      codomainAllocation.state.declarative_bounded bodyContextBounded).2
  have codomainBounded : Ty.BoundedBy q₁ (.var (q.nextTy + 1)) :=
    (Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends
  have executableCodomainBounded : (fixCodomain state path).BoundedBy q₁ := by
    change (((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
      codomainOrigin).1).BoundedBy q₁
    rw [codomainAllocation.target_eq]
    exact codomainBounded
  let alignmentRun :=
    DemandTypingInferenceCompletenessAlignmentTraversal.ddAlignTypesWithLedger_complete
      (origin := resultOrigin) bodyRun.run.completion.state bodyRun.run.target
      codomainRelatedAtBody bodyDeclarativeBounded codomainBounded
      bodyRun.rawTargetBounded executableCodomainBounded aligned
  let rawRun := DemandTypingInferenceCompletenessExprTraversal.inferExprFuel_fix_complete
    before distinct direct nonMatcher bodyRun.run alignmentRun
  exact ⟨⟨rawRun, by
    have placeholderBounded : executablePlaceholder.BoundedBy q₁ := by
      change (Ty.fn (visit state .exprFix path |>.freshTy domainOrigin).1
        ((visit state .exprFix path |>.freshTy domainOrigin).2.freshTy
          codomainOrigin).1).BoundedBy q₁
      rw [domainAllocation.target_eq, codomainAllocation.target_eq]
      exact Ty.BoundedBy.fnOf
        ((Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends)
        ((Ty.BoundedBy.varOf (by simp)).mono bodyOrigin.erase.supplyExtends)
    exact placeholderBounded⟩⟩

/-- A matcher capability inferred from already-normalized clause holes is an
image of the idempotent local substitution and is therefore already fixed. -/
theorem matcherInferredCapability_fixed
    {signature : FrozenSig} {S : Subst}
    {clauses : List Clause} {rawHoleLists : List (List Dual)}
    {evidence : List Shape.Evidence} {capability : Cap}
    (idempotent : S.Idempotent)
    (collected : collectClauseEvidence signature.toMatcherSig clauses
      (terminalHoleCaps S rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability) :
    capability.apply S.cap = capability := by
  apply Cap.apply_eq_self_of_fcv_fixed
  intro varId varMem
  obtain ⟨holeCaps, holeCapsMem, varIn⟩ :=
    Inference.collectClauseEvidence_fcv collected varId
      (Shape.inferShape_fcv inferred varMem)
  obtain ⟨rawHoles, rawHolesMem, rfl⟩ := List.mem_map.mp holeCapsMem
  obtain ⟨resolvedCap, resolvedCapMem, varInCap⟩ :=
    Cap.mem_fcvList_split varIn
  obtain ⟨resolvedDual, resolvedDualMem, rfl⟩ :=
    List.mem_map.mp resolvedCapMem
  obtain ⟨rawDual, rawDualMem, rfl⟩ := List.mem_map.mp resolvedDualMem
  apply idempotent.image_cap_fixed (.matcher rawDual.cap rawDual.target) varId
  change varId ∈ (S.apply (.matcher rawDual.cap rawDual.target)).fcv
  simp only [Subst.apply_matcher, Ty.fcv, List.mem_append]
  exact Or.inl varInCap

/-- Final assembly of a matcher literal once the clause dispatcher and its
paired local finalization bridge have been reconstructed.  Keeping this
constructor independent isolates the remaining equivariance proof which
builds `MatcherFinalizationCompletion` from DD finalization evidence. -/
theorem auditedSynthMatcher_complete_of_finalization
    {signature : FrozenSig} {declarativeContext executableContext : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {clauses : List Clause}
    {rawHoleLists : List (List Dual)} {capability : Cap}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger₁ : CapabilityOriginLedger} {state : InferState}
    (fuel : Nat) (before : TraversalStateCorrespondence q S ledger state)
    (clausesRun : ClausesRunCompletion
      ((before.visit .exprMatcher path).freshTy
        (freshOrigin .matcherClause path "matcher-target")).state
      (inferClausesFuel fuel signature executableContext selfEnv path 0 clauses
        (.var q.nextTy)
        ((visit state .exprMatcher path).freshTy
          (freshOrigin .matcherClause path "matcher-target")).2)
      q' S' ledger₁ (.var q.nextTy) rawHoleLists)
    (finalization :
      DemandTypingInferenceCompletenessMatcherExprTraversal.MatcherFinalizationCompletion
        clausesRun signature clauses capability)
    (targetBounded : Ty.BoundedBy q' (.var q.nextTy)) :
    Nonempty (BoundedSynthRunCompletion before
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state) q' S'
      (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy))) := by
  let rawRun :=
    DemandTypingInferenceCompletenessMatcherExprTraversal.inferMatcherFuel_complete
      (before.visit .exprMatcher path) clausesRun finalization
  let finished :=
    DemandTypingInferenceCompletenessExprTraversal.SynthRunCompletion.finish
      rawRun (.matcher clauses) path
  let boundedFinished : BoundedSynthRunCompletion (before.visit .exprMatcher path)
      (do
        let inner ← inferMatcherFuel (fuel + 1) signature executableContext
          selfEnv path clauses (visit state .exprMatcher path)
        pure (finishExpr (.matcher clauses) path inner.target inner.state)) q' S'
      (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy)) :=
    ⟨finished, by
      change Ty.BoundedBy q'
        (.matcher finalization.executableCapability (.var q.nextTy))
      exact Ty.BoundedBy.matcherOf finalization.executableCapabilityBounded
        targetBounded⟩
  let normalized : BoundedSynthRunCompletion (before.visit .exprMatcher path)
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state) q' S'
      (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy)) := by
    have operationEq :
        (do
          let inner ← inferMatcherFuel (fuel + 1) signature executableContext
            selfEnv path clauses (visit state .exprMatcher path)
          pure (finishExpr (.matcher clauses) path inner.target inner.state)) =
        inferExprFuel (fuel + 2) signature executableContext selfEnv path
          (.matcher clauses) state := by
      simp only [inferExprFuel]
      cases inferMatcherFuel (fuel + 1) signature executableContext selfEnv path
          clauses (visit state .exprMatcher path) <;> rfl
    rw [← operationEq]
    exact boundedFinished
  let outerRun : SynthRunCompletion before
      (inferExprFuel (fuel + 2) signature executableContext selfEnv path
        (.matcher clauses) state) q' S'
      (DDLedger.freezeMatcherProducer ledger₁ capability)
      (.matcher capability (.var q.nextTy)) :=
    { normalized.run with
      transition := (before.visitExtension .exprMatcher path).seq
        normalized.run.transition }
  exact ⟨⟨outerRun, normalized.rawTargetBounded⟩⟩

end DemandTypingInferenceCompletenessMain
end TypePM
