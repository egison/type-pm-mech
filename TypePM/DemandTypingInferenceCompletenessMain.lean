import TypePM.DemandTypingInferenceCompletenessMatcherTraversal
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

end DemandTypingInferenceCompletenessMain
end TypePM
