import TypePM.InferenceBase
import TypePM.SchemeOpeningLists
import TypePM.Recursion
import TypePM.SourceSubstitution
import TypePM.PairedUnification

/-!
# Executable inference trace foundation

This module is the syntax-directed, terminating foundation for Algorithm W over
the two-sorted specification.  It deliberately separates
three layers:

* certified local solving (origin-oriented capability equality, paired target
  equality, and producer-stable `matchCap`),
* chronological replay of one prevailing paired substitution, and
* a complete traversal of the mutually recursive source syntax.

The state-free `TypingInvariant`/`ClauseTy` reconstruction is connected only after a
successful trace.  In particular, no inference result or bridge-condition
record contains the desired final typing judgment as a field.

The trace retains raw and prevailing-substitution-resolved forms separately.
This distinction is essential for matcher-clause holes: a raw hole
`chi ▷ tau` is consumed later as `C chi ▷ S tau`, never by inventing an
unrelated external slot constant.
-/

namespace TypePM
namespace Inference

/-! ## Resolved indices -/

/-- Resolve both components of a raw dual with the same prevailing pair. -/
def ResolvedDual (prevailing : Subst) (raw : Dual) : Dual :=
  raw.applySubst prevailing

/-- Resolve a raw list of hole duals without changing its source order. -/
def ResolvedDuals (prevailing : Subst) (raw : List Dual) : List Dual :=
  raw.map (ResolvedDual prevailing)

/-- Resolve every monomorphic pattern binding with one prevailing pair. -/
def ResolvedMonoCtx (prevailing : Subst) (raw : MonoCtx) : MonoCtx :=
  raw.applySubst prevailing

/-- Resolve an expression context capture-avoidably under scheme binders. -/
def ResolvedContext (prevailing : Subst) (raw : Context) : Context :=
  raw.applySubst prevailing

@[simp] theorem resolvedDual_id (raw : Dual) :
    ResolvedDual Subst.id raw = raw :=
  Dual.applySubst_id raw

@[simp] theorem resolvedDuals_id (raw : List Dual) :
    ResolvedDuals Subst.id raw = raw := by
  change List.map (ResolvedDual Subst.id) raw = raw
  induction raw with
  | nil => rfl
  | cons dual raw ih =>
      simp only [List.map_cons, resolvedDual_id]
      rw [ih]

@[simp] theorem resolvedMonoCtx_id (raw : MonoCtx) :
    ResolvedMonoCtx Subst.id raw = raw :=
  MonoCtx.applySubst_id raw

@[simp] theorem resolvedContext_id (raw : Context) :
    ResolvedContext Subst.id raw = raw :=
  Context.applySubst_id raw

/-! ## Constraint origins and certified local solving -/

/-- A reverse syntax path: the nearest child index is stored first. -/
abbrev SyntaxPath := List Nat

/-- The phase that emitted a constraint. -/
inductive ConstraintPhase where
  | expression
  | pattern
  | primitivePattern
  | dataPattern
  | matcherClause
  | matcherCoverage
  | recursiveBinder
deriving Repr, DecidableEq

/-- Stable source location retained by every solver step. -/
structure ConstraintOrigin where
  phase : ConstraintPhase
  path : SyntaxPath
  label : String
deriving Repr, DecidableEq

/--
The three primitive constraints solved by inference.

Capability equality is symmetric.  Target equality is symmetric but treats
capability annotations as rigid.  `producerToSlot` is intentionally one-way:
only the consumer capability may be instantiated.
-/
inductive Constraint where
  | capEq : Cap -> Cap -> Constraint
  | targetEq : Ty -> Ty -> Constraint
  | producerToSlot : Cap -> Ty -> Cap -> Ty -> Constraint
deriving Repr

/-- Apply the prevailing substitution to every occurrence in a constraint. -/
def Constraint.resolve (prevailing : Subst) : Constraint -> Constraint
  | .capEq left right =>
      .capEq (left.apply prevailing.cap) (right.apply prevailing.cap)
  | .targetEq left right =>
      .targetEq (prevailing.apply left) (prevailing.apply right)
  | .producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      .producerToSlot
        (producerCap.apply prevailing.cap)
        (prevailing.apply producerTarget)
        (consumerCap.apply prevailing.cap)
        (prevailing.apply consumerTarget)

/--
Local solver soundness, before composing the returned delta with earlier
solutions.  Cross-range conditions belong to replay, not to the local solver.
-/
def LocallySound (constraint : Constraint) (delta : Subst) : Prop :=
  match constraint with
  | .capEq left right =>
      delta.target = TySubst.id /\
      left.apply delta.cap = right.apply delta.cap
  | .targetEq left right =>
      delta.apply left = delta.apply right
  | .producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      OneWayAt delta.cap producerCap consumerCap /\
      (producerTarget.applyCapability delta.cap).applyTarget delta.target =
        (consumerTarget.applyCapability delta.cap).applyTarget delta.target

/-- The concrete executable solver branch that produced a local delta.
Unlike extensional local soundness, this certificate retains the exact
`mgu`/`matchCap` equations required by source reconstruction. -/
inductive SolveCertificate
    (ledger : CapabilityOriginLedger) : Constraint -> Subst -> Prop where
  | capEq {left right capabilitySubst} :
      Unification.mguCap left right = some capabilitySubst ->
      SolveCertificate ledger (.capEq left right)
        ⟨capabilitySubst, TySubst.id⟩
  | capEqOriented {left right result} :
      PairedUnification.solveCap
        (PairedUnification.mguOrientedCapCompleteFuel ledger left right)
        ledger left right = some result ->
      SolveCertificate ledger (.capEq left right)
        ⟨result.subst, TySubst.id⟩
  | targetEq {left right targetSubst} :
      Unification.mguTy left right = some targetSubst ->
      SolveCertificate ledger (.targetEq left right)
        ⟨CapSubst.id, targetSubst⟩
  | targetEqPaired {left right result} :
      PairedUnification.solvePairedTy
        (PairedUnification.mguPairedTyCompleteFuel ledger left right)
        ledger left right = some result ->
      SolveCertificate ledger (.targetEq left right) result.subst
  | producerToSlot
      {producerCap producerTarget consumerCap consumerTarget bindings
       targetSubst} :
      CapMatch.matchCap producerCap consumerCap = some bindings ->
      Unification.mguTy
        (producerTarget.applyCapability
          (bindings.toSubstWithin consumerCap.fcv))
        (consumerTarget.applyCapability
          (bindings.toSubstWithin consumerCap.fcv)) = some targetSubst ->
      SolveCertificate ledger
        (.producerToSlot producerCap producerTarget consumerCap consumerTarget)
        ⟨bindings.toSubstWithin consumerCap.fcv, targetSubst⟩

/-- A chronological solver step carrying its local soundness certificate. -/
structure SolveStep where
  solveCount : Nat
  origin : ConstraintOrigin
  /-- Origin policy observed at the exact solve cut. -/
  ledgerSnapshot : CapabilityOriginLedger
  constraint : Constraint
  delta : Subst
  /-- Finite support of the target component, produced by target mgu. -/
  targetDomain : List TypePM.TyVar
  targetSupport : delta.target.SupportWithin targetDomain
  certificate : SolveCertificate ledgerSnapshot constraint delta
  locallySound : LocallySound constraint delta

/-- The exact restricted substitution returned by `matchCap` is one-way. -/
theorem matchCap_restricted_sound
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    (hmatch : CapMatch.matchCap producer consumer = some bindings) :
    OneWayAt
      (bindings.toSubstWithin consumer.fcv) producer consumer := by
  exact CapMatch.matchCap_restricted_sound hmatch

/--
Solve an already-resolved primitive constraint.  Every success contains the
corresponding unifier/matcher soundness proof; failure is explicit.
-/
def solveResolvedAt
    (ledger : CapabilityOriginLedger)
    (solveCount : Nat) (origin : ConstraintOrigin) (constraint : Constraint) :
    Option SolveStep :=
  match constraint with
  | .capEq left right =>
      match hsolve : Unification.mguCap left right with
      | none => none
      | some capabilitySubst =>
          some {
            solveCount := solveCount
            origin := origin
            ledgerSnapshot := ledger
            constraint := .capEq left right
            delta := ⟨capabilitySubst, TySubst.id⟩
            targetDomain := []
            targetSupport := TySubst.id_supportWithin []
            certificate := .capEq hsolve
            locallySound := ⟨rfl, Unification.mguCap_sound hsolve⟩
          }
  | .targetEq left right =>
      match hsolve : Unification.mguTy left right with
      | none => none
      | some targetSubst =>
          some {
            solveCount := solveCount
            origin := origin
            ledgerSnapshot := ledger
            constraint := .targetEq left right
            delta := ⟨CapSubst.id, targetSubst⟩
            targetDomain := Unification.mguTySupport left right
            targetSupport := Unification.mguTy_support hsolve
            certificate := .targetEq hsolve
            locallySound := by
              change
                (Subst.mk CapSubst.id targetSubst).apply left =
                  (Subst.mk CapSubst.id targetSubst).apply right
              rw [Subst.apply, Subst.apply, Ty.applyCapability_id,
                Ty.applyCapability_id]
              exact Unification.mguTy_sound hsolve
          }
  | .producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      match hmatch : CapMatch.matchCap producerCap consumerCap with
      | none => none
      | some bindings =>
          let capabilitySubst :=
            bindings.toSubstWithin consumerCap.fcv
          match hsolve : Unification.mguTy
              (producerTarget.applyCapability capabilitySubst)
              (consumerTarget.applyCapability capabilitySubst) with
          | none => none
          | some targetSubst =>
              some {
                solveCount := solveCount
                origin := origin
                ledgerSnapshot := ledger
                constraint := .producerToSlot
                  producerCap producerTarget consumerCap consumerTarget
                delta := ⟨capabilitySubst, targetSubst⟩
                targetDomain := Unification.mguTySupport
                  (producerTarget.applyCapability capabilitySubst)
                  (consumerTarget.applyCapability capabilitySubst)
                targetSupport := Unification.mguTy_support hsolve
                certificate := .producerToSlot hmatch hsolve
                locallySound :=
                  ⟨matchCap_restricted_sound hmatch,
                    Unification.mguTy_sound hsolve⟩
              }

/-- Legacy symmetric solver, retained for specification-level regressions and
raw candidate inspection.  Executable W uses the ledger-aware entry below. -/
def solveResolved
    (solveCount : Nat) (origin : ConstraintOrigin) (constraint : Constraint) :
    Option SolveStep :=
  solveResolvedAt [] solveCount origin constraint

/-- Ledger-aware origin-oriented capability equality solving. -/
def solveCapEqWithLedger
    (ledger : CapabilityOriginLedger)
    (solveCount : Nat) (origin : ConstraintOrigin)
    (left right : Cap) : Option SolveStep :=
  match hsolve : PairedUnification.solveCap
      (PairedUnification.mguOrientedCapCompleteFuel ledger left right)
      ledger left right with
  | none => none
  | some result =>
      some {
        solveCount := solveCount
        origin := origin
        ledgerSnapshot := ledger
        constraint := .capEq left right
        delta := ⟨result.subst, TySubst.id⟩
        targetDomain := []
        targetSupport := TySubst.id_supportWithin []
        certificate := .capEqOriented hsolve
        locallySound := ⟨rfl, result.sound⟩
      }

/-- Ledger-aware recursive paired target equality solving. -/
def solveTargetEqWithLedger
    (ledger : CapabilityOriginLedger)
    (solveCount : Nat) (origin : ConstraintOrigin)
    (left right : Ty) : Option SolveStep :=
  match hsolve : PairedUnification.solvePairedTy
      (PairedUnification.mguPairedTyCompleteFuel ledger left right)
      ledger left right with
  | none => none
  | some result =>
      some {
        solveCount := solveCount
        origin := origin
        ledgerSnapshot := ledger
        constraint := .targetEq left right
        delta := result.subst
        targetDomain := result.targetSupportVars
        targetSupport := result.targetSupport
        certificate := .targetEqPaired hsolve
        locallySound := result.sound
      }

/-- Ledger-checked form of the dedicated one-way producer-to-slot solver.
The exact restricted `CapMatch` substitution is checked before target
unification and before a chronological step is emitted. -/
def solveProducerToSlotWithLedger
    (ledger : CapabilityOriginLedger)
    (solveCount : Nat) (origin : ConstraintOrigin)
    (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty) : Option SolveStep :=
  match hmatch : CapMatch.matchCap producerCap consumerCap with
  | none => none
  | some bindings =>
      let capabilitySubst := bindings.toSubstWithin consumerCap.fcv
      if admissibleCapPostCheck ledger capabilitySubst consumerCap.fcv then
        match hsolve : Unification.mguTy
            (producerTarget.applyCapability capabilitySubst)
            (consumerTarget.applyCapability capabilitySubst) with
        | none => none
        | some targetSubst =>
            some {
              solveCount := solveCount
              origin := origin
              ledgerSnapshot := ledger
              constraint := .producerToSlot
                producerCap producerTarget consumerCap consumerTarget
              delta := ⟨capabilitySubst, targetSubst⟩
              targetDomain := Unification.mguTySupport
                (producerTarget.applyCapability capabilitySubst)
                (consumerTarget.applyCapability capabilitySubst)
              targetSupport := Unification.mguTy_support hsolve
              certificate := .producerToSlot hmatch hsolve
              locallySound :=
                ⟨matchCap_restricted_sound hmatch,
                  Unification.mguTy_sound hsolve⟩
            }
      else
        none

/-- Resolve a primitive equality at one origin-ledger cut.  Capability
equality uses the oriented capability kernel, while ordinary equality uses
the recursive paired kernel so nested matcher/slot annotations observe the
same origin policy.  Producer-to-slot remains the dedicated one-way solver. -/
def solveResolvedWithLedger
    (ledger : CapabilityOriginLedger)
    (solveCount : Nat) (origin : ConstraintOrigin) (constraint : Constraint) :
    Option SolveStep :=
  match constraint with
  | .capEq left right =>
      solveCapEqWithLedger ledger solveCount origin left right
  | .targetEq left right =>
      solveTargetEqWithLedger ledger solveCount origin left right
  | .producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      solveProducerToSlotWithLedger ledger solveCount origin
        producerCap producerTarget consumerCap consumerTarget

/-! ## Cumulative replay -/

/-- Replay chronological solver deltas after an existing substitution. -/
def replayFrom : Subst -> List SolveStep -> Subst
  | prevailing, [] => prevailing
  | prevailing, step :: steps =>
      replayFrom (Subst.seq step.delta prevailing) steps

/-- Replay a whole trace from the identity substitution. -/
def replay (steps : List SolveStep) : Subst :=
  replayFrom Subst.id steps

/-- Apply solver deltas in chronological order to an already-resolved type. -/
def applyDeltas : List SolveStep -> Ty -> Ty
  | [], target => target
  | step :: steps, target => applyDeltas steps (step.delta.apply target)

/--
Semantic replay certificate retained by the reconstruction API.

Replay uses the cross-sort-aware `Subst.seq`, so chronological application is
unconditional: a later capability action is applied inside every earlier
target image while the new target component is built.  No range-fixedness or
cross-range commutation premise is required.
-/
def ReplayConditions (prevailing : Subst) (steps : List SolveStep) : Prop :=
  ∀ target,
    (replayFrom prevailing steps).apply target =
      applyDeltas steps (prevailing.apply target)

/-- Conditions for replaying a complete trace from identity. -/
def TraceReplayConditions (steps : List SolveStep) : Prop :=
  ReplayConditions Subst.id steps

/-- Executable finite check of the paper's paired-substitution range
condition.  `domain` is a certified support ledger for the target component. -/
def rangeFixedOnCheck (substitution : Subst)
    (domain : List TypePM.TyVar) : Bool :=
  domain.all fun varId =>
    decide ((substitution.target varId).applyCapability substitution.cap =
      substitution.target varId)

/-- Checking the certified finite support suffices for the total range
condition because the target substitution is identity off that support. -/
theorem rangeFixedOnCheck_sound
    {substitution : Subst} {domain : List TypePM.TyVar}
    (support : substitution.target.SupportWithin domain)
    (checked : rangeFixedOnCheck substitution domain = true) :
    substitution.RangeFixed := by
  intro varId
  by_cases member : varId ∈ domain
  · have point := List.all_eq_true.mp checked varId member
    exact of_decide_eq_true point
  · rw [support varId member]
    rfl

/-- The finite range check accepts every genuinely range-fixed paired
substitution, independently of the chosen certified support domain. -/
theorem rangeFixedOnCheck_complete
    {substitution : Subst} {domain : List TypePM.TyVar}
    (fixed : substitution.RangeFixed) :
    rangeFixedOnCheck substitution domain = true := by
  unfold rangeFixedOnCheck
  apply List.all_eq_true.mpr
  intro varId _membership
  exact decide_eq_true (fixed varId)

/-- Sequential replay agrees with chronological application unconditionally. -/
theorem replayFrom_apply
    (prevailing : Subst) (steps : List SolveStep) (target : Ty) :
    (replayFrom prevailing steps).apply target =
      applyDeltas steps (prevailing.apply target) := by
  induction steps generalizing prevailing target with
  | nil => rfl
  | cons step steps induction =>
      simp only [replayFrom, applyDeltas]
      rw [induction, Subst.seq_apply]

/-- Every chronological trace has a semantic replay certificate. -/
theorem replayConditions
    (prevailing : Subst) (steps : List SolveStep) :
    ReplayConditions prevailing steps := by
  exact replayFrom_apply prevailing steps

/-- Every complete trace has a replay certificate without an external audit. -/
theorem traceReplayConditions (steps : List SolveStep) :
    TraceReplayConditions steps := by
  exact replayConditions Subst.id steps

theorem replayFrom_append
    (prevailing : Subst) (front suffix : List SolveStep) :
    replayFrom prevailing (front ++ suffix) =
      replayFrom (replayFrom prevailing front) suffix := by
  induction front generalizing prevailing with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.cons_append, replayFrom]
      exact ih (Subst.seq step.delta prevailing)

theorem replay_snoc (steps : List SolveStep) (step : SolveStep) :
    replay (steps ++ [step]) = Subst.seq step.delta (replay steps) := by
  rw [replay, replayFrom_append]
  rfl

/-- A certified replay remains certified after dropping a chronological
prefix.  This is the suffix certificate used when a recursive W call is
reconstructed directly at the terminal prevailing substitution. -/
theorem ReplayConditions.afterPrefix
    {prevailing : Subst} {front suffix : List SolveStep}
    (_conditions : ReplayConditions prevailing (front ++ suffix)) :
    ReplayConditions (replayFrom prevailing front) suffix := by
  exact replayConditions (replayFrom prevailing front) suffix

/-- In particular, a full trace certificate supplies the certified suffix
after any concrete list prefix. -/
theorem TraceReplayConditions.afterPrefix
    {front suffix : List SolveStep}
    (conditions : TraceReplayConditions (front ++ suffix)) :
    ReplayConditions (replay front) suffix := by
  exact ReplayConditions.afterPrefix conditions

/-- Eliminate a semantic replay certificate. -/
theorem ReplayConditions.apply_eq_sequential
    {prevailing : Subst} {steps : List SolveStep}
    (conditions : ReplayConditions prevailing steps) (target : Ty) :
    (replayFrom prevailing steps).apply target =
      applyDeltas steps (prevailing.apply target) := by
  exact conditions target

/-! ## Inference trace and state -/

/-- Every source form receives a traversal event. -/
inductive NodeKind where
  | exprVar | exprLam | exprFix | exprApp | exprLit | exprTuple
  | exprCtor | exprPrim | exprLet | exprSomething | exprMatcher
  | exprMatchAll
  | patternVar | patternWild | patternValue | patternEmbed
  | patternCtor | patternAnd | patternOr | patternApp | patternTuple
  | ppatHole | ppatWild | ppatValue | ppatCtor | ppatTuple
  | dpatVar | dpatWild | dpatCtor | dpatTuple
  | arm | clause
deriving Repr, DecidableEq

/-- A capability-visible external flow location used by provenance replay. -/
structure FlowTag where
  path : SyntaxPath
  sourceName : String
  capability : Cap
  target : Ty
deriving Repr

/-- Non-solver observations retained by reconstruction. -/
inductive TraceEvent where
  | visit : NodeKind -> SyntaxPath -> TraceEvent
  | freshCap : ConstraintOrigin -> CapVar -> TraceEvent
  | freshTy : ConstraintOrigin -> TypePM.TyVar -> TraceEvent
  | fixPlaceholder : String -> String -> Ty -> SyntaxPath -> TraceEvent
  | directSelfAccepted : String -> Ty -> SyntaxPath -> TraceEvent
  | directSelfReference : String -> Ty -> SyntaxPath -> TraceEvent
  | actualClauseEvidence : Clause -> List Cap -> Shape.Evidence -> TraceEvent
  | literalCoverage : List Clause -> Cap -> TraceEvent
  | matcherFinalization : Nat -> List Clause ->
      Ty -> List (List Dual) -> Ty -> List (List Cap) ->
      List Shape.Evidence -> Cap -> TraceEvent
  | letGeneralization : Nat -> String -> Context -> Ty -> Context -> Ty ->
      Scheme -> TraceEvent
  | capabilityFlow : FlowTag -> Shape.Evidence -> TraceEvent
  | inferredExpr : Expr -> Ty -> SyntaxPath -> TraceEvent
  | inferredPattern : Pattern -> Dual -> MonoCtx -> SyntaxPath -> TraceEvent
  | patternVarFresh : Context -> PatternCtx -> MonoCtx -> CapVar ->
      TypePM.TyVar -> TraceEvent
  | patternWildFresh : Context -> PatternCtx -> MonoCtx -> CapVar ->
      TypePM.TyVar -> TraceEvent
  | patternValueFresh : Context -> PatternCtx -> MonoCtx -> CapVar -> Ty ->
      TraceEvent
  /-- Raw constructor-child and result capabilities at the local solving cut.
  The pattern branch checks their locally zonked forms immediately; the
  terminal validator reapplies the final prevailing substitution to these raw
  operands before checking `CapCompatible` again. -/
  | patternCtorCompatibility : Nat -> String -> List Cap -> Cap -> TraceEvent
  | inferredPPat : PPat -> Ty -> List Dual -> MonoCtx -> SyntaxPath -> TraceEvent
  | inferredDPat : DPat -> Ty -> MonoCtx -> SyntaxPath -> TraceEvent
  /-- One complete expected-type alignment.  The half-open solve interval
  `[startSolve, endSolve)` contains its exact raw certificates; later
  reconstruction relates that interval to a terminal suffix without rerunning
  either matcher or unifier on transformed inputs. -/
  | slotAlignment : Nat -> Nat -> Ty -> Ty -> TraceEvent
  /-- Symmetric type equality alignment, retaining the already-resolved local
  inputs and its exact half-open solver interval. -/
  | typeAlignment : Nat -> Nat -> Ty -> Ty -> Ty -> Ty -> TraceEvent
  /-- Capability/target equality for the two components of a pattern dual. -/
  | dualAlignment : Nat -> Nat -> Dual -> Dual -> Dual -> Dual -> TraceEvent
  | schemeInstantiation : Nat -> InferenceBase.FreshSupply -> Scheme ->
      String -> Context -> Context ->
      List CapVar -> List TypePM.TyVar -> List CapVar -> List TypePM.TyVar ->
      Ty -> List CapVar -> List TypePM.TyVar -> TraceEvent
  | ctorInstantiation : Nat -> InferenceBase.FreshSupply -> CtorScheme ->
      List Ty -> Ty -> List CapVar -> TraceEvent
  | dualInstantiation : Nat -> InferenceBase.FreshSupply -> DualScheme ->
      Context -> PatternCtx -> MonoCtx -> Context -> PatternCtx -> MonoCtx ->
      List CapVar -> List TypePM.TyVar -> List CapVar -> List TypePM.TyVar ->
      List Dual -> Dual -> List CapVar -> List TypePM.TyVar -> TraceEvent
  /-- Constructor/primitive-local capability binders are frozen only after
  their use is solved.  The event retains the raw images, exported payload,
  its cut-local resolved form, and the surviving image leaves that changed
  from structural flexibility to rename-only. -/
  | capabilityExportFreeze : Nat -> List CapVar -> Ty -> Ty ->
      List CapVar -> TraceEvent
deriving Repr

/-- Chronological solver and reconstruction traces. -/
structure InferTrace where
  solves : List SolveStep
  events : List TraceEvent

/-- Capability identifiers allocated either singly or by a quantified-binder
batch.  Keeping ownership in the executable trace lets finalization distinguish
inference-owned producer variables from free variables inherited from source
inputs. -/
def TraceEvent.allocatedCapVars : TraceEvent -> List CapVar
  | .freshCap _ varId => [varId]
  | .schemeInstantiation _ _ _ _ _ _ _ _ _ _ _ capImages _ => capImages
  | .ctorInstantiation _ _ _ _ _ capImages => capImages
  | .dualInstantiation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ capImages _ =>
      capImages
  | _ => []

/-- Every capability identifier allocated in a chronological trace. -/
def InferTrace.allocatedCapVars (trace : InferTrace) : List CapVar :=
  trace.events.flatMap TraceEvent.allocatedCapVars

/--
The only three origins allowed to seed known direct-self evidence.

The constructors contain source data, not a typing derivation.  Their concrete
validity is checked against the trace below, and the later reconstruction
bridge proves that a capability-flow event came from a typed occurrence.
-/
inductive KnownOrigin where
  | actualClause : Clause -> List Cap -> KnownOrigin
  | finalizedLiteral :
      List Clause -> List (List Cap) -> List Shape.Evidence -> Cap ->
      KnownOrigin
  | externalFlow : FlowTag -> KnownOrigin
deriving Repr

/-- Provenance-bearing inputs for the singleton direct-self evidence fold. -/
inductive ProducerSource where
  | known : Shape.Evidence -> KnownOrigin -> ProducerSource
  | selfReference : String -> Ty -> SyntaxPath -> ProducerSource
deriving Repr

/-- Mutable data threaded by the terminating inference traversal. -/
structure InferState where
  supply : InferenceBase.FreshSupply
  trace : InferTrace
  sources : List ProducerSource
  /-- Inference-owned capability variables exported by value-producing
  instantiations or finalized matcher producers. -/
  protectedCaps : List CapVar
  /-- Capability policy at the current chronological cut.  Equality solving
  reads this ledger directly; `protectedCaps` remains the legacy one-way and
  terminal-audit bridge for already exported producer leaves. -/
  capabilityOrigins : CapabilityOriginLedger

/-- Empty state at caller-supplied fresh lower bounds. -/
def InferState.empty
    (supply : InferenceBase.FreshSupply :=
      InferenceBase.FreshSupply.empty) : InferState :=
  ⟨supply, ⟨[], []⟩, [], [], []⟩

/--
The inference-owned variables that remain visible in a finalized matcher
capability.  Intersecting trace ownership with the final capability excludes
free source variables as well as temporary consumer and pattern metas that do
not belong to the matcher producer returned to the caller.
-/
def matcherProducerVars
    (state : InferState) (capability : Cap) : List CapVar :=
  capability.fcv.filter fun varId =>
    varId ∈ state.trace.allocatedCapVars

/-- Structurally flexible ledger leaves visible in a finalized matcher
producer.  Unlike `matcherProducerVars`, this selector governs only the
origin-ledger transition: already frozen variables need no redundant ledger
entry, while `protectedCaps` continues to retain trace-owned producer
variables for the one-way guard. -/
def matcherProducerLedgerLeaves
    (ledger : CapabilityOriginLedger) (capability : Cap) : List CapVar :=
  (capability.fcv.filter fun varId =>
      varId ∈ ledger.map Prod.fst).eraseDups.filter
    fun varId => ledger.originOf varId = .structuralFlexible

/-- Producer-owned variables after excluding capabilities borrowed from the
surrounding context or an active recursive placeholder. -/
def matcherProducerVarsExcept
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    List CapVar :=
  (matcherProducerVars state capability).filter fun varId =>
    varId ∉ borrowed

/-- Ledger leaves owned by the matcher itself, excluding borrowed variables. -/
def matcherProducerLedgerLeavesExcept
    (ledger : CapabilityOriginLedger) (capability : Cap)
    (borrowed : List CapVar) : List CapVar :=
  (matcherProducerLedgerLeaves ledger capability).filter fun varId =>
    varId ∉ borrowed

@[simp] theorem mem_matcherProducerVars
    (state : InferState) (capability : Cap) (varId : CapVar) :
    varId ∈ matcherProducerVars state capability ↔
      varId ∈ capability.fcv ∧
        varId ∈ state.trace.allocatedCapVars := by
  simp [matcherProducerVars]

/-- Protect exactly the inference-owned variables visible in a finalized matcher
producer.  This is a ledger-only update: supply, provenance, and chronological
history remain unchanged. -/
def InferState.protectMatcherCapability
    (state : InferState) (capability : Cap) : InferState :=
  { state with
    protectedCaps :=
      state.protectedCaps ++ matcherProducerVars state capability
    capabilityOrigins := state.capabilityOrigins.setOrigins
      (matcherProducerLedgerLeaves state.capabilityOrigins capability)
      .renameOnly }

/-- Finalize a matcher without freezing capability variables supplied by its
ambient context or active direct-self placeholder. -/
def InferState.protectMatcherCapabilityExcept
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    InferState :=
  { state with
    protectedCaps := state.protectedCaps ++
      matcherProducerVarsExcept state capability borrowed
    capabilityOrigins := state.capabilityOrigins.setOrigins
      (matcherProducerLedgerLeavesExcept state.capabilityOrigins capability
        borrowed)
      .renameOnly }

@[simp] theorem InferState.protectMatcherCapability_trace
    (state : InferState) (capability : Cap) :
    (state.protectMatcherCapability capability).trace =
      state.trace :=
  rfl

@[simp] theorem InferState.protectMatcherCapability_supply
    (state : InferState) (capability : Cap) :
    (state.protectMatcherCapability capability).supply =
      state.supply :=
  rfl

@[simp] theorem InferState.protectMatcherCapabilityExcept_trace
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).trace =
      state.trace :=
  rfl

@[simp] theorem InferState.protectMatcherCapabilityExcept_supply
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).supply =
      state.supply :=
  rfl

@[simp] theorem InferState.protectMatcherCapability_capabilityOrigins
    (state : InferState) (capability : Cap) :
    (state.protectMatcherCapability capability).capabilityOrigins =
      state.capabilityOrigins.setOrigins
        (matcherProducerLedgerLeaves state.capabilityOrigins capability)
        .renameOnly :=
  rfl

@[simp] theorem InferState.protectMatcherCapability_protectedCaps
    (state : InferState) (capability : Cap) :
    (state.protectMatcherCapability capability).protectedCaps =
      state.protectedCaps ++
        matcherProducerVars state capability :=
  rfl

@[simp] theorem InferState.protectMatcherCapabilityExcept_capabilityOrigins
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).capabilityOrigins =
      state.capabilityOrigins.setOrigins
        (matcherProducerLedgerLeavesExcept state.capabilityOrigins capability
          borrowed)
        .renameOnly :=
  rfl

@[simp] theorem InferState.protectMatcherCapabilityExcept_protectedCaps
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).protectedCaps =
      state.protectedCaps ++
        matcherProducerVarsExcept state capability borrowed :=
  rfl

theorem InferState.protectMatcherCapability_origin_of_mem
    (state : InferState) (capability : Cap) (varId : CapVar)
    (membership : varId ∈
      matcherProducerLedgerLeaves state.capabilityOrigins capability) :
    (state.protectMatcherCapability capability).capabilityOrigins.originOf
        varId = .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    state.capabilityOrigins
      (matcherProducerLedgerLeaves state.capabilityOrigins capability) varId
      .renameOnly membership

theorem InferState.protectMatcherCapabilityExcept_origin_of_mem
    (state : InferState) (capability : Cap) (borrowed : List CapVar)
    (varId : CapVar)
    (membership : varId ∈ matcherProducerLedgerLeavesExcept
      state.capabilityOrigins capability borrowed) :
    (state.protectMatcherCapabilityExcept capability borrowed).capabilityOrigins.originOf
        varId = .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    state.capabilityOrigins
      (matcherProducerLedgerLeavesExcept state.capabilityOrigins capability
        borrowed)
      varId .renameOnly membership

@[simp] theorem InferState.mem_protectMatcherCapability_protectedCaps
    (state : InferState) (capability : Cap) (varId : CapVar) :
    varId ∈ (state.protectMatcherCapability capability).protectedCaps ↔
      varId ∈ state.protectedCaps ∨
        (varId ∈ capability.fcv ∧
          varId ∈ state.trace.allocatedCapVars) := by
  simp

@[simp] theorem InferState.mem_protectMatcherCapabilityExcept_protectedCaps
    (state : InferState) (capability : Cap) (borrowed : List CapVar)
    (varId : CapVar) :
    varId ∈ (state.protectMatcherCapabilityExcept capability borrowed).protectedCaps ↔
      varId ∈ state.protectedCaps ∨
        (varId ∈ capability.fcv ∧
          varId ∈ state.trace.allocatedCapVars ∧ varId ∉ borrowed) := by
  simp [matcherProducerVarsExcept]
  grind

/-! ### Producer non-strengthening -/

/-- A capability substitution fixes every protected producer variable. -/
def FixesCapVars (substitution : CapSubst)
    (varIds : List CapVar) : Prop :=
  ∀ varId, varId ∈ varIds -> substitution varId = .var varId

/-- Executable form of `CapSubst.FixesVars`. -/
def capSubstFixesVarsCheck
    (substitution : CapSubst) (varIds : List CapVar) : Bool :=
  varIds.all fun varId => substitution varId == .var varId

theorem capSubstFixesVarsCheck_eq_true
    (substitution : CapSubst) (varIds : List CapVar) :
    capSubstFixesVarsCheck substitution varIds = true <->
      FixesCapVars substitution varIds := by
  simp [capSubstFixesVarsCheck, FixesCapVars, List.all_eq_true]

/-- A capability post sends every protected producer to a variable whose
origin is no longer structurally flexible.  Safe renaming is intentional:
producer freeze forbids structural strengthening, not alpha-renaming. -/
def SafeCapVars (ledger : CapabilityOriginLedger)
    (substitution : CapSubst) (varIds : List CapVar) : Prop :=
  ∀ varId, varId ∈ varIds →
    ∃ image,
      substitution varId = .var image ∧
        ledger.originOf image ≠ .structuralFlexible

/-- Finite executable check for ledger-safe producer renaming. -/
def capSubstSafeVarsCheck (ledger : CapabilityOriginLedger)
    (substitution : CapSubst) (varIds : List CapVar) : Bool :=
  varIds.all fun varId =>
    match substitution varId with
    | .var image => decide (ledger.originOf image ≠ .structuralFlexible)
    | _ => false

theorem capSubstSafeVarsCheck_eq_true
    (ledger : CapabilityOriginLedger) (substitution : CapSubst)
    (varIds : List CapVar) :
    capSubstSafeVarsCheck ledger substitution varIds = true ↔
      SafeCapVars ledger substitution varIds := by
  simp only [capSubstSafeVarsCheck, List.all_eq_true, SafeCapVars]
  constructor
  · intro checked varId membership
    have checkedAt := checked varId membership
    cases equation : substitution varId with
    | var image =>
        refine ⟨image, rfl, ?_⟩
        simpa [equation] using checkedAt
    | any => simp [equation] at checkedAt
    | skolem name => simp [equation] at checkedAt
    | con name children => simp [equation] at checkedAt
    | prod children => simp [equation] at checkedAt
  · intro safe varId membership
    rcases safe varId membership with ⟨image, equation, nonStructural⟩
    simp [equation, nonStructural]

/-- The final prevailing substitution preserves every protected producer as
a ledger-safe variable image.  Unlike the former guard, this condition does
not require each historical delta to fix every producer pointwise. -/
def ProtectedProducerTrace (state : InferState) : Prop :=
  SafeCapVars state.capabilityOrigins (replay state.trace.solves).cap
    state.protectedCaps

/-- Executable terminal audit of producer non-strengthening. -/
def protectedProducerTraceCheck (state : InferState) : Bool :=
  capSubstSafeVarsCheck state.capabilityOrigins
    (replay state.trace.solves).cap
    state.protectedCaps

theorem protectedProducerTraceCheck_eq_true (state : InferState) :
  protectedProducerTraceCheck state = true <->
      ProtectedProducerTrace state := by
  exact capSubstSafeVarsCheck_eq_true _ _ _

/-- The unique prevailing substitution is replayed from all prior steps. -/
def InferState.prevailing (state : InferState) : Subst :=
  replay state.trace.solves

@[simp] theorem InferState.protectMatcherCapability_prevailing
    (state : InferState) (capability : Cap) :
    (state.protectMatcherCapability capability).prevailing =
      state.prevailing :=
  rfl

@[simp] theorem InferState.protectMatcherCapabilityExcept_prevailing
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    (state.protectMatcherCapabilityExcept capability borrowed).prevailing =
      state.prevailing :=
  rfl

/-- `later` extends the chronological solver/event history of `earlier`.
Inference is allowed to advance the fresh supply and its producer ledgers, but
it never edits an already emitted solver certificate or reconstruction event.
Keeping this relation about history only makes it stable under all of those
other state updates. -/
def InferState.HistoryPrefix (earlier later : InferState) : Prop :=
  ∃ solveSuffix eventSuffix,
    later.trace.solves = earlier.trace.solves ++ solveSuffix ∧
    later.trace.events = earlier.trace.events ++ eventSuffix

theorem InferState.HistoryPrefix.refl (state : InferState) :
    state.HistoryPrefix state := by
  exact ⟨[], [], by simp, by simp⟩

theorem InferState.HistoryPrefix.trans
    {first middle last : InferState}
    (front : first.HistoryPrefix middle)
    (back : middle.HistoryPrefix last) :
    first.HistoryPrefix last := by
  rcases front with ⟨frontSolves, frontEvents, hfrontSolves, hfrontEvents⟩
  rcases back with ⟨backSolves, backEvents, hbackSolves, hbackEvents⟩
  refine ⟨frontSolves ++ backSolves, frontEvents ++ backEvents, ?_, ?_⟩
  · rw [hbackSolves, hfrontSolves, List.append_assoc]
  · rw [hbackEvents, hfrontEvents, List.append_assoc]

/-- Every event already present in a prefix remains present in the final
trace. -/
theorem InferState.HistoryPrefix.event_mem
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    {event : TraceEvent} (membership : event ∈ earlier.trace.events) :
    event ∈ later.trace.events := by
  rcases history with ⟨_, suffix, _, events⟩
  rw [events]
  exact List.mem_append_left suffix membership

/-- Every solver certificate already present in a prefix remains present in
the final trace. -/
theorem InferState.HistoryPrefix.solve_mem
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    {step : SolveStep} (membership : step ∈ earlier.trace.solves) :
    step ∈ later.trace.solves := by
  rcases history with ⟨suffix, _, solves, _⟩
  rw [solves]
  exact List.mem_append_left suffix membership

/-- The final prevailing substitution is precisely replay of the suffix after
the prefix prevailing substitution. -/
theorem InferState.HistoryPrefix.prevailing_eq
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    ∃ suffix,
      later.prevailing = replayFrom earlier.prevailing suffix := by
  rcases history with ⟨suffix, _, solves, _⟩
  refine ⟨suffix, ?_⟩
  simp only [InferState.prevailing, replay]
  rw [solves, replayFrom_append]

/-- A history prefix cannot contain more solver steps than its extension. -/
theorem InferState.HistoryPrefix.solve_length_le
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    earlier.trace.solves.length ≤ later.trace.solves.length := by
  rcases history with ⟨suffix, _, solves, _⟩
  rw [solves, List.length_append]
  exact Nat.le_add_right _ _

/-- A history prefix cannot contain more events than its extension. -/
theorem InferState.HistoryPrefix.event_length_le
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    earlier.trace.events.length ≤ later.trace.events.length := by
  rcases history with ⟨_, suffix, _, events⟩
  rw [events, List.length_append]
  exact Nat.le_add_right _ _

/-- Taking the old solver length from an extended history recovers the old
solver list exactly. -/
theorem InferState.HistoryPrefix.take_solves
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    later.trace.solves.take earlier.trace.solves.length =
      earlier.trace.solves := by
  rcases history with ⟨suffix, _, solves, _⟩
  rw [solves, List.take_append_of_le_length (Nat.le_refl _)]
  simp

/-- Taking the old event length from an extended history recovers the old
event list exactly. -/
theorem InferState.HistoryPrefix.take_events
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    later.trace.events.take earlier.trace.events.length =
      earlier.trace.events := by
  rcases history with ⟨_, suffix, _, events⟩
  rw [events, List.take_append_of_le_length (Nat.le_refl _)]
  simp

/-- The half-open interval following a history prefix is exactly the suffix
appended by that prefix relation. -/
theorem InferState.HistoryPrefix.solveSlice_eq_suffix
    {earlier later : InferState} (history : earlier.HistoryPrefix later) :
    ∃ suffix,
      later.trace.solves = earlier.trace.solves ++ suffix ∧
      (later.trace.solves.take later.trace.solves.length).drop
          earlier.trace.solves.length = suffix := by
  rcases history with ⟨suffix, _, solves, _⟩
  refine ⟨suffix, solves, ?_⟩
  rw [solves]
  change
    ((earlier.trace.solves ++ suffix).take
      (earlier.trace.solves ++ suffix).length).drop
        earlier.trace.solves.length = suffix
  rw [List.take_length, List.drop_append_length]

/-- Certified replay identifies the final value of every raw target with the
chronological deltas occurring after an arbitrary successful prefix. -/
theorem InferState.HistoryPrefix.final_apply_eq_applyDeltas
    {earlier later : InferState} (history : earlier.HistoryPrefix later)
    (conditions : TraceReplayConditions later.trace.solves) (target : Ty) :
    later.prevailing.apply target =
      applyDeltas
        ((later.trace.solves.take later.trace.solves.length).drop
          earlier.trace.solves.length)
        (earlier.prevailing.apply target) := by
  rcases history with ⟨suffix, _, solves, _⟩
  have suffixConditions : ReplayConditions earlier.prevailing suffix := by
    rw [solves] at conditions
    simpa only [InferState.prevailing, replay] using
      TraceReplayConditions.afterPrefix conditions
  have sequential := suffixConditions.apply_eq_sequential target
  simp only [InferState.prevailing, replay] at sequential ⊢
  rw [solves, replayFrom_append]
  simp only [List.take_length, List.drop_append_length]
  exact sequential

/-- Updating non-history fields preserves the history prefix reflexively. -/
theorem InferState.HistoryPrefix.of_same_trace
    {earlier later : InferState} (same : later.trace = earlier.trace) :
    earlier.HistoryPrefix later := by
  refine ⟨[], [], ?_, ?_⟩
  · simpa using congrArg InferTrace.solves same
  · simpa using congrArg InferTrace.events same

/-- Final matcher-producer protection changes only the producer ledger. -/
theorem InferState.historyPrefix_protectMatcherCapability
    (state : InferState) (capability : Cap) :
    state.HistoryPrefix
      (state.protectMatcherCapability capability) := by
  exact InferState.HistoryPrefix.of_same_trace rfl

/-- Excluding context-owned variables from final matcher-producer protection
also changes only the producer ledger. -/
theorem InferState.historyPrefix_protectMatcherCapabilityExcept
    (state : InferState) (capability : Cap) (borrowed : List CapVar) :
    state.HistoryPrefix
      (state.protectMatcherCapabilityExcept capability borrowed) := by
  exact InferState.HistoryPrefix.of_same_trace rfl

/-- Eliminate the state component of a successful pair-returning helper. -/
theorem InferState.HistoryPrefix.snd_of_eq
    {α : Type} {initial final : InferState} {pair : α × InferState}
    {value : α} (history : initial.HistoryPrefix pair.2)
    (equality : pair = (value, final)) : initial.HistoryPrefix final := by
  have stateEquality : pair.2 = final := congrArg Prod.snd equality
  simpa only [stateEquality] using history

/-- Rewrite the terminal state of an append-only history. -/
theorem InferState.HistoryPrefix.right_congr
    {initial first second : InferState}
    (history : initial.HistoryPrefix first) (equality : first = second) :
    initial.HistoryPrefix second := by
  subst second
  exact history

/-- Append a reconstruction event in source order. -/
def InferState.recordEvent
    (state : InferState) (event : TraceEvent) : InferState :=
  { state with trace.events := state.trace.events ++ [event] }

/-- Append one certified local solution in chronological order. -/
def InferState.recordSolve
    (state : InferState) (step : SolveStep) : InferState :=
  { state with trace.solves := state.trace.solves ++ [step] }

/-- Retain one direct-self source in chronological discovery order. -/
def InferState.recordSource
    (state : InferState) (source : ProducerSource) : InferState :=
  { state with sources := state.sources ++ [source] }

theorem InferState.historyPrefix_recordEvent
    (state : InferState) (event : TraceEvent) :
    state.HistoryPrefix (state.recordEvent event) := by
  exact ⟨[], [event], by simp [InferState.recordEvent],
    by simp [InferState.recordEvent]⟩

theorem InferState.historyPrefix_recordSolve
    (state : InferState) (step : SolveStep) :
    state.HistoryPrefix (state.recordSolve step) := by
  exact ⟨[step], [], by simp [InferState.recordSolve],
    by simp [InferState.recordSolve]⟩

theorem InferState.historyPrefix_recordSource
    (state : InferState) (source : ProducerSource) :
    state.HistoryPrefix (state.recordSource source) := by
  exact ⟨[], [], by simp [InferState.recordSource],
    by simp [InferState.recordSource]⟩

@[simp] theorem InferState.prevailing_recordEvent
    (state : InferState) (event : TraceEvent) :
    (state.recordEvent event).prevailing = state.prevailing :=
  rfl

theorem InferState.prevailing_recordSolve
    (state : InferState) (step : SolveStep) :
    (state.recordSolve step).prevailing =
      Subst.seq step.delta state.prevailing := by
  exact replay_snoc state.trace.solves step

/-- Resolve and solve one constraint against all preceding solutions. -/
def runConstraint
    (state : InferState) (origin : ConstraintOrigin)
    (raw : Constraint) : Option InferState := do
  let resolved := raw.resolve state.prevailing
  let step <- solveResolvedWithLedger state.capabilityOrigins
    state.trace.solves.length origin resolved
  match resolved with
  | .producerToSlot _ _ _ _ =>
      if capSubstSafeVarsCheck state.capabilityOrigins step.delta.cap
          state.protectedCaps then
        pure (state.recordSolve step)
      else
        none
  | _ => pure (state.recordSolve step)

/-- Allocate and trace one fresh target meta. -/
def InferState.freshTy
    (state : InferState) (origin : ConstraintOrigin) : Ty × InferState :=
  let (target, supply) := InferenceBase.freshTyMeta state.supply
  let event := TraceEvent.freshTy origin state.supply.nextTy
  (target, ({ state with supply := supply }).recordEvent event)

/-- Allocate and trace one fresh capability meta. -/
def InferState.freshCap
    (state : InferState) (origin : ConstraintOrigin) : Cap × InferState :=
  let (capability, supply) := InferenceBase.freshCapMeta state.supply
  let event := TraceEvent.freshCap origin ⟨state.supply.nextCap⟩
  let state :=
    { state with
      supply := supply
      capabilityOrigins := state.capabilityOrigins.setOrigin
        ⟨state.supply.nextCap⟩ .structuralFlexible }
  (capability, state.recordEvent event)

@[simp] theorem InferState.freshTy_advances
    (state : InferState) (origin : ConstraintOrigin) :
    (state.freshTy origin).2.supply.nextTy = state.supply.nextTy + 1 :=
  rfl

@[simp] theorem InferState.freshCap_advances
    (state : InferState) (origin : ConstraintOrigin) :
    (state.freshCap origin).2.supply.nextCap = state.supply.nextCap + 1 :=
  rfl

@[simp] theorem InferState.freshCap_capabilityOrigin
    (state : InferState) (origin : ConstraintOrigin) :
    ((state.freshCap origin).2.capabilityOrigins.originOf
      ⟨state.supply.nextCap⟩) = .structuralFlexible := by
  simp [InferState.freshCap, InferState.recordEvent]

/-! ## Executable mandatory coverage -/

mutual

/-- Structural equality for primitive-pattern patterns. -/
def ppatEq : PPat -> PPat -> Bool
  | .hole, .hole => true
  | .wild, .wild => true
  | .pval left, .pval right => left == right
  | .ctor leftName leftChildren, .ctor rightName rightChildren =>
      leftName == rightName && ppatListEq leftChildren rightChildren
  | .tuple left, .tuple right => ppatListEq left right
  | _, _ => false

/-- Structural equality for primitive-pattern lists. -/
def ppatListEq : List PPat -> List PPat -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      ppatEq left right && ppatListEq lefts rights
  | _, _ => false

end

mutual

theorem ppatEq_eq_true : forall left right,
    ppatEq left right = true <-> left = right
  | .hole, right => by cases right <;> simp [ppatEq]
  | .wild, right => by cases right <;> simp [ppatEq]
  | .pval name, right => by cases right <;> simp [ppatEq]
  | .ctor name children, right => by
      cases right <;> simp [ppatEq, ppatListEq_eq_true]
  | .tuple patterns, right => by
      cases right <;> simp [ppatEq, ppatListEq_eq_true]

theorem ppatListEq_eq_true : forall left right,
    ppatListEq left right = true <-> left = right
  | [], right => by cases right <;> simp [ppatListEq]
  | left :: lefts, right => by
      cases right <;>
        simp [ppatListEq, ppatEq_eq_true, ppatListEq_eq_true]

end

/-- Does the actual clause list contain this exact primitive pattern? -/
def hasClausePP : List Clause -> PPat -> Bool
  | [], _ => false
  | clause :: clauses, pattern =>
      ppatEq clause.pp pattern || hasClausePP clauses pattern

theorem hasClausePP_sound
    {clauses : List Clause} {pattern : PPat}
    (hcheck : hasClausePP clauses pattern = true) :
    HasClausePP clauses pattern := by
  induction clauses with
  | nil => simp [hasClausePP] at hcheck
  | cons clause clauses ih =>
      simp only [hasClausePP, Bool.or_eq_true] at hcheck
      rcases hcheck with hhead | htail
      · exact ⟨clause, by simp, (ppatEq_eq_true _ _).mp hhead⟩
      · rcases ih htail with ⟨found, hmem, heq⟩
        exact ⟨found, by simp [hmem], heq⟩

theorem hasClausePP_complete
    {clauses : List Clause} {pattern : PPat}
    (hfound : HasClausePP clauses pattern) :
    hasClausePP clauses pattern = true := by
  rcases hfound with ⟨found, hmem, heq⟩
  induction clauses with
  | nil => cases hmem
  | cons clause clauses ih =>
      simp only [List.mem_cons] at hmem
      simp only [hasClausePP, Bool.or_eq_true]
      rcases hmem with hhead | htail
      · subst found
        exact Or.inl ((ppatEq_eq_true _ _).mpr heq)
      · exact Or.inr (ih htail)

theorem hasClausePP_eq_true (clauses : List Clause) (pattern : PPat) :
    hasClausePP clauses pattern = true <-> HasClausePP clauses pattern :=
  ⟨hasClausePP_sound, hasClausePP_complete⟩

/-- Every constructor required by a former has an exact general clause. -/
def constructorsCovered
    (clauses : List Clause) (constructors : List GeneralCtor) : Bool :=
  constructors.all fun constructor =>
    hasClausePP clauses (generalPP constructor.1 constructor.2)

theorem constructorsCovered_sound
    {clauses : List Clause} {constructors : List GeneralCtor}
    (hcheck : constructorsCovered clauses constructors = true) :
    forall constructor,
      constructor ∈ constructors ->
      HasClausePP clauses (generalPP constructor.1 constructor.2) := by
  intro constructor hmem
  apply hasClausePP_sound
  exact List.all_eq_true.mp hcheck constructor hmem

theorem constructorsCovered_complete
    {clauses : List Clause} {constructors : List GeneralCtor}
    (hcovered : forall constructor,
      constructor ∈ constructors ->
      HasClausePP clauses (generalPP constructor.1 constructor.2)) :
    constructorsCovered clauses constructors = true := by
  apply List.all_eq_true.mpr
  intro constructor hmem
  exact hasClausePP_complete (hcovered constructor hmem)

/--
Decide the formal core's shallow `CoverageOK` requirement.

This checker is mandatory at every matcher-literal finalization.  Flexible or
skolem roots fail closed; `Any`, constructor, and product roots follow the
declarative definition exactly.
-/
def coverageCheck
    (signature : FrozenMatcherSig) (clauses : List Clause) : Cap -> Bool
  | .any => true
  | .con former _ =>
      match signature.constructorsFor? former with
      | none => false
      | some constructors => constructorsCovered clauses constructors
  | .prod components =>
      hasClausePP clauses (generalTuplePP components.length)
  | .var _ => false
  | .skolem _ => false

theorem coverageCheck_sound
    {signature : FrozenMatcherSig} {clauses : List Clause} {capability : Cap}
    (hcheck : coverageCheck signature clauses capability = true) :
    CoverageOK signature clauses capability := by
  cases capability with
  | any => trivial
  | var varId => simp [coverageCheck] at hcheck
  | skolem skolemId => simp [coverageCheck] at hcheck
  | con former children =>
      simp only [coverageCheck] at hcheck
      split at hcheck
      next => contradiction
      next constructors hlookup =>
        exact ⟨constructors, hlookup,
          constructorsCovered_sound hcheck⟩
  | prod components =>
      exact hasClausePP_sound hcheck

theorem coverageCheck_complete
    {signature : FrozenMatcherSig} {clauses : List Clause} {capability : Cap}
    (hcoverage : CoverageOK signature clauses capability) :
    coverageCheck signature clauses capability = true := by
  cases capability with
  | any => rfl
  | var varId => contradiction
  | skolem skolemId => contradiction
  | con former children =>
      rcases hcoverage with ⟨constructors, hlookup, hcovered⟩
      simp only [coverageCheck]
      rw [hlookup]
      exact constructorsCovered_complete hcovered
  | prod components =>
      exact hasClausePP_complete hcoverage

theorem coverageCheck_eq_true
    (signature : FrozenMatcherSig) (clauses : List Clause)
    (capability : Cap) :
    coverageCheck signature clauses capability = true <->
      CoverageOK signature clauses capability :=
  ⟨coverageCheck_sound, coverageCheck_complete⟩

/-- Reject failure or record a proof-reconstructible successful coverage run. -/
def checkCoverage
    (signature : FrozenMatcherSig) (clauses : List Clause)
    (capability : Cap) (state : InferState) : Option InferState :=
  if coverageCheck signature clauses capability then
    some (state.recordEvent (.literalCoverage clauses capability))
  else
    none

theorem checkCoverage_success_sound
    {signature : FrozenMatcherSig} {clauses : List Clause}
    {capability : Cap} {state result : InferState}
    (hsuccess : checkCoverage signature clauses capability state = some result) :
    CoverageOK signature clauses capability := by
  unfold checkCoverage at hsuccess
  split at hsuccess
  next htrue => exact coverageCheck_sound htrue
  next => contradiction

/-! ## Concrete direct-self source provenance -/

/-- Pointwise actual-clause evidence, preserving all three source-order lists. -/
inductive ClauseEvidenceList (signature : FrozenMatcherSig) :
    List Clause -> List (List Cap) -> List Shape.Evidence -> Prop where
  | nil : ClauseEvidenceList signature [] [] []
  | cons {clause clauses holes holeLists evidence evidences} :
      clauseEvidence signature clause.pp holes = some evidence ->
      ClauseEvidenceList signature clauses holeLists evidences ->
      ClauseEvidenceList signature
        (clause :: clauses) (holes :: holeLists) (evidence :: evidences)

/-- Execute the actual-clause evidence pass for an exact-length hole ledger. -/
def collectClauseEvidence
    (signature : FrozenMatcherSig) :
    List Clause -> List (List Cap) -> Option (List Shape.Evidence)
  | [], [] => some []
  | clause :: clauses, holes :: holeLists => do
      let evidence <- clauseEvidence signature clause.pp holes
      let evidences <- collectClauseEvidence signature clauses holeLists
      pure (evidence :: evidences)
  | _, _ => none

theorem collectClauseEvidence_sound
    {signature : FrozenMatcherSig} {clauses : List Clause}
    {holeLists : List (List Cap)} {evidences : List Shape.Evidence}
    (hcollect :
      collectClauseEvidence signature clauses holeLists = some evidences) :
    ClauseEvidenceList signature clauses holeLists evidences := by
  induction clauses generalizing holeLists evidences with
  | nil =>
      cases holeLists <;> simp [collectClauseEvidence] at hcollect
      subst evidences
      exact .nil
  | cons clause clauses ih =>
      cases holeLists with
      | nil => simp [collectClauseEvidence] at hcollect
      | cons holes holeLists =>
          cases hevidence : clauseEvidence signature clause.pp holes with
          | none =>
              simp [collectClauseEvidence, hevidence] at hcollect
          | some evidence =>
              cases hrest :
                  collectClauseEvidence signature clauses holeLists with
              | none =>
                  simp [collectClauseEvidence, hevidence, hrest] at hcollect
              | some rest =>
                  simp [collectClauseEvidence, hevidence, hrest] at hcollect
                  subst evidences
                  exact .cons hevidence (ih hrest)

/-! ### Executable primitive-pattern capability alignment -/

mutual

/-- Structural equality for partial capability evidence. -/
def evidenceEq : Shape.Evidence -> Shape.Evidence -> Bool
  | .unseen, .unseen => true
  | .known left, .known right => decide (left = right)
  | .con leftName leftChildren, .con rightName rightChildren =>
      decide (leftName = rightName) && evidenceListEq leftChildren rightChildren
  | .prod left, .prod right => evidenceListEq left right
  | _, _ => false

/-- Structural equality for evidence lists. -/
def evidenceListEq : List Shape.Evidence -> List Shape.Evidence -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      evidenceEq left right && evidenceListEq lefts rights
  | _, _ => false

end

mutual

theorem evidenceEq_eq_true : ∀ left right,
    evidenceEq left right = true <-> left = right
  | .unseen, right => by cases right <;> simp [evidenceEq]
  | .known leaf, right => by cases right <;> simp [evidenceEq]
  | .con name children, right => by
      cases right <;> simp [evidenceEq, evidenceListEq_eq_true]
  | .prod components, right => by
      cases right <;> simp [evidenceEq, evidenceListEq_eq_true]

theorem evidenceListEq_eq_true : ∀ left right,
    evidenceListEq left right = true <-> left = right
  | [], right => by cases right <;> simp [evidenceListEq]
  | left :: lefts, right => by
      cases right <;>
        simp [evidenceListEq, evidenceEq_eq_true, evidenceListEq_eq_true]

end

/-- Number of primitive holes in source order. -/
def PPat.holeCount : PPat -> Nat
  | .hole => 1
  | .wild | .pval _ => 0
  | .ctor _ patterns | .tuple patterns =>
      patterns.foldl (fun count pattern => count + pattern.holeCount) 0

/-- Finite lists of a fixed length drawn from a finite candidate set.  The
alignment checker is intentionally conservative; every returned candidate is
validated again by the exact declarative equations. -/
def capChoices (candidates : List Cap) : Nat -> List (List Cap)
  | 0 => [[]]
  | count + 1 =>
      candidates.flatMap fun capability =>
        (capChoices candidates count).map fun rest => capability :: rest

/-- Executable form of constructor capability compatibility. -/
def capCompatibleCheck
    {observable : Shape.Observability}
    (entry : PatternCtorScheme observable) (children : List Cap)
    (outer : Cap) : Bool :=
  match Projection.projectSignature entry.projection
      (children.map Shape.ofCap) with
  | none => false
  | some projected =>
      match Shape.merge projected (Shape.ofCap outer) with
      | some merged => evidenceEq merged (Shape.ofCap outer)
      | none => false

theorem capCompatibleCheck_sound
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable} {children : List Cap}
    {outer : Cap} (checked : capCompatibleCheck entry children outer = true) :
    entry.CapCompatible children outer := by
  unfold capCompatibleCheck at checked
  split at checked
  · contradiction
  · rename_i projected projectedEq
    split at checked
    · rename_i merged mergedEq
      have mergeResult : merged = Shape.ofCap outer :=
        (evidenceEq_eq_true _ _).mp checked
      subst merged
      exact ⟨projected, projectedEq, mergedEq⟩
    · contradiction

/-- Declarative constructor compatibility is also sufficient for the
executable compatibility check. -/
theorem capCompatibleCheck_complete
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable} {children : List Cap}
    {outer : Cap} (compatible : entry.CapCompatible children outer) :
    capCompatibleCheck entry children outer = true := by
  rcases compatible with ⟨projected, projectedEq, mergedEq⟩
  simp [capCompatibleCheck, projectedEq, mergedEq, evidenceEq_eq_true]

mutual

/-- Executable check of the exact `PPatCapsAt` judgment.  Constructor child
capabilities are searched only in the finite set consisting of the outer
capability, its flexible leaves, the concrete hole capabilities, and `Any`.
Including the outer leaves is necessary for specialized clauses such as
`#$val :: $`: with outer capability `List κ`, its value-pattern child uses
`κ` while its hole child uses `List κ`.  Every candidate tuple is rechecked
by `CapCompatible`, so extending this search set does not weaken soundness. -/
def ppatCapsAtCheck
    (signature : FrozenSig) (atRoot : Bool) :
    PPat -> List Cap -> Cap -> Bool
  | .hole, holes, outer =>
      match atRoot, holes with
      | true, [_] => true
      | false, [hole] => decide (hole = outer)
      | _, _ => false
  | .wild, holes, _ | .pval _, holes, _ => decide (holes = [])
  | .ctor name patterns, holes, outer =>
      match signature.findPatternCtor name with
      | none => false
      | some entry =>
          let candidates :=
            outer :: Cap.any :: (holes ++ outer.fcv.map Cap.var)
          (capChoices candidates patterns.length).any fun children =>
            ppatCapsListCheck signature patterns holes children &&
            capCompatibleCheck entry children outer
  | .tuple patterns, holes, outer =>
      match outer with
      | .prod children => ppatCapsListCheck signature patterns holes children
      | _ => false

/-- Left-to-right executable list alignment.  The syntactic hole count gives
the unique split of the flattened hole ledger for each child. -/
def ppatCapsListCheck
    (signature : FrozenSig) : List PPat -> List Cap -> List Cap -> Bool
  | [], holes, children => decide (holes = []) && decide (children = [])
  | pattern :: patterns, holes, child :: children =>
      let count := pattern.holeCount
      ppatCapsAtCheck signature false pattern (holes.take count) child &&
        ppatCapsListCheck signature patterns (holes.drop count) children
  | _ :: _, _, [] => false

end

mutual

/-- Soundness of the finite primitive-pattern capability audit. -/
theorem ppatCapsAtCheck_sound
    (signature : FrozenSig) :
    ∀ atRoot pattern holes outer,
      ppatCapsAtCheck signature atRoot pattern holes outer = true ->
      PPatCapsAt signature atRoot pattern holes outer
  | false, .hole, holes, outer, checked => by
      cases holes with
      | nil => simp [ppatCapsAtCheck] at checked
      | cons hole rest =>
          cases rest with
          | cons another more => simp [ppatCapsAtCheck] at checked
          | nil =>
              have equality : hole = outer := by
                exact of_decide_eq_true (by
                  simpa [ppatCapsAtCheck] using checked)
              subst outer
              exact .childHole
  | true, .hole, holes, outer, checked => by
      cases holes with
      | nil => simp [ppatCapsAtCheck] at checked
      | cons hole rest =>
          cases rest with
          | cons another more => simp [ppatCapsAtCheck] at checked
          | nil => exact .rootHole
  | atRoot, .wild, holes, outer, checked => by
      have empty : holes = [] := by
        exact of_decide_eq_true (by simpa [ppatCapsAtCheck] using checked)
      subst holes
      exact .wild
  | atRoot, .pval name, holes, outer, checked => by
      have empty : holes = [] := by
        exact of_decide_eq_true (by simpa [ppatCapsAtCheck] using checked)
      subst holes
      exact .pval
  | atRoot, .ctor name patterns, holes, outer, checked => by
      simp only [ppatCapsAtCheck] at checked
      split at checked
      · contradiction
      · rename_i entry lookup
        rcases List.any_eq_true.mp checked with
          ⟨children, _, childrenChecked⟩
        rw [Bool.and_eq_true] at childrenChecked
        rcases childrenChecked with ⟨aligned, compatible⟩
        exact .ctor lookup
          (ppatCapsListCheck_sound signature patterns holes children aligned)
          (capCompatibleCheck_sound compatible)
  | atRoot, .tuple patterns, holes, outer, checked => by
      cases outer <;> try simp [ppatCapsAtCheck] at checked
      case prod children =>
        exact .tuple
          (ppatCapsListCheck_sound signature patterns holes children checked)

/-- Soundness of the exact-length list audit. -/
theorem ppatCapsListCheck_sound
    (signature : FrozenSig) :
    ∀ patterns holes children,
      ppatCapsListCheck signature patterns holes children = true ->
      PPatCapsList signature patterns holes children
  | [], holes, children, checked => by
      simp only [ppatCapsListCheck, Bool.and_eq_true,
        decide_eq_true_eq] at checked
      rcases checked with ⟨emptyHoles, emptyChildren⟩
      subst holes
      subst children
      exact .nil
  | pattern :: patterns, holes, child :: children, checked => by
      simp only [ppatCapsListCheck, Bool.and_eq_true] at checked
      rcases checked with ⟨headChecked, tailChecked⟩
      have head := ppatCapsAtCheck_sound signature false pattern
        (holes.take pattern.holeCount) child headChecked
      have tail := ppatCapsListCheck_sound signature patterns
        (holes.drop pattern.holeCount) children tailChecked
      simpa only [List.take_append_drop] using PPatCapsList.cons head tail
  | _ :: _, _, [], checked => by simp [ppatCapsListCheck] at checked

end

/-- Exact source-order alignment of every clause with its finalized hole
capabilities and the one matcher capability. -/
inductive ClauseCapsList (signature : FrozenSig) :
    List Clause -> List (List Cap) -> Cap -> Prop where
  | nil : ClauseCapsList signature [] [] capability
  | cons {clause clauses holes holeLists capability} :
      PPatCapsAt signature true clause.pp holes capability ->
      ClauseCapsList signature clauses holeLists capability ->
      ClauseCapsList signature (clause :: clauses) (holes :: holeLists)
        capability

/-- Execute final primitive-pattern capability alignment for every clause. -/
def clauseCapsListCheck
    (signature : FrozenSig) (capability : Cap) :
    List Clause -> List (List Cap) -> Bool
  | [], [] => true
  | clause :: clauses, holes :: holeLists =>
      ppatCapsAtCheck signature true clause.pp holes capability &&
        clauseCapsListCheck signature capability clauses holeLists
  | _, _ => false

theorem clauseCapsListCheck_sound
    {signature : FrozenSig} {capability : Cap}
    {clauses : List Clause} {holeLists : List (List Cap)}
    (checked : clauseCapsListCheck signature capability clauses holeLists = true) :
    ClauseCapsList signature clauses holeLists capability := by
  induction clauses generalizing holeLists with
  | nil =>
      cases holeLists <;> simp [clauseCapsListCheck] at checked
      exact .nil
  | cons clause clauses induction =>
      cases holeLists with
      | nil => simp [clauseCapsListCheck] at checked
      | cons holes holeLists =>
          simp only [clauseCapsListCheck, Bool.and_eq_true] at checked
          exact .cons (ppatCapsAtCheck_sound _ _ _ _ _ checked.1)
            (induction checked.2)

/-- Concrete validity of one allowed known-evidence origin. -/
def KnownOrigin.Valid
    (signature : FrozenMatcherSig) (trace : InferTrace)
    (evidence : Shape.Evidence) : KnownOrigin -> Prop
  | .actualClause clause holes =>
      clauseEvidence signature clause.pp holes = some evidence
  | .finalizedLiteral clauses holeLists evidences capability =>
      ClauseEvidenceList signature clauses holeLists evidences /\
      Shape.inferShape signature.observability evidences = some capability /\
      coverageCheck signature clauses capability = true /\
      evidence = Shape.ofCap capability
  | .externalFlow tag =>
      TraceEvent.capabilityFlow tag evidence ∈ trace.events

/-- Every retained source must have concrete provenance in the same trace. -/
def ProducerSource.Valid
    (signature : FrozenMatcherSig) (trace : InferTrace) :
    ProducerSource -> Prop
  | .known evidence origin => origin.Valid signature trace evidence
  | .selfReference binder placeholder path =>
      TraceEvent.directSelfReference binder placeholder path ∈ trace.events

/-- Erase provenance only at the already-verified recursion-kernel boundary. -/
def ProducerSource.toRecursion : ProducerSource -> Recursion.Source
  | .known evidence _ => .known evidence
  | .selfReference binder _ _ => .reference binder

/-- The complete named provenance obligation for one inference state. -/
def SourceProvenanceConditions
    (signature : FrozenMatcherSig) (state : InferState) : Prop :=
  forall source,
    source ∈ state.sources -> source.Valid signature state.trace

/-- Check and record one actual-clause evidence source. -/
def recordActualClauseSource
    (signature : FrozenMatcherSig) (clause : Clause) (holes : List Cap)
    (state : InferState) : Option InferState :=
  match clauseEvidence signature clause.pp holes with
  | none => none
  | some evidence =>
      some <|
        (state.recordEvent (.actualClauseEvidence clause holes evidence)).recordSource
          (.known evidence (.actualClause clause holes))

/--
Finalize a prior literal only after actual evidence collection and mandatory
coverage both succeed, then retain it as a genuine known source.
-/
def recordFinalizedLiteralSource
    (signature : FrozenMatcherSig) (clauses : List Clause)
    (holeLists : List (List Cap)) (state : InferState) : Option InferState := do
  let evidences <- collectClauseEvidence signature clauses holeLists
  let capability <- Shape.inferShape signature.observability evidences
  if coverageCheck signature clauses capability then
    let source := ProducerSource.known (Shape.ofCap capability)
      (.finalizedLiteral clauses holeLists evidences capability)
    pure <|
      (state.recordEvent (.literalCoverage clauses capability)).recordSource
        source
  else
    none

/--
Record an externally typed, capability-visible flow claim.  The later named
trace bridge must justify the event; merely having a value in the context does
not emit this source.
-/
def recordExternalFlowSource
    (tag : FlowTag) (evidence : Shape.Evidence)
    (state : InferState) : InferState :=
  (state.recordEvent (.capabilityFlow tag evidence)).recordSource
    (.known evidence (.externalFlow tag))

theorem recordActualClauseSource_new_valid
    {signature : FrozenMatcherSig} {clause : Clause} {holes : List Cap}
    {state result : InferState}
    (hsuccess :
      recordActualClauseSource signature clause holes state = some result) :
    exists evidence,
      ProducerSource.known evidence (.actualClause clause holes) ∈
        result.sources /\
      (KnownOrigin.actualClause clause holes).Valid
        signature result.trace evidence := by
  unfold recordActualClauseSource at hsuccess
  split at hsuccess
  next => contradiction
  next evidence hevidence =>
    simp only [Option.some.injEq] at hsuccess
    subst result
    refine ⟨evidence, ?_, hevidence⟩
    simp [InferState.recordEvent, InferState.recordSource]

/-! ## Shared traversal state and direct-self provenance -/

/-- Active singleton-recursive binders and their unique monotype placeholders. -/
abbrev SelfEnv := List (String × Ty)

/-- Shadowing-aware lookup of an active recursive binder. -/
def SelfEnv.find? (environment : SelfEnv) (name : String) : Option Ty :=
  (List.find? (fun entry => entry.1 == name) environment).map Prod.snd

/-- Remove every recursive binder shadowed by one source binder. -/
def SelfEnv.erase (environment : SelfEnv) (name : String) : SelfEnv :=
  environment.filter fun entry => entry.1 != name

/-- Remove a finite left-to-right collection of shadowed names. -/
def SelfEnv.eraseMany : SelfEnv -> List String -> SelfEnv
  | environment, [] => environment
  | environment, name :: names =>
      eraseMany (environment.erase name) names

/-- Free capability variables in a context entry's top-level slot demand.
For an active recursive placeholder, that demand is the top-level slot in its
function domain.  Capabilities elsewhere in the scheme remain producer-owned. -/
def schemeMatcherDemandCapVars (scheme : Scheme) : List CapVar :=
  match scheme.body with
  | .slot capability _ => capability.fcv
  | .fn (.slot capability _) _ => capability.fcv
  | _ => []

/-- Capability variables supplied by matcher-slot demands in the surrounding
context at one substitution cut.  A recursive self placeholder is already in
that context, so no separate operational self environment is needed. -/
def borrowedMatcherCapVarsAt (prevailing : Subst) (context : Context) :
    List CapVar :=
  ((context.applySubst prevailing).flatMap fun
      (entry : String × Scheme) =>
      schemeMatcherDemandCapVars entry.2).eraseDups

/-- State-indexed executable form of `borrowedMatcherCapVarsAt`. -/
def borrowedMatcherCapVars (state : InferState) (context : Context) :
    List CapVar :=
  borrowedMatcherCapVarsAt state.prevailing context

@[simp] theorem SelfEnv.find?_cons_self
    (name : String) (placeholder : Ty) (environment : SelfEnv) :
    SelfEnv.find? ((name, placeholder) :: environment) name =
      some placeholder := by
  simp [SelfEnv.find?]

/-- Add one syntax-node visit to the chronological event trace. -/
def visit (state : InferState) (kind : NodeKind) (path : SyntaxPath) :
    InferState :=
  state.recordEvent (.visit kind path)

/-- Record a direct-self reference and its provenance source atomically. -/
def recordSelfReference
    (state : InferState) (binder : String) (placeholder : Ty)
    (path : SyntaxPath) : InferState :=
  (state.recordEvent (.directSelfReference binder placeholder path)).recordSource
    (.selfReference binder placeholder path)

/-- Recording a direct-self source is append-only in both chronological
ledgers. -/
theorem recordSelfReference_historyPrefix
    (state : InferState) (binder : String) (placeholder : Ty)
    (path : SyntaxPath) :
    state.HistoryPrefix (recordSelfReference state binder placeholder path) := by
  exact (state.historyPrefix_recordEvent _).trans
    (InferState.historyPrefix_recordSource _ _)

/-- The event/source pair emitted for a direct call justifies its own concrete
provenance; no separate traversal is needed. -/
theorem recordSelfReference_new_valid
    (signature : FrozenMatcherSig) (state : InferState)
    (binder : String) (placeholder : Ty) (path : SyntaxPath) :
    let result := recordSelfReference state binder placeholder path
    ProducerSource.selfReference binder placeholder path ∈ result.sources ∧
      (ProducerSource.selfReference binder placeholder path).Valid
        signature result.trace := by
  simp [recordSelfReference, ProducerSource.Valid, InferState.recordEvent,
    InferState.recordSource]

/-- A helper origin for fresh metas allocated at one source path. -/
def freshOrigin
    (phase : ConstraintPhase) (path : SyntaxPath) (label : String) :
    ConstraintOrigin :=
  ⟨phase, path, label⟩

/-! A positive structural fuel bound for primitive-pattern traversal. -/
mutual
def ppatTraversalFuel : PPat -> Nat
  | .hole => 1
  | .wild => 1
  | .pval _ => 1
  | .ctor _ patterns => 1 + ppatListTraversalFuel patterns
  | .tuple patterns => 1 + ppatListTraversalFuel patterns

def ppatListTraversalFuel : List PPat -> Nat
  | [] => 1
  | pattern :: patterns =>
      1 + ppatTraversalFuel pattern + ppatListTraversalFuel patterns
end

/-! A positive structural fuel bound for primitive-data-pattern traversal. -/
mutual
def dpatTraversalFuel : DPat -> Nat
  | .var _ => 1
  | .wild => 1
  | .ctor _ patterns => 1 + dpatListTraversalFuel patterns
  | .tuple patterns => 1 + dpatListTraversalFuel patterns

def dpatListTraversalFuel : List DPat -> Nat
  | [] => 1
  | pattern :: patterns =>
      1 + dpatTraversalFuel pattern + dpatListTraversalFuel patterns
end

/-!
One structural bound for the mutually recursive expression/pattern/clause
syntax.  It is intentionally generous: fuel is consumed along a call chain,
while this measure sums every child and sibling.
-/
mutual

def exprTraversalFuel : Expr -> Nat
  | .var _ => 1
  | .lam _ body => 1 + exprTraversalFuel body
  | .fix _ _ body => 1 + exprTraversalFuel body
  | .app function argument =>
      1 + exprTraversalFuel function + exprTraversalFuel argument
  | .lit _ => 1
  | .tuple expressions => 1 + exprListTraversalFuel expressions
  | .ctor _ expressions => 1 + exprListTraversalFuel expressions
  | .prim _ expressions => 1 + exprListTraversalFuel expressions
  | .letE _ value body =>
      1 + exprTraversalFuel value + exprTraversalFuel body
  | .something => 1
  | .matcher clauses => 1 + clauseListTraversalFuel clauses
  | .matchAll target matcher pattern body =>
      1 + exprTraversalFuel target + exprTraversalFuel matcher +
        patternTraversalFuel pattern + exprTraversalFuel body

def exprListTraversalFuel : List Expr -> Nat
  | [] => 1
  | expression :: expressions =>
      1 + exprTraversalFuel expression + exprListTraversalFuel expressions

def patternTraversalFuel : Pattern -> Nat
  | .pvar _ => 1
  | .wild => 1
  | .pval expression => 1 + exprTraversalFuel expression
  | .embed _ => 1
  | .pctor _ patterns => 1 + patternListTraversalFuel patterns
  | .pand left right =>
      1 + patternTraversalFuel left + patternTraversalFuel right
  | .por left right =>
      1 + patternTraversalFuel left + patternTraversalFuel right
  | .papp _ patterns => 1 + patternListTraversalFuel patterns
  | .ptuple patterns => 1 + patternListTraversalFuel patterns

def patternListTraversalFuel : List Pattern -> Nat
  | [] => 1
  | pattern :: patterns =>
      1 + patternTraversalFuel pattern + patternListTraversalFuel patterns

def armTraversalFuel : Arm -> Nat
  | .mk dataPattern body =>
      1 + dpatTraversalFuel dataPattern + exprTraversalFuel body

def armListTraversalFuel : List Arm -> Nat
  | [] => 1
  | arm :: arms => 1 + armTraversalFuel arm + armListTraversalFuel arms

def clauseTraversalFuel : Clause -> Nat
  | .mk primitivePattern next arms =>
      1 + ppatTraversalFuel primitivePattern + exprTraversalFuel next +
        armListTraversalFuel arms

def clauseListTraversalFuel : List Clause -> Nat
  | [] => 1
  | clause :: clauses =>
      1 + clauseTraversalFuel clause + clauseListTraversalFuel clauses

end

/-! ## Executable Algorithm W -/

/-- Fresh lower bounds above every variable already reserved by input data. -/
def initialSupply (signature : FrozenSig) (context : Context) :
    InferenceBase.FreshSupply :=
  { nextCap := InferenceBase.binderSpan
      ((signature.capVars ++ context.allCapVars).map CapVar.id)
    nextTy := InferenceBase.binderSpan
      (signature.tyVars ++ context.allTyVars) }

/-- The initial capability counter is automatically above the complete source
scope; callers of the reconstruction bridge do not need to assume this. -/
theorem initialSupply_capVarsBelow
    (signature : FrozenSig) (context : Context) :
    InferenceBase.CapVarsBelow (initialSupply signature context)
      (SourceCapScope signature context) := by
  intro varId membership
  have allMembership :
      varId ∈ signature.capVars ++ context.allCapVars := by
    simp only [SourceCapScope, FrozenSig.fcv, FrozenSig.capVars,
      Context.fcv, Context.allCapVars, List.mem_append,
      List.mem_flatMap] at membership ⊢
    rcases membership with signatureMembership | contextMembership
    · left
      rcases signatureMembership with
        ((dataMembership | patternCtorMembership) |
          patternFunMembership) | primitiveMembership
      · rcases dataMembership with ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember,
          CtorScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩))
      · rcases patternCtorMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inl (Or.inr ⟨entry, entryMember,
          CtorScheme.mem_capVars_of_mem_fcv entry.2.scheme variableMember⟩))
      · rcases patternFunMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inr ⟨entry, entryMember,
          DualScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩)
      · rcases primitiveMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inr ⟨entry, entryMember,
          CtorScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩
    · right
      rcases contextMembership with ⟨entry, entryMember, variableMember⟩
      exact ⟨entry, entryMember, variableMember⟩
  simpa only [initialSupply] using
    InferenceBase.mem_lt_binderSpan
      (List.mem_map.mpr ⟨varId, allMembership, rfl⟩)

/-- The initial target counter is automatically above the complete source
scope; callers of the reconstruction bridge do not need to assume this. -/
theorem initialSupply_tyVarsBelow
    (signature : FrozenSig) (context : Context) :
    InferenceBase.TyVarsBelow (initialSupply signature context)
      (SourceTyScope signature context) := by
  intro varId membership
  have allMembership :
      varId ∈ signature.tyVars ++ context.allTyVars := by
    simp only [SourceTyScope, FrozenSig.ftv, FrozenSig.tyVars,
      Context.ftv, Context.allTyVars, List.mem_append,
      List.mem_flatMap] at membership ⊢
    rcases membership with signatureMembership | contextMembership
    · left
      rcases signatureMembership with
        ((dataMembership | patternCtorMembership) |
          patternFunMembership) | primitiveMembership
      · rcases dataMembership with ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember,
          CtorScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩))
      · rcases patternCtorMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inl (Or.inr ⟨entry, entryMember,
          CtorScheme.mem_tyVars_of_mem_ftv entry.2.scheme variableMember⟩))
      · rcases patternFunMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inl (Or.inr ⟨entry, entryMember,
          DualScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩)
      · rcases primitiveMembership with
          ⟨entry, entryMember, variableMember⟩
        exact Or.inr ⟨entry, entryMember,
          CtorScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩
    · right
      rcases contextMembership with ⟨entry, entryMember, variableMember⟩
      exact ⟨entry, entryMember, variableMember⟩
  simpa only [initialSupply] using
    InferenceBase.mem_lt_binderSpan allMembership

/-- Initial W state for one frozen signature and source context. -/
def initialState (signature : FrozenSig) (context : Context) : InferState :=
  InferState.empty (initialSupply signature context)

structure ExprResult where
  target : Ty
  state : InferState

structure ExprsResult where
  targets : List Ty
  state : InferState

structure PatternResult where
  dual : Dual
  bindings : MonoCtx
  state : InferState

structure PatternsResult where
  duals : List Dual
  bindings : MonoCtx
  state : InferState

structure PPatResult where
  target : Ty
  holes : List Dual
  bindings : MonoCtx
  state : InferState

structure PPatsResult where
  targets : List Ty
  holes : List Dual
  bindings : MonoCtx
  state : InferState

structure DPatResult where
  target : Ty
  bindings : MonoCtx
  state : InferState

structure DPatsResult where
  targets : List Ty
  bindings : MonoCtx
  state : InferState

structure ClauseResult where
  target : Ty
  rawHoles : List Dual
  state : InferState

structure ClausesResult where
  target : Ty
  rawHoleLists : List (List Dual)
  state : InferState

/-- Resolve one inferred type at the complete trace prefix. -/
def ExprResult.resolvedTarget (result : ExprResult) : Ty :=
  result.state.prevailing.apply result.target

/-- Append an inferred-expression event. -/
def finishExpr
    (expression : Expr) (path : SyntaxPath)
    (target : Ty) (state : InferState) : ExprResult :=
  ⟨target, state.recordEvent (.inferredExpr expression target path)⟩

/-- Run a constraint that its caller has already occurrence-wide resolved. -/
def runResolvedConstraint
    (state : InferState) (origin : ConstraintOrigin)
    (constraint : Constraint) : Option InferState := do
  let step <- solveResolvedWithLedger state.capabilityOrigins
    state.trace.solves.length origin constraint
  match constraint with
  | .producerToSlot _ _ _ _ =>
      if capSubstSafeVarsCheck state.capabilityOrigins step.delta.cap
          state.protectedCaps then
        pure (state.recordSolve step)
      else
        none
  | _ => pure (state.recordSolve step)

/--
Align full types, solving matcher/slot capabilities in their own sort before
running the protected target solver.
-/
def alignTypesCore
    (state : InferState) (origin : ConstraintOrigin)
    (left right : Ty) : Option InferState := do
  let resolvedLeft := state.prevailing.apply left
  let resolvedRight := state.prevailing.apply right
  match resolvedLeft, resolvedRight with
  | .matcher leftCap _leftTarget, .matcher rightCap _rightTarget
  | .slot leftCap _leftTarget, .slot rightCap _rightTarget =>
      let state <- runResolvedConstraint state origin
        (.capEq leftCap rightCap)
      let afterLeft := state.prevailing.apply left
      let afterRight := state.prevailing.apply right
      match afterLeft, afterRight with
      | .matcher _ leftTarget, .matcher _ rightTarget
      | .slot _ leftTarget, .slot _ rightTarget =>
          runResolvedConstraint state origin (.targetEq leftTarget rightTarget)
      | _, _ => none
  | _, _ =>
      runResolvedConstraint state origin (.targetEq resolvedLeft resolvedRight)

/-- Record one complete ordinary equality alignment around its solver core. -/
def alignTypes
    (state : InferState) (origin : ConstraintOrigin)
    (left right : Ty) : Option InferState := do
  let startSolve := state.trace.solves.length
  let resolvedLeft := state.prevailing.apply left
  let resolvedRight := state.prevailing.apply right
  let aligned <- alignTypesCore state origin left right
  pure (aligned.recordEvent (.typeAlignment startSolve
    aligned.trace.solves.length left right resolvedLeft resolvedRight))

/-- Producer-stable checking at a slot use site. -/
def alignAtSlot
    (state : InferState) (origin : ConstraintOrigin)
    (inferred expected : Ty) : Option InferState := do
  let resolvedInferred := state.prevailing.apply inferred
  let resolvedExpected := state.prevailing.apply expected
  match resolvedInferred, resolvedExpected with
  | .matcher producerCap producerTarget, .slot consumerCap consumerTarget =>
      runResolvedConstraint state origin
        (.producerToSlot producerCap producerTarget consumerCap consumerTarget)
  | .slot sourceCap _sourceTarget, .slot requestedCap _requestedTarget =>
      let state <- runResolvedConstraint state origin
        (.capEq sourceCap requestedCap)
      let afterSource := state.prevailing.apply inferred
      let afterRequested := state.prevailing.apply expected
      match afterSource, afterRequested with
      | .slot _ sourceTarget, .slot _ requestedTarget =>
          runResolvedConstraint state origin
            (.targetEq sourceTarget requestedTarget)
      | _, _ => none
  | _, _ => alignTypes state origin inferred expected

/-! ### Explicit product-matcher use-site coercion -/

/-- View a matcher type as the dual carried by that matcher. -/
def matcherDual? : Ty -> Option Dual
  | .matcher capability target => some ⟨capability, target⟩
  | _ => none

/-- Recognize a product whose every component is a matcher. -/
def productMatcherDuals? : Ty -> Option (List Dual)
  | .prod targets => targets.mapM matcherDual?
  | _ => none

/-- A successful product-matcher view recovers the exact raw product type. -/
theorem productMatcherDuals?_sound
    {target : Ty} {duals : List Dual}
    (success : productMatcherDuals? target = some duals) :
    target = .prod (duals.map fun dual =>
      .matcher dual.cap dual.target) := by
  cases target <;> try simp [productMatcherDuals?] at success
  case prod targets =>
    congr 1
    induction targets generalizing duals with
    | nil => simpa [productMatcherDuals?] using success
    | cons head tail induction =>
        simp only [List.mapM_cons] at success
        cases head <;> try simp [matcherDual?] at success
        case matcher capability componentTarget =>
          cases tailView : List.mapM matcherDual? tail with
          | none => simp [tailView] at success
          | some tailDuals =>
              simp [tailView] at success
              subst duals
              simp only [List.map_cons, List.cons.injEq, true_and]
              exact induction tailView

/-- Read one slot component as the dual carried by that slot. -/
def slotDual? : Ty -> Option Dual
  | .slot capability target => some ⟨capability, target⟩
  | _ => none

/-- Recognize a product whose every component is already a slot. -/
def productSlotDuals? : Ty -> Option (List Dual)
  | .prod targets => targets.mapM slotDual?
  | _ => none

/-- A successful product-slot view recovers the exact raw product type. -/
theorem productSlotDuals?_sound
    {target : Ty} {duals : List Dual}
    (success : productSlotDuals? target = some duals) :
    target = .prod (duals.map fun dual =>
      .slot dual.cap dual.target) := by
  cases target <;> try simp [productSlotDuals?] at success
  case prod targets =>
    congr 1
    induction targets generalizing duals with
    | nil => simpa [productSlotDuals?] using success
    | cons head tail induction =>
        simp only [List.mapM_cons] at success
        cases head <;> try simp [slotDual?] at success
        case slot capability componentTarget =>
          cases tailView : List.mapM slotDual? tail with
          | none => simp [tailView] at success
          | some tailDuals =>
              simp [tailView] at success
              subst duals
              simp only [List.map_cons, List.cons.injEq, true_and]
              exact induction tailView

/-- Build the unary product-matcher coercion target for raw component duals. -/
def productMatcherTarget (duals : List Dual) : Ty :=
  .matcher (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))

/-- Build the unary slot-tuple coercion target for raw component duals. -/
def slotTupleTarget (duals : List Dual) : Ty :=
  .slot (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))

/-- Executable branch selected at one expected-type cut.  Product recognition
uses exactly the same cut-resolved source view as `DemandTyping.demandClass`.
The selected duals are local views, never raw reconstruction indices. -/
inductive ExpectedCoercionPlan where
  | productMatcherLift (duals : List Dual)
  | slotTupleLift (duals : List Dual)
  | raw
deriving Repr, DecidableEq

/-- Select a use-site coercion from the two cut-resolved views.  Matcher-product
lifting has precedence for the empty product, mirroring `demandClass`. -/
def expectedCoercionPlan
    (state : InferState) (inferred expected : Ty) : ExpectedCoercionPlan :=
  match productMatcherDuals? (state.prevailing.apply inferred),
      productSlotDuals? (state.prevailing.apply inferred),
      state.prevailing.apply expected with
  | some duals, _, .slot _ _ => .productMatcherLift duals
  | _, some duals, .slot _ _ => .slotTupleLift duals
  | _, _, _ => .raw

/-- The slot-demand principle in theorem form: whenever the selector presents
anything other than the raw synthesized type, the substituted expected type
already exposes a slot head at this cut. -/
theorem expectedCoercionPlan_slotDemand
    (state : InferState) (inferred expected : Ty)
    (changed : expectedCoercionPlan state inferred expected ≠ .raw) :
    ∃ consumerCap consumerTarget,
      state.prevailing.apply expected = .slot consumerCap consumerTarget := by
  unfold expectedCoercionPlan at changed
  split at changed
  all_goals first
    | exact absurd rfl changed
    | exact ⟨_, _, by assumption⟩

/-- A matcher-headed expectation is not a coercion demand: the selector
leaves the synthesized type untouched, so only the ordinary alignment of a
raw matcher can succeed at such a use site. -/
theorem expectedCoercionPlan_matcherExpected
    (state : InferState) (inferred expected : Ty)
    {consumerCap : Cap} {consumerTarget : Ty}
    (matcherExpected :
      state.prevailing.apply expected = .matcher consumerCap consumerTarget) :
    expectedCoercionPlan state inferred expected = .raw := by
  unfold expectedCoercionPlan
  split <;> simp_all

/-- An unresolved expected target variable leaves the synthesized type raw.
The selector does not guess a matcher-slot head before an earlier
chronological constraint has exposed one. -/
theorem expectedCoercionPlan_variableExpected
    (state : InferState) (inferred expected : Ty) {varId : TyVar}
    (variableExpected : state.prevailing.apply expected = .var varId) :
    expectedCoercionPlan state inferred expected = .raw := by
  unfold expectedCoercionPlan
  split <;> simp_all

/-- Execute the product-matcher branch on the already resolved component
duals.  No prevailing substitution is applied to these local views again. -/
def alignResolvedProductMatcherAtSlot
    (state : InferState) (origin : ConstraintOrigin) (duals : List Dual)
    (consumerCap : Cap) (consumerTarget : Ty) : Option InferState :=
  runResolvedConstraint state origin
    (.producerToSlot (.prod (duals.map Dual.cap))
      (.prod (duals.map Dual.target)) consumerCap consumerTarget)

/-- Execute the slot-tuple branch on already resolved component duals.  The
capability delta, rather than the full prevailing substitution, is applied to
the local targets before the second solve. -/
def alignResolvedSlotTupleAtSlot
    (state : InferState) (origin : ConstraintOrigin) (duals : List Dual)
    (consumerCap : Cap) (consumerTarget : Ty) : Option InferState := do
  let step <- solveResolvedWithLedger state.capabilityOrigins
    state.trace.solves.length origin
    (.capEq (.prod (duals.map Dual.cap)) consumerCap)
  let middle := state.recordSolve step
  runResolvedConstraint middle origin
    (.targetEq (step.delta.apply (.prod (duals.map Dual.target)))
      (step.delta.apply consumerTarget))

/--
Align an already-synthesized expression result with an expected type and
record the complete slot-alignment event.  Keeping this non-recursive boundary
shared lets ordinary checking and domain-directed application use exactly the
same coercion selection without changing the mutual recursion graph.
-/
def alignExprResultAtExpected
    (path : SyntaxPath) (result : ExprResult) (expected : Ty) :
    Option InferState :=
  let resolvedInferred := result.state.prevailing.apply result.target
  let requested := result.state.prevailing.apply expected
  let plan := expectedCoercionPlan result.state result.target expected
  let inferred := match plan with
    | .productMatcherLift duals => productMatcherTarget duals
    | .slotTupleLift duals => slotTupleTarget duals
    | .raw => resolvedInferred
  let aligned := match plan, requested with
    | .productMatcherLift duals, .slot consumerCap consumerTarget =>
        alignResolvedProductMatcherAtSlot result.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget
    | .slotTupleLift duals, .slot consumerCap consumerTarget =>
        alignResolvedSlotTupleAtSlot result.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget
    | .raw, _ => alignAtSlot result.state
        (freshOrigin .expression path "expected-type") result.target expected
    | _, _ => none
  match aligned with
  | none => none
  | some aligned =>
      some (aligned.recordEvent (.slotAlignment
        result.state.trace.solves.length aligned.trace.solves.length
        inferred requested))

/-- Fresh capability images allocated for a binder batch. -/
def freshCapImages
    (supply : InferenceBase.FreshSupply) (binders : List CapVar) :
    List CapVar :=
  binders.map fun binder => ⟨supply.nextCap + binder.id⟩

/-- Fresh ordinary-type images allocated for a binder batch. -/
def freshTyImages
    (supply : InferenceBase.FreshSupply)
    (binders : List TypePM.TyVar) : List TypePM.TyVar :=
  binders.map fun binder => supply.nextTy + binder

/-- The same executable binder batch supplies the algorithmic `FreshInstAt`
allocation witness for a pattern-function scheme. -/
theorem instantiateDualScheme_freshInstAt
    (supply : InferenceBase.FreshSupply) (scheme : DualScheme)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (capNodup : scheme.capBinders.Nodup)
    (tyNodup : scheme.tyBinders.Nodup)
    (capBelow : InferenceBase.CapVarsBelow supply reservedCaps)
    (tyBelow : InferenceBase.TyVarsBelow supply reservedTys) :
    scheme.FreshInstAt reservedCaps reservedTys
      (InferenceBase.instantiateDualScheme supply scheme).subst.cap
      (InferenceBase.instantiateDualScheme supply scheme).subst.target
      (freshCapImages supply scheme.capBinders)
      (freshTyImages supply scheme.tyBinders)
      (InferenceBase.instantiateDualScheme supply scheme).value.1
      (InferenceBase.instantiateDualScheme supply scheme).value.2 := by
  have capFresh := InferenceBase.instantiateBinders_cap_fresh supply
    scheme.capBinders scheme.tyBinders reservedCaps capNodup capBelow
  have tyFresh := InferenceBase.instantiateBinders_ty_fresh supply
    scheme.capBinders scheme.tyBinders reservedTys tyNodup tyBelow
  refine ⟨InferenceBase.instantiateBinders_cap_support supply
      scheme.capBinders scheme.tyBinders,
    InferenceBase.instantiateBinders_ty_support supply
      scheme.capBinders scheme.tyBinders, ?_, ?_, ?_, ?_, ?_, ?_,
    InferenceBase.instantiateBinders_rangeFixed supply
      scheme.capBinders scheme.tyBinders, rfl, rfl⟩
  · simp only [freshCapImages, List.map_map]
    apply List.map_congr_left
    intro binder membership
    simp [InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
      membership]
  · simp only [freshTyImages, List.map_map]
    apply List.map_congr_left
    intro binder membership
    simp [InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders, InferenceBase.freshTySubst,
      membership]
  · unfold freshCapImages
    apply List.Pairwise.map _ ?_ capNodup
    intro left right distinct equality
    apply distinct
    cases left with
    | mk leftId =>
        cases right with
        | mk rightId =>
            have sameId : leftId = rightId :=
              Nat.add_left_cancel
                (congrArg (fun varId : CapVar => varId.id) equality)
            subst rightId
            rfl
  · unfold freshTyImages
    apply List.Pairwise.map _ ?_ tyNodup
    intro left right distinct equality
    exact distinct (Nat.add_left_cancel equality)
  · intro image imageMembership reservedMembership
    simp only [freshCapImages] at imageMembership
    rcases List.mem_map.mp imageMembership with ⟨binder, _, rfl⟩
    apply (capFresh.2 binder (by assumption)
      ⟨supply.nextCap + binder.id⟩ reservedMembership)
    simp [InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
      show binder ∈ scheme.capBinders by assumption]
  · intro image imageMembership reservedMembership
    simp only [freshTyImages] at imageMembership
    rcases List.mem_map.mp imageMembership with ⟨binder, _, rfl⟩
    apply (tyFresh.2 binder (by assumption)
      (supply.nextTy + binder) reservedMembership)
    simp [InferenceBase.instantiateBinders, InferenceBase.freshTySubst,
      show binder ∈ scheme.tyBinders by assumption]

/--
Instantiate a context scheme, protect its fresh capability images against
later structural strengthening, and retain the instance in the trace.
-/
def instantiateSchemeInState
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) : Ty × InferState :=
  let incomingSupply := state.supply
  let instantiation := InferenceBase.instantiateScheme incomingSupply scheme
  let protectedIds := Scheme.canonicalCapImages incomingSupply scheme
  let targetImages := Scheme.canonicalTyImages incomingSupply scheme
  let fixedCaps := SourceFixedCapScope signature normalizedContext
  let fixedTys := SourceFixedTyScope signature normalizedContext
  let reservedCaps := SourceCapScope signature normalizedContext
  let reservedTys := SourceTyScope signature normalizedContext
  let state :=
    { state with
      supply := instantiation.supply
      protectedCaps := state.protectedCaps ++ protectedIds
      capabilityOrigins := state.capabilityOrigins.setOrigins protectedIds
        .renameOnly }
  (instantiation.value,
    state.recordEvent (.schemeInstantiation state.trace.solves.length
      incomingSupply scheme name rawContext normalizedContext fixedCaps fixedTys
      reservedCaps reservedTys instantiation.value protectedIds targetImages))

/-- Instantiate a constructor/primitive scheme and advance both counters.
Capability images remain structurally flexible during the local argument or
pattern solve.  Their externally surviving prevailing-image leaves are frozen
by `freezeCapabilityExport` at the corresponding use boundary. -/
def instantiateCtorInState
    (state : InferState) (scheme : CtorScheme) :
    (List Ty × Ty) × InferState :=
  let incomingSupply := state.supply
  let instantiation := InferenceBase.instantiateCtorScheme incomingSupply scheme
  let protectedIds := freshCapImages incomingSupply scheme.capBinders
  let state :=
    { state with
      supply := instantiation.supply
      capabilityOrigins := state.capabilityOrigins.setOrigins protectedIds
        .structuralFlexible }
  (instantiation.value,
    state.recordEvent (.ctorInstantiation state.trace.solves.length incomingSupply
      scheme instantiation.value.1 instantiation.value.2 protectedIds))

/-- Encode the capability and target components of an exported result in one
type payload.  A matcher over `unit` carries each standalone capability
without adding target variables; the surrounding product then exposes exactly
the union of the capability-list and target-list free capability variables to
the ordinary `Ty.fcv` traversal. -/
def capabilityExportPayload
    (capabilities : List Cap) (targets : List Ty) : Ty :=
  .prod ((capabilities.map fun capability => .matcher capability .unit) ++
    targets)

/-- Variable leaves in the prevailing images of a constructor's fresh
capability binders that still occur in its exported payload.  Only leaves that
remain structurally flexible at this cut are selected: rigid external leaves
must never be downgraded, and already frozen leaves need no second event. -/
def capabilityExportLeaves
    (state : InferState) (capImages : List CapVar)
    (exportedPayload : Ty) : List CapVar :=
  let exportedVars := (state.prevailing.apply exportedPayload).fcv
  let imageLeaves := capImages.flatMap fun varId =>
    (state.prevailing.cap varId).fcv
  (imageLeaves.filter fun varId => varId ∈ exportedVars).eraseDups.filter
    fun varId =>
      state.capabilityOrigins.originOf varId == .structuralFlexible

/-- Freeze exactly the surviving structural leaves of one completed
constructor/primitive instance and record the solve cut that determined the
prevailing images. -/
def InferState.freezeCapabilityExport
    (state : InferState) (capImages : List CapVar)
    (exportedPayload : Ty) : InferState :=
  let leaves := capabilityExportLeaves state capImages exportedPayload
  let resolvedPayload := state.prevailing.apply exportedPayload
  let frozen :=
    { state with
      protectedCaps := state.protectedCaps ++ leaves
      capabilityOrigins := state.capabilityOrigins.setOrigins leaves
        .renameOnly }
  frozen.recordEvent (.capabilityExportFreeze state.trace.solves.length
    capImages exportedPayload resolvedPayload leaves)

@[simp] theorem InferState.freezeCapabilityExport_protectedCaps
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).protectedCaps =
      state.protectedCaps ++
        capabilityExportLeaves state capImages exportedPayload := by
  rfl

theorem InferState.freezeCapabilityExport_origin_of_mem
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty)
    (varId : CapVar)
    (membership :
      varId ∈ capabilityExportLeaves state capImages exportedPayload) :
    ((state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
        ).originOf varId = .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    state.capabilityOrigins
    (capabilityExportLeaves state capImages exportedPayload) varId
    .renameOnly membership

/-- Export freezing changes only the producer ledgers and appends its explicit
cut event, so all prior solver and event history is preserved. -/
theorem InferState.historyPrefix_freezeCapabilityExport
    (state : InferState) (capImages : List CapVar) (exportedPayload : Ty) :
    state.HistoryPrefix
      (state.freezeCapabilityExport capImages exportedPayload) := by
  refine ⟨[], [TraceEvent.capabilityExportFreeze
    state.trace.solves.length capImages exportedPayload
    (state.prevailing.apply exportedPayload)
    (capabilityExportLeaves state capImages exportedPayload)], ?_, ?_⟩
  · simp [InferState.freezeCapabilityExport, InferState.recordEvent]
  · simp [InferState.freezeCapabilityExport, InferState.recordEvent]

/-- Instantiate a dual scheme and advance both counters. -/
def instantiateDualInState
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (state : InferState) (scheme : DualScheme) :
    (List Dual × Dual) × InferState :=
  let incomingSupply := state.supply
  let instantiation := InferenceBase.instantiateDualScheme incomingSupply scheme
  let protectedIds := freshCapImages incomingSupply scheme.capBinders
  let targetImages := freshTyImages incomingSupply scheme.tyBinders
  let fixedCaps :=
    PatternFixedCapScope signature context parameters bindings
  let fixedTys :=
    PatternFixedTyScope signature context parameters bindings
  let reservedCaps :=
    PatternCapScope signature context parameters bindings
  let reservedTys :=
    PatternTyScope signature context parameters bindings
  let state :=
    { state with
      supply := instantiation.supply
      protectedCaps := state.protectedCaps ++ protectedIds
      capabilityOrigins := state.capabilityOrigins.setOrigins protectedIds
        .renameOnly }
  (instantiation.value,
    state.recordEvent (.dualInstantiation state.trace.solves.length incomingSupply
      scheme rawContext rawParameters rawBindings context parameters bindings
      fixedCaps fixedTys reservedCaps reservedTys instantiation.value.1
      instantiation.value.2 protectedIds targetImages))

/-- Executable duplicate check for source binder names. -/
def namesNodup : List String -> Bool
  | [] => true
  | name :: names => !names.contains name && namesNodup names

/-- Executable disjointness check for two source binder lists. -/
def namesDisjoint (left right : List String) : Bool :=
  left.all fun name => !right.contains name

/-- Syntactic final catch-all check used by W. -/
def catchAllLastCheck (clauses : List Clause) : Bool :=
  match clauses.reverse with
  | .mk .hole _ [.mk (.var _) _] :: earlierReversed =>
      earlierReversed.all fun clause =>
        match clause.pp with
        | .hole => false
        | _ => true
  | _ => false

/-- The syntactic checker returns the exact final bare-hole/variable-arm
decomposition required by the declarative matcher rule. -/
theorem catchAllLastCheck_sound
    {clauses : List Clause} (checked : catchAllLastCheck clauses = true) :
    CatchAllLast clauses := by
  unfold catchAllLastCheck at checked
  generalize reverseEquation : clauses.reverse = reversed at checked
  cases reversed with
  | nil => simp at checked
  | cons last earlierReversed =>
      cases last with
      | mk primitive next arms =>
          cases primitive <;> try simp at checked
          case hole =>
            cases arms with
            | nil => simp at checked
            | cons arm remainingArms =>
                cases arm with
                | mk pattern body =>
                    cases pattern <;> try simp at checked
                    case var name =>
                      cases remainingArms with
                      | cons another more => simp at checked
                      | nil =>
                          refine ⟨earlierReversed.reverse, next, name, body,
                            ?_, ?_⟩
                          · have restored :=
                              congrArg List.reverse reverseEquation
                            simpa [List.reverse_cons] using restored
                          · intro clause membership isHole
                            have reversedMembership :
                                clause ∈ earlierReversed := by
                              simpa using membership
                            have accepted :=
                              List.all_eq_true.mp checked clause
                                reversedMembership
                            cases clause with
                            | mk pp next arms =>
                                cases pp <;> simp_all

/-- Executable PP/arm binder hygiene required by T-MATCHER. -/
def matcherBindersCheck (clauses : List Clause) : Bool :=
  clauses.all fun clause =>
    namesNodup clause.pp.bindVars &&
    clause.arms.all fun arm =>
      namesNodup arm.pat.bindVars &&
      namesDisjoint arm.pat.bindVars clause.pp.bindVars

/-- The frozen deterministic arm exhaustiveness pass for every actual clause. -/
def armExhaustiveCheck
    (signature : FrozenSig) (clauses : List Clause) (target : Ty) : Bool :=
  clauses.all fun clause => signature.armExhaustive clause.armPatterns target

theorem namesNodup_eq_true (names : List String) :
    namesNodup names = true <-> names.Nodup := by
  induction names with
  | nil => simp [namesNodup]
  | cons name names induction =>
      simp [namesNodup, List.nodup_cons, induction]

theorem namesDisjoint_eq_true (left right : List String) :
    namesDisjoint left right = true <->
      ∀ name, name ∈ left -> name ∉ right := by
  simp [namesDisjoint, List.all_eq_true]

/-- A successful binder checker supplies both declarative hygiene predicates. -/
theorem matcherBindersCheck_sound
    {clauses : List Clause}
    (checked : matcherBindersCheck clauses = true) :
    PPBindNodup clauses ∧ ArmBindNodup clauses := by
  have each := List.all_eq_true.mp checked
  constructor
  · intro clause membership
    have clauseChecked := each clause membership
    simp only [Bool.and_eq_true] at clauseChecked
    exact (namesNodup_eq_true clause.pp.bindVars).mp
      clauseChecked.1
  · intro clause clauseMembership arm armMembership
    have clauseChecked := each clause clauseMembership
    simp only [Bool.and_eq_true] at clauseChecked
    have armsChecked := List.all_eq_true.mp
      clauseChecked.2 arm armMembership
    simp only [Bool.and_eq_true] at armsChecked
    exact ⟨(namesNodup_eq_true arm.pat.bindVars).mp armsChecked.1,
      (namesDisjoint_eq_true arm.pat.bindVars clause.pp.bindVars).mp
        armsChecked.2⟩

/-- The executable arm pass is definitionally the source-side predicate. -/
theorem armExhaustiveCheck_sound
    {signature : FrozenSig} {clauses : List Clause} {target : Ty}
    (checked : armExhaustiveCheck signature clauses target = true) :
    ArmExhaustive signature clauses target := by
  exact List.all_eq_true.mp checked

/-- Does a source body syntactically produce a matcher at its root? -/
def matcherProducingRoot : Expr -> Bool
  | .matcher _ => true
  | _ => false

/-! ### Source-driven recursive matcher templates -/

mutual

/--
Erase matcher-hole capabilities while retaining only the structural evidence
contributed by the primitive-pattern pattern itself.  This is deliberately
independent of next-matcher expressions and of every expected target.
-/
def ppatSkeletonEvidence
    (signature : FrozenMatcherSig) : PPat -> Option Shape.Evidence
  | .hole | .wild | .pval _ => some .unseen
  | .ctor name patterns => do
      let constructor <- signature.findPatternConstructor? name
      let children <- ppatSkeletonEvidenceList signature patterns
      Projection.projectSignature constructor children
  | .tuple patterns => do
      let children <- ppatSkeletonEvidenceList signature patterns
      pure (.prod children)

/-- List traversal for structural primitive-pattern evidence. -/
def ppatSkeletonEvidenceList
    (signature : FrozenMatcherSig) : List PPat -> Option (List Shape.Evidence)
  | [] => some []
  | pattern :: patterns => do
      let head <- ppatSkeletonEvidence signature pattern
      let tail <- ppatSkeletonEvidenceList signature patterns
      pure (head :: tail)

end


/-- Structural evidence of every actual matcher clause. -/
def matcherSkeletonEvidence
    (signature : FrozenMatcherSig) (clauses : List Clause) :
    Option Shape.Evidence := do
  let evidence <- clauses.mapM fun clause =>
    ppatSkeletonEvidence signature clause.pp
  Shape.mergeAll evidence

mutual

/--
Replace an observable, structurally unknown leaf in matcher-skeleton evidence
by a fresh capability meta.  Skeleton evidence contains no delegated leaves,
so unobservable constructor fields are canonically `Any`, matching ordinary
`Shape.finalize` behavior.
-/
def freshenSkeleton
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    Shape.Evidence -> InferState -> Option (Cap × InferState)
  | .unseen, state => some (state.freshCap origin)
  | .known leaf, state => some (leaf.toCap, state)
  | .con name children, state => do
      let mask <- observable name
      let (capabilities, state) <-
        freshenSkeletonMasked observable origin mask children state
      pure (.con name capabilities, state)
  | .prod components, state => do
      let (capabilities, state) <-
        freshenSkeletonList observable origin components state
      pure (.prod capabilities, state)

/-- Freshen every observable component of product evidence. -/
def freshenSkeletonList
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    List Shape.Evidence -> InferState -> Option (List Cap × InferState)
  | [], state => some ([], state)
  | evidence :: rest, state => do
      let (head, state) <- freshenSkeleton observable origin evidence state
      let (tail, state) <- freshenSkeletonList observable origin rest state
      pure (head :: tail, state)

/-- Freshen exactly the observable fields selected by a constructor mask. -/
def freshenSkeletonMasked
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    List Bool -> List Shape.Evidence -> InferState ->
      Option (List Cap × InferState)
  | [], [], state => some ([], state)
  | isObservable :: mask, evidence :: rest, state => do
      let (head, state) <-
        if isObservable then freshenSkeleton observable origin evidence state
        else some (.any, state)
      let (tail, state) <-
        freshenSkeletonMasked observable origin mask rest state
      pure (head :: tail, state)
  | _, _, _ => none

end

/-! ### Consumer-side capability solving for user pattern constructors -/

/--
Allocate one shared capability meta-variable for each observable ordinary
variable of a pattern-constructor result.  The keys are constructor-scheme
variables, while the evidence leaves are fresh inference metas.  Repeated
result occurrences therefore receive the same capability leaf.
-/
def freshPatternCtorAssignments
    (origin : ConstraintOrigin) :
    List TypePM.TyVar -> InferState ->
      Projection.Assignments × InferState
  | [], state => ([], state)
  | varId :: variables, state =>
      let (capability, state) := state.freshCap origin
      let (assignments, state) :=
        freshPatternCtorAssignments origin variables state
      ((varId, Shape.ofCap capability) :: assignments, state)

/--
Build the capability demanded of each constructor child by the shared result
assignment.  A field with no observable path to a result variable contributes
no constraint; capability evidence is never seeded from an unrelated target
position.
-/
def patternCtorFieldDemands
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    List Ty -> Option (List (Option Cap))
  | [] => some []
  | fieldType :: fieldTypes => do
      let relevant <-
        Projection.relevantVars observable resultVariables fieldType
      let demand <-
        match relevant with
        | [] => pure none
        | _ :: _ => do
            let evidence <- Projection.buildResultTemplate observable
              resultVariables assignments fieldType
            let capability <- Shape.finalize observable evidence
            pure (some capability)
      let demands <- patternCtorFieldDemands observable resultVariables
        assignments fieldTypes
      pure (demand :: demands)

/--
Solve only the consumer capabilities of constructor children against the
shared structural demands induced by the constructor relation.  For example,
the generic List `cons` signature generates `kappa` and `List kappa` for its
two fields.  Protected producer variables are still guarded by
`runResolvedConstraint`.
-/
def alignPatternCtorCapabilities :
    InferState -> ConstraintOrigin -> List Cap -> List (Option Cap) ->
      Option InferState
  | state, _, [], [] => some state
  | state, origin, child :: children, demand :: demands => do
      let state <-
        match demand with
        | none => pure state
        | some expected =>
            runResolvedConstraint state origin
              (.capEq (child.apply state.prevailing.cap)
                (expected.apply state.prevailing.cap))
      alignPatternCtorCapabilities state origin children demands
  | _, _, _, _ => none

/--
Infer a user pattern-constructor capability from its actual child consumers.
The existing exact-projection path remains the fast path.  When independent
fresh child variables obscure sharing required by the constructor signature,
the fallback allocates one shared result skeleton, solves the corresponding
field constraints, and reruns exact projection on the zonked children.
-/
def solvePatternCtorCapability
    (signature : FrozenSig) (entry : PatternCtorScheme signature.observability)
    (origin : ConstraintOrigin) (childCaps : List Cap)
    (state : InferState) : Option (Cap × InferState) := do
  let resolvedChildren :=
    childCaps.map fun capability => capability.apply state.prevailing.cap
  match Projection.projectSignature entry.projection
      (resolvedChildren.map Shape.ofCap) with
  | some projected =>
      freshenSkeleton signature.observability origin projected state
  | none =>
      let resultVariables <- Projection.relevantVars signature.observability
        (Projection.targetVars entry.projection.resultType)
        entry.projection.resultType
      let resultVariables := resultVariables.eraseDups
      let (assignments, state) :=
        freshPatternCtorAssignments origin resultVariables state
      let demands <- patternCtorFieldDemands signature.observability
        resultVariables assignments entry.projection.fieldTypes
      let state <- alignPatternCtorCapabilities state origin childCaps demands
      let resolvedChildren :=
        childCaps.map fun capability => capability.apply state.prevailing.cap
      let projected <- Projection.projectSignature entry.projection
        (resolvedChildren.map Shape.ofCap)
      freshenSkeleton signature.observability origin projected state


/--
Infer the recursive producer skeleton from actual clause syntax alone.  A
  pure catch-all remains the closed producer `Any`; no consumer demand or
target annotation is consulted.
-/
def recursiveMatcherTemplate
    (signature : FrozenSig) (path : SyntaxPath) (clauses : List Clause)
    (state : InferState) : Option (Cap × InferState) := do
  let evidence <- matcherSkeletonEvidence signature.toMatcherSig clauses
  match evidence with
  | .unseen => pure (.any, state)
  | evidence =>
      freshenSkeleton signature.observability
        (freshOrigin .recursiveBinder path "fix-producer-shape")
        evidence state

/-- Build the monomorphic domain/codomain placeholder used while checking a
recursive binder.  Keeping this state-threading fragment named makes its
append-only history available independently of the expression mutual
recursion. -/
def buildFixPlaceholder
    (signature : FrozenSig) (path : SyntaxPath) (body : Expr)
    (state : InferState) : Option (Ty × Ty × InferState) :=
  match body with
  | .matcher clauses => do
      let (capability, state) <-
        recursiveMatcherTemplate signature path clauses state
      let (argumentCapability, state) :=
        match capability.fcv with
        | first :: _ => (Cap.var first, state)
        | [] => state.freshCap
            (freshOrigin .recursiveBinder path "fix-argument-capability")
      let (argumentTarget, state) := state.freshTy
        (freshOrigin .recursiveBinder path "fix-argument-target")
      let (producerTarget, state) := state.freshTy
        (freshOrigin .recursiveBinder path "fix-producer-target")
      pure (.slot argumentCapability argumentTarget,
        .matcher capability producerTarget, state)
  | _ =>
      let (domain, state) := state.freshTy
        (freshOrigin .recursiveBinder path "fix-domain")
      let (codomain, state) := state.freshTy
        (freshOrigin .recursiveBinder path "fix-codomain")
      some (domain, codomain, state)

mutual

/-- Fuelled executable W for expressions. -/
def inferExprFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Expr ->
      InferState -> Option ExprResult
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, signature, context, selfEnv, path, expression, state =>
      let state := visit state (match expression with
        | .var _ => .exprVar | .lam _ _ => .exprLam | .fix _ _ _ => .exprFix
        | .app _ _ => .exprApp | .lit _ => .exprLit | .tuple _ => .exprTuple
        | .ctor _ _ => .exprCtor | .prim _ _ => .exprPrim
        | .letE _ _ _ => .exprLet | .something => .exprSomething
        | .matcher _ => .exprMatcher | .matchAll _ _ _ _ => .exprMatchAll) path
      match expression with
      | .var name =>
          let normalizedContext := context.applySubst state.prevailing
          match normalizedContext.find? name with
          | none => none
          | some scheme =>
              let (target, state) :=
                instantiateSchemeInState signature context normalizedContext
                  name state scheme
              let state :=
                match selfEnv.find? name with
                | none => state
                | some placeholder =>
                    recordSelfReference state name placeholder path
              some (finishExpr expression path target state)
      | .lam name body =>
          let (domain, state) :=
            state.freshTy (freshOrigin .expression path "lambda-domain")
          match inferExprFuel fuel signature
              ((name, Scheme.mono domain) :: context)
              (selfEnv.erase name) (0 :: path) body state with
          | none => none
          | some bodyResult =>
              some (finishExpr expression path
                (.fn domain bodyResult.target) bodyResult.state)
      | .fix self argument body =>
          if self != argument && DirectSelf.check self body then
            match buildFixPlaceholder signature path body state with
            | none => none
            | some (domain, codomain, state) =>
                let placeholder := Ty.fn domain codomain
                let state :=
                  (state.recordEvent
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
                    match alignTypes bodyResult.state
                        (freshOrigin .recursiveBinder path "fix-result")
                        bodyResult.target codomain with
                    | none => none
                    | some state =>
                        some (finishExpr expression path placeholder state)
          else none
      | .app function argument =>
          match inferExprFuel fuel signature context selfEnv
              (0 :: path) function state with
          | none => none
          | some functionResult =>
              let (domain, state) := functionResult.state.freshTy
                (freshOrigin .expression path "application-domain")
              let (resultTarget, state) := state.freshTy
                (freshOrigin .expression path "application-result")
              match alignTypes state
                  (freshOrigin .expression path "application-function")
                  functionResult.target (.fn domain resultTarget) with
              | none => none
              | some state =>
                  match inferExprFuel fuel signature context selfEnv
                      (1 :: path) argument state with
                  | none => none
                  | some argumentResult =>
                      match alignExprResultAtExpected (1 :: path)
                          argumentResult domain with
                      | none => none
                      | some state =>
                          some (finishExpr expression path resultTarget state)
      | .lit _ => some (finishExpr expression path .int state)
      | .tuple expressions =>
          match inferExprsFuel fuel signature context selfEnv path 0
              expressions state with
          | none => none
          | some results =>
              some (finishExpr expression path (.prod results.targets)
                results.state)
      | .ctor name expressions =>
          match signature.findDataCtor name with
          | none => none
          | some scheme =>
              let incomingSupply := state.supply
              let capImages := freshCapImages incomingSupply scheme.capBinders
              let ((expected, resultTarget), state) :=
                instantiateCtorInState state scheme
              match checkExprsFuel fuel signature context selfEnv path 0
                  expressions expected state with
              | none => none
              | some state =>
                  let state :=
                    state.freezeCapabilityExport capImages resultTarget
                  some (finishExpr expression path resultTarget state)
      | .prim op expressions =>
          match signature.findPrimitive op with
          | none => none
          | some scheme =>
              let incomingSupply := state.supply
              let capImages := freshCapImages incomingSupply scheme.capBinders
              let ((expected, resultTarget), state) :=
                instantiateCtorInState state scheme
              match checkExprsFuel fuel signature context selfEnv path 0
                  expressions expected state with
              | none => none
              | some state =>
                  let state :=
                    state.freezeCapabilityExport capImages resultTarget
                  some (finishExpr expression path resultTarget state)
      | .letE name value body =>
          match inferExprFuel fuel signature context selfEnv
              (0 :: path) value state with
          | none => none
          | some valueResult =>
              let normalizedContext :=
                context.applySubst valueResult.state.prevailing
              let normalizedValue :=
                valueResult.state.prevailing.apply valueResult.target
              let scheme := signature.generalize normalizedContext normalizedValue
              let state := valueResult.state.recordEvent
                (.letGeneralization valueResult.state.trace.solves.length
                  name context valueResult.target normalizedContext
                  normalizedValue scheme)
              match inferExprFuel fuel signature
                  ((name, scheme) :: context)
                  (selfEnv.erase name) (1 :: path) body state with
              | none => none
              | some bodyResult =>
                  some (finishExpr expression path bodyResult.target
                    bodyResult.state)
      | .something =>
          let (target, state) := state.freshTy
            (freshOrigin .expression path "something-target")
          some (finishExpr expression path (.matcher .any target) state)
      | .matcher clauses =>
          match inferMatcherFuel fuel signature context selfEnv path clauses
              state with
          | none => none
          | some result =>
              some (finishExpr expression path result.target result.state)
      | .matchAll target matcher pattern body =>
          match inferExprFuel fuel signature context selfEnv
              (0 :: path) target state with
          | none => none
          | some targetResult =>
              match inferPatternFuel fuel signature context [] [] selfEnv
                  (2 :: path) pattern targetResult.state with
              | none => none
              | some patternResult =>
                  match alignTypes patternResult.state
                      (freshOrigin .pattern (2 :: path) "match-target")
                      patternResult.dual.target targetResult.target with
                  | none => none
                  | some state =>
                      match checkExprFuel fuel signature context selfEnv
                          (1 :: path) matcher
                          (.slot patternResult.dual.cap targetResult.target) state with
                      | none => none
                      | some state =>
                          let bodyContext :=
                            patternResult.bindings.toContext ++ context
                          let bodyEnv := selfEnv.eraseMany pattern.patVars
                          match inferExprFuel fuel signature bodyContext bodyEnv
                              (3 :: path) body state with
                          | none => none
                          | some bodyResult =>
                              some (finishExpr expression path
                                (Ty.listT bodyResult.target) bodyResult.state)

/-- Infer a list of expressions in source order. -/
def inferExprsFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Nat -> List Expr ->
      InferState -> Option ExprsResult
  | 0, _, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [], state => some ⟨[], state⟩
  | fuel + 1, signature, context, selfEnv, parent, index,
      expression :: expressions, state =>
      match inferExprFuel fuel signature context selfEnv
          (index :: parent) expression state with
      | none => none
      | some head =>
          match inferExprsFuel fuel signature context selfEnv parent
              (index + 1) expressions head.state with
          | none => none
          | some tail => some ⟨head.target :: tail.targets, tail.state⟩

/-- Check an expression against an expected type, using slot alignment when needed. -/
def checkExprFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Expr -> Ty ->
      InferState -> Option InferState
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, signature, context, selfEnv, path, expression, expected, state =>
      match inferExprFuel fuel signature context selfEnv path expression state with
      | none => none
      | some result => alignExprResultAtExpected path result expected

/-- Check equal-length expression/type lists. -/
def checkExprsFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Nat ->
      List Expr -> List Ty -> InferState -> Option InferState
  | 0, _, _, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [], [], state => some state
  | fuel + 1, signature, context, selfEnv, parent, index,
      expression :: expressions, expected :: expecteds, state =>
      match checkExprFuel fuel signature context selfEnv (index :: parent)
          expression expected state with
      | none => none
      | some state =>
          checkExprsFuel fuel signature context selfEnv parent (index + 1)
            expressions expecteds state
  | _ + 1, _, _, _, _, _, _, _, _ => none

/-- Infer one user pattern with left-to-right monomorphic bindings. -/
def inferPatternFuel :
    Nat -> FrozenSig -> Context -> PatternCtx -> MonoCtx -> SelfEnv ->
      SyntaxPath -> Pattern -> InferState -> Option PatternResult
  | 0, _, _, _, _, _, _, _, _ => none
  | fuel + 1, signature, context, parameters, bindings, selfEnv,
      path, pattern, state =>
      match pattern with
      | .pvar name =>
          if bindings.names.contains name then none
          else
            let capVar : CapVar := ⟨state.supply.nextCap⟩
            let (capability, state) := state.freshCap
              (freshOrigin .pattern path "pattern-variable-capability")
            let tyVar := state.supply.nextTy
            let (target, state) := state.freshTy
              (freshOrigin .pattern path "pattern-variable-target")
            let resultBindings := bindings ++ [(name, target)]
            let dual := Dual.mk capability target
            some ⟨dual, resultBindings,
              ((state.recordEvent
                  (.patternVarFresh context parameters bindings capVar tyVar))
                |> fun state => visit state .patternVar path).recordEvent
                  (.inferredPattern pattern dual resultBindings path)⟩
      | .wild =>
          let capVar : CapVar := ⟨state.supply.nextCap⟩
          let (capability, state) := state.freshCap
            (freshOrigin .pattern path "pattern-wild-capability")
          let tyVar := state.supply.nextTy
          let (target, state) := state.freshTy
            (freshOrigin .pattern path "pattern-wild-target")
          let dual := Dual.mk capability target
          some ⟨dual, bindings,
            ((state.recordEvent
                (.patternWildFresh context parameters bindings capVar tyVar))
              |> fun state => visit state .patternWild path).recordEvent
                (.inferredPattern pattern dual bindings path)⟩
      | .pval expression =>
          match inferExprFuel fuel signature
              (bindings.toContext ++ context) selfEnv
              (0 :: path) expression (visit state .patternValue path) with
          | none => none
          | some result =>
              let capVar : CapVar := ⟨result.state.supply.nextCap⟩
              let (capability, state) := result.state.freshCap
                (freshOrigin .pattern path "pattern-value-capability")
              let dual := Dual.mk capability result.target
              some ⟨dual, bindings,
                (state.recordEvent
                    (.patternValueFresh context parameters bindings capVar
                      result.target)).recordEvent
                    (.inferredPattern pattern dual bindings path)⟩
      | .embed name =>
          match parameters.find? name with
          | none => none
          | some dual =>
              some ⟨dual, bindings,
                (visit state .patternEmbed path).recordEvent
                  (.inferredPattern pattern dual bindings path)⟩
      | .ptuple patterns =>
          match inferPatternsFuel fuel signature context parameters bindings
              selfEnv path 0 patterns (visit state .patternTuple path) with
          | none => none
          | some results =>
              let dual := Dual.mk (.prod (results.duals.map Dual.cap))
                (.prod (results.duals.map Dual.target))
              some ⟨dual, results.bindings,
                results.state.recordEvent
                  (.inferredPattern pattern dual results.bindings path)⟩
      | .pctor name patterns =>
          match signature.findPatternCtor name with
          | none => none
          | some entry =>
              let incomingSupply := state.supply
              let capImages :=
                freshCapImages incomingSupply entry.scheme.capBinders
              let ((expectedTargets, resultTarget), state) :=
                instantiateCtorInState state entry.scheme
              match inferPatternsFuel fuel signature context parameters bindings
                  selfEnv path 0 patterns (visit state .patternCtor path) with
              | none => none
              | some results =>
                  match alignPatternTargets results.state
                      (freshOrigin .pattern path "pattern-constructor-fields")
                      results.duals expectedTargets with
                  | none => none
                  | some state =>
                      let childCaps := results.duals.map Dual.cap
                      match solvePatternCtorCapability signature entry
                          (freshOrigin .pattern path
                            "pattern-constructor-capability")
                          childCaps state with
                      | none => none
                      | some (capability, state) =>
                          -- Keep raw operands in the trace for provenance, but
                          -- make this acceptance decision at the local zonked
                          -- cut produced by the consumer-side solver.
                          let resolvedChildren := childCaps.map fun child =>
                            child.apply state.prevailing.cap
                          let resolvedCapability :=
                            capability.apply state.prevailing.cap
                          if capCompatibleCheck entry resolvedChildren
                              resolvedCapability then
                            let dual := Dual.mk capability resultTarget
                            let exportPayload := capabilityExportPayload
                              [dual.cap]
                              (dual.target :: results.bindings.map fun entry =>
                                entry.2)
                            let state := state.freezeCapabilityExport
                              capImages exportPayload
                            some ⟨dual, results.bindings,
                              (state.recordEvent
                                  (.patternCtorCompatibility
                                    state.trace.solves.length name childCaps
                                    capability)).recordEvent
                                  (.inferredPattern pattern dual
                                    results.bindings path)⟩
                          else none
      | .pand left right =>
          match inferPatternFuel fuel signature context parameters bindings
              selfEnv (0 :: path) left (visit state .patternAnd path) with
          | none => none
          | some leftResult =>
              match inferPatternFuel fuel signature context parameters
                  leftResult.bindings selfEnv (1 :: path) right
                  leftResult.state with
              | none => none
              | some rightResult =>
                  match alignDuals rightResult.state
                      (freshOrigin .pattern path "pattern-and")
                      leftResult.dual rightResult.dual with
                  | none => none
                  | some state =>
                      some ⟨leftResult.dual, rightResult.bindings,
                        state.recordEvent (.inferredPattern pattern
                          leftResult.dual rightResult.bindings path)⟩
      | .por left right =>
          match inferPatternFuel fuel signature context parameters bindings
              selfEnv (0 :: path) left (visit state .patternOr path) with
          | none => none
          | some leftResult =>
              match inferPatternFuel fuel signature context parameters bindings
                  selfEnv (1 :: path) right leftResult.state with
              | none => none
              | some rightResult =>
                  match alignDuals rightResult.state
                      (freshOrigin .pattern path "pattern-or")
                      leftResult.dual rightResult.dual with
                  | none => none
                  | some aligned =>
                      match alignBindings aligned
                          (freshOrigin .pattern path "pattern-or-bindings")
                          leftResult.bindings rightResult.bindings with
                      | none => none
                      | some state =>
                          some ⟨leftResult.dual, leftResult.bindings,
                            state.recordEvent (.inferredPattern pattern
                              leftResult.dual leftResult.bindings path)⟩
      | .papp name patterns =>
          match signature.findPatternFun name with
          | none => none
          | some scheme =>
              let normalizedContext := context.applySubst state.prevailing
              let normalizedParameters :=
                parameters.applySubst state.prevailing
              let normalizedBindings := bindings.applySubst state.prevailing
              let ((expectedArgs, resultDual), state) :=
                instantiateDualInState signature context parameters bindings
                  normalizedContext normalizedParameters normalizedBindings
                  state scheme
              match inferPatternsFuel fuel signature context parameters bindings
                  selfEnv path 0 patterns (visit state .patternApp path) with
              | none => none
              | some results =>
                  match alignDualLists results.state
                      (freshOrigin .pattern path "pattern-function-arguments")
                      results.duals expectedArgs with
                  | none => none
                  | some state =>
                      some ⟨resultDual, results.bindings,
                        state.recordEvent (.inferredPattern pattern resultDual
                          results.bindings path)⟩

/-- Align two monomorphic binding contexts entrywise.  Binder names must
coincide positionally; the bound types are unified rather than compared for
raw syntactic identity, so or-alternatives that allocated separate
metavariables for the same binder still align. -/
def alignBindings :
    InferState -> ConstraintOrigin -> MonoCtx -> MonoCtx -> Option InferState
  | state, _, [], [] => some state
  | state, origin, left :: lefts, right :: rights =>
      if left.1 = right.1 then do
        let state <- alignTypes state origin left.2 right.2
        alignBindings state origin lefts rights
      else
        none
  | _, _, _, _ => none

/-- Infer a pattern list while threading its monomorphic binding context. -/
def inferPatternsFuel :
    Nat -> FrozenSig -> Context -> PatternCtx -> MonoCtx -> SelfEnv ->
      SyntaxPath -> Nat -> List Pattern -> InferState -> Option PatternsResult
  | 0, _, _, _, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, bindings, _, _, _, [], state =>
      some ⟨[], bindings, state⟩
  | fuel + 1, signature, context, parameters, bindings, selfEnv,
      parent, index, pattern :: patterns, state =>
      match inferPatternFuel fuel signature context parameters bindings selfEnv
          (index :: parent) pattern state with
      | none => none
      | some head =>
          match inferPatternsFuel fuel signature context parameters
              head.bindings selfEnv parent (index + 1) patterns head.state with
          | none => none
          | some tail => some ⟨head.dual :: tail.duals, tail.bindings, tail.state⟩

/-- Align a capability/target dual in the two separate solver sorts. -/
def alignDuals :
    InferState -> ConstraintOrigin -> Dual -> Dual -> Option InferState
  | state, origin, left, right => do
      let startSolve := state.trace.solves.length
      let resolvedLeft := left.applySubst state.prevailing
      let resolvedRight := right.applySubst state.prevailing
      let state <- runResolvedConstraint state origin
        (.capEq (left.cap.apply state.prevailing.cap)
          (right.cap.apply state.prevailing.cap))
      let state <- alignTypes state origin left.target right.target
      pure (state.recordEvent (.dualAlignment startSolve
        state.trace.solves.length left right resolvedLeft resolvedRight))

/-- Align equal-length dual lists. -/
def alignDualLists :
    InferState -> ConstraintOrigin -> List Dual -> List Dual -> Option InferState
  | state, _, [], [] => some state
  | state, origin, left :: lefts, right :: rights => do
      let state <- alignDuals state origin left right
      alignDualLists state origin lefts rights
  | _, _, _, _ => none

/-- Align pattern targets against an instantiated constructor field list. -/
def alignPatternTargets :
    InferState -> ConstraintOrigin -> List Dual -> List Ty -> Option InferState
  | state, _, [], [] => some state
  | state, origin, dual :: duals, expected :: expecteds => do
      let state <- alignTypes state origin dual.target expected
      alignPatternTargets state origin duals expecteds
  | _, _, _, _ => none

/-- Infer a primitive-pattern pattern against one shared matcher target. -/
def inferPPatFuel :
    Nat -> FrozenSig -> SyntaxPath -> PPat -> Ty -> InferState ->
      Option PPatResult
  | 0, _, _, _, _, _ => none
  | fuel + 1, signature, path, pattern, expectedTarget, state =>
      match pattern with
      | .hole =>
          let (capability, state) := state.freshCap
            (freshOrigin .primitivePattern path "primitive-hole")
          let holes := [Dual.mk capability expectedTarget]
          some ⟨expectedTarget, holes, [],
            (visit state .ppatHole path).recordEvent
              (.inferredPPat pattern expectedTarget holes [] path)⟩
      | .wild =>
          some ⟨expectedTarget, [], [],
            (visit state .ppatWild path).recordEvent
              (.inferredPPat pattern expectedTarget [] [] path)⟩
      | .pval name =>
          let bindings := [(name, expectedTarget)]
          some ⟨expectedTarget, [], bindings,
            (visit state .ppatValue path).recordEvent
              (.inferredPPat pattern expectedTarget [] bindings path)⟩
      | .ctor name patterns =>
          match signature.findPatternCtor name with
          | none => none
          | some entry =>
              let incomingSupply := state.supply
              let capImages :=
                freshCapImages incomingSupply entry.scheme.capBinders
              let ((fieldTargets, resultTarget), state) :=
                instantiateCtorInState state entry.scheme
              match alignTypes state
                  (freshOrigin .primitivePattern path "pp-constructor-result")
                  resultTarget expectedTarget with
              | none => none
              | some state =>
                  match inferPPatsFuel fuel signature path 0 patterns
                      fieldTargets state with
                  | none => none
                  | some results =>
                      let exportPayload := capabilityExportPayload
                        (results.holes.map Dual.cap)
                        (results.holes.map Dual.target ++
                          expectedTarget :: results.bindings.map fun entry =>
                            entry.2)
                      let state := results.state.freezeCapabilityExport
                        capImages exportPayload
                      some ⟨expectedTarget, results.holes, results.bindings,
                        (visit state .ppatCtor path).recordEvent
                          (.inferredPPat pattern expectedTarget results.holes
                            results.bindings path)⟩
      | .tuple patterns =>
          match freshTargets state
              (freshOrigin .primitivePattern path "pp-tuple-field")
              patterns.length with
          | (targets, state) =>
              match alignTypes state
                  (freshOrigin .primitivePattern path "pp-tuple-result")
                  (.prod targets) expectedTarget with
              | none => none
              | some state =>
                  match inferPPatsFuel fuel signature path 0 patterns targets
                      state with
                  | none => none
                  | some results =>
                      some ⟨expectedTarget, results.holes, results.bindings,
                        (visit results.state .ppatTuple path).recordEvent
                          (.inferredPPat pattern expectedTarget results.holes
                            results.bindings path)⟩

/-- Infer equal-length primitive-pattern/target lists. -/
def inferPPatsFuel :
    Nat -> FrozenSig -> SyntaxPath -> Nat -> List PPat -> List Ty ->
      InferState -> Option PPatsResult
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, [], [], state => some ⟨[], [], [], state⟩
  | fuel + 1, signature, parent, index,
      pattern :: patterns, target :: targets, state =>
      match inferPPatFuel fuel signature (index :: parent) pattern target state with
      | none => none
      | some head =>
          match inferPPatsFuel fuel signature parent (index + 1)
              patterns targets head.state with
          | none => none
          | some tail =>
              if namesDisjoint head.bindings.names tail.bindings.names then
                some ⟨head.target :: tail.targets,
                  head.holes ++ tail.holes,
                  head.bindings ++ tail.bindings, tail.state⟩
              else none
  | _ + 1, _, _, _, _, _, _ => none

/-- Allocate a finite list of fresh target metas. -/
def freshTargets :
    InferState -> ConstraintOrigin -> Nat -> List Ty × InferState
  | state, _, 0 => ([], state)
  | state, origin, count + 1 =>
      let (target, state) := state.freshTy origin
      let (targets, state) := freshTargets state origin count
      (target :: targets, state)

/-- Infer one primitive data pattern against an expected target. -/
def inferDPatFuel :
    Nat -> FrozenSig -> SyntaxPath -> DPat -> Ty -> InferState ->
      Option DPatResult
  | 0, _, _, _, _, _ => none
  | fuel + 1, signature, path, pattern, expectedTarget, state =>
      match pattern with
      | .var name =>
          let bindings := [(name, expectedTarget)]
          some ⟨expectedTarget, bindings,
            (visit state .dpatVar path).recordEvent
              (.inferredDPat pattern expectedTarget bindings path)⟩
      | .wild =>
          some ⟨expectedTarget, [],
            (visit state .dpatWild path).recordEvent
              (.inferredDPat pattern expectedTarget [] path)⟩
      | .ctor name patterns =>
          match signature.findDataCtor name with
          | none => none
          | some scheme =>
              let incomingSupply := state.supply
              let capImages := freshCapImages incomingSupply scheme.capBinders
              let ((fieldTargets, resultTarget), state) :=
                instantiateCtorInState state scheme
              match alignTypes state
                  (freshOrigin .dataPattern path "dp-constructor-result")
                  resultTarget expectedTarget with
              | none => none
              | some state =>
                  match inferDPatsFuel fuel signature path 0 patterns
                      fieldTargets state with
                  | none => none
                  | some results =>
                      let exportPayload := capabilityExportPayload []
                        (expectedTarget :: results.bindings.map fun entry =>
                          entry.2)
                      let state := results.state.freezeCapabilityExport
                        capImages exportPayload
                      some ⟨expectedTarget, results.bindings,
                        (visit state .dpatCtor path).recordEvent
                          (.inferredDPat pattern expectedTarget
                            results.bindings path)⟩
      | .tuple patterns =>
          match freshTargets state
              (freshOrigin .dataPattern path "dp-tuple-field")
              patterns.length with
          | (targets, state) =>
              match alignTypes state
                  (freshOrigin .dataPattern path "dp-tuple-result")
                  (.prod targets) expectedTarget with
              | none => none
              | some state =>
                  match inferDPatsFuel fuel signature path 0 patterns targets
                      state with
                  | none => none
                  | some results =>
                      some ⟨expectedTarget, results.bindings,
                        (visit results.state .dpatTuple path).recordEvent
                          (.inferredDPat pattern expectedTarget
                            results.bindings path)⟩

/-- Infer equal-length primitive-data-pattern/target lists. -/
def inferDPatsFuel :
    Nat -> FrozenSig -> SyntaxPath -> Nat -> List DPat -> List Ty ->
      InferState -> Option DPatsResult
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, [], [], state => some ⟨[], [], state⟩
  | fuel + 1, signature, parent, index,
      pattern :: patterns, target :: targets, state =>
      match inferDPatFuel fuel signature (index :: parent) pattern target state with
      | none => none
      | some head =>
          match inferDPatsFuel fuel signature parent (index + 1)
              patterns targets head.state with
          | none => none
          | some tail =>
              if namesDisjoint head.bindings.names tail.bindings.names then
                some ⟨head.target :: tail.targets,
                  head.bindings ++ tail.bindings, tail.state⟩
              else none
  | _ + 1, _, _, _, _, _, _ => none

/-- Check every arm of one clause against its decomposition-result type. -/
def checkArmsFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> MonoCtx -> SyntaxPath -> Nat ->
      List Arm -> Ty -> Ty -> InferState -> Option InferState
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, _, [], _, _, state => some state
  | fuel + 1, signature, context, selfEnv, ppBindings, parent, index,
      .mk dataPattern body :: arms, clauseTarget, bodyTarget, state =>
      match inferDPatFuel fuel signature (0 :: index :: parent)
          dataPattern clauseTarget state with
      | none => none
      | some dataResult =>
          if namesDisjoint dataResult.bindings.names ppBindings.names then
            let bodyContext :=
              dataResult.bindings.toContext ++ ppBindings.toContext ++ context
            let bodyEnv := selfEnv.eraseMany
              (ppBindings.names ++ dataResult.bindings.names)
            match checkExprFuel fuel signature bodyContext bodyEnv
                (1 :: index :: parent) body bodyTarget dataResult.state with
            | none => none
            | some state =>
                checkArmsFuel fuel signature context selfEnv ppBindings parent
                  (index + 1) arms clauseTarget bodyTarget state
          else none

/-- Infer one matcher clause under the shared target and cumulative state. -/
def inferClauseFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Clause -> Ty ->
      InferState -> Option ClauseResult
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, signature, context, selfEnv, path,
      (.mk primitivePattern next arms), sharedTarget, state =>
      match inferPPatFuel fuel signature (0 :: path) primitivePattern
          sharedTarget (visit state .clause path) with
      | none => none
      | some ppResult =>
          match decomposeME next ppResult.holes.length with
          | none => none
          | some nextMatchers =>
              let slotTargets := ppResult.holes.map fun hole =>
                Ty.slot hole.cap hole.target
              match checkExprsFuel fuel signature context selfEnv (1 :: path) 0
                  nextMatchers slotTargets ppResult.state with
              | none => none
              | some state =>
                  let armBodyTarget :=
                    Ty.listT (prodTy (ppResult.holes.map Dual.target))
                  match checkArmsFuel fuel signature context selfEnv
                      ppResult.bindings (2 :: path) 0 arms sharedTarget
                      armBodyTarget state with
                  | none => none
                  | some state =>
                      some ⟨sharedTarget, ppResult.holes, state⟩

/-- Infer all matcher clauses under one shared target and substitution trace. -/
def inferClausesFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> Nat ->
      List Clause -> Ty -> InferState -> Option ClausesResult
  | 0, _, _, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [], target, state => some ⟨target, [], state⟩
  | fuel + 1, signature, context, selfEnv, parent, index,
      clause :: clauses, target, state =>
      match inferClauseFuel fuel signature context selfEnv (index :: parent)
          clause target state with
      | none => none
      | some head =>
          match inferClausesFuel fuel signature context selfEnv parent
              (index + 1) clauses target head.state with
          | none => none
          | some tail =>
              some ⟨target, head.rawHoles :: tail.rawHoleLists, tail.state⟩

/-- Infer and finalize an actual matcher literal with mandatory coverage. -/
def inferMatcherFuel :
    Nat -> FrozenSig -> Context -> SelfEnv -> SyntaxPath -> List Clause ->
      InferState -> Option ExprResult
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, signature, context, selfEnv, path, clauses, state =>
      let (target, state) := state.freshTy
        (freshOrigin .matcherClause path "matcher-target")
      match inferClausesFuel fuel signature context selfEnv path 0 clauses target
          state with
      | none => none
      | some clausesResult =>
          let finalHoleLists := clausesResult.rawHoleLists.map fun holes =>
            (holes.map (Dual.applySubst clausesResult.state.prevailing)).map
              Dual.cap
          match collectClauseEvidence signature.toMatcherSig clauses
              finalHoleLists with
          | none => none
          | some evidence =>
              match Shape.inferShape signature.observability evidence with
              | none => none
              | some capability =>
                  let finalTarget := clausesResult.state.prevailing.apply target
                  if clauseCapsListCheck signature capability clauses
                        finalHoleLists &&
                      catchAllLastCheck clauses && matcherBindersCheck clauses &&
                      armExhaustiveCheck signature clauses finalTarget &&
                      coverageCheck signature.toMatcherSig clauses capability then
                    let state := clausesResult.state.recordEvent
                      (.literalCoverage clauses capability)
                    let state := state.recordEvent
                      (.matcherFinalization state.trace.solves.length clauses
                        target clausesResult.rawHoleLists finalTarget
                        finalHoleLists evidence capability)
                    let borrowed :=
                      borrowedMatcherCapVars state context
                    let state := state.protectMatcherCapabilityExcept capability
                      borrowed
                    some ⟨Ty.matcher capability target, state⟩
                  else none

end

/-- A successful lookup of an active recursive binder records both the
reference event and its provenance source in the actual W result. -/
theorem inferExprFuel_activeSelf_records
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String}
    {state : InferState} {result : ExprResult} {placeholder : Ty}
    (active : selfEnv.find? name = some placeholder)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.var name) state = some result) :
    .directSelfReference name placeholder path ∈ result.state.trace.events ∧
      .selfReference name placeholder path ∈ result.state.sources := by
  let entered := visit state .exprVar path
  let normalizedContext := context.applySubst entered.prevailing
  cases lookup : normalizedContext.find? name with
  | none => simp [inferExprFuel, entered, normalizedContext, lookup] at success
  | some scheme =>
      cases instantiated : instantiateSchemeInState signature context
          normalizedContext name entered scheme with
      | mk target next =>
          simp [inferExprFuel, entered, normalizedContext, lookup, instantiated,
            active] at success
          subst result
          simp [finishExpr, recordSelfReference, InferState.recordEvent,
            InferState.recordSource]

/-- A generous fuel bound for W, including solver and list-administration calls. -/
def inferenceFuel (expression : Expr) : Nat :=
  8 * (exprTraversalFuel expression + 1)

/-- Reject a result whose trace ever strengthened an instantiated producer. -/
def enforceProtectedResult (result : ExprResult) : Option ExprResult :=
  if protectedProducerTraceCheck result.state then some result else none

/-- Raw Algorithm W traversal with producer protection, before the
terminal reconstruction audit used by the public entry point. -/
def inferRaw
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    Option ExprResult :=
  (inferExprFuel (inferenceFuel expression) signature context [] [] expression
    (initialState signature context)).bind enforceProtectedResult

/-- Passing the raw producer-protection filter certifies non-strengthening. -/
theorem enforceProtectedResult_sound
    {input output : ExprResult}
    (success : enforceProtectedResult input = some output) :
    input = output /\ ProtectedProducerTrace output.state := by
  unfold enforceProtectedResult at success
  split at success
  · rename_i checked
    have equality := Option.some.inj success
    subst output
    exact ⟨rfl, (protectedProducerTraceCheck_eq_true input.state).mp checked⟩
  · contradiction

/-- Every successful complete inference trace preserves protected producers. -/
theorem inferRaw_protected
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : ExprResult}
    (success : inferRaw signature context expression = some result) :
    ProtectedProducerTrace result.state := by
  unfold inferRaw at success
  cases core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) with
  | none => simp [core] at success
  | some raw =>
      have guarded : enforceProtectedResult raw = some result := by
        simpa [core] using success
      exact (enforceProtectedResult_sound guarded).2

/-- Raw result type after replaying the one prevailing substitution. -/
def inferRawType
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    Option Ty := do
  let result <- inferRaw signature context expression
  pure result.resolvedTarget

/-- Executable success/failure of W. -/
def rawInferenceSucceeds
    (signature : FrozenSig) (context : Context) (expression : Expr) : Bool :=
  (inferRaw signature context expression).isSome

/-- Decidability of the raw protected traversal. -/
theorem rawInference_decides
    (signature : FrozenSig) (context : Context) (expression : Expr) :
    rawInferenceSucceeds signature context expression = true ∨
      rawInferenceSucceeds signature context expression = false := by
  cases rawInferenceSucceeds signature context expression <;> simp

/-! ## Append-only history of executable W -/

theorem InferState.historyPrefix_freshTy
    (state : InferState) (origin : ConstraintOrigin) :
    state.HistoryPrefix (state.freshTy origin).2 := by
  let middle : InferState :=
    { state with supply := (InferenceBase.freshTyMeta state.supply).2 }
  have first : state.HistoryPrefix middle :=
    InferState.HistoryPrefix.of_same_trace rfl
  have second : middle.HistoryPrefix
      (middle.recordEvent (.freshTy origin state.supply.nextTy)) :=
    middle.historyPrefix_recordEvent _
  simpa only [InferState.freshTy, middle] using first.trans second

theorem InferState.historyPrefix_freshCap
    (state : InferState) (origin : ConstraintOrigin) :
    state.HistoryPrefix (state.freshCap origin).2 := by
  let middle : InferState :=
    { state with
      supply := (InferenceBase.freshCapMeta state.supply).2
      capabilityOrigins := state.capabilityOrigins.setOrigin
        ⟨state.supply.nextCap⟩ .structuralFlexible }
  have first : state.HistoryPrefix middle :=
    InferState.HistoryPrefix.of_same_trace rfl
  have second : middle.HistoryPrefix
      (middle.recordEvent (.freshCap origin ⟨state.supply.nextCap⟩)) :=
    middle.historyPrefix_recordEvent _
  simpa only [InferState.freshCap, middle] using first.trans second

/-- Freshening structural matcher evidence only appends fresh-capability
events; the three mutually recursive traversals never edit prior history. -/
theorem freshenSkeleton_historyPrefix
    {observable origin evidence state capability result}
    (success : freshenSkeleton observable origin evidence state =
      some (capability, result)) : state.HistoryPrefix result := by
  apply freshenSkeleton.induct
    (motive_1 := fun evidence state => ∀ capability result,
      freshenSkeleton observable origin evidence state =
          some (capability, result) →
        state.HistoryPrefix result)
    (motive_2 := fun evidence state => ∀ capabilities result,
      freshenSkeletonList observable origin evidence state =
          some (capabilities, result) →
        state.HistoryPrefix result)
    (motive_3 := fun mask evidence state => ∀ capabilities result,
      freshenSkeletonMasked observable origin mask evidence state =
          some (capabilities, result) →
        state.HistoryPrefix result)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true })
  case case10 t x state mismatchNil mismatchCons capabilities result success =>
    cases x <;> cases t <;> simp_all [freshenSkeletonMasked]
  all_goals first
    | assumption
    | exact InferState.HistoryPrefix.refl _
    | grind [InferState.historyPrefix_freshCap,
        InferState.HistoryPrefix.refl, InferState.HistoryPrefix.trans,
        Option.bind_eq_some_iff, freshenSkeleton,
        freshenSkeletonList, freshenSkeletonMasked]

/-- Building the recursive matcher placeholder is append-only as well. -/
theorem recursiveMatcherTemplate_historyPrefix
    {signature path clauses state capability result}
    (success : recursiveMatcherTemplate signature path clauses state =
      some (capability, result)) : state.HistoryPrefix result := by
  unfold recursiveMatcherTemplate at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨evidence, skeleton, finished⟩
  cases evidence with
  | unseen =>
      cases finished
      exact InferState.HistoryPrefix.refl state
  | known leaf => exact freshenSkeleton_historyPrefix finished
  | con name children => exact freshenSkeleton_historyPrefix finished
  | prod components => exact freshenSkeleton_historyPrefix finished

/-- Recursive-placeholder construction only allocates fresh metas and hence
preserves the already recorded solver/event history. -/
theorem buildFixPlaceholder_historyPrefix
    {signature path body state domain codomain result}
    (success : buildFixPlaceholder signature path body state =
      some (domain, codomain, result)) : state.HistoryPrefix result := by
  cases body <;> simp_all [buildFixPlaceholder]
  case matcher clauses =>
    rcases Option.bind_eq_some_iff.mp success with
      ⟨pair, recursiveSuccess, rest⟩
    rcases pair with ⟨capability, middle⟩
    have recursiveHistory :=
      recursiveMatcherTemplate_historyPrefix recursiveSuccess
    simp only [Option.some.injEq, Prod.mk.injEq] at rest
    split at rest
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveHistory.trans
        ((InferState.historyPrefix_freshTy _ _).trans
          (InferState.historyPrefix_freshTy _ _))
    · rcases rest with ⟨_, _, rfl⟩
      exact recursiveHistory.trans
        ((InferState.historyPrefix_freshCap _ _).trans
          ((InferState.historyPrefix_freshTy _ _).trans
            (InferState.historyPrefix_freshTy _ _)))
  all_goals
    rcases success with ⟨_, _, rfl⟩
    exact (InferState.historyPrefix_freshTy _ _).trans
      (InferState.historyPrefix_freshTy _ _)

theorem visit_historyPrefix
    (state : InferState) (kind : NodeKind) (path : SyntaxPath) :
    state.HistoryPrefix (visit state kind path) := by
  exact state.historyPrefix_recordEvent _

theorem finishExpr_historyPrefix
    (expression : Expr) (path : SyntaxPath) (target : Ty)
    (state : InferState) :
    state.HistoryPrefix (finishExpr expression path target state).state := by
  exact state.historyPrefix_recordEvent _

theorem instantiateSchemeInState_historyPrefix
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (state : InferState) (scheme : Scheme) :
    state.HistoryPrefix
      (instantiateSchemeInState signature rawContext normalizedContext name
        state scheme).2 := by
  simp only [instantiateSchemeInState]
  apply InferState.HistoryPrefix.trans
    (InferState.HistoryPrefix.of_same_trace rfl)
  apply InferState.historyPrefix_recordEvent

theorem instantiateCtorInState_historyPrefix
    (state : InferState) (scheme : CtorScheme) :
    state.HistoryPrefix (instantiateCtorInState state scheme).2 := by
  simp only [instantiateCtorInState]
  apply InferState.HistoryPrefix.trans
    (InferState.HistoryPrefix.of_same_trace rfl)
  apply InferState.historyPrefix_recordEvent

theorem instantiateDualInState_historyPrefix
    (signature : FrozenSig)
    (rawContext : Context) (rawParameters : PatternCtx)
    (rawBindings : MonoCtx) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (state : InferState) (scheme : DualScheme) :
    state.HistoryPrefix
      (instantiateDualInState signature rawContext rawParameters rawBindings
        context parameters bindings state scheme).2 := by
  simp only [instantiateDualInState]
  apply InferState.HistoryPrefix.trans
    (InferState.HistoryPrefix.of_same_trace rfl)
  apply InferState.historyPrefix_recordEvent

theorem instantiateSchemeInState_historyPrefix_of_eq
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state final : InferState} {scheme : Scheme} {target : Ty}
    (success : instantiateSchemeInState signature rawContext normalizedContext
      name state scheme = (target, final)) : state.HistoryPrefix final := by
  exact InferState.HistoryPrefix.snd_of_eq
    (instantiateSchemeInState_historyPrefix signature rawContext
      normalizedContext name state scheme) success

theorem instantiateCtorInState_historyPrefix_of_eq
    {state final : InferState} {scheme : CtorScheme}
    {arguments : List Ty} {target : Ty}
    (success : instantiateCtorInState state scheme =
      ((arguments, target), final)) : state.HistoryPrefix final := by
  exact InferState.HistoryPrefix.snd_of_eq
    (instantiateCtorInState_historyPrefix state scheme) success

theorem instantiateDualInState_historyPrefix_of_eq
    {signature : FrozenSig} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {state final : InferState} {scheme : DualScheme}
    {arguments : List Dual} {target : Dual}
    (success : instantiateDualInState signature rawContext rawParameters
      rawBindings context parameters bindings state scheme =
      ((arguments, target), final)) :
    state.HistoryPrefix final := by
  exact InferState.HistoryPrefix.snd_of_eq
    (instantiateDualInState_historyPrefix signature rawContext rawParameters
      rawBindings context parameters bindings state scheme) success

/-- The constructor-instantiation event emitted by the executable helper is
present in its returned state. -/
theorem instantiateCtorInState_event_mem_of_eq
    {state final : InferState} {scheme : CtorScheme}
    {arguments : List Ty} {target : Ty}
    (success : instantiateCtorInState state scheme =
      ((arguments, target), final)) :
    ∃ solveCount supply capImages,
      .ctorInstantiation solveCount supply scheme arguments target capImages ∈
        final.trace.events := by
  unfold instantiateCtorInState at success
  simp only [Prod.mk.injEq] at success
  rcases success with ⟨argumentsEq, finalEq⟩
  subst final
  refine ⟨state.trace.solves.length, state.supply,
    freshCapImages state.supply scheme.capBinders, ?_⟩
  rw [argumentsEq]
  simp [InferState.recordEvent]

/-- The expression-scheme instantiation helper retains its complete ambient
scope event in the returned state. -/
theorem instantiateSchemeInState_event_mem_of_eq
    {signature : FrozenSig} {rawContext normalizedContext : Context}
    {name : String} {state final : InferState} {scheme : Scheme} {target : Ty}
    (success : instantiateSchemeInState signature rawContext normalizedContext
      name state scheme = (target, final)) :
    ∃ solveCount supply fixedCaps fixedTys reservedCaps reservedTys capImages
        tyImages,
      .schemeInstantiation solveCount supply scheme name rawContext
          normalizedContext fixedCaps fixedTys reservedCaps reservedTys target
          capImages tyImages ∈ final.trace.events := by
  unfold instantiateSchemeInState at success
  simp only [Prod.mk.injEq] at success
  rcases success with ⟨targetEq, finalEq⟩
  subst final
  refine ⟨state.trace.solves.length, state.supply,
    SourceFixedCapScope signature normalizedContext,
    SourceFixedTyScope signature normalizedContext,
    SourceCapScope signature normalizedContext,
    SourceTyScope signature normalizedContext,
    Scheme.canonicalCapImages state.supply scheme,
    Scheme.canonicalTyImages state.supply scheme, ?_⟩
  rw [targetEq]
  simp [InferState.recordEvent]

/-- The dual-scheme instantiation helper retains its raw and normalized
pattern environments in the returned state. -/
theorem instantiateDualInState_event_mem_of_eq
    {signature : FrozenSig} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx}
    {state final : InferState} {scheme : DualScheme}
    {arguments : List Dual} {target : Dual}
    (success : instantiateDualInState signature rawContext rawParameters
      rawBindings context parameters bindings state scheme =
      ((arguments, target), final)) :
    ∃ solveCount supply fixedCaps fixedTys reservedCaps reservedTys capImages
        tyImages,
      .dualInstantiation solveCount supply scheme rawContext rawParameters
          rawBindings context parameters bindings fixedCaps fixedTys reservedCaps
          reservedTys arguments target capImages tyImages ∈
        final.trace.events := by
  unfold instantiateDualInState at success
  simp only [Prod.mk.injEq] at success
  rcases success with ⟨resultEq, finalEq⟩
  subst final
  refine ⟨state.trace.solves.length, state.supply,
    PatternFixedCapScope signature context parameters bindings,
    PatternFixedTyScope signature context parameters bindings,
    PatternCapScope signature context parameters bindings,
    PatternTyScope signature context parameters bindings,
    freshCapImages state.supply scheme.capBinders,
    freshTyImages state.supply scheme.tyBinders, ?_⟩
  rw [resultEq]
  simp [InferState.recordEvent]

/-- The ordinary alignment wrapper retains its raw inputs and local normalized
inputs in the returned trace. -/
theorem alignTypes_event_mem
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some result) :
    .typeAlignment state.trace.solves.length result.trace.solves.length
        left right (state.prevailing.apply left) (state.prevailing.apply right) ∈
      result.trace.events := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, _coreSuccess, finished⟩
  have resultEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length left right
      (state.prevailing.apply left) (state.prevailing.apply right)) = result :=
    Option.some.inj finished
  subst result
  simp [InferState.recordEvent]

/-- The dual alignment wrapper likewise retains both raw dual indices. -/
theorem alignDuals_event_mem
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some result) :
    .dualAlignment state.trace.solves.length result.trace.solves.length
        left right (left.applySubst state.prevailing)
          (right.applySubst state.prevailing) ∈ result.trace.events := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, _capSuccess, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with
    ⟨aligned, _typeSuccess, finished⟩
  have resultEq : aligned.recordEvent (.dualAlignment
      state.trace.solves.length aligned.trace.solves.length left right
      (left.applySubst state.prevailing)
      (right.applySubst state.prevailing)) = result :=
    Option.some.inj finished
  subst result
  simp [InferState.recordEvent]

theorem runResolvedConstraint_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {constraint : Constraint}
    (success : runResolvedConstraint state origin constraint = some result) :
    state.HistoryPrefix result := by
  unfold runResolvedConstraint at success
  cases stepEquation : solveResolvedWithLedger state.capabilityOrigins
      state.trace.solves.length origin constraint with
  | none => simp [stepEquation] at success
  | some step =>
      simp only [stepEquation] at success
      cases constraint with
      | capEq _ _ | targetEq _ _ =>
          change some (state.recordSolve step) = some result at success
          exact (state.historyPrefix_recordSolve step).right_congr
            (Option.some.inj success)
      | producerToSlot _ _ _ _ =>
          change (if capSubstSafeVarsCheck state.capabilityOrigins
              step.delta.cap state.protectedCaps
            then some (state.recordSolve step) else none) =
              some result at success
          split at success <;> try contradiction
          have equality := Option.some.inj success
          subst result
          exact state.historyPrefix_recordSolve step

theorem alignTypesCore_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypesCore state origin left right = some result) :
    state.HistoryPrefix result := by
  unfold alignTypesCore at success
  simp only at success
  split at success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_historyPrefix firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      have second : middle.HistoryPrefix result :=
        runResolvedConstraint_historyPrefix restSuccess
      exact first.trans second
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_historyPrefix firstSuccess
    split at restSuccess <;> try contradiction
    all_goals
      have second : middle.HistoryPrefix result :=
        runResolvedConstraint_historyPrefix restSuccess
      exact first.trans second
  · exact runResolvedConstraint_historyPrefix success

theorem alignTypes_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin} {left right : Ty}
    (success : alignTypes state origin left right = some result) :
    state.HistoryPrefix result := by
  unfold alignTypes at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨aligned, coreSuccess, finished⟩
  have coreHistory := alignTypesCore_historyPrefix coreSuccess
  have resultEq : aligned.recordEvent (.typeAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (state.prevailing.apply left)
      (state.prevailing.apply right)) = result :=
    Option.some.inj finished
  exact (coreHistory.trans (aligned.historyPrefix_recordEvent _)).right_congr
    resultEq

theorem alignAtSlot_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {inferred expected : Ty}
    (success : alignAtSlot state origin inferred expected = some result) :
    state.HistoryPrefix result := by
  unfold alignAtSlot at success
  simp only at success
  split at success
  · exact runResolvedConstraint_historyPrefix success
  ·
    rcases Option.bind_eq_some_iff.mp success with
      ⟨middle, firstSuccess, restSuccess⟩
    have first := runResolvedConstraint_historyPrefix firstSuccess
    split at restSuccess <;> try contradiction
    have second : middle.HistoryPrefix result :=
      runResolvedConstraint_historyPrefix restSuccess
    exact first.trans second
  · exact alignTypes_historyPrefix success

theorem alignResolvedProductMatcherAtSlot_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedProductMatcherAtSlot state origin duals consumerCap
      consumerTarget = some result) :
    state.HistoryPrefix result := by
  exact runResolvedConstraint_historyPrefix success

theorem alignResolvedSlotTupleAtSlot_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {consumerCap : Cap} {consumerTarget : Ty}
    (success : alignResolvedSlotTupleAtSlot state origin duals consumerCap
      consumerTarget = some result) :
    state.HistoryPrefix result := by
  unfold alignResolvedSlotTupleAtSlot at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨step, stepSuccess, restSuccess⟩
  exact (state.historyPrefix_recordSolve step).trans
    (runResolvedConstraint_historyPrefix restSuccess)

/-- Expected-type alignment extends the synthesized expression history. -/
theorem alignExprResultAtExpected_historyPrefix
    {path : SyntaxPath} {expressionResult : ExprResult}
    {expected : Ty} {result : InferState}
    (success : alignExprResultAtExpected path expressionResult expected =
      some result) :
    expressionResult.state.HistoryPrefix result := by
  unfold alignExprResultAtExpected at success
  cases planEq : expectedCoercionPlan expressionResult.state
      expressionResult.target expected with
  | productMatcherLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedProductMatcherAtSlot
          expressionResult.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst result
          exact
            (alignResolvedProductMatcherAtSlot_historyPrefix alignmentEq).trans
              (aligned.historyPrefix_recordEvent _)
  | slotTupleLift duals =>
      cases requestedEq : expressionResult.state.prevailing.apply expected <;>
        simp [planEq, requestedEq] at success
      rename_i consumerCap consumerTarget
      cases alignmentEq : alignResolvedSlotTupleAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type") duals consumerCap
          consumerTarget with
      | none => simp [alignmentEq] at success
      | some aligned =>
          simp only [alignmentEq, Option.some.injEq] at success
          subst result
          exact (alignResolvedSlotTupleAtSlot_historyPrefix alignmentEq).trans
            (aligned.historyPrefix_recordEvent _)
  | raw =>
      cases alignmentEq : alignAtSlot expressionResult.state
          (freshOrigin .expression path "expected-type") expressionResult.target
          expected with
      | none => simp [planEq, alignmentEq] at success
      | some aligned =>
          simp only [planEq, alignmentEq, Option.some.injEq] at success
          subst result
          exact (alignAtSlot_historyPrefix alignmentEq).trans
            (aligned.historyPrefix_recordEvent _)

theorem alignDuals_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals state origin left right = some result) :
    state.HistoryPrefix result := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, firstSuccess, secondSuccess⟩
  rcases Option.bind_eq_some_iff.mp secondSuccess with
    ⟨aligned, alignSuccess, finished⟩
  have resultEq : aligned.recordEvent (.dualAlignment
      state.trace.solves.length aligned.trace.solves.length
      left right (left.applySubst state.prevailing)
      (right.applySubst state.prevailing)) = result :=
    Option.some.inj finished
  exact ((runResolvedConstraint_historyPrefix firstSuccess).trans
      ((alignTypes_historyPrefix alignSuccess).trans
        (aligned.historyPrefix_recordEvent _))).right_congr resultEq

theorem alignDualLists_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : List Dual}
    (success : alignDualLists state origin left right = some result) :
    state.HistoryPrefix result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignDualLists] at success
      subst result
      exact InferState.HistoryPrefix.refl state
  | cons head tail induction =>
      cases right with
      | nil => simp [alignDualLists] at success
      | cons expected expecteds =>
          simp only [alignDualLists] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignDuals_historyPrefix firstSuccess).trans
            (induction restSuccess)

theorem alignPatternTargets_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some result) :
    state.HistoryPrefix result := by
  induction duals generalizing state targets with
  | nil =>
      cases targets <;> simp [alignPatternTargets] at success
      subst result
      exact InferState.HistoryPrefix.refl state
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, firstSuccess, restSuccess⟩
          exact (alignTypes_historyPrefix firstSuccess).trans
            (induction restSuccess)

theorem alignBindings_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : MonoCtx}
    (success : alignBindings state origin left right = some result) :
    state.HistoryPrefix result := by
  induction left generalizing state right with
  | nil =>
      cases right <;> simp [alignBindings] at success
      subst result
      exact InferState.HistoryPrefix.refl state
  | cons entry entries induction =>
      cases right with
      | nil => simp [alignBindings] at success
      | cons expected expecteds =>
          simp only [alignBindings] at success
          split at success
          · rcases Option.bind_eq_some_iff.mp success with
              ⟨middle, firstSuccess, restSuccess⟩
            exact (alignTypes_historyPrefix firstSuccess).trans
              (induction restSuccess)
          · exact absurd success (by simp)

theorem freshPatternCtorAssignments_historyPrefix
    {origin : ConstraintOrigin} {variables : List TypePM.TyVar}
    {state result : InferState} {assignments : Projection.Assignments}
    (success : freshPatternCtorAssignments origin variables state =
      (assignments, result)) :
    state.HistoryPrefix result := by
  induction variables generalizing state assignments result with
  | nil =>
      simp only [freshPatternCtorAssignments, Prod.mk.injEq] at success
      rcases success with ⟨_, rfl⟩
      exact InferState.HistoryPrefix.refl state
  | cons varId variables induction =>
      simp only [freshPatternCtorAssignments] at success
      let fresh := state.freshCap origin
      cases restEq : freshPatternCtorAssignments origin variables fresh.2 with
      | mk restAssignments restState =>
          simp only [fresh, restEq, Prod.mk.injEq] at success
          rcases success with ⟨_, rfl⟩
          exact (InferState.historyPrefix_freshCap state origin).trans
            (induction restEq)

theorem alignPatternCtorCapabilities_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {children : List Cap} {demands : List (Option Cap)}
    (success : alignPatternCtorCapabilities state origin children demands =
      some result) :
    state.HistoryPrefix result := by
  induction children generalizing state demands with
  | nil =>
      cases demands <;>
        simp [alignPatternCtorCapabilities] at success
      subst result
      exact InferState.HistoryPrefix.refl state
  | cons child children induction =>
      cases demands with
      | nil => simp [alignPatternCtorCapabilities] at success
      | cons demand demands =>
          cases demand with
          | none =>
              simpa only [alignPatternCtorCapabilities] using
                induction success
          | some expected =>
              simp only [alignPatternCtorCapabilities] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨middle, firstSuccess, restSuccess⟩
              exact (runResolvedConstraint_historyPrefix firstSuccess).trans
                (induction restSuccess)

theorem solvePatternCtorCapability_historyPrefix
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {childCaps : List Cap}
    {state result : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin childCaps
      state = some (capability, result)) :
    state.HistoryPrefix result := by
  unfold solvePatternCtorCapability at success
  simp only at success
  split at success
  · exact freshenSkeleton_historyPrefix success
  ·
    rcases Option.bind_eq_some_iff.mp success with
      ⟨resultVariables, _resultVariablesEq, rest⟩
    let uniqueVariables := resultVariables.eraseDups
    let allocated :=
      freshPatternCtorAssignments origin uniqueVariables state
    rcases allocatedEq : allocated with ⟨assignments, allocatedState⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨demands, _demandsEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨alignedState, alignmentEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨projected, _projectionEq, skeletonEq⟩
    have allocationEq :
        freshPatternCtorAssignments origin uniqueVariables state =
          (assignments, allocatedState) := by
      simpa [allocated] using allocatedEq
    rw [allocationEq] at alignmentEq
    exact (freshPatternCtorAssignments_historyPrefix allocationEq).trans
      ((alignPatternCtorCapabilities_historyPrefix alignmentEq).trans
        (freshenSkeleton_historyPrefix skeletonEq))

theorem freshTargets_historyPrefix
    {state result : InferState} {origin : ConstraintOrigin}
    {count : Nat} {targets : List Ty}
    (success : freshTargets state origin count = (targets, result)) :
    state.HistoryPrefix result := by
  induction count generalizing state targets result with
  | zero =>
      simp only [freshTargets, Prod.mk.injEq] at success
      rcases success with ⟨_, equality⟩
      subst result
      exact InferState.HistoryPrefix.refl state
  | succ count induction =>
      simp only [freshTargets] at success
      let fresh := state.freshTy origin
      let rest := freshTargets fresh.2 origin count
      have first : state.HistoryPrefix fresh.2 := by
        exact InferState.historyPrefix_freshTy state origin
      have restHistory : fresh.2.HistoryPrefix rest.2 :=
        induction (state := fresh.2) (targets := rest.1)
          (result := rest.2) rfl
      have finalEq : rest.2 = result := by
        exact congrArg Prod.snd success
      subst result
      exact first.trans restHistory

/-- Primitive-pattern inference and its list traversal are append-only. -/
theorem inferPPatFuel_historyPrefix
    {fuel signature path pattern target state result}
    (success : inferPPatFuel fuel signature path pattern target state =
      some result) : state.HistoryPrefix result.state := by
  apply inferPPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferPPatFuel fuel signature path pattern target state = some result →
        state.HistoryPrefix result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferPPatsFuel fuel signature path index patterns targets state =
            some result →
          state.HistoryPrefix result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferPPatFuel, inferPPatsFuel, Option.some.injEq]
  all_goals try
    have ctorHistory := instantiateCtorInState_historyPrefix_of_eq
      (by assumption)
  all_goals try
    have alignmentHistory := alignTypes_historyPrefix (by assumption)
  all_goals try
    have freshHistory := freshTargets_historyPrefix (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.HistoryPrefix.refl _
    | grind [InferState.HistoryPrefix.refl,
        InferState.HistoryPrefix.trans,
        InferState.HistoryPrefix.snd_of_eq,
        InferState.HistoryPrefix.right_congr,
        InferState.historyPrefix_freshCap,
        instantiateCtorInState_historyPrefix,
        instantiateCtorInState_historyPrefix_of_eq,
        InferState.historyPrefix_freezeCapabilityExport,
        alignTypes_historyPrefix,
        freshTargets_historyPrefix,
        visit_historyPrefix,
        InferState.historyPrefix_recordEvent,
        Option.bind_eq_some_iff,
        inferPPatFuel, inferPPatsFuel]

/-- The list-traversal companion of `inferPPatFuel_historyPrefix`. -/
theorem inferPPatsFuel_historyPrefix
    {fuel signature path index patterns targets state result}
    (success : inferPPatsFuel fuel signature path index patterns targets state =
      some result) : state.HistoryPrefix result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferPPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferPPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.HistoryPrefix.refl state
          | cons target targets => simp [inferPPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferPPatsFuel] at success
          | cons target targets =>
              simp only [inferPPatsFuel] at success
              cases headEq : inferPPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferPPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact (inferPPatFuel_historyPrefix headEq).trans
                          (induction (index := index + 1)
                            (patterns := patterns) (targets := targets)
                            (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

/-- Primitive data-pattern inference and its list traversal are append-only. -/
theorem inferDPatFuel_historyPrefix
    {fuel signature path pattern target state result}
    (success : inferDPatFuel fuel signature path pattern target state =
      some result) : state.HistoryPrefix result.state := by
  apply inferDPatFuel.induct
    (motive_1 := fun fuel signature path pattern target state => ∀ result,
      inferDPatFuel fuel signature path pattern target state = some result →
        state.HistoryPrefix result.state)
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferDPatsFuel fuel signature path index patterns targets state =
            some result →
          state.HistoryPrefix result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferDPatFuel, inferDPatsFuel, Option.some.injEq]
  all_goals try
    have ctorHistory := instantiateCtorInState_historyPrefix_of_eq
      (by assumption)
  all_goals try
    have alignmentHistory := alignTypes_historyPrefix (by assumption)
  all_goals try
    have freshHistory := freshTargets_historyPrefix (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.HistoryPrefix.refl _
    | grind [InferState.HistoryPrefix.refl,
        InferState.HistoryPrefix.trans,
        InferState.HistoryPrefix.snd_of_eq,
        InferState.HistoryPrefix.right_congr,
        instantiateCtorInState_historyPrefix,
        instantiateCtorInState_historyPrefix_of_eq,
        InferState.historyPrefix_freezeCapabilityExport,
        alignTypes_historyPrefix,
        freshTargets_historyPrefix,
        visit_historyPrefix,
        InferState.historyPrefix_recordEvent,
        Option.bind_eq_some_iff,
        inferDPatFuel, inferDPatsFuel]

/-- The list traversal companion of `inferDPatFuel_historyPrefix`.  It is
public because terminal reconstruction needs the history between a
constructor's alignment cut and the end of its children. -/
theorem inferDPatsFuel_historyPrefix
    {fuel signature path index patterns targets state result}
    (success : inferDPatsFuel fuel signature path index patterns targets state =
      some result) : state.HistoryPrefix result.state := by
  induction fuel generalizing index patterns targets state result with
  | zero => simp [inferDPatsFuel] at success
  | succ fuel induction =>
      cases patterns with
      | nil =>
          cases targets with
          | nil =>
              simp only [inferDPatsFuel, Option.some.injEq] at success
              subst result
              exact InferState.HistoryPrefix.refl state
          | cons target targets => simp [inferDPatsFuel] at success
      | cons pattern patterns =>
          cases targets with
          | nil => simp [inferDPatsFuel] at success
          | cons target targets =>
              simp only [inferDPatsFuel] at success
              cases headEq : inferDPatFuel fuel signature (index :: path)
                  pattern target state with
              | none => simp [headEq] at success
              | some head =>
                  cases tailEq : inferDPatsFuel fuel signature path (index + 1)
                      patterns targets head.state with
                  | none => simp [headEq, tailEq] at success
                  | some tail =>
                      by_cases distinct : namesDisjoint head.bindings.names
                          tail.bindings.names = true
                      · simp [headEq, tailEq, distinct] at success
                        subst result
                        exact (inferDPatFuel_historyPrefix headEq).trans
                          (induction (index := index + 1)
                            (patterns := patterns) (targets := targets)
                            (state := head.state) (result := tail) tailEq)
                      · simp [headEq, tailEq, distinct] at success

set_option maxHeartbeats 1000000 in
/-- Every successful expression inference run, including all nine mutually
recursive checking traversals, only extends the incoming solver/event
history. -/
theorem inferExprFuel_historyPrefix
    {fuel signature context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result) : state.HistoryPrefix result.state := by
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression state =>
      ∀ result,
        inferExprFuel fuel signature context selfEnv path expression state =
            some result →
          state.HistoryPrefix result.state)
    (motive2 := fun fuel signature context selfEnv path expression expected
        state =>
      ∀ result,
        checkExprFuel fuel signature context selfEnv path expression expected
            state = some result →
          state.HistoryPrefix result)
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern state =>
      ∀ result,
        inferPatternFuel fuel signature context parameters bindings selfEnv path
            pattern state = some result →
          state.HistoryPrefix result.state)
    (motive4 := fun fuel signature context parameters bindings selfEnv path
        index patterns state =>
      ∀ result,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            path index patterns state = some result →
          state.HistoryPrefix result.state)
    (motive5 := fun fuel signature context selfEnv path clauses state =>
      ∀ result,
        inferMatcherFuel fuel signature context selfEnv path clauses state =
            some result →
          state.HistoryPrefix result.state)
    (motive6 := fun fuel signature context selfEnv path index clauses target
        state =>
      ∀ result,
        inferClausesFuel fuel signature context selfEnv path index clauses target
            state = some result →
          state.HistoryPrefix result.state)
    (motive7 := fun fuel signature context selfEnv path clause target state =>
      ∀ result,
        inferClauseFuel fuel signature context selfEnv path clause target state =
            some result →
          state.HistoryPrefix result.state)
    (motive8 := fun fuel signature context selfEnv bindings path index arms
        target bodyTarget state =>
      ∀ result,
        checkArmsFuel fuel signature context selfEnv bindings path index arms
            target bodyTarget state = some result →
          state.HistoryPrefix result)
    (motive9 := fun fuel signature context selfEnv path index expressions
        expecteds state =>
      ∀ result,
        checkExprsFuel fuel signature context selfEnv path index expressions
            expecteds state = some result →
          state.HistoryPrefix result)
    (motive10 := fun fuel signature context selfEnv path index expressions
        state =>
      ∀ result,
        inferExprsFuel fuel signature context selfEnv path index expressions
            state = some result →
          state.HistoryPrefix result.state)
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [Option.some.injEq, inferExprFuel, checkExprFuel, inferPatternFuel,
      inferPatternsFuel, inferMatcherFuel, inferClausesFuel, inferClauseFuel,
      checkArmsFuel, checkExprsFuel, inferExprsFuel]
  all_goals try
    have placeholderHistory := buildFixPlaceholder_historyPrefix (by assumption)
  all_goals try
    have dpatHistory := inferDPatFuel_historyPrefix (by assumption)
  all_goals try
    have ppatHistory := inferPPatFuel_historyPrefix (by assumption)
  all_goals try
    have alignmentHistory := alignTypes_historyPrefix (by assumption)
  all_goals try
    have slotAlignmentHistory := alignAtSlot_historyPrefix (by assumption)
  all_goals try
    have expectedAlignmentHistory :=
      alignExprResultAtExpected_historyPrefix (by assumption)
  all_goals try
    have dualAlignmentHistory := alignDuals_historyPrefix (by assumption)
  all_goals try
    have dualListHistory := alignDualLists_historyPrefix (by assumption)
  all_goals try
    have patternTargetsHistory := alignPatternTargets_historyPrefix
      (by assumption)
  all_goals try
    have bindingAlignmentHistory := alignBindings_historyPrefix
      (by assumption)
  all_goals try
    have patternCtorCapabilityHistory :=
      solvePatternCtorCapability_historyPrefix (by assumption)
  all_goals try
    have skeletonHistory := freshenSkeleton_historyPrefix (by assumption)
  all_goals try
    have recursiveMatcherHistory :=
      recursiveMatcherTemplate_historyPrefix (by assumption)
  all_goals try
    have schemeHistory := instantiateSchemeInState_historyPrefix_of_eq
      (by assumption)
  all_goals try
    have ctorHistory := instantiateCtorInState_historyPrefix_of_eq
      (by assumption)
  all_goals try
    have dualInstanceHistory := instantiateDualInState_historyPrefix_of_eq
      (by assumption)
  all_goals try subst_vars
  all_goals first
    | assumption
    | exact InferState.HistoryPrefix.refl _
    | grind [visit_historyPrefix, finishExpr_historyPrefix,
        recordSelfReference_historyPrefix,
        instantiateSchemeInState_historyPrefix,
        instantiateCtorInState_historyPrefix,
        instantiateDualInState_historyPrefix,
        InferState.historyPrefix_freshTy,
        InferState.historyPrefix_freshCap,
        InferState.historyPrefix_protectMatcherCapability,
        InferState.historyPrefix_protectMatcherCapabilityExcept,
        InferState.historyPrefix_freezeCapabilityExport,
        InferState.historyPrefix_recordEvent,
        InferState.historyPrefix_recordSource,
        alignTypes_historyPrefix,
        alignAtSlot_historyPrefix,
        alignExprResultAtExpected_historyPrefix,
        alignDuals_historyPrefix,
        alignDualLists_historyPrefix,
        alignBindings_historyPrefix,
        alignPatternTargets_historyPrefix,
        solvePatternCtorCapability_historyPrefix,
        runResolvedConstraint_historyPrefix,
        freshenSkeleton_historyPrefix,
        recursiveMatcherTemplate_historyPrefix,
        buildFixPlaceholder_historyPrefix,
        inferPPatFuel_historyPrefix,
        inferDPatFuel_historyPrefix,
        freshTargets_historyPrefix,
        InferState.HistoryPrefix.snd_of_eq,
        InferState.HistoryPrefix.right_congr,
        InferState.HistoryPrefix.refl,
        InferState.HistoryPrefix.trans]

/-- Regression: the empty suffix of a pattern list preserves a nonempty
left-to-right binding context instead of resetting it. -/
theorem inferPatternsFuel_empty_preserves_nonempty_bindings
    (signature : FrozenSig) (context : Context) (parameters : PatternCtx)
    (bindings : MonoCtx) (selfEnv : SelfEnv) (path : SyntaxPath)
    (index fuel : Nat) (state : InferState) (_nonempty : bindings ≠ []) :
    ∃ result,
      inferPatternsFuel fuel.succ signature context parameters bindings
          selfEnv path index [] state = some result ∧
        result.bindings = bindings := by
  exact ⟨⟨[], bindings, state⟩, by simp [inferPatternsFuel], rfl⟩

/-- Same-named fix and argument binders are rejected by the raw traversal. -/
theorem same_named_fix_argument_rejected (signature : FrozenSig) :
    rawInferenceSucceeds signature [] (.fix "f" "f" (.lit 0)) = false := by
  simp [rawInferenceSucceeds, inferRaw, inferenceFuel, exprTraversalFuel,
    inferExprFuel]

/-! ## Producer non-strengthening regression -/

private def protectionSignature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("consumeProducer", {
    capBinders := []
    tyBinders := []
    args := [.matcher (.con "List" [.any]) .int]
    result := .int })]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

private def polymorphicProducer : Scheme :=
  Scheme.close [⟨0⟩] [] (.matcher (.var ⟨0⟩) .int)

/--
An instantiated producer capability cannot be strengthened from a fresh leaf
to `List none` merely because a consumer constructor requests that shape.
-/
theorem polymorphicProducer_strengthening_rejected :
    rawInferenceSucceeds protectionSignature
      [("producer", polymorphicProducer)]
      (.ctor "consumeProducer" [.var "producer"]) = false := by
  native_decide



/-! ## Flexible capability variables of skeleton and clause evidence

Skeleton evidence is built from clause syntax alone and is therefore
variable-free; actual clause evidence only embeds the supplied hole
capabilities; the fallback field demands only carry the shared assignment
skeleton.  These conservation lemmas feed the freshness invariant of the
demand-directed judgments.
-/

mutual

/-- Structural skeleton evidence is variable-free. -/
theorem ppatSkeletonEvidence_fcv {signature : FrozenMatcherSig} :
    ∀ {pattern : PPat} {evidence : Shape.Evidence},
      ppatSkeletonEvidence signature pattern = some evidence →
      evidence.fcv = []
  | .hole, _, h => by
      cases h
      simp [Shape.Evidence.fcv]
  | .wild, _, h => by
      cases h
      simp [Shape.Evidence.fcv]
  | .pval _, _, h => by
      cases h
      simp [Shape.Evidence.fcv]
  | .ctor name patterns, evidence, h => by
      cases hctor : signature.findPatternConstructor? name with
      | none => simp [ppatSkeletonEvidence, hctor] at h
      | some constructor =>
          cases hchildren : ppatSkeletonEvidenceList signature patterns with
          | none => simp [ppatSkeletonEvidence, hctor, hchildren] at h
          | some children =>
              simp only [ppatSkeletonEvidence, hctor, hchildren,
                Option.bind_eq_bind, Option.bind] at h
              have hsub := Projection.projectSignature_fcv h
              rw [ppatSkeletonEvidenceList_fcv hchildren] at hsub
              exact List.subset_nil.mp hsub
  | .tuple patterns, evidence, h => by
      cases hchildren : ppatSkeletonEvidenceList signature patterns with
      | none => simp [ppatSkeletonEvidence, hchildren] at h
      | some children =>
          simp only [ppatSkeletonEvidence, hchildren, Option.bind_eq_bind,
            Option.bind] at h
          cases h
          simp [Shape.Evidence.fcv,
            ppatSkeletonEvidenceList_fcv hchildren]

/-- List form of `ppatSkeletonEvidence_fcv`. -/
theorem ppatSkeletonEvidenceList_fcv {signature : FrozenMatcherSig} :
    ∀ {patterns : List PPat} {evidences : List Shape.Evidence},
      ppatSkeletonEvidenceList signature patterns = some evidences →
      Shape.Evidence.fcvList evidences = []
  | [], _, h => by
      cases h
      simp [Shape.Evidence.fcvList]
  | pattern :: patterns, evidences, h => by
      cases hhead : ppatSkeletonEvidence signature pattern with
      | none => simp [ppatSkeletonEvidenceList, hhead] at h
      | some head =>
          cases htail : ppatSkeletonEvidenceList signature patterns with
          | none => simp [ppatSkeletonEvidenceList, hhead, htail] at h
          | some tail =>
              simp only [ppatSkeletonEvidenceList, hhead, htail,
                Option.bind_eq_bind, Option.bind] at h
              cases h
              simp [Shape.Evidence.fcvList,
                ppatSkeletonEvidence_fcv hhead,
                ppatSkeletonEvidenceList_fcv htail]

end

/-- The pointwise skeleton pass over clauses is variable-free. -/
theorem mapM_ppatSkeletonEvidence_fcv {signature : FrozenMatcherSig} :
    ∀ {clauses : List Clause} {evidences : List Shape.Evidence},
      clauses.mapM
          (fun clause => ppatSkeletonEvidence signature clause.pp) =
        some evidences →
      Shape.Evidence.fcvList evidences = []
  | [], _, h => by
      cases h
      simp [Shape.Evidence.fcvList]
  | clause :: clauses, evidences, h => by
      rw [List.mapM_cons] at h
      cases hhead : ppatSkeletonEvidence signature clause.pp with
      | none => simp [hhead] at h
      | some head =>
          cases htail : clauses.mapM
              (fun clause => ppatSkeletonEvidence signature clause.pp) with
          | none => simp [hhead, htail] at h
          | some tail =>
              simp only [hhead, htail, Option.bind_eq_bind,
                Option.bind, Option.pure_def] at h
              cases h
              simp [Shape.Evidence.fcvList,
                ppatSkeletonEvidence_fcv hhead,
                mapM_ppatSkeletonEvidence_fcv htail]

/-- The recursive matcher skeleton is variable-free. -/
theorem matcherSkeletonEvidence_fcv {signature : FrozenMatcherSig}
    {clauses : List Clause} {evidence : Shape.Evidence}
    (h : matcherSkeletonEvidence signature clauses = some evidence) :
    evidence.fcv = [] := by
  unfold matcherSkeletonEvidence at h
  cases hmap : clauses.mapM
      (fun clause => ppatSkeletonEvidence signature clause.pp) with
  | none => simp [hmap] at h
  | some evidences =>
      simp only [hmap, Option.bind_eq_bind, Option.bind] at h
      have hsub := Shape.mergeAll_fcv h
      rw [mapM_ppatSkeletonEvidence_fcv hmap] at hsub
      exact List.subset_nil.mp hsub

mutual

/-- Actual clause evidence only embeds the supplied hole capabilities, and
the unconsumed suffix only carries supplied variables. -/
theorem clauseEvidenceGo_fcv {signature : FrozenMatcherSig} :
    ∀ {atRoot : Bool} {pattern : PPat} {capabilities : List Cap}
      {evidence : Shape.Evidence} {remaining : List Cap},
      clauseEvidenceGo signature atRoot pattern capabilities =
        some (evidence, remaining) →
      evidence.fcv ⊆ Cap.fcvList capabilities ∧
        Cap.fcvList remaining ⊆ Cap.fcvList capabilities
  | _, .hole, [], _, _, h => nomatch h
  | true, .hole, capability :: capabilities, evidence, remaining, h => by
      simp only [clauseEvidenceGo] at h
      cases h
      constructor
      · intro x mem
        have mem' : x ∈ Shape.Evidence.unseen.fcv := mem
        simp only [Shape.Evidence.fcv] at mem'
        exact nomatch mem'
      · intro x mem
        simp only [Cap.fcvList, List.mem_append]
        exact Or.inr mem
  | false, .hole, capability :: capabilities, evidence, remaining, h => by
      simp only [clauseEvidenceGo] at h
      cases h
      constructor
      · intro x mem
        have mem' : x ∈
            (Shape.ofDelegatedCap signature.observability capability).fcv :=
          mem
        rw [Shape.fcv_ofDelegatedCap] at mem'
        simp only [Cap.fcvList, List.mem_append]
        exact Or.inl mem'
      · intro x mem
        simp only [Cap.fcvList, List.mem_append]
        exact Or.inr mem
  | _, .wild, capabilities, evidence, remaining, h => by
      simp only [clauseEvidenceGo] at h
      cases h
      constructor
      · intro x mem
        simp only [Shape.Evidence.fcv] at mem
        exact nomatch mem
      · exact fun x mem => mem
  | _, .pval _, capabilities, evidence, remaining, h => by
      simp only [clauseEvidenceGo] at h
      cases h
      constructor
      · intro x mem
        simp only [Shape.Evidence.fcv] at mem
        exact nomatch mem
      · exact fun x mem => mem
  | atRoot, .ctor name patterns, capabilities, evidence, remaining, h => by
      cases hctor : signature.findPatternConstructor? name with
      | none => simp [clauseEvidenceGo, hctor] at h
      | some constructor =>
          cases hchildren : clauseEvidenceListGo signature patterns
              capabilities with
          | none => simp [clauseEvidenceGo, hctor, hchildren] at h
          | some result =>
              obtain ⟨children, afterChildren⟩ := result
              cases hproject : Projection.projectClauseSignature
                  constructor children with
              | none =>
                  simp [clauseEvidenceGo, hctor, hchildren, hproject] at h
              | some projected =>
                  simp only [clauseEvidenceGo, hctor, hchildren, hproject,
                    Option.bind_eq_bind, Option.bind] at h
                  cases h
                  obtain ⟨hchildrenFcv, hremaining⟩ :=
                    clauseEvidenceListGo_fcv hchildren
                  exact ⟨fun x mem => hchildrenFcv
                      (Projection.projectClauseSignature_fcv hproject mem),
                    hremaining⟩
  | atRoot, .tuple patterns, capabilities, evidence, remaining, h => by
      cases hchildren : clauseEvidenceListGo signature patterns
          capabilities with
      | none => simp [clauseEvidenceGo, hchildren] at h
      | some result =>
          obtain ⟨children, afterChildren⟩ := result
          simp only [clauseEvidenceGo, hchildren, Option.bind_eq_bind,
            Option.bind] at h
          cases h
          obtain ⟨hchildrenFcv, hremaining⟩ :=
            clauseEvidenceListGo_fcv hchildren
          exact ⟨hchildrenFcv, hremaining⟩

/-- List form of `clauseEvidenceGo_fcv`. -/
theorem clauseEvidenceListGo_fcv {signature : FrozenMatcherSig} :
    ∀ {patterns : List PPat} {capabilities : List Cap}
      {evidences : List Shape.Evidence} {remaining : List Cap},
      clauseEvidenceListGo signature patterns capabilities =
        some (evidences, remaining) →
      Shape.Evidence.fcvList evidences ⊆ Cap.fcvList capabilities ∧
        Cap.fcvList remaining ⊆ Cap.fcvList capabilities
  | [], capabilities, evidences, remaining, h => by
      simp only [clauseEvidenceListGo] at h
      cases h
      constructor
      · intro x mem
        simp only [Shape.Evidence.fcvList] at mem
        exact nomatch mem
      · exact fun x mem => mem
  | pattern :: patterns, capabilities, evidences, remaining, h => by
      cases hhead : clauseEvidenceGo signature false pattern
          capabilities with
      | none => simp [clauseEvidenceListGo, hhead] at h
      | some headResult =>
          obtain ⟨head, afterHead⟩ := headResult
          cases htail : clauseEvidenceListGo signature patterns
              afterHead with
          | none => simp [clauseEvidenceListGo, hhead, htail] at h
          | some tailResult =>
              obtain ⟨tail, afterTail⟩ := tailResult
              simp only [clauseEvidenceListGo, hhead, htail,
                Option.bind_eq_bind, Option.bind] at h
              cases h
              obtain ⟨hheadFcv, hafterHead⟩ := clauseEvidenceGo_fcv hhead
              obtain ⟨htailFcv, hafterTail⟩ := clauseEvidenceListGo_fcv htail
              constructor
              · intro x mem
                simp only [Shape.Evidence.fcvList, List.mem_append] at mem
                rcases mem with hh | ht
                · exact hheadFcv hh
                · exact hafterHead (htailFcv ht)
              · exact fun x mem => hafterHead (hafterTail mem)

end

/-- Complete clause evidence only embeds the supplied hole capabilities. -/
theorem clauseEvidence_fcv {signature : FrozenMatcherSig} {pattern : PPat}
    {holeCapabilities : List Cap} {evidence : Shape.Evidence}
    (h : clauseEvidence signature pattern holeCapabilities =
      some evidence) :
    evidence.fcv ⊆ Cap.fcvList holeCapabilities := by
  unfold clauseEvidence at h
  split at h
  · split at h
    · unfold finishClauseEvidence at h
      split at h
      · rename_i result ev heq
        cases h
        exact (clauseEvidenceGo_fcv heq).1
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- Every collected clause evidence only carries the variables of one hole
ledger entry. -/
theorem collectClauseEvidence_fcv {signature : FrozenMatcherSig} :
    ∀ {clauses : List Clause} {holeLists : List (List Cap)}
      {evidences : List Shape.Evidence},
      collectClauseEvidence signature clauses holeLists = some evidences →
      ∀ varId ∈ Shape.Evidence.fcvList evidences,
        ∃ holes ∈ holeLists, varId ∈ Cap.fcvList holes
  | [], [], _, h => by
      cases h
      intro varId mem
      simp only [Shape.Evidence.fcvList] at mem
      exact nomatch mem
  | clause :: clauses, holes :: holeLists, evidences, h => by
      cases hevidence : clauseEvidence signature clause.pp holes with
      | none => simp [collectClauseEvidence, hevidence] at h
      | some evidence =>
          cases hrest : collectClauseEvidence signature clauses
              holeLists with
          | none => simp [collectClauseEvidence, hevidence, hrest] at h
          | some rest =>
              simp only [collectClauseEvidence, hevidence, hrest,
                Option.bind_eq_bind, Option.bind] at h
              cases h
              intro varId mem
              simp only [Shape.Evidence.fcvList, List.mem_append] at mem
              rcases mem with hh | ht
              · exact ⟨holes, by simp,
                  clauseEvidence_fcv hevidence hh⟩
              · obtain ⟨holes', hmem, hvar⟩ :=
                  collectClauseEvidence_fcv hrest varId ht
                exact ⟨holes', by simp [hmem], hvar⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- Fallback field demands only carry the shared assignment skeleton. -/
theorem patternCtorFieldDemands_fcv
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar}
    {assignments : Projection.Assignments} :
    ∀ {fieldTypes : List Ty} {demands : List (Option Cap)},
      patternCtorFieldDemands observable resultVariables assignments
        fieldTypes = some demands →
      ∀ demand ∈ demands, ∀ capability, demand = some capability →
        capability.fcv ⊆ Projection.assignmentsFcv assignments
  | [], _, h => by
      cases h
      intro demand mem
      exact nomatch mem
  | fieldType :: fieldTypes, demands, h => by
      cases hrelevant : Projection.relevantVars observable resultVariables
          fieldType with
      | none => simp [patternCtorFieldDemands, hrelevant] at h
      | some relevant =>
          cases relevant with
          | nil =>
              cases hrest : patternCtorFieldDemands observable
                  resultVariables assignments fieldTypes with
              | none =>
                  simp [patternCtorFieldDemands, hrelevant, hrest] at h
              | some rest =>
                  simp only [patternCtorFieldDemands, hrelevant, hrest,
                    Option.bind_eq_bind, Option.bind, Option.pure_def] at h
                  cases h
                  intro demand mem capability hdemand
                  rcases List.mem_cons.mp mem with hhead | htail
                  · rw [hhead] at hdemand
                    exact nomatch hdemand
                  · exact patternCtorFieldDemands_fcv hrest demand htail
                      capability hdemand
          | cons headVar tailVars =>
              cases htemplate : Projection.buildResultTemplate observable
                  resultVariables assignments fieldType with
              | none =>
                  simp [patternCtorFieldDemands, hrelevant, htemplate] at h
              | some template =>
                  cases hfinal : Shape.finalize observable template with
                  | none =>
                      simp [patternCtorFieldDemands, hrelevant, htemplate,
                        hfinal] at h
                  | some headCapability =>
                      cases hrest : patternCtorFieldDemands observable
                          resultVariables assignments fieldTypes with
                      | none =>
                          simp [patternCtorFieldDemands, hrelevant,
                            htemplate, hrest] at h
                      | some rest =>
                          simp only [patternCtorFieldDemands, hrelevant,
                            htemplate, hfinal, hrest, Option.bind_eq_bind,
                            Option.bind, Option.pure_def] at h
                          cases h
                          intro demand mem capability hdemand
                          rcases List.mem_cons.mp mem with hhead | htail
                          · rw [hhead] at hdemand
                            cases hdemand
                            intro x xmem
                            exact Projection.buildResultTemplate_fcv
                              htemplate
                              (Shape.finalize_fcv hfinal xmem)
                          · exact patternCtorFieldDemands_fcv hrest demand
                              htail capability hdemand


end Inference
end TypePM
