import TypePM.DemandTypingInferenceSoundnessFixMatcher

/-!
# Pattern-layer slices of executable-to-DD soundness

This module supplies the exact-state alignment bridges and constructor slices
needed by the user-pattern part of the mutual inference soundness proof.  The
lemmas take recursive-family hypotheses as arguments, so the main fuel
induction can use them without duplicating branch-local state bookkeeping.
-/

namespace TypePM
namespace Inference

/-- Exact-state certificate for capability/target dual alignment. -/
def DDAlignDualRun (left right : Dual) (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignDualWithLedger initial.capabilityOrigins initial.prevailing
        left right final.prevailing

/-- Exact-state certificate for pointwise dual-list alignment. -/
def DDAlignDualListRun (left right : List Dual)
    (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignDualListWithLedger initial.capabilityOrigins initial.prevailing
        left right final.prevailing

/-- Exact-state certificate for constructor-field target alignment. -/
def DDAlignPatternTargetsRun (duals : List Dual) (targets : List Ty)
    (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignTargetListWithLedger initial.capabilityOrigins
        initial.prevailing duals targets final.prevailing

/-- Exact-state certificate for entrywise or-pattern binding alignment. -/
def DDAlignBindingsRun (left right : MonoCtx)
    (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignBindingsWithLedger initial.capabilityOrigins initial.prevailing
        left right final.prevailing

/-- Exact-state certificate for consumer-side constructor capability
alignment. -/
def DDAlignCtorCapsRun (children : List Cap) (demands : List (Option Cap))
    (initial final : InferState) : Prop :=
  final.supply = initial.supply ∧
    final.capabilityOrigins = initial.capabilityOrigins ∧
      DDAlignCtorCapsWithLedger initial.capabilityOrigins initial.prevailing
        children demands final.prevailing

/-- Exact-state certificate for pattern-constructor capability inference. -/
def DDPatternCtorCapRun (signature : FrozenSig)
    (entry : PatternCtorScheme signature.observability)
    (children : List Cap) (initial : InferState) (capability : Cap)
    (final : InferState) : Prop :=
  ∃ derived : DDPatternCtorCap signature entry initial.supply
      initial.prevailing children capability final.supply final.prevailing,
    DDPatternCtorCapOrigin signature entry derived initial.capabilityOrigins
      final.capabilityOrigins

/-- Recover the exact origin-safe capability solve underlying one executable
constraint step. -/
private theorem runResolvedConstraint_capEq_exact
    {initial final : InferState} {origin : ConstraintOrigin}
    {left right : Cap}
    (success : runResolvedConstraint initial origin (.capEq left right) =
      some final) :
    ∃ step,
      final = initial.recordSolve step ∧
      step.delta.target = TySubst.id ∧
      OriginSafeExactCapMGU initial.capabilityOrigins left right
        step.delta.cap := by
  unfold runResolvedConstraint at success
  cases stepEq : solveResolvedWithLedger initial.capabilityOrigins
      initial.trace.solves.length origin (.capEq left right) with
  | none => simp [stepEq] at success
  | some step =>
      simp only [stepEq] at success
      have finalEq := Option.some.inj success
      subst final
      rcases solveResolvedWithLedger_capEq_originSafeExactCapMGU stepEq with
        ⟨targetId, exactCap⟩
      exact ⟨step, rfl, targetId, exactCap⟩

/-- Successful executable dual alignment is exactly the corresponding
ledger-aware DD alignment. -/
theorem alignDuals_ddAlignDualRun
    {initial final : InferState} {origin : ConstraintOrigin}
    {left right : Dual}
    (success : alignDuals initial origin left right = some final) :
    DDAlignDualRun left right initial final := by
  unfold alignDuals at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨middle, capSuccess, afterCap⟩
  rcases Option.bind_eq_some_iff.mp afterCap with
    ⟨aligned, targetSuccess, finished⟩
  rcases runResolvedConstraint_capEq_exact capSuccess with
    ⟨step, middleEq, targetId, capExact⟩
  subst middle
  have finalEq := Option.some.inj finished
  subst final
  rcases alignTypes_ddAlignTypesRun targetSuccess with
    ⟨supplyEq, ledgerEq, targetAligned⟩
  have middleSupply : (initial.recordSolve step).supply = initial.supply := rfl
  have middleLedger :
      (initial.recordSolve step).capabilityOrigins =
        initial.capabilityOrigins := rfl
  rw [middleSupply] at supplyEq
  rw [middleLedger] at ledgerEq targetAligned
  refine ⟨?_, ?_, ?_⟩
  · exact supplyEq
  · exact ledgerEq
  · have stepEq : step.delta = ⟨step.delta.cap, TySubst.id⟩ := by
      rw [← targetId]
    rw [InferState.prevailing_recordSolve, stepEq] at targetAligned
    exact
      (DDAlignDualWithLedger.mk capExact targetAligned)

/-- Successful pointwise dual-list traversal reconstructs its DD list
alignment in source order. -/
theorem alignDualLists_ddAlignDualListRun
    {initial final : InferState} {origin : ConstraintOrigin}
    {left right : List Dual}
    (success : alignDualLists initial origin left right = some final) :
    DDAlignDualListRun left right initial final := by
  induction left generalizing right initial with
  | nil =>
      cases right with
      | nil =>
          simp only [alignDualLists, Option.some.injEq] at success
          subst final
          exact ⟨rfl, rfl, .nil⟩
      | cons head tail => simp [alignDualLists] at success
  | cons head tail induction =>
      cases right with
      | nil => simp [alignDualLists] at success
      | cons rightHead rightTail =>
          simp only [alignDualLists] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, headEq, tailEq⟩
          have headRun := alignDuals_ddAlignDualRun headEq
          have tailRun := induction tailEq
          rcases headRun with ⟨headSupply, headLedger, headDD⟩
          rcases tailRun with ⟨tailSupply, tailLedger, tailDD⟩
          rw [headLedger] at tailDD
          refine ⟨tailSupply.trans headSupply, tailLedger.trans headLedger,
            ?_⟩
          exact DDAlignDualListWithLedger.cons headDD tailDD

/-- Successful constructor-field target alignment reconstructs the
ledger-aware target-list relation. -/
theorem alignPatternTargets_ddAlignPatternTargetsRun
    {initial final : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets initial origin duals targets = some final) :
    DDAlignPatternTargetsRun duals targets initial final := by
  induction duals generalizing targets initial with
  | nil =>
      cases targets with
      | nil =>
          simp only [alignPatternTargets, Option.some.injEq] at success
          subst final
          exact ⟨rfl, rfl, .nil⟩
      | cons head tail => simp [alignPatternTargets] at success
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨middle, headEq, tailEq⟩
          rcases alignTypes_ddAlignTypesRun headEq with
            ⟨headSupply, headLedger, headDD⟩
          rcases induction tailEq with
            ⟨tailSupply, tailLedger, tailDD⟩
          rw [headLedger] at tailDD
          refine ⟨tailSupply.trans headSupply, tailLedger.trans headLedger,
            ?_⟩
          exact DDAlignTargetListWithLedger.cons headDD tailDD

/-- Successful binding-context alignment reconstructs its origin-safe DD
relation, including the executable positional name check. -/
theorem alignBindings_ddAlignBindingsRun
    {initial final : InferState} {origin : ConstraintOrigin}
    {left right : MonoCtx}
    (success : alignBindings initial origin left right = some final) :
    DDAlignBindingsRun left right initial final := by
  induction left generalizing right initial with
  | nil =>
      cases right with
      | nil =>
          simp only [alignBindings, Option.some.injEq] at success
          subst final
          exact ⟨rfl, rfl, .nil⟩
      | cons head tail => simp [alignBindings] at success
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp [alignBindings] at success
      | cons rightHead rightTail =>
          simp only [alignBindings] at success
          split at success
          · rename_i namesEq
            rcases Option.bind_eq_some_iff.mp success with
              ⟨middle, headEq, tailEq⟩
            rcases alignTypes_ddAlignTypesRun headEq with
              ⟨headSupply, headLedger, headDD⟩
            rcases induction tailEq with
              ⟨tailSupply, tailLedger, tailDD⟩
            rw [headLedger] at tailDD
            refine ⟨tailSupply.trans headSupply,
              tailLedger.trans headLedger, ?_⟩
            exact DDAlignBindingsWithLedger.cons namesEq headDD tailDD
          · contradiction

/-- Successful constructor-capability alignment reconstructs its exact
ledger-aware list relation. -/
theorem alignPatternCtorCapabilities_ddAlignCtorCapsRun
    {initial final : InferState} {origin : ConstraintOrigin}
    {children : List Cap} {demands : List (Option Cap)}
    (success : alignPatternCtorCapabilities initial origin children demands =
      some final) :
    DDAlignCtorCapsRun children demands initial final := by
  induction children generalizing demands initial with
  | nil =>
      cases demands with
      | nil =>
          simp only [alignPatternCtorCapabilities, Option.some.injEq]
            at success
          subst final
          exact ⟨rfl, rfl, .nil⟩
      | cons demand demands =>
          simp [alignPatternCtorCapabilities] at success
  | cons child children induction =>
      cases demands with
      | nil => simp [alignPatternCtorCapabilities] at success
      | cons demand demands =>
          cases demand with
          | none =>
              simp only [alignPatternCtorCapabilities] at success
              rcases induction success with ⟨supplyEq, ledgerEq, tail⟩
              exact ⟨supplyEq, ledgerEq,
                DDAlignCtorCapsWithLedger.skip tail⟩
          | some expected =>
              simp only [alignPatternCtorCapabilities] at success
              rcases Option.bind_eq_some_iff.mp success with
                ⟨middle, headEq, tailEq⟩
              rcases runResolvedConstraint_capEq_exact headEq with
                ⟨step, middleEq, targetId, exactCap⟩
              subst middle
              rcases induction tailEq with
                ⟨supplyEq, ledgerEq, tail⟩
              have middleSupply :
                  (initial.recordSolve step).supply = initial.supply := rfl
              have middleLedger :
                  (initial.recordSolve step).capabilityOrigins =
                    initial.capabilityOrigins := rfl
              rw [middleSupply] at supplyEq
              rw [middleLedger] at ledgerEq tail
              have stepEq : step.delta =
                  ⟨step.delta.cap, TySubst.id⟩ := by
                rw [← targetId]
              rw [InferState.prevailing_recordSolve, stepEq] at tail
              exact ⟨supplyEq, ledgerEq,
                DDAlignCtorCapsWithLedger.solve exactCap tail⟩

/-- The executable pattern-constructor capability solver agrees with its
pure supply-indexed DD relation in both projection and fallback branches. -/
theorem solvePatternCtorCapability_ddPatternCtorCapRun
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {origin : ConstraintOrigin} {children : List Cap}
    {initial final : InferState} {capability : Cap}
    (success : solvePatternCtorCapability signature entry origin children
      initial = some (capability, final)) :
    DDPatternCtorCapRun signature entry children initial capability final := by
  unfold DDPatternCtorCapRun
  unfold solvePatternCtorCapability at success
  simp only at success
  split at success
  · rename_i projected projectionEq
    rcases freshenSkeleton_supplyExact success with
      ⟨freshened, prevailingEq, ledgerEq⟩
    rw [prevailingEq, ledgerEq]
    exact ⟨DDPatternCtorCap.project projectionEq freshened,
      DDPatternCtorCapOrigin.project projectionEq freshened⟩
  · rename_i projectionEq
    rcases Option.bind_eq_some_iff.mp success with
      ⟨resultVariables, resultVariablesEq, rest⟩
    let uniqueVariables := resultVariables.eraseDups
    let allocated :=
      freshPatternCtorAssignments origin uniqueVariables initial
    rcases allocatedEq : allocated with ⟨assignments, allocatedState⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨demands, demandsEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨alignedState, alignmentEq, rest⟩
    rcases Option.bind_eq_some_iff.mp rest with
      ⟨projected, projectionHit, skeletonEq⟩
    have allocationEq :
        freshPatternCtorAssignments origin uniqueVariables initial =
          (assignments, allocatedState) := by
      simpa [allocated] using allocatedEq
    rw [allocationEq] at alignmentEq
    have demandsEqActual : patternCtorFieldDemands signature.observability
        uniqueVariables assignments entry.projection.fieldTypes =
          some demands := by
      simpa [uniqueVariables, allocationEq] using demandsEq
    have allocationFacts :=
      freshPatternCtorAssignments_supplyExact origin uniqueVariables initial
    simp only [allocationEq] at allocationFacts
    rcases allocationFacts with
      ⟨assignmentsEq, allocatedSupply, allocatedPrevailing,
        allocatedLedger⟩
    rcases alignPatternCtorCapabilities_ddAlignCtorCapsRun alignmentEq with
      ⟨alignedSupply, alignedLedger, alignedDD⟩
    rcases freshenSkeleton_supplyExact skeletonEq with
      ⟨freshened, finalPrevailing, finalLedger⟩
    have alignedDD' : DDAlignCtorCapsWithLedger
        (DDLedger.markCapRange initial.capabilityOrigins initial.supply
          (patternCtorAssignmentsSupply uniqueVariables initial.supply).2)
        initial.prevailing children demands alignedState.prevailing := by
      rw [← allocatedSupply, ← allocatedLedger,
        ← allocatedPrevailing]
      exact alignedDD
    have demandsEq' : patternCtorFieldDemands signature.observability
        uniqueVariables
        (patternCtorAssignmentsSupply uniqueVariables initial.supply).1
        entry.projection.fieldTypes = some demands := by
      rw [← assignmentsEq]
      exact demandsEqActual
    have freshened' : freshenSkeletonSupply signature.observability projected
        (patternCtorAssignmentsSupply uniqueVariables initial.supply).2 =
          some (capability, final.supply) := by
      rw [← allocatedSupply, ← alignedSupply]
      exact freshened
    have finalPrevailing' : final.prevailing = alignedState.prevailing :=
      finalPrevailing
    have finalLedger' : final.capabilityOrigins =
        DDLedger.markCapRange
          (DDLedger.markCapRange initial.capabilityOrigins initial.supply
            (patternCtorAssignmentsSupply uniqueVariables initial.supply).2)
          (patternCtorAssignmentsSupply uniqueVariables initial.supply).2
          final.supply := by
      rw [finalLedger, alignedLedger, allocatedLedger,
        alignedSupply, allocatedSupply]
    rw [finalPrevailing', finalLedger']
    exact ⟨DDPatternCtorCap.fallback projectionEq resultVariablesEq
        demandsEq' alignedDD'.erase projectionHit freshened',
      DDPatternCtorCapOrigin.fallback projectionEq resultVariablesEq
        demandsEq' alignedDD' projectionHit freshened'⟩

@[simp] theorem instantiateDualInState_value
    (signature : FrozenSig) (rawContext : Context)
    (rawParameters : PatternCtx) (rawBindings : MonoCtx)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (state : InferState) (scheme : DualScheme) :
    (instantiateDualInState signature rawContext rawParameters rawBindings
      context parameters bindings state scheme).1 =
        (InferenceBase.instantiateDualScheme state.supply scheme).value :=
  rfl

@[simp] theorem instantiateDualInState_supply
    (signature : FrozenSig) (rawContext : Context)
    (rawParameters : PatternCtx) (rawBindings : MonoCtx)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (state : InferState) (scheme : DualScheme) :
    (instantiateDualInState signature rawContext rawParameters rawBindings
      context parameters bindings state scheme).2.supply =
        (InferenceBase.instantiateDualScheme state.supply scheme).supply :=
  rfl

@[simp] theorem instantiateDualInState_prevailing
    (signature : FrozenSig) (rawContext : Context)
    (rawParameters : PatternCtx) (rawBindings : MonoCtx)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (state : InferState) (scheme : DualScheme) :
    (instantiateDualInState signature rawContext rawParameters rawBindings
      context parameters bindings state scheme).2.prevailing =
        state.prevailing :=
  rfl

@[simp] theorem instantiateDualInState_capabilityOrigins
    (signature : FrozenSig) (rawContext : Context)
    (rawParameters : PatternCtx) (rawBindings : MonoCtx)
    (context : Context) (parameters : PatternCtx) (bindings : MonoCtx)
    (state : InferState) (scheme : DualScheme) :
    (instantiateDualInState signature rawContext rawParameters rawBindings
      context parameters bindings state scheme).2.capabilityOrigins =
        DDLedger.markDualInstance state.capabilityOrigins state.supply
          scheme :=
  rfl

/-! ## Recursive user-pattern constructor slices -/

/-- The and-pattern branch composes its two recursive pattern runs and the
single dual-alignment cut. -/
theorem inferPatternFuel_pand_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {left right : Pattern} {initial : InferState}
    {result : PatternResult}
    (leftSound : ∀ leftResult : PatternResult,
      inferPatternFuel fuel signature context parameters bindings selfEnv
        (0 :: path) left (visit initial .patternAnd path) = some leftResult →
      DDPatternRun signature context parameters bindings left
        (visit initial .patternAnd path) leftResult)
    (rightSound : ∀ (leftResult rightResult : PatternResult),
      inferPatternFuel fuel signature context parameters leftResult.bindings
        selfEnv (1 :: path) right leftResult.state = some rightResult →
      DDPatternRun signature context parameters leftResult.bindings right
        leftResult.state rightResult)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pand left right) initial = some result) :
    DDPatternRun signature context parameters bindings (.pand left right)
      initial result := by
  cases leftEq : inferPatternFuel fuel signature context parameters bindings
      selfEnv (0 :: path) left (visit initial .patternAnd path) with
  | none => simp [inferPatternFuel, leftEq] at success
  | some leftResult =>
      cases rightEq : inferPatternFuel fuel signature context parameters
          leftResult.bindings selfEnv (1 :: path) right leftResult.state with
      | none => simp [inferPatternFuel, leftEq, rightEq] at success
      | some rightResult =>
          cases alignedEq : alignDuals rightResult.state
              (freshOrigin .pattern path "pattern-and") leftResult.dual
              rightResult.dual with
          | none =>
              simp [inferPatternFuel, leftEq, rightEq, alignedEq] at success
          | some final =>
              simp only [inferPatternFuel, leftEq, rightEq, alignedEq,
                Option.some.injEq] at success
              subst result
              rcases leftSound leftResult leftEq with
                ⟨leftRaw, leftOrigin⟩
              rcases rightSound leftResult rightResult rightEq with
                ⟨rightRaw, rightOrigin⟩
              rcases alignDuals_ddAlignDualRun alignedEq with
                ⟨supplyEq, ledgerEq, aligned⟩
              simp only [visit, InferState.recordEvent_supply,
                InferState.prevailing_recordEvent,
                InferState.recordEvent_capabilityOrigins] at leftRaw leftOrigin
              change ∃ derived : DDPattern signature initial.supply
                  initial.prevailing context parameters bindings
                  (.pand left right) leftResult.dual rightResult.bindings
                  final.supply final.prevailing,
                DDPatternOrigin signature derived initial.capabilityOrigins
                  final.capabilityOrigins
              rw [supplyEq, ledgerEq]
              exact ⟨DDPattern.pand leftRaw rightRaw aligned.erase,
                DDPatternOrigin.pand leftOrigin rightOrigin aligned⟩

/-- The or-pattern branch additionally aligns the independently accumulated
binder contexts after aligning the alternative duals. -/
theorem inferPatternFuel_por_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {left right : Pattern} {initial : InferState}
    {result : PatternResult}
    (leftSound : ∀ leftResult : PatternResult,
      inferPatternFuel fuel signature context parameters bindings selfEnv
        (0 :: path) left (visit initial .patternOr path) = some leftResult →
      DDPatternRun signature context parameters bindings left
        (visit initial .patternOr path) leftResult)
    (rightSound : ∀ (leftResult rightResult : PatternResult),
      inferPatternFuel fuel signature context parameters bindings selfEnv
        (1 :: path) right leftResult.state = some rightResult →
      DDPatternRun signature context parameters bindings right
        leftResult.state rightResult)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.por left right) initial = some result) :
    DDPatternRun signature context parameters bindings (.por left right)
      initial result := by
  cases leftEq : inferPatternFuel fuel signature context parameters bindings
      selfEnv (0 :: path) left (visit initial .patternOr path) with
  | none => simp [inferPatternFuel, leftEq] at success
  | some leftResult =>
      cases rightEq : inferPatternFuel fuel signature context parameters
          bindings selfEnv (1 :: path) right leftResult.state with
      | none => simp [inferPatternFuel, leftEq, rightEq] at success
      | some rightResult =>
          cases dualEq : alignDuals rightResult.state
              (freshOrigin .pattern path "pattern-or") leftResult.dual
              rightResult.dual with
          | none => simp [inferPatternFuel, leftEq, rightEq, dualEq] at success
          | some dualFinal =>
              cases bindingsEq : alignBindings dualFinal
                  (freshOrigin .pattern path "pattern-or-bindings")
                  leftResult.bindings rightResult.bindings with
              | none =>
                  simp [inferPatternFuel, leftEq, rightEq, dualEq,
                    bindingsEq] at success
              | some final =>
                  simp only [inferPatternFuel, leftEq, rightEq, dualEq,
                    bindingsEq, Option.some.injEq] at success
                  subst result
                  rcases leftSound leftResult leftEq with
                    ⟨leftRaw, leftOrigin⟩
                  rcases rightSound leftResult rightResult rightEq with
                    ⟨rightRaw, rightOrigin⟩
                  rcases alignDuals_ddAlignDualRun dualEq with
                    ⟨dualSupply, dualLedger, dualAligned⟩
                  rcases alignBindings_ddAlignBindingsRun bindingsEq with
                    ⟨bindingsSupply, bindingsLedger, bindingsAligned⟩
                  simp only [visit, InferState.recordEvent_supply,
                    InferState.prevailing_recordEvent,
                    InferState.recordEvent_capabilityOrigins]
                    at leftRaw leftOrigin
                  rw [dualLedger] at bindingsAligned
                  have finalSupply : final.supply = rightResult.state.supply :=
                    bindingsSupply.trans dualSupply
                  have finalLedger :
                      final.capabilityOrigins =
                        rightResult.state.capabilityOrigins :=
                    bindingsLedger.trans dualLedger
                  change ∃ derived : DDPattern signature initial.supply
                      initial.prevailing context parameters bindings
                      (.por left right) leftResult.dual leftResult.bindings
                      final.supply final.prevailing,
                    DDPatternOrigin signature derived initial.capabilityOrigins
                      final.capabilityOrigins
                  rw [finalSupply, finalLedger]
                  exact ⟨DDPattern.por leftRaw rightRaw dualAligned.erase
                      bindingsAligned.erase,
                    DDPatternOrigin.por leftOrigin rightOrigin dualAligned
                      bindingsAligned⟩

/-- Pattern-function application instantiates its dual scheme, traverses the
arguments, and aligns the produced dual list with the instantiated domains. -/
theorem inferPatternFuel_papp_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {patterns : List Pattern}
    {initial : InferState} {result : PatternResult}
    (childrenSound : ∀ (scheme : DualScheme) (children : PatternsResult),
      let normalizedContext := context.applySubst initial.prevailing
      let normalizedParameters := parameters.applySubst initial.prevailing
      let normalizedBindings := bindings.applySubst initial.prevailing
      let instantiated := instantiateDualInState signature context parameters
        bindings normalizedContext normalizedParameters normalizedBindings
          initial scheme
      inferPatternsFuel fuel signature context parameters bindings selfEnv path
        0 patterns (visit instantiated.2 .patternApp path) = some children →
      DDPatternsRun signature context parameters bindings patterns
        (visit instantiated.2 .patternApp path) children)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.papp name patterns) initial = some result) :
    DDPatternRun signature context parameters bindings (.papp name patterns)
      initial result := by
  cases lookup : signature.findPatternFun name with
  | none => simp [inferPatternFuel, lookup] at success
  | some scheme =>
      let normalizedContext := context.applySubst initial.prevailing
      let normalizedParameters := parameters.applySubst initial.prevailing
      let normalizedBindings := bindings.applySubst initial.prevailing
      let instantiated := instantiateDualInState signature context parameters
        bindings normalizedContext normalizedParameters normalizedBindings
          initial scheme
      cases childrenEq : inferPatternsFuel fuel signature context parameters
          bindings selfEnv path 0 patterns
          (visit instantiated.2 .patternApp path) with
      | none =>
          simp [inferPatternFuel, lookup, normalizedContext,
            normalizedParameters, normalizedBindings, instantiated,
            childrenEq] at success
      | some children =>
          cases alignedEq : alignDualLists children.state
              (freshOrigin .pattern path "pattern-function-arguments")
              children.duals instantiated.1.1 with
          | none =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateDualInState]
                at actualAlignedEq
              have actualSuccess := success
              simp only [inferPatternFuel, lookup, normalizedContext,
                normalizedParameters, normalizedBindings, instantiated,
                childrenEq] at actualSuccess
              simp only [instantiateDualInState] at actualSuccess
              simp [actualAlignedEq] at actualSuccess
          | some final =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateDualInState]
                at actualAlignedEq
              have actualSuccess := success
              simp only [inferPatternFuel, lookup, normalizedContext,
                normalizedParameters, normalizedBindings, instantiated,
                childrenEq] at actualSuccess
              simp only [instantiateDualInState] at actualSuccess
              simp only [actualAlignedEq, Option.some.injEq] at actualSuccess
              subst result
              rcases childrenSound scheme children childrenEq with
                ⟨childrenRaw, childrenOrigin⟩
              rcases alignDualLists_ddAlignDualListRun alignedEq with
                ⟨supplyEq, ledgerEq, aligned⟩
              simp only [visit, InferState.recordEvent_supply,
                InferState.prevailing_recordEvent,
                InferState.recordEvent_capabilityOrigins,
                instantiateDualInState_supply,
                instantiateDualInState_prevailing,
                instantiateDualInState_capabilityOrigins]
                at childrenRaw childrenOrigin
              change ∃ derived : DDPattern signature initial.supply
                  initial.prevailing context parameters bindings
                  (.papp name patterns)
                  (InferenceBase.instantiateDualScheme initial.supply
                    scheme).value.2 children.bindings final.supply
                  final.prevailing,
                DDPatternOrigin signature derived initial.capabilityOrigins
                  final.capabilityOrigins
              rw [supplyEq, ledgerEq]
              exact ⟨DDPattern.papp lookup childrenRaw aligned.erase,
                DDPatternOrigin.papp lookup childrenOrigin aligned⟩

/-- Pattern-constructor synthesis reconstructs constructor instantiation,
field target alignment, consumer capability solving, the local compatibility
check, and the final export freeze at their exact executable cuts. -/
theorem inferPatternFuel_pctor_ddPatternRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {patterns : List Pattern}
    {initial : InferState} {result : PatternResult}
    (childrenSound : ∀
        (entry : PatternCtorScheme signature.observability)
        (children : PatternsResult),
      let instantiated := instantiateCtorInState initial entry.scheme
      inferPatternsFuel fuel signature context parameters bindings selfEnv path
        0 patterns (visit instantiated.2 .patternCtor path) = some children →
      DDPatternsRun signature context parameters bindings patterns
        (visit instantiated.2 .patternCtor path) children)
    (success : inferPatternFuel (fuel + 1) signature context parameters
      bindings selfEnv path (.pctor name patterns) initial = some result) :
    DDPatternRun signature context parameters bindings (.pctor name patterns)
      initial result := by
  cases lookup : signature.findPatternCtor name with
  | none => simp [inferPatternFuel, lookup] at success
  | some entry =>
      let instantiated := instantiateCtorInState initial entry.scheme
      cases childrenEq : inferPatternsFuel fuel signature context parameters
          bindings selfEnv path 0 patterns
          (visit instantiated.2 .patternCtor path) with
      | none =>
          simp [inferPatternFuel, lookup, instantiated, childrenEq] at success
      | some children =>
          cases targetsEq : alignPatternTargets children.state
              (freshOrigin .pattern path "pattern-constructor-fields")
              children.duals instantiated.1.1 with
          | none =>
              have actualTargetsEq := targetsEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualTargetsEq
              simp [inferPatternFuel, lookup, instantiated, childrenEq,
                actualTargetsEq] at success
          | some targetsFinal =>
              let childCaps := children.duals.map Dual.cap
              cases capabilityEq : solvePatternCtorCapability signature entry
                  (freshOrigin .pattern path
                    "pattern-constructor-capability")
                  childCaps targetsFinal with
              | none =>
                  have actualTargetsEq := targetsEq
                  simp only [instantiated, instantiateCtorInState_target]
                    at actualTargetsEq
                  simp [inferPatternFuel, lookup, instantiated, childrenEq,
                    actualTargetsEq, childCaps, capabilityEq] at success
              | some solved =>
                  rcases solved with ⟨capability, solvedState⟩
                  let resolvedChildren := childCaps.map fun child =>
                    child.apply solvedState.prevailing.cap
                  let resolvedCapability :=
                    capability.apply solvedState.prevailing.cap
                  by_cases compatible :
                      capCompatibleCheck entry resolvedChildren
                        resolvedCapability = true
                  · let resultTarget :=
                      (InferenceBase.instantiateCtorScheme initial.supply
                        entry.scheme).value.2
                    let exportPayload := capabilityExportPayload [capability]
                      (resultTarget :: children.bindings.map fun binding =>
                        binding.2)
                    let frozen := solvedState.freezeCapabilityExport
                      (freshCapImages initial.supply entry.scheme.capBinders)
                      exportPayload
                    let compatibilityEvent :=
                      TraceEvent.patternCtorCompatibility
                        frozen.trace.solves.length name childCaps capability
                    let inferredEvent := TraceEvent.inferredPattern
                      (.pctor name patterns) ⟨capability, resultTarget⟩
                      children.bindings path
                    have actualTargetsEq := targetsEq
                    simp only [instantiated, instantiateCtorInState_target]
                      at actualTargetsEq
                    have resultEq : some ⟨⟨capability, resultTarget⟩,
                        children.bindings,
                        (frozen.recordEvent compatibilityEvent).recordEvent
                          inferredEvent⟩ = some result := by
                      have branchSuccess := success
                      simp [inferPatternFuel, lookup, instantiated,
                        childrenEq, actualTargetsEq, childCaps, capabilityEq,
                        List.map_map, Function.comp_def] at branchSuccess
                      exact congrArg some branchSuccess.2
                    have exactResult := Option.some.inj resultEq
                    subst result
                    rcases childrenSound entry children childrenEq with
                      ⟨childrenRaw, childrenOrigin⟩
                    simp only [visit,
                      instantiateCtorInState_supply,
                      instantiateCtorInState_prevailing,
                      instantiateCtorInState_capabilityOrigins,
                      InferState.recordEvent_supply,
                      InferState.prevailing_recordEvent,
                      InferState.recordEvent_capabilityOrigins]
                      at childrenRaw childrenOrigin
                    rcases alignPatternTargets_ddAlignPatternTargetsRun
                        targetsEq with
                      ⟨targetsSupply, targetsLedger, targetsAligned⟩
                    rcases solvePatternCtorCapability_ddPatternCtorCapRun
                        capabilityEq with
                      ⟨capRaw, capOrigin⟩
                    have capAt :
                        ∃ raw : DDPatternCtorCap signature entry
                            children.state.supply targetsFinal.prevailing
                            childCaps capability solvedState.supply
                            solvedState.prevailing,
                          DDPatternCtorCapOrigin signature entry raw
                            children.state.capabilityOrigins
                            solvedState.capabilityOrigins := by
                      rw [← targetsSupply, ← targetsLedger]
                      exact ⟨capRaw, capOrigin⟩
                    rcases capAt with ⟨capRaw', capOrigin'⟩
                    simp only [DDPatternRun, frozen, compatibilityEvent,
                      inferredEvent, InferState.recordEvent_supply,
                      InferState.prevailing_recordEvent,
                      InferState.recordEvent_capabilityOrigins,
                      InferState.freezeCapabilityExport_supply,
                      InferState.freezeCapabilityExport_prevailing,
                      InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
                    exact ⟨DDPattern.pctor lookup childrenRaw
                        targetsAligned.erase capRaw' compatible,
                      DDPatternOrigin.pctor lookup childrenOrigin
                        targetsAligned capOrigin' compatible⟩
                  · have actualTargetsEq := targetsEq
                    simp only [instantiated, instantiateCtorInState_target]
                      at actualTargetsEq
                    have actualCompatible : ¬ capCompatibleCheck entry
                        (children.duals.map fun dual =>
                          dual.cap.apply solvedState.prevailing.cap)
                        (capability.apply solvedState.prevailing.cap) =
                          true := by
                      simpa [resolvedChildren, resolvedCapability, childCaps,
                        List.map_map, Function.comp_def] using compatible
                    have branchSuccess := success
                    simp [inferPatternFuel, lookup, instantiated,
                      childrenEq, actualTargetsEq, childCaps, capabilityEq,
                      List.map_map, Function.comp_def] at branchSuccess
                    exact (actualCompatible branchSuccess.1).elim

/-! ## Primitive/data pattern and clause exact-state packages -/

def DDPPatRun (signature : FrozenSig) (pattern : PPat) (expected : Ty)
    (initial : InferState) (result : PPatResult) : Prop :=
  result.target = expected ∧
    ∃ derived : DDPPat signature initial.supply initial.prevailing pattern
        expected result.holes result.bindings result.state.supply
        result.state.prevailing,
      DDPPatOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

def DDPPatsRun (signature : FrozenSig) (patterns : List PPat)
    (targets : List Ty) (initial : InferState) (result : PPatsResult) : Prop :=
  result.targets = targets ∧
    ∃ derived : DDPPats signature initial.supply initial.prevailing patterns
        targets result.holes result.bindings result.state.supply
        result.state.prevailing,
      DDPPatsOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

def DDDPatRun (signature : FrozenSig) (pattern : DPat) (expected : Ty)
    (initial : InferState) (result : DPatResult) : Prop :=
  result.target = expected ∧
    ∃ derived : DDDPat signature initial.supply initial.prevailing pattern
        expected result.bindings result.state.supply result.state.prevailing,
      DDDPatOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

def DDDPatsRun (signature : FrozenSig) (patterns : List DPat)
    (targets : List Ty) (initial : InferState) (result : DPatsResult) : Prop :=
  result.targets = targets ∧
    ∃ derived : DDDPats signature initial.supply initial.prevailing patterns
        targets result.bindings result.state.supply result.state.prevailing,
      DDDPatsOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

def DDArmsRun (signature : FrozenSig) (context : Context)
    (ppBindings : MonoCtx) (arms : List Arm) (clauseTarget bodyTarget : Ty)
    (initial final : InferState) : Prop :=
  ∃ derived : DDArms signature initial.supply initial.prevailing context
      ppBindings arms clauseTarget bodyTarget final.supply final.prevailing,
    DDArmsOrigin signature derived initial.capabilityOrigins
      final.capabilityOrigins

def DDClauseRun (signature : FrozenSig) (context : Context)
    (clause : Clause) (sharedTarget : Ty) (initial : InferState)
    (result : ClauseResult) : Prop :=
  result.target = sharedTarget ∧
    ∃ derived : DDClause signature initial.supply initial.prevailing context
        clause sharedTarget result.rawHoles result.state.supply
        result.state.prevailing,
      DDClauseOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

def DDClausesRun (signature : FrozenSig) (context : Context)
    (clauses : List Clause) (sharedTarget : Ty) (initial : InferState)
    (result : ClausesResult) : Prop :=
  result.target = sharedTarget ∧
    ∃ derived : DDClauses signature initial.supply initial.prevailing context
        clauses sharedTarget result.rawHoleLists result.state.supply
        result.state.prevailing,
      DDClausesOrigin signature derived initial.capabilityOrigins
        result.state.capabilityOrigins

theorem inferPPatFuel_hole_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {expected : Ty} {initial : InferState} {result : PPatResult}
    (success : inferPPatFuel (fuel + 1) signature path .hole expected initial =
      some result) :
    DDPPatRun signature .hole expected initial result := by
  simp only [inferPPatFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDPPat.hole, DDPPatOrigin.hole⟩

theorem inferPPatFuel_wild_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {expected : Ty} {initial : InferState} {result : PPatResult}
    (success : inferPPatFuel (fuel + 1) signature path .wild expected initial =
      some result) :
    DDPPatRun signature .wild expected initial result := by
  simp only [inferPPatFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDPPat.wild, DDPPatOrigin.wild⟩

theorem inferPPatFuel_pval_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {name : String} {expected : Ty} {initial : InferState}
    {result : PPatResult}
    (success : inferPPatFuel (fuel + 1) signature path (.pval name) expected
      initial = some result) :
    DDPPatRun signature (.pval name) expected initial result := by
  simp only [inferPPatFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDPPat.pval, DDPPatOrigin.pval⟩

theorem inferDPatFuel_var_ddDPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {name : String} {expected : Ty} {initial : InferState}
    {result : DPatResult}
    (success : inferDPatFuel (fuel + 1) signature path (.var name) expected
      initial = some result) :
    DDDPatRun signature (.var name) expected initial result := by
  simp only [inferDPatFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDDPat.var, DDDPatOrigin.var⟩

theorem inferDPatFuel_wild_ddDPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {expected : Ty} {initial : InferState} {result : DPatResult}
    (success : inferDPatFuel (fuel + 1) signature path .wild expected initial =
      some result) :
    DDDPatRun signature .wild expected initial result := by
  simp only [inferDPatFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDDPat.wild, DDDPatOrigin.wild⟩

/-- Stateful target allocation has the same values and final supply as its
pure supply-indexed twin, and changes neither substitution nor origin ledger. -/
theorem freshTargets_eq_freshTargetsSupply
    (count : Nat) (initial : InferState) (origin : ConstraintOrigin) :
    let allocated := freshTargets initial origin count
    allocated.1 = (freshTargetsSupply count initial.supply).1 ∧
      allocated.2.supply = (freshTargetsSupply count initial.supply).2 ∧
      allocated.2.prevailing = initial.prevailing ∧
      allocated.2.capabilityOrigins = initial.capabilityOrigins := by
  induction count generalizing initial with
  | zero => simp [freshTargets, freshTargetsSupply]
  | succ count induction =>
      simp only [freshTargets, freshTargetsSupply]
      let next := (initial.freshTy origin).2
      have supplyStep : (InferenceBase.freshTyMeta initial.supply).2 =
          { initial.supply with nextTy := initial.supply.nextTy + 1 } := by
        cases initial.supply
        rfl
      have nextSupply : next.supply =
          { initial.supply with nextTy := initial.supply.nextTy + 1 } := by
        simp [next, InferState.freshTy, supplyStep]
      have nextPrevailing : next.prevailing = initial.prevailing := by
        rfl
      have nextLedger :
          next.capabilityOrigins = initial.capabilityOrigins := by
        rfl
      rcases induction next with
        ⟨targetsEq, finalSupply, finalPrevailing, finalLedger⟩
      rw [nextSupply] at targetsEq finalSupply
      rw [nextPrevailing] at finalPrevailing
      rw [nextLedger] at finalLedger
      exact ⟨congrArg (Ty.var initial.supply.nextTy :: ·) targetsEq,
        finalSupply, finalPrevailing, finalLedger⟩

/-- Primitive-pattern constructor reconstruction: instantiate, align the
result target, traverse fields, and freeze the constructor export ledger. -/
theorem inferPPatFuel_ctor_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath} {name : String}
    {patterns : List PPat} {expected : Ty} {initial : InferState}
    {result : PPatResult}
    (childrenSound : ∀
        (entry : PatternCtorScheme signature.observability)
        (aligned : InferState) (children : PPatsResult),
      inferPPatsFuel fuel signature path 0 patterns
        (InferenceBase.instantiateCtorScheme initial.supply
          entry.scheme).value.1 aligned = some children →
      DDPPatsRun signature patterns
        (InferenceBase.instantiateCtorScheme initial.supply
          entry.scheme).value.1 aligned children)
    (success : inferPPatFuel (fuel + 1) signature path (.ctor name patterns)
      expected initial = some result) :
    DDPPatRun signature (.ctor name patterns) expected initial result := by
  cases lookup : signature.findPatternCtor name with
  | none => simp [inferPPatFuel, lookup] at success
  | some entry =>
      let instantiated := instantiateCtorInState initial entry.scheme
      cases alignedEq : alignTypes instantiated.2
          (freshOrigin .primitivePattern path "pp-constructor-result")
          instantiated.1.2 expected with
      | none =>
          have actualAlignedEq := alignedEq
          simp only [instantiated, instantiateCtorInState_target]
            at actualAlignedEq
          simp [inferPPatFuel, lookup, actualAlignedEq] at success
      | some aligned =>
          cases childrenEq : inferPPatsFuel fuel signature path 0 patterns
              instantiated.1.1 aligned with
          | none =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualAlignedEq
              have actualChildrenEq := childrenEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualChildrenEq
              simp [inferPPatFuel, lookup, actualAlignedEq,
                actualChildrenEq] at success
          | some children =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualAlignedEq
              have actualChildrenEq := childrenEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualChildrenEq
              have resultEq : some ⟨expected, children.holes,
                  children.bindings,
                  (children.state.freezeCapabilityExport
                    (freshCapImages initial.supply entry.scheme.capBinders)
                    (capabilityExportPayload (children.holes.map Dual.cap)
                      (children.holes.map Dual.target ++ expected ::
                        children.bindings.map fun binding => binding.2))
                    |> fun state => visit state .ppatCtor path).recordEvent
                      (.inferredPPat (.ctor name patterns) expected
                        children.holes children.bindings path)⟩ =
                    some result := by
                simpa [inferPPatFuel, lookup, actualAlignedEq,
                  actualChildrenEq] using success
              have exactResult := Option.some.inj resultEq
              subst result
              rcases alignTypes_ddAlignTypesRun alignedEq with
                ⟨alignedSupply, alignedLedger, alignedDD⟩
              rcases childrenSound entry aligned children childrenEq with
                ⟨_, childrenRaw, childrenOrigin⟩
              simp only [instantiated, instantiateCtorInState_prevailing,
                instantiateCtorInState_capabilityOrigins] at alignedDD
              have childrenAt :
                  ∃ raw : DDPPats signature instantiated.2.supply
                      aligned.prevailing patterns
                      (InferenceBase.instantiateCtorScheme initial.supply
                        entry.scheme).value.1 children.holes
                      children.bindings children.state.supply
                      children.state.prevailing,
                    DDPPatsOrigin signature raw
                      instantiated.2.capabilityOrigins
                      children.state.capabilityOrigins := by
                rw [← alignedSupply, ← alignedLedger]
                exact ⟨childrenRaw, childrenOrigin⟩
              rcases childrenAt with ⟨childrenRaw', childrenOrigin'⟩
              simp only [DDPPatRun, visit, InferState.recordEvent_supply,
                InferState.prevailing_recordEvent,
                InferState.recordEvent_capabilityOrigins,
                InferState.freezeCapabilityExport_supply,
                InferState.freezeCapabilityExport_prevailing,
                InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
              exact ⟨True.intro,
                DDPPat.ctor lookup alignedDD.erase childrenRaw',
                DDPPatOrigin.ctor lookup alignedDD childrenOrigin'⟩

/-- Primitive-pattern tuple reconstruction uses the deterministic finite
target allocator before its result alignment and child traversal. -/
theorem inferPPatFuel_tuple_ddPPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {patterns : List PPat} {expected : Ty} {initial : InferState}
    {result : PPatResult}
    (childrenSound : ∀ (targets : List Ty) (allocated aligned : InferState)
        (children : PPatsResult),
      freshTargets initial
        (freshOrigin .primitivePattern path "pp-tuple-field")
        patterns.length = (targets, allocated) →
      inferPPatsFuel fuel signature path 0 patterns targets aligned =
        some children →
      DDPPatsRun signature patterns targets aligned children)
    (success : inferPPatFuel (fuel + 1) signature path (.tuple patterns)
      expected initial = some result) :
    DDPPatRun signature (.tuple patterns) expected initial result := by
  let allocation := freshTargets initial
    (freshOrigin .primitivePattern path "pp-tuple-field") patterns.length
  cases allocationEq : allocation with
  | mk targets allocated =>
      cases alignedEq : alignTypes allocated
          (freshOrigin .primitivePattern path "pp-tuple-result")
          (.prod targets) expected with
      | none =>
          simp [inferPPatFuel, allocation, allocationEq, alignedEq] at success
      | some aligned =>
          cases childrenEq : inferPPatsFuel fuel signature path 0 patterns
              targets aligned with
          | none =>
              simp [inferPPatFuel, allocation, allocationEq, alignedEq,
                childrenEq] at success
          | some children =>
              have resultEq : some ⟨expected, children.holes,
                  children.bindings,
                  (visit children.state .ppatTuple path).recordEvent
                    (.inferredPPat (.tuple patterns) expected children.holes
                      children.bindings path)⟩ = some result := by
                simpa [inferPPatFuel, allocation, allocationEq, alignedEq,
                  childrenEq] using success
              have exactResult := Option.some.inj resultEq
              subst result
              have allocationFacts :=
                freshTargets_eq_freshTargetsSupply patterns.length initial
                  (freshOrigin .primitivePattern path "pp-tuple-field")
              simp only [allocation, allocationEq] at allocationFacts
              rcases allocationFacts with
                ⟨targetsEq, supplyEq, prevailingEq, ledgerEq⟩
              rcases alignTypes_ddAlignTypesRun alignedEq with
                ⟨alignedSupply, alignedLedger, alignedDD⟩
              rcases childrenSound targets allocated aligned children
                  (by simp [allocation, allocationEq]) childrenEq with
                ⟨_, childrenRaw, childrenOrigin⟩
              subst targetsEq
              rw [prevailingEq, ledgerEq] at alignedDD
              have childrenAt :
                  ∃ raw : DDPPats signature
                      (freshTargetsSupply patterns.length initial.supply).2
                      aligned.prevailing patterns
                      (freshTargetsSupply patterns.length initial.supply).1
                      children.holes children.bindings children.state.supply
                      children.state.prevailing,
                    DDPPatsOrigin signature raw initial.capabilityOrigins
                      children.state.capabilityOrigins := by
                rw [← supplyEq, ← alignedSupply, ← ledgerEq,
                  ← alignedLedger]
                exact ⟨childrenRaw, childrenOrigin⟩
              rcases childrenAt with ⟨childrenRaw', childrenOrigin'⟩
              exact ⟨rfl, DDPPat.tuple alignedDD.erase childrenRaw',
                DDPPatOrigin.tuple alignedDD childrenOrigin'⟩

/-- Data-pattern constructor reconstruction mirrors the primitive-pattern
constructor path without hole capabilities. -/
theorem inferDPatFuel_ctor_ddDPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath} {name : String}
    {patterns : List DPat} {expected : Ty} {initial : InferState}
    {result : DPatResult}
    (childrenSound : ∀ (scheme : CtorScheme) (aligned : InferState)
        (children : DPatsResult),
      inferDPatsFuel fuel signature path 0 patterns
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        aligned = some children →
      DDDPatsRun signature patterns
        (InferenceBase.instantiateCtorScheme initial.supply scheme).value.1
        aligned children)
    (success : inferDPatFuel (fuel + 1) signature path (.ctor name patterns)
      expected initial = some result) :
    DDDPatRun signature (.ctor name patterns) expected initial result := by
  cases lookup : signature.findDataCtor name with
  | none => simp [inferDPatFuel, lookup] at success
  | some scheme =>
      let instantiated := instantiateCtorInState initial scheme
      cases alignedEq : alignTypes instantiated.2
          (freshOrigin .dataPattern path "dp-constructor-result")
          instantiated.1.2 expected with
      | none =>
          have actualAlignedEq := alignedEq
          simp only [instantiated, instantiateCtorInState_target]
            at actualAlignedEq
          simp [inferDPatFuel, lookup, actualAlignedEq] at success
      | some aligned =>
          cases childrenEq : inferDPatsFuel fuel signature path 0 patterns
              instantiated.1.1 aligned with
          | none =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualAlignedEq
              have actualChildrenEq := childrenEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualChildrenEq
              simp [inferDPatFuel, lookup, actualAlignedEq,
                actualChildrenEq] at success
          | some children =>
              have actualAlignedEq := alignedEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualAlignedEq
              have actualChildrenEq := childrenEq
              simp only [instantiated, instantiateCtorInState_target]
                at actualChildrenEq
              have resultEq : some ⟨expected, children.bindings,
                  (children.state.freezeCapabilityExport
                    (freshCapImages initial.supply scheme.capBinders)
                    (capabilityExportPayload []
                      (expected :: children.bindings.map fun binding =>
                        binding.2))
                    |> fun state => visit state .dpatCtor path).recordEvent
                      (.inferredDPat (.ctor name patterns) expected
                        children.bindings path)⟩ = some result := by
                simpa [inferDPatFuel, lookup, actualAlignedEq,
                  actualChildrenEq] using success
              have exactResult := Option.some.inj resultEq
              subst result
              rcases alignTypes_ddAlignTypesRun alignedEq with
                ⟨alignedSupply, alignedLedger, alignedDD⟩
              rcases childrenSound scheme aligned children childrenEq with
                ⟨_, childrenRaw, childrenOrigin⟩
              simp only [instantiated, instantiateCtorInState_prevailing,
                instantiateCtorInState_capabilityOrigins] at alignedDD
              have childrenAt :
                  ∃ raw : DDDPats signature instantiated.2.supply
                      aligned.prevailing patterns
                      (InferenceBase.instantiateCtorScheme initial.supply
                        scheme).value.1 children.bindings
                      children.state.supply children.state.prevailing,
                    DDDPatsOrigin signature raw
                      instantiated.2.capabilityOrigins
                      children.state.capabilityOrigins := by
                rw [← alignedSupply, ← alignedLedger]
                exact ⟨childrenRaw, childrenOrigin⟩
              rcases childrenAt with ⟨childrenRaw', childrenOrigin'⟩
              simp only [DDDPatRun, visit, InferState.recordEvent_supply,
                InferState.prevailing_recordEvent,
                InferState.recordEvent_capabilityOrigins,
                InferState.freezeCapabilityExport_supply,
                InferState.freezeCapabilityExport_prevailing,
                InferState.freezeCapabilityExport_capabilityOrigins_eq_freezeExport]
              exact ⟨True.intro,
                DDDPat.ctor lookup alignedDD.erase childrenRaw',
                DDDPatOrigin.ctor lookup alignedDD childrenOrigin'⟩

/-- Data-pattern tuple reconstruction reuses the same deterministic target
allocator bridge as primitive-pattern tuples. -/
theorem inferDPatFuel_tuple_ddDPatRun
    {fuel : Nat} {signature : FrozenSig} {path : SyntaxPath}
    {patterns : List DPat} {expected : Ty} {initial : InferState}
    {result : DPatResult}
    (childrenSound : ∀ (targets : List Ty) (allocated aligned : InferState)
        (children : DPatsResult),
      freshTargets initial (freshOrigin .dataPattern path "dp-tuple-field")
        patterns.length = (targets, allocated) →
      inferDPatsFuel fuel signature path 0 patterns targets aligned =
        some children →
      DDDPatsRun signature patterns targets aligned children)
    (success : inferDPatFuel (fuel + 1) signature path (.tuple patterns)
      expected initial = some result) :
    DDDPatRun signature (.tuple patterns) expected initial result := by
  let allocation := freshTargets initial
    (freshOrigin .dataPattern path "dp-tuple-field") patterns.length
  cases allocationEq : allocation with
  | mk targets allocated =>
      cases alignedEq : alignTypes allocated
          (freshOrigin .dataPattern path "dp-tuple-result")
          (.prod targets) expected with
      | none =>
          simp [inferDPatFuel, allocation, allocationEq, alignedEq] at success
      | some aligned =>
          cases childrenEq : inferDPatsFuel fuel signature path 0 patterns
              targets aligned with
          | none =>
              simp [inferDPatFuel, allocation, allocationEq, alignedEq,
                childrenEq] at success
          | some children =>
              have resultEq : some ⟨expected, children.bindings,
                  (visit children.state .dpatTuple path).recordEvent
                    (.inferredDPat (.tuple patterns) expected
                      children.bindings path)⟩ = some result := by
                simpa [inferDPatFuel, allocation, allocationEq, alignedEq,
                  childrenEq] using success
              have exactResult := Option.some.inj resultEq
              subst result
              have allocationFacts :=
                freshTargets_eq_freshTargetsSupply patterns.length initial
                  (freshOrigin .dataPattern path "dp-tuple-field")
              simp only [allocation, allocationEq] at allocationFacts
              rcases allocationFacts with
                ⟨targetsEq, supplyEq, prevailingEq, ledgerEq⟩
              rcases alignTypes_ddAlignTypesRun alignedEq with
                ⟨alignedSupply, alignedLedger, alignedDD⟩
              rcases childrenSound targets allocated aligned children
                  (by simp [allocation, allocationEq]) childrenEq with
                ⟨_, childrenRaw, childrenOrigin⟩
              subst targetsEq
              rw [prevailingEq, ledgerEq] at alignedDD
              have childrenAt :
                  ∃ raw : DDDPats signature
                      (freshTargetsSupply patterns.length initial.supply).2
                      aligned.prevailing patterns
                      (freshTargetsSupply patterns.length initial.supply).1
                      children.bindings children.state.supply
                      children.state.prevailing,
                    DDDPatsOrigin signature raw initial.capabilityOrigins
                      children.state.capabilityOrigins := by
                rw [← supplyEq, ← alignedSupply, ← ledgerEq,
                  ← alignedLedger]
                exact ⟨childrenRaw, childrenOrigin⟩
              rcases childrenAt with ⟨childrenRaw', childrenOrigin'⟩
              exact ⟨rfl, DDDPat.tuple alignedDD.erase childrenRaw',
                DDDPatOrigin.tuple alignedDD childrenOrigin'⟩

theorem inferPPatsFuel_nil_ddPPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {initial : InferState} {result : PPatsResult}
    (success : inferPPatsFuel (fuel + 1) signature parent index [] [] initial =
      some result) :
    DDPPatsRun signature [] [] initial result := by
  simp only [inferPPatsFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDPPats.nil, DDPPatsOrigin.nil⟩

theorem inferPPatsFuel_cons_ddPPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {pattern : PPat} {patterns : List PPat} {target : Ty}
    {targets : List Ty} {initial : InferState} {result : PPatsResult}
    (headSound : ∀ head : PPatResult,
      inferPPatFuel fuel signature (index :: parent) pattern target initial =
        some head → DDPPatRun signature pattern target initial head)
    (tailSound : ∀ (head : PPatResult) (tail : PPatsResult),
      inferPPatsFuel fuel signature parent (index + 1) patterns targets
        head.state = some tail →
      DDPPatsRun signature patterns targets head.state tail)
    (success : inferPPatsFuel (fuel + 1) signature parent index
      (pattern :: patterns) (target :: targets) initial = some result) :
    DDPPatsRun signature (pattern :: patterns) (target :: targets) initial
      result := by
  cases headEq : inferPPatFuel fuel signature (index :: parent) pattern target
      initial with
  | none => simp [inferPPatsFuel, headEq] at success
  | some head =>
      cases tailEq : inferPPatsFuel fuel signature parent (index + 1) patterns
          targets head.state with
      | none => simp [inferPPatsFuel, headEq, tailEq] at success
      | some tail =>
          by_cases disjointCheck :
              namesDisjoint head.bindings.names tail.bindings.names = true
          · have resultEq :
                some ⟨head.target :: tail.targets,
                  head.holes ++ tail.holes,
                  head.bindings ++ tail.bindings, tail.state⟩ =
                    some result := by
                simpa [inferPPatsFuel, headEq, tailEq, disjointCheck] using
                  success
            have exactResult := Option.some.inj resultEq
            subst result
            rcases headSound head headEq with ⟨headTarget, headRaw, headOrigin⟩
            rcases tailSound head tail tailEq with
              ⟨tailTargets, tailRaw, tailOrigin⟩
            have disjoint :=
              (namesDisjoint_eq_true head.bindings.names
                tail.bindings.names).mp disjointCheck
            subst headTarget
            subst tailTargets
            exact ⟨rfl, DDPPats.cons headRaw tailRaw disjoint,
              DDPPatsOrigin.cons headOrigin tailOrigin disjoint⟩
          · simp [inferPPatsFuel, headEq, tailEq, disjointCheck] at success

theorem inferDPatsFuel_nil_ddDPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {initial : InferState} {result : DPatsResult}
    (success : inferDPatsFuel (fuel + 1) signature parent index [] [] initial =
      some result) :
    DDDPatsRun signature [] [] initial result := by
  simp only [inferDPatsFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDDPats.nil, DDDPatsOrigin.nil⟩

theorem inferDPatsFuel_cons_ddDPatsRun
    {fuel : Nat} {signature : FrozenSig} {parent : SyntaxPath} {index : Nat}
    {pattern : DPat} {patterns : List DPat} {target : Ty}
    {targets : List Ty} {initial : InferState} {result : DPatsResult}
    (headSound : ∀ head : DPatResult,
      inferDPatFuel fuel signature (index :: parent) pattern target initial =
        some head → DDDPatRun signature pattern target initial head)
    (tailSound : ∀ (head : DPatResult) (tail : DPatsResult),
      inferDPatsFuel fuel signature parent (index + 1) patterns targets
        head.state = some tail →
      DDDPatsRun signature patterns targets head.state tail)
    (success : inferDPatsFuel (fuel + 1) signature parent index
      (pattern :: patterns) (target :: targets) initial = some result) :
    DDDPatsRun signature (pattern :: patterns) (target :: targets) initial
      result := by
  cases headEq : inferDPatFuel fuel signature (index :: parent) pattern target
      initial with
  | none => simp [inferDPatsFuel, headEq] at success
  | some head =>
      cases tailEq : inferDPatsFuel fuel signature parent (index + 1) patterns
          targets head.state with
      | none => simp [inferDPatsFuel, headEq, tailEq] at success
      | some tail =>
          by_cases disjointCheck :
              namesDisjoint head.bindings.names tail.bindings.names = true
          · have resultEq :
                some ⟨head.target :: tail.targets,
                  head.bindings ++ tail.bindings, tail.state⟩ =
                    some result := by
                simpa [inferDPatsFuel, headEq, tailEq, disjointCheck] using
                  success
            have exactResult := Option.some.inj resultEq
            subst result
            rcases headSound head headEq with ⟨headTarget, headRaw, headOrigin⟩
            rcases tailSound head tail tailEq with
              ⟨tailTargets, tailRaw, tailOrigin⟩
            have disjoint :=
              (namesDisjoint_eq_true head.bindings.names
                tail.bindings.names).mp disjointCheck
            subst headTarget
            subst tailTargets
            exact ⟨rfl, DDDPats.cons headRaw tailRaw disjoint,
              DDDPatsOrigin.cons headOrigin tailOrigin disjoint⟩
          · simp [inferDPatsFuel, headEq, tailEq, disjointCheck] at success

theorem checkArmsFuel_nil_ddArmsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {ppBindings : MonoCtx} {parent : SyntaxPath}
    {index : Nat} {clauseTarget bodyTarget : Ty} {initial final : InferState}
    (success : checkArmsFuel (fuel + 1) signature context selfEnv ppBindings
      parent index [] clauseTarget bodyTarget initial = some final) :
    DDArmsRun signature context ppBindings [] clauseTarget bodyTarget initial
      final := by
  simp only [checkArmsFuel, Option.some.injEq] at success
  subst final
  exact ⟨DDArms.nil, DDArmsOrigin.nil⟩

theorem checkArmsFuel_cons_ddArmsRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {ppBindings : MonoCtx} {parent : SyntaxPath}
    {index : Nat} {pattern : DPat} {body : Expr} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {initial final : InferState}
    (patternSound : ∀ patternResult : DPatResult,
      inferDPatFuel fuel signature (0 :: index :: parent) pattern clauseTarget
        initial = some patternResult →
      DDDPatRun signature pattern clauseTarget initial patternResult)
    (bodySound : ∀ (patternResult : DPatResult) (bodyFinal : InferState),
      checkExprFuel fuel signature
        (patternResult.bindings.toContext ++
          (ppBindings.toContext ++ context))
        (selfEnv.eraseMany
          (ppBindings.names ++ patternResult.bindings.names))
        (1 :: index :: parent) body bodyTarget patternResult.state =
          some bodyFinal →
      DDCheckRun signature
        (patternResult.bindings.toContext ++
          (ppBindings.toContext ++ context))
        body bodyTarget patternResult.state bodyFinal)
    (tailSound : ∀ bodyFinal tailFinal,
      checkArmsFuel fuel signature context selfEnv ppBindings parent
        (index + 1) arms clauseTarget bodyTarget bodyFinal = some tailFinal →
      DDArmsRun signature context ppBindings arms clauseTarget bodyTarget
        bodyFinal tailFinal)
    (success : checkArmsFuel (fuel + 1) signature context selfEnv ppBindings
      parent index (.mk pattern body :: arms) clauseTarget bodyTarget initial =
        some final) :
    DDArmsRun signature context ppBindings (.mk pattern body :: arms)
      clauseTarget bodyTarget initial final := by
  cases patternEq : inferDPatFuel fuel signature (0 :: index :: parent) pattern
      clauseTarget initial with
  | none => simp [checkArmsFuel, patternEq] at success
  | some patternResult =>
      by_cases disjointCheck :
          namesDisjoint patternResult.bindings.names ppBindings.names = true
      ·
        cases bodyEq : checkExprFuel fuel signature
            (patternResult.bindings.toContext ++
              (ppBindings.toContext ++ context))
            (selfEnv.eraseMany
              (ppBindings.names ++ patternResult.bindings.names))
            (1 :: index :: parent) body bodyTarget patternResult.state with
        | none =>
            simp [checkArmsFuel, patternEq, disjointCheck, bodyEq] at success
        | some bodyFinal =>
            cases tailEq : checkArmsFuel fuel signature context selfEnv
                ppBindings parent (index + 1) arms clauseTarget bodyTarget
                bodyFinal with
            | none =>
                simp [checkArmsFuel, patternEq, disjointCheck, bodyEq,
                  tailEq] at success
            | some tailFinal =>
                have finalEq : some tailFinal = some final := by
                  simpa [checkArmsFuel, patternEq, disjointCheck, bodyEq,
                    tailEq] using success
                have exactFinal := Option.some.inj finalEq
                subst final
                rcases patternSound patternResult patternEq with
                  ⟨patternTarget, patternRaw, patternOrigin⟩
                rcases bodySound patternResult bodyFinal bodyEq with
                  ⟨bodyRaw, bodyOrigin⟩
                rcases tailSound bodyFinal tailFinal tailEq with
                  ⟨tailRaw, tailOrigin⟩
                subst patternTarget
                have disjoint :=
                  (namesDisjoint_eq_true patternResult.bindings.names
                    ppBindings.names).mp disjointCheck
                have bodyRaw' : DDCheck signature
                    patternResult.state.supply patternResult.state.prevailing
                    (patternResult.bindings.toContext ++
                      ppBindings.toContext ++ context)
                    body bodyTarget bodyFinal.supply bodyFinal.prevailing := by
                  simpa only [List.append_assoc] using bodyRaw
                have bodyOrigin' : DDCheckOrigin signature bodyRaw'
                    patternResult.state.capabilityOrigins
                    bodyFinal.capabilityOrigins := by
                  simpa only [List.append_assoc] using bodyOrigin
                exact ⟨DDArms.cons patternRaw disjoint bodyRaw' tailRaw,
                  DDArmsOrigin.cons patternOrigin disjoint bodyOrigin'
                    tailOrigin⟩
      · simp [checkArmsFuel, patternEq, disjointCheck] at success

theorem inferClauseFuel_ddClauseRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {pp : PPat} {next : Expr}
    {arms : List Arm} {sharedTarget : Ty} {initial : InferState}
    {result : ClauseResult}
    (ppSound : ∀ ppResult : PPatResult,
      inferPPatFuel fuel signature (0 :: path) pp sharedTarget
        (visit initial .clause path) = some ppResult →
      DDPPatRun signature pp sharedTarget (visit initial .clause path)
        ppResult)
    (nextSound : ∀ (ppResult : PPatResult) (nextMatchers : List Expr)
        (nextFinal : InferState),
      checkExprsFuel fuel signature context selfEnv (1 :: path) 0 nextMatchers
        (ppResult.holes.map fun hole => .slot hole.cap hole.target)
        ppResult.state = some nextFinal →
      DDChecksRun signature context nextMatchers
        (ppResult.holes.map fun hole => .slot hole.cap hole.target)
        ppResult.state nextFinal)
    (armsSound : ∀ (ppResult : PPatResult) (armsInitial armsFinal : InferState),
      checkArmsFuel fuel signature context selfEnv ppResult.bindings (2 :: path)
        0 arms sharedTarget
        (Ty.listT (prodTy (ppResult.holes.map Dual.target))) armsInitial =
          some armsFinal →
      DDArmsRun signature context ppResult.bindings arms sharedTarget
        (Ty.listT (prodTy (ppResult.holes.map Dual.target))) armsInitial
        armsFinal)
    (success : inferClauseFuel (fuel + 1) signature context selfEnv path
      (.mk pp next arms) sharedTarget initial = some result) :
    DDClauseRun signature context (.mk pp next arms) sharedTarget initial
      result := by
  cases ppEq : inferPPatFuel fuel signature (0 :: path) pp sharedTarget
      (visit initial .clause path) with
  | none => simp [inferClauseFuel, ppEq] at success
  | some ppResult =>
      cases decomposed : decomposeME next ppResult.holes.length with
      | none => simp [inferClauseFuel, ppEq, decomposed] at success
      | some nextMatchers =>
          cases nextEq : checkExprsFuel fuel signature context selfEnv
              (1 :: path) 0 nextMatchers
              (ppResult.holes.map fun hole => .slot hole.cap hole.target)
              ppResult.state with
          | none =>
              simp [inferClauseFuel, ppEq, decomposed, nextEq] at success
          | some nextFinal =>
              cases armsEq : checkArmsFuel fuel signature context selfEnv
                  ppResult.bindings (2 :: path) 0 arms sharedTarget
                  (Ty.listT (prodTy (ppResult.holes.map Dual.target)))
                  nextFinal with
              | none =>
                  simp [inferClauseFuel, ppEq, decomposed, nextEq,
                    armsEq] at success
              | some armsFinal =>
                  have resultEq :
                      some ⟨sharedTarget, ppResult.holes, armsFinal⟩ =
                        some result := by
                    simpa [inferClauseFuel, ppEq, decomposed, nextEq,
                      armsEq] using success
                  have exactResult := Option.some.inj resultEq
                  subst result
                  rcases ppSound ppResult ppEq with
                    ⟨ppTarget, ppRaw, ppOrigin⟩
                  subst ppTarget
                  rcases nextSound ppResult nextMatchers nextFinal nextEq with
                    ⟨nextRaw, nextOrigin⟩
                  rcases armsSound ppResult nextFinal armsFinal armsEq with
                    ⟨armsRaw, armsOrigin⟩
                  simp only [visit, InferState.recordEvent_supply,
                    InferState.prevailing_recordEvent,
                    InferState.recordEvent_capabilityOrigins] at ppRaw ppOrigin
                  exact ⟨rfl, DDClause.mk ppRaw decomposed nextRaw armsRaw,
                    DDClauseOrigin.mk ppOrigin decomposed nextOrigin
                      armsOrigin⟩

theorem inferClausesFuel_nil_ddClausesRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {sharedTarget : Ty} {initial : InferState} {result : ClausesResult}
    (success : inferClausesFuel (fuel + 1) signature context selfEnv parent
      index [] sharedTarget initial = some result) :
    DDClausesRun signature context [] sharedTarget initial result := by
  simp only [inferClausesFuel, Option.some.injEq] at success
  subst result
  exact ⟨rfl, DDClauses.nil, DDClausesOrigin.nil⟩

theorem inferClausesFuel_cons_ddClausesRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {clause : Clause} {clauses : List Clause} {sharedTarget : Ty}
    {initial : InferState} {result : ClausesResult}
    (headSound : ∀ head : ClauseResult,
      inferClauseFuel fuel signature context selfEnv (index :: parent) clause
        sharedTarget initial = some head →
      DDClauseRun signature context clause sharedTarget initial head)
    (tailSound : ∀ (head : ClauseResult) (tail : ClausesResult),
      inferClausesFuel fuel signature context selfEnv parent (index + 1)
        clauses sharedTarget head.state = some tail →
      DDClausesRun signature context clauses sharedTarget head.state tail)
    (success : inferClausesFuel (fuel + 1) signature context selfEnv parent
      index (clause :: clauses) sharedTarget initial = some result) :
    DDClausesRun signature context (clause :: clauses) sharedTarget initial
      result := by
  cases headEq : inferClauseFuel fuel signature context selfEnv
      (index :: parent) clause sharedTarget initial with
  | none => simp [inferClausesFuel, headEq] at success
  | some head =>
      cases tailEq : inferClausesFuel fuel signature context selfEnv parent
          (index + 1) clauses sharedTarget head.state with
      | none => simp [inferClausesFuel, headEq, tailEq] at success
      | some tail =>
          have resultEq :
              some ⟨sharedTarget, head.rawHoles :: tail.rawHoleLists,
                tail.state⟩ = some result := by
            simpa [inferClausesFuel, headEq, tailEq] using success
          have exactResult := Option.some.inj resultEq
          subst result
          rcases headSound head headEq with
            ⟨headTarget, headRaw, headOrigin⟩
          rcases tailSound head tail tailEq with
            ⟨_, tailRaw, tailOrigin⟩
          subst headTarget
          exact ⟨rfl, DDClauses.cons headRaw tailRaw,
            DDClausesOrigin.cons headOrigin tailOrigin⟩

end Inference
end TypePM
