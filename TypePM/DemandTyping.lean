import TypePM.Inference

/-!
# Raw demand-directed typing derivations

This module defines the syntax-directed, state-threaded demand-directed
judgments `DDSynth`/`DDCheck` announced by the roadmap, independently of the
executable inference functions.  The two judgments thread a fresh supply `q`
and a prevailing substitution `S` in input/output position:

```
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       -- DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  -- DDCheck
```

Design commitments realized here:

* **Synthesis-first checking.**  `DDCheck` has exactly one rule: synthesize
  the expression without an expected type, then align the raw result with the
  expected type at the exact output cut `q₁; S₁` (`DDAlign`).
* **Slot-demand coercion.**  A non-identity coercion branch is available only
  when the substituted expected type already exposes a `MatcherSlot` head at
  the cut.  Branch selection is classified by the deterministic
  `demandClass`, computed on the *cut-resolved* source view `S₁ τraw` — not
  on the raw synthesized type.  The raw-source visibility restriction of the
  current executable selector is therefore a separate fragment condition
  (`RawSourceVisible`), not part of this judgment.
* **No-guess solves.**  Every solve delta is required to be an *exact*
  most general unifier of the constraint resolved at its cut — most general
  and the identity outside the constraint's variables (`ExactCapMGU`,
  `ExactTargetMGU`, `ExactPairedMGU`) — or the exact one-way
  producer-to-slot solution (`OneWayDelta`).  The bare forms `CapMGU`/
  `TargetMGU`/`PairedMGU` remain as the subject of the no-guess theorems:
  most-generality alone already forbids structuring or collapsing an
  unrelated metavariable, and exactness removes only the residual renaming
  freedom, which the value-flow transport boundary shows would capture
  scheme binders.  λ domains are fresh metavariables; no rule structures an
  unrelated metavariable to enable a coercion.
* **No executable-inference dependency.**  The rules never mention
  `inferRaw`/`infer` or reconstruction certificates.  They reuse only the
  deterministic supply-indexed instantiation helpers and the pure syntactic
  recognizers shared with the rest of the development.

The judgments cover the full core syntax.  The pattern layer mirrors the
executable traversal through supply-indexed pure twins of its fresh
allocators (`freshTargetsSupply`, `freshenSkeletonSupply`,
`patternCtorAssignmentsSupply`, `fixMatcherPlaceholderSupply`) and
relational forms of its solver sequences (`DDAlignDual`,
`DDAlignTargetList`, `DDAlignBindings`, `DDAlignCtorCaps`,
`DDPatternCtorCap`); matcher-literal finalization consumes the same
executable coverage checks as the declarative rule.  The
capability-freeze/export ledger axis is not yet indexed by these raw
judgments.  Consequently the state-erasure map from DD derivations to the
internal `RuntimeTyping` certificate still needs a freeze-compatibility
condition.  This is a missing component of the DD specification, not a second
source-typing relation.
-/

namespace TypePM

open Inference (productMatcherDuals? productSlotDuals? matcherProducingRoot
  initialSupply freshCapImages)

/-! ## Most-general solve deltas, in specification form

The shapes mirror the proof-carrying kernel certificates
(`Unification.CapResult`/`TyResult` and the paired-kernel results), stated
relationally so the judgment does not depend on any solver run.
-/

/-- `subst` unifies two capabilities and every unifier factors through it. -/
def CapMGU (left right : Cap) (subst : CapSubst) : Prop :=
  left.apply subst = right.apply subst ∧
  ∀ U : CapSubst, left.apply U = right.apply U →
    ∃ R : CapSubst, U = CapSubst.comp R subst

/-- `subst` unifies two targets and every unifier factors through it. -/
def TargetMGU (left right : Ty) (subst : TySubst) : Prop :=
  left.applyTarget subst = right.applyTarget subst ∧
  ∀ U : TySubst, left.applyTarget U = right.applyTarget U →
    ∃ R : TySubst, U = TySubst.comp R subst

/-- `subst` is a most general *paired* unifier: it solves both sorts at once
and every paired unifier factors through it under cross-sort-aware
sequencing. -/
def PairedMGU (left right : Ty) (subst : Subst) : Prop :=
  subst.apply left = subst.apply right ∧
  ∀ U : Subst, U.apply left = U.apply right →
    ∃ R : Subst, U = Subst.seq R subst

/-- An exact most general capability solution: most general, and the
identity outside the constraint's variables.  The no-guess theorems below
show that bare most-generality already forbids structuring or collapsing
outside variables; exactness removes the residual renaming freedom, which
the value-flow transport boundary shows is genuinely harmful.  The image
conditions confine solve deltas to the constraint's own variables; without
them a most general delta could mention arbitrary — in particular
not-yet-allocated — variables in its images.

The images of the listed capability variables stay within the list. -/
def CapSubst.RangeWithin (S : CapSubst) (vars : List CapVar) : Prop :=
  ∀ varId ∈ vars, ∀ image ∈ (S varId).fcv, image ∈ vars

/-- The target images of the listed target variables stay within the
list. -/
def TySubst.RangeWithin (S : TySubst) (vars : List TypePM.TyVar) : Prop :=
  ∀ varId ∈ vars, ∀ image ∈ (S varId).ftv, image ∈ vars

/-- The capability variables of the images of the listed target variables
stay within the listed capability variables. -/
def TySubst.CapRangeWithin (S : TySubst) (tyVars : List TypePM.TyVar)
    (capVars : List CapVar) : Prop :=
  ∀ varId ∈ tyVars, ∀ image ∈ (S varId).fcv, image ∈ capVars

/-- The executable target unifier never introduces a target variable outside
the constraint.  This is the demand-typing projection of the kernel-local
`TyRange` certificate exposed by `Unification.mguTy_inputRange`. -/
theorem Unification.mguTy_rangeWithin
    {left right : Ty} {S : TySubst}
    (success : Unification.mguTy left right = some S) :
    S.RangeWithin (left.ftv ++ right.ftv) := by
  intro varId varMem image imageMem
  rcases Unification.mguTy_inputRange success varId image imageMem with
    rfl | imageIn
  · exact varMem
  · exact imageIn

/-- The executable target unifier changes only target variables occurring in
its input constraint. -/
theorem Unification.mguTy_supportWithin
    {left right : Ty} {S : TySubst}
    (success : Unification.mguTy left right = some S) :
    S.SupportWithin (left.ftv ++ right.ftv) :=
  Unification.mguTy_supportInput success

/-- Applying twice is applying once: the capability solved-form condition. -/
def CapSubst.Idempotent (S : CapSubst) : Prop :=
  ∀ capability : Cap, (capability.apply S).apply S = capability.apply S

/-- Applying twice is applying once: the target solved-form condition. -/
def TySubst.Idempotent (S : TySubst) : Prop :=
  ∀ target : Ty, (target.applyTarget S).applyTarget S = target.applyTarget S

/-- Applying twice is applying once: the paired solved-form condition. -/
def Subst.Idempotent (S : Subst) : Prop :=
  ∀ target : Ty, S.apply (S.apply target) = S.apply target

def ExactCapMGU (left right : Cap) (subst : CapSubst) : Prop :=
  CapMGU left right subst ∧
  subst.SupportWithin (left.fcv ++ right.fcv) ∧
  subst.RangeWithin (left.fcv ++ right.fcv) ∧
  subst.Idempotent

/-- An exact most general target solution. -/
def ExactTargetMGU (left right : Ty) (subst : TySubst) : Prop :=
  TargetMGU left right subst ∧
  subst.SupportWithin (left.ftv ++ right.ftv) ∧
  subst.RangeWithin (left.ftv ++ right.ftv) ∧
  subst.CapRangeWithin (left.ftv ++ right.ftv) (left.fcv ++ right.fcv) ∧
  subst.Idempotent

/-- An exact most general paired solution: exact in both sorts, with the
images of constraint variables confined to the constraint, in solved form. -/
def ExactPairedMGU (left right : Ty) (subst : Subst) : Prop :=
  PairedMGU left right subst ∧
  subst.cap.SupportWithin (left.fcv ++ right.fcv) ∧
  subst.target.SupportWithin (left.ftv ++ right.ftv) ∧
  subst.cap.RangeWithin (left.fcv ++ right.fcv) ∧
  subst.target.RangeWithin (left.ftv ++ right.ftv) ∧
  subst.target.CapRangeWithin (left.ftv ++ right.ftv)
    (left.fcv ++ right.fcv) ∧
  subst.Idempotent

/-- The exact one-way producer-to-slot solution: the capability component is
the restricted `matchCap` binding substitution (exact by construction), and
the target component is an exact most general unifier of the
capability-adjusted targets. -/
def OneWayDelta (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty) (delta : Subst) : Prop :=
  ∃ bindings,
    CapMatch.matchCap producerCap consumerCap = some bindings ∧
    delta.cap = bindings.toSubstWithin consumerCap.fcv ∧
    ExactTargetMGU (producerTarget.applyCapability delta.cap)
      (consumerTarget.applyCapability delta.cap) delta.target

/-! ### Capability-origin ledger transitions

The demand-directed families use the same chronological origin policy as the
executable traversal, but the policy is expressed here without an
`InferState` or trace.  Instance allocation and export freezing are pure
ledger transitions; equality solving itself leaves the ledger unchanged and
must instead present one of the admissible exact-solve certificates below.
-/

namespace DDLedger

/-- Fresh capability images of a value-flow scheme are exported immediately,
so later solves may only rename them to another non-structural variable. -/
def markSchemeInstance (ledger : CapabilityOriginLedger)
    (q : InferenceBase.FreshSupply) (scheme : Scheme) :
    CapabilityOriginLedger :=
  ledger.setOrigins (freshCapImages q scheme.capBinders) .renameOnly

/-- Pattern-function lookup is value flow and uses the same rename-only
instance policy as ordinary context lookup. -/
def markDualInstance (ledger : CapabilityOriginLedger)
    (q : InferenceBase.FreshSupply) (scheme : DualScheme) :
    CapabilityOriginLedger :=
  ledger.setOrigins (freshCapImages q scheme.capBinders) .renameOnly

/-- Constructor and primitive instance variables remain structurally flexible
while their local arguments or patterns are checked. -/
def markCtorInstance (ledger : CapabilityOriginLedger)
    (q : InferenceBase.FreshSupply) (scheme : CtorScheme) :
    CapabilityOriginLedger :=
  ledger.setOrigins (freshCapImages q scheme.capBinders)
    .structuralFlexible

/-- A single fresh consumer capability is structurally flexible at its
allocation cut. -/
def markFreshCap (ledger : CapabilityOriginLedger)
    (q : InferenceBase.FreshSupply) : CapabilityOriginLedger :=
  ledger.markStructuralFlexible ⟨q.nextCap⟩

/-- Capability metavariables allocated in the half-open supply interval
`[initial.nextCap, final.nextCap)` become structurally flexible.  Pure
supply-indexed traversals such as skeleton freshening use this batch form in
place of the executable state's sequence of `freshCap` updates. -/
def markCapRange (ledger : CapabilityOriginLedger)
    (initial final : InferenceBase.FreshSupply) :
    CapabilityOriginLedger :=
  let offsets := List.range (final.nextCap - initial.nextCap)
  let varIds := offsets.map fun offset => ⟨initial.nextCap + offset⟩
  ledger.setOrigins varIds .structuralFlexible

/-- Variable leaves in the prevailing images of constructor-instance binders
that still occur in the exported payload and remain structurally flexible. -/
def exportLeaves (ledger : CapabilityOriginLedger) (S : Subst)
    (capImages : List CapVar) (exportedPayload : Ty) : List CapVar :=
  let exportedVars := (S.apply exportedPayload).fcv
  let imageLeaves := capImages.flatMap fun varId => (S.cap varId).fcv
  (imageLeaves.filter fun varId => varId ∈ exportedVars).eraseDups.filter
    fun varId => ledger.originOf varId = .structuralFlexible

/-- Freeze exactly the surviving structural leaves of a completed
constructor or primitive instance. -/
def freezeExport (ledger : CapabilityOriginLedger) (S : Subst)
    (capImages : List CapVar) (exportedPayload : Ty) :
    CapabilityOriginLedger :=
  ledger.setOrigins (exportLeaves ledger S capImages exportedPayload)
    .renameOnly

/-- Inference-owned, still-structural leaves visible in a finalized matcher
producer.  Explicit ledger membership is the state-free counterpart of the
executable trace's allocation ownership.  This includes an earlier recursive
placeholder that flows into a nested matcher result, while excluding rigid
source variables that are absent from the ledger. -/
def matcherProducerLeaves (ledger : CapabilityOriginLedger)
    (capability : Cap) : List CapVar :=
  (capability.fcv.filter fun varId =>
      varId ∈ ledger.map Prod.fst).eraseDups.filter
    fun varId => ledger.originOf varId = .structuralFlexible

/-- Finalizing a matcher freezes every inference-owned structurally flexible
leaf visible in its producer capability; rigid ambient and already-frozen
leaves are left untouched. -/
def freezeMatcherProducer (ledger : CapabilityOriginLedger) (capability : Cap) :
    CapabilityOriginLedger :=
  ledger.setOrigins
    (matcherProducerLeaves ledger capability) .renameOnly

theorem exportLeaves_origin
    (ledger : CapabilityOriginLedger) (S : Subst)
    (capImages : List CapVar) (exportedPayload : Ty) (varId : CapVar)
    (membership : varId ∈ exportLeaves ledger S capImages exportedPayload) :
    ledger.originOf varId = .structuralFlexible := by
  simp [exportLeaves] at membership
  cases originEquation : ledger.originOf varId <;> simp_all

theorem matcherProducerLeaves_recorded
    (ledger : CapabilityOriginLedger) (capability : Cap) (varId : CapVar)
    (membership : varId ∈ matcherProducerLeaves ledger capability) :
    varId ∈ capability.fcv ∧ varId ∈ ledger.map Prod.fst := by
  simp [matcherProducerLeaves] at membership
  rcases membership.1.2 with ⟨origin, entryMembership⟩
  exact ⟨membership.1.1,
    List.mem_map.mpr ⟨(varId, origin), entryMembership, rfl⟩⟩

theorem matcherProducerLeaves_origin
    (ledger : CapabilityOriginLedger) (capability : Cap) (varId : CapVar)
    (membership : varId ∈ matcherProducerLeaves ledger capability) :
    ledger.originOf varId = .structuralFlexible := by
  simp [matcherProducerLeaves] at membership
  cases originEquation : ledger.originOf varId <;> simp_all

theorem markSchemeInstance_origin_of_mem
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : Scheme) (varId : CapVar)
    (membership : varId ∈ freshCapImages q scheme.capBinders) :
    (markSchemeInstance ledger q scheme).originOf varId = .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    ledger (freshCapImages q scheme.capBinders) varId .renameOnly membership

theorem markDualInstance_origin_of_mem
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : DualScheme) (varId : CapVar)
    (membership : varId ∈ freshCapImages q scheme.capBinders) :
    (markDualInstance ledger q scheme).originOf varId = .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    ledger (freshCapImages q scheme.capBinders) varId .renameOnly membership

theorem markCtorInstance_origin_of_mem
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : CtorScheme) (varId : CapVar)
    (membership : varId ∈ freshCapImages q scheme.capBinders) :
    (markCtorInstance ledger q scheme).originOf varId =
      .structuralFlexible := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem
    ledger (freshCapImages q scheme.capBinders) varId .structuralFlexible
      membership

@[simp] theorem markFreshCap_origin
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply) :
    (markFreshCap ledger q).originOf ⟨q.nextCap⟩ =
      .structuralFlexible := by
  simp [markFreshCap]

theorem freezeExport_origin_of_mem
    (ledger : CapabilityOriginLedger) (S : Subst)
    (capImages : List CapVar) (exportedPayload : Ty) (varId : CapVar)
    (membership : varId ∈ exportLeaves ledger S capImages exportedPayload) :
    (freezeExport ledger S capImages exportedPayload).originOf varId =
      .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem ledger
    (exportLeaves ledger S capImages exportedPayload) varId .renameOnly
      membership

theorem freezeExport_origin_of_not_mem
    (ledger : CapabilityOriginLedger) (S : Subst)
    (capImages : List CapVar) (exportedPayload : Ty) (varId : CapVar)
    (membership : varId ∉ exportLeaves ledger S capImages exportedPayload) :
    (freezeExport ledger S capImages exportedPayload).originOf varId =
      ledger.originOf varId := by
  simp [freezeExport,
    CapabilityOriginLedger.originOf_setOrigins_eq, membership]

theorem freezeMatcherProducer_origin_of_mem
    (ledger : CapabilityOriginLedger) (capability : Cap) (varId : CapVar)
    (membership : varId ∈ matcherProducerLeaves ledger capability) :
    (freezeMatcherProducer ledger capability).originOf varId =
      .renameOnly := by
  exact CapabilityOriginLedger.originOf_setOrigins_of_mem ledger
    (matcherProducerLeaves ledger capability) varId .renameOnly
      membership

theorem freezeMatcherProducer_origin_of_not_mem
    (ledger : CapabilityOriginLedger) (capability : Cap) (varId : CapVar)
    (membership : varId ∉ matcherProducerLeaves ledger capability) :
    (freezeMatcherProducer ledger capability).originOf varId =
      ledger.originOf varId := by
  simp [freezeMatcherProducer,
    CapabilityOriginLedger.originOf_setOrigins_eq, membership]

end DDLedger

/-! ### Origin-safe exact solves -/

/-- An exact capability MGU that is legal at the given origin-ledger cut. -/
structure OriginSafeExactCapMGU (ledger : CapabilityOriginLedger)
    (left right : Cap) (subst : CapSubst) : Prop where
  exact : ExactCapMGU left right subst
  admissible : AdmissibleCapPost ledger subst

/-- An exact paired MGU that is legal at the given origin-ledger cut. -/
structure OriginSafeExactPairedMGU (ledger : CapabilityOriginLedger)
    (left right : Ty) (subst : Subst) : Prop where
  exact : ExactPairedMGU left right subst
  admissible : AdmissiblePost ledger subst

/-- An exact producer-to-slot delta that is legal at the given
origin-ledger cut. -/
structure OriginSafeOneWayDelta (ledger : CapabilityOriginLedger)
    (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty) (delta : Subst) : Prop where
  exact : OneWayDelta producerCap producerTarget consumerCap consumerTarget
    delta
  admissible : AdmissiblePost ledger delta

/-! ### Reflexive and single-binding witnesses -/

/-- Identity is a most general unifier of syntactically equal capabilities. -/
theorem CapMGU.refl (capability : Cap) :
    CapMGU capability capability CapSubst.id := by
  refine ⟨rfl, fun U _ => ⟨U, ?_⟩⟩
  funext candidate
  show (CapSubst.id candidate).apply U = U candidate
  rfl

/-- Identity is a most general unifier of syntactically equal targets. -/
theorem TargetMGU.refl (target : Ty) :
    TargetMGU target target TySubst.id := by
  refine ⟨rfl, fun U _ => ⟨U, ?_⟩⟩
  funext candidate
  show (TySubst.id candidate).applyTarget U = U candidate
  rfl

/-- Binding one absent capability variable is a most general solution of a
variable-versus-capability constraint. -/
theorem CapMGU.varLeft (varId : CapVar) (capability : Cap)
    (notMem : varId ∉ capability.fcv) :
    CapMGU (.var varId) capability
      (Unification.CapSubst.single varId capability) := by
  constructor
  · show (Cap.var varId).apply (Unification.CapSubst.single varId capability) =
      capability.apply (Unification.CapSubst.single varId capability)
    rw [Unification.Cap.apply_single_of_not_mem varId capability capability
      notMem]
    show Unification.CapSubst.single varId capability varId = capability
    simp [Unification.CapSubst.single]
  · intro U unifies
    refine ⟨U, ?_⟩
    funext candidate
    show U candidate =
      (Unification.CapSubst.single varId capability candidate).apply U
    by_cases hcase : varId = candidate
    · subst hcase
      simp only [Unification.CapSubst.single]
      exact unifies
    · simp only [Unification.CapSubst.single, if_neg hcase]
      rfl

/-- Symmetric form of `CapMGU.varLeft`. -/
theorem CapMGU.varRight (capability : Cap) (varId : CapVar)
    (notMem : varId ∉ capability.fcv) :
    CapMGU capability (.var varId)
      (Unification.CapSubst.single varId capability) := by
  obtain ⟨sound, universal⟩ := CapMGU.varLeft varId capability notMem
  exact ⟨sound.symm, fun U unifies => universal U unifies.symm⟩

/-- Binding one absent target variable is a most general solution of a
variable-versus-target constraint. -/
theorem TargetMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    TargetMGU (.var varId) target
      (Unification.TySubst.single varId target) := by
  constructor
  · show (Ty.var varId).applyTarget
        (Unification.TySubst.single varId target) =
      target.applyTarget (Unification.TySubst.single varId target)
    rw [Unification.Ty.applyTarget_single_of_not_mem varId target target
      notMem]
    show Unification.TySubst.single varId target varId = target
    simp [Unification.TySubst.single]
  · intro U unifies
    refine ⟨U, ?_⟩
    funext candidate
    show U candidate =
      (Unification.TySubst.single varId target candidate).applyTarget U
    by_cases hcase : varId = candidate
    · subst hcase
      simp only [Unification.TySubst.single]
      exact unifies
    · simp only [Unification.TySubst.single, if_neg hcase]
      rfl

/-- Symmetric form of `TargetMGU.varLeft`. -/
theorem TargetMGU.varRight (target : Ty) (varId : TypePM.TyVar)
    (notMem : varId ∉ target.ftv) :
    TargetMGU target (.var varId)
      (Unification.TySubst.single varId target) := by
  obtain ⟨sound, universal⟩ := TargetMGU.varLeft varId target notMem
  exact ⟨sound.symm, fun U unifies => universal U unifies.symm⟩

/-- Identity is a most general paired unifier of syntactically equal types. -/
theorem PairedMGU.refl (target : Ty) :
    PairedMGU target target Subst.id :=
  ⟨rfl, fun U _ => ⟨U, (Subst.seq_id_right U).symm⟩⟩

/-- Binding one absent target variable is a most general paired solution of a
variable-versus-type constraint. -/
theorem PairedMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    PairedMGU (.var varId) target
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  constructor
  · show ((Ty.var varId).applyCapability CapSubst.id).applyTarget
        (Unification.TySubst.single varId target) =
      (target.applyCapability CapSubst.id).applyTarget
        (Unification.TySubst.single varId target)
    rw [Ty.applyCapability_id, Ty.applyCapability_id,
      Unification.Ty.applyTarget_single_of_not_mem varId target target notMem]
    show Unification.TySubst.single varId target varId = target
    simp [Unification.TySubst.single]
  · intro U unifies
    refine ⟨U, ?_⟩
    have targetEq : U.target = fun candidate =>
        U.apply (Unification.TySubst.single varId target candidate) := by
      funext candidate
      by_cases hcase : varId = candidate
      · subst hcase
        simp only [Unification.TySubst.single, if_true]
        exact unifies
      · simp only [Unification.TySubst.single, if_neg hcase]
        rfl
    exact congrArg (Subst.mk U.cap) targetEq

/-- Symmetric form of `PairedMGU.varLeft`. -/
theorem PairedMGU.varRight (target : Ty) (varId : TypePM.TyVar)
    (notMem : varId ∉ target.ftv) :
    PairedMGU target (.var varId)
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  obtain ⟨sound, universal⟩ := PairedMGU.varLeft varId target notMem
  exact ⟨sound.symm, fun U unifies => universal U unifies.symm⟩

/-- The diagonal function-alignment delta: solve `fn ?a ?a ≐ fn ?b ?c` by
mapping the shared variable to the fresh domain and collapsing the fresh
codomain onto the same image. -/
def fnDiagonalDelta (shared domain codomain : TypePM.TyVar) : TySubst :=
  fun candidate =>
    if candidate = shared then .var domain
    else if candidate = codomain then .var domain
    else .var candidate

/-- The diagonal delta is a most general paired solution of the
application-function alignment against a fresh domain/codomain pair. -/
theorem PairedMGU.fnDiagonal (shared domain codomain : TypePM.TyVar)
    (domainNeShared : domain ≠ shared) (domainNeCodomain : domain ≠ codomain)
    (codomainNeShared : codomain ≠ shared) :
    PairedMGU (.fn (.var shared) (.var shared))
      (.fn (.var domain) (.var codomain))
      ⟨CapSubst.id, fnDiagonalDelta shared domain codomain⟩ := by
  have evalShared :
      fnDiagonalDelta shared domain codomain shared = .var domain := by
    simp [fnDiagonalDelta]
  have evalDomain :
      fnDiagonalDelta shared domain codomain domain = .var domain := by
    simp [fnDiagonalDelta, domainNeShared, domainNeCodomain]
  have evalCodomain :
      fnDiagonalDelta shared domain codomain codomain = .var domain := by
    simp [fnDiagonalDelta, codomainNeShared]
  constructor
  · show Ty.fn (fnDiagonalDelta shared domain codomain shared)
        (fnDiagonalDelta shared domain codomain shared) =
      Ty.fn (fnDiagonalDelta shared domain codomain domain)
        (fnDiagonalDelta shared domain codomain codomain)
    rw [evalShared, evalDomain, evalCodomain]
  · intro U unifies
    have components :
        Ty.fn (U.target shared) (U.target shared) =
          Ty.fn (U.target domain) (U.target codomain) := unifies
    have domainEq : U.target shared = U.target domain := by
      injection components
    have codomainEq : U.target shared = U.target codomain := by
      injection components with _ codomainEq
    refine ⟨U, congrArg (Subst.mk U.cap) ?_⟩
    funext candidate
    show U.target candidate =
      U.apply (fnDiagonalDelta shared domain codomain candidate)
    by_cases hshared : candidate = shared
    · rw [show fnDiagonalDelta shared domain codomain candidate =
        .var domain by simp [fnDiagonalDelta, hshared], hshared]
      exact domainEq
    · by_cases hcodomain : candidate = codomain
      · rw [show fnDiagonalDelta shared domain codomain candidate =
          .var domain by
            simp [fnDiagonalDelta, hcodomain, codomainNeShared], hcodomain]
        exact codomainEq.symm.trans domainEq
      · rw [show fnDiagonalDelta shared domain codomain candidate =
          .var candidate by simp [fnDiagonalDelta, hshared, hcodomain]]
        rfl

/-! ### Exact witnesses

Each reflexive/single-binding/diagonal witness extends to the exact form:
the concrete deltas are the identity outside their constraint by
construction. -/

theorem CapSubst.id_rangeWithin (vars : List CapVar) :
    CapSubst.id.RangeWithin vars := by
  intro varId mem image imageMem
  have h : image = varId := by
    simpa [CapSubst.id, Cap.fcv] using imageMem
  simpa [h] using mem

theorem TySubst.id_rangeWithin (vars : List TypePM.TyVar) :
    TySubst.id.RangeWithin vars := by
  intro varId mem image imageMem
  have h : image = varId := by
    simpa [TySubst.id, Ty.ftv] using imageMem
  simpa [h] using mem

theorem TySubst.id_capRangeWithin (tyVars : List TypePM.TyVar)
    (capVars : List CapVar) :
    TySubst.id.CapRangeWithin tyVars capVars := by
  intro varId _ image imageMem
  have empty : (TySubst.id varId).fcv = ([] : List CapVar) := rfl
  rw [empty] at imageMem
  nomatch imageMem

/-- Range confinement of the single capability binding. -/
theorem capSingle_rangeWithin {varId : CapVar} {capability : Cap}
    {vars : List CapVar} (imagesWithin : ∀ image ∈ capability.fcv,
      image ∈ vars) :
    (Unification.CapSubst.single varId capability).RangeWithin vars := by
  intro candidate mem image imageMem
  by_cases hcase : varId = candidate
  · subst hcase
    rw [show Unification.CapSubst.single varId capability varId = capability
      from if_pos rfl] at imageMem
    exact imagesWithin image imageMem
  · rw [show Unification.CapSubst.single varId capability candidate =
      .var candidate from if_neg hcase] at imageMem
    have h : image = candidate := by simpa [Cap.fcv] using imageMem
    simpa [h] using mem

/-- Range confinement of the single target binding. -/
theorem tySingle_rangeWithin {varId : TypePM.TyVar} {target : Ty}
    {vars : List TypePM.TyVar} (imagesWithin : ∀ image ∈ target.ftv,
      image ∈ vars) :
    (Unification.TySubst.single varId target).RangeWithin vars := by
  intro candidate mem image imageMem
  by_cases hcase : varId = candidate
  · subst hcase
    rw [show Unification.TySubst.single varId target varId = target
      from if_pos rfl] at imageMem
    exact imagesWithin image imageMem
  · rw [show Unification.TySubst.single varId target candidate =
      .var candidate from if_neg hcase] at imageMem
    have h : image = candidate := by simpa [Ty.ftv] using imageMem
    simpa [h] using mem

/-- Capability-range confinement of the single target binding. -/
theorem tySingle_capRangeWithin {varId : TypePM.TyVar} {target : Ty}
    {tyVars : List TypePM.TyVar} {capVars : List CapVar}
    (imagesWithin : ∀ image ∈ target.fcv, image ∈ capVars) :
    (Unification.TySubst.single varId target).CapRangeWithin tyVars
      capVars := by
  intro candidate _ image imageMem
  by_cases hcase : varId = candidate
  · subst hcase
    rw [show Unification.TySubst.single varId target varId = target
      from if_pos rfl] at imageMem
    exact imagesWithin image imageMem
  · rw [show Unification.TySubst.single varId target candidate =
      .var candidate from if_neg hcase] at imageMem
    have empty : (Ty.var candidate).fcv = ([] : List CapVar) := rfl
    rw [empty] at imageMem
    nomatch imageMem

/-! ### Solved-form (idempotency) helpers

Exactness confines a delta's support and range to its constraint, but a
renaming that is its own inverse on two constraint variables still satisfies
both confinement clauses on a trivially satisfied constraint.  The
solved-form clause removes exactly that residue: applying a delta twice is
applying it once, which is what prevailing-substitution absorption
(`Subst.seq_absorbs_of_idempotent`) needs. -/

/-- Pointwise fixed images make a capability substitution idempotent. -/
theorem CapSubst.idempotent_of_pointwise {S : CapSubst}
    (fixed : ∀ varId, (S varId).apply S = S varId) : S.Idempotent := by
  intro capability
  rw [← Cap.apply_comp]
  congr 1
  funext varId
  exact fixed varId

/-- Pointwise fixed images make a target substitution idempotent. -/
theorem TySubst.idempotent_of_pointwise {S : TySubst}
    (fixed : ∀ varId, (S varId).applyTarget S = S varId) : S.Idempotent := by
  intro target
  rw [← Ty.applyTarget_comp]
  congr 1
  funext varId
  exact fixed varId

/-- The identity capability substitution is idempotent. -/
theorem CapSubst.id_idempotent : CapSubst.id.Idempotent := by
  intro capability
  simp [Cap.apply_id]

/-- The identity target substitution is idempotent. -/
theorem TySubst.id_idempotent : TySubst.id.Idempotent := by
  intro target
  simp [Ty.applyTarget_id]

/-- The identity paired substitution is idempotent. -/
theorem Subst.id_idempotent : Subst.Idempotent Subst.id := by
  intro target
  simp [Subst.apply_id]

/-- A capability-identity paired delta is idempotent exactly when its target
component is. -/
theorem Subst.idempotent_of_capId {T : TySubst} (idem : T.Idempotent) :
    Subst.Idempotent ⟨CapSubst.id, T⟩ := by
  intro target
  show (((target.applyCapability CapSubst.id).applyTarget T).applyCapability
      CapSubst.id).applyTarget T =
    (target.applyCapability CapSubst.id).applyTarget T
  rw [Ty.applyCapability_id, Ty.applyCapability_id]
  exact idem target

/-- The single capability binding is idempotent under its occurs condition. -/
theorem capSingle_idempotent {varId : CapVar} {capability : Cap}
    (notMem : varId ∉ capability.fcv) :
    (Unification.CapSubst.single varId capability).Idempotent := by
  apply CapSubst.idempotent_of_pointwise
  intro candidate
  by_cases hcase : varId = candidate
  · subst hcase
    rw [show Unification.CapSubst.single varId capability varId = capability
      from if_pos rfl]
    exact Unification.Cap.apply_single_of_not_mem varId capability capability
      notMem
  · rw [show Unification.CapSubst.single varId capability candidate =
      .var candidate from if_neg hcase]
    show Unification.CapSubst.single varId capability candidate =
      .var candidate
    exact if_neg hcase

/-- The single target binding is idempotent under its occurs condition. -/
theorem tySingle_idempotent {varId : TypePM.TyVar} {target : Ty}
    (notMem : varId ∉ target.ftv) :
    (Unification.TySubst.single varId target).Idempotent := by
  apply TySubst.idempotent_of_pointwise
  intro candidate
  by_cases hcase : varId = candidate
  · subst hcase
    rw [show Unification.TySubst.single varId target varId = target
      from if_pos rfl]
    exact Unification.Ty.applyTarget_single_of_not_mem varId target target
      notMem
  · rw [show Unification.TySubst.single varId target candidate =
      .var candidate from if_neg hcase]
    show Unification.TySubst.single varId target candidate = .var candidate
    exact if_neg hcase

/-- Sequencing any later substitution onto an idempotent prevailing
substitution absorbs the prevailing action: the composite does not see the
earlier substitution twice. -/
theorem Subst.seq_absorbs_of_idempotent {S : Subst}
    (idem : S.Idempotent) (U : Subst) (target : Ty) :
    (Subst.seq U S).apply (S.apply target) = (Subst.seq U S).apply target := by
  rw [Subst.seq_apply, Subst.seq_apply, idem]

/-- A solved-form delta whose composite images stay fixed by the prevailing
substitution keeps the composite in solved form.  The fixedness premise is
where freshness discharges: the delta's constraint variables and images are
prevailing-resolved, so the prevailing substitution does not move them. -/
theorem Subst.seq_idempotent {S delta : Subst}
    (idemDelta : delta.Idempotent)
    (fixed : ∀ target : Ty,
      S.apply (delta.apply (S.apply target)) =
        delta.apply (S.apply target)) :
    (Subst.seq delta S).Idempotent := by
  intro target
  rw [Subst.seq_apply, Subst.seq_apply, fixed, idemDelta]

/-- Identity is an exact most general unifier of equal capabilities. -/
theorem ExactCapMGU.refl (capability : Cap) :
    ExactCapMGU capability capability CapSubst.id :=
  ⟨CapMGU.refl capability, CapSubst.id_supportWithin _,
    CapSubst.id_rangeWithin _, CapSubst.id_idempotent⟩

/-- The single binding is an exact most general capability solution. -/
theorem ExactCapMGU.varLeft (varId : CapVar) (capability : Cap)
    (notMem : varId ∉ capability.fcv) :
    ExactCapMGU (.var varId) capability
      (Unification.CapSubst.single varId capability) := by
  refine ⟨CapMGU.varLeft varId capability notMem, ?_,
    capSingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inr mem)),
    capSingle_idempotent notMem⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Cap.fcv])
  simp [Unification.CapSubst.single, hne]

/-- Symmetric form of `ExactCapMGU.varLeft`. -/
theorem ExactCapMGU.varRight (capability : Cap) (varId : CapVar)
    (notMem : varId ∉ capability.fcv) :
    ExactCapMGU capability (.var varId)
      (Unification.CapSubst.single varId capability) := by
  refine ⟨CapMGU.varRight capability varId notMem, ?_,
    capSingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inl mem)),
    capSingle_idempotent notMem⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Cap.fcv])
  simp [Unification.CapSubst.single, hne]

/-- Identity is an exact most general unifier of equal targets. -/
theorem ExactTargetMGU.refl (target : Ty) :
    ExactTargetMGU target target TySubst.id :=
  ⟨TargetMGU.refl target, fun _ _ => rfl, TySubst.id_rangeWithin _,
    TySubst.id_capRangeWithin _ _, TySubst.id_idempotent⟩

/-- The single binding is an exact most general target solution. -/
theorem ExactTargetMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    ExactTargetMGU (.var varId) target
      (Unification.TySubst.single varId target) := by
  refine ⟨TargetMGU.varLeft varId target notMem, ?_,
    tySingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inr mem)),
    tySingle_capRangeWithin
      (fun image mem => List.mem_append.mpr (Or.inr mem)),
    tySingle_idempotent notMem⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [Unification.TySubst.single, hne]

/-- Symmetric form of `ExactTargetMGU.varLeft`. -/
theorem ExactTargetMGU.varRight (target : Ty) (varId : TypePM.TyVar)
    (notMem : varId ∉ target.ftv) :
    ExactTargetMGU target (.var varId)
      (Unification.TySubst.single varId target) := by
  refine ⟨TargetMGU.varRight target varId notMem, ?_,
    tySingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inl mem)),
    tySingle_capRangeWithin
      (fun image mem => List.mem_append.mpr (Or.inl mem)),
    tySingle_idempotent notMem⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [Unification.TySubst.single, hne]

/-- Identity is an exact most general paired unifier of equal types. -/
theorem ExactPairedMGU.refl (target : Ty) :
    ExactPairedMGU target target Subst.id :=
  ⟨PairedMGU.refl target, CapSubst.id_supportWithin _, fun _ _ => rfl,
    CapSubst.id_rangeWithin _, TySubst.id_rangeWithin _,
    TySubst.id_capRangeWithin _ _, Subst.id_idempotent⟩

/-- The single target binding is an exact most general paired solution. -/
theorem ExactPairedMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    ExactPairedMGU (.var varId) target
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  refine ⟨PairedMGU.varLeft varId target notMem,
    CapSubst.id_supportWithin _, ?_, CapSubst.id_rangeWithin _,
    tySingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inr mem)),
    tySingle_capRangeWithin
      (fun image mem => List.mem_append.mpr (Or.inr mem)),
    Subst.idempotent_of_capId (tySingle_idempotent notMem)⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [Unification.TySubst.single, hne]

/-- Symmetric form of `ExactPairedMGU.varLeft`. -/
theorem ExactPairedMGU.varRight (target : Ty) (varId : TypePM.TyVar)
    (notMem : varId ∉ target.ftv) :
    ExactPairedMGU target (.var varId)
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  refine ⟨PairedMGU.varRight target varId notMem,
    CapSubst.id_supportWithin _, ?_, CapSubst.id_rangeWithin _,
    tySingle_rangeWithin
      (fun image mem => List.mem_append.mpr (Or.inl mem)),
    tySingle_capRangeWithin
      (fun image mem => List.mem_append.mpr (Or.inl mem)),
    Subst.idempotent_of_capId (tySingle_idempotent notMem)⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [Unification.TySubst.single, hne]

/-- The diagonal function-alignment delta is exact. -/
theorem ExactPairedMGU.fnDiagonal (shared domain codomain : TypePM.TyVar)
    (domainNeShared : domain ≠ shared) (domainNeCodomain : domain ≠ codomain)
    (codomainNeShared : codomain ≠ shared) :
    ExactPairedMGU (.fn (.var shared) (.var shared))
      (.fn (.var domain) (.var codomain))
      ⟨CapSubst.id, fnDiagonalDelta shared domain codomain⟩ := by
  have deltaIdem : (fnDiagonalDelta shared domain codomain).Idempotent := by
    apply TySubst.idempotent_of_pointwise
    intro candidate
    have imageFixed :
        fnDiagonalDelta shared domain codomain domain = .var domain := by
      simp [fnDiagonalDelta, domainNeShared, domainNeCodomain]
    by_cases hshared : candidate = shared
    · subst hshared
      rw [show fnDiagonalDelta candidate domain codomain candidate =
        .var domain from by simp [fnDiagonalDelta]]
      exact imageFixed
    · by_cases hcodomain : candidate = codomain
      · subst hcodomain
        rw [show fnDiagonalDelta shared domain candidate candidate =
          .var domain from by
            simp [fnDiagonalDelta, fun h : candidate = shared =>
              codomainNeShared h]]
        exact imageFixed
      · rw [show fnDiagonalDelta shared domain codomain candidate =
          .var candidate from by simp [fnDiagonalDelta, hshared, hcodomain]]
        show fnDiagonalDelta shared domain codomain candidate =
          .var candidate
        simp [fnDiagonalDelta, hshared, hcodomain]
  refine ⟨PairedMGU.fnDiagonal shared domain codomain domainNeShared
    domainNeCodomain codomainNeShared, CapSubst.id_supportWithin _, ?_,
    CapSubst.id_rangeWithin _, ?_, ?_, Subst.idempotent_of_capId deltaIdem⟩
  · intro candidate outside
    have hshared : ¬ candidate = shared := fun h => outside (by
      cases h
      simp [Ty.ftv])
    have hcodomain : ¬ candidate = codomain := fun h => outside (by
      cases h
      simp [Ty.ftv])
    simp [fnDiagonalDelta, hshared, hcodomain]
  · intro candidate mem image imageMem
    have imageMem' : image ∈
        (fnDiagonalDelta shared domain codomain candidate).ftv := imageMem
    by_cases hshared : candidate = shared
    · subst hshared
      rw [show fnDiagonalDelta candidate domain codomain candidate =
        .var domain from by simp [fnDiagonalDelta]] at imageMem'
      have h : image = domain := by simpa [Ty.ftv] using imageMem'
      subst h
      exact List.mem_append.mpr (Or.inr (by simp [Ty.ftv]))
    · by_cases hcodomain : candidate = codomain
      · subst hcodomain
        rw [show fnDiagonalDelta shared domain candidate candidate =
          .var domain from by
            simp [fnDiagonalDelta, fun h : candidate = shared =>
              codomainNeShared h]] at imageMem'
        have h : image = domain := by simpa [Ty.ftv] using imageMem'
        subst h
        exact List.mem_append.mpr (Or.inr (by simp [Ty.ftv]))
      · rw [show fnDiagonalDelta shared domain codomain candidate =
          .var candidate from by
            simp [fnDiagonalDelta, hshared, hcodomain]] at imageMem'
        have h : image = candidate := by simpa [Ty.ftv] using imageMem'
        simpa [h] using mem
  · intro candidate _ image imageMem
    have imageMem' : image ∈
        (fnDiagonalDelta shared domain codomain candidate).fcv := imageMem
    by_cases hshared : candidate = shared
    · subst hshared
      rw [show fnDiagonalDelta candidate domain codomain candidate =
        .var domain from by simp [fnDiagonalDelta]] at imageMem'
      have empty : (Ty.var domain).fcv = ([] : List CapVar) := rfl
      rw [empty] at imageMem'
      nomatch imageMem'
    · by_cases hcodomain : candidate = codomain
      · subst hcodomain
        rw [show fnDiagonalDelta shared domain candidate candidate =
          .var domain from by
            simp [fnDiagonalDelta, fun h : candidate = shared =>
              codomainNeShared h]] at imageMem'
        have empty : (Ty.var domain).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'
      · rw [show fnDiagonalDelta shared domain codomain candidate =
          .var candidate from by
            simp [fnDiagonalDelta, hshared, hcodomain]] at imageMem'
        have empty : (Ty.var candidate).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'

/-- The fresh function-alignment delta: substitute the two already-resolved
components for the two fresh variables. -/
def fnFreshDelta (domainImage codomainImage : Ty)
    (domainVar codomainVar : TypePM.TyVar) : TySubst :=
  fun candidate =>
    if candidate = domainVar then domainImage
    else if candidate = codomainVar then codomainImage
    else .var candidate

/-- Aligning a resolved function type against a fresh domain/codomain pair
is exactly solved by substituting the components for the fresh pair. -/
theorem ExactPairedMGU.fnFresh (domainImage codomainImage : Ty)
    (domainVar codomainVar : TypePM.TyVar)
    (domainVarFreshLeft : domainVar ∉ domainImage.ftv)
    (domainVarFreshRight : domainVar ∉ codomainImage.ftv)
    (codomainVarFreshLeft : codomainVar ∉ domainImage.ftv)
    (codomainVarFreshRight : codomainVar ∉ codomainImage.ftv)
    (varsDistinct : domainVar ≠ codomainVar) :
    ExactPairedMGU (.fn domainImage codomainImage)
      (.fn (.var domainVar) (.var codomainVar))
      ⟨CapSubst.id,
        fnFreshDelta domainImage codomainImage domainVar codomainVar⟩ := by
  have fixesDomain :
      domainImage.applyTarget
        (fnFreshDelta domainImage codomainImage domainVar codomainVar) =
        domainImage :=
    Ty.applyTarget_eq_self_of_ftv_fixed _ domainImage
      (fun candidate membership => by
        show (if candidate = domainVar then domainImage
          else if candidate = codomainVar then codomainImage
          else .var candidate) = .var candidate
        rw [if_neg (fun h : candidate = domainVar =>
            domainVarFreshLeft (h ▸ membership)),
          if_neg (fun h : candidate = codomainVar =>
            codomainVarFreshLeft (h ▸ membership))])
  have fixesCodomain :
      codomainImage.applyTarget
        (fnFreshDelta domainImage codomainImage domainVar codomainVar) =
        codomainImage :=
    Ty.applyTarget_eq_self_of_ftv_fixed _ codomainImage
      (fun candidate membership => by
        show (if candidate = domainVar then domainImage
          else if candidate = codomainVar then codomainImage
          else .var candidate) = .var candidate
        rw [if_neg (fun h : candidate = domainVar =>
            domainVarFreshRight (h ▸ membership)),
          if_neg (fun h : candidate = codomainVar =>
            codomainVarFreshRight (h ▸ membership))])
  have deltaIdem :
      (fnFreshDelta domainImage codomainImage domainVar
        codomainVar).Idempotent := by
    apply TySubst.idempotent_of_pointwise
    intro candidate
    by_cases hdomain : candidate = domainVar
    · subst hdomain
      rw [show fnFreshDelta domainImage codomainImage candidate codomainVar
        candidate = domainImage from if_pos rfl]
      exact fixesDomain
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnFreshDelta domainImage codomainImage domainVar candidate
          candidate = codomainImage from by
            show (if candidate = domainVar then domainImage
              else if candidate = candidate then codomainImage
              else .var candidate) = codomainImage
            rw [if_neg hdomain, if_pos rfl]]
        exact fixesCodomain
      · rw [show fnFreshDelta domainImage codomainImage domainVar codomainVar
          candidate = .var candidate from by
            show (if candidate = domainVar then domainImage
              else if candidate = codomainVar then codomainImage
              else .var candidate) = .var candidate
            rw [if_neg hdomain, if_neg hcodomain]]
        show (if candidate = domainVar then domainImage
          else if candidate = codomainVar then codomainImage
          else .var candidate) = .var candidate
        rw [if_neg hdomain, if_neg hcodomain]
  refine ⟨⟨?_, ?_⟩, CapSubst.id_supportWithin _, ?_,
    CapSubst.id_rangeWithin _, ?_, ?_, Subst.idempotent_of_capId deltaIdem⟩
  · show Ty.fn
        ((domainImage.applyCapability CapSubst.id).applyTarget
          (fnFreshDelta domainImage codomainImage domainVar codomainVar))
        ((codomainImage.applyCapability CapSubst.id).applyTarget
          (fnFreshDelta domainImage codomainImage domainVar codomainVar)) =
      Ty.fn
        (if domainVar = domainVar then domainImage
          else if domainVar = codomainVar then codomainImage
          else .var domainVar)
        (if codomainVar = domainVar then domainImage
          else if codomainVar = codomainVar then codomainImage
          else .var codomainVar)
    rw [Ty.applyCapability_id, Ty.applyCapability_id, fixesDomain,
      fixesCodomain, if_pos rfl,
      if_neg (fun h : codomainVar = domainVar => varsDistinct h.symm),
      if_pos rfl]
  · intro U unifies
    have components :
        Ty.fn (U.apply domainImage) (U.apply codomainImage) =
        Ty.fn (U.target domainVar) (U.target codomainVar) := unifies
    injection components with domainEq codomainEq
    refine ⟨U, ?_⟩
    have targetEq : U.target = fun candidate =>
        U.apply (fnFreshDelta domainImage codomainImage domainVar
          codomainVar candidate) := by
      funext candidate
      by_cases hdomain : candidate = domainVar
      · subst hdomain
        show U.target candidate =
          U.apply (if candidate = candidate then domainImage
            else if candidate = codomainVar then codomainImage
            else .var candidate)
        rw [if_pos rfl]
        exact domainEq.symm
      · by_cases hcodomain : candidate = codomainVar
        · subst hcodomain
          show U.target candidate =
            U.apply (if candidate = domainVar then domainImage
              else if candidate = candidate then codomainImage
              else .var candidate)
          rw [if_neg hdomain, if_pos rfl]
          exact codomainEq.symm
        · show U.target candidate =
            U.apply (if candidate = domainVar then domainImage
              else if candidate = codomainVar then codomainImage
              else .var candidate)
          rw [if_neg hdomain, if_neg hcodomain]
          rfl
    exact congrArg (Subst.mk U.cap) targetEq
  · intro candidate outside
    have hdomain : ¬ candidate = domainVar := fun h => outside (by
      cases h
      simp [Ty.ftv])
    have hcodomain : ¬ candidate = codomainVar := fun h => outside (by
      cases h
      simp [Ty.ftv])
    show (if candidate = domainVar then domainImage
      else if candidate = codomainVar then codomainImage
      else .var candidate) = .var candidate
    rw [if_neg hdomain, if_neg hcodomain]
  · intro candidate mem image imageMem
    have imageMem' : image ∈
        (fnFreshDelta domainImage codomainImage domainVar codomainVar
          candidate).ftv := imageMem
    by_cases hdomain : candidate = domainVar
    · subst hdomain
      rw [show fnFreshDelta domainImage codomainImage candidate codomainVar
        candidate = domainImage from if_pos rfl] at imageMem'
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl imageMem')))
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnFreshDelta domainImage codomainImage domainVar candidate
          candidate = codomainImage from by
            show (if candidate = domainVar then domainImage
              else if candidate = candidate then codomainImage
              else .var candidate) = codomainImage
            rw [if_neg hdomain, if_pos rfl]] at imageMem'
        exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr imageMem')))
      · rw [show fnFreshDelta domainImage codomainImage domainVar codomainVar
          candidate = .var candidate from by
            show (if candidate = domainVar then domainImage
              else if candidate = codomainVar then codomainImage
              else .var candidate) = .var candidate
            rw [if_neg hdomain, if_neg hcodomain]] at imageMem'
        have h : image = candidate := by simpa [Ty.ftv] using imageMem'
        simpa [h] using mem
  · intro candidate _ image imageMem
    have imageMem' : image ∈
        (fnFreshDelta domainImage codomainImage domainVar codomainVar
          candidate).fcv := imageMem
    by_cases hdomain : candidate = domainVar
    · subst hdomain
      rw [show fnFreshDelta domainImage codomainImage candidate codomainVar
        candidate = domainImage from if_pos rfl] at imageMem'
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl imageMem')))
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnFreshDelta domainImage codomainImage domainVar candidate
          candidate = codomainImage from by
            show (if candidate = domainVar then domainImage
              else if candidate = candidate then codomainImage
              else .var candidate) = codomainImage
            rw [if_neg hdomain, if_pos rfl]] at imageMem'
        exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr imageMem')))
      · rw [show fnFreshDelta domainImage codomainImage domainVar codomainVar
          candidate = .var candidate from by
            show (if candidate = domainVar then domainImage
              else if candidate = codomainVar then codomainImage
              else .var candidate) = .var candidate
            rw [if_neg hdomain, if_neg hcodomain]] at imageMem'
        have empty : (Ty.var candidate).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'

/-- The shared-domain function-alignment delta: both the shared variable and
the fresh codomain variable collapse onto the resolved domain image. -/
def fnSharedFreshDelta (sharedVar : TypePM.TyVar) (image : Ty)
    (codomainVar : TypePM.TyVar) : TySubst :=
  fun candidate =>
    if candidate = sharedVar then image
    else if candidate = codomainVar then image
    else .var candidate

/-- Aligning `fn ?s ?s` against a resolved domain with a fresh codomain is
exactly solved by collapsing both variables onto the domain image. -/
theorem ExactPairedMGU.fnSharedFresh (sharedVar : TypePM.TyVar) (image : Ty)
    (codomainVar : TypePM.TyVar)
    (sharedFresh : sharedVar ∉ image.ftv)
    (codomainFresh : codomainVar ∉ image.ftv)
    (varsDistinct : sharedVar ≠ codomainVar) :
    ExactPairedMGU (.fn (.var sharedVar) (.var sharedVar))
      (.fn image (.var codomainVar))
      ⟨CapSubst.id, fnSharedFreshDelta sharedVar image codomainVar⟩ := by
  have fixesImage :
      image.applyTarget (fnSharedFreshDelta sharedVar image codomainVar) =
        image :=
    Ty.applyTarget_eq_self_of_ftv_fixed _ image
      (fun candidate membership => by
        show (if candidate = sharedVar then image
          else if candidate = codomainVar then image
          else .var candidate) = .var candidate
        rw [if_neg (fun h : candidate = sharedVar =>
            sharedFresh (h ▸ membership)),
          if_neg (fun h : candidate = codomainVar =>
            codomainFresh (h ▸ membership))])
  have deltaIdem :
      (fnSharedFreshDelta sharedVar image codomainVar).Idempotent := by
    apply TySubst.idempotent_of_pointwise
    intro candidate
    by_cases hshared : candidate = sharedVar
    · subst hshared
      rw [show fnSharedFreshDelta candidate image codomainVar candidate =
        image from if_pos rfl]
      exact fixesImage
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnSharedFreshDelta sharedVar image candidate candidate =
          image from by
            show (if candidate = sharedVar then image
              else if candidate = candidate then image
              else .var candidate) = image
            rw [if_neg hshared, if_pos rfl]]
        exact fixesImage
      · rw [show fnSharedFreshDelta sharedVar image codomainVar candidate =
          .var candidate from by
            show (if candidate = sharedVar then image
              else if candidate = codomainVar then image
              else .var candidate) = .var candidate
            rw [if_neg hshared, if_neg hcodomain]]
        show (if candidate = sharedVar then image
          else if candidate = codomainVar then image
          else .var candidate) = .var candidate
        rw [if_neg hshared, if_neg hcodomain]
  refine ⟨⟨?_, ?_⟩, CapSubst.id_supportWithin _, ?_,
    CapSubst.id_rangeWithin _, ?_, ?_, Subst.idempotent_of_capId deltaIdem⟩
  · show Ty.fn
        (if sharedVar = sharedVar then image
          else if sharedVar = codomainVar then image else .var sharedVar)
        (if sharedVar = sharedVar then image
          else if sharedVar = codomainVar then image else .var sharedVar) =
      Ty.fn
        ((image.applyCapability CapSubst.id).applyTarget
          (fnSharedFreshDelta sharedVar image codomainVar))
        (if codomainVar = sharedVar then image
          else if codomainVar = codomainVar then image
          else .var codomainVar)
    rw [Ty.applyCapability_id, fixesImage, if_pos rfl,
      if_neg (fun h : codomainVar = sharedVar => varsDistinct h.symm),
      if_pos rfl]
  · intro U unifies
    have components :
        Ty.fn (U.target sharedVar) (U.target sharedVar) =
        Ty.fn (U.apply image) (U.target codomainVar) := unifies
    injection components with domainEq codomainEq
    refine ⟨U, ?_⟩
    have targetEq : U.target = fun candidate =>
        U.apply (fnSharedFreshDelta sharedVar image codomainVar
          candidate) := by
      funext candidate
      by_cases hshared : candidate = sharedVar
      · subst hshared
        show U.target candidate =
          U.apply (if candidate = candidate then image
            else if candidate = codomainVar then image
            else .var candidate)
        rw [if_pos rfl]
        exact domainEq
      · by_cases hcodomain : candidate = codomainVar
        · subst hcodomain
          show U.target candidate =
            U.apply (if candidate = sharedVar then image
              else if candidate = candidate then image
              else .var candidate)
          rw [if_neg hshared, if_pos rfl]
          exact codomainEq.symm.trans domainEq
        · show U.target candidate =
            U.apply (if candidate = sharedVar then image
              else if candidate = codomainVar then image
              else .var candidate)
          rw [if_neg hshared, if_neg hcodomain]
          rfl
    exact congrArg (Subst.mk U.cap) targetEq
  · intro candidate outside
    have hshared : ¬ candidate = sharedVar := fun h => outside (by
      cases h
      simp [Ty.ftv])
    have hcodomain : ¬ candidate = codomainVar := fun h => outside (by
      cases h
      simp [Ty.ftv])
    show (if candidate = sharedVar then image
      else if candidate = codomainVar then image
      else .var candidate) = .var candidate
    rw [if_neg hshared, if_neg hcodomain]
  · intro candidate mem imageVar imageMem
    have imageMem' : imageVar ∈
        (fnSharedFreshDelta sharedVar image codomainVar candidate).ftv :=
      imageMem
    by_cases hshared : candidate = sharedVar
    · subst hshared
      rw [show fnSharedFreshDelta candidate image codomainVar candidate =
        image from if_pos rfl] at imageMem'
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl imageMem')))
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnSharedFreshDelta sharedVar image candidate candidate =
          image from by
            show (if candidate = sharedVar then image
              else if candidate = candidate then image
              else .var candidate) = image
            rw [if_neg hshared, if_pos rfl]] at imageMem'
        exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inl imageMem')))
      · rw [show fnSharedFreshDelta sharedVar image codomainVar candidate =
          .var candidate from by
            show (if candidate = sharedVar then image
              else if candidate = codomainVar then image
              else .var candidate) = .var candidate
            rw [if_neg hshared, if_neg hcodomain]] at imageMem'
        have h : imageVar = candidate := by simpa [Ty.ftv] using imageMem'
        simpa [h] using mem
  · intro candidate _ imageVar imageMem
    have imageMem' : imageVar ∈
        (fnSharedFreshDelta sharedVar image codomainVar candidate).fcv :=
      imageMem
    by_cases hshared : candidate = sharedVar
    · subst hshared
      rw [show fnSharedFreshDelta candidate image codomainVar candidate =
        image from if_pos rfl] at imageMem'
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl imageMem')))
    · by_cases hcodomain : candidate = codomainVar
      · subst hcodomain
        rw [show fnSharedFreshDelta sharedVar image candidate candidate =
          image from by
            show (if candidate = sharedVar then image
              else if candidate = candidate then image
              else .var candidate) = image
            rw [if_neg hshared, if_pos rfl]] at imageMem'
        exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inl imageMem')))
      · rw [show fnSharedFreshDelta sharedVar image codomainVar candidate =
          .var candidate from by
            show (if candidate = sharedVar then image
              else if candidate = codomainVar then image
              else .var candidate) = .var candidate
            rw [if_neg hshared, if_neg hcodomain]] at imageMem'
        have empty : (Ty.var candidate).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'

/-! ### No-guess metatheory of most general solve deltas

Universality alone already bounds what a most general solve delta may do to
variables the constraint does not force.  Any variable kept fixed by some
unifier of the constraint is mapped to a bare variable; variables outside
the constraint are therefore at most renamed, never structured; and two
distinct outside variables are never collapsed.  This is the no-guess
principle as a theorem about the solve-delta specifications themselves —
no additional relevance side condition is needed to rule out structuring an
unrelated metavariable.
-/

/-- A capability whose substitution image is a bare variable is itself a
bare variable. -/
theorem Cap.eq_var_of_apply_var {capability : Cap} {R : CapSubst}
    {image : CapVar} (applied : capability.apply R = .var image) :
    ∃ varId, capability = .var varId := by
  cases capability with
  | var varId => exact ⟨varId, rfl⟩
  | any => nomatch applied
  | skolem varId => nomatch applied
  | con name children => nomatch applied
  | prod components => nomatch applied

/-- A type whose target-substitution image is a bare variable is itself a
bare variable. -/
theorem Ty.eq_var_of_applyTarget_var {target : Ty} {T : TySubst}
    {image : TypePM.TyVar} (applied : target.applyTarget T = .var image) :
    ∃ varId, target = .var varId := by
  cases target with
  | var varId => exact ⟨varId, rfl⟩
  | skolem varId => nomatch applied
  | unit => nomatch applied
  | int => nomatch applied
  | bool => nomatch applied
  | data name arguments => nomatch applied
  | prod components => nomatch applied
  | fn domain codomain => nomatch applied
  | matcher capability inner => nomatch applied
  | slot capability inner => nomatch applied

/-- A type whose paired-substitution image is a bare variable is itself a
bare variable. -/
theorem Ty.eq_var_of_apply_var {target : Ty} {R : Subst}
    {image : TypePM.TyVar} (applied : R.apply target = .var image) :
    ∃ varId, target = .var varId := by
  cases target with
  | var varId => exact ⟨varId, rfl⟩
  | skolem varId => nomatch applied
  | unit => nomatch applied
  | int => nomatch applied
  | bool => nomatch applied
  | data name arguments => nomatch applied
  | prod components => nomatch applied
  | fn domain codomain => nomatch applied
  | matcher capability inner => nomatch applied
  | slot capability inner => nomatch applied

/-- Target application depends only on the free target leaves of its
input. -/
theorem Ty.applyTarget_eq_of_ftv_agree (left right : TySubst) (target : Ty)
    (agree : ∀ varId, varId ∈ target.ftv → left varId = right varId) :
    target.applyTarget left = target.applyTarget right := by
  have paired := Subst.apply_eq_of_free_agree ⟨CapSubst.id, left⟩
    ⟨CapSubst.id, right⟩ target (fun _ _ => rfl) agree
  simpa [Subst.apply, Ty.applyCapability_id] using paired

/-- Most general capability unification is symmetric in its constraint. -/
theorem CapMGU.symm {left right : Cap} {subst : CapSubst}
    (mgu : CapMGU left right subst) : CapMGU right left subst :=
  ⟨mgu.1.symm, fun U unifies => mgu.2 U unifies.symm⟩

/-- Most general target unification is symmetric in its constraint. -/
theorem TargetMGU.symm {left right : Ty} {subst : TySubst}
    (mgu : TargetMGU left right subst) : TargetMGU right left subst :=
  ⟨mgu.1.symm, fun U unifies => mgu.2 U unifies.symm⟩

/-- Most general paired unification is symmetric in its constraint. -/
theorem PairedMGU.symm {left right : Ty} {subst : Subst}
    (mgu : PairedMGU left right subst) : PairedMGU right left subst :=
  ⟨mgu.1.symm, fun U unifies => mgu.2 U unifies.symm⟩

/-- Any variable kept fixed by some unifier of the constraint is mapped to
a bare variable by every most general capability solution. -/
theorem CapMGU.image_var_of_fixing_unifier {left right : Cap}
    {subst : CapSubst} (mgu : CapMGU left right subst) {U : CapSubst}
    (unifies : left.apply U = right.apply U) {varId : CapVar}
    (fixed : U varId = .var varId) :
    ∃ image, subst varId = .var image := by
  obtain ⟨R, factored⟩ := mgu.2 U unifies
  have pointwise : U varId = (subst varId).apply R := congrFun factored varId
  rw [fixed] at pointwise
  exact Cap.eq_var_of_apply_var pointwise.symm

/-- A most general capability solution maps every variable outside its
constraint to a bare variable: outside variables are at most renamed. -/
theorem CapMGU.outside_image_var {left right : Cap} {subst : CapSubst}
    (mgu : CapMGU left right subst) {varId : CapVar}
    (leftOutside : varId ∉ left.fcv) (rightOutside : varId ∉ right.fcv) :
    ∃ image, subst varId = .var image := by
  refine mgu.image_var_of_fixing_unifier
    (U := fun candidate =>
      if candidate = varId then .var varId else subst candidate)
    ?_ (if_pos rfl)
  have leftEq := Cap.apply_eq_of_fcv_agree
    (fun candidate =>
      if candidate = varId then .var varId else subst candidate) subst left
    (fun candidate membership =>
      if_neg fun h : candidate = varId => leftOutside (h ▸ membership))
  have rightEq := Cap.apply_eq_of_fcv_agree
    (fun candidate =>
      if candidate = varId then .var varId else subst candidate) subst right
    (fun candidate membership =>
      if_neg fun h : candidate = varId => rightOutside (h ▸ membership))
  rw [leftEq, rightEq]
  exact mgu.1

/-- A most general capability solution never collapses two distinct
variables outside its constraint. -/
theorem CapMGU.outside_injective {left right : Cap} {subst : CapSubst}
    (mgu : CapMGU left right subst) {varId otherId : CapVar}
    (varLeftOutside : varId ∉ left.fcv)
    (varRightOutside : varId ∉ right.fcv)
    (otherLeftOutside : otherId ∉ left.fcv)
    (otherRightOutside : otherId ∉ right.fcv)
    (collapsed : subst varId = subst otherId) : varId = otherId := by
  by_cases hcase : varId = otherId
  · exact hcase
  exfalso
  have hne : ¬ otherId = varId := fun h => hcase h.symm
  have unifies :
      left.apply (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) =
      right.apply (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) := by
    have leftEq := Cap.apply_eq_of_fcv_agree
      (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) subst left
      (fun candidate membership => by
        rw [if_neg fun h : candidate = varId => varLeftOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherLeftOutside (h ▸ membership)])
    have rightEq := Cap.apply_eq_of_fcv_agree
      (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) subst right
      (fun candidate membership => by
        rw [if_neg fun h : candidate = varId => varRightOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherRightOutside (h ▸ membership)])
    rw [leftEq, rightEq]
    exact mgu.1
  obtain ⟨R, factored⟩ := mgu.2 _ unifies
  have varPointwise : Cap.var varId = (subst varId).apply R := by
    simpa [CapSubst.comp] using congrFun factored varId
  have otherPointwise : Cap.var otherId = (subst otherId).apply R := by
    simpa [hne, CapSubst.comp] using congrFun factored otherId
  rw [collapsed] at varPointwise
  have images : Cap.var varId = Cap.var otherId :=
    varPointwise.trans otherPointwise.symm
  injection images with h
  exact hcase h

/-- Any variable kept fixed by some unifier of the constraint is mapped to
a bare variable by every most general target solution. -/
theorem TargetMGU.image_var_of_fixing_unifier {left right : Ty}
    {subst : TySubst} (mgu : TargetMGU left right subst) {U : TySubst}
    (unifies : left.applyTarget U = right.applyTarget U)
    {varId : TypePM.TyVar} (fixed : U varId = .var varId) :
    ∃ image, subst varId = .var image := by
  obtain ⟨R, factored⟩ := mgu.2 U unifies
  have pointwise : U varId = (subst varId).applyTarget R :=
    congrFun factored varId
  rw [fixed] at pointwise
  exact Ty.eq_var_of_applyTarget_var pointwise.symm

/-- A most general target solution maps every variable outside its
constraint to a bare variable. -/
theorem TargetMGU.outside_image_var {left right : Ty} {subst : TySubst}
    (mgu : TargetMGU left right subst) {varId : TypePM.TyVar}
    (leftOutside : varId ∉ left.ftv) (rightOutside : varId ∉ right.ftv) :
    ∃ image, subst varId = .var image := by
  refine mgu.image_var_of_fixing_unifier
    (U := fun candidate =>
      if candidate = varId then .var varId else subst candidate)
    ?_ (if_pos rfl)
  have leftEq := Ty.applyTarget_eq_of_ftv_agree
    (fun candidate =>
      if candidate = varId then .var varId else subst candidate) subst left
    (fun candidate membership =>
      if_neg fun h : candidate = varId => leftOutside (h ▸ membership))
  have rightEq := Ty.applyTarget_eq_of_ftv_agree
    (fun candidate =>
      if candidate = varId then .var varId else subst candidate) subst right
    (fun candidate membership =>
      if_neg fun h : candidate = varId => rightOutside (h ▸ membership))
  rw [leftEq, rightEq]
  exact mgu.1

/-- A most general target solution never collapses two distinct variables
outside its constraint. -/
theorem TargetMGU.outside_injective {left right : Ty} {subst : TySubst}
    (mgu : TargetMGU left right subst) {varId otherId : TypePM.TyVar}
    (varLeftOutside : varId ∉ left.ftv)
    (varRightOutside : varId ∉ right.ftv)
    (otherLeftOutside : otherId ∉ left.ftv)
    (otherRightOutside : otherId ∉ right.ftv)
    (collapsed : subst varId = subst otherId) : varId = otherId := by
  by_cases hcase : varId = otherId
  · exact hcase
  exfalso
  have hne : ¬ otherId = varId := fun h => hcase h.symm
  have unifies :
      left.applyTarget (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) =
      right.applyTarget (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) := by
    have leftEq := Ty.applyTarget_eq_of_ftv_agree
      (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) subst left
      (fun candidate membership => by
        rw [if_neg fun h : candidate = varId => varLeftOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherLeftOutside (h ▸ membership)])
    have rightEq := Ty.applyTarget_eq_of_ftv_agree
      (fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst candidate) subst right
      (fun candidate membership => by
        rw [if_neg fun h : candidate = varId => varRightOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherRightOutside (h ▸ membership)])
    rw [leftEq, rightEq]
    exact mgu.1
  obtain ⟨R, factored⟩ := mgu.2 _ unifies
  have varPointwise : Ty.var varId = (subst varId).applyTarget R := by
    simpa [TySubst.comp] using congrFun factored varId
  have otherPointwise : Ty.var otherId = (subst otherId).applyTarget R := by
    simpa [hne, TySubst.comp] using congrFun factored otherId
  rw [collapsed] at varPointwise
  have images : Ty.var varId = Ty.var otherId :=
    varPointwise.trans otherPointwise.symm
  injection images with h
  exact hcase h

/-- Any target variable kept fixed by some paired unifier of the constraint
is mapped to a bare variable by every most general paired solution. -/
theorem PairedMGU.target_image_var_of_fixing_unifier {left right : Ty}
    {subst : Subst} (mgu : PairedMGU left right subst) {U : Subst}
    (unifies : U.apply left = U.apply right) {varId : TypePM.TyVar}
    (fixed : U.target varId = .var varId) :
    ∃ image, subst.target varId = .var image := by
  obtain ⟨R, factored⟩ := mgu.2 U unifies
  have pointwise : U.target varId = R.apply (subst.target varId) := by
    rw [factored]; rfl
  rw [fixed] at pointwise
  exact Ty.eq_var_of_apply_var pointwise.symm

/-- Any capability variable kept fixed by some paired unifier of the
constraint is mapped to a bare variable by every most general paired
solution. -/
theorem PairedMGU.cap_image_var_of_fixing_unifier {left right : Ty}
    {subst : Subst} (mgu : PairedMGU left right subst) {U : Subst}
    (unifies : U.apply left = U.apply right) {varId : CapVar}
    (fixed : U.cap varId = .var varId) :
    ∃ image, subst.cap varId = .var image := by
  obtain ⟨R, factored⟩ := mgu.2 U unifies
  have pointwise : U.cap varId = (subst.cap varId).apply R.cap := by
    rw [factored]; rfl
  rw [fixed] at pointwise
  exact Cap.eq_var_of_apply_var pointwise.symm

/-- A most general paired solution maps every target variable outside its
constraint to a bare variable. -/
theorem PairedMGU.outside_target_image_var {left right : Ty} {subst : Subst}
    (mgu : PairedMGU left right subst) {varId : TypePM.TyVar}
    (leftOutside : varId ∉ left.ftv) (rightOutside : varId ∉ right.ftv) :
    ∃ image, subst.target varId = .var image := by
  refine mgu.target_image_var_of_fixing_unifier
    (U := ⟨subst.cap, fun candidate =>
      if candidate = varId then .var varId else subst.target candidate⟩)
    ?_ (if_pos rfl)
  have leftEq := Subst.apply_eq_of_free_agree
    ⟨subst.cap, fun candidate =>
      if candidate = varId then .var varId else subst.target candidate⟩
    subst left (fun _ _ => rfl)
    (fun candidate membership =>
      if_neg fun h : candidate = varId => leftOutside (h ▸ membership))
  have rightEq := Subst.apply_eq_of_free_agree
    ⟨subst.cap, fun candidate =>
      if candidate = varId then .var varId else subst.target candidate⟩
    subst right (fun _ _ => rfl)
    (fun candidate membership =>
      if_neg fun h : candidate = varId => rightOutside (h ▸ membership))
  rw [leftEq, rightEq]
  exact mgu.1

/-- A most general paired solution maps every capability variable outside
its constraint to a bare variable. -/
theorem PairedMGU.outside_cap_image_var {left right : Ty} {subst : Subst}
    (mgu : PairedMGU left right subst) {varId : CapVar}
    (leftOutside : varId ∉ left.fcv) (rightOutside : varId ∉ right.fcv) :
    ∃ image, subst.cap varId = .var image := by
  refine mgu.cap_image_var_of_fixing_unifier
    (U := ⟨fun candidate =>
      if candidate = varId then .var varId else subst.cap candidate,
      subst.target⟩)
    ?_ (if_pos rfl)
  have leftEq := Subst.apply_eq_of_free_agree
    ⟨fun candidate =>
      if candidate = varId then .var varId else subst.cap candidate,
      subst.target⟩
    subst left
    (fun candidate membership =>
      if_neg fun h : candidate = varId => leftOutside (h ▸ membership))
    (fun _ _ => rfl)
  have rightEq := Subst.apply_eq_of_free_agree
    ⟨fun candidate =>
      if candidate = varId then .var varId else subst.cap candidate,
      subst.target⟩
    subst right
    (fun candidate membership =>
      if_neg fun h : candidate = varId => rightOutside (h ▸ membership))
    (fun _ _ => rfl)
  rw [leftEq, rightEq]
  exact mgu.1

/-- A most general paired solution never collapses two distinct target
variables outside its constraint. -/
theorem PairedMGU.outside_target_injective {left right : Ty} {subst : Subst}
    (mgu : PairedMGU left right subst) {varId otherId : TypePM.TyVar}
    (varLeftOutside : varId ∉ left.ftv)
    (varRightOutside : varId ∉ right.ftv)
    (otherLeftOutside : otherId ∉ left.ftv)
    (otherRightOutside : otherId ∉ right.ftv)
    (collapsed : subst.target varId = subst.target otherId) :
    varId = otherId := by
  by_cases hcase : varId = otherId
  · exact hcase
  exfalso
  have hne : ¬ otherId = varId := fun h => hcase h.symm
  have unifies :
      Subst.apply
        ⟨subst.cap, fun candidate =>
          if candidate = varId then .var varId
          else if candidate = otherId then .var otherId
          else subst.target candidate⟩ left =
      Subst.apply
        ⟨subst.cap, fun candidate =>
          if candidate = varId then .var varId
          else if candidate = otherId then .var otherId
          else subst.target candidate⟩ right := by
    have leftEq := Subst.apply_eq_of_free_agree
      ⟨subst.cap, fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst.target candidate⟩
      subst left (fun _ _ => rfl)
      (fun candidate membership => by
        show (if candidate = varId then Ty.var varId
          else if candidate = otherId then Ty.var otherId
          else subst.target candidate) = subst.target candidate
        rw [if_neg fun h : candidate = varId => varLeftOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherLeftOutside (h ▸ membership)])
    have rightEq := Subst.apply_eq_of_free_agree
      ⟨subst.cap, fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst.target candidate⟩
      subst right (fun _ _ => rfl)
      (fun candidate membership => by
        show (if candidate = varId then Ty.var varId
          else if candidate = otherId then Ty.var otherId
          else subst.target candidate) = subst.target candidate
        rw [if_neg fun h : candidate = varId => varRightOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherRightOutside (h ▸ membership)])
    rw [leftEq, rightEq]
    exact mgu.1
  obtain ⟨R, factored⟩ := mgu.2 _ unifies
  have varPointwise : Ty.var varId = R.apply (subst.target varId) := by
    simpa [Subst.seq] using congrArg (fun S => Subst.target S varId) factored
  have otherPointwise : Ty.var otherId = R.apply (subst.target otherId) := by
    simpa [hne, Subst.seq] using congrArg (fun S => Subst.target S otherId)
      factored
  rw [collapsed] at varPointwise
  have images : Ty.var varId = Ty.var otherId :=
    varPointwise.trans otherPointwise.symm
  injection images with h
  exact hcase h

/-- A most general paired solution never collapses two distinct capability
variables outside its constraint. -/
theorem PairedMGU.outside_cap_injective {left right : Ty} {subst : Subst}
    (mgu : PairedMGU left right subst) {varId otherId : CapVar}
    (varLeftOutside : varId ∉ left.fcv)
    (varRightOutside : varId ∉ right.fcv)
    (otherLeftOutside : otherId ∉ left.fcv)
    (otherRightOutside : otherId ∉ right.fcv)
    (collapsed : subst.cap varId = subst.cap otherId) : varId = otherId := by
  by_cases hcase : varId = otherId
  · exact hcase
  exfalso
  have hne : ¬ otherId = varId := fun h => hcase h.symm
  have unifies :
      Subst.apply
        ⟨fun candidate =>
          if candidate = varId then .var varId
          else if candidate = otherId then .var otherId
          else subst.cap candidate, subst.target⟩ left =
      Subst.apply
        ⟨fun candidate =>
          if candidate = varId then .var varId
          else if candidate = otherId then .var otherId
          else subst.cap candidate, subst.target⟩ right := by
    have leftEq := Subst.apply_eq_of_free_agree
      ⟨fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst.cap candidate, subst.target⟩
      subst left
      (fun candidate membership => by
        show (if candidate = varId then Cap.var varId
          else if candidate = otherId then Cap.var otherId
          else subst.cap candidate) = subst.cap candidate
        rw [if_neg fun h : candidate = varId => varLeftOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherLeftOutside (h ▸ membership)])
      (fun _ _ => rfl)
    have rightEq := Subst.apply_eq_of_free_agree
      ⟨fun candidate =>
        if candidate = varId then .var varId
        else if candidate = otherId then .var otherId
        else subst.cap candidate, subst.target⟩
      subst right
      (fun candidate membership => by
        show (if candidate = varId then Cap.var varId
          else if candidate = otherId then Cap.var otherId
          else subst.cap candidate) = subst.cap candidate
        rw [if_neg fun h : candidate = varId => varRightOutside (h ▸ membership),
          if_neg fun h : candidate = otherId =>
            otherRightOutside (h ▸ membership)])
      (fun _ _ => rfl)
    rw [leftEq, rightEq]
    exact mgu.1
  obtain ⟨R, factored⟩ := mgu.2 _ unifies
  have varPointwise : Cap.var varId = (subst.cap varId).apply R.cap := by
    simpa [Subst.seq, CapSubst.comp] using
      congrArg (fun S => Subst.cap S varId) factored
  have otherPointwise : Cap.var otherId = (subst.cap otherId).apply R.cap := by
    simpa [hne, Subst.seq, CapSubst.comp] using
      congrArg (fun S => Subst.cap S otherId) factored
  rw [collapsed] at varPointwise
  have images : Cap.var varId = Cap.var otherId :=
    varPointwise.trans otherPointwise.symm
  injection images with h
  exact hcase h

/-- Against a variable-versus-type constraint whose variable does not occur
in the type, a most general paired solution maps every other target
variable to a bare variable.  This is the shape of every fresh
domain/codomain alignment: solving the constraint may rename the fresh
variables but can never structure them. -/
theorem PairedMGU.varConstraint_target_image_var
    {domainVar : TypePM.TyVar} {shape : Ty} {subst : Subst}
    (mgu : PairedMGU (.var domainVar) shape subst)
    (occurs : domainVar ∉ shape.ftv) {varId : TypePM.TyVar}
    (distinct : varId ≠ domainVar) :
    ∃ image, subst.target varId = .var image := by
  have fixesShape :
      shape.applyTarget (fun candidate =>
        if candidate = domainVar then shape else .var candidate) = shape :=
    Ty.applyTarget_eq_self_of_ftv_fixed _ shape
      (fun candidate membership =>
        if_neg fun h : candidate = domainVar => occurs (h ▸ membership))
  refine mgu.target_image_var_of_fixing_unifier
    (U := ⟨CapSubst.id, fun candidate =>
      if candidate = domainVar then shape else .var candidate⟩)
    ?_ (if_neg distinct)
  show ((Ty.var domainVar).applyCapability CapSubst.id).applyTarget
      (fun candidate =>
        if candidate = domainVar then shape else .var candidate) =
    (shape.applyCapability CapSubst.id).applyTarget
      (fun candidate =>
        if candidate = domainVar then shape else .var candidate)
  rw [Ty.applyCapability_id, Ty.applyCapability_id, fixesShape]
  show (if domainVar = domainVar then shape else Ty.var domainVar) = shape
  rw [if_pos rfl]

/-! ## Deterministic branch classifiers

Checking dispatches on cut-resolved views only.  The classifiers make the
branch choice a function of the two resolved types, so the coercion rules of
`DDAlign` are mutually exclusive by construction and the selector-determinacy
principle holds definitionally.
-/

/-- Head classification for ordinary equality alignment. -/
inductive AlignPairClass where
  | matcherPair
  | slotPair
  | ordinary
deriving Repr, DecidableEq

/-- Classify one resolved pair for ordinary equality alignment. -/
def alignPairClass : Ty → Ty → AlignPairClass
  | .matcher _ _, .matcher _ _ => .matcherPair
  | .slot _ _, .slot _ _ => .slotPair
  | _, _ => .ordinary

/-- Branch classification at one checking cut. -/
inductive DemandClass where
  | productMatcherLift
  | slotTupleLift
  | matcherToSlot
  | slotToSlot
  | ordinary
deriving Repr, DecidableEq

/-- Classify one checking cut from the resolved source and expected views.
Product-of-matchers has precedence for the empty product, mirroring the
executable selector.  Every non-`ordinary` class requires a slot-headed
expected view: this is the slot-demand principle as a case split. -/
def demandClass (source expected : Ty) : DemandClass :=
  match productMatcherDuals? source, productSlotDuals? source, expected with
  | some _, _, .slot _ _ => .productMatcherLift
  | _, some _, .slot _ _ => .slotTupleLift
  | _, _, _ =>
    match source, expected with
    | .matcher _ _, .slot _ _ => .matcherToSlot
    | .slot _ _, .slot _ _ => .slotToSlot
    | _, _ => .ordinary

/-- Every non-identity demand class exposes a slot-headed expected view. -/
theorem demandClass_slotDemand {source expected : Ty}
    (nonOrdinary : demandClass source expected ≠ .ordinary) :
    ∃ consumerCap consumerTarget,
      expected = .slot consumerCap consumerTarget := by
  unfold demandClass at nonOrdinary
  split at nonOrdinary
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · split at nonOrdinary
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact absurd rfl nonOrdinary

/-- A matcher-headed expectation is never a coercion demand. -/
theorem demandClass_matcherExpected (source : Ty)
    {consumerCap : Cap} {consumerTarget : Ty} :
    demandClass source (.matcher consumerCap consumerTarget) = .ordinary := by
  unfold demandClass
  split <;> (try split) <;> simp_all

/-! ## State-threaded alignment relations

`DDAlignTypes` mirrors ordinary equality alignment: annotated pairs solve the
capability sort first and then the capability-adjusted targets; every other
pair is one paired solve of the resolved views.  `DDAlign` is the complete
checking cut: branch selection by `demandClass` on the resolved views,
followed by the alignment steps of the selected branch.  Each solve composes
its delta onto the prevailing substitution with cross-sort-aware sequencing.
-/

/-- Ordinary equality alignment at one cut. -/
inductive DDAlignTypes : Subst → Ty → Ty → Subst → Prop where
  | matcherPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .matcher leftCap leftTarget →
      S.apply right = .matcher rightCap rightTarget →
      ExactCapMGU leftCap rightCap capDelta →
      ExactPairedMGU (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypes S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | slotPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .slot leftCap leftTarget →
      S.apply right = .slot rightCap rightTarget →
      ExactCapMGU leftCap rightCap capDelta →
      ExactPairedMGU (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypes S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {left right : Ty} {delta : Subst} :
      alignPairClass (S.apply left) (S.apply right) = .ordinary →
      ExactPairedMGU (S.apply left) (S.apply right) delta →
      DDAlignTypes S left right (Subst.seq delta S)

/-- The complete checking cut: demand-classified coercion selection and
alignment of one raw synthesized type against one raw expected type. -/
inductive DDAlign : Subst → Ty → Ty → Subst → Prop where
  | productMatcherLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      productMatcherDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      OneWayDelta (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))
        consumerCap consumerTarget delta →
      DDAlign S raw expected (Subst.seq delta S)
  | slotTupleLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .slotTupleLift →
      productSlotDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      ExactCapMGU (.prod (duals.map Dual.cap)) consumerCap capDelta →
      ExactPairedMGU
        ((Ty.prod (duals.map Dual.target)).applyCapability capDelta)
        (consumerTarget.applyCapability capDelta) targetDelta →
      DDAlign S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | matcherToSlot {S : Subst} {raw expected : Ty}
      {producerCap : Cap} {producerTarget : Ty}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      S.apply raw = .matcher producerCap producerTarget →
      S.apply expected = .slot consumerCap consumerTarget →
      OneWayDelta producerCap producerTarget consumerCap consumerTarget
        delta →
      DDAlign S raw expected (Subst.seq delta S)
  | slotToSlot {S : Subst} {raw expected : Ty}
      {sourceCap : Cap} {sourceTarget : Ty}
      {requestedCap : Cap} {requestedTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply raw = .slot sourceCap sourceTarget →
      S.apply expected = .slot requestedCap requestedTarget →
      ExactCapMGU sourceCap requestedCap capDelta →
      ExactPairedMGU (sourceTarget.applyCapability capDelta)
        (requestedTarget.applyCapability capDelta) targetDelta →
      DDAlign S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {raw expected : Ty} {S' : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .ordinary →
      DDAlignTypes S raw expected S' →
      DDAlign S raw expected S'

/-! The ledger-aware forms below are additive counterparts of the existing
alignment relations.  They expose the same output substitution, but every
local solve must also respect the capability-origin policy at this cut. -/

/-- Origin-safe ordinary equality alignment at one cut. -/
inductive DDAlignTypesWithLedger (ledger : CapabilityOriginLedger) :
    Subst → Ty → Ty → Subst → Prop where
  | matcherPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .matcher leftCap leftTarget →
      S.apply right = .matcher rightCap rightTarget →
      OriginSafeExactCapMGU ledger leftCap rightCap capDelta →
      OriginSafeExactPairedMGU ledger
        (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypesWithLedger ledger S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | slotPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .slot leftCap leftTarget →
      S.apply right = .slot rightCap rightTarget →
      OriginSafeExactCapMGU ledger leftCap rightCap capDelta →
      OriginSafeExactPairedMGU ledger
        (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypesWithLedger ledger S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {left right : Ty} {delta : Subst} :
      alignPairClass (S.apply left) (S.apply right) = .ordinary →
      OriginSafeExactPairedMGU ledger (S.apply left) (S.apply right) delta →
      DDAlignTypesWithLedger ledger S left right (Subst.seq delta S)

/-- Origin-safe complete checking-cut alignment. -/
inductive DDAlignWithLedger (ledger : CapabilityOriginLedger) :
    Subst → Ty → Ty → Subst → Prop where
  | productMatcherLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      productMatcherDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      OriginSafeOneWayDelta ledger (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) consumerCap consumerTarget delta →
      DDAlignWithLedger ledger S raw expected (Subst.seq delta S)
  | slotTupleLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .slotTupleLift →
      productSlotDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      OriginSafeExactCapMGU ledger (.prod (duals.map Dual.cap)) consumerCap
        capDelta →
      OriginSafeExactPairedMGU ledger
        ((Ty.prod (duals.map Dual.target)).applyCapability capDelta)
        (consumerTarget.applyCapability capDelta) targetDelta →
      DDAlignWithLedger ledger S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | matcherToSlot {S : Subst} {raw expected : Ty}
      {producerCap : Cap} {producerTarget : Ty}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      S.apply raw = .matcher producerCap producerTarget →
      S.apply expected = .slot consumerCap consumerTarget →
      OriginSafeOneWayDelta ledger producerCap producerTarget consumerCap
        consumerTarget delta →
      DDAlignWithLedger ledger S raw expected (Subst.seq delta S)
  | slotToSlot {S : Subst} {raw expected : Ty}
      {sourceCap : Cap} {sourceTarget : Ty}
      {requestedCap : Cap} {requestedTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply raw = .slot sourceCap sourceTarget →
      S.apply expected = .slot requestedCap requestedTarget →
      OriginSafeExactCapMGU ledger sourceCap requestedCap capDelta →
      OriginSafeExactPairedMGU ledger
        (sourceTarget.applyCapability capDelta)
        (requestedTarget.applyCapability capDelta) targetDelta →
      DDAlignWithLedger ledger S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {raw expected : Ty} {S' : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .ordinary →
      DDAlignTypesWithLedger ledger S raw expected S' →
      DDAlignWithLedger ledger S raw expected S'

/-- Ledger-aware ordinary alignment makes its two inputs equal under the
output substitution. -/
theorem DDAlignTypesWithLedger.output_equal
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst}
    (aligned : DDAlignTypesWithLedger ledger S left right S') :
    S'.apply left = S'.apply right := by
  cases aligned with
  | matcherPair leftView rightView capSafe targetSafe =>
      rw [Subst.seq_apply, Subst.seq_apply,
        Subst.seq_apply, Subst.seq_apply, leftView, rightView]
      have capEqual := capSafe.exact.1.1
      have targetEqual := targetSafe.exact.1.1
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget_id]
        at targetEqual ⊢
      rw [capEqual]
      exact congrArg (Ty.matcher _) targetEqual
  | slotPair leftView rightView capSafe targetSafe =>
      rw [Subst.seq_apply, Subst.seq_apply,
        Subst.seq_apply, Subst.seq_apply, leftView, rightView]
      have capEqual := capSafe.exact.1.1
      have targetEqual := targetSafe.exact.1.1
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget_id]
        at targetEqual ⊢
      rw [capEqual]
      exact congrArg (Ty.slot _) targetEqual
  | ordinary _ deltaSafe =>
      rw [Subst.seq_apply, Subst.seq_apply]
      exact deltaSafe.exact.1.1

/-- Every ledger-aware ordinary alignment factors its output into the input
followed by one origin-admissible post. -/
theorem DDAlignTypesWithLedger.relativeAdmissible
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst}
    (aligned : DDAlignTypesWithLedger ledger S left right S') :
    ∃ post, S' = Subst.seq post S ∧ AdmissiblePost ledger post := by
  cases aligned with
  | matcherPair _ _ capSafe targetSafe =>
      exact ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _,
        AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible }⟩
  | slotPair _ _ capSafe targetSafe =>
      exact ⟨Subst.seq _ ⟨_, TySubst.id⟩,
        PhasedPost.seq_assoc _ _ _,
        AdmissiblePost.seq targetSafe.admissible
          { cap := capSafe.admissible }⟩
  | ordinary _ deltaSafe =>
      exact ⟨_, rfl, deltaSafe.admissible⟩

/-- Solving a variable against a fresh function shape cannot structure either
fresh component.  In particular, the fresh domain remains a bare target
variable at the output cut. -/
theorem DDAlignTypesWithLedger.var_fn_domain_variable
    {ledger : CapabilityOriginLedger} {shared domain codomain : TypePM.TyVar}
    {S' : Subst}
    (aligned : DDAlignTypesWithLedger ledger Subst.id (.var shared)
      (.fn (.var domain) (.var codomain)) S')
    (sharedNeDomain : shared ≠ domain)
    (sharedNeCodomain : shared ≠ codomain)
    (domainNeShared : domain ≠ shared) :
    ∃ image, S'.apply (.var domain) = .var image := by
  cases aligned with
  | matcherPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      cases leftView
  | slotPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      cases leftView
  | ordinary ordinaryClass deltaSafe =>
      rename_i delta
      have mgu := deltaSafe.exact.1
      simp only [Subst.apply_id] at mgu
      rcases mgu.varConstraint_target_image_var
          (by
            intro membership
            simp only [Ty.ftv, List.mem_append, List.mem_singleton] at membership
            exact membership.elim sharedNeDomain sharedNeCodomain)
          domainNeShared with
        ⟨image, imageView⟩
      refine ⟨image, ?_⟩
      rw [Subst.seq_apply, Subst.apply_id]
      change delta.target domain = .var image
      exact imageView

/-- A non-structural capability variable cannot be equated with `Any` by an
origin-safe ordinary alignment. -/
theorem DDAlignTypesWithLedger.not_of_nonStructuralMatcher_any
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst} {varId : CapVar} {leftTarget rightTarget : Ty}
    (aligned : DDAlignTypesWithLedger ledger S left right S')
    (leftView : S.apply left = .matcher (.var varId) leftTarget)
    (rightView : S.apply right = .matcher .any rightTarget)
    (nonStructural : ledger.originOf varId ≠ .structuralFlexible) : False := by
  cases aligned with
  | matcherPair resolvedLeft resolvedRight capSafe _ =>
      rw [leftView] at resolvedLeft
      cases resolvedLeft
      rw [rightView] at resolvedRight
      cases resolvedRight
      have solved := capSafe.exact.1.1
      simp only [Cap.apply] at solved
      cases origin : ledger.originOf varId with
      | rigid =>
          have fixed := capSafe.admissible.rigid origin
          rw [solved] at fixed
          cases fixed
      | renameOnly =>
          rcases capSafe.admissible.renameOnly_image_variable origin solved with
            ⟨_, imageVariable, _⟩
          cases imageVariable
      | structuralFlexible => exact nonStructural origin
  | slotPair resolvedLeft _ _ _ =>
      rw [leftView] at resolvedLeft
      cases resolvedLeft
  | ordinary pairClass _ =>
      rw [leftView, rightView] at pairClass
      cases pairClass

/-- Symmetric orientation of
`DDAlignTypesWithLedger.not_of_nonStructuralMatcher_any`. -/
theorem DDAlignTypesWithLedger.not_of_any_nonStructuralMatcher
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst} {varId : CapVar} {leftTarget rightTarget : Ty}
    (aligned : DDAlignTypesWithLedger ledger S left right S')
    (leftView : S.apply left = .matcher .any leftTarget)
    (rightView : S.apply right = .matcher (.var varId) rightTarget)
    (nonStructural : ledger.originOf varId ≠ .structuralFlexible) : False := by
  cases aligned with
  | matcherPair resolvedLeft resolvedRight capSafe _ =>
      rw [leftView] at resolvedLeft
      cases resolvedLeft
      rw [rightView] at resolvedRight
      cases resolvedRight
      have solved := capSafe.exact.1.1
      simp only [Cap.apply] at solved
      have solved' := solved.symm
      cases origin : ledger.originOf varId with
      | rigid =>
          have fixed := capSafe.admissible.rigid origin
          rw [solved'] at fixed
          cases fixed
      | renameOnly =>
          rcases capSafe.admissible.renameOnly_image_variable origin solved' with
            ⟨_, imageVariable, _⟩
          cases imageVariable
      | structuralFlexible => exact nonStructural origin
  | slotPair resolvedLeft _ _ _ =>
      rw [leftView] at resolvedLeft
      cases resolvedLeft
  | ordinary pairClass _ =>
      rw [leftView, rightView] at pairClass
      cases pairClass

/-- The complete checking cut inherits the same non-structural matcher/`Any`
separation: every coercive branch requires a slot-headed expectation. -/
theorem DDAlignWithLedger.not_of_nonStructuralMatcher_any
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} {varId : CapVar} {rawTarget expectedTarget : Ty}
    (aligned : DDAlignWithLedger ledger S raw expected S')
    (rawView : S.apply raw = .matcher (.var varId) rawTarget)
    (expectedView : S.apply expected = .matcher .any expectedTarget)
    (nonStructural : ledger.originOf varId ≠ .structuralFlexible) : False := by
  cases aligned with
  | productMatcherLift _ slotView _ =>
      rw [expectedView] at slotView
      cases slotView
  | slotTupleLift _ _ slotView _ _ =>
      rw [expectedView] at slotView
      cases slotView
  | matcherToSlot _ slotView _ =>
      rw [expectedView] at slotView
      cases slotView
  | slotToSlot _ slotView _ _ =>
      rw [expectedView] at slotView
      cases slotView
  | ordinary _ ordinaryAligned =>
      exact ordinaryAligned.not_of_nonStructuralMatcher_any rawView
        expectedView nonStructural

/-- Symmetric orientation of
`DDAlignWithLedger.not_of_nonStructuralMatcher_any`. -/
theorem DDAlignWithLedger.not_of_any_nonStructuralMatcher
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} {varId : CapVar} {rawTarget expectedTarget : Ty}
    (aligned : DDAlignWithLedger ledger S raw expected S')
    (rawView : S.apply raw = .matcher .any rawTarget)
    (expectedView : S.apply expected = .matcher (.var varId) expectedTarget)
    (nonStructural : ledger.originOf varId ≠ .structuralFlexible) : False := by
  cases aligned with
  | productMatcherLift _ slotView _ =>
      rw [expectedView] at slotView
      cases slotView
  | slotTupleLift _ _ slotView _ _ =>
      rw [expectedView] at slotView
      cases slotView
  | matcherToSlot _ slotView _ =>
      rw [expectedView] at slotView
      cases slotView
  | slotToSlot _ slotView _ _ =>
      rw [expectedView] at slotView
      cases slotView
  | ordinary _ ordinaryAligned =>
      exact ordinaryAligned.not_of_any_nonStructuralMatcher rawView
        expectedView nonStructural

/-- Forgetting ledger admissibility recovers ordinary equality alignment. -/
theorem DDAlignTypesWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Ty}
    {S' : Subst}
    (aligned : DDAlignTypesWithLedger ledger S left right S') :
    DDAlignTypes S left right S' := by
  cases aligned with
  | matcherPair leftView rightView capDelta targetDelta =>
      exact .matcherPair leftView rightView capDelta.exact targetDelta.exact
  | slotPair leftView rightView capDelta targetDelta =>
      exact .slotPair leftView rightView capDelta.exact targetDelta.exact
  | ordinary ordinaryClass delta =>
      exact .ordinary ordinaryClass delta.exact

/-- Forgetting ledger admissibility recovers the original checking cut. -/
theorem DDAlignWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} (aligned : DDAlignWithLedger ledger S raw expected S') :
    DDAlign S raw expected S' := by
  cases aligned with
  | productMatcherLift productView slotView delta =>
      exact .productMatcherLift productView slotView delta.exact
  | slotTupleLift demand productView slotView capDelta targetDelta =>
      exact .slotTupleLift demand productView slotView capDelta.exact
        targetDelta.exact
  | matcherToSlot matcherView slotView delta =>
      exact .matcherToSlot matcherView slotView delta.exact
  | slotToSlot sourceView requestedView capDelta targetDelta =>
      exact .slotToSlot sourceView requestedView capDelta.exact
        targetDelta.exact
  | ordinary demand aligned =>
      exact .ordinary demand aligned.erase

/-- Any checking cut whose derivation is not ordinary alignment already has a
slot-headed resolved expected view: the slot-demand principle at the level of
the judgment. -/
theorem DDAlign.slotDemand {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlign S raw expected S') :
    DDAlignTypes S raw expected S' ∨
      ∃ consumerCap consumerTarget,
        S.apply expected = .slot consumerCap consumerTarget := by
  cases aligned with
  | productMatcherLift _ slotView _ => exact Or.inr ⟨_, _, slotView⟩
  | slotTupleLift _ _ slotView _ _ => exact Or.inr ⟨_, _, slotView⟩
  | matcherToSlot _ slotView _ => exact Or.inr ⟨_, _, slotView⟩
  | slotToSlot _ slotView _ _ => exact Or.inr ⟨_, _, slotView⟩
  | ordinary _ aligned => exact Or.inl aligned

/-- Under a matcher-headed resolved expectation every checking-cut derivation
degenerates to ordinary alignment: matcher expectations admit only the
ordinary alignment of the raw synthesized type. -/
theorem DDAlign.matcherExpected {S : Subst} {raw expected : Ty} {S' : Subst}
    {consumerCap : Cap} {consumerTarget : Ty}
    (aligned : DDAlign S raw expected S')
    (matcherView :
      S.apply expected = .matcher consumerCap consumerTarget) :
    DDAlignTypes S raw expected S' := by
  cases aligned with
  | productMatcherLift _ slotView _ =>
      rw [matcherView] at slotView; cases slotView
  | slotTupleLift _ _ slotView _ _ =>
      rw [matcherView] at slotView; cases slotView
  | matcherToSlot _ slotView _ =>
      rw [matcherView] at slotView; cases slotView
  | slotToSlot _ slotView _ _ =>
      rw [matcherView] at slotView; cases slotView
  | ordinary _ aligned => exact aligned

/-! ## Supply-threaded deterministic allocation helpers

The pattern layer reuses the executable traversal's fresh-allocation
discipline through pure supply-indexed twins of the state-threading helpers.
Each function is deterministic in the incoming supply, so the judgment stays
independent of `InferState` while pinning the exact allocation order of the
executable traversal.
-/

/-- Allocate `count` consecutive fresh target metas. -/
def freshTargetsSupply :
    Nat → InferenceBase.FreshSupply → List Ty × InferenceBase.FreshSupply
  | 0, q => ([], q)
  | count + 1, q =>
      (.var q.nextTy ::
        (freshTargetsSupply count { q with nextTy := q.nextTy + 1 }).1,
        (freshTargetsSupply count { q with nextTy := q.nextTy + 1 }).2)

mutual

/-- Supply twin of skeleton freshening: replace observable, structurally
unknown leaves by fresh capability metas and canonicalize unobservable
constructor fields to `Any`. -/
def freshenSkeletonSupply (observable : Shape.Observability) :
    Shape.Evidence → InferenceBase.FreshSupply →
      Option (Cap × InferenceBase.FreshSupply)
  | .unseen, q =>
      some (.var ⟨q.nextCap⟩, { q with nextCap := q.nextCap + 1 })
  | .known leaf, q => some (leaf.toCap, q)
  | .con name children, q =>
      match observable name with
      | none => none
      | some mask =>
          match freshenSkeletonMaskedSupply observable mask children q with
          | none => none
          | some (capabilities, q') => some (.con name capabilities, q')
  | .prod components, q =>
      match freshenSkeletonListSupply observable components q with
      | none => none
      | some (capabilities, q') => some (.prod capabilities, q')

/-- List form of `freshenSkeletonSupply`. -/
def freshenSkeletonListSupply (observable : Shape.Observability) :
    List Shape.Evidence → InferenceBase.FreshSupply →
      Option (List Cap × InferenceBase.FreshSupply)
  | [], q => some ([], q)
  | evidence :: rest, q =>
      match freshenSkeletonSupply observable evidence q with
      | none => none
      | some (head, q) =>
          match freshenSkeletonListSupply observable rest q with
          | none => none
          | some (tail, q') => some (head :: tail, q')

/-- Masked form of `freshenSkeletonSupply`: only observable fields freshen,
the rest canonicalize to `Any`. -/
def freshenSkeletonMaskedSupply (observable : Shape.Observability) :
    List Bool → List Shape.Evidence → InferenceBase.FreshSupply →
      Option (List Cap × InferenceBase.FreshSupply)
  | [], [], q => some ([], q)
  | isObservable :: mask, evidence :: rest, q =>
      match
        if isObservable then freshenSkeletonSupply observable evidence q
        else some (Cap.any, q)
      with
      | none => none
      | some (head, q) =>
          match freshenSkeletonMaskedSupply observable mask rest q with
          | none => none
          | some (tail, q') => some (head :: tail, q')
  | _, _, _ => none

end

/-- Supply twin of the shared pattern-constructor result assignments: one
fresh capability leaf per observable result variable. -/
def patternCtorAssignmentsSupply :
    List TypePM.TyVar → InferenceBase.FreshSupply →
      Projection.Assignments × InferenceBase.FreshSupply
  | [], q => ([], q)
  | varId :: variables, q =>
      ((varId, Shape.ofCap (.var ⟨q.nextCap⟩)) ::
        (patternCtorAssignmentsSupply variables
          { q with nextCap := q.nextCap + 1 }).1,
        (patternCtorAssignmentsSupply variables
          { q with nextCap := q.nextCap + 1 }).2)

/-- Supply twin of the matcher-bodied recursive-binder placeholder: freshen
the skeleton capability inferred from actual clause syntax alone, reuse its
first capability leaf as the argument capability (or allocate one), and
allocate the argument and producer targets. -/
def fixMatcherPlaceholderSupply (signature : FrozenSig)
    (clauses : List Clause) (q : InferenceBase.FreshSupply) :
    Option (Ty × Ty × InferenceBase.FreshSupply) :=
  match Inference.matcherSkeletonEvidence signature.toMatcherSig clauses with
  | none => none
  | some evidence =>
      match
        match evidence with
        | .unseen => some (Cap.any, q)
        | evidence => freshenSkeletonSupply signature.observability evidence q
      with
      | none => none
      | some (capability, q) =>
          match capability.fcv with
          | first :: _ =>
              some (.slot (Cap.var first) (.var q.nextTy),
                .matcher capability (.var (q.nextTy + 1)),
                { q with nextTy := q.nextTy + 2 })
          | [] =>
              some (.slot (Cap.var ⟨q.nextCap⟩) (.var q.nextTy),
                .matcher capability (.var (q.nextTy + 1)),
                { q with
                    nextCap := q.nextCap + 1
                    nextTy := q.nextTy + 2 })

/-- Instantiating a scheme with no binders returns its body unchanged: the
allocated binder substitution has empty support. -/
theorem instantiateScheme_noBinder_value (q : InferenceBase.FreshSupply)
    (body : Ty) :
    (InferenceBase.instantiateScheme q ⟨[], [], body⟩).value = body := by
  refine Subst.apply_eq_self_of_free_fixed _ body ?_ ?_
  · intro varId _
    exact InferenceBase.instantiateBinders_cap_support q [] [] varId
      (by simp)
  · intro varId _
    exact InferenceBase.instantiateBinders_ty_support q [] [] varId
      (by simp)

/-- Instantiating a substituted monomorphic scheme returns the substituted
body: the mask at an empty binder list is the substitution itself, and the
allocated binder substitution has empty support. -/
theorem instantiateScheme_monoApplySubst_value
    (q : InferenceBase.FreshSupply) (S : Subst) (body : Ty) :
    (InferenceBase.instantiateScheme q
      ((Scheme.mono body).applySubst S)).value = S.apply body := by
  show (InferenceBase.instantiateBinders q [] []).subst.apply
      ((Subst.mk (S.cap.mask []) (S.target.mask [])).apply body) =
    S.apply body
  rw [Subst.apply_eq_self_of_free_fixed
      (InferenceBase.instantiateBinders q [] []).subst _
      (fun varId _ =>
        InferenceBase.instantiateBinders_cap_support q [] [] varId (by simp))
      (fun varId _ =>
        InferenceBase.instantiateBinders_ty_support q [] [] varId (by simp))]
  exact Subst.apply_eq_of_free_agree _ S body (fun _ _ => rfl) (fun _ _ => rfl)

/-- The terminal per-clause hole capabilities consumed by matcher
finalization. -/
def terminalHoleCaps (S : Subst) (rawHoleLists : List (List Dual)) :
    List (List Cap) :=
  rawHoleLists.map fun holes => (holes.map (Dual.applySubst S)).map Dual.cap

/-! ## Pattern-layer alignment relations

Each relation mirrors one executable solver sequence in relational form: the
capability sort is solved on cut-resolved views first, and each delta is a
most general solution of exactly the constraint resolved at its cut.
-/

/-- Dual alignment at one cut: capability solve on the resolved views, then
ordinary alignment of the raw targets under the extended substitution. -/
inductive DDAlignDual : Subst → Dual → Dual → Subst → Prop where
  | mk {S : Subst} {left right : Dual} {capDelta : CapSubst} {S' : Subst} :
      ExactCapMGU (left.cap.apply S.cap) (right.cap.apply S.cap)
        capDelta →
      DDAlignTypes (Subst.seq ⟨capDelta, TySubst.id⟩ S)
        left.target right.target S' →
      DDAlignDual S left right S'

/-- Pointwise dual-list alignment. -/
inductive DDAlignDualList : Subst → List Dual → List Dual → Subst → Prop where
  | nil {S : Subst} : DDAlignDualList S [] [] S
  | cons {S : Subst} {left right : Dual} {lefts rights : List Dual}
      {S₁ S' : Subst} :
      DDAlignDual S left right S₁ →
      DDAlignDualList S₁ lefts rights S' →
      DDAlignDualList S (left :: lefts) (right :: rights) S'

/-- Pointwise alignment of pattern-result targets against instantiated
constructor fields. -/
inductive DDAlignTargetList : Subst → List Dual → List Ty → Subst → Prop where
  | nil {S : Subst} : DDAlignTargetList S [] [] S
  | cons {S : Subst} {dual : Dual} {expected : Ty} {duals : List Dual}
      {expecteds : List Ty} {S₁ S' : Subst} :
      DDAlignTypes S dual.target expected S₁ →
      DDAlignTargetList S₁ duals expecteds S' →
      DDAlignTargetList S (dual :: duals) (expected :: expecteds) S'

/-- Entrywise or-alternative binding alignment: binder names must coincide
positionally while the bound types are unified. -/
inductive DDAlignBindings : Subst → MonoCtx → MonoCtx → Subst → Prop where
  | nil {S : Subst} : DDAlignBindings S [] [] S
  | cons {S : Subst} {left right : String × Ty} {lefts rights : MonoCtx}
      {S₁ S' : Subst} :
      left.1 = right.1 →
      DDAlignTypes S left.2 right.2 S₁ →
      DDAlignBindings S₁ lefts rights S' →
      DDAlignBindings S (left :: lefts) (right :: rights) S'

/-- Consumer-side pattern-constructor capability solving against the shared
structural demands; a field with no observable path to a result variable
contributes no constraint. -/
inductive DDAlignCtorCaps :
    Subst → List Cap → List (Option Cap) → Subst → Prop where
  | nil {S : Subst} : DDAlignCtorCaps S [] [] S
  | skip {S : Subst} {child : Cap} {children : List Cap}
      {demands : List (Option Cap)} {S' : Subst} :
      DDAlignCtorCaps S children demands S' →
      DDAlignCtorCaps S (child :: children) (none :: demands) S'
  | solve {S : Subst} {child expected : Cap} {children : List Cap}
      {demands : List (Option Cap)} {capDelta : CapSubst} {S' : Subst} :
      ExactCapMGU (child.apply S.cap) (expected.apply S.cap) capDelta →
      DDAlignCtorCaps (Subst.seq ⟨capDelta, TySubst.id⟩ S) children demands
        S' →
      DDAlignCtorCaps S (child :: children) (some expected :: demands) S'

/-- Pattern-constructor capability inference from actual child consumers:
exact projection on the resolved children is the fast path; otherwise one
shared result skeleton is allocated, the induced field demands are solved,
and exact projection reruns on the re-resolved children. -/
inductive DDPatternCtorCap (signature : FrozenSig)
    (entry : PatternCtorScheme signature.observability) :
    InferenceBase.FreshSupply → Subst → List Cap → Cap →
      InferenceBase.FreshSupply → Subst → Prop where
  | project {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
      {projected : Shape.Evidence} {capability : Cap}
      {q' : InferenceBase.FreshSupply} :
      Projection.projectSignature entry.projection
        ((childCaps.map fun child => child.apply S.cap).map Shape.ofCap) =
          some projected →
      freshenSkeletonSupply signature.observability projected q =
        some (capability, q') →
      DDPatternCtorCap signature entry q S childCaps capability q' S
  | fallback {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
      {resultVariables : List TypePM.TyVar} {demands : List (Option Cap)}
      {S₁ : Subst} {projected : Shape.Evidence} {capability : Cap}
      {q' : InferenceBase.FreshSupply} :
      Projection.projectSignature entry.projection
        ((childCaps.map fun child => child.apply S.cap).map Shape.ofCap) =
          none →
      Projection.relevantVars signature.observability
        (Projection.targetVars entry.projection.resultType)
        entry.projection.resultType = some resultVariables →
      Inference.patternCtorFieldDemands signature.observability
        resultVariables.eraseDups
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).1
        entry.projection.fieldTypes = some demands →
      DDAlignCtorCaps S childCaps demands S₁ →
      Projection.projectSignature entry.projection
        ((childCaps.map fun child => child.apply S₁.cap).map Shape.ofCap) =
          some projected →
      freshenSkeletonSupply signature.observability projected
        (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 =
        some (capability, q') →
      DDPatternCtorCap signature entry q S childCaps capability q' S₁

/-! ### Ledger-aware pattern-layer alignments

These five relations complete the additive ledger-aware alignment surface.
Together with `DDAlignTypesWithLedger` and `DDAlignWithLedger`, every alignment
cut used by the expression and pattern families can state admissibility
without changing the existing DD derivations yet.
-/

/-- Origin-safe dual alignment: capability solve followed by target
alignment. -/
inductive DDAlignDualWithLedger (ledger : CapabilityOriginLedger) :
    Subst → Dual → Dual → Subst → Prop where
  | mk {S : Subst} {left right : Dual} {capDelta : CapSubst} {S' : Subst} :
      OriginSafeExactCapMGU ledger (left.cap.apply S.cap)
        (right.cap.apply S.cap) capDelta →
      DDAlignTypesWithLedger ledger
        (Subst.seq ⟨capDelta, TySubst.id⟩ S) left.target right.target S' →
      DDAlignDualWithLedger ledger S left right S'

/-- Origin-safe pointwise dual-list alignment. -/
inductive DDAlignDualListWithLedger (ledger : CapabilityOriginLedger) :
    Subst → List Dual → List Dual → Subst → Prop where
  | nil {S : Subst} : DDAlignDualListWithLedger ledger S [] [] S
  | cons {S : Subst} {left right : Dual} {lefts rights : List Dual}
      {S₁ S' : Subst} :
      DDAlignDualWithLedger ledger S left right S₁ →
      DDAlignDualListWithLedger ledger S₁ lefts rights S' →
      DDAlignDualListWithLedger ledger S (left :: lefts) (right :: rights) S'

/-- Origin-safe pointwise alignment of pattern-result targets. -/
inductive DDAlignTargetListWithLedger (ledger : CapabilityOriginLedger) :
    Subst → List Dual → List Ty → Subst → Prop where
  | nil {S : Subst} : DDAlignTargetListWithLedger ledger S [] [] S
  | cons {S : Subst} {dual : Dual} {expected : Ty} {duals : List Dual}
      {expecteds : List Ty} {S₁ S' : Subst} :
      DDAlignTypesWithLedger ledger S dual.target expected S₁ →
      DDAlignTargetListWithLedger ledger S₁ duals expecteds S' →
      DDAlignTargetListWithLedger ledger S (dual :: duals)
        (expected :: expecteds) S'

/-- Origin-safe entrywise alignment of or-alternative bindings. -/
inductive DDAlignBindingsWithLedger (ledger : CapabilityOriginLedger) :
    Subst → MonoCtx → MonoCtx → Subst → Prop where
  | nil {S : Subst} : DDAlignBindingsWithLedger ledger S [] [] S
  | cons {S : Subst} {left right : String × Ty} {lefts rights : MonoCtx}
      {S₁ S' : Subst} :
      left.1 = right.1 →
      DDAlignTypesWithLedger ledger S left.2 right.2 S₁ →
      DDAlignBindingsWithLedger ledger S₁ lefts rights S' →
      DDAlignBindingsWithLedger ledger S (left :: lefts) (right :: rights) S'

/-- Origin-safe consumer-side pattern-constructor capability alignment. -/
inductive DDAlignCtorCapsWithLedger (ledger : CapabilityOriginLedger) :
    Subst → List Cap → List (Option Cap) → Subst → Prop where
  | nil {S : Subst} : DDAlignCtorCapsWithLedger ledger S [] [] S
  | skip {S : Subst} {child : Cap} {children : List Cap}
      {demands : List (Option Cap)} {S' : Subst} :
      DDAlignCtorCapsWithLedger ledger S children demands S' →
      DDAlignCtorCapsWithLedger ledger S (child :: children) (none :: demands)
        S'
  | solve {S : Subst} {child expected : Cap} {children : List Cap}
      {demands : List (Option Cap)} {capDelta : CapSubst} {S' : Subst} :
      OriginSafeExactCapMGU ledger (child.apply S.cap)
        (expected.apply S.cap) capDelta →
      DDAlignCtorCapsWithLedger ledger
        (Subst.seq ⟨capDelta, TySubst.id⟩ S) children demands S' →
      DDAlignCtorCapsWithLedger ledger S (child :: children)
        (some expected :: demands) S'

/-- Erase origin evidence from one dual alignment. -/
theorem DDAlignDualWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : Dual}
    {S' : Subst} (aligned : DDAlignDualWithLedger ledger S left right S') :
    DDAlignDual S left right S' := by
  cases aligned with
  | mk capDelta targets => exact .mk capDelta.exact targets.erase

/-- Erase origin evidence from pointwise dual alignment. -/
theorem DDAlignDualListWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : List Dual}
    {S' : Subst}
    (aligned : DDAlignDualListWithLedger ledger S left right S') :
    DDAlignDualList S left right S' := by
  induction aligned with
  | nil => exact .nil
  | cons head tail tailInduction =>
      exact .cons head.erase tailInduction

/-- Erase origin evidence from pattern-result target alignment. -/
theorem DDAlignTargetListWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {duals : List Dual}
    {expecteds : List Ty} {S' : Subst}
    (aligned : DDAlignTargetListWithLedger ledger S duals expecteds S') :
    DDAlignTargetList S duals expecteds S' := by
  induction aligned with
  | nil => exact .nil
  | cons head tail tailInduction =>
      exact .cons head.erase tailInduction

/-- Erase origin evidence from or-alternative binding alignment. -/
theorem DDAlignBindingsWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {left right : MonoCtx}
    {S' : Subst}
    (aligned : DDAlignBindingsWithLedger ledger S left right S') :
    DDAlignBindings S left right S' := by
  induction aligned with
  | nil => exact .nil
  | cons names head tail tailInduction =>
      exact .cons names head.erase tailInduction

/-- Erase origin evidence from pattern-constructor capability alignment. -/
theorem DDAlignCtorCapsWithLedger.erase
    {ledger : CapabilityOriginLedger} {S : Subst} {children : List Cap}
    {demands : List (Option Cap)} {S' : Subst}
    (aligned : DDAlignCtorCapsWithLedger ledger S children demands S') :
    DDAlignCtorCaps S children demands S' := by
  induction aligned with
  | nil => exact .nil
  | skip tail tailInduction => exact .skip tailInduction
  | solve delta tail tailInduction => exact .solve delta.exact tailInduction

/-! ## Primitive-pattern and data-pattern layers

Both families are expression-free, so they close outside the main mutual
block.  Targets flow inward: each pattern is checked against one expected
target, allocating fresh component targets only at tuple nodes and fresh
hole capabilities only at primitive holes.
-/

mutual

/-- Demand-directed primitive data-pattern checking
`q; S ⊢ dp ⇐ τ ⇒ Δ ⊣ q'; S'`. -/
inductive DDDPat (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → DPat → Ty → MonoCtx →
      InferenceBase.FreshSupply → Subst → Prop where
  | var {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {expectedTarget : Ty} :
      DDDPat signature q S (.var name) expectedTarget
        [(name, expectedTarget)] q S
  | wild {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty} :
      DDDPat signature q S .wild expectedTarget [] q S
  | ctor {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {patterns : List DPat} {expectedTarget : Ty} {scheme : CtorScheme}
      {S₁ : Subst} {bindings : MonoCtx} {q' : InferenceBase.FreshSupply}
      {S' : Subst} :
      signature.findDataCtor name = some scheme →
      DDAlignTypes S (InferenceBase.instantiateCtorScheme q scheme).value.2
        expectedTarget S₁ →
      DDDPats signature (InferenceBase.instantiateCtorScheme q scheme).supply
        S₁ patterns (InferenceBase.instantiateCtorScheme q scheme).value.1
        bindings q' S' →
      DDDPat signature q S (.ctor name patterns) expectedTarget bindings q' S'
  | tuple {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List DPat}
      {expectedTarget : Ty} {S₁ : Subst} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDAlignTypes S (.prod (freshTargetsSupply patterns.length q).1)
        expectedTarget S₁ →
      DDDPats signature (freshTargetsSupply patterns.length q).2 S₁ patterns
        (freshTargetsSupply patterns.length q).1 bindings q' S' →
      DDDPat signature q S (.tuple patterns) expectedTarget bindings q' S'

/-- Equal-length data-pattern/target list checking with disjoint binders. -/
inductive DDDPats (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → List DPat → List Ty → MonoCtx →
      InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} :
      DDDPats signature q S [] [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
      {patterns : List DPat} {target : Ty} {targets : List Ty}
      {bindings restBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ : Subst} {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDDPat signature q S pattern target bindings q₁ S₁ →
      DDDPats signature q₁ S₁ patterns targets restBindings q' S' →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      DDDPats signature q S (pattern :: patterns) (target :: targets)
        (bindings ++ restBindings) q' S'

end

mutual

/-- Demand-directed primitive-pattern checking against one shared matcher
target `q; S ⊢ pp ⇐ τ ⇒ holes; Δ ⊣ q'; S'`. -/
inductive DDPPat (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → PPat → Ty → List Dual → MonoCtx →
      InferenceBase.FreshSupply → Subst → Prop where
  | hole {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty} :
      DDPPat signature q S .hole expectedTarget
        [⟨.var ⟨q.nextCap⟩, expectedTarget⟩] []
        { q with nextCap := q.nextCap + 1 } S
  | wild {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty} :
      DDPPat signature q S .wild expectedTarget [] [] q S
  | pval {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {expectedTarget : Ty} :
      DDPPat signature q S (.pval name) expectedTarget []
        [(name, expectedTarget)] q S
  | ctor {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {patterns : List PPat} {expectedTarget : Ty}
      {entry : PatternCtorScheme signature.observability} {S₁ : Subst}
      {holes : List Dual} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      signature.findPatternCtor name = some entry →
      DDAlignTypes S
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2
        expectedTarget S₁ →
      DDPPats signature
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
        patterns (InferenceBase.instantiateCtorScheme q entry.scheme).value.1
        holes bindings q' S' →
      DDPPat signature q S (.ctor name patterns) expectedTarget holes bindings
        q' S'
  | tuple {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List PPat}
      {expectedTarget : Ty} {S₁ : Subst} {holes : List Dual}
      {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDAlignTypes S (.prod (freshTargetsSupply patterns.length q).1)
        expectedTarget S₁ →
      DDPPats signature (freshTargetsSupply patterns.length q).2 S₁ patterns
        (freshTargetsSupply patterns.length q).1 holes bindings q' S' →
      DDPPat signature q S (.tuple patterns) expectedTarget holes bindings
        q' S'

/-- Equal-length primitive-pattern/target list checking with disjoint
binders. -/
inductive DDPPats (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → List PPat → List Ty → List Dual →
      MonoCtx → InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} :
      DDPPats signature q S [] [] [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
      {patterns : List PPat} {target : Ty} {targets : List Ty}
      {holes restHoles : List Dual} {bindings restBindings : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDPPat signature q S pattern target holes bindings q₁ S₁ →
      DDPPats signature q₁ S₁ patterns targets restHoles restBindings q' S' →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      DDPPats signature q S (pattern :: patterns) (target :: targets)
        (holes ++ restHoles) (bindings ++ restBindings) q' S'

end

/-! ## The demand-directed judgments -/

/-- The synthesis-order recursive-binder placeholder selector: the
non-matcher `fix` template applies exactly when the body is not a matcher
literal; matcher-bodied binders take the skeleton placeholder of
`fixMatcherPlaceholderSupply` instead. -/
abbrev NonMatcherBody (body : Expr) : Prop :=
  matcherProducingRoot body = false

mutual

/-- Demand-directed synthesis `q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'`.

Rules mirror the left-to-right synthesis traversal: context lookup applies
the prevailing substitution first, λ and application domains are fresh
metavariables, `let` generalizes the value type in the substituted context,
and constructor/primitive arguments are checked against the supply-indexed
instantiation of the declared scheme.  `matchAll` synthesizes its target,
infers the pattern, aligns the pattern target, and demands a slot from the
matcher expression; `matcher` literals allocate one shared target, traverse
every clause, and finalize through the same executable coverage checks
consumed by the declarative rule. -/
inductive DDSynth (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → Expr → Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | var {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {scheme : Scheme} :
      (Γ.applySubst S).find? name = some scheme →
      DDSynth signature q S Γ (.var name)
        (InferenceBase.instantiateScheme q scheme).value
        (InferenceBase.instantiateScheme q scheme).supply S
  | lam {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {body : Expr} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature { q with nextTy := q.nextTy + 1 } S
        ((name, Scheme.mono (.var q.nextTy)) :: Γ) body bodyTarget q' S' →
      DDSynth signature q S Γ (.lam name body)
        (.fn (.var q.nextTy) bodyTarget) q' S'
  | fix {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {self argument : String} {body : Expr} {bodyTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      self ≠ argument →
      DirectSelf.Holds self body →
      NonMatcherBody body →
      DDSynth signature { q with nextTy := q.nextTy + 2 } S
        ((argument, Scheme.mono (.var q.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: Γ)
        body bodyTarget q₁ S₁ →
      DDAlignTypes S₁ bodyTarget (.var (q.nextTy + 1)) S' →
      DDSynth signature q S Γ (.fix self argument body)
        (.fn (.var q.nextTy) (.var (q.nextTy + 1))) q₁ S'
  | app {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {function argument : Expr} {functionTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₃ : Subst} :
      DDSynth signature q S Γ function functionTarget q₁ S₁ →
      DDAlignTypes S₁ functionTarget
        (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂ →
      DDCheck signature { q₁ with nextTy := q₁.nextTy + 2 } S₂ Γ argument
        (.var q₁.nextTy) q₂ S₃ →
      DDSynth signature q S Γ (.app function argument)
        (.var (q₁.nextTy + 1)) q₂ S₃
  | lit {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {value : Int} :
      DDSynth signature q S Γ (.lit value) .int q S
  | tuple {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expressions : List Expr} {targets : List Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynths signature q S Γ expressions targets q' S' →
      DDSynth signature q S Γ (.tuple expressions) (.prod targets) q' S'
  | ctor {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      signature.findDataCtor name = some scheme →
      DDChecks signature (InferenceBase.instantiateCtorScheme q scheme).supply
        S Γ expressions
        (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S' →
      DDSynth signature q S Γ (.ctor name expressions)
        (InferenceBase.instantiateCtorScheme q scheme).value.2 q' S'
  | prim {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {op : PrimOp} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      signature.findPrimitive op = some scheme →
      DDChecks signature (InferenceBase.instantiateCtorScheme q scheme).supply
        S Γ expressions
        (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S' →
      DDSynth signature q S Γ (.prim op expressions)
        (InferenceBase.instantiateCtorScheme q scheme).value.2 q' S'
  | letE {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {value body : Expr} {valueTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature q S Γ value valueTarget q₁ S₁ →
      DDSynth signature q₁ S₁
        ((name, signature.generalize (Γ.applySubst S₁)
          (S₁.apply valueTarget)) :: Γ) body bodyTarget q' S' →
      DDSynth signature q S Γ (.letE name value body) bodyTarget q' S'
  | something {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDSynth signature q S Γ .something (.matcher .any (.var q.nextTy))
        { q with nextTy := q.nextTy + 1 } S
  | matcher {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {clauses : List Clause} {rawHoleLists : List (List Dual)}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {evidence : List Shape.Evidence} {capability : Cap} :
      DDClauses signature { q with nextTy := q.nextTy + 1 } S Γ clauses
        (.var q.nextTy) rawHoleLists q' S' →
      Inference.collectClauseEvidence signature.toMatcherSig clauses
        (terminalHoleCaps S' rawHoleLists) = some evidence →
      Shape.inferShape signature.observability evidence = some capability →
      Inference.clauseCapsListCheck signature capability clauses
        (terminalHoleCaps S' rawHoleLists) = true →
      Inference.catchAllLastCheck clauses = true →
      Inference.matcherBindersCheck clauses = true →
      Inference.armExhaustiveCheck signature clauses
        (S'.apply (.var q.nextTy)) = true →
      Inference.coverageCheck signature.toMatcherSig clauses capability =
        true →
      DDSynth signature q S Γ (.matcher clauses)
        (.matcher capability (.var q.nextTy)) q' S'
  | matchAll {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {target matcher : Expr} {pattern : Pattern} {body : Expr}
      {targetTarget : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {dual : Dual} {Δ : MonoCtx} {q₂ : InferenceBase.FreshSupply}
      {S₂ S₃ : Subst} {q₃ : InferenceBase.FreshSupply} {S₄ : Subst}
      {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature q S Γ target targetTarget q₁ S₁ →
      DDPattern signature q₁ S₁ Γ [] [] pattern dual Δ q₂ S₂ →
      DDAlignTypes S₂ dual.target targetTarget S₃ →
      DDCheck signature q₂ S₃ Γ matcher (.slot dual.cap targetTarget) q₃ S₄ →
      DDSynth signature q₃ S₄ (Δ.toContext ++ Γ) body bodyTarget q' S' →
      DDSynth signature q S Γ (.matchAll target matcher pattern body)
        (Ty.listT bodyTarget) q' S'
  | fixMatcher {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {self argument : String} {clauses : List Clause} {domain codomain : Ty}
      {q₀ : InferenceBase.FreshSupply} {bodyTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      self ≠ argument →
      DirectSelf.Holds self (.matcher clauses) →
      fixMatcherPlaceholderSupply signature clauses q =
        some (domain, codomain, q₀) →
      DDSynth signature q₀ S
        ((argument, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: Γ)
        (.matcher clauses) bodyTarget q₁ S₁ →
      DDAlignTypes S₁ bodyTarget codomain S' →
      DDSynth signature q S Γ (.fix self argument (.matcher clauses))
        (.fn domain codomain) q₁ S'

/-- Left-to-right synthesis of an expression list. -/
inductive DDSynths (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → List Expr → List Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDSynths signature q S Γ [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expressions : List Expr} {target : Ty}
      {targets : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature q S Γ expression target q₁ S₁ →
      DDSynths signature q₁ S₁ Γ expressions targets q' S' →
      DDSynths signature q S Γ (expression :: expressions)
        (target :: targets) q' S'

/-- Demand-directed checking `q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'`: synthesize
first, then align at the exact output cut. -/
inductive DDCheck (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → Expr → Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | mk {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expected raw : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      DDSynth signature q S Γ expression raw q₁ S₁ →
      DDAlign S₁ raw expected S' →
      DDCheck signature q S Γ expression expected q₁ S'

/-- Pointwise checking of equal-length expression/type lists. -/
inductive DDChecks (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → List Expr → List Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDChecks signature q S Γ [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expressions : List Expr} {expected : Ty}
      {expecteds : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDCheck signature q S Γ expression expected q₁ S₁ →
      DDChecks signature q₁ S₁ Γ expressions expecteds q' S' →
      DDChecks signature q S Γ (expression :: expressions)
        (expected :: expecteds) q' S'

/-- Demand-directed user-pattern synthesis
`q; S; Γ; Φ; Δ ⊢ p ⇒ dual ⊣ Δ'; q'; S'`, threading the monomorphic binding
context left to right. -/
inductive DDPattern (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → PatternCtx → MonoCtx →
      Pattern → Dual → MonoCtx → InferenceBase.FreshSupply → Subst →
      Prop where
  | pvar {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {name : String} :
      name ∉ Δ.names →
      DDPattern signature q S Γ Φ Δ (.pvar name)
        ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ (Δ ++ [(name, .var q.nextTy)])
        { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
  | wild {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} :
      DDPattern signature q S Γ Φ Δ .wild
        ⟨.var ⟨q.nextCap⟩, .var q.nextTy⟩ Δ
        { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } S
  | pval {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {expression : Expr} {target : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} :
      DDSynth signature q S (Δ.toContext ++ Γ) expression target q₁ S₁ →
      DDPattern signature q S Γ Φ Δ (.pval expression)
        ⟨.var ⟨q₁.nextCap⟩, target⟩ Δ
        { q₁ with nextCap := q₁.nextCap + 1 } S₁
  | embed {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {name : String} {dual : Dual} :
      Φ.find? name = some dual →
      DDPattern signature q S Γ Φ Δ (.embed name) dual Δ q S
  | ptuple {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {patterns : List Pattern}
      {duals : List Dual} {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply}
      {S' : Subst} :
      DDPatterns signature q S Γ Φ Δ patterns duals Δ' q' S' →
      DDPattern signature q S Γ Φ Δ (.ptuple patterns)
        ⟨.prod (duals.map Dual.cap), .prod (duals.map Dual.target)⟩ Δ' q' S'
  | pctor {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {name : String}
      {patterns : List Pattern}
      {entry : PatternCtorScheme signature.observability}
      {duals : List Dual} {Δ' : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ S₂ : Subst} {capability : Cap} {q₂ : InferenceBase.FreshSupply}
      {S₃ : Subst} :
      signature.findPatternCtor name = some entry →
      DDPatterns signature
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply S Γ Φ Δ
        patterns duals Δ' q₁ S₁ →
      DDAlignTargetList S₁ duals
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂ →
      DDPatternCtorCap signature entry q₁ S₂ (duals.map Dual.cap) capability
        q₂ S₃ →
      Inference.capCompatibleCheck entry
        ((duals.map Dual.cap).map fun child => child.apply S₃.cap)
        (capability.apply S₃.cap) = true →
      DDPattern signature q S Γ Φ Δ (.pctor name patterns)
        ⟨capability,
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.2⟩
        Δ' q₂ S₃
  | pand {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {left right : Pattern}
      {leftDual : Dual} {Δₗ : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ : Subst} {rightDual : Dual} {Δ' : MonoCtx}
      {q₂ : InferenceBase.FreshSupply} {S₂ S' : Subst} :
      DDPattern signature q S Γ Φ Δ left leftDual Δₗ q₁ S₁ →
      DDPattern signature q₁ S₁ Γ Φ Δₗ right rightDual Δ' q₂ S₂ →
      DDAlignDual S₂ leftDual rightDual S' →
      DDPattern signature q S Γ Φ Δ (.pand left right) leftDual Δ' q₂ S'
  | por {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {left right : Pattern}
      {leftDual : Dual} {Δₗ : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ : Subst} {rightDual : Dual} {Δᵣ : MonoCtx}
      {q₂ : InferenceBase.FreshSupply} {S₂ S₃ S' : Subst} :
      DDPattern signature q S Γ Φ Δ left leftDual Δₗ q₁ S₁ →
      DDPattern signature q₁ S₁ Γ Φ Δ right rightDual Δᵣ q₂ S₂ →
      DDAlignDual S₂ leftDual rightDual S₃ →
      DDAlignBindings S₃ Δₗ Δᵣ S' →
      DDPattern signature q S Γ Φ Δ (.por left right) leftDual Δₗ q₂ S'
  | papp {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {name : String}
      {patterns : List Pattern} {scheme : DualScheme} {duals : List Dual}
      {Δ' : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      signature.findPatternFun name = some scheme →
      DDPatterns signature
        (InferenceBase.instantiateDualScheme q scheme).supply S Γ Φ Δ
        patterns duals Δ' q₁ S₁ →
      DDAlignDualList S₁ duals
        (InferenceBase.instantiateDualScheme q scheme).value.1 S' →
      DDPattern signature q S Γ Φ Δ (.papp name patterns)
        (InferenceBase.instantiateDualScheme q scheme).value.2 Δ' q₁ S'

/-- Left-to-right user-pattern list synthesis threading the binding
context. -/
inductive DDPatterns (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → PatternCtx → MonoCtx →
      List Pattern → List Dual → MonoCtx → InferenceBase.FreshSupply →
      Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} :
      DDPatterns signature q S Γ Φ Δ [] [] Δ q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {pattern : Pattern}
      {patterns : List Pattern} {dual : Dual} {duals : List Dual}
      {Δ₁ : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDPattern signature q S Γ Φ Δ pattern dual Δ₁ q₁ S₁ →
      DDPatterns signature q₁ S₁ Γ Φ Δ₁ patterns duals Δ' q' S' →
      DDPatterns signature q S Γ Φ Δ (pattern :: patterns) (dual :: duals)
        Δ' q' S'

/-- Check every arm of one clause against its decomposition-result type. -/
inductive DDArms (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → MonoCtx → List Arm → Ty →
      Ty → InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {ppBindings : MonoCtx} {clauseTarget bodyTarget : Ty} :
      DDArms signature q S Γ ppBindings [] clauseTarget bodyTarget q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {ppBindings : MonoCtx} {dataPattern : DPat} {body : Expr}
      {arms : List Arm} {clauseTarget bodyTarget : Ty}
      {armBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDDPat signature q S dataPattern clauseTarget armBindings q₁ S₁ →
      (∀ name, name ∈ armBindings.names → name ∉ ppBindings.names) →
      DDCheck signature q₁ S₁
        (armBindings.toContext ++ ppBindings.toContext ++ Γ) body bodyTarget
        q₂ S₂ →
      DDArms signature q₂ S₂ Γ ppBindings arms clauseTarget bodyTarget
        q' S' →
      DDArms signature q S Γ ppBindings (.mk dataPattern body :: arms)
        clauseTarget bodyTarget q' S'

/-- Infer one matcher clause under the shared target: primitive pattern,
next-matcher slots, then every arm. -/
inductive DDClause (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → Clause → Ty → List Dual →
      InferenceBase.FreshSupply → Subst → Prop where
  | mk {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {pp : PPat}
      {next : Expr} {arms : List Arm} {sharedTarget : Ty}
      {holes : List Dual} {ppBindings : MonoCtx} {nextMatchers : List Expr}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDPPat signature q S pp sharedTarget holes ppBindings q₁ S₁ →
      decomposeME next holes.length = some nextMatchers →
      DDChecks signature q₁ S₁ Γ nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) q₂ S₂ →
      DDArms signature q₂ S₂ Γ ppBindings arms sharedTarget
        (Ty.listT (prodTy (holes.map Dual.target))) q' S' →
      DDClause signature q S Γ (.mk pp next arms) sharedTarget holes q' S'

/-- Left-to-right clause-list inference under one shared target. -/
inductive DDClauses (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → List Clause → Ty →
      List (List Dual) → InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {sharedTarget : Ty} :
      DDClauses signature q S Γ [] sharedTarget [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {clause : Clause} {clauses : List Clause} {sharedTarget : Ty}
      {holes : List Dual} {holeLists : List (List Dual)}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDClause signature q S Γ clause sharedTarget holes q₁ S₁ →
      DDClauses signature q₁ S₁ Γ clauses sharedTarget holeLists q' S' →
      DDClauses signature q S Γ (clause :: clauses) sharedTarget
        (holes :: holeLists) q' S'

end

/-! ## Prevailing replay

Every judgment output substitution is the input substitution extended by a
chronological chain of solve deltas, mirroring the replay factorization of
the executable trace. -/

/-- Chronological delta replay onto an existing prevailing substitution. -/
def replayDeltas : Subst → List Subst → Subst
  | S, [] => S
  | S, delta :: deltas => replayDeltas (Subst.seq delta S) deltas

@[simp] theorem replayDeltas_nil (S : Subst) : replayDeltas S [] = S := rfl

theorem replayDeltas_append (S : Subst) (first rest : List Subst) :
    replayDeltas S (first ++ rest) =
      replayDeltas (replayDeltas S first) rest := by
  induction first generalizing S with
  | nil => rfl
  | cons delta deltas ih =>
      simpa [replayDeltas] using ih (Subst.seq delta S)

/-- The later substitution replays the earlier one through a chronological
delta chain. -/
def ReplayExtends (earlier later : Subst) : Prop :=
  ∃ deltas, later = replayDeltas earlier deltas

theorem ReplayExtends.refl (S : Subst) : ReplayExtends S S :=
  ⟨[], rfl⟩

theorem ReplayExtends.solve {S : Subst} (delta : Subst) :
    ReplayExtends S (Subst.seq delta S) :=
  ⟨[delta], rfl⟩

theorem ReplayExtends.trans {S₁ S₂ S₃ : Subst}
    (first : ReplayExtends S₁ S₂) (second : ReplayExtends S₂ S₃) :
    ReplayExtends S₁ S₃ := by
  obtain ⟨firstDeltas, firstEq⟩ := first
  obtain ⟨secondDeltas, secondEq⟩ := second
  exact ⟨firstDeltas ++ secondDeltas, by
    rw [replayDeltas_append, ← firstEq, secondEq]⟩

/-- Equality established by an earlier prevailing substitution remains true
after replaying any later solve deltas. -/
private theorem replayDeltas_apply_eq
    {S : Subst} {left right : Ty}
    (equal : S.apply left = S.apply right) (deltas : List Subst) :
    (replayDeltas S deltas).apply left =
      (replayDeltas S deltas).apply right := by
  induction deltas generalizing S with
  | nil => exact equal
  | cons delta deltas ih =>
      apply ih
      rw [Subst.seq_apply, Subst.seq_apply, equal]

/-- Equality established at an earlier prevailing cut is preserved by every
later substitution related by replay. -/
theorem ReplayExtends.apply_eq
    {earlier later : Subst} {left right : Ty}
    (extension : ReplayExtends earlier later)
    (equal : earlier.apply left = earlier.apply right) :
    later.apply left = later.apply right := by
  obtain ⟨deltas, rfl⟩ := extension
  exact replayDeltas_apply_eq equal deltas

/-- Ordinary alignment extends the prevailing substitution by replay. -/
theorem DDAlignTypes.replayExtends {S : Subst} {left right : Ty} {S' : Subst}
    (aligned : DDAlignTypes S left right S') : ReplayExtends S S' := by
  cases aligned with
  | matcherPair _ _ _ _ =>
      exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | slotPair _ _ _ _ =>
      exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | ordinary _ _ =>
      exact ⟨[_], rfl⟩

/-- Every checking cut extends the prevailing substitution by replay. -/
theorem DDAlign.replayExtends {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlign S raw expected S') : ReplayExtends S S' := by
  cases aligned with
  | productMatcherLift _ _ _ => exact ⟨[_], rfl⟩
  | slotTupleLift _ _ _ _ _ => exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | matcherToSlot _ _ _ => exact ⟨[_], rfl⟩
  | slotToSlot _ _ _ _ => exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | ordinary _ aligned => exact aligned.replayExtends

/-- Dual alignment extends the prevailing substitution by replay. -/
theorem DDAlignDual.replayExtends {S : Subst} {left right : Dual}
    {S' : Subst} (aligned : DDAlignDual S left right S') :
    ReplayExtends S S' := by
  cases aligned with
  | mk _ typesAligned =>
      exact (ReplayExtends.solve _).trans typesAligned.replayExtends

/-- Dual-list alignment extends the prevailing substitution by replay. -/
theorem DDAlignDualList.replayExtends {S : Subst} {lefts rights : List Dual}
    {S' : Subst} :
    DDAlignDualList S lefts rights S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail => (head.replayExtends).trans tail.replayExtends

/-- Target-list alignment extends the prevailing substitution by replay. -/
theorem DDAlignTargetList.replayExtends {S : Subst} {duals : List Dual}
    {expecteds : List Ty} {S' : Subst} :
    DDAlignTargetList S duals expecteds S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail => (head.replayExtends).trans tail.replayExtends

/-- Binding alignment extends the prevailing substitution by replay. -/
theorem DDAlignBindings.replayExtends {S : Subst} {lefts rights : MonoCtx}
    {S' : Subst} :
    DDAlignBindings S lefts rights S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons _ head tail => (head.replayExtends).trans tail.replayExtends

/-- Constructor-capability demand solving extends the substitution by
replay. -/
theorem DDAlignCtorCaps.replayExtends {S : Subst} {children : List Cap}
    {demands : List (Option Cap)} {S' : Subst} :
    DDAlignCtorCaps S children demands S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .skip rest => rest.replayExtends
  | .solve _ rest => (ReplayExtends.solve _).trans rest.replayExtends

/-- Pattern-constructor capability inference extends the substitution by
replay. -/
theorem DDPatternCtorCap.replayExtends {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPatternCtorCap signature entry q S childCaps capability q' S' →
      ReplayExtends S S'
  | .project _ _ => ReplayExtends.refl _
  | .fallback _ _ _ aligned _ _ => aligned.replayExtends

mutual

/-- Primitive-pattern checking extends the substitution by replay. -/
theorem DDPPat.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
    {expectedTarget : Ty} {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPPat signature q S pattern expectedTarget holes bindings q' S' →
      ReplayExtends S S'
  | .hole => ReplayExtends.refl _
  | .wild => ReplayExtends.refl _
  | .pval => ReplayExtends.refl _
  | .ctor _ aligned children =>
      (aligned.replayExtends).trans children.replayExtends
  | .tuple aligned children =>
      (aligned.replayExtends).trans children.replayExtends

/-- Primitive-pattern list checking extends the substitution by replay. -/
theorem DDPPats.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List PPat}
    {targets : List Ty} {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPPats signature q S patterns targets holes bindings q' S' →
      ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail _ => (head.replayExtends).trans tail.replayExtends

end

mutual

/-- Data-pattern checking extends the substitution by replay. -/
theorem DDDPat.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
    {expectedTarget : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDDPat signature q S pattern expectedTarget bindings q' S' →
      ReplayExtends S S'
  | .var => ReplayExtends.refl _
  | .wild => ReplayExtends.refl _
  | .ctor _ aligned children =>
      (aligned.replayExtends).trans children.replayExtends
  | .tuple aligned children =>
      (aligned.replayExtends).trans children.replayExtends

/-- Data-pattern list checking extends the substitution by replay. -/
theorem DDDPats.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List DPat}
    {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDDPats signature q S patterns targets bindings q' S' →
      ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail _ => (head.replayExtends).trans tail.replayExtends

end

mutual

/-- Synthesis extends the prevailing substitution by chronological replay. -/
theorem DDSynth.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {τ : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDSynth signature q S Γ e τ q' S' → ReplayExtends S S'
  | .var _ => ReplayExtends.refl _
  | .lam body => body.replayExtends
  | .fix _ _ _ body aligned =>
      (body.replayExtends).trans aligned.replayExtends
  | .app function aligned argument =>
      ((function.replayExtends).trans aligned.replayExtends).trans
        argument.replayExtends
  | .lit => ReplayExtends.refl _
  | .tuple expressions => expressions.replayExtends
  | .ctor _ arguments => arguments.replayExtends
  | .prim _ arguments => arguments.replayExtends
  | .letE value body =>
      (value.replayExtends).trans body.replayExtends
  | .something => ReplayExtends.refl _
  | .matcher clauses _ _ _ _ _ _ _ => clauses.replayExtends
  | .matchAll target pattern aligned matcher body =>
      ((((target.replayExtends).trans pattern.replayExtends).trans
        aligned.replayExtends).trans matcher.replayExtends).trans
        body.replayExtends
  | .fixMatcher _ _ _ body aligned =>
      (body.replayExtends).trans aligned.replayExtends

/-- List synthesis extends the prevailing substitution by replay. -/
theorem DDSynths.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {τs : List Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDSynths signature q S Γ es τs q' S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail =>
      (head.replayExtends).trans tail.replayExtends

/-- Checking extends the prevailing substitution by replay. -/
theorem DDCheck.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {expected : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDCheck signature q S Γ e expected q' S' → ReplayExtends S S'
  | .mk synthesized aligned =>
      (synthesized.replayExtends).trans aligned.replayExtends

/-- List checking extends the prevailing substitution by replay. -/
theorem DDChecks.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDChecks signature q S Γ es expecteds q' S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail =>
      (head.replayExtends).trans tail.replayExtends

/-- Pattern synthesis extends the prevailing substitution by replay. -/
theorem DDPattern.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {Φ : PatternCtx} {Δ : MonoCtx} {pattern : Pattern} {dual : Dual}
    {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPattern signature q S Γ Φ Δ pattern dual Δ' q' S' →
      ReplayExtends S S'
  | .pvar _ => ReplayExtends.refl _
  | .wild => ReplayExtends.refl _
  | .pval value => value.replayExtends
  | .embed _ => ReplayExtends.refl _
  | .ptuple patterns => patterns.replayExtends
  | .pctor _ patterns aligned ctorCap _ =>
      ((patterns.replayExtends).trans aligned.replayExtends).trans
        ctorCap.replayExtends
  | .pand left right aligned =>
      ((left.replayExtends).trans right.replayExtends).trans
        aligned.replayExtends
  | .por left right aligned alignedBindings =>
      (((left.replayExtends).trans right.replayExtends).trans
        aligned.replayExtends).trans alignedBindings.replayExtends
  | .papp _ patterns aligned =>
      (patterns.replayExtends).trans aligned.replayExtends

/-- Pattern-list synthesis extends the prevailing substitution by replay. -/
theorem DDPatterns.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {Φ : PatternCtx} {Δ : MonoCtx} {patterns : List Pattern}
    {duals : List Dual} {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDPatterns signature q S Γ Φ Δ patterns duals Δ' q' S' →
      ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail => (head.replayExtends).trans tail.replayExtends

/-- Arm checking extends the prevailing substitution by replay. -/
theorem DDArms.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {ppBindings : MonoCtx} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDArms signature q S Γ ppBindings arms clauseTarget bodyTarget q' S' →
      ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons dataPattern _ body rest =>
      ((dataPattern.replayExtends).trans body.replayExtends).trans
        rest.replayExtends

/-- Clause inference extends the prevailing substitution by replay. -/
theorem DDClause.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {clause : Clause} {sharedTarget : Ty} {holes : List Dual}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDClause signature q S Γ clause sharedTarget holes q' S' →
      ReplayExtends S S'
  | .mk pp _ nextMatchers arms =>
      ((pp.replayExtends).trans nextMatchers.replayExtends).trans
        arms.replayExtends

/-- Clause-list inference extends the prevailing substitution by replay. -/
theorem DDClauses.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDClauses signature q S Γ clauses sharedTarget holeLists q' S' →
      ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail => (head.replayExtends).trans tail.replayExtends

end

/-! ## Supply monotonicity -/

/-- Componentwise order on fresh supplies. -/
def SupplyExtends (earlier later : InferenceBase.FreshSupply) : Prop :=
  earlier.nextCap ≤ later.nextCap ∧ earlier.nextTy ≤ later.nextTy

theorem SupplyExtends.refl (q : InferenceBase.FreshSupply) :
    SupplyExtends q q :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem SupplyExtends.trans {q₁ q₂ q₃ : InferenceBase.FreshSupply}
    (first : SupplyExtends q₁ q₂) (second : SupplyExtends q₂ q₃) :
    SupplyExtends q₁ q₃ :=
  ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩

theorem SupplyExtends.bumpTy (q : InferenceBase.FreshSupply) (count : Nat) :
    SupplyExtends q { q with nextTy := q.nextTy + count } :=
  ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

/-- Scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateScheme
    (q : InferenceBase.FreshSupply) (scheme : Scheme) :
    SupplyExtends q (InferenceBase.instantiateScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Constructor-scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateCtorScheme
    (q : InferenceBase.FreshSupply) (scheme : CtorScheme) :
    SupplyExtends q (InferenceBase.instantiateCtorScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Dual-scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateDualScheme
    (q : InferenceBase.FreshSupply) (scheme : DualScheme) :
    SupplyExtends q (InferenceBase.instantiateDualScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem SupplyExtends.bumpCap (q : InferenceBase.FreshSupply) (count : Nat) :
    SupplyExtends q { q with nextCap := q.nextCap + count } :=
  ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem SupplyExtends.bumpBoth (q : InferenceBase.FreshSupply)
    (capCount tyCount : Nat) :
    SupplyExtends q
      { q with nextCap := q.nextCap + capCount
               nextTy := q.nextTy + tyCount } :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Consecutive fresh-target allocation only advances the target counter. -/
theorem SupplyExtends.freshTargets (count : Nat)
    (q : InferenceBase.FreshSupply) :
    SupplyExtends q (freshTargetsSupply count q).2 := by
  induction count generalizing q with
  | zero => exact SupplyExtends.refl _
  | succ count ih => exact (SupplyExtends.bumpTy q 1).trans (ih _)

/-- Shared result-assignment allocation only advances the capability
counter. -/
theorem SupplyExtends.patternCtorAssignments
    (variables : List TypePM.TyVar) (q : InferenceBase.FreshSupply) :
    SupplyExtends q (patternCtorAssignmentsSupply variables q).2 := by
  induction variables generalizing q with
  | nil => exact SupplyExtends.refl _
  | cons varId variables ih =>
      exact (SupplyExtends.bumpCap q 1).trans (ih _)

mutual

/-- Skeleton freshening only advances the capability counter. -/
theorem SupplyExtends.freshenSkeleton {observable : Shape.Observability} :
    ∀ {evidence : Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capability : Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonSupply observable evidence q = some (capability, q') →
      SupplyExtends q q'
  | .unseen, q, _, _, freshened => by
      cases freshened
      exact SupplyExtends.bumpCap q 1
  | .known _, _, _, _, freshened => by
      cases freshened
      exact SupplyExtends.refl _
  | .con _ children, q, _, _, freshened => by
      simp only [freshenSkeletonSupply] at freshened
      split at freshened
      · cases freshened
      · split at freshened
        · cases freshened
        · rename_i capabilities middleSupply maskedEq
          cases freshened
          exact SupplyExtends.freshenSkeletonMasked maskedEq
  | .prod components, q, _, _, freshened => by
      simp only [freshenSkeletonSupply] at freshened
      split at freshened
      · cases freshened
      · rename_i capabilities middleSupply listedEq
        cases freshened
        exact SupplyExtends.freshenSkeletonList listedEq

/-- List skeleton freshening only advances the capability counter. -/
theorem SupplyExtends.freshenSkeletonList {observable : Shape.Observability} :
    ∀ {evidences : List Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capabilities : List Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonListSupply observable evidences q =
        some (capabilities, q') →
      SupplyExtends q q'
  | [], _, _, _, freshened => by
      cases freshened
      exact SupplyExtends.refl _
  | evidence :: rest, q, _, _, freshened => by
      simp only [freshenSkeletonListSupply] at freshened
      split at freshened
      · cases freshened
      · rename_i headCap headSupply headEq
        split at freshened
        · cases freshened
        · rename_i tailCaps tailSupply tailEq
          cases freshened
          exact (SupplyExtends.freshenSkeleton headEq).trans
            (SupplyExtends.freshenSkeletonList tailEq)

/-- Masked skeleton freshening only advances the capability counter. -/
theorem SupplyExtends.freshenSkeletonMasked
    {observable : Shape.Observability} :
    ∀ {mask : List Bool} {evidences : List Shape.Evidence}
      {q : InferenceBase.FreshSupply} {capabilities : List Cap}
      {q' : InferenceBase.FreshSupply},
      freshenSkeletonMaskedSupply observable mask evidences q =
        some (capabilities, q') →
      SupplyExtends q q'
  | [], [], _, _, _, freshened => by
      cases freshened
      exact SupplyExtends.refl _
  | isObservable :: mask, evidence :: rest, q, _, _, freshened => by
      simp only [freshenSkeletonMaskedSupply] at freshened
      split at freshened
      · cases freshened
      · rename_i headCap headSupply headEq
        split at freshened
        · cases freshened
        · rename_i tailCaps tailSupply tailEq
          cases freshened
          refine SupplyExtends.trans ?_
            (SupplyExtends.freshenSkeletonMasked tailEq)
          cases isObservable with
          | true =>
              exact SupplyExtends.freshenSkeleton (by simpa using headEq)
          | false =>
              have collapsed : some (Cap.any, q) =
                  some (headCap, headSupply) := by simpa using headEq
              cases collapsed
              exact SupplyExtends.refl _
  | [], _ :: _, _, _, _, freshened => by cases freshened
  | _ :: _, [], _, _, _, freshened => by cases freshened

end

/-- The matcher-bodied placeholder only advances both counters. -/
theorem SupplyExtends.fixMatcherPlaceholder {signature : FrozenSig}
    {clauses : List Clause} {q : InferenceBase.FreshSupply}
    {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
    (built : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q₀)) :
    SupplyExtends q q₀ := by
  unfold fixMatcherPlaceholderSupply at built
  split at built
  · cases built
  · split at built
    · cases built
    · rename_i middleCap middleSupply middleEq
      have middleExtends : SupplyExtends q middleSupply := by
        split at middleEq
        · cases middleEq
          exact SupplyExtends.refl _
        all_goals exact SupplyExtends.freshenSkeleton middleEq
      refine middleExtends.trans ?_
      split at built <;> cases built
      · exact SupplyExtends.bumpTy _ 2
      · exact SupplyExtends.bumpBoth _ 1 2

/-- Pattern-constructor capability inference only advances the supply. -/
theorem DDPatternCtorCap.supplyExtends {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPatternCtorCap signature entry q S childCaps capability q' S' →
      SupplyExtends q q'
  | .project _ freshened => SupplyExtends.freshenSkeleton freshened
  | .fallback (resultVariables := resultVariables) _ _ _ _ _ freshened =>
      (SupplyExtends.patternCtorAssignments resultVariables.eraseDups _).trans
        (SupplyExtends.freshenSkeleton freshened)

mutual

/-- Primitive-pattern checking only advances the fresh supply. -/
theorem DDPPat.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
    {expectedTarget : Ty} {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPPat signature q S pattern expectedTarget holes bindings q' S' →
      SupplyExtends q q'
  | .hole => SupplyExtends.bumpCap _ 1
  | .wild => SupplyExtends.refl _
  | .pval => SupplyExtends.refl _
  | .ctor (entry := entry) _ _ children =>
      (SupplyExtends.instantiateCtorScheme _ entry.scheme).trans
        children.supplyExtends
  | .tuple (patterns := patterns) _ children =>
      (SupplyExtends.freshTargets patterns.length _).trans
        children.supplyExtends

/-- Primitive-pattern list checking only advances the fresh supply. -/
theorem DDPPats.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List PPat}
    {targets : List Ty} {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPPats signature q S patterns targets holes bindings q' S' →
      SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail _ => (head.supplyExtends).trans tail.supplyExtends

end

mutual

/-- Data-pattern checking only advances the fresh supply. -/
theorem DDDPat.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
    {expectedTarget : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDDPat signature q S pattern expectedTarget bindings q' S' →
      SupplyExtends q q'
  | .var => SupplyExtends.refl _
  | .wild => SupplyExtends.refl _
  | .ctor (scheme := scheme) _ _ children =>
      (SupplyExtends.instantiateCtorScheme _ scheme).trans
        children.supplyExtends
  | .tuple (patterns := patterns) _ children =>
      (SupplyExtends.freshTargets patterns.length _).trans
        children.supplyExtends

/-- Data-pattern list checking only advances the fresh supply. -/
theorem DDDPats.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List DPat}
    {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDDPats signature q S patterns targets bindings q' S' →
      SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail _ => (head.supplyExtends).trans tail.supplyExtends

end

mutual

/-- Synthesis only advances the fresh supply. -/
theorem DDSynth.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {τ : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDSynth signature q S Γ e τ q' S' → SupplyExtends q q'
  | .var (scheme := scheme) _ => SupplyExtends.instantiateScheme _ scheme
  | .lam body =>
      (SupplyExtends.bumpTy _ 1).trans body.supplyExtends
  | .fix _ _ _ body _ =>
      (SupplyExtends.bumpTy _ 2).trans body.supplyExtends
  | .app function _ argument =>
      (function.supplyExtends).trans
        ((SupplyExtends.bumpTy _ 2).trans argument.supplyExtends)
  | .lit => SupplyExtends.refl _
  | .tuple expressions => expressions.supplyExtends
  | .ctor (scheme := scheme) _ arguments =>
      (SupplyExtends.instantiateCtorScheme _ scheme).trans
        arguments.supplyExtends
  | .prim (scheme := scheme) _ arguments =>
      (SupplyExtends.instantiateCtorScheme _ scheme).trans
        arguments.supplyExtends
  | .letE value body =>
      (value.supplyExtends).trans body.supplyExtends
  | .something => SupplyExtends.bumpTy _ 1
  | .matcher clauses _ _ _ _ _ _ _ =>
      (SupplyExtends.bumpTy _ 1).trans clauses.supplyExtends
  | .matchAll target pattern _ matcher body =>
      (target.supplyExtends).trans ((pattern.supplyExtends).trans
        ((matcher.supplyExtends).trans body.supplyExtends))
  | .fixMatcher _ _ built body _ =>
      (SupplyExtends.fixMatcherPlaceholder built).trans body.supplyExtends

/-- List synthesis only advances the fresh supply. -/
theorem DDSynths.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {τs : List Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDSynths signature q S Γ es τs q' S' → SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail =>
      (head.supplyExtends).trans tail.supplyExtends

/-- Checking only advances the fresh supply. -/
theorem DDCheck.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {expected : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDCheck signature q S Γ e expected q' S' → SupplyExtends q q'
  | .mk synthesized _ => synthesized.supplyExtends

/-- List checking only advances the fresh supply. -/
theorem DDChecks.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDChecks signature q S Γ es expecteds q' S' → SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail =>
      (head.supplyExtends).trans tail.supplyExtends

/-- Pattern synthesis only advances the fresh supply. -/
theorem DDPattern.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {Φ : PatternCtx} {Δ : MonoCtx} {pattern : Pattern} {dual : Dual}
    {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDPattern signature q S Γ Φ Δ pattern dual Δ' q' S' →
      SupplyExtends q q'
  | .pvar _ => SupplyExtends.bumpBoth _ 1 1
  | .wild => SupplyExtends.bumpBoth _ 1 1
  | .pval value => (value.supplyExtends).trans (SupplyExtends.bumpCap _ 1)
  | .embed _ => SupplyExtends.refl _
  | .ptuple patterns => patterns.supplyExtends
  | .pctor (entry := entry) _ patterns _ ctorCap _ =>
      (SupplyExtends.instantiateCtorScheme _ entry.scheme).trans
        ((patterns.supplyExtends).trans ctorCap.supplyExtends)
  | .pand left right _ => (left.supplyExtends).trans right.supplyExtends
  | .por left right _ _ => (left.supplyExtends).trans right.supplyExtends
  | .papp (scheme := scheme) _ patterns _ =>
      (SupplyExtends.instantiateDualScheme _ scheme).trans
        patterns.supplyExtends

/-- Pattern-list synthesis only advances the fresh supply. -/
theorem DDPatterns.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {Φ : PatternCtx} {Δ : MonoCtx} {patterns : List Pattern}
    {duals : List Dual} {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDPatterns signature q S Γ Φ Δ patterns duals Δ' q' S' →
      SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail => (head.supplyExtends).trans tail.supplyExtends

/-- Arm checking only advances the fresh supply. -/
theorem DDArms.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {ppBindings : MonoCtx} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDArms signature q S Γ ppBindings arms clauseTarget bodyTarget q' S' →
      SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons dataPattern _ body rest =>
      (dataPattern.supplyExtends).trans
        ((body.supplyExtends).trans rest.supplyExtends)

/-- Clause inference only advances the fresh supply. -/
theorem DDClause.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {clause : Clause} {sharedTarget : Ty} {holes : List Dual}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDClause signature q S Γ clause sharedTarget holes q' S' →
      SupplyExtends q q'
  | .mk pp _ nextMatchers arms =>
      (pp.supplyExtends).trans
        ((nextMatchers.supplyExtends).trans arms.supplyExtends)

/-- Clause-list inference only advances the fresh supply. -/
theorem DDClauses.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDClauses signature q S Γ clauses sharedTarget holeLists q' S' →
      SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail => (head.supplyExtends).trans tail.supplyExtends

end

/-! ## Freshness: supply-bounded variables

The first layer of the freshness invariant: boundedness of both variable
sorts by a fresh supply, monotone along supply extension, closed under
application and sequencing of bounded substitutions, and the half of
exact-delta boundedness that already follows from exactness — a solve
delta of a bounded constraint is the identity at and above the bound.  The
remaining half (images of in-constraint variables stay below the bound) is
the recorded next step: it either follows from most-generality through the
executable solver's range certificates, or becomes one more exactness
conjunct.
-/

mutual

/-- Capability application does not change target variables. -/
theorem Ty.ftv_applyCapability :
    ∀ (target : Ty) (C : CapSubst),
      (target.applyCapability C).ftv = target.ftv
  | .var _, _ => rfl
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data _ fields, C => by
      simp only [Ty.applyCapability, Ty.ftv]
      exact Ty.ftvList_applyCapabilityList fields C
  | .prod components, C => by
      simp only [Ty.applyCapability, Ty.ftv]
      exact Ty.ftvList_applyCapabilityList components C
  | .fn domain codomain, C => by
      simp only [Ty.applyCapability, Ty.ftv,
        Ty.ftv_applyCapability domain C, Ty.ftv_applyCapability codomain C]
  | .matcher capability target, C => by
      simp only [Ty.applyCapability, Ty.ftv]
      exact Ty.ftv_applyCapability target C
  | .slot capability target, C => by
      simp only [Ty.applyCapability, Ty.ftv]
      exact Ty.ftv_applyCapability target C

/-- List form of `Ty.ftv_applyCapability`. -/
theorem Ty.ftvList_applyCapabilityList :
    ∀ (types : List Ty) (C : CapSubst),
      Ty.ftvList (Ty.applyCapabilityList C types) = Ty.ftvList types
  | [], _ => rfl
  | τ :: types, C => by
      simp only [Ty.applyCapabilityList, Ty.ftvList,
        Ty.ftv_applyCapability τ C, Ty.ftvList_applyCapabilityList types C]

end

mutual

/-- Capability variables of a capability-substituted type are the image
variables of its capability variables. -/
theorem Ty.fcv_applyCapability :
    ∀ (target : Ty) (C : CapSubst),
      (target.applyCapability C).fcv = target.fcv.flatMap fun x => (C x).fcv
  | .var _, _ => rfl
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data _ fields, C => by
      simp only [Ty.applyCapability, Ty.fcv]
      exact Ty.fcvList_applyCapabilityList fields C
  | .prod components, C => by
      simp only [Ty.applyCapability, Ty.fcv]
      exact Ty.fcvList_applyCapabilityList components C
  | .fn domain codomain, C => by
      simp only [Ty.applyCapability, Ty.fcv, List.flatMap_append,
        Ty.fcv_applyCapability domain C, Ty.fcv_applyCapability codomain C]
  | .matcher capability target, C => by
      simp only [Ty.applyCapability, Ty.fcv, List.flatMap_append,
        Unification.Cap.fcv_apply capability C,
        Ty.fcv_applyCapability target C]
  | .slot capability target, C => by
      simp only [Ty.applyCapability, Ty.fcv, List.flatMap_append,
        Unification.Cap.fcv_apply capability C,
        Ty.fcv_applyCapability target C]

/-- List form of `Ty.fcv_applyCapability`. -/
theorem Ty.fcvList_applyCapabilityList :
    ∀ (types : List Ty) (C : CapSubst),
      Ty.fcvList (Ty.applyCapabilityList C types) =
        (Ty.fcvList types).flatMap fun x => (C x).fcv
  | [], _ => rfl
  | τ :: types, C => by
      simp only [Ty.applyCapabilityList, Ty.fcvList, List.flatMap_append,
        Ty.fcv_applyCapability τ C, Ty.fcvList_applyCapabilityList types C]

end

mutual

/-- A capability variable of a target-substituted type is either an
original capability variable or a capability variable of an image. -/
theorem Ty.mem_fcv_applyTarget :
    ∀ (target : Ty) (T : TySubst) (varId : CapVar),
      varId ∈ (target.applyTarget T).fcv →
      varId ∈ target.fcv ∨
        ∃ tyVar, tyVar ∈ target.ftv ∧ varId ∈ (T tyVar).fcv
  | .var tyVar, _, _, mem => Or.inr ⟨tyVar, by simp [Ty.ftv], mem⟩
  | .skolem _, _, _, mem => nomatch mem
  | .unit, _, _, mem => nomatch mem
  | .int, _, _, mem => nomatch mem
  | .bool, _, _, mem => nomatch mem
  | .data _ fields, T, varId, mem =>
      Ty.memList_fcvList_applyTargetList fields T varId mem
  | .prod components, T, varId, mem =>
      Ty.memList_fcvList_applyTargetList components T varId mem
  | .fn domain codomain, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · rcases Ty.mem_fcv_applyTarget domain T varId here with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inl own))
        · obtain ⟨tyVar, tyMem, imageMem⟩ := image
          exact Or.inr ⟨tyVar, List.mem_append.mpr (Or.inl tyMem), imageMem⟩
      · rcases Ty.mem_fcv_applyTarget codomain T varId there with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inr own))
        · obtain ⟨tyVar, tyMem, imageMem⟩ := image
          exact Or.inr ⟨tyVar, List.mem_append.mpr (Or.inr tyMem), imageMem⟩
  | .matcher capability target, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact Or.inl (List.mem_append.mpr (Or.inl here))
      · rcases Ty.mem_fcv_applyTarget target T varId there with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inr own))
        · exact Or.inr image
  | .slot capability target, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact Or.inl (List.mem_append.mpr (Or.inl here))
      · rcases Ty.mem_fcv_applyTarget target T varId there with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inr own))
        · exact Or.inr image

/-- List form of `Ty.mem_fcv_applyTarget`. -/
theorem Ty.memList_fcvList_applyTargetList :
    ∀ (types : List Ty) (T : TySubst) (varId : CapVar),
      varId ∈ Ty.fcvList (Ty.applyTargetList T types) →
      varId ∈ Ty.fcvList types ∨
        ∃ tyVar, tyVar ∈ Ty.ftvList types ∧ varId ∈ (T tyVar).fcv
  | [], _, _, mem => nomatch mem
  | τ :: types, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · rcases Ty.mem_fcv_applyTarget τ T varId here with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inl own))
        · obtain ⟨tyVar, tyMem, imageMem⟩ := image
          exact Or.inr ⟨tyVar, List.mem_append.mpr (Or.inl tyMem), imageMem⟩
      · rcases Ty.memList_fcvList_applyTargetList types T varId there
          with own | image
        · exact Or.inl (List.mem_append.mpr (Or.inr own))
        · obtain ⟨tyVar, tyMem, imageMem⟩ := image
          exact Or.inr ⟨tyVar, List.mem_append.mpr (Or.inr tyMem), imageMem⟩

end

mutual

/-- Target substitution cannot erase a capability occurrence already present
in the target skeleton.  It may add capability occurrences through target
images, but every original capability leaf survives. -/
theorem Ty.mem_fcv_applyTarget_of_mem :
    ∀ (target : Ty) (T : TySubst) (varId : CapVar),
      varId ∈ target.fcv → varId ∈ (target.applyTarget T).fcv
  | .var _, _, _, mem => nomatch mem
  | .skolem _, _, _, mem => nomatch mem
  | .unit, _, _, mem => nomatch mem
  | .int, _, _, mem => nomatch mem
  | .bool, _, _, mem => nomatch mem
  | .data name fields, T, varId, mem =>
      Ty.memList_fcvList_applyTargetList_of_mem fields T varId mem
  | .prod components, T, varId, mem =>
      Ty.memList_fcvList_applyTargetList_of_mem components T varId mem
  | .fn domain codomain, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact List.mem_append.mpr (Or.inl
          (Ty.mem_fcv_applyTarget_of_mem domain T varId here))
      · exact List.mem_append.mpr (Or.inr
          (Ty.mem_fcv_applyTarget_of_mem codomain T varId there))
  | .matcher capability target, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact List.mem_append.mpr (Or.inl here)
      · exact List.mem_append.mpr (Or.inr
          (Ty.mem_fcv_applyTarget_of_mem target T varId there))
  | .slot capability target, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact List.mem_append.mpr (Or.inl here)
      · exact List.mem_append.mpr (Or.inr
          (Ty.mem_fcv_applyTarget_of_mem target T varId there))

/-- List form of `Ty.mem_fcv_applyTarget_of_mem`. -/
theorem Ty.memList_fcvList_applyTargetList_of_mem :
    ∀ (types : List Ty) (T : TySubst) (varId : CapVar),
      varId ∈ Ty.fcvList types →
        varId ∈ Ty.fcvList (Ty.applyTargetList T types)
  | [], _, _, mem => nomatch mem
  | target :: targets, T, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact List.mem_append.mpr (Or.inl
          (Ty.mem_fcv_applyTarget_of_mem target T varId here))
      · exact List.mem_append.mpr (Or.inr
          (Ty.memList_fcvList_applyTargetList_of_mem targets T varId there))

end

/-! ### Scheme-instance capability views

These small certificates connect the three representations of one quantified
capability at a context lookup: its scheme binder, the fresh variable placed
in the executable instance, and the rename-only entry installed in the DD
origin ledger.  Keeping the connection explicit avoids reconstructing fresh
image arithmetic during derivation inversion. -/

/-- The fresh capability image allocated for one expression-scheme binder,
together with its origin at the post-lookup ledger cut. -/
structure SchemeInstanceCapView (ledger : CapabilityOriginLedger)
    (q : InferenceBase.FreshSupply) (scheme : Scheme)
    (binder image : CapVar) : Prop where
  binderMem : binder ∈ scheme.capBinders
  imageEquation :
    (InferenceBase.instantiateScheme q scheme).subst.cap binder = .var image
  imageMem : image ∈ Inference.freshCapImages q scheme.capBinders
  markedOrigin :
    (DDLedger.markSchemeInstance ledger q scheme).originOf image =
      .renameOnly

/-- A scheme-instance capability view whose binder actually occurs in the
scheme body.  The corresponding fresh image therefore occurs in the
instantiated value as well. -/
structure SchemeInstanceCapOccurrenceView
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : Scheme) (binder image : CapVar) : Prop
    extends SchemeInstanceCapView ledger q scheme binder image where
  bodyMem : binder ∈ scheme.body.fcv
  valueMem : image ∈ (InferenceBase.instantiateScheme q scheme).value.fcv

/-- Capture-avoiding scheme substitution preserves the binder lists. -/
@[simp] theorem Scheme.applySubst_capBinders (scheme : Scheme) (S : Subst) :
    (scheme.applySubst S).capBinders = scheme.capBinders := rfl

/-- A bound capability occurrence in a scheme body survives every
capture-avoiding external substitution because masking fixes the binder. -/
theorem Scheme.mem_applySubst_body_fcv_of_bound
    (scheme : Scheme) (S : Subst) {binder : CapVar}
    (binderMem : binder ∈ scheme.capBinders)
    (bodyMem : binder ∈ scheme.body.fcv) :
    binder ∈ (scheme.applySubst S).body.fcv := by
  let masked := Subst.mk (S.cap.mask scheme.capBinders)
    (S.target.mask scheme.tyBinders)
  have maskedImage : masked.cap binder = .var binder := by
    simp [masked, CapSubst.mask, binderMem]
  have inCapabilityApplied : binder ∈
      (scheme.body.applyCapability masked.cap).fcv := by
    rw [Ty.fcv_applyCapability]
    simp only [List.mem_flatMap]
    exact ⟨binder, bodyMem, by simp [maskedImage, Cap.fcv]⟩
  change binder ∈
    ((scheme.body.applyCapability masked.cap).applyTarget masked.target).fcv
  exact Ty.mem_fcv_applyTarget_of_mem _ _ _ inCapabilityApplied

/-- Membership in a generalized capability-binder list entails occurrence
in the generalized body. -/
theorem FrozenSig.generalize_capBinder_bodyMem
    (signature : FrozenSig) (context : Context) (target : Ty)
    {binder : CapVar}
    (binderMem : binder ∈
      (signature.generalize context target).capBinders) :
    binder ∈ (signature.generalize context target).body.fcv := by
  unfold FrozenSig.generalize TypePM.generalize at binderMem ⊢
  exact (List.mem_filter.mp (mem_uniqueVars.mp binderMem)).1

/-- Every quantified capability binder has one canonical fresh-image view at
the lookup cut. -/
theorem SchemeInstanceCapView.ofBinder
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : Scheme) {binder : CapVar}
    (binderMem : binder ∈ scheme.capBinders) :
    SchemeInstanceCapView ledger q scheme binder
      ⟨q.nextCap + binder.id⟩ := by
  have imageMem : ⟨q.nextCap + binder.id⟩ ∈
      Inference.freshCapImages q scheme.capBinders :=
    List.mem_map.mpr ⟨binder, binderMem, rfl⟩
  exact
    { binderMem := binderMem
      imageEquation := by
        simp [InferenceBase.instantiateScheme,
          InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
          binderMem]
      imageMem := imageMem
      markedOrigin := DDLedger.markSchemeInstance_origin_of_mem
        ledger q scheme _ imageMem }

/-- If a viewed binder is the capability at a function domain's matcher
head, instantiation exposes its fresh image at that same head. -/
theorem SchemeInstanceCapView.value_fnMatcherView
    {ledger : CapabilityOriginLedger} {q : InferenceBase.FreshSupply}
    {scheme : Scheme} {binder image : CapVar}
    (view : SchemeInstanceCapView ledger q scheme binder image)
    {domain codomain : Ty}
    (bodyView : scheme.body = .fn (.matcher (.var binder) domain) codomain) :
    (InferenceBase.instantiateScheme q scheme).value =
      .fn (.matcher (.var image)
        ((InferenceBase.instantiateScheme q scheme).subst.apply domain))
        ((InferenceBase.instantiateScheme q scheme).subst.apply codomain) := by
  change (InferenceBase.instantiateScheme q scheme).subst.apply scheme.body = _
  rw [bodyView]
  change Ty.fn
      (Ty.matcher
        ((InferenceBase.instantiateScheme q scheme).subst.cap binder)
        ((InferenceBase.instantiateScheme q scheme).subst.apply domain))
      ((InferenceBase.instantiateScheme q scheme).subst.apply codomain) = _
  rw [view.imageEquation]

/-- Capture-avoiding substitution preserves a matcher-headed function domain
whose capability variable is bound by the scheme. -/
theorem Scheme.applySubst_body_fnMatcherView_of_bound
    (scheme : Scheme) (external : Subst) {binder : CapVar}
    {domain codomain : Ty}
    (binderMem : binder ∈ scheme.capBinders)
    (bodyView : scheme.body = .fn (.matcher (.var binder) domain) codomain) :
    (scheme.applySubst external).body =
      .fn (.matcher (.var binder)
        ((Subst.mk (external.cap.mask scheme.capBinders)
          (external.target.mask scheme.tyBinders)).apply domain))
        ((Subst.mk (external.cap.mask scheme.capBinders)
          (external.target.mask scheme.tyBinders)).apply codomain) := by
  change (Subst.mk (external.cap.mask scheme.capBinders)
      (external.target.mask scheme.tyBinders)).apply scheme.body = _
  rw [bodyView]
  simp [CapSubst.mask, binderMem, Cap.apply]

/-- If the binder occurs in the scheme body, its canonical fresh image is
visible in the instantiated type. -/
theorem SchemeInstanceCapOccurrenceView.ofBodyBinder
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (scheme : Scheme) {binder : CapVar}
    (binderMem : binder ∈ scheme.capBinders)
    (bodyMem : binder ∈ scheme.body.fcv) :
    SchemeInstanceCapOccurrenceView ledger q scheme binder
      ⟨q.nextCap + binder.id⟩ := by
  let assignment := InferenceBase.instantiateBinders q
    scheme.capBinders scheme.tyBinders
  have imageEquation : assignment.subst.cap binder =
      .var ⟨q.nextCap + binder.id⟩ := by
    simp [assignment, InferenceBase.instantiateBinders,
      InferenceBase.freshCapSubst, binderMem]
  have inCapabilityApplied : ⟨q.nextCap + binder.id⟩ ∈
      (scheme.body.applyCapability assignment.subst.cap).fcv := by
    rw [Ty.fcv_applyCapability]
    simp only [List.mem_flatMap]
    exact ⟨binder, bodyMem, by simp [imageEquation, Cap.fcv]⟩
  have valueMem : ⟨q.nextCap + binder.id⟩ ∈
      (InferenceBase.instantiateScheme q scheme).value.fcv := by
    change ⟨q.nextCap + binder.id⟩ ∈
      ((scheme.body.applyCapability assignment.subst.cap).applyTarget
        assignment.subst.target).fcv
    exact Ty.mem_fcv_applyTarget_of_mem _ _ _ inCapabilityApplied
  exact
    { toSchemeInstanceCapView :=
        SchemeInstanceCapView.ofBinder ledger q scheme binderMem
      bodyMem := bodyMem
      valueMem := valueMem }

/-- Direct lookup view for a binder of a generalized scheme after the
prevailing substitution has been applied to the body context.  This is the
shape consumed by the DD `let` rule. -/
theorem SchemeInstanceCapOccurrenceView.ofGeneralizedBinder
    (ledger : CapabilityOriginLedger) (q : InferenceBase.FreshSupply)
    (signature : FrozenSig) (context : Context) (target : Ty)
    (external : Subst) {binder : CapVar}
    (binderMem : binder ∈
      (signature.generalize context target).capBinders) :
    SchemeInstanceCapOccurrenceView ledger q
      ((signature.generalize context target).applySubst external) binder
      ⟨q.nextCap + binder.id⟩ := by
  apply SchemeInstanceCapOccurrenceView.ofBodyBinder
  · simpa using binderMem
  · exact Scheme.mem_applySubst_body_fcv_of_bound _ _ binderMem
      (FrozenSig.generalize_capBinder_bodyMem _ _ _ binderMem)

/-! ### Fixedness discharge for solved-form composition

A solved-form prevailing substitution fixes the free variables of its own
images, an exact delta's support and range live on prevailing images, and
therefore the prevailing substitution fixes every composite image.  This
discharges the fixedness premise of `Subst.seq_idempotent` at every
ordinary alignment, so prevailing substitutions built from ordinary exact
solves stay in solved form and absorb
(`Subst.seq_absorbs_of_idempotent`). -/

mutual

/-- If applying a capability substitution reproduces a capability exactly,
the substitution fixes every free variable of that capability. -/
theorem Cap.fixed_of_apply_self {S : CapSubst} :
    ∀ capability : Cap, capability.apply S = capability →
      ∀ varId ∈ capability.fcv, S varId = .var varId
  | .any, _, _, mem => nomatch mem
  | .var a, applied, varId, mem => by
      have h : varId = a := by simpa [Cap.fcv] using mem
      subst h
      exact applied
  | .skolem _, _, _, mem => nomatch mem
  | .con n caps, applied, varId, mem => by
      have applied' : Cap.con n (Cap.applyList S caps) = Cap.con n caps :=
        applied
      injection applied' with _ listEq
      exact Cap.fixed_of_applyList_self caps listEq varId mem
  | .prod caps, applied, varId, mem => by
      have applied' : Cap.prod (Cap.applyList S caps) = Cap.prod caps :=
        applied
      injection applied' with listEq
      exact Cap.fixed_of_applyList_self caps listEq varId mem

/-- List form of `Cap.fixed_of_apply_self`. -/
theorem Cap.fixed_of_applyList_self {S : CapSubst} :
    ∀ capabilities : List Cap,
      Cap.applyList S capabilities = capabilities →
      ∀ varId ∈ Cap.fcvList capabilities, S varId = .var varId
  | [], _, _, mem => nomatch mem
  | capability :: capabilities, applied, varId, mem => by
      have applied' :
          capability.apply S :: Cap.applyList S capabilities =
            capability :: capabilities := applied
      injection applied' with headEq tailEq
      have mem' : varId ∈ capability.fcv ++ Cap.fcvList capabilities := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Cap.fixed_of_apply_self capability headEq varId here
      · exact Cap.fixed_of_applyList_self capabilities tailEq varId there

end

mutual

/-- If a paired substitution reproduces a type exactly, its target component
fixes every free target variable of that type. -/
theorem Subst.target_fixed_of_apply_self {S : Subst} :
    ∀ target : Ty, S.apply target = target →
      ∀ varId ∈ target.ftv, S.target varId = .var varId
  | .var a, applied, varId, mem => by
      have h : varId = a := by simpa [Ty.ftv] using mem
      subst h
      exact applied
  | .skolem _, _, _, mem => nomatch mem
  | .unit, _, _, mem => nomatch mem
  | .int, _, _, mem => nomatch mem
  | .bool, _, _, mem => nomatch mem
  | .data n targets, applied, varId, mem => by
      have applied' :
          Ty.data n (Ty.applyTargetList S.target
            (Ty.applyCapabilityList S.cap targets)) = Ty.data n targets :=
        applied
      injection applied' with _ listEq
      exact Subst.target_fixed_of_applyList_self targets listEq varId mem
  | .prod targets, applied, varId, mem => by
      have applied' :
          Ty.prod (Ty.applyTargetList S.target
            (Ty.applyCapabilityList S.cap targets)) = Ty.prod targets :=
        applied
      injection applied' with listEq
      exact Subst.target_fixed_of_applyList_self targets listEq varId mem
  | .fn domain codomain, applied, varId, mem => by
      have applied' :
          Ty.fn (S.apply domain) (S.apply codomain) = Ty.fn domain codomain :=
        applied
      injection applied' with domainEq codomainEq
      have mem' : varId ∈ domain.ftv ++ codomain.ftv := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Subst.target_fixed_of_apply_self domain domainEq varId here
      · exact Subst.target_fixed_of_apply_self codomain codomainEq varId there
  | .matcher capability target, applied, varId, mem => by
      have applied' :
          Ty.matcher (capability.apply S.cap) (S.apply target) =
            Ty.matcher capability target := applied
      injection applied' with _ targetEq
      exact Subst.target_fixed_of_apply_self target targetEq varId mem
  | .slot capability target, applied, varId, mem => by
      have applied' :
          Ty.slot (capability.apply S.cap) (S.apply target) =
            Ty.slot capability target := applied
      injection applied' with _ targetEq
      exact Subst.target_fixed_of_apply_self target targetEq varId mem

/-- List form of `Subst.target_fixed_of_apply_self`. -/
theorem Subst.target_fixed_of_applyList_self {S : Subst} :
    ∀ targets : List Ty,
      Ty.applyTargetList S.target (Ty.applyCapabilityList S.cap targets) =
        targets →
      ∀ varId ∈ Ty.ftvList targets, S.target varId = .var varId
  | [], _, _, mem => nomatch mem
  | target :: targets, applied, varId, mem => by
      have applied' :
          S.apply target ::
            Ty.applyTargetList S.target
              (Ty.applyCapabilityList S.cap targets) =
            target :: targets := applied
      injection applied' with headEq tailEq
      have mem' : varId ∈ target.ftv ++ Ty.ftvList targets := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Subst.target_fixed_of_apply_self target headEq varId here
      · exact Subst.target_fixed_of_applyList_self targets tailEq varId there

end

mutual

/-- If a paired substitution reproduces a type exactly, its capability
component fixes every free capability variable of that type. -/
theorem Subst.cap_fixed_of_apply_self {S : Subst} :
    ∀ target : Ty, S.apply target = target →
      ∀ varId ∈ target.fcv, S.cap varId = .var varId
  | .var _, _, _, mem => nomatch mem
  | .skolem _, _, _, mem => nomatch mem
  | .unit, _, _, mem => nomatch mem
  | .int, _, _, mem => nomatch mem
  | .bool, _, _, mem => nomatch mem
  | .data n targets, applied, varId, mem => by
      have applied' :
          Ty.data n (Ty.applyTargetList S.target
            (Ty.applyCapabilityList S.cap targets)) = Ty.data n targets :=
        applied
      injection applied' with _ listEq
      exact Subst.cap_fixed_of_applyList_self targets listEq varId mem
  | .prod targets, applied, varId, mem => by
      have applied' :
          Ty.prod (Ty.applyTargetList S.target
            (Ty.applyCapabilityList S.cap targets)) = Ty.prod targets :=
        applied
      injection applied' with listEq
      exact Subst.cap_fixed_of_applyList_self targets listEq varId mem
  | .fn domain codomain, applied, varId, mem => by
      have applied' :
          Ty.fn (S.apply domain) (S.apply codomain) = Ty.fn domain codomain :=
        applied
      injection applied' with domainEq codomainEq
      have mem' : varId ∈ domain.fcv ++ codomain.fcv := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Subst.cap_fixed_of_apply_self domain domainEq varId here
      · exact Subst.cap_fixed_of_apply_self codomain codomainEq varId there
  | .matcher capability target, applied, varId, mem => by
      have applied' :
          Ty.matcher (capability.apply S.cap) (S.apply target) =
            Ty.matcher capability target := applied
      injection applied' with capEq targetEq
      have mem' : varId ∈ capability.fcv ++ target.fcv := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Cap.fixed_of_apply_self capability capEq varId here
      · exact Subst.cap_fixed_of_apply_self target targetEq varId there
  | .slot capability target, applied, varId, mem => by
      have applied' :
          Ty.slot (capability.apply S.cap) (S.apply target) =
            Ty.slot capability target := applied
      injection applied' with capEq targetEq
      have mem' : varId ∈ capability.fcv ++ target.fcv := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Cap.fixed_of_apply_self capability capEq varId here
      · exact Subst.cap_fixed_of_apply_self target targetEq varId there

/-- List form of `Subst.cap_fixed_of_apply_self`. -/
theorem Subst.cap_fixed_of_applyList_self {S : Subst} :
    ∀ targets : List Ty,
      Ty.applyTargetList S.target (Ty.applyCapabilityList S.cap targets) =
        targets →
      ∀ varId ∈ Ty.fcvList targets, S.cap varId = .var varId
  | [], _, _, mem => nomatch mem
  | target :: targets, applied, varId, mem => by
      have applied' :
          S.apply target ::
            Ty.applyTargetList S.target
              (Ty.applyCapabilityList S.cap targets) =
            target :: targets := applied
      injection applied' with headEq tailEq
      have mem' : varId ∈ target.fcv ++ Ty.fcvList targets := mem
      rcases List.mem_append.mp mem' with here | there
      · exact Subst.cap_fixed_of_apply_self target headEq varId here
      · exact Subst.cap_fixed_of_applyList_self targets tailEq varId there

end

/-- A solved-form substitution fixes the target variables of its images. -/
theorem Subst.Idempotent.image_target_fixed {S : Subst}
    (idem : S.Idempotent) (target : Ty) :
    ∀ varId ∈ (S.apply target).ftv, S.target varId = .var varId :=
  Subst.target_fixed_of_apply_self (S.apply target) (idem target)

/-- A solved-form substitution fixes the capability variables of its
images. -/
theorem Subst.Idempotent.image_cap_fixed {S : Subst}
    (idem : S.Idempotent) (target : Ty) :
    ∀ varId ∈ (S.apply target).fcv, S.cap varId = .var varId :=
  Subst.cap_fixed_of_apply_self (S.apply target) (idem target)

/-- Fixing both sorts of free variables fixes the whole type. -/
theorem Subst.apply_eq_self_of_fixed {S : Subst} {target : Ty}
    (targetsFixed : ∀ varId ∈ target.ftv, S.target varId = .var varId)
    (capsFixed : ∀ varId ∈ target.fcv, S.cap varId = .var varId) :
    S.apply target = target := by
  show (target.applyCapability S.cap).applyTarget S.target = target
  rw [Ty.applyCapability_eq_self_of_fcv_fixed S.cap target capsFixed]
  exact Ty.applyTarget_eq_self_of_ftv_fixed S.target target targetsFixed

/-- The prevailing substitution fixes every image of an exact delta over a
prevailing-resolved constraint: the delta's support and range live on
prevailing images, which a solved-form prevailing substitution does not
move.  This discharges the fixedness premise of `Subst.seq_idempotent` at
every ordinary alignment. -/
theorem ExactPairedMGU.prevailing_fixed {S delta : Subst} {left right : Ty}
    (idem : S.Idempotent)
    (exact : ExactPairedMGU (S.apply left) (S.apply right) delta) :
    ∀ target : Ty,
      S.apply (delta.apply (S.apply target)) =
        delta.apply (S.apply target) := by
  intro target
  apply Subst.apply_eq_self_of_fixed
  · intro varId mem
    have mem' : varId ∈
        (((S.apply target).applyCapability delta.cap).applyTarget
          delta.target).ftv := mem
    rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability] at mem'
    obtain ⟨tyVar, tyMem, imageMem⟩ := List.mem_flatMap.mp mem'
    by_cases inConstraint :
        tyVar ∈ (S.apply left).ftv ++ (S.apply right).ftv
    · have imageIn : varId ∈ (S.apply left).ftv ++ (S.apply right).ftv :=
        exact.2.2.2.2.1 tyVar inConstraint varId imageMem
      rcases List.mem_append.mp imageIn with here | there
      · exact idem.image_target_fixed left varId here
      · exact idem.image_target_fixed right varId there
    · rw [exact.2.2.1 tyVar inConstraint] at imageMem
      have h : varId = tyVar := by simpa [Ty.ftv] using imageMem
      subst h
      exact idem.image_target_fixed target varId tyMem
  · intro varId mem
    have mem' : varId ∈
        (((S.apply target).applyCapability delta.cap).applyTarget
          delta.target).fcv := mem
    rcases Ty.mem_fcv_applyTarget _ _ _ mem' with inCapSide | inTargetImage
    · rw [Ty.fcv_applyCapability] at inCapSide
      obtain ⟨capVar, capMem, imageMem⟩ := List.mem_flatMap.mp inCapSide
      by_cases inConstraint :
          capVar ∈ (S.apply left).fcv ++ (S.apply right).fcv
      · have imageIn : varId ∈ (S.apply left).fcv ++ (S.apply right).fcv :=
          exact.2.2.2.1 capVar inConstraint varId imageMem
        rcases List.mem_append.mp imageIn with here | there
        · exact idem.image_cap_fixed left varId here
        · exact idem.image_cap_fixed right varId there
      · rw [exact.2.1 capVar inConstraint] at imageMem
        have h : varId = capVar := by simpa [Cap.fcv] using imageMem
        subst h
        exact idem.image_cap_fixed target varId capMem
    · obtain ⟨tyVar, tyMem, imageMem⟩ := inTargetImage
      rw [Ty.ftv_applyCapability] at tyMem
      by_cases inConstraint :
          tyVar ∈ (S.apply left).ftv ++ (S.apply right).ftv
      · have imageIn : varId ∈ (S.apply left).fcv ++ (S.apply right).fcv :=
          exact.2.2.2.2.2.1 tyVar inConstraint varId imageMem
        rcases List.mem_append.mp imageIn with here | there
        · exact idem.image_cap_fixed left varId here
        · exact idem.image_cap_fixed right varId there
      · rw [exact.2.2.1 tyVar inConstraint] at imageMem
        nomatch imageMem

/-- An ordinary exact solve over a solved-form prevailing substitution
keeps the composite prevailing substitution in solved form. -/
theorem ExactPairedMGU.seq_idempotent {S delta : Subst} {left right : Ty}
    (idem : S.Idempotent)
    (exact : ExactPairedMGU (S.apply left) (S.apply right) delta) :
    (Subst.seq delta S).Idempotent :=
  Subst.seq_idempotent exact.2.2.2.2.2.2 (exact.prevailing_fixed idem)

/-- All capability variables lie below the supply's capability counter. -/
def Cap.BoundedBy (q : InferenceBase.FreshSupply) (capability : Cap) : Prop :=
  ∀ varId ∈ capability.fcv, varId.id < q.nextCap

/-- All variables of both sorts lie below the supply's counters. -/
structure Ty.BoundedBy (q : InferenceBase.FreshSupply) (target : Ty) :
    Prop where
  caps : ∀ varId ∈ target.fcv, varId.id < q.nextCap
  targets : ∀ varId ∈ target.ftv, varId < q.nextTy

/-- A bounded substitution: the identity at and above the counters, with
bounded images below them. -/
structure Subst.BoundedBy (q : InferenceBase.FreshSupply) (S : Subst) :
    Prop where
  capFixedAbove : ∀ varId : CapVar, q.nextCap ≤ varId.id →
    S.cap varId = .var varId
  capImagesBounded : ∀ varId : CapVar, varId.id < q.nextCap →
    Cap.BoundedBy q (S.cap varId)
  targetFixedAbove : ∀ varId : TypePM.TyVar, q.nextTy ≤ varId →
    S.target varId = .var varId
  targetImagesBounded : ∀ varId : TypePM.TyVar, varId < q.nextTy →
    Ty.BoundedBy q (S.target varId)

/-- A substitution bounded at a cut cannot anticipate the next capability
metavariable allocated at that cut. -/
theorem Subst.BoundedBy.freshCapFixed
    {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) :
    S.cap ⟨q.nextCap⟩ = .var ⟨q.nextCap⟩ :=
  bounded.capFixedAbove ⟨q.nextCap⟩ (Nat.le_refl _)

/-- Ordinary-variable counterpart of `freshCapFixed`. -/
theorem Subst.BoundedBy.freshTargetFixed
    {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) :
    S.target q.nextTy = .var q.nextTy :=
  bounded.targetFixedAbove q.nextTy (Nat.le_refl _)

/-- Capability boundedness is monotone along supply extension. -/
theorem Cap.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {capability : Cap} (extends_ : SupplyExtends q q')
    (bounded : capability.BoundedBy q) : capability.BoundedBy q' :=
  fun varId mem => Nat.lt_of_lt_of_le (bounded varId mem) extends_.1

/-- Type boundedness is monotone along supply extension. -/
theorem Ty.BoundedBy.mono {q q' : InferenceBase.FreshSupply} {target : Ty}
    (extends_ : SupplyExtends q q') (bounded : target.BoundedBy q) :
    target.BoundedBy q' :=
  ⟨fun varId mem => Nat.lt_of_lt_of_le (bounded.caps varId mem) extends_.1,
    fun varId mem =>
      Nat.lt_of_lt_of_le (bounded.targets varId mem) extends_.2⟩

/-- Substitution boundedness is monotone along supply extension. -/
theorem Subst.BoundedBy.mono {q q' : InferenceBase.FreshSupply} {S : Subst}
    (extends_ : SupplyExtends q q') (bounded : S.BoundedBy q) :
    S.BoundedBy q' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    exact bounded.capFixedAbove varId (Nat.le_trans extends_.1 above)
  · intro varId below
    by_cases original : varId.id < q.nextCap
    · exact (bounded.capImagesBounded varId original).mono extends_
    · rw [bounded.capFixedAbove varId (Nat.le_of_not_lt original)]
      intro image mem
      have : image = varId := by
        simpa [Cap.fcv] using mem
      simpa [this]
  · intro varId above
    exact bounded.targetFixedAbove varId (Nat.le_trans extends_.2 above)
  · intro varId below
    by_cases original : varId < q.nextTy
    · exact (bounded.targetImagesBounded varId original).mono extends_
    · rw [bounded.targetFixedAbove varId (Nat.le_of_not_lt original)]
      constructor
      · intro image mem
        have empty : (Ty.var varId).fcv = ([] : List CapVar) := rfl
        rw [empty] at mem
        nomatch mem
      · intro image mem
        have : image = varId := by
          simpa [Ty.ftv] using mem
        simpa [this]

/-- The identity substitution is bounded by every supply. -/
theorem Subst.boundedBy_id (q : InferenceBase.FreshSupply) :
    Subst.BoundedBy q Subst.id := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, ?_⟩
  · intro varId below image mem
    have : image = varId := by
      simpa [Subst.id, CapSubst.id, Cap.fcv] using mem
    simpa [this]
  · intro varId below
    constructor
    · intro image mem
      have empty : (Subst.id.target varId).fcv = [] := rfl
      rw [empty] at mem
      nomatch mem
    · intro image mem
      have : image = varId := by
        simpa [Subst.id, TySubst.id, Ty.ftv] using mem
      simpa [this]

/-- Applying a bounded substitution to a bounded capability is bounded. -/
theorem Subst.BoundedBy.applyCap {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) {capability : Cap}
    (capBounded : capability.BoundedBy q) :
    (capability.apply S.cap).BoundedBy q := by
  intro varId mem
  rw [Unification.Cap.fcv_apply] at mem
  simp only [List.mem_flatMap] at mem
  obtain ⟨original, originalMem, imageMem⟩ := mem
  exact bounded.capImagesBounded original (capBounded original originalMem)
    varId imageMem

/-- Applying a bounded substitution to a bounded type is bounded. -/
theorem Subst.BoundedBy.apply {q : InferenceBase.FreshSupply} {S : Subst}
    (bounded : S.BoundedBy q) {target : Ty}
    (targetBounded : target.BoundedBy q) :
    (S.apply target).BoundedBy q := by
  constructor
  · intro varId mem
    rcases Ty.mem_fcv_applyTarget _ S.target varId mem with own | image
    · rw [Ty.fcv_applyCapability] at own
      simp only [List.mem_flatMap] at own
      obtain ⟨original, originalMem, imageMem⟩ := own
      exact bounded.capImagesBounded original
        (targetBounded.caps original originalMem) varId imageMem
    · obtain ⟨tyVar, tyMem, imageMem⟩ := image
      rw [Ty.ftv_applyCapability] at tyMem
      exact (bounded.targetImagesBounded tyVar
        (targetBounded.targets tyVar tyMem)).caps varId imageMem
  · intro varId mem
    have mem' : varId ∈
        ((target.applyCapability S.cap).applyTarget S.target).ftv := mem
    rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability] at mem'
    simp only [List.mem_flatMap] at mem'
    obtain ⟨original, originalMem, imageMem⟩ := mem'
    exact (bounded.targetImagesBounded original
      (targetBounded.targets original originalMem)).targets varId imageMem

/-- Sequencing bounded substitutions is bounded. -/
theorem Subst.BoundedBy.seq {q : InferenceBase.FreshSupply}
    {delta S : Subst} (deltaBounded : delta.BoundedBy q)
    (bounded : S.BoundedBy q) : (Subst.seq delta S).BoundedBy q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro varId above
    show (S.cap varId).apply delta.cap = .var varId
    rw [bounded.capFixedAbove varId above]
    show delta.cap varId = .var varId
    exact deltaBounded.capFixedAbove varId above
  · intro varId below
    exact deltaBounded.applyCap (bounded.capImagesBounded varId below)
  · intro varId above
    show delta.apply (S.target varId) = .var varId
    rw [bounded.targetFixedAbove varId above]
    show (((Ty.var varId).applyCapability delta.cap).applyTarget
      delta.target) = .var varId
    exact deltaBounded.targetFixedAbove varId above
  · intro varId below
    exact deltaBounded.apply (bounded.targetImagesBounded varId below)

/-! ### Boundedness of exact solve deltas -/

/-- Split membership in the capability variables of a list. -/
theorem Cap.mem_fcvList_split :
    ∀ {caps : List Cap} {varId : CapVar}, varId ∈ Cap.fcvList caps →
      ∃ capability, capability ∈ caps ∧ varId ∈ capability.fcv
  | [], _, mem => nomatch mem
  | cap :: caps, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨cap, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- Split membership in the capability variables of a type list. -/
theorem Ty.mem_fcvList_split :
    ∀ {types : List Ty} {varId : CapVar}, varId ∈ Ty.fcvList types →
      ∃ target, target ∈ types ∧ varId ∈ target.fcv
  | [], _, mem => nomatch mem
  | τ :: types, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨τ, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Ty.mem_fcvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- Split membership in the target variables of a type list. -/
theorem Ty.mem_ftvList_split :
    ∀ {types : List Ty} {varId : TypePM.TyVar}, varId ∈ Ty.ftvList types →
      ∃ target, target ∈ types ∧ varId ∈ target.ftv
  | [], _, mem => nomatch mem
  | τ :: types, varId, mem => by
      rcases List.mem_append.mp mem with here | there
      · exact ⟨τ, by simp, here⟩
      · obtain ⟨inner, innerMem, hMem⟩ := Ty.mem_ftvList_split there
        exact ⟨inner, by simp [innerMem], hMem⟩

/-- Components of a bounded matcher type are bounded. -/
theorem Ty.BoundedBy.matcherParts {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (bounded : (Ty.matcher capability target).BoundedBy q) :
    capability.BoundedBy q ∧ target.BoundedBy q := by
  refine ⟨fun w hw => bounded.caps w ?_,
    ⟨fun w hw => bounded.caps w ?_, fun w hw => bounded.targets w ?_⟩⟩
  · exact List.mem_append.mpr (Or.inl hw)
  · exact List.mem_append.mpr (Or.inr hw)
  · exact hw

/-- Components of a bounded slot type are bounded. -/
theorem Ty.BoundedBy.slotParts {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (bounded : (Ty.slot capability target).BoundedBy q) :
    capability.BoundedBy q ∧ target.BoundedBy q := by
  refine ⟨fun w hw => bounded.caps w ?_,
    ⟨fun w hw => bounded.caps w ?_, fun w hw => bounded.targets w ?_⟩⟩
  · exact List.mem_append.mpr (Or.inl hw)
  · exact List.mem_append.mpr (Or.inr hw)
  · exact hw

/-- A product of bounded types is bounded. -/
theorem Ty.BoundedBy.prodOfForall {q : InferenceBase.FreshSupply}
    {components : List Ty}
    (bounded : ∀ target ∈ components, Ty.BoundedBy q target) :
    (Ty.prod components).BoundedBy q := by
  constructor
  · intro w hw
    obtain ⟨τ, τMem, hMem⟩ := Ty.mem_fcvList_split hw
    exact (bounded τ τMem).caps w hMem
  · intro w hw
    obtain ⟨τ, τMem, hMem⟩ := Ty.mem_ftvList_split hw
    exact (bounded τ τMem).targets w hMem

/-- A member of a bounded product type is bounded. -/
theorem Ty.BoundedBy.of_mem_prod {q : InferenceBase.FreshSupply}
    {components : List Ty}
    (bounded : (Ty.prod components).BoundedBy q) {target : Ty}
    (mem : target ∈ components) : target.BoundedBy q :=
  ⟨fun w hw => bounded.caps w (Ty.mem_fcvList_of_mem mem hw),
    fun w hw => bounded.targets w (Ty.mem_ftvList_of_mem mem hw)⟩

/-- A product of bounded capabilities is bounded. -/
theorem Cap.BoundedBy.prodOfForall {q : InferenceBase.FreshSupply}
    {components : List Cap}
    (bounded : ∀ capability ∈ components, Cap.BoundedBy q capability) :
    (Cap.prod components).BoundedBy q := by
  intro w hw
  obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split hw
  exact bounded inner innerMem w hMem

/-- The exactness half of delta boundedness: an exact capability solution
of a bounded constraint is the identity at and above the bound. -/
theorem ExactCapMGU.fixedAbove {left right : Cap} {subst : CapSubst}
    {q : InferenceBase.FreshSupply} (exact : ExactCapMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q)
    (varId : CapVar) (above : q.nextCap ≤ varId.id) :
    subst varId = .var varId := by
  refine exact.2.1 varId ?_
  intro mem
  rcases List.mem_append.mp mem with here | there
  · have := leftBounded varId here
    omega
  · have := rightBounded varId there
    omega

/-- The exactness half of delta boundedness for target solutions. -/
theorem ExactTargetMGU.fixedAbove {left right : Ty} {subst : TySubst}
    {q : InferenceBase.FreshSupply} (exact : ExactTargetMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q)
    (varId : TypePM.TyVar) (above : q.nextTy ≤ varId) :
    subst varId = .var varId := by
  refine exact.2.1 varId ?_
  intro mem
  rcases List.mem_append.mp mem with here | there
  · exact Nat.lt_irrefl _
      (Nat.lt_of_lt_of_le (leftBounded.targets varId here) above)
  · exact Nat.lt_irrefl _
      (Nat.lt_of_lt_of_le (rightBounded.targets varId there) above)

/-- The exactness half of delta boundedness for paired solutions, in both
sorts. -/
theorem ExactPairedMGU.fixedAbove {left right : Ty} {subst : Subst}
    {q : InferenceBase.FreshSupply} (exact : ExactPairedMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    (∀ varId : CapVar, q.nextCap ≤ varId.id →
      subst.cap varId = .var varId) ∧
    (∀ varId : TypePM.TyVar, q.nextTy ≤ varId →
      subst.target varId = .var varId) := by
  constructor
  · intro varId above
    refine exact.2.1 varId ?_
    intro mem
    rcases List.mem_append.mp mem with here | there
    · have := leftBounded.caps varId here
      omega
    · have := rightBounded.caps varId there
      omega
  · intro varId above
    refine exact.2.2.1 varId ?_
    intro mem
    rcases List.mem_append.mp mem with here | there
    · exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (leftBounded.targets varId here) above)
    · exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (rightBounded.targets varId there) above)

/-- An exact capability solution of a bounded constraint, paired with the
identity target action, is a bounded substitution. -/
theorem ExactCapMGU.boundedBy_pair {left right : Cap} {subst : CapSubst}
    {q : InferenceBase.FreshSupply} (exact : ExactCapMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    Subst.BoundedBy q ⟨subst, TySubst.id⟩ := by
  refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
  · intro varId above
    refine exact.2.1 varId ?_
    intro mem
    rcases List.mem_append.mp mem with here | there
    · have := leftBounded varId here
      omega
    · have := rightBounded varId there
      omega
  · intro varId below image imageMem
    have imageMem' : image ∈ (subst varId).fcv := imageMem
    by_cases inConstraint : varId ∈ left.fcv ++ right.fcv
    · have := exact.2.2.1 varId inConstraint image imageMem'
      rcases List.mem_append.mp this with h | h
      · exact leftBounded image h
      · exact rightBounded image h
    · rw [exact.2.1 varId inConstraint] at imageMem'
      have h : image = varId := by simpa [Cap.fcv] using imageMem'
      simpa [h] using below
  · intro varId below
    constructor
    · intro image imageMem
      have empty : (TySubst.id varId).fcv = ([] : List CapVar) := rfl
      rw [show ((⟨subst, TySubst.id⟩ : Subst).target varId).fcv =
        ([] : List CapVar) from empty] at imageMem
      nomatch imageMem
    · intro image imageMem
      have h : image = varId := by
        simpa [TySubst.id, Ty.ftv] using
          (show image ∈ (TySubst.id varId).ftv from imageMem)
      simpa [h] using below

/-- An exact target solution of a bounded constraint is bounded in the
target component; paired with the identity capability action it is a
bounded substitution. -/
theorem ExactTargetMGU.boundedBy_pair {left right : Ty} {subst : TySubst}
    {q : InferenceBase.FreshSupply} (exact : ExactTargetMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    Subst.BoundedBy q ⟨CapSubst.id, subst⟩ := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro varId below image imageMem
    have h : image = varId := by
      simpa [CapSubst.id, Cap.fcv] using
        (show image ∈ (CapSubst.id varId).fcv from imageMem)
    simpa [h] using below
  · intro varId above
    refine exact.2.1 varId ?_
    intro mem
    rcases List.mem_append.mp mem with here | there
    · exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (leftBounded.targets varId here) above)
    · exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (rightBounded.targets varId there) above)
  · intro varId below
    by_cases inConstraint : varId ∈ left.ftv ++ right.ftv
    · constructor
      · intro image imageMem
        have := exact.2.2.2.1 varId inConstraint image
          (show image ∈ (subst varId).fcv from imageMem)
        rcases List.mem_append.mp this with h | h
        · exact leftBounded.caps image h
        · exact rightBounded.caps image h
      · intro image imageMem
        have := exact.2.2.1 varId inConstraint image
          (show image ∈ (subst varId).ftv from imageMem)
        rcases List.mem_append.mp this with h | h
        · exact leftBounded.targets image h
        · exact rightBounded.targets image h
    · have fixed : subst varId = .var varId := exact.2.1 varId inConstraint
      constructor
      · intro image imageMem
        have imageMem' : image ∈ (subst varId).fcv := imageMem
        rw [fixed] at imageMem'
        have empty : (Ty.var varId).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'
      · intro image imageMem
        have imageMem' : image ∈ (subst varId).ftv := imageMem
        rw [fixed] at imageMem'
        have h : image = varId := by simpa [Ty.ftv] using imageMem'
        simpa [h] using below

/-- An exact paired solution of a bounded constraint is a bounded
substitution. -/
theorem ExactPairedMGU.boundedBy {left right : Ty} {subst : Subst}
    {q : InferenceBase.FreshSupply} (exact : ExactPairedMGU left right subst)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    subst.BoundedBy q := by
  obtain ⟨capAbove, targetAbove⟩ :=
    exact.fixedAbove leftBounded rightBounded
  refine ⟨capAbove, ?_, targetAbove, ?_⟩
  · intro varId below image imageMem
    by_cases inConstraint : varId ∈ left.fcv ++ right.fcv
    · have := exact.2.2.2.1 varId inConstraint image imageMem
      rcases List.mem_append.mp this with h | h
      · exact leftBounded.caps image h
      · exact rightBounded.caps image h
    · have imageMem' : image ∈ (subst.cap varId).fcv := imageMem
      rw [exact.2.1 varId inConstraint] at imageMem'
      have h : image = varId := by simpa [Cap.fcv] using imageMem'
      simpa [h] using below
  · intro varId below
    by_cases inConstraint : varId ∈ left.ftv ++ right.ftv
    · constructor
      · intro image imageMem
        have := exact.2.2.2.2.2.1 varId inConstraint image imageMem
        rcases List.mem_append.mp this with h | h
        · exact leftBounded.caps image h
        · exact rightBounded.caps image h
      · intro image imageMem
        have := exact.2.2.2.2.1 varId inConstraint image imageMem
        rcases List.mem_append.mp this with h | h
        · exact leftBounded.targets image h
        · exact rightBounded.targets image h
    · have fixed : subst.target varId = .var varId :=
        exact.2.2.1 varId inConstraint
      constructor
      · intro image imageMem
        have imageMem' : image ∈ (subst.target varId).fcv := imageMem
        rw [fixed] at imageMem'
        have empty : (Ty.var varId).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem'
        nomatch imageMem'
      · intro image imageMem
        have imageMem' : image ∈ (subst.target varId).ftv := imageMem
        rw [fixed] at imageMem'
        have h : image = varId := by simpa [Ty.ftv] using imageMem'
        simpa [h] using below

/-- Capability boundedness is preserved by a bounded capability action. -/
theorem Subst.BoundedBy.applyCapabilityTy {q : InferenceBase.FreshSupply}
    {S : Subst} (bounded : S.BoundedBy q) {target : Ty}
    (targetBounded : target.BoundedBy q) :
    (target.applyCapability S.cap).BoundedBy q := by
  constructor
  · intro w hw
    rw [Ty.fcv_applyCapability] at hw
    simp only [List.mem_flatMap] at hw
    obtain ⟨original, originalMem, imageMem⟩ := hw
    exact bounded.capImagesBounded original
      (targetBounded.caps original originalMem) w imageMem
  · intro w hw
    rw [Ty.ftv_applyCapability] at hw
    exact targetBounded.targets w hw


/-! ### Boundedness of the one-way solution and the checking cut -/

mutual

/-- Bindings produced by one-way matching map variables to producer
subterms: every image variable lies within the ambient list containing the
producer's variables. -/
theorem matchCapAcc_imagesWithin (vars : List CapVar) :
    ∀ (producer consumer : Cap) (acc bindings : CapMatch.Bindings),
      CapMatch.matchCapAcc producer consumer acc = some bindings →
      (∀ image ∈ producer.fcv, image ∈ vars) →
      (∀ varId capability, CapMatch.Bindings.lookup varId acc =
        some capability → ∀ image ∈ capability.fcv, image ∈ vars) →
      ∀ varId capability, CapMatch.Bindings.lookup varId bindings =
        some capability → ∀ image ∈ capability.fcv, image ∈ vars
  | producer, .any, acc, bindings, run, _, accWithin => by
      simp only [CapMatch.matchCapAcc] at run
      cases run
      exact accWithin
  | producer, .var varId, acc, bindings, run, pWithin, accWithin => by
      simp only [CapMatch.matchCapAcc] at run
      unfold CapMatch.bindVar at run
      split at run
      · cases run
        intro v capability lookupEq
        rw [show CapMatch.Bindings.lookup v ((varId, producer) :: acc) =
          (if v = varId then some producer
            else CapMatch.Bindings.lookup v acc) from rfl] at lookupEq
        by_cases hv : v = varId
        · rw [if_pos hv] at lookupEq
          cases lookupEq
          exact pWithin
        · rw [if_neg hv] at lookupEq
          exact accWithin v capability lookupEq
      · split at run
        · cases run
          exact accWithin
        · cases run
  | .skolem producerId, .skolem consumerId, acc, bindings, run, _,
      accWithin => by
      simp only [CapMatch.matchCapAcc] at run
      split at run
      · cases run
        exact accWithin
      · cases run
  | .con producerName producerChildren, .con consumerName consumerChildren,
      acc, bindings, run, pWithin, accWithin => by
      simp only [CapMatch.matchCapAcc] at run
      split at run
      · exact matchCapListAcc_imagesWithin vars producerChildren
          consumerChildren acc bindings run pWithin accWithin
      · cases run
  | .prod producerComponents, .prod consumerComponents, acc, bindings, run,
      pWithin, accWithin => by
      simp only [CapMatch.matchCapAcc] at run
      exact matchCapListAcc_imagesWithin vars producerComponents
        consumerComponents acc bindings run pWithin accWithin
  | .any, .skolem _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .any, .con _ _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .any, .prod _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .var _, .skolem _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .var _, .con _ _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .var _, .prod _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .skolem _, .con _ _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .skolem _, .prod _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .con _ _, .skolem _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .con _ _, .prod _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .prod _, .skolem _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run
  | .prod _, .con _ _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapAcc] at run
      nomatch run

/-- List form of `matchCapAcc_imagesWithin`. -/
theorem matchCapListAcc_imagesWithin (vars : List CapVar) :
    ∀ (producers consumers : List Cap) (acc bindings : CapMatch.Bindings),
      CapMatch.matchCapListAcc producers consumers acc = some bindings →
      (∀ image ∈ Cap.fcvList producers, image ∈ vars) →
      (∀ varId capability, CapMatch.Bindings.lookup varId acc =
        some capability → ∀ image ∈ capability.fcv, image ∈ vars) →
      ∀ varId capability, CapMatch.Bindings.lookup varId bindings =
        some capability → ∀ image ∈ capability.fcv, image ∈ vars
  | [], [], acc, bindings, run, _, accWithin => by
      simp only [CapMatch.matchCapListAcc] at run
      cases run
      exact accWithin
  | producer :: producers, consumer :: consumers, acc, bindings, run,
      pWithin, accWithin => by
      simp only [CapMatch.matchCapListAcc] at run
      split at run
      next updated headRun =>
        exact matchCapListAcc_imagesWithin vars producers consumers updated
          bindings run
          (fun image mem => pWithin image (List.mem_append.mpr (Or.inr mem)))
          (matchCapAcc_imagesWithin vars producer consumer acc updated
            headRun
            (fun image mem => pWithin image (List.mem_append.mpr (Or.inl mem)))
            accWithin)
      next => cases run
  | [], _ :: _, _, _, run, _, _ => by
      simp only [CapMatch.matchCapListAcc] at run
      nomatch run
  | _ :: _, [], _, _, run, _, _ => by
      simp only [CapMatch.matchCapListAcc] at run
      nomatch run

end

/-- One-way match bindings map consumer variables to producer subterms. -/
theorem matchCap_imagesWithin {producer consumer : Cap}
    {bindings : CapMatch.Bindings}
    (run : CapMatch.matchCap producer consumer = some bindings) :
    ∀ varId capability, CapMatch.Bindings.lookup varId bindings =
      some capability → ∀ image ∈ capability.fcv, image ∈ producer.fcv := by
  obtain ⟨raw, -⟩ :=
    (CapMatch.matchCap_eq_some_iff producer consumer bindings).mp run
  exact matchCapAcc_imagesWithin producer.fcv producer consumer [] bindings
    raw (fun _ mem => mem) (fun v c h => nomatch h)

/-- The one-way producer-to-slot solution of a bounded constraint is a
bounded substitution. -/
theorem OneWayDelta.boundedBy {producerCap : Cap} {producerTarget : Ty}
    {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst}
    {q : InferenceBase.FreshSupply}
    (oneWay : OneWayDelta producerCap producerTarget consumerCap
      consumerTarget delta)
    (producerCapBounded : producerCap.BoundedBy q)
    (producerTargetBounded : producerTarget.BoundedBy q)
    (consumerCapBounded : consumerCap.BoundedBy q)
    (consumerTargetBounded : consumerTarget.BoundedBy q) :
    delta.BoundedBy q := by
  obtain ⟨bindings, run, capEq, targetExact⟩ := oneWay
  have capAbove : ∀ varId : CapVar, q.nextCap ≤ varId.id →
      delta.cap varId = .var varId := by
    intro v above
    rw [capEq]
    show (if v ∈ consumerCap.fcv then CapMatch.Bindings.toSubst bindings v
      else .var v) = .var v
    rw [if_neg (fun mem => Nat.lt_irrefl _
      (Nat.lt_of_lt_of_le (consumerCapBounded v mem) above))]
  have capImages : ∀ varId : CapVar, varId.id < q.nextCap →
      Cap.BoundedBy q (delta.cap varId) := by
    intro v below image imageMem
    have imageMem' : image ∈ (delta.cap v).fcv := imageMem
    rw [capEq] at imageMem'
    by_cases hmem : v ∈ consumerCap.fcv
    · rw [show CapMatch.Bindings.toSubstWithin consumerCap.fcv bindings v =
        CapMatch.Bindings.toSubst bindings v from if_pos hmem] at imageMem'
      cases hlook : CapMatch.Bindings.lookup v bindings with
      | none =>
          rw [show CapMatch.Bindings.toSubst bindings v = .var v from by
            unfold CapMatch.Bindings.toSubst
            rw [hlook]] at imageMem'
          have h : image = v := by simpa [Cap.fcv] using imageMem'
          simpa [h] using below
      | some capability =>
          rw [show CapMatch.Bindings.toSubst bindings v = capability from by
            unfold CapMatch.Bindings.toSubst
            rw [hlook]] at imageMem'
          exact producerCapBounded image
            (matchCap_imagesWithin run v capability hlook image imageMem')
    · rw [show CapMatch.Bindings.toSubstWithin consumerCap.fcv bindings v =
        .var v from if_neg hmem] at imageMem'
      have h : image = v := by simpa [Cap.fcv] using imageMem'
      simpa [h] using below
  have capPairBounded : Subst.BoundedBy q ⟨delta.cap, TySubst.id⟩ := by
    refine ⟨capAbove, capImages, fun _ _ => rfl, ?_⟩
    intro varId below
    constructor
    · intro image imageMem
      have empty : ((⟨delta.cap, TySubst.id⟩ : Subst).target varId).fcv =
        ([] : List CapVar) := rfl
      rw [empty] at imageMem
      nomatch imageMem
    · intro image imageMem
      have h : image = varId := by
        simpa [TySubst.id, Ty.ftv] using
          (show image ∈ (TySubst.id varId).ftv from imageMem)
      simpa [h] using below
  have targetPairBounded : Subst.BoundedBy q ⟨CapSubst.id, delta.target⟩ :=
    targetExact.boundedBy_pair
      (capPairBounded.applyCapabilityTy producerTargetBounded)
      (capPairBounded.applyCapabilityTy consumerTargetBounded)
  exact ⟨capAbove, capImages, targetPairBounded.targetFixedAbove,
    targetPairBounded.targetImagesBounded⟩

/-- Ordinary equality alignment preserves boundedness of the prevailing
substitution. -/
theorem DDAlignTypes.boundedBy {S : Subst} {left right : Ty} {S' : Subst}
    {q : InferenceBase.FreshSupply}
    (aligned : DDAlignTypes S left right S') (Sb : S.BoundedBy q)
    (leftBounded : left.BoundedBy q) (rightBounded : right.BoundedBy q) :
    S'.BoundedBy q := by
  cases aligned with
  | matcherPair hleft hright capMGU targetMGU =>
      have resolvedLeft := Sb.apply leftBounded
      have resolvedRight := Sb.apply rightBounded
      rw [hleft] at resolvedLeft
      rw [hright] at resolvedRight
      obtain ⟨lcB, ltB⟩ := resolvedLeft.matcherParts
      obtain ⟨rcB, rtB⟩ := resolvedRight.matcherParts
      have capPairB := capMGU.boundedBy_pair lcB rcB
      have targetB := targetMGU.boundedBy
        (capPairB.applyCapabilityTy ltB) (capPairB.applyCapabilityTy rtB)
      exact targetB.seq (capPairB.seq Sb)
  | slotPair hleft hright capMGU targetMGU =>
      have resolvedLeft := Sb.apply leftBounded
      have resolvedRight := Sb.apply rightBounded
      rw [hleft] at resolvedLeft
      rw [hright] at resolvedRight
      obtain ⟨lcB, ltB⟩ := resolvedLeft.slotParts
      obtain ⟨rcB, rtB⟩ := resolvedRight.slotParts
      have capPairB := capMGU.boundedBy_pair lcB rcB
      have targetB := targetMGU.boundedBy
        (capPairB.applyCapabilityTy ltB) (capPairB.applyCapabilityTy rtB)
      exact targetB.seq (capPairB.seq Sb)
  | ordinary hclass mgu =>
      exact (mgu.boundedBy (Sb.apply leftBounded)
        (Sb.apply rightBounded)).seq Sb

/-- Every checking cut preserves boundedness of the prevailing
substitution. -/
theorem DDAlign.boundedBy {S : Subst} {raw expected : Ty} {S' : Subst}
    {q : InferenceBase.FreshSupply} (aligned : DDAlign S raw expected S')
    (Sb : S.BoundedBy q) (rawBounded : raw.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) : S'.BoundedBy q := by
  cases aligned with
  | productMatcherLift hduals hslot oneWay =>
      rename_i duals consumerCap consumerTarget delta
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [Inference.productMatcherDuals?_sound hduals] at resolvedRaw
      rw [hslot] at resolvedExpected
      obtain ⟨ccB, ctB⟩ := resolvedExpected.slotParts
      have dualsB : ∀ dual ∈ duals,
          Cap.BoundedBy q dual.cap ∧ Ty.BoundedBy q dual.target := by
        intro dual dualMem
        have memProd : (Ty.matcher dual.cap dual.target) ∈
            duals.map (fun dual => Ty.matcher dual.cap dual.target) :=
          List.mem_map.mpr ⟨dual, dualMem, rfl⟩
        exact (resolvedRaw.of_mem_prod memProd).matcherParts
      have producerCapB : Cap.BoundedBy q (.prod (duals.map Dual.cap)) := by
        apply Cap.BoundedBy.prodOfForall
        intro c cMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp cMem
        exact (dualsB dual dualMem).1
      have producerTargetB :
          Ty.BoundedBy q (.prod (duals.map Dual.target)) := by
        apply Ty.BoundedBy.prodOfForall
        intro τ τMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp τMem
        exact (dualsB dual dualMem).2
      exact (oneWay.boundedBy producerCapB producerTargetB ccB ctB).seq Sb
  | slotTupleLift hclass hduals hslot capMGU targetMGU =>
      rename_i duals consumerCap consumerTarget capDelta targetDelta
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [Inference.productSlotDuals?_sound hduals] at resolvedRaw
      rw [hslot] at resolvedExpected
      obtain ⟨ccB, ctB⟩ := resolvedExpected.slotParts
      have dualsB : ∀ dual ∈ duals,
          Cap.BoundedBy q dual.cap ∧ Ty.BoundedBy q dual.target := by
        intro dual dualMem
        have memProd : (Ty.slot dual.cap dual.target) ∈
            duals.map (fun dual => Ty.slot dual.cap dual.target) :=
          List.mem_map.mpr ⟨dual, dualMem, rfl⟩
        exact (resolvedRaw.of_mem_prod memProd).slotParts
      have producerCapB : Cap.BoundedBy q (.prod (duals.map Dual.cap)) := by
        apply Cap.BoundedBy.prodOfForall
        intro c cMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp cMem
        exact (dualsB dual dualMem).1
      have producerTargetB :
          Ty.BoundedBy q (.prod (duals.map Dual.target)) := by
        apply Ty.BoundedBy.prodOfForall
        intro τ τMem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp τMem
        exact (dualsB dual dualMem).2
      have capPairB := capMGU.boundedBy_pair producerCapB ccB
      have targetB := targetMGU.boundedBy
        (capPairB.applyCapabilityTy producerTargetB)
        (capPairB.applyCapabilityTy ctB)
      exact targetB.seq (capPairB.seq Sb)
  | matcherToSlot hraw hslot oneWay =>
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [hraw] at resolvedRaw
      rw [hslot] at resolvedExpected
      obtain ⟨pcB, ptB⟩ := resolvedRaw.matcherParts
      obtain ⟨ccB, ctB⟩ := resolvedExpected.slotParts
      exact (oneWay.boundedBy pcB ptB ccB ctB).seq Sb
  | slotToSlot hraw hslot capMGU targetMGU =>
      have resolvedRaw := Sb.apply rawBounded
      have resolvedExpected := Sb.apply expectedBounded
      rw [hraw] at resolvedRaw
      rw [hslot] at resolvedExpected
      obtain ⟨scB, stB⟩ := resolvedRaw.slotParts
      obtain ⟨rcB, rtB⟩ := resolvedExpected.slotParts
      have capPairB := capMGU.boundedBy_pair scB rcB
      have targetB := targetMGU.boundedBy
        (capPairB.applyCapabilityTy stB) (capPairB.applyCapabilityTy rtB)
      exact targetB.seq (capPairB.seq Sb)
  | ordinary hclass aligned =>
      exact aligned.boundedBy Sb rawBounded expectedBounded


/-- Both components of a dual lie below the supply's counters. -/
def Dual.BoundedBy (q : InferenceBase.FreshSupply) (dual : Dual) : Prop :=
  dual.cap.BoundedBy q ∧ dual.target.BoundedBy q

/-- Dual alignment preserves boundedness of the prevailing substitution. -/
theorem DDAlignDual.boundedBy {S : Subst} {left right : Dual} {S' : Subst}
    {q : InferenceBase.FreshSupply} (aligned : DDAlignDual S left right S')
    (Sb : S.BoundedBy q) (leftBounded : left.BoundedBy q)
    (rightBounded : right.BoundedBy q) : S'.BoundedBy q := by
  cases aligned with
  | mk capMGU typesAligned =>
      have capPairB := capMGU.boundedBy_pair
        (Sb.applyCap leftBounded.1) (Sb.applyCap rightBounded.1)
      exact typesAligned.boundedBy (capPairB.seq Sb) leftBounded.2
        rightBounded.2

/-- Dual-list alignment preserves boundedness. -/
theorem DDAlignDualList.boundedBy {S : Subst} {lefts rights : List Dual}
    {S' : Subst} {q : InferenceBase.FreshSupply} :
    DDAlignDualList S lefts rights S' → S.BoundedBy q →
    (∀ dual ∈ lefts, Dual.BoundedBy q dual) →
    (∀ dual ∈ rights, Dual.BoundedBy q dual) → S'.BoundedBy q
  | .nil, Sb, _, _ => Sb
  | .cons head tail, Sb, leftsB, rightsB =>
      tail.boundedBy
        (head.boundedBy Sb (leftsB _ (by simp)) (rightsB _ (by simp)))
        (fun dual mem => leftsB dual (by simp [mem]))
        (fun dual mem => rightsB dual (by simp [mem]))

/-- Target-list alignment preserves boundedness. -/
theorem DDAlignTargetList.boundedBy {S : Subst} {duals : List Dual}
    {expecteds : List Ty} {S' : Subst} {q : InferenceBase.FreshSupply} :
    DDAlignTargetList S duals expecteds S' → S.BoundedBy q →
    (∀ dual ∈ duals, Dual.BoundedBy q dual) →
    (∀ expected ∈ expecteds, Ty.BoundedBy q expected) → S'.BoundedBy q
  | .nil, Sb, _, _ => Sb
  | .cons head tail, Sb, dualsB, expectedsB =>
      tail.boundedBy
        (head.boundedBy Sb (dualsB _ (by simp)).2 (expectedsB _ (by simp)))
        (fun dual mem => dualsB dual (by simp [mem]))
        (fun expected mem => expectedsB expected (by simp [mem]))

/-- Binding alignment preserves boundedness. -/
theorem DDAlignBindings.boundedBy {S : Subst} {lefts rights : MonoCtx}
    {S' : Subst} {q : InferenceBase.FreshSupply} :
    DDAlignBindings S lefts rights S' → S.BoundedBy q →
    (∀ entry ∈ lefts, Ty.BoundedBy q entry.2) →
    (∀ entry ∈ rights, Ty.BoundedBy q entry.2) → S'.BoundedBy q
  | .nil, Sb, _, _ => Sb
  | .cons _ head tail, Sb, leftsB, rightsB =>
      tail.boundedBy
        (head.boundedBy Sb (leftsB _ (by simp)) (rightsB _ (by simp)))
        (fun entry mem => leftsB entry (by simp [mem]))
        (fun entry mem => rightsB entry (by simp [mem]))

/-- Constructor-capability demand solving preserves boundedness. -/
theorem DDAlignCtorCaps.boundedBy {S : Subst} {children : List Cap}
    {demands : List (Option Cap)} {S' : Subst}
    {q : InferenceBase.FreshSupply} :
    DDAlignCtorCaps S children demands S' → S.BoundedBy q →
    (∀ child ∈ children, Cap.BoundedBy q child) →
    (∀ demand ∈ demands, ∀ capability, demand = some capability →
      Cap.BoundedBy q capability) → S'.BoundedBy q
  | .nil, Sb, _, _ => Sb
  | .skip rest, Sb, childrenB, demandsB =>
      rest.boundedBy Sb (fun child mem => childrenB child (by simp [mem]))
        (fun demand mem => demandsB demand (by simp [mem]))
  | .solve capMGU rest, Sb, childrenB, demandsB =>
      rest.boundedBy
        ((capMGU.boundedBy_pair
          (Sb.applyCap (childrenB _ (by simp)))
          (Sb.applyCap (demandsB _ (by simp) _ rfl))).seq Sb)
        (fun child mem => childrenB child (by simp [mem]))
        (fun demand mem => demandsB demand (by simp [mem]))

/-! ### Boundedness of the pattern-layer supply twins

Every supply twin returns output bounded by its successor supply.  The two
signature-fed twins consume the flexible-variable conservation lemmas of
the projection pipeline: freshening only allocates at or above the input
counter, embeds already-bounded evidence leaves unchanged, and the
recursive-matcher skeleton is variable-free.
-/

/-- Constructor form of `Cap.BoundedBy.prodOfForall`. -/
theorem Cap.BoundedBy.conOfForall {q : InferenceBase.FreshSupply}
    {name : String} {components : List Cap}
    (bounded : ∀ capability ∈ components, Cap.BoundedBy q capability) :
    (Cap.con name components).BoundedBy q := by
  intro w hw
  obtain ⟨inner, innerMem, hMem⟩ := Cap.mem_fcvList_split hw
  exact bounded inner innerMem w hMem

/-- Freshly allocated targets are bounded by the successor supply. -/
theorem freshTargetsSupply_boundedBy :
    ∀ (count : Nat) (q : InferenceBase.FreshSupply),
      ∀ target ∈ (freshTargetsSupply count q).1,
        Ty.BoundedBy (freshTargetsSupply count q).2 target
  | 0, q => by
      intro target mem
      exact nomatch mem
  | count + 1, q => by
      intro target mem
      simp only [freshTargetsSupply] at mem ⊢
      rcases List.mem_cons.mp mem with hhead | htail
      · subst hhead
        refine ⟨?_, ?_⟩
        · intro varId varMem
          simp only [Ty.fcv] at varMem
          exact nomatch varMem
        · intro varId varMem
          simp only [Ty.ftv, List.mem_singleton] at varMem
          subst varMem
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            (SupplyExtends.freshTargets count
              { q with nextTy := q.nextTy + 1 }).2
      · exact freshTargetsSupply_boundedBy count _ target htail

mutual

/-- Freshening bounded skeleton evidence yields a bounded capability. -/
theorem freshenSkeletonSupply_boundedBy
    {observable : Shape.Observability} :
    ∀ {evidence : Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capability : Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonSupply observable evidence q =
        some (capability, q') →
      (∀ varId ∈ evidence.fcv, varId.id < q.nextCap) →
      capability.BoundedBy q'
  | .unseen, q, capability, q', h, bounded => by
      simp only [freshenSkeletonSupply] at h
      cases h
      intro varId mem
      simp only [Cap.fcv, List.mem_singleton] at mem
      subst mem
      exact Nat.lt_succ_self _
  | .known leaf, q, capability, q', h, bounded => by
      simp only [freshenSkeletonSupply] at h
      cases h
      intro varId mem
      rw [Shape.Leaf.fcv_toCap] at mem
      exact bounded varId mem
  | .con name children, q, capability, q', h, bounded => by
      cases hobs : observable name with
      | none => simp [freshenSkeletonSupply, hobs] at h
      | some mask =>
          cases hmasked : freshenSkeletonMaskedSupply observable mask
              children q with
          | none => simp [freshenSkeletonSupply, hobs, hmasked] at h
          | some result =>
              obtain ⟨capabilities, q₁⟩ := result
              simp only [freshenSkeletonSupply, hobs, hmasked] at h
              cases h
              exact Cap.BoundedBy.conOfForall
                (freshenSkeletonMaskedSupply_boundedBy hmasked bounded)
  | .prod components, q, capability, q', h, bounded => by
      cases hlist : freshenSkeletonListSupply observable components q with
      | none => simp [freshenSkeletonSupply, hlist] at h
      | some result =>
          obtain ⟨capabilities, q₁⟩ := result
          simp only [freshenSkeletonSupply, hlist] at h
          cases h
          exact Cap.BoundedBy.prodOfForall
            (freshenSkeletonListSupply_boundedBy hlist bounded)

/-- List form of `freshenSkeletonSupply_boundedBy`. -/
theorem freshenSkeletonListSupply_boundedBy
    {observable : Shape.Observability} :
    ∀ {evidences : List Shape.Evidence} {q : InferenceBase.FreshSupply}
      {capabilities : List Cap} {q' : InferenceBase.FreshSupply},
      freshenSkeletonListSupply observable evidences q =
        some (capabilities, q') →
      (∀ varId ∈ Shape.Evidence.fcvList evidences,
        varId.id < q.nextCap) →
      ∀ capability ∈ capabilities, capability.BoundedBy q'
  | [], q, capabilities, q', h, bounded => by
      simp only [freshenSkeletonListSupply] at h
      cases h
      intro capability mem
      exact nomatch mem
  | evidence :: rest, q, capabilities, q', h, bounded => by
      cases hhead : freshenSkeletonSupply observable evidence q with
      | none => simp [freshenSkeletonListSupply, hhead] at h
      | some headResult =>
          obtain ⟨head, q₁⟩ := headResult
          cases htail : freshenSkeletonListSupply observable rest q₁ with
          | none => simp [freshenSkeletonListSupply, hhead, htail] at h
          | some tailResult =>
              obtain ⟨tail, q₂⟩ := tailResult
              simp only [freshenSkeletonListSupply, hhead, htail] at h
              cases h
              have boundedHead : ∀ varId ∈ evidence.fcv,
                  varId.id < q.nextCap := fun varId varMem =>
                bounded varId (by
                  simp only [Shape.Evidence.fcvList, List.mem_append]
                  exact Or.inl varMem)
              have boundedTail : ∀ varId ∈ Shape.Evidence.fcvList rest,
                  varId.id < q₁.nextCap := fun varId varMem =>
                Nat.lt_of_lt_of_le
                  (bounded varId (by
                    simp only [Shape.Evidence.fcvList, List.mem_append]
                    exact Or.inr varMem))
                  (SupplyExtends.freshenSkeleton hhead).1
              intro capability mem
              rcases List.mem_cons.mp mem with hh | ht
              · subst hh
                exact (freshenSkeletonSupply_boundedBy hhead
                    boundedHead).mono
                  (SupplyExtends.freshenSkeletonList htail)
              · exact freshenSkeletonListSupply_boundedBy htail boundedTail
                  capability ht

/-- Masked form of `freshenSkeletonSupply_boundedBy`. -/
theorem freshenSkeletonMaskedSupply_boundedBy
    {observable : Shape.Observability} :
    ∀ {mask : List Bool} {evidences : List Shape.Evidence}
      {q : InferenceBase.FreshSupply} {capabilities : List Cap}
      {q' : InferenceBase.FreshSupply},
      freshenSkeletonMaskedSupply observable mask evidences q =
        some (capabilities, q') →
      (∀ varId ∈ Shape.Evidence.fcvList evidences,
        varId.id < q.nextCap) →
      ∀ capability ∈ capabilities, capability.BoundedBy q'
  | [], [], q, capabilities, q', h, bounded => by
      simp only [freshenSkeletonMaskedSupply] at h
      cases h
      intro capability mem
      exact nomatch mem
  | isObservable :: mask, evidence :: rest, q, capabilities, q', h,
      bounded => by
      have boundedHead : ∀ varId ∈ evidence.fcv,
          varId.id < q.nextCap := fun varId varMem =>
        bounded varId (by
          simp only [Shape.Evidence.fcvList, List.mem_append]
          exact Or.inl varMem)
      have boundedTailAt : ∀ {qmid : InferenceBase.FreshSupply},
          SupplyExtends q qmid →
          ∀ varId ∈ Shape.Evidence.fcvList rest,
            varId.id < qmid.nextCap := fun ext varId varMem =>
        Nat.lt_of_lt_of_le
          (bounded varId (by
            simp only [Shape.Evidence.fcvList, List.mem_append]
            exact Or.inr varMem))
          ext.1
      cases isObservable with
      | true =>
          cases hhead : freshenSkeletonSupply observable evidence q with
          | none => simp [freshenSkeletonMaskedSupply, hhead] at h
          | some headResult =>
              obtain ⟨head, q₁⟩ := headResult
              cases htail : freshenSkeletonMaskedSupply observable mask
                  rest q₁ with
              | none => simp [freshenSkeletonMaskedSupply, hhead,
                  htail] at h
              | some tailResult =>
                  obtain ⟨tail, q₂⟩ := tailResult
                  simp only [freshenSkeletonMaskedSupply, hhead, htail,
                    reduceIte] at h
                  cases h
                  intro capability mem
                  rcases List.mem_cons.mp mem with hh | ht
                  · subst hh
                    exact (freshenSkeletonSupply_boundedBy hhead
                        boundedHead).mono
                      (SupplyExtends.freshenSkeletonMasked htail)
                  · exact freshenSkeletonMaskedSupply_boundedBy htail
                      (boundedTailAt (SupplyExtends.freshenSkeleton hhead))
                      capability ht
      | false =>
          have h' : (match freshenSkeletonMaskedSupply observable mask
                rest q with
              | none => none
              | some (tail, q₂) => some ((Cap.any :: tail : List Cap), q₂))
              = some (capabilities, q') := h
          cases htail : freshenSkeletonMaskedSupply observable mask
              rest q with
          | none => rw [htail] at h'; exact nomatch h'
          | some tailResult =>
              obtain ⟨tail, q₂⟩ := tailResult
              rw [htail] at h'
              cases h'
              intro capability mem
              rcases List.mem_cons.mp mem with hh | ht
              · subst hh
                intro varId varMem
                simp only [Cap.fcv] at varMem
                exact nomatch varMem
              · exact freshenSkeletonMaskedSupply_boundedBy htail
                  (boundedTailAt (SupplyExtends.refl q)) capability ht
  | [], _ :: _, _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, _, h, _ => nomatch h

end

/-- The shared pattern-constructor assignments are bounded by the successor
supply. -/
theorem patternCtorAssignmentsSupply_fcv :
    ∀ (variables : List TypePM.TyVar) (q : InferenceBase.FreshSupply),
      ∀ varId ∈ Projection.assignmentsFcv
          (patternCtorAssignmentsSupply variables q).1,
        varId.id < (patternCtorAssignmentsSupply variables q).2.nextCap
  | [], q => by
      intro varId mem
      simp only [patternCtorAssignmentsSupply,
        Projection.assignmentsFcv] at mem
      exact nomatch mem
  | tyVar :: variables, q => by
      intro varId mem
      simp only [patternCtorAssignmentsSupply,
        Projection.assignmentsFcv] at mem ⊢
      rcases List.mem_append.mp mem with hhead | htail
      · have : varId ∈ (Cap.var ⟨q.nextCap⟩).fcv := by
          simpa [Shape.fcv_ofCap] using hhead
        simp only [Cap.fcv, List.mem_singleton] at this
        subst this
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
          (SupplyExtends.patternCtorAssignments variables
            { q with nextCap := q.nextCap + 1 }).1
      · exact patternCtorAssignmentsSupply_fcv variables _ varId htail

/-- The matcher-bodied recursive-binder placeholder is bounded by its
successor supply. -/
theorem fixMatcherPlaceholderSupply_boundedBy {signature : FrozenSig}
    {clauses : List Clause} {q : InferenceBase.FreshSupply}
    {domain codomain : Ty} {q₀ : InferenceBase.FreshSupply}
    (h : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q₀)) :
    domain.BoundedBy q₀ ∧ codomain.BoundedBy q₀ := by
  unfold fixMatcherPlaceholderSupply at h
  split at h
  next => exact nomatch h
  next evidence hskeleton =>
    have evidenceBounded : ∀ varId ∈ evidence.fcv,
        varId.id < q.nextCap := by
      intro varId mem
      rw [Inference.matcherSkeletonEvidence_fcv hskeleton] at mem
      exact nomatch mem
    split at h
    next => exact nomatch h
    next capability qc heq =>
      have capBounded : capability.BoundedBy qc := by
        cases evidence with
        | unseen =>
            cases heq
            intro varId mem
            simp only [Cap.fcv] at mem
            exact nomatch mem
        | known leaf =>
            exact freshenSkeletonSupply_boundedBy heq evidenceBounded
        | con name children =>
            exact freshenSkeletonSupply_boundedBy heq evidenceBounded
        | prod components =>
            exact freshenSkeletonSupply_boundedBy heq evidenceBounded
      cases hfcv : capability.fcv with
      | cons first restVars =>
          rw [hfcv] at h
          cases h
          constructor
          · refine ⟨?_, ?_⟩
            · intro varId mem
              simp only [Ty.fcv, Cap.fcv, List.append_nil,
                List.mem_singleton] at mem
              cases mem
              exact capBounded first (by simp [hfcv])
            · intro varId mem
              simp only [Ty.ftv, List.mem_singleton] at mem
              subst mem
              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
                (Nat.le_succ _)
          · refine ⟨?_, ?_⟩
            · intro varId mem
              simp only [Ty.fcv, List.append_nil] at mem
              exact capBounded varId mem
            · intro varId mem
              simp only [Ty.ftv, List.mem_singleton] at mem
              subst mem
              exact Nat.lt_succ_self _
      | nil =>
          rw [hfcv] at h
          cases h
          constructor
          · refine ⟨?_, ?_⟩
            · intro varId mem
              simp only [Ty.fcv, Cap.fcv, List.append_nil,
                List.mem_singleton] at mem
              subst mem
              exact Nat.lt_succ_self _
            · intro varId mem
              simp only [Ty.ftv, List.mem_singleton] at mem
              subst mem
              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
                (Nat.le_succ _)
          · refine ⟨?_, ?_⟩
            · intro varId mem
              simp only [Ty.fcv, List.append_nil] at mem
              exact Nat.lt_succ_of_lt (capBounded varId mem)
            · intro varId mem
              simp only [Ty.ftv, List.mem_singleton] at mem
              subst mem
              exact Nat.lt_succ_self _

/-- The pattern-constructor capability relation preserves boundedness and
returns a bounded capability. -/
theorem DDPatternCtorCap.boundedBy {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst}
    (built : DDPatternCtorCap signature entry q S childCaps capability
      q' S')
    (Sb : S.BoundedBy q)
    (childrenBounded : ∀ child ∈ childCaps, child.BoundedBy q) :
    capability.BoundedBy q' ∧ S'.BoundedBy q' := by
  cases built with
  | project hproject freshened =>
      constructor
      · apply freshenSkeletonSupply_boundedBy freshened
        intro varId mem
        have hsub := Projection.projectSignature_fcv hproject mem
        rw [Shape.fcvList_map_ofCap] at hsub
        obtain ⟨resolved, resolvedMem, varMem⟩ :=
          Cap.mem_fcvList_split hsub
        obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp resolvedMem
        exact (Sb.applyCap (childrenBounded child childMem)) varId varMem
      · exact Sb.mono (SupplyExtends.freshenSkeleton freshened)
  | fallback hproject hvars hdemands aligned hprojected freshened =>
      rename_i resultVariables demands projected
      have extendsQA := SupplyExtends.patternCtorAssignments
        resultVariables.eraseDups (q := q)
      have demandsBounded : ∀ demand ∈ demands, ∀ capability,
          demand = some capability →
          Cap.BoundedBy (patternCtorAssignmentsSupply
            resultVariables.eraseDups q).2 capability := by
        intro demand mem capability heq varId varMem
        exact patternCtorAssignmentsSupply_fcv resultVariables.eraseDups q
          varId (Inference.patternCtorFieldDemands_fcv hdemands demand mem
            capability heq varMem)
      have alignedBounded : S'.BoundedBy (patternCtorAssignmentsSupply
          resultVariables.eraseDups q).2 :=
        aligned.boundedBy (Sb.mono extendsQA)
          (fun child mem => (childrenBounded child mem).mono extendsQA)
          demandsBounded
      constructor
      · apply freshenSkeletonSupply_boundedBy freshened
        intro varId mem
        have hsub := Projection.projectSignature_fcv hprojected mem
        rw [Shape.fcvList_map_ofCap] at hsub
        obtain ⟨resolved, resolvedMem, varMem⟩ :=
          Cap.mem_fcvList_split hsub
        obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp resolvedMem
        exact (alignedBounded.applyCap ((childrenBounded child childMem).mono
          extendsQA)) varId varMem
      · exact alignedBounded.mono (SupplyExtends.freshenSkeleton freshened)

/-! ### Boundedness of schemes, contexts, and instantiation

Bounded schemes have all out-of-binder free variables below the supply's
counters.  Binder instantiation then yields output bounded by the successor
supply: quantified variables receive metas inside the consumed interval and
free variables persist below the original counters.  Signature schemes are
consumed through the closedness predicate `FrozenSig.SchemesClosed`, which
makes them bounded at every supply.
-/

/-- All free variables of an expression scheme lie below the counters. -/
structure Scheme.BoundedBy (q : InferenceBase.FreshSupply)
    (scheme : Scheme) : Prop where
  caps : ∀ varId ∈ scheme.fcv, varId.id < q.nextCap
  targets : ∀ varId ∈ scheme.ftv, varId < q.nextTy

/-- Scheme boundedness is monotone along supply extension. -/
theorem Scheme.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {scheme : Scheme} (extends_ : SupplyExtends q q')
    (bounded : scheme.BoundedBy q) : scheme.BoundedBy q' :=
  ⟨fun varId mem => Nat.lt_of_lt_of_le (bounded.caps varId mem) extends_.1,
    fun varId mem =>
      Nat.lt_of_lt_of_le (bounded.targets varId mem) extends_.2⟩

/-- A monomorphic scheme of a bounded type is bounded. -/
theorem Scheme.BoundedBy.ofMono {q : InferenceBase.FreshSupply} {τ : Ty}
    (bounded : Ty.BoundedBy q τ) : (Scheme.mono τ).BoundedBy q :=
  ⟨fun varId mem => bounded.caps varId (List.mem_filter.mp mem).1,
    fun varId mem => bounded.targets varId (List.mem_filter.mp mem).1⟩

/-- Instantiating binders over a capability with bounded free variables
yields a capability bounded by the successor supply. -/
theorem instantiateBinders_applyCap_boundedBy
    {q : InferenceBase.FreshSupply} {capBinders : List CapVar}
    {tyBinders : List TypePM.TyVar} {capability : Cap}
    (capsBounded : ∀ varId ∈ capability.fcv, varId ∉ capBinders →
      varId.id < q.nextCap) :
    Cap.BoundedBy
      (InferenceBase.instantiateBinders q capBinders tyBinders).supply
      (capability.apply
        (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.cap) := by
  intro varId mem
  rw [Unification.Cap.fcv_apply] at mem
  simp only [List.mem_flatMap] at mem
  obtain ⟨original, originalMem, imageMem⟩ := mem
  by_cases hbinder : original ∈ capBinders
  · obtain ⟨freshId, hmap, hlow, hhigh⟩ :=
      InferenceBase.instantiateBinders_cap_bounds q capBinders tyBinders
        hbinder
    rw [hmap] at imageMem
    simp only [Cap.fcv, List.mem_singleton] at imageMem
    subst imageMem
    exact hhigh
  · rw [InferenceBase.instantiateBinders_cap_support q capBinders tyBinders
      original hbinder] at imageMem
    simp only [Cap.fcv, List.mem_singleton] at imageMem
    subst imageMem
    refine Nat.lt_of_lt_of_le (capsBounded varId originalMem hbinder) ?_
    rw [InferenceBase.instantiateBinders_nextCap]
    exact Nat.le_add_right _ _

/-- Instantiating binders over a type with bounded free variables yields a
type bounded by the successor supply. -/
theorem instantiateBinders_apply_boundedBy
    {q : InferenceBase.FreshSupply} {capBinders : List CapVar}
    {tyBinders : List TypePM.TyVar} {body : Ty}
    (capsBounded : ∀ varId ∈ body.fcv, varId ∉ capBinders →
      varId.id < q.nextCap)
    (targetsBounded : ∀ varId ∈ body.ftv, varId ∉ tyBinders →
      varId < q.nextTy) :
    Ty.BoundedBy
      (InferenceBase.instantiateBinders q capBinders tyBinders).supply
      ((InferenceBase.instantiateBinders q capBinders
        tyBinders).subst.apply body) := by
  constructor
  · intro varId mem
    have mem' : varId ∈ ((body.applyCapability
        (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.cap).applyTarget
        (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.target).fcv := mem
    rcases Ty.mem_fcv_applyTarget _ _ varId mem' with own | image
    · rw [Ty.fcv_applyCapability] at own
      simp only [List.mem_flatMap] at own
      obtain ⟨original, originalMem, imageMem⟩ := own
      by_cases hbinder : original ∈ capBinders
      · obtain ⟨freshId, hmap, hlow, hhigh⟩ :=
          InferenceBase.instantiateBinders_cap_bounds q capBinders
            tyBinders hbinder
        rw [hmap] at imageMem
        simp only [Cap.fcv, List.mem_singleton] at imageMem
        subst imageMem
        exact hhigh
      · rw [InferenceBase.instantiateBinders_cap_support q capBinders
          tyBinders original hbinder] at imageMem
        simp only [Cap.fcv, List.mem_singleton] at imageMem
        subst imageMem
        refine Nat.lt_of_lt_of_le
          (capsBounded varId originalMem hbinder) ?_
        rw [InferenceBase.instantiateBinders_nextCap]
        exact Nat.le_add_right _ _
    · obtain ⟨tyVar, tyMem, imageMem⟩ := image
      rcases InferenceBase.freshTySubst_is_var q.nextTy tyBinders tyVar
        with ⟨freshId, hvar⟩
      have himg : (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.target tyVar = .var freshId := hvar
      rw [himg] at imageMem
      simp only [Ty.fcv] at imageMem
      exact nomatch imageMem
  · intro varId mem
    have mem' : varId ∈ ((body.applyCapability
        (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.cap).applyTarget
        (InferenceBase.instantiateBinders q capBinders
          tyBinders).subst.target).ftv := mem
    rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability] at mem'
    simp only [List.mem_flatMap] at mem'
    obtain ⟨original, originalMem, imageMem⟩ := mem'
    by_cases hbinder : original ∈ tyBinders
    · obtain ⟨freshId, hmap, hlow, hhigh⟩ :=
        InferenceBase.instantiateBinders_ty_bounds q capBinders tyBinders
          hbinder
      rw [hmap] at imageMem
      simp only [Ty.ftv, List.mem_singleton] at imageMem
      subst imageMem
      exact hhigh
    · rw [InferenceBase.instantiateBinders_ty_support q capBinders
        tyBinders original hbinder] at imageMem
      simp only [Ty.ftv, List.mem_singleton] at imageMem
      subst imageMem
      refine Nat.lt_of_lt_of_le
        (targetsBounded varId originalMem hbinder) ?_
      rw [InferenceBase.instantiateBinders_nextTy]
      exact Nat.le_add_right _ _

/-- Instantiating a bounded expression scheme yields a bounded type. -/
theorem instantiateScheme_boundedBy {q : InferenceBase.FreshSupply}
    {scheme : Scheme} (bounded : Scheme.BoundedBy q scheme) :
    Ty.BoundedBy (InferenceBase.instantiateScheme q scheme).supply
      (InferenceBase.instantiateScheme q scheme).value :=
  instantiateBinders_apply_boundedBy
    (fun varId mem hbinder => bounded.caps varId
      (List.mem_filter.mpr ⟨mem, by simpa using hbinder⟩))
    (fun varId mem hbinder => bounded.targets varId
      (List.mem_filter.mpr ⟨mem, by simpa using hbinder⟩))

/-- All free variables of a constructor scheme lie below the counters. -/
structure CtorScheme.BoundedBy (q : InferenceBase.FreshSupply)
    (scheme : CtorScheme) : Prop where
  caps : ∀ varId ∈ scheme.fcv, varId.id < q.nextCap
  targets : ∀ varId ∈ scheme.ftv, varId < q.nextTy

/-- Instantiating a bounded constructor scheme bounds both the argument
targets and the result. -/
theorem instantiateCtorScheme_boundedBy {q : InferenceBase.FreshSupply}
    {scheme : CtorScheme} (bounded : CtorScheme.BoundedBy q scheme) :
    (∀ arg ∈ (InferenceBase.instantiateCtorScheme q scheme).value.1,
      Ty.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply
        arg) ∧
    Ty.BoundedBy (InferenceBase.instantiateCtorScheme q scheme).supply
      (InferenceBase.instantiateCtorScheme q scheme).value.2 := by
  constructor
  · intro arg argMem
    have argMem' : arg ∈ scheme.args.map
        (InferenceBase.instantiateBinders q scheme.capBinders
          scheme.tyBinders).subst.apply := argMem
    obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp argMem'
    exact instantiateBinders_apply_boundedBy
      (fun varId mem hbinder => bounded.caps varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl
          (Ty.mem_fcvList_of_mem originalMem mem)),
          by simpa using hbinder⟩))
      (fun varId mem hbinder => bounded.targets varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl
          (Ty.mem_ftvList_of_mem originalMem mem)),
          by simpa using hbinder⟩))
  · exact instantiateBinders_apply_boundedBy
      (fun varId mem hbinder => bounded.caps varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr mem),
          by simpa using hbinder⟩))
      (fun varId mem hbinder => bounded.targets varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr mem),
          by simpa using hbinder⟩))

/-- All free variables of a dual scheme lie below the counters. -/
structure DualScheme.BoundedBy (q : InferenceBase.FreshSupply)
    (scheme : DualScheme) : Prop where
  caps : ∀ varId ∈ scheme.fcv, varId.id < q.nextCap
  targets : ∀ varId ∈ scheme.ftv, varId < q.nextTy

/-- Instantiating a bounded dual scheme bounds the argument duals and the
result dual. -/
theorem instantiateDualScheme_boundedBy {q : InferenceBase.FreshSupply}
    {scheme : DualScheme} (bounded : DualScheme.BoundedBy q scheme) :
    (∀ dual ∈ (InferenceBase.instantiateDualScheme q scheme).value.1,
      Dual.BoundedBy (InferenceBase.instantiateDualScheme q scheme).supply
        dual) ∧
    Dual.BoundedBy (InferenceBase.instantiateDualScheme q scheme).supply
      (InferenceBase.instantiateDualScheme q scheme).value.2 := by
  have dualBounded : ∀ dual : Dual,
      (∀ varId ∈ dual.fcv, varId ∉ scheme.capBinders →
        varId.id < q.nextCap) →
      (∀ varId ∈ dual.ftv, varId ∉ scheme.tyBinders →
        varId < q.nextTy) →
      Dual.BoundedBy
        (InferenceBase.instantiateBinders q scheme.capBinders
          scheme.tyBinders).supply
        (dual.apply
          (InferenceBase.instantiateBinders q scheme.capBinders
            scheme.tyBinders).subst.cap
          (InferenceBase.instantiateBinders q scheme.capBinders
            scheme.tyBinders).subst.target) := by
    intro dual capsBounded targetsBounded
    constructor
    · exact instantiateBinders_applyCap_boundedBy
        (fun varId mem hbinder => capsBounded varId
          (List.mem_append.mpr (Or.inl mem)) hbinder)
    · exact instantiateBinders_apply_boundedBy
        (fun varId mem hbinder => capsBounded varId
          (List.mem_append.mpr (Or.inr mem)) hbinder)
        (fun varId mem hbinder => targetsBounded varId mem hbinder)
  constructor
  · intro dual dualMem
    have dualMem' : dual ∈ scheme.args.map (Dual.apply
        (InferenceBase.instantiateBinders q scheme.capBinders
          scheme.tyBinders).subst.cap
        (InferenceBase.instantiateBinders q scheme.capBinders
          scheme.tyBinders).subst.target) := dualMem
    obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp dualMem'
    exact dualBounded original
      (fun varId mem hbinder => bounded.caps varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl
          (List.mem_flatMap.mpr ⟨original, originalMem, mem⟩)),
          by simpa using hbinder⟩))
      (fun varId mem hbinder => bounded.targets varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl
          (List.mem_flatMap.mpr ⟨original, originalMem, mem⟩)),
          by simpa using hbinder⟩))
  · exact dualBounded scheme.result
      (fun varId mem hbinder => bounded.caps varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr mem),
          by simpa using hbinder⟩))
      (fun varId mem hbinder => bounded.targets varId
        (List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr mem),
          by simpa using hbinder⟩))

/-! ### Closed signature schemes -/

/-- A constructor scheme with no free variables outside its binders. -/
def CtorScheme.Closed (scheme : CtorScheme) : Prop :=
  scheme.fcv = [] ∧ scheme.ftv = []

/-- A dual scheme with no free variables outside its binders. -/
def DualScheme.Closed (scheme : DualScheme) : Prop :=
  scheme.fcv = [] ∧ scheme.ftv = []

/-- A closed constructor scheme is bounded by every supply. -/
theorem CtorScheme.Closed.boundedBy {q : InferenceBase.FreshSupply}
    {scheme : CtorScheme} (closed : scheme.Closed) :
    CtorScheme.BoundedBy q scheme := by
  constructor
  · intro varId mem
    rw [closed.1] at mem
    exact nomatch mem
  · intro varId mem
    rw [closed.2] at mem
    exact nomatch mem

/-- A closed dual scheme is bounded by every supply. -/
theorem DualScheme.Closed.boundedBy {q : InferenceBase.FreshSupply}
    {scheme : DualScheme} (closed : scheme.Closed) :
    DualScheme.BoundedBy q scheme := by
  constructor
  · intro varId mem
    rw [closed.1] at mem
    exact nomatch mem
  · intro varId mem
    rw [closed.2] at mem
    exact nomatch mem

instance : DecidablePred CtorScheme.Closed := fun scheme =>
  decidable_of_iff (scheme.fcv = [] ∧ scheme.ftv = []) Iff.rfl

instance : DecidablePred DualScheme.Closed := fun scheme =>
  decidable_of_iff (scheme.fcv = [] ∧ scheme.ftv = []) Iff.rfl

/-- Every scheme reachable from the frozen lookup tables is closed.  This
is the signature-closedness condition of the freshness invariant: a frozen
signature never leaks an ambient inference metavariable. -/
structure FrozenSig.SchemesClosed (signature : FrozenSig) : Prop where
  dataCtors : ∀ {name : String} {scheme : CtorScheme},
    signature.findDataCtor name = some scheme → scheme.Closed
  patternCtors : ∀ {name : String}
    {entry : PatternCtorScheme signature.observability},
    signature.findPatternCtor name = some entry → entry.scheme.Closed
  patternFuns : ∀ {name : String} {scheme : DualScheme},
    signature.findPatternFun name = some scheme → scheme.Closed
  primitives : ∀ {op : PrimOp} {scheme : CtorScheme},
    signature.findPrimitive op = some scheme → scheme.Closed
  /-- The complete table representation carries no free capability
  metavariables, including entries shadowed by lookup. -/
  signatureCaps : signature.fcv = []
  /-- Ordinary free metavariables are absent from the complete table
  representation as well. -/
  signatureTargets : signature.ftv = []

/-- Entry-wise sufficient condition for signature closedness: for a
concrete frozen signature every table is a finite literal, so each
hypothesis is decidable. -/
theorem FrozenSig.SchemesClosed.of_entries {signature : FrozenSig}
    (dataClosed : ∀ entry ∈ signature.dataCtors, entry.2.Closed)
    (patternClosed : ∀ entry ∈ signature.patternCtors,
      entry.2.scheme.Closed)
    (funClosed : ∀ entry ∈ signature.patternFuns, entry.2.Closed)
    (primClosed : ∀ entry ∈ signature.primitives, entry.2.Closed) :
    signature.SchemesClosed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name scheme hfind
    unfold FrozenSig.findDataCtor at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.dataCtors with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact dataClosed entry (List.mem_of_find?_eq_some hlist)
  · intro name entry hfind
    unfold FrozenSig.findPatternCtor at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.patternCtors with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some found =>
        rw [hlist] at hfind
        cases hfind
        exact patternClosed found (List.mem_of_find?_eq_some hlist)
  · intro name scheme hfind
    unfold FrozenSig.findPatternFun at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.patternFuns with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact funClosed entry (List.mem_of_find?_eq_some hlist)
  · intro op scheme hfind
    unfold FrozenSig.findPrimitive at hfind
    cases hlist : List.find? (fun entry => entry.1 == op)
        signature.primitives with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact primClosed entry (List.mem_of_find?_eq_some hlist)
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro varId membership
    simp only [FrozenSig.fcv, List.mem_append] at membership
    rcases membership with ((dataMem | patternMem) | funMem) | primMem
    · rcases List.mem_flatMap.mp dataMem with
        ⟨entry, entryMem, varMem⟩
      rw [(dataClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp patternMem with
        ⟨entry, entryMem, varMem⟩
      rw [(patternClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp funMem with
        ⟨entry, entryMem, varMem⟩
      rw [(funClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp primMem with
        ⟨entry, entryMem, varMem⟩
      rw [(primClosed entry entryMem).1] at varMem
      contradiction
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro varId membership
    simp only [FrozenSig.ftv, List.mem_append] at membership
    rcases membership with ((dataMem | patternMem) | funMem) | primMem
    · rcases List.mem_flatMap.mp dataMem with
        ⟨entry, entryMem, varMem⟩
      rw [(dataClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp patternMem with
        ⟨entry, entryMem, varMem⟩
      rw [(patternClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp funMem with
        ⟨entry, entryMem, varMem⟩
      rw [(funClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp primMem with
        ⟨entry, entryMem, varMem⟩
      rw [(primClosed entry entryMem).2] at varMem
      contradiction

/-! ### Boundedness of contexts -/

/-- All schemes of an expression context are bounded. -/
def Context.BoundedBy (q : InferenceBase.FreshSupply) (Γ : Context) :
    Prop :=
  ∀ entry ∈ Γ, Scheme.BoundedBy q entry.2

/-- Context boundedness is monotone along supply extension. -/
theorem Context.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {Γ : Context} (extends_ : SupplyExtends q q')
    (bounded : Context.BoundedBy q Γ) : Context.BoundedBy q' Γ :=
  fun entry mem => (bounded entry mem).mono extends_

/-- Extending a bounded context with a bounded scheme is bounded. -/
theorem Context.BoundedBy.cons {q : InferenceBase.FreshSupply}
    {entry : String × Scheme} {Γ : Context}
    (entryBounded : Scheme.BoundedBy q entry.2)
    (bounded : Context.BoundedBy q Γ) :
    Context.BoundedBy q (entry :: Γ) := by
  intro e mem
  rcases List.mem_cons.mp mem with rfl | hmem
  · exact entryBounded
  · exact bounded e hmem

/-- Appending bounded contexts is bounded. -/
theorem Context.BoundedBy.append {q : InferenceBase.FreshSupply}
    {Γ₁ Γ₂ : Context} (bounded₁ : Context.BoundedBy q Γ₁)
    (bounded₂ : Context.BoundedBy q Γ₂) :
    Context.BoundedBy q (Γ₁ ++ Γ₂) := by
  intro e mem
  rcases List.mem_append.mp mem with hmem | hmem
  · exact bounded₁ e hmem
  · exact bounded₂ e hmem

/-- Lookup in a bounded context returns a bounded scheme. -/
theorem Context.BoundedBy.find? {q : InferenceBase.FreshSupply}
    {Γ : Context} {name : String} {scheme : Scheme}
    (bounded : Context.BoundedBy q Γ)
    (found : Context.find? Γ name = some scheme) :
    Scheme.BoundedBy q scheme := by
  unfold Context.find? at found
  cases hfind : List.find? (fun entry => entry.1 == name) Γ with
  | none => rw [hfind] at found; exact nomatch found
  | some entry =>
      rw [hfind] at found
      cases found
      exact bounded entry (List.mem_of_find?_eq_some hfind)

/-- Applying a bounded substitution to a bounded scheme is bounded. -/
theorem Scheme.BoundedBy.applySubst {q : InferenceBase.FreshSupply}
    {S : Subst} {scheme : Scheme} (Sb : S.BoundedBy q)
    (bounded : Scheme.BoundedBy q scheme) :
    (scheme.applySubst S).BoundedBy q := by
  have maskedCap : ∀ original : CapVar,
      S.cap.mask scheme.capBinders original =
        (if original ∈ scheme.capBinders then Cap.var original
          else S.cap original) := fun _ => rfl
  have maskedTarget : ∀ original : TypePM.TyVar,
      S.target.mask scheme.tyBinders original =
        (if original ∈ scheme.tyBinders then Ty.var original
          else S.target original) := fun _ => rfl
  constructor
  · intro varId mem
    simp only [Scheme.applySubst, Scheme.fcv] at mem
    obtain ⟨mem', hnotbinder⟩ := List.mem_filter.mp mem
    rcases Ty.mem_fcv_applyTarget _ _ varId mem' with own | image
    · rw [Ty.fcv_applyCapability] at own
      simp only [List.mem_flatMap] at own
      obtain ⟨original, originalMem, imageMem⟩ := own
      by_cases hbinder : original ∈ scheme.capBinders
      · rw [maskedCap original, if_pos hbinder] at imageMem
        simp only [Cap.fcv, List.mem_singleton] at imageMem
        subst imageMem
        exact absurd hbinder (by simpa using hnotbinder)
      · rw [maskedCap original, if_neg hbinder] at imageMem
        exact Sb.capImagesBounded original
          (bounded.caps original (List.mem_filter.mpr
            ⟨originalMem, by simpa using hbinder⟩)) varId imageMem
    · obtain ⟨tyVar, tyMem, imageMem⟩ := image
      rw [Ty.ftv_applyCapability] at tyMem
      have imageMem' : varId ∈
          (S.target.mask scheme.tyBinders tyVar).fcv := imageMem
      by_cases hbinder : tyVar ∈ scheme.tyBinders
      · rw [maskedTarget tyVar, if_pos hbinder] at imageMem'
        simp only [Ty.fcv] at imageMem'
        exact nomatch imageMem'
      · rw [maskedTarget tyVar, if_neg hbinder] at imageMem'
        exact (Sb.targetImagesBounded tyVar (bounded.targets tyVar
          (List.mem_filter.mpr ⟨tyMem, by simpa using hbinder⟩))).caps
          varId imageMem'
  · intro varId mem
    simp only [Scheme.applySubst, Scheme.ftv] at mem
    obtain ⟨mem', hnotbinder⟩ := List.mem_filter.mp mem
    have mem'' : varId ∈ ((scheme.body.applyCapability
        (S.cap.mask scheme.capBinders)).applyTarget
        (S.target.mask scheme.tyBinders)).ftv := mem'
    rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability] at mem''
    simp only [List.mem_flatMap] at mem''
    obtain ⟨original, originalMem, imageMem⟩ := mem''
    have imageMem' : varId ∈
        (S.target.mask scheme.tyBinders original).ftv := imageMem
    by_cases hbinder : original ∈ scheme.tyBinders
    · rw [maskedTarget original, if_pos hbinder] at imageMem'
      simp only [Ty.ftv, List.mem_singleton] at imageMem'
      subst imageMem'
      exact absurd hbinder (by simpa using hnotbinder)
    · rw [maskedTarget original, if_neg hbinder] at imageMem'
      exact (Sb.targetImagesBounded original (bounded.targets original
        (List.mem_filter.mpr ⟨originalMem,
          by simpa using hbinder⟩))).targets varId imageMem'

/-- Applying a bounded substitution to a bounded context is bounded. -/
theorem Context.BoundedBy.applySubst {q : InferenceBase.FreshSupply}
    {S : Subst} {Γ : Context} (Sb : S.BoundedBy q)
    (bounded : Context.BoundedBy q Γ) :
    Context.BoundedBy q (Context.applySubst S Γ) := by
  intro entry mem
  obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp mem
  exact Scheme.BoundedBy.applySubst Sb (bounded original originalMem)

/-- All types of a monomorphic context are bounded. -/
def MonoCtx.BoundedBy (q : InferenceBase.FreshSupply) (Δ : MonoCtx) :
    Prop :=
  ∀ entry ∈ Δ, Ty.BoundedBy q entry.2

/-- Monomorphic-context boundedness is monotone along supply extension. -/
theorem MonoCtx.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {Δ : MonoCtx} (extends_ : SupplyExtends q q')
    (bounded : MonoCtx.BoundedBy q Δ) : MonoCtx.BoundedBy q' Δ :=
  fun entry mem => (bounded entry mem).mono extends_

/-- Extending a bounded monomorphic context with a bounded type. -/
theorem MonoCtx.BoundedBy.cons {q : InferenceBase.FreshSupply}
    {entry : String × Ty} {Δ : MonoCtx}
    (entryBounded : Ty.BoundedBy q entry.2)
    (bounded : MonoCtx.BoundedBy q Δ) :
    MonoCtx.BoundedBy q (entry :: Δ) := by
  intro e mem
  rcases List.mem_cons.mp mem with rfl | hmem
  · exact entryBounded
  · exact bounded e hmem

/-- Appending bounded monomorphic contexts is bounded. -/
theorem MonoCtx.BoundedBy.append {q : InferenceBase.FreshSupply}
    {Δ₁ Δ₂ : MonoCtx} (bounded₁ : MonoCtx.BoundedBy q Δ₁)
    (bounded₂ : MonoCtx.BoundedBy q Δ₂) :
    MonoCtx.BoundedBy q (Δ₁ ++ Δ₂) := by
  intro e mem
  rcases List.mem_append.mp mem with hmem | hmem
  · exact bounded₁ e hmem
  · exact bounded₂ e hmem

/-- A bounded monomorphic context yields a bounded expression context. -/
theorem MonoCtx.BoundedBy.toContext {q : InferenceBase.FreshSupply}
    {Δ : MonoCtx} (bounded : MonoCtx.BoundedBy q Δ) :
    Context.BoundedBy q (MonoCtx.toContext Δ) := by
  intro entry mem
  obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp mem
  exact Scheme.BoundedBy.ofMono (bounded original originalMem)

/-- All duals of a pattern-parameter context are bounded. -/
def PatternCtx.BoundedBy (q : InferenceBase.FreshSupply)
    (Φ : PatternCtx) : Prop :=
  ∀ entry ∈ Φ, Dual.BoundedBy q entry.2

/-- Pattern-context boundedness is monotone along supply extension. -/
theorem PatternCtx.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {Φ : PatternCtx} (extends_ : SupplyExtends q q')
    (bounded : PatternCtx.BoundedBy q Φ) : PatternCtx.BoundedBy q' Φ :=
  fun entry mem =>
    ⟨(bounded entry mem).1.mono extends_,
      (bounded entry mem).2.mono extends_⟩

/-- Lookup in a bounded pattern context returns a bounded dual. -/
theorem PatternCtx.BoundedBy.find? {q : InferenceBase.FreshSupply}
    {Φ : PatternCtx} {name : String} {dual : Dual}
    (bounded : PatternCtx.BoundedBy q Φ)
    (found : PatternCtx.find? Φ name = some dual) :
    Dual.BoundedBy q dual := by
  unfold PatternCtx.find? at found
  cases hfind : List.find? (fun entry => entry.1 == name) Φ with
  | none => rw [hfind] at found; exact nomatch found
  | some entry =>
      rw [hfind] at found
      cases found
      exact bounded entry (List.mem_of_find?_eq_some hfind)

/-- Generalization relative to a frozen signature preserves boundedness:
the generalized scheme's free variables are free variables of its body. -/
theorem FrozenSig.generalize_boundedBy {q : InferenceBase.FreshSupply}
    {signature : FrozenSig} {Γ : Context} {τ : Ty}
    (bounded : Ty.BoundedBy q τ) :
    Scheme.BoundedBy q (signature.generalize Γ τ) :=
  ⟨fun varId mem => bounded.caps varId (List.mem_filter.mp mem).1,
    fun varId mem => bounded.targets varId (List.mem_filter.mp mem).1⟩

/-! ### Boundedness sweep: pattern-layer families

Every demand-directed judgment preserves the freshness invariant: from a
bounded input state (prevailing substitution, context, and expected types
below the input supply), the output substitution and every published
output are bounded by the output supply.  The expression-free data- and
primitive-pattern families close first.
-/

/-- A capability variable below the counter is bounded. -/
theorem Cap.BoundedBy.varOf {q : InferenceBase.FreshSupply}
    {varId : CapVar} (h : varId.id < q.nextCap) :
    (Cap.var varId).BoundedBy q := by
  intro w hw
  simp only [Cap.fcv, List.mem_singleton] at hw
  subst hw
  exact h

/-- A target variable below the counter is bounded. -/
theorem Ty.BoundedBy.varOf {q : InferenceBase.FreshSupply}
    {varId : TypePM.TyVar} (h : varId < q.nextTy) :
    (Ty.var varId).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv] at hw
    exact nomatch hw
  · intro w hw
    simp only [Ty.ftv, List.mem_singleton] at hw
    subst hw
    exact h

/-- The integer base type is bounded by every supply. -/
theorem Ty.BoundedBy.int {q : InferenceBase.FreshSupply} :
    Ty.int.BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv] at hw
    exact nomatch hw
  · intro w hw
    simp only [Ty.ftv] at hw
    exact nomatch hw

/-- A function type of bounded components is bounded. -/
theorem Ty.BoundedBy.fnOf {q : InferenceBase.FreshSupply}
    {domain codomain : Ty} (domainBounded : domain.BoundedBy q)
    (codomainBounded : codomain.BoundedBy q) :
    (Ty.fn domain codomain).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    rcases hw with h | h
    · exact domainBounded.caps w h
    · exact codomainBounded.caps w h
  · intro w hw
    simp only [Ty.ftv, List.mem_append] at hw
    rcases hw with h | h
    · exact domainBounded.targets w h
    · exact codomainBounded.targets w h

/-- A matcher type of bounded components is bounded. -/
theorem Ty.BoundedBy.matcherOf {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (capBounded : capability.BoundedBy q)
    (targetBounded : target.BoundedBy q) :
    (Ty.matcher capability target).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    rcases hw with h | h
    · exact capBounded w h
    · exact targetBounded.caps w h
  · intro w hw
    simp only [Ty.ftv] at hw
    exact targetBounded.targets w hw

/-- A slot type of bounded components is bounded. -/
theorem Ty.BoundedBy.slotOf {q : InferenceBase.FreshSupply}
    {capability : Cap} {target : Ty}
    (capBounded : capability.BoundedBy q)
    (targetBounded : target.BoundedBy q) :
    (Ty.slot capability target).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.fcv, List.mem_append] at hw
    rcases hw with h | h
    · exact capBounded w h
    · exact targetBounded.caps w h
  · intro w hw
    simp only [Ty.ftv] at hw
    exact targetBounded.targets w hw

/-- Dual boundedness is monotone along supply extension. -/
theorem Dual.BoundedBy.mono {q q' : InferenceBase.FreshSupply}
    {dual : Dual} (extends_ : SupplyExtends q q')
    (bounded : Dual.BoundedBy q dual) : Dual.BoundedBy q' dual :=
  ⟨bounded.1.mono extends_, bounded.2.mono extends_⟩

/-- The canonical tuple type of bounded components is bounded. -/
theorem prodTy_boundedBy {q : InferenceBase.FreshSupply} :
    ∀ {targets : List Ty},
      (∀ target ∈ targets, target.BoundedBy q) →
      (prodTy targets).BoundedBy q
  | [], _ => Ty.BoundedBy.prodOfForall (fun target mem => nomatch mem)
  | [target], bounded => bounded target (by simp)
  | target₁ :: target₂ :: targets, bounded =>
      Ty.BoundedBy.prodOfForall bounded

/-- The list type of a bounded element is bounded. -/
theorem listT_boundedBy {q : InferenceBase.FreshSupply} {τ : Ty}
    (bounded : τ.BoundedBy q) : (Ty.listT τ).BoundedBy q := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Ty.listT, Ty.fcv, Ty.fcvList, List.append_nil] at hw
    exact bounded.caps w hw
  · intro w hw
    simp only [Ty.listT, Ty.ftv, Ty.ftvList, List.append_nil] at hw
    exact bounded.targets w hw

mutual

/-- Data-pattern checking preserves boundedness. -/
theorem DDDPat.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
      {expectedTarget : Ty} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDDPat signature q S pattern expectedTarget bindings q' S' →
      signature.SchemesClosed → S.BoundedBy q →
      expectedTarget.BoundedBy q →
      S'.BoundedBy q' ∧ MonoCtx.BoundedBy q' bindings
  | _, _, _, _, _, _, _, .var, _, Sb, expectedBounded =>
      ⟨Sb, by
        intro entry mem
        rcases List.mem_cons.mp mem with rfl | h
        · exact expectedBounded
        · exact nomatch h⟩
  | _, _, _, _, _, _, _, .wild, _, Sb, _ =>
      ⟨Sb, fun entry mem => nomatch mem⟩
  | _, _, _, _, _, _, _,
      .ctor (scheme := scheme) hfind aligned children, closed, Sb,
      expectedBounded => by
      rename_i q S expectedTarget bindings q' S' name patterns S₁
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateCtorScheme q scheme
      have S₁Bounded := aligned.boundedBy (Sb.mono extendsInst)
        instBounded.2 (expectedBounded.mono extendsInst)
      exact children.boundedBy closed S₁Bounded instBounded.1
  | _, _, _, _, _, _, _,
      .tuple (patterns := patterns) aligned children, closed, Sb,
      expectedBounded => by
      rename_i q S expectedTarget S₁ bindings q' S'
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      have extendsF := SupplyExtends.freshTargets patterns.length q
      have S₁Bounded := aligned.boundedBy (Sb.mono extendsF)
        (Ty.BoundedBy.prodOfForall targetsBounded)
        (expectedBounded.mono extendsF)
      exact children.boundedBy closed S₁Bounded targetsBounded

/-- Data-pattern list checking preserves boundedness. -/
theorem DDDPats.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List DPat}
      {targets : List Ty} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDDPats signature q S patterns targets bindings q' S' →
      signature.SchemesClosed → S.BoundedBy q →
      (∀ target ∈ targets, target.BoundedBy q) →
      S'.BoundedBy q' ∧ MonoCtx.BoundedBy q' bindings
  | _, _, _, _, _, _, _, .nil, _, Sb, _ =>
      ⟨Sb, fun entry mem => nomatch mem⟩
  | _, _, _, _, _, _, _, .cons head tail hdisjoint, closed, Sb,
      targetsBounded => by
      obtain ⟨S₁Bounded, headBindings⟩ := head.boundedBy closed Sb
        (targetsBounded _ (by simp))
      obtain ⟨S'Bounded, tailBindings⟩ := tail.boundedBy closed S₁Bounded
        (fun target mem => (targetsBounded target (by simp [mem])).mono
          head.supplyExtends)
      exact ⟨S'Bounded, MonoCtx.BoundedBy.append
        (headBindings.mono tail.supplyExtends) tailBindings⟩

end

mutual

/-- Primitive-pattern checking preserves boundedness and returns bounded
holes and bindings. -/
theorem DDPPat.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
      {expectedTarget : Ty} {holes : List Dual} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDPPat signature q S pattern expectedTarget holes bindings q' S' →
      signature.SchemesClosed → S.BoundedBy q →
      expectedTarget.BoundedBy q →
      S'.BoundedBy q' ∧ (∀ dual ∈ holes, Dual.BoundedBy q' dual) ∧
        MonoCtx.BoundedBy q' bindings
  | _, _, _, _, _, _, _, _, .hole, _, Sb, expectedBounded => by
      refine ⟨Sb.mono (SupplyExtends.bumpCap _ 1), ?_, ?_⟩
      · intro dual mem
        rcases List.mem_cons.mp mem with rfl | h
        · exact ⟨Cap.BoundedBy.varOf (Nat.lt_succ_self _),
            expectedBounded.mono (SupplyExtends.bumpCap _ 1)⟩
        · exact nomatch h
      · intro entry mem
        exact nomatch mem
  | _, _, _, _, _, _, _, _, .wild, _, Sb, _ => by
      refine ⟨Sb, ?_, ?_⟩
      · intro dual mem
        exact nomatch mem
      · intro entry mem
        exact nomatch mem
  | _, _, _, _, _, _, _, _, .pval, _, Sb, expectedBounded => by
      refine ⟨Sb, ?_, ?_⟩
      · intro dual mem
        exact nomatch mem
      · intro entry mem
        rcases List.mem_cons.mp mem with rfl | h
        · exact expectedBounded
        · exact nomatch h
  | _, _, _, _, _, _, _, _,
      .ctor (entry := entry) hfind aligned children, closed, Sb,
      expectedBounded => by
      rename_i q S expectedTarget holes bindings q' S' name patterns S₁
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateCtorScheme q entry.scheme
      have S₁Bounded := aligned.boundedBy (Sb.mono extendsInst)
        instBounded.2 (expectedBounded.mono extendsInst)
      exact children.boundedBy closed S₁Bounded instBounded.1
  | _, _, _, _, _, _, _, _,
      .tuple (patterns := patterns) aligned children, closed, Sb,
      expectedBounded => by
      rename_i q S expectedTarget S₁ holes bindings q' S'
      have targetsBounded := freshTargetsSupply_boundedBy patterns.length q
      have extendsF := SupplyExtends.freshTargets patterns.length q
      have S₁Bounded := aligned.boundedBy (Sb.mono extendsF)
        (Ty.BoundedBy.prodOfForall targetsBounded)
        (expectedBounded.mono extendsF)
      exact children.boundedBy closed S₁Bounded targetsBounded

/-- Primitive-pattern list checking preserves boundedness. -/
theorem DDPPats.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List PPat}
      {targets : List Ty} {holes : List Dual} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDPPats signature q S patterns targets holes bindings q' S' →
      signature.SchemesClosed → S.BoundedBy q →
      (∀ target ∈ targets, target.BoundedBy q) →
      S'.BoundedBy q' ∧ (∀ dual ∈ holes, Dual.BoundedBy q' dual) ∧
        MonoCtx.BoundedBy q' bindings
  | _, _, _, _, _, _, _, _, .nil, _, Sb, _ => by
      refine ⟨Sb, ?_, ?_⟩
      · intro dual mem
        exact nomatch mem
      · intro entry mem
        exact nomatch mem
  | _, _, _, _, _, _, _, _, .cons head tail hdisjoint, closed, Sb,
      targetsBounded => by
      obtain ⟨S₁Bounded, headHoles, headBindings⟩ := head.boundedBy closed
        Sb (targetsBounded _ (by simp))
      obtain ⟨S'Bounded, tailHoles, tailBindings⟩ := tail.boundedBy closed
        S₁Bounded
        (fun target mem => (targetsBounded target (by simp [mem])).mono
          head.supplyExtends)
      refine ⟨S'Bounded, ?_, MonoCtx.BoundedBy.append
        (headBindings.mono tail.supplyExtends) tailBindings⟩
      intro dual mem
      rcases List.mem_append.mp mem with h | h
      · exact ⟨(headHoles dual h).1.mono tail.supplyExtends,
          (headHoles dual h).2.mono tail.supplyExtends⟩
      · exact tailHoles dual h

end

mutual

/-- Synthesis preserves boundedness and publishes a bounded raw type. -/
theorem DDSynth.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
      {τ : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDSynth signature q S Γ e τ q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      S'.BoundedBy q' ∧ τ.BoundedBy q'
  | q, _, _, _, _, _, _, .var (scheme := scheme) hfind, _, Sb, Γb => by
      exact ⟨Sb.mono (SupplyExtends.instantiateScheme q scheme),
        instantiateScheme_boundedBy
          (Context.BoundedBy.find? (Γb.applySubst Sb) hfind)⟩
  | q, _, _, _, _, _, _, .lam body, closed, Sb, Γb => by
      have qb := SupplyExtends.bumpTy q 1
      have domB : Ty.BoundedBy { q with nextTy := q.nextTy + 1 }
          (.var q.nextTy) := Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      obtain ⟨S'b, bodyB⟩ := body.boundedBy closed (Sb.mono qb)
        (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domB)
          (Γb.mono qb))
      exact ⟨S'b, Ty.BoundedBy.fnOf (domB.mono body.supplyExtends) bodyB⟩
  | q, _, _, _, _, _, _, .fix hne hself hnonmatcher body aligned, closed,
      Sb, Γb => by
      have qb := SupplyExtends.bumpTy q 2
      have domB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var q.nextTy) :=
        Ty.BoundedBy.varOf (show q.nextTy < q.nextTy + 2 by omega)
      have codB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var (q.nextTy + 1)) :=
        Ty.BoundedBy.varOf (show q.nextTy + 1 < q.nextTy + 2 by omega)
      obtain ⟨S₁b, bodyB⟩ := body.boundedBy closed (Sb.mono qb)
        (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domB)
          (Context.BoundedBy.cons
            (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domB codB))
            (Γb.mono qb)))
      have ext := body.supplyExtends
      exact ⟨aligned.boundedBy S₁b bodyB (codB.mono ext),
        Ty.BoundedBy.fnOf (domB.mono ext) (codB.mono ext)⟩
  | q, _, _, _, _, _, _,
      .app (q₁ := q₁) function aligned argument, closed, Sb, Γb => by
      obtain ⟨S₁b, fnB⟩ := function.boundedBy closed Sb Γb
      have qb := SupplyExtends.bumpTy q₁ 2
      have domB : Ty.BoundedBy { q₁ with nextTy := q₁.nextTy + 2 }
          (.var q₁.nextTy) :=
        Ty.BoundedBy.varOf (show q₁.nextTy < q₁.nextTy + 2 by omega)
      have codB : Ty.BoundedBy { q₁ with nextTy := q₁.nextTy + 2 }
          (.var (q₁.nextTy + 1)) :=
        Ty.BoundedBy.varOf (show q₁.nextTy + 1 < q₁.nextTy + 2 by omega)
      have S₂b := aligned.boundedBy (S₁b.mono qb) (fnB.mono qb)
        (Ty.BoundedBy.fnOf domB codB)
      have S₃b := argument.boundedBy closed S₂b
        (Γb.mono ((function.supplyExtends).trans qb)) domB
      exact ⟨S₃b, codB.mono argument.supplyExtends⟩
  | _, _, _, _, _, _, _, .lit, _, Sb, _ => ⟨Sb, Ty.BoundedBy.int⟩
  | _, _, _, _, _, _, _, .tuple expressions, closed, Sb, Γb => by
      obtain ⟨S'b, targetsB⟩ := expressions.boundedBy closed Sb Γb
      exact ⟨S'b, Ty.BoundedBy.prodOfForall targetsB⟩
  | q, _, _, _, _, _, _, .ctor (scheme := scheme) hfind arguments, closed,
      Sb, Γb => by
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateCtorScheme q scheme
      have S'b := arguments.boundedBy closed (Sb.mono extendsInst)
        (Γb.mono extendsInst) instBounded.1
      exact ⟨S'b, instBounded.2.mono arguments.supplyExtends⟩
  | q, _, _, _, _, _, _, .prim (scheme := scheme) hfind arguments, closed,
      Sb, Γb => by
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.primitives hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateCtorScheme q scheme
      have S'b := arguments.boundedBy closed (Sb.mono extendsInst)
        (Γb.mono extendsInst) instBounded.1
      exact ⟨S'b, instBounded.2.mono arguments.supplyExtends⟩
  | q, _, Γ, _, _, _, _,
      .letE (valueTarget := valueTarget) (S₁ := S₁) value body, closed,
      Sb, Γb => by
      obtain ⟨S₁b, valueB⟩ := value.boundedBy closed Sb Γb
      have ext₁ := value.supplyExtends
      obtain ⟨S'b, bodyB⟩ := body.boundedBy closed S₁b
        (Context.BoundedBy.cons
          (FrozenSig.generalize_boundedBy (S₁b.apply valueB))
          (Γb.mono ext₁))
      exact ⟨S'b, bodyB⟩
  | q, _, _, _, _, _, _, .something, _, Sb, _ => by
      refine ⟨Sb.mono (SupplyExtends.bumpTy q 1),
        Ty.BoundedBy.matcherOf ?_
          (Ty.BoundedBy.varOf (Nat.lt_succ_self _))⟩
      intro w hw
      simp only [Cap.fcv] at hw
      exact nomatch hw
  | q, _, _, _, _, q', S',
      .matcher (rawHoleLists := rawHoleLists) (capability := capability)
        clausesD hcollect hshape hcaps hcatch hbind harm hcover,
      closed, Sb, Γb => by
      have qb := SupplyExtends.bumpTy q 1
      obtain ⟨S'b, holesB⟩ := clausesD.boundedBy closed (Sb.mono qb)
        (Γb.mono qb) (Ty.BoundedBy.varOf (Nat.lt_succ_self _))
      have capB : capability.BoundedBy q' := by
        intro varId varMem
        obtain ⟨holeCaps, holeCapsMem, varIn⟩ :=
          Inference.collectClauseEvidence_fcv hcollect varId
            (Shape.inferShape_fcv hshape varMem)
        obtain ⟨rawHoles, rawMem, rfl⟩ := List.mem_map.mp holeCapsMem
        obtain ⟨resolvedCap, resolvedMem, varInCap⟩ :=
          Cap.mem_fcvList_split varIn
        obtain ⟨resolvedDual, resolvedDualMem, rfl⟩ :=
          List.mem_map.mp resolvedMem
        obtain ⟨rawDual, rawDualMem, rfl⟩ :=
          List.mem_map.mp resolvedDualMem
        exact (S'b.applyCap
          (holesB rawHoles rawMem rawDual rawDualMem).1) varId varInCap
      exact ⟨S'b, Ty.BoundedBy.matcherOf capB
        (Ty.BoundedBy.varOf
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            clausesD.supplyExtends.2))⟩
  | _, _, Γ, _, _, _, _,
      .matchAll (dual := dual) (Δ := Δ) target pattern aligned matcher
        body,
      closed, Sb, Γb => by
      obtain ⟨S₁b, targetB⟩ := target.boundedBy closed Sb Γb
      have ext₁ := target.supplyExtends
      obtain ⟨S₂b, dualB, ΔB⟩ := pattern.boundedBy closed S₁b
        (Γb.mono ext₁) (fun entry mem => nomatch mem)
        (fun entry mem => nomatch mem)
      have ext₂ := pattern.supplyExtends
      have S₃b := aligned.boundedBy S₂b dualB.2 (targetB.mono ext₂)
      have S₄b := matcher.boundedBy closed S₃b
        (Γb.mono (ext₁.trans ext₂))
        (Ty.BoundedBy.slotOf dualB.1 (targetB.mono ext₂))
      have ext₃ := matcher.supplyExtends
      obtain ⟨S'b, bodyB⟩ := body.boundedBy closed S₄b
        (Context.BoundedBy.append ((ΔB.mono ext₃).toContext)
          (Γb.mono ((ext₁.trans ext₂).trans ext₃)))
      exact ⟨S'b, listT_boundedBy bodyB⟩
  | q, _, _, _, _, _, _,
      .fixMatcher (domain := domain) (codomain := codomain) (q₀ := q₀)
        hne hself built body aligned,
      closed, Sb, Γb => by
      obtain ⟨domB, codB⟩ := fixMatcherPlaceholderSupply_boundedBy built
      have ext₀ := SupplyExtends.fixMatcherPlaceholder built
      obtain ⟨S₁b, bodyB⟩ := body.boundedBy closed (Sb.mono ext₀)
        (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domB)
          (Context.BoundedBy.cons
            (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domB codB))
            (Γb.mono ext₀)))
      have ext₁ := body.supplyExtends
      exact ⟨aligned.boundedBy S₁b bodyB (codB.mono ext₁),
        Ty.BoundedBy.fnOf (domB.mono ext₁) (codB.mono ext₁)⟩

/-- List synthesis preserves boundedness. -/
theorem DDSynths.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {es : List Expr} {τs : List Ty} {q' : InferenceBase.FreshSupply}
      {S' : Subst},
      DDSynths signature q S Γ es τs q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      S'.BoundedBy q' ∧ ∀ τ ∈ τs, τ.BoundedBy q'
  | _, _, _, _, _, _, _, .nil, _, Sb, _ => by
      refine ⟨Sb, ?_⟩
      intro τ mem
      exact nomatch mem
  | _, _, _, _, _, _, _, .cons head tail, closed, Sb, Γb => by
      obtain ⟨S₁b, headB⟩ := head.boundedBy closed Sb Γb
      obtain ⟨S'b, tailB⟩ := tail.boundedBy closed S₁b
        (Γb.mono head.supplyExtends)
      refine ⟨S'b, ?_⟩
      intro τ mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact headB.mono tail.supplyExtends
      · exact tailB τ h

/-- Checking preserves boundedness. -/
theorem DDCheck.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
      {expected : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDCheck signature q S Γ e expected q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      expected.BoundedBy q → S'.BoundedBy q'
  | _, _, _, _, _, _, _, .mk synthesized aligned, closed, Sb, Γb,
      expectedB => by
      obtain ⟨S₁b, rawB⟩ := synthesized.boundedBy closed Sb Γb
      exact aligned.boundedBy S₁b rawB
        (expectedB.mono synthesized.supplyExtends)

/-- List checking preserves boundedness. -/
theorem DDChecks.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {es : List Expr} {expecteds : List Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDChecks signature q S Γ es expecteds q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      (∀ expected ∈ expecteds, expected.BoundedBy q) → S'.BoundedBy q'
  | _, _, _, _, _, _, _, .nil, _, Sb, _, _ => Sb
  | _, _, _, _, _, _, _, .cons head tail, closed, Sb, Γb, expectedsB => by
      have S₁b := head.boundedBy closed Sb Γb (expectedsB _ (by simp))
      exact tail.boundedBy closed S₁b (Γb.mono head.supplyExtends)
        (fun expected mem => (expectedsB expected (by simp [mem])).mono
          head.supplyExtends)

/-- Pattern synthesis preserves boundedness and publishes a bounded dual
and binding context. -/
theorem DDPattern.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {pattern : Pattern} {dual : Dual}
      {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDPattern signature q S Γ Φ Δ pattern dual Δ' q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      PatternCtx.BoundedBy q Φ → MonoCtx.BoundedBy q Δ →
      S'.BoundedBy q' ∧ Dual.BoundedBy q' dual ∧
        MonoCtx.BoundedBy q' Δ'
  | q, _, _, _, _, _, _, _, _, _, .pvar hfresh, _, Sb, _, _, Δb => by
      have qb : SupplyExtends q
          { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } :=
        SupplyExtends.bumpBoth q 1 1
      refine ⟨Sb.mono qb,
        ⟨Cap.BoundedBy.varOf (Nat.lt_succ_self _),
          Ty.BoundedBy.varOf (Nat.lt_succ_self _)⟩, ?_⟩
      refine MonoCtx.BoundedBy.append (Δb.mono qb) ?_
      intro entry mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      · exact nomatch h
  | q, _, _, _, _, _, _, _, _, _, .wild, _, Sb, _, _, Δb => by
      have qb : SupplyExtends q
          { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 1 } :=
        SupplyExtends.bumpBoth q 1 1
      exact ⟨Sb.mono qb,
        ⟨Cap.BoundedBy.varOf (Nat.lt_succ_self _),
          Ty.BoundedBy.varOf (Nat.lt_succ_self _)⟩, Δb.mono qb⟩
  | _, _, _, _, _, _, _, _, _, _, .pval (q₁ := q₁) value, closed, Sb, Γb,
      _, Δb => by
      obtain ⟨S₁b, targetB⟩ := value.boundedBy closed Sb
        (Context.BoundedBy.append (Δb.toContext) Γb)
      have ext₁ := value.supplyExtends
      have qb := SupplyExtends.bumpCap q₁ 1
      exact ⟨S₁b.mono qb,
        ⟨Cap.BoundedBy.varOf (Nat.lt_succ_self _), targetB.mono qb⟩,
        (Δb.mono (ext₁.trans qb))⟩
  | _, _, _, _, _, _, _, _, _, _, .embed hfind, _, Sb, _, Φb, Δb =>
      ⟨Sb, Φb.find? hfind, Δb⟩
  | _, _, _, _, _, _, _, _, _, _, .ptuple patterns, closed, Sb, Γb, Φb,
      Δb => by
      obtain ⟨S'b, dualsB, Δ'b⟩ := patterns.boundedBy closed Sb Γb Φb Δb
      refine ⟨S'b, ⟨?_, ?_⟩, Δ'b⟩
      · apply Cap.BoundedBy.prodOfForall
        intro capability mem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp mem
        exact (dualsB dual dualMem).1
      · apply Ty.BoundedBy.prodOfForall
        intro target mem
        obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp mem
        exact (dualsB dual dualMem).2
  | q, _, _, _, _, _, _, _, _, _,
      .pctor (entry := entry) (capability := capability) hfind patterns
        alignedTargets ctorCap hcompatible,
      closed, Sb, Γb, Φb, Δb => by
      have instBounded := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateCtorScheme q
        entry.scheme
      obtain ⟨S₁b, dualsB, Δ'b⟩ := patterns.boundedBy closed
        (Sb.mono extendsInst) (Γb.mono extendsInst) (Φb.mono extendsInst)
        (Δb.mono extendsInst)
      have ext₁ := patterns.supplyExtends
      have S₂b := alignedTargets.boundedBy S₁b dualsB
        (fun expected mem => (instBounded.1 expected mem).mono ext₁)
      obtain ⟨capB, S₃b⟩ := ctorCap.boundedBy S₂b
        (fun child mem => by
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp mem
          exact (dualsB dual dualMem).1)
      have ext₂ := ctorCap.supplyExtends
      exact ⟨S₃b, ⟨capB, (instBounded.2.mono (ext₁.trans ext₂))⟩,
        Δ'b.mono ext₂⟩
  | _, _, _, _, _, _, _, _, _, _, .pand left right aligned, closed, Sb,
      Γb, Φb, Δb => by
      obtain ⟨S₁b, leftDualB, Δₗb⟩ := left.boundedBy closed Sb Γb Φb Δb
      have ext₁ := left.supplyExtends
      obtain ⟨S₂b, rightDualB, Δ'b⟩ := right.boundedBy closed S₁b
        (Γb.mono ext₁) (Φb.mono ext₁) Δₗb
      have ext₂ := right.supplyExtends
      have S'b := aligned.boundedBy S₂b
        (Dual.BoundedBy.mono ext₂ leftDualB) rightDualB
      exact ⟨S'b, Dual.BoundedBy.mono ext₂ leftDualB, Δ'b⟩
  | _, _, _, _, _, _, _, _, _, _, .por left right alignedDual
      alignedBindings, closed, Sb, Γb, Φb, Δb => by
      obtain ⟨S₁b, leftDualB, Δₗb⟩ := left.boundedBy closed Sb Γb Φb Δb
      have ext₁ := left.supplyExtends
      obtain ⟨S₂b, rightDualB, Δᵣb⟩ := right.boundedBy closed S₁b
        (Γb.mono ext₁) (Φb.mono ext₁) (Δb.mono ext₁)
      have ext₂ := right.supplyExtends
      have S₃b := alignedDual.boundedBy S₂b
        (Dual.BoundedBy.mono ext₂ leftDualB) rightDualB
      have S'b := alignedBindings.boundedBy S₃b
        (fun entry mem => (Δₗb.mono ext₂) entry mem)
        (fun entry mem => Δᵣb entry mem)
      exact ⟨S'b, Dual.BoundedBy.mono ext₂ leftDualB, Δₗb.mono ext₂⟩
  | q, _, _, _, _, _, _, _, _, _,
      .papp (scheme := scheme) hfind patterns aligned, closed, Sb, Γb,
      Φb, Δb => by
      have instBounded := instantiateDualScheme_boundedBy (q := q)
        ((closed.patternFuns hfind).boundedBy)
      have extendsInst := SupplyExtends.instantiateDualScheme q scheme
      obtain ⟨S₁b, dualsB, Δ'b⟩ := patterns.boundedBy closed
        (Sb.mono extendsInst) (Γb.mono extendsInst) (Φb.mono extendsInst)
        (Δb.mono extendsInst)
      have ext₁ := patterns.supplyExtends
      have S'b := aligned.boundedBy S₁b dualsB
        (fun dual mem => ⟨(instBounded.1 dual mem).1.mono ext₁,
          (instBounded.1 dual mem).2.mono ext₁⟩)
      exact ⟨S'b, ⟨(instBounded.2.1.mono ext₁), (instBounded.2.2.mono
        ext₁)⟩, Δ'b⟩

/-- Pattern-list synthesis preserves boundedness. -/
theorem DDPatterns.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {Φ : PatternCtx} {Δ : MonoCtx} {patterns : List Pattern}
      {duals : List Dual} {Δ' : MonoCtx} {q' : InferenceBase.FreshSupply}
      {S' : Subst},
      DDPatterns signature q S Γ Φ Δ patterns duals Δ' q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      PatternCtx.BoundedBy q Φ → MonoCtx.BoundedBy q Δ →
      S'.BoundedBy q' ∧ (∀ dual ∈ duals, Dual.BoundedBy q' dual) ∧
        MonoCtx.BoundedBy q' Δ'
  | _, _, _, _, _, _, _, _, _, _, .nil, _, Sb, _, _, Δb => by
      refine ⟨Sb, ?_, Δb⟩
      intro dual mem
      exact nomatch mem
  | _, _, _, _, _, _, _, _, _, _, .cons head tail, closed, Sb, Γb, Φb,
      Δb => by
      obtain ⟨S₁b, headDualB, Δ₁b⟩ := head.boundedBy closed Sb Γb Φb Δb
      have ext₁ := head.supplyExtends
      obtain ⟨S'b, tailDualsB, Δ'b⟩ := tail.boundedBy closed S₁b
        (Γb.mono ext₁) (Φb.mono ext₁) Δ₁b
      have ext₂ := tail.supplyExtends
      refine ⟨S'b, ?_, Δ'b⟩
      intro dual mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact Dual.BoundedBy.mono ext₂ headDualB
      · exact tailDualsB dual h

/-- Arm checking preserves boundedness. -/
theorem DDArms.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {ppBindings : MonoCtx} {arms : List Arm}
      {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
      {S' : Subst},
      DDArms signature q S Γ ppBindings arms clauseTarget bodyTarget
        q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      MonoCtx.BoundedBy q ppBindings → clauseTarget.BoundedBy q →
      bodyTarget.BoundedBy q → S'.BoundedBy q'
  | _, _, _, _, _, _, _, _, _, .nil, _, Sb, _, _, _, _ => Sb
  | _, _, _, _, _, _, _, _, _, .cons dataPattern hdisjoint body rest,
      closed, Sb, Γb, ppB, clauseTargetB, bodyTargetB => by
      obtain ⟨S₁b, armBindingsB⟩ := dataPattern.boundedBy closed Sb
        clauseTargetB
      have ext₁ := dataPattern.supplyExtends
      have S₂b := body.boundedBy closed S₁b
        (Context.BoundedBy.append
          (Context.BoundedBy.append (armBindingsB.toContext)
            ((ppB.mono ext₁).toContext))
          (Γb.mono ext₁))
        (bodyTargetB.mono ext₁)
      have ext₂ := body.supplyExtends
      exact rest.boundedBy closed S₂b (Γb.mono (ext₁.trans ext₂))
        (ppB.mono (ext₁.trans ext₂))
        (clauseTargetB.mono (ext₁.trans ext₂))
        (bodyTargetB.mono (ext₁.trans ext₂))

/-- Clause inference preserves boundedness and publishes bounded holes. -/
theorem DDClause.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {clause : Clause} {sharedTarget : Ty} {holes : List Dual}
      {q' : InferenceBase.FreshSupply} {S' : Subst},
      DDClause signature q S Γ clause sharedTarget holes q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      sharedTarget.BoundedBy q →
      S'.BoundedBy q' ∧ ∀ dual ∈ holes, Dual.BoundedBy q' dual
  | _, _, _, _, _, _, _, _, .mk pp hdecompose nextMatchers arms, closed,
      Sb, Γb, sharedB => by
      obtain ⟨S₁b, holesB, ppBindB⟩ := pp.boundedBy closed Sb sharedB
      have ext₁ := pp.supplyExtends
      have S₂b := nextMatchers.boundedBy closed S₁b (Γb.mono ext₁)
        (fun expected mem => by
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp mem
          exact Ty.BoundedBy.slotOf (holesB dual dualMem).1
            (holesB dual dualMem).2)
      have ext₂ := nextMatchers.supplyExtends
      have S'b := arms.boundedBy closed S₂b
        (Γb.mono (ext₁.trans ext₂)) (ppBindB.mono ext₂)
        (sharedB.mono (ext₁.trans ext₂))
        (listT_boundedBy (prodTy_boundedBy (fun target mem => by
          obtain ⟨dual, dualMem, rfl⟩ := List.mem_map.mp mem
          exact ((holesB dual dualMem).2.mono ext₂))))
      have ext₃ := arms.supplyExtends
      refine ⟨S'b, ?_⟩
      intro dual mem
      exact ⟨(holesB dual mem).1.mono (ext₂.trans ext₃),
        (holesB dual mem).2.mono (ext₂.trans ext₃)⟩

/-- Clause-list inference preserves boundedness and publishes bounded hole
ledgers. -/
theorem DDClauses.boundedBy {signature : FrozenSig} :
    ∀ {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {clauses : List Clause} {sharedTarget : Ty}
      {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
      {S' : Subst},
      DDClauses signature q S Γ clauses sharedTarget holeLists q' S' →
      signature.SchemesClosed → S.BoundedBy q → Context.BoundedBy q Γ →
      sharedTarget.BoundedBy q →
      S'.BoundedBy q' ∧ ∀ holes ∈ holeLists, ∀ dual ∈ holes,
        Dual.BoundedBy q' dual
  | _, _, _, _, _, _, _, _, .nil, _, Sb, _, _ => by
      refine ⟨Sb, ?_⟩
      intro holes mem
      exact nomatch mem
  | _, _, _, _, _, _, _, _, .cons head tail, closed, Sb, Γb, sharedB => by
      obtain ⟨S₁b, headHolesB⟩ := head.boundedBy closed Sb Γb sharedB
      have ext₁ := head.supplyExtends
      obtain ⟨S'b, tailHolesB⟩ := tail.boundedBy closed S₁b
        (Γb.mono ext₁) (sharedB.mono ext₁)
      have ext₂ := tail.supplyExtends
      refine ⟨S'b, ?_⟩
      intro holes mem
      rcases List.mem_cons.mp mem with rfl | h
      · intro dual dualMem
        exact ⟨(headHolesB dual dualMem).1.mono ext₂,
          (headHolesB dual dualMem).2.mono ext₂⟩
      · exact tailHolesB holes h

end


/-! ### The closed wrapper starts bounded

The initial supply reserves every variable of the signature and the
context, the identity substitution is bounded at every supply, and the
sweep therefore bounds every published type of the closed wrapper by the
terminal supply of its derivation.
-/

/-- The initial supply bounds its own context. -/
theorem initialSupply_context_boundedBy (signature : FrozenSig)
    (context : Context) :
    Context.BoundedBy (Inference.initialSupply signature context)
      context := by
  intro entry mem
  constructor
  · intro varId varMem
    apply InferenceBase.mem_lt_binderSpan
    apply List.mem_map.mpr
    refine ⟨varId, List.mem_append.mpr (Or.inr ?_), rfl⟩
    refine List.mem_flatMap.mpr ⟨entry, mem, ?_⟩
    exact List.mem_append.mpr (Or.inr (List.mem_filter.mp varMem).1)
  · intro varId varMem
    apply InferenceBase.mem_lt_binderSpan
    refine List.mem_append.mpr (Or.inr ?_)
    refine List.mem_flatMap.mpr ⟨entry, mem, ?_⟩
    exact List.mem_append.mpr (Or.inr (List.mem_filter.mp varMem).1)

end TypePM
