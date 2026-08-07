import TypePM.Inference

/-!
# Demand-directed typing (`DDTyping`), expression layer

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
capability-freeze/export ledger axis is deliberately absent: it is the
separate `FreezeCompatible` correspondence condition of stage 3-3, not part
of the demand specification.
-/

namespace TypePM

open Inference (productMatcherDuals? productSlotDuals? matcherProducingRoot
  initialSupply)

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
the value-flow transport boundary shows is genuinely harmful. -/
def ExactCapMGU (left right : Cap) (subst : CapSubst) : Prop :=
  CapMGU left right subst ∧
  subst.SupportWithin (left.fcv ++ right.fcv)

/-- An exact most general target solution. -/
def ExactTargetMGU (left right : Ty) (subst : TySubst) : Prop :=
  TargetMGU left right subst ∧
  subst.SupportWithin (left.ftv ++ right.ftv)

/-- An exact most general paired solution: exact in both sorts. -/
def ExactPairedMGU (left right : Ty) (subst : Subst) : Prop :=
  PairedMGU left right subst ∧
  subst.cap.SupportWithin (left.fcv ++ right.fcv) ∧
  subst.target.SupportWithin (left.ftv ++ right.ftv)

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

/-- Identity is an exact most general unifier of equal capabilities. -/
theorem ExactCapMGU.refl (capability : Cap) :
    ExactCapMGU capability capability CapSubst.id :=
  ⟨CapMGU.refl capability, CapSubst.id_supportWithin _⟩

/-- The single binding is an exact most general capability solution. -/
theorem ExactCapMGU.varLeft (varId : CapVar) (capability : Cap)
    (notMem : varId ∉ capability.fcv) :
    ExactCapMGU (.var varId) capability
      (Unification.CapSubst.single varId capability) := by
  refine ⟨CapMGU.varLeft varId capability notMem, ?_⟩
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
  refine ⟨CapMGU.varRight capability varId notMem, ?_⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Cap.fcv])
  simp [Unification.CapSubst.single, hne]

/-- Identity is an exact most general unifier of equal targets. -/
theorem ExactTargetMGU.refl (target : Ty) :
    ExactTargetMGU target target TySubst.id :=
  ⟨TargetMGU.refl target, fun _ _ => rfl⟩

/-- The single binding is an exact most general target solution. -/
theorem ExactTargetMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    ExactTargetMGU (.var varId) target
      (Unification.TySubst.single varId target) := by
  refine ⟨TargetMGU.varLeft varId target notMem, ?_⟩
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
  refine ⟨TargetMGU.varRight target varId notMem, ?_⟩
  intro candidate outside
  have hne : ¬ varId = candidate := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [Unification.TySubst.single, hne]

/-- Identity is an exact most general paired unifier of equal types. -/
theorem ExactPairedMGU.refl (target : Ty) :
    ExactPairedMGU target target Subst.id :=
  ⟨PairedMGU.refl target, CapSubst.id_supportWithin _, fun _ _ => rfl⟩

/-- The single target binding is an exact most general paired solution. -/
theorem ExactPairedMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    ExactPairedMGU (.var varId) target
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  refine ⟨PairedMGU.varLeft varId target notMem,
    CapSubst.id_supportWithin _, ?_⟩
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
    CapSubst.id_supportWithin _, ?_⟩
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
  refine ⟨PairedMGU.fnDiagonal shared domain codomain domainNeShared
    domainNeCodomain codomainNeShared, CapSubst.id_supportWithin _, ?_⟩
  intro candidate outside
  have hshared : ¬ candidate = shared := fun h => outside (by
    cases h
    simp [Ty.ftv])
  have hcodomain : ¬ candidate = codomain := fun h => outside (by
    cases h
    simp [Ty.ftv])
  simp [fnDiagonalDelta, hshared, hcodomain]

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
  refine ⟨⟨?_, ?_⟩, CapSubst.id_supportWithin _, ?_⟩
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
  refine ⟨⟨?_, ?_⟩, CapSubst.id_supportWithin _, ?_⟩
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

/-- The closed wrapper: start from the source-scope supply and the identity
substitution, and publish the terminal substitution applied to the raw
result. -/
def DDTyping (signature : FrozenSig) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ raw q' S',
    DDSynth signature (initialSupply signature context) Subst.id context
      expression raw q' S' ∧
    target = S'.apply raw

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

end TypePM
