import TypePM.P2.CapTarget
import TypePM.P2.Relation
import TypePM.P2.Shape

/-!
# P2 runtime matcher boundary

This module states the reusable runtime proof kernel needed by the two-index
P2 core.  It does not pretend that the existing one-index `ClauseTy`
derivations have already been migrated.  `RuntimeSpec` keeps the remaining
source typing/evidence connection explicit and indexed by the actual runtime
environment and clause list.  The public non-CAS source boundary is the
narrower `CoreSpecWF` in `TypePM.P2.CoreSpec`; it derives a `RuntimeSpec` from
a deterministic checker on each actual clause.

Use-site coercion is proof-relevant: its combined substitution remains in the
constructor and is applied to the conclusion.  An unresolved consumer
capability or target is never left behind for later generalization.

Target compatibility here is syntactic equality after the retained
substitution.  CAS normalization/equivalence is deliberately outside this
runtime boundary.
-/

namespace TypePM.P2

/--
The general runtime proof-kernel interface.

`clauseEvidence` is indexed by the actual runtime closure and is functional,
so one matcher value cannot be assigned two unrelated evidence lists.
`observability` is frozen once for the whole specification.  Coverage is a
predicate of the actual clause list and inferred capability, rather than an
arbitrary proposition selected by each certificate.

`literalSubstitute` is exposed only at a certificate's actual evidence and
inferred capability.  It is invoked under both the same capability-stability
premise used by runtime slot coercion and an explicit `substAdmissible`
premise for the captured environment.  In particular, Ξ-closure alone is not
mistaken for closure of that environment.

Formal-core theorems must instantiate this through `CoreSpecWF`; a bare
`RuntimeSpec` is useful for parametric algebraic lemmas but is not by itself a
well-formed source calculus or a type-safety theorem.
-/
structure RuntimeSpec where
  observability : Shape.Observability
  literalTyped : Env → List Clause → Ty → Prop
  clauseEvidence : Env → List Clause → List Shape.Evidence → Prop
  substAdmissible : Env → CapSubst → TySubst → Prop
  evidenceUnique :
    ∀ {ρ cls left right},
      clauseEvidence ρ cls left →
      clauseEvidence ρ cls right →
      left = right
  literalSubstitute :
    ∀ {ρ cls evidence cap target},
      literalTyped ρ cls target →
      clauseEvidence ρ cls evidence →
      Shape.inferShape observability evidence = some cap →
      ∀ (C : CapSubst) (T : TySubst),
        cap.apply C = cap →
        substAdmissible ρ C T →
        literalTyped ρ cls (applyBoth C T target)
  coverageOK : List Clause → Cap → Prop

/-- Coverage mode for matcher certificates and runtime values. -/
inductive Mode where
  | ordinary
  | covered
deriving Repr, DecidableEq, BEq

/-- Only covered mode requires the source specification's coverage proof. -/
def CoverageReq : Mode → Prop → Prop
  | .ordinary, _ => True
  | .covered, coverage => coverage

@[simp] theorem coverageReq_ordinary (coverage : Prop) :
    CoverageReq .ordinary coverage :=
  True.intro

@[simp] theorem coverageReq_covered (coverage : Prop) :
    CoverageReq .covered coverage ↔ coverage :=
  Iff.rfl

/--
A certificate for one concrete runtime matcher literal.

The capability is computed exclusively from the evidence related to the
actual `ρ` and `cls`.  The ordinary target occurs in separate source-typing and
`CapTargetOK` fields, so target specialization cannot become ShapeCap evidence.
-/
structure MatcherCert
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty))
    (ρ : Env) (cls : List Clause) (cap : Cap) (target : Ty) where
  evidence : List Shape.Evidence
  literalTyped : spec.literalTyped ρ cls target
  sourceEvidence : spec.clauseEvidence ρ cls evidence
  shape :
    Shape.inferShape spec.observability evidence = some cap
  targetOK :
    CapTargetOK Ξ cap target
  coverage :
    CoverageReq mode (spec.coverageOK cls cap)

/-- Forget a covered certificate's coverage requirement. -/
def MatcherCert.toOrdinary
    {spec : RuntimeSpec}
    {Ξ : List (Cap × Ty)} {ρ : Env} {cls : List Clause}
    {cap : Cap} {target : Ty}
    (cert : MatcherCert spec .covered Ξ ρ cls cap target) :
    MatcherCert spec .ordinary Ξ ρ cls cap target where
  evidence := cert.evidence
  literalTyped := cert.literalTyped
  sourceEvidence := cert.sourceEvidence
  shape := cert.shape
  targetOK := cert.targetOK
  coverage := True.intro

/-- A covered certificate exposes coverage of its actual clauses. -/
theorem MatcherCert.coveredCoverage
    {spec : RuntimeSpec}
    {Ξ : List (Cap × Ty)} {ρ : Env} {cls : List Clause}
    {cap : Cap} {target : Ty}
    (cert : MatcherCert spec .covered Ξ ρ cls cap target) :
    spec.coverageOK cls cap :=
  cert.coverage

/--
Two certificates for the same runtime literal have the same intrinsic
capability.  This is where `RuntimeSpec.evidenceUnique` prevents arbitrary
re-certification of a value with unrelated clause evidence.
-/
theorem MatcherCert.intrinsicCapability_unique
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ : List (Cap × Ty)} {ρ : Env} {cls : List Clause}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    (left :
      MatcherCert spec mode Ξ ρ cls leftCap leftTarget)
    (right :
      MatcherCert spec mode Ξ ρ cls rightCap rightTarget) :
    leftCap = rightCap := by
  have evidence_eq : left.evidence = right.evidence :=
    spec.evidenceUnique left.sourceEvidence right.sourceEvidence
  have shapes_eq : some leftCap = some rightCap := by
    rw [← left.shape, ← right.shape, evidence_eq]
  exact Option.some.inj shapes_eq

/--
Transport a runtime certificate through an admissible coupled two-sorted
substitution.

The source bridge must type the genuinely substituted target.  Shape evidence
and coverage remain tied to the original runtime literal, while `CapTargetOK`
moves to the destination correspondence context.  `hcap` states the essential
runtime stability condition: the value's intrinsic capability is not changed
by a consumer-side substitution.  `hadmissible` separately states that the
same captured environment remains realizable at the substituted target.
-/
def MatcherCert.substStable
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)}
    {ρ : Env} {cls : List Clause} {cap : Cap} {target : Ty}
    {C : CapSubst} {T : TySubst}
    (cert : MatcherCert spec mode Ξ ρ cls cap target)
    (hcoupled : CoupledSubstOK Ξ Ξ' C T)
    (hcap : cap.apply C = cap)
    (hadmissible : spec.substAdmissible ρ C T) :
    MatcherCert spec mode Ξ' ρ cls cap (applyBoth C T target) where
  evidence := cert.evidence
  literalTyped :=
    spec.literalSubstitute cert.literalTyped cert.sourceEvidence cert.shape
      C T hcap hadmissible
  sourceEvidence := cert.sourceEvidence
  shape := cert.shape
  targetOK := by
    simpa only [hcap] using cert.targetOK.subst hcoupled
  coverage := cert.coverage

/--
Specialize only the target of a Ξ-closed certificate.

This is the identity-capability instance of `MatcherCert.substStable`.
Ξ-closure does not discharge admissibility for the captured environment.
-/
def MatcherCert.targetSpecializeClosed
    {spec : RuntimeSpec} {mode : Mode}
    {ρ : Env} {cls : List Clause} {cap : Cap} {target : Ty}
    (cert : MatcherCert spec mode [] ρ cls cap target) (T : TySubst)
    (hadmissible : spec.substAdmissible ρ CapSubst.id T) :
    MatcherCert spec mode [] ρ cls cap (target.applyTarget T) := by
  simpa [applyBoth, Ty.applyCapability_id] using
    cert.substStable (coupledSubstOK_nil CapSubst.id T)
      (Cap.apply_id cap) hadmissible

mutual

/-- Intrinsic two-index typing for type-erased runtime matcher values. -/
inductive MatcherValueTy
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) :
    Value → Cap → Ty → Prop where
  | something {target} :
      MatcherValueTy spec mode Ξ .something .none target
  | literal {ρ cls cap target} :
      MatcherCert spec mode Ξ ρ cls cap target →
      MatcherValueTy spec mode Ξ (.matcherV ρ cls) cap target
  | product {values caps targets} :
      MatcherValueTyList spec mode Ξ values caps targets →
      MatcherValueTy spec mode Ξ
        (.tuple values) (.prod caps) (.prod targets)

/-- Componentwise intrinsic typing for product matcher values. -/
inductive MatcherValueTyList
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) :
    List Value → List Cap → List Ty → Prop where
  | nil :
      MatcherValueTyList spec mode Ξ [] [] []
  | cons {value cap target values caps targets} :
      MatcherValueTy spec mode Ξ value cap target →
      MatcherValueTyList spec mode Ξ values caps targets →
      MatcherValueTyList spec mode Ξ
        (value :: values) (cap :: caps) (target :: targets)

end

mutual

/--
Every matcher literal contained in a runtime matcher value admits the
prevailing two-sorted substitution at its captured environment.
-/
def MatcherSubstAdmissible
    (spec : RuntimeSpec) (C : CapSubst) (T : TySubst) :
    Value → Prop
  | .something =>
      True
  | .matcherV ρ _ =>
      spec.substAdmissible ρ C T
  | .tuple values =>
      MatcherSubstAdmissibleList spec C T values
  | _ =>
      False

/-- List form of `MatcherSubstAdmissible`. -/
def MatcherSubstAdmissibleList
    (spec : RuntimeSpec) (C : CapSubst) (T : TySubst) :
    List Value → Prop
  | [] =>
      True
  | value :: values =>
      MatcherSubstAdmissible spec C T value ∧
        MatcherSubstAdmissibleList spec C T values

end

mutual

/--
The intrinsic capability of a runtime matcher value is unique.

Targets may legitimately differ after ordinary specialization, but the
capability is determined by the value: `something` has `none`, a literal has
the unique capability inferred from its clause evidence, and a tuple is
determined componentwise.
-/
theorem MatcherValueTy.intrinsicCapability_unique
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {value : Value}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    (left :
      MatcherValueTy spec mode Ξ value leftCap leftTarget)
    (right :
      MatcherValueTy spec mode Ξ value rightCap rightTarget) :
    leftCap = rightCap := by
  cases left with
  | something =>
      cases right
      rfl
  | literal leftCert =>
      cases right with
      | literal rightCert =>
          exact leftCert.intrinsicCapability_unique rightCert
  | product leftValues =>
      cases right with
      | product rightValues =>
          exact congrArg Cap.prod
            (MatcherValueTyList.intrinsicCapability_unique
              leftValues rightValues)

/-- List form of `MatcherValueTy.intrinsicCapability_unique`. -/
theorem MatcherValueTyList.intrinsicCapability_unique
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {values : List Value}
    {leftCaps rightCaps : List Cap}
    {leftTargets rightTargets : List Ty}
    (left :
      MatcherValueTyList spec mode Ξ values leftCaps leftTargets)
    (right :
      MatcherValueTyList spec mode Ξ values rightCaps rightTargets) :
    leftCaps = rightCaps := by
  cases left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail =>
      cases right with
      | cons rightHead rightTail =>
          congr
          · exact MatcherValueTy.intrinsicCapability_unique
              leftHead rightHead
          · exact MatcherValueTyList.intrinsicCapability_unique
              leftTail rightTail

end

/--
No typing derivation can assign the runtime value `something` a capability
other than `none`, regardless of its specialized target.
-/
theorem MatcherValueTy.something_capability_exclusive
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {cap : Cap} {target : Ty}
    (h : MatcherValueTy spec mode Ξ .something cap target) :
    cap = .none :=
  h.intrinsicCapability_unique
    (MatcherValueTy.something (target := target))

mutual

/--
Transport an intrinsically typed runtime matcher value through a coupled
substitution that fixes its intrinsic capability.
-/
theorem MatcherValueTy.substStable
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    {C : CapSubst} {T : TySubst}
    (h : MatcherValueTy spec mode Ξ value cap target)
    (hcoupled : CoupledSubstOK Ξ Ξ' C T)
    (hcap : cap.apply C = cap)
    (hadmissible : MatcherSubstAdmissible spec C T value) :
    MatcherValueTy spec mode Ξ' value cap (applyBoth C T target) := by
  cases h with
  | something =>
      exact MatcherValueTy.something
  | literal cert =>
      exact MatcherValueTy.literal
        (cert.substStable hcoupled hcap hadmissible)
  | product hs =>
      have hcaps := Cap.prod.inj hcap
      exact MatcherValueTy.product
        (MatcherValueTyList.substStable
          hs hcoupled hcaps hadmissible)

/-- List form of `MatcherValueTy.substStable`. -/
theorem MatcherValueTyList.substStable
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    {C : CapSubst} {T : TySubst}
    (h : MatcherValueTyList spec mode Ξ values caps targets)
    (hcoupled : CoupledSubstOK Ξ Ξ' C T)
    (hcaps : Cap.applyList C caps = caps)
    (hadmissible :
      MatcherSubstAdmissibleList spec C T values) :
    MatcherValueTyList spec mode Ξ' values caps
      (Ty.applyCapabilityList C (Ty.applyTargetList T targets)) := by
  cases h with
  | nil =>
      exact MatcherValueTyList.nil
  | cons hhead htail =>
      simp only [Cap.applyList, List.cons.injEq] at hcaps
      rcases hadmissible with ⟨hheadAdmissible, htailAdmissible⟩
      exact MatcherValueTyList.cons
        (MatcherValueTy.substStable
          hhead hcoupled hcaps.1 hheadAdmissible)
        (MatcherValueTyList.substStable
          htail hcoupled hcaps.2 htailAdmissible)

end

mutual

/-- Every intrinsically typed matcher value satisfies `CapTargetOK`. -/
theorem MatcherValueTy.capTargetOK
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    (h : MatcherValueTy spec mode Ξ value cap target) :
    CapTargetOK Ξ cap target := by
  cases h with
  | something =>
      exact CapTargetOK.none
  | literal cert =>
      exact cert.targetOK
  | product hs =>
      exact CapTargetOK.prod (MatcherValueTyList.capTargetOK hs)

/-- List form of `MatcherValueTy.capTargetOK`. -/
theorem MatcherValueTyList.capTargetOK
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : MatcherValueTyList spec mode Ξ values caps targets) :
    CapTargetOKList Ξ caps targets := by
  cases h with
  | nil =>
      exact CapTargetOKList.nil
  | cons hhead htail =>
      exact CapTargetOKList.cons
        (MatcherValueTy.capTargetOK hhead)
        (MatcherValueTyList.capTargetOK htail)

end

mutual

/-- Covered runtime matcher typing erases to ordinary typing. -/
theorem MatcherValueTy.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    (h : MatcherValueTy spec .covered Ξ value cap target) :
    MatcherValueTy spec .ordinary Ξ value cap target := by
  cases h with
  | something =>
      exact MatcherValueTy.something
  | literal cert =>
      exact MatcherValueTy.literal cert.toOrdinary
  | product hs =>
      exact MatcherValueTy.product (MatcherValueTyList.toOrdinary hs)

/-- List form of `MatcherValueTy.toOrdinary`. -/
theorem MatcherValueTyList.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : MatcherValueTyList spec .covered Ξ values caps targets) :
    MatcherValueTyList spec .ordinary Ξ values caps targets := by
  cases h with
  | nil =>
      exact MatcherValueTyList.nil
  | cons hhead htail =>
      exact MatcherValueTyList.cons
        (MatcherValueTy.toOrdinary hhead)
        (MatcherValueTyList.toOrdinary htail)

end

mutual

/--
Ξ-closed runtime matcher values preserve their intrinsic capability under
every admissible ordinary target specialization.
-/
theorem MatcherValueTy.targetSpecializeClosed
    {spec : RuntimeSpec} {mode : Mode}
    {value : Value} {cap : Cap} {target : Ty}
    (h : MatcherValueTy spec mode [] value cap target) (T : TySubst)
    (hadmissible :
      MatcherSubstAdmissible spec CapSubst.id T value) :
    MatcherValueTy spec mode [] value cap (target.applyTarget T) := by
  cases h with
  | something =>
      exact MatcherValueTy.something
  | literal cert =>
      exact MatcherValueTy.literal
        (cert.targetSpecializeClosed T hadmissible)
  | product hs =>
      exact MatcherValueTy.product
        (MatcherValueTyList.targetSpecializeClosed hs T hadmissible)

/-- List form of `MatcherValueTy.targetSpecializeClosed`. -/
theorem MatcherValueTyList.targetSpecializeClosed
    {spec : RuntimeSpec} {mode : Mode}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : MatcherValueTyList spec mode [] values caps targets) (T : TySubst)
    (hadmissible :
      MatcherSubstAdmissibleList spec CapSubst.id T values) :
    MatcherValueTyList spec mode [] values caps
      (Ty.applyTargetList T targets) := by
  cases h with
  | nil =>
      exact MatcherValueTyList.nil
  | cons hhead htail =>
      rcases hadmissible with ⟨hheadAdmissible, htailAdmissible⟩
      exact MatcherValueTyList.cons
        (MatcherValueTy.targetSpecializeClosed
          hhead T hheadAdmissible)
        (MatcherValueTyList.targetSpecializeClosed
          htail T htailAdmissible)

end

/-! ## Witness-threaded slot coercion -/

/--
A combined substitution aligns two target types.

This is intentionally proof-relevant at the slot boundary.  In an Algorithm W
integration the same `S` must also be applied to the environment, constraints,
and all remaining occurrences.
-/
def TargetCompatibleAt (S : Subst) (left right : Ty) : Prop :=
  S.apply left = S.apply right

/-- Existential target compatibility, useful only when the witness is retained. -/
def TargetCompatible (left right : Ty) : Prop :=
  ∃ S : Subst, TargetCompatibleAt S left right

/-- Target compatibility is reflexive. -/
theorem targetCompatible_refl (target : Ty) :
    TargetCompatible target target :=
  ⟨Subst.id, rfl⟩

/--
The substitution equations needed to consume one matcher value.

This predicate deliberately has no support premise.  A product coercion uses
one prevailing substitution for all components, so a component-local support
condition would reject bindings used by its siblings.  `SlotCoercionAt` adds
the support condition once, against the whole consumer capability.
-/
def CapAcceptsAt
    (C : CapSubst) (producer consumer : Cap) : Prop :=
  producer.apply C = producer ∧
  consumer.apply C = producer

/-- Forget the support premise of a one-way matching witness. -/
theorem OneWayAt.capAccepts
    {C : CapSubst} {producer consumer : Cap}
    (h : OneWayAt C producer consumer) :
    CapAcceptsAt C producer consumer :=
  h.2

/-- Add the whole-consumer support premise to the substitution equations. -/
theorem CapAcceptsAt.toOneWay
    {C : CapSubst} {producer consumer : Cap}
    (h : CapAcceptsAt C producer consumer)
    (hsupport : C.SupportWithin consumer.fcv) :
    OneWayAt C producer consumer :=
  ⟨hsupport, h⟩

mutual

/--
Typing of an already resolved runtime slot value.

This judgment contains no unresolved consumer index and no hidden
substitution.  A scalar is just an exact intrinsic matcher typing; a product
is componentwise.  `SlotCoercionAt.resolve` is the only bridge from raw slot
indices into this judgment.
-/
inductive SlotValueTy
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) :
    Value → Cap → Ty → Prop where
  | fromMatcher
      {value cap target} :
      MatcherValueTy spec mode Ξ value cap target →
      SlotValueTy spec mode Ξ value cap target
  | product {values caps targets} :
      SlotValueTyList spec mode Ξ values caps targets →
      SlotValueTy spec mode Ξ
        (.tuple values) (.prod caps) (.prod targets)

/-- Componentwise slot typing for product matcher values. -/
inductive SlotValueTyList
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) :
    List Value → List Cap → List Ty → Prop where
  | nil :
      SlotValueTyList spec mode Ξ [] [] []
  | cons {value cap target values caps targets} :
      SlotValueTy spec mode Ξ value cap target →
      SlotValueTyList spec mode Ξ values caps targets →
      SlotValueTyList spec mode Ξ
        (value :: values) (cap :: caps) (target :: targets)

end

mutual

/-- Every resolved slot value satisfies the capability/target invariant. -/
theorem SlotValueTy.capTargetOK
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    (h : SlotValueTy spec mode Ξ value cap target) :
    CapTargetOK Ξ cap target := by
  cases h with
  | fromMatcher hm =>
      exact hm.capTargetOK
  | product hs =>
      exact CapTargetOK.prod hs.capTargetOK

/-- List form of `SlotValueTy.capTargetOK`. -/
theorem SlotValueTyList.capTargetOK
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : SlotValueTyList spec mode Ξ values caps targets) :
    CapTargetOKList Ξ caps targets := by
  cases h with
  | nil =>
      exact CapTargetOKList.nil
  | cons hhead htail =>
      exact CapTargetOKList.cons hhead.capTargetOK htail.capTargetOK

end

mutual

/-- Covered slot typing erases to ordinary slot typing. -/
theorem SlotValueTy.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    (h : SlotValueTy spec .covered Ξ value cap target) :
    SlotValueTy spec .ordinary Ξ value cap target := by
  cases h with
  | fromMatcher hm =>
      exact SlotValueTy.fromMatcher hm.toOrdinary
  | product hs =>
      exact SlotValueTy.product (SlotValueTyList.toOrdinary hs)

/-- List form of `SlotValueTy.toOrdinary`. -/
theorem SlotValueTyList.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : SlotValueTyList spec .covered Ξ values caps targets) :
    SlotValueTyList spec .ordinary Ξ values caps targets := by
  cases h with
  | nil =>
      exact SlotValueTyList.nil
  | cons hhead htail =>
      exact SlotValueTyList.cons hhead.toOrdinary htail.toOrdinary

end

/--
Scalar resolved slot typing is exactly intrinsic matcher typing.
-/
theorem scalar_slot_value_invariant
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {value : Value} {cap : Cap} {target : Ty}
    (h : SlotValueTy spec mode Ξ value cap target)
    (hscalar : ∀ values, value ≠ .tuple values) :
    MatcherValueTy spec mode Ξ value cap target := by
  cases h with
  | fromMatcher hm =>
      exact hm
  | product hs =>
      exact False.elim (hscalar _ rfl)

/-! ## Shared-witness slot coercion -/

mutual

/--
Support-free coercion derivations under one fixed prevailing substitution.

The scalar rule stores producer stability, consumer resolution, and target
compatibility.  Every product component is checked under the same `S`.
-/
inductive SlotCoercionCoreAt
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) (S : Subst) :
    Value → Cap → Ty → Prop where
  | fromMatcher
      {value producer consumer producerTarget rawTarget} :
      MatcherValueTy spec mode Ξ value producer producerTarget →
      MatcherSubstAdmissible spec S.cap S.target value →
      CapAcceptsAt S.cap producer consumer →
      TargetCompatibleAt S producerTarget rawTarget →
      SlotCoercionCoreAt spec mode Ξ S value consumer rawTarget
  | product {values caps targets} :
      SlotCoercionAtList spec mode Ξ S values caps targets →
      SlotCoercionCoreAt spec mode Ξ S
        (.tuple values) (.prod caps) (.prod targets)

/-- Componentwise coercion premises, all threaded through the same `S`. -/
inductive SlotCoercionAtList
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) (S : Subst) :
    List Value → List Cap → List Ty → Prop where
  | nil :
      SlotCoercionAtList spec mode Ξ S [] [] []
  | cons {value cap target values caps targets} :
      SlotCoercionCoreAt spec mode Ξ S value cap target →
      SlotCoercionAtList spec mode Ξ S values caps targets →
      SlotCoercionAtList spec mode Ξ S
        (value :: values) (cap :: caps) (target :: targets)

end

/--
A raw slot coercion with one prevailing substitution and one aggregate
support condition.

For products, support is measured against the whole raw consumer capability.
It is intentionally not repeated on scalar components: the same substitution
may bind variables occurring in different siblings.
-/
structure SlotCoercionAt
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty)) (S : Subst)
    (value : Value) (rawConsumer : Cap) (rawTarget : Ty) : Prop where
  support : S.cap.SupportWithin rawConsumer.fcv
  core :
    SlotCoercionCoreAt spec mode Ξ S value rawConsumer rawTarget

/-- Build a scalar coercion from the public one-way relation. -/
def SlotCoercionAt.fromMatcher
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {S : Subst} {value : Value}
    {producer consumer : Cap} {producerTarget rawTarget : Ty}
    (hm : MatcherValueTy spec mode Ξ value producer producerTarget)
    (hadmissible :
      MatcherSubstAdmissible spec S.cap S.target value)
    (hcap : OneWayAt S.cap producer consumer)
    (htarget : TargetCompatibleAt S producerTarget rawTarget) :
    SlotCoercionAt spec mode Ξ S value consumer rawTarget where
  support := hcap.1
  core :=
    SlotCoercionCoreAt.fromMatcher
      hm hadmissible hcap.capAccepts htarget

/-- Build a product coercion with one aggregate support proof. -/
def SlotCoercionAt.product
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {S : Subst} {values : List Value}
    {caps : List Cap} {targets : List Ty}
    (hs : SlotCoercionAtList spec mode Ξ S values caps targets)
    (hsupport : S.cap.SupportWithin (Cap.prod caps).fcv) :
    SlotCoercionAt spec mode Ξ S
      (.tuple values) (.prod caps) (.prod targets) where
  support := hsupport
  core := SlotCoercionCoreAt.product hs

mutual

/-- Covered coercion premises erase to ordinary coercion premises. -/
theorem SlotCoercionCoreAt.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)} {S : Subst}
    {value : Value} {cap : Cap} {target : Ty}
    (h : SlotCoercionCoreAt spec .covered Ξ S value cap target) :
    SlotCoercionCoreAt spec .ordinary Ξ S value cap target := by
  cases h with
  | fromMatcher hm hadmissible hcap htarget =>
      exact SlotCoercionCoreAt.fromMatcher
        hm.toOrdinary hadmissible hcap htarget
  | product hs =>
      exact SlotCoercionCoreAt.product hs.toOrdinary

/-- List form of `SlotCoercionCoreAt.toOrdinary`. -/
theorem SlotCoercionAtList.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)} {S : Subst}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : SlotCoercionAtList spec .covered Ξ S values caps targets) :
    SlotCoercionAtList spec .ordinary Ξ S values caps targets := by
  cases h with
  | nil =>
      exact SlotCoercionAtList.nil
  | cons hhead htail =>
      exact SlotCoercionAtList.cons hhead.toOrdinary htail.toOrdinary

end

/-- Covered whole-slot coercion erases to ordinary coercion. -/
def SlotCoercionAt.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)} {S : Subst}
    {value : Value} {cap : Cap} {target : Ty}
    (h : SlotCoercionAt spec .covered Ξ S value cap target) :
    SlotCoercionAt spec .ordinary Ξ S value cap target where
  support := h.support
  core := h.core.toOrdinary

mutual

/--
Resolve a support-free coercion derivation under a valid coupled substitution.

The conclusion is actual resolved inhabitation at exactly
`rawConsumer.apply S.cap` and `S.apply rawTarget`.
-/
private theorem SlotCoercionCoreAt.resolve
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)} {S : Subst}
    {value : Value} {rawConsumer : Cap} {rawTarget : Ty}
    (h :
      SlotCoercionCoreAt spec mode Ξ S
        value rawConsumer rawTarget)
    (hcoupled : CoupledSubstOK Ξ Ξ' S.cap S.target) :
    SlotValueTy spec mode Ξ' value
      (rawConsumer.apply S.cap) (S.apply rawTarget) := by
  cases h with
  | fromMatcher hm hadmissible hcap htarget =>
      rcases hcap with ⟨hproducer, hconsumer⟩
      have hresolved :=
        hm.substStable hcoupled hproducer hadmissible
      have htargetBoth :
          applyBoth S.cap S.target _ =
            applyBoth S.cap S.target _ :=
        htarget
      rw [htargetBoth] at hresolved
      rw [hconsumer]
      exact SlotValueTy.fromMatcher hresolved
  | product hs =>
      exact SlotValueTy.product
        (SlotCoercionAtList.resolve hs hcoupled)

/-- List form of `SlotCoercionCoreAt.resolve`. -/
private theorem SlotCoercionAtList.resolve
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)} {S : Subst}
    {values : List Value} {caps : List Cap} {targets : List Ty}
    (h : SlotCoercionAtList spec mode Ξ S values caps targets)
    (hcoupled : CoupledSubstOK Ξ Ξ' S.cap S.target) :
    SlotValueTyList spec mode Ξ' values
      (Cap.applyList S.cap caps)
      (Ty.applyCapabilityList S.cap
        (Ty.applyTargetList S.target targets)) := by
  cases h with
  | nil =>
      exact SlotValueTyList.nil
  | cons hhead htail =>
      exact SlotValueTyList.cons
        (SlotCoercionCoreAt.resolve hhead hcoupled)
        (SlotCoercionAtList.resolve htail hcoupled)

end

/-- Resolve a whole-slot coercion at its retained prevailing substitution. -/
theorem SlotCoercionAt.resolve
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)} {S : Subst}
    {value : Value} {rawConsumer : Cap} {rawTarget : Ty}
    (h :
      SlotCoercionAt spec mode Ξ S value rawConsumer rawTarget)
    (hcoupled : CoupledSubstOK Ξ Ξ' S.cap S.target) :
    SlotValueTy spec mode Ξ' value
      (rawConsumer.apply S.cap) (S.apply rawTarget) :=
  h.core.resolve hcoupled

/--
The resolved indices of a valid slot coercion satisfy the syntactic
capability/target correspondence in the destination context.
-/
theorem SlotCoercionAt.resolvedCapTargetOK
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)} {S : Subst}
    {value : Value} {rawConsumer : Cap} {rawTarget : Ty}
    (h :
      SlotCoercionAt spec mode Ξ S value rawConsumer rawTarget)
    (hcoupled : CoupledSubstOK Ξ Ξ' S.cap S.target) :
    CapTargetOK Ξ'
      (rawConsumer.apply S.cap) (S.apply rawTarget) :=
  (h.resolve hcoupled).capTargetOK

/--
Invert a scalar raw-slot coercion.  At this outer boundary, aggregate support
is support for the scalar consumer itself, so the support-free equations
recover the public `OneWayAt` relation.
-/
theorem scalar_slot_coercion_invariant
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {S : Subst} {value : Value}
    {rawConsumer : Cap} {rawTarget : Ty}
    (h :
      SlotCoercionAt spec mode Ξ S value rawConsumer rawTarget)
    (hscalar : ∀ values, value ≠ .tuple values) :
    ∃ producer producerTarget,
      MatcherValueTy spec mode Ξ value producer producerTarget ∧
      OneWayAt S.cap producer rawConsumer ∧
      TargetCompatibleAt S producerTarget rawTarget := by
  rcases h with ⟨hsupport, hcore⟩
  cases hcore with
  | fromMatcher hm _ hcap htarget =>
      exact ⟨_, _, hm, hcap.toOneWay hsupport, htarget⟩
  | product hs =>
      exact False.elim (hscalar _ rfl)

/--
After a scalar coercion is resolved, the resulting indices are inhabited by
the same runtime matcher value in the destination correspondence context.
-/
theorem scalar_slot_resolved_invariant
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)} {S : Subst}
    {value : Value} {rawConsumer : Cap} {rawTarget : Ty}
    (h :
      SlotCoercionAt spec mode Ξ S value rawConsumer rawTarget)
    (hcoupled : CoupledSubstOK Ξ Ξ' S.cap S.target)
    (hscalar : ∀ values, value ≠ .tuple values) :
    MatcherValueTy spec mode Ξ' value
      (rawConsumer.apply S.cap) (S.apply rawTarget) :=
  scalar_slot_value_invariant (h.resolve hcoupled) hscalar

/-! ## Matcher-bearing environment invariant -/

/-- Type environment used by the P2 matcher-flow invariant. -/
abbrev MatcherCtx := List (String × Scheme)

/-- Lookup in a P2 matcher type environment. -/
def MatcherCtx.find? (Γ : MatcherCtx) (name : String) : Option Scheme :=
  (List.find? (fun entry => entry.1 == name) Γ).map (·.2)

/--
The matcher-bearing fragment of `EnvTyped`, explicitly conditional on the
chosen source/runtime bridge.
-/
def MatcherEnvTyped
    (spec : RuntimeSpec)
    (mode : Mode) (Ξ : List (Cap × Ty))
    (Γ : MatcherCtx) (ρ : Env) : Prop :=
  ∀ name value scheme,
    Env.find? ρ name = some value →
    MatcherCtx.find? Γ name = some scheme →
    ∀ cap target, scheme.Inst (.matcher cap target) →
      MatcherValueTy spec mode Ξ value cap target

/-- Covered matcher-bearing environments erase to ordinary environments. -/
theorem MatcherEnvTyped.toOrdinary
    {spec : RuntimeSpec} {Ξ : List (Cap × Ty)}
    {Γ : MatcherCtx} {ρ : Env}
    (h : MatcherEnvTyped spec .covered Ξ Γ ρ) :
    MatcherEnvTyped spec .ordinary Ξ Γ ρ := by
  intro name value scheme hvalue hscheme cap target hinst
  exact (h name value scheme hvalue hscheme cap target hinst).toOrdinary

/-- Direct lookup consequence of `MatcherEnvTyped`. -/
theorem matcherEnvTyped_lookup
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {Γ : MatcherCtx} {ρ : Env}
    (henv : MatcherEnvTyped spec mode Ξ Γ ρ)
    {name : String} {value : Value} {scheme : Scheme}
    (hvalue : Env.find? ρ name = some value)
    (hscheme : MatcherCtx.find? Γ name = some scheme)
    {cap : Cap} {target : Ty}
    (hinst : scheme.Inst (.matcher cap target)) :
    MatcherValueTy spec mode Ξ value cap target :=
  henv name value scheme hvalue hscheme cap target hinst

/--
An environment binding with the `something` scheme can never be looked up at
a strengthened constructor capability.
-/
theorem matcherEnvTyped_something_retains_none
    {spec : RuntimeSpec} {mode : Mode} {Ξ : List (Cap × Ty)}
    {Γ : MatcherCtx} {ρ : Env}
    (henv : MatcherEnvTyped spec mode Ξ Γ ρ)
    {name : String} {value : Value}
    (hvalue : Env.find? ρ name = some value)
    (hscheme : MatcherCtx.find? Γ name = some somethingScheme)
    {instanceTy : Ty}
    (hinst : somethingScheme.Inst instanceTy) :
    ∃ target,
      instanceTy = .matcher .none target ∧
      MatcherValueTy spec mode Ξ value .none target := by
  obtain ⟨target, hshape⟩ :=
    somethingScheme_instance_retains_none hinst
  subst instanceTy
  exact ⟨target, rfl,
    matcherEnvTyped_lookup henv hvalue hscheme hinst⟩

/-- Ordinary mode imposes no coverage obligation when the predicate is false. -/
theorem ordinary_allows_missing_coverage :
    CoverageReq .ordinary False :=
  True.intro

/-- Covered mode cannot certify a false coverage predicate. -/
theorem covered_rejects_missing_coverage :
    ¬ CoverageReq .covered False := by
  simp [CoverageReq]

end TypePM.P2
