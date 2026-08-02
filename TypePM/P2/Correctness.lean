import TypePM.P2.Annotation
import TypePM.P2.CapMatch
import TypePM.P2.Observability
import TypePM.P2.Projection
import TypePM.P2.Recursion
import TypePM.P2.CoreSpec

/-!
# P2 core correctness composition

This module composes the executable and declarative P2 layers.  Algebraic
lemmas remain parametric in the reusable `RuntimeSpec` proof kernel, while
`CoreSpecWF` is the public non-CAS source boundary: it deterministically
generates evidence from each actual clause and derives the runtime
specification rather than postulating an arbitrary evidence relation.
-/

namespace TypePM.P2
namespace Correctness

/--
The finite substitution returned by the executable capability matcher is the
exact producer-stable witness required by `OneWayAt`.
-/
theorem matchCap_oneWayAt
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    (hmatch : CapMatch.matchCap producer consumer = some bindings) :
    OneWayAt
      (bindings.toSubstWithin consumer.fcv) producer consumer := by
  let unrestricted := bindings.toSubst
  let restricted := bindings.toSubstWithin consumer.fcv
  have hchecked :=
    (CapMatch.matchCap_eq_some_iff producer consumer bindings).mp hmatch
  have hunrestricted :
      consumer.apply unrestricted = producer :=
    CapMatch.matchCapAcc_apply_eq producer consumer [] bindings
      hchecked.1 unrestricted bindings.toSubst_agrees
  refine ⟨bindings.toSubstWithin_support consumer.fcv,
    hchecked.2, ?_⟩
  calc
    consumer.apply restricted =
        consumer.apply unrestricted := by
      apply CapMatch.apply_congr_on_fcv
      intro varId hmem
      simp [restricted, unrestricted,
        CapMatch.Bindings.toSubstWithin, hmem]
    _ = producer := hunrestricted

/--
Two components that share consumer variable `p` under one prevailing witness
must agree on their producer capability.
-/
theorem shared_consumer_producers_agree
    {S : Subst} {p : CapVar} {leftProducer rightProducer : Cap}
    (leftMatch :
      CapAcceptsAt S.cap leftProducer (.var p))
    (rightMatch :
      CapAcceptsAt S.cap rightProducer (.var p)) :
    leftProducer = rightProducer := by
  have left_eq : S.cap p = leftProducer := by
    simpa only [Cap.apply] using leftMatch.2
  have right_eq : S.cap p = rightProducer := by
    simpa only [Cap.apply] using rightMatch.2
  exact left_eq.symm.trans right_eq

/--
Equivalently, incompatible producer capabilities cannot occupy two components
that share consumer variable `p` under the same prevailing substitution.
-/
theorem shared_consumer_rejects_incompatible_producers
    {S : Subst} {p : CapVar} {leftProducer rightProducer : Cap}
    (hincompatible : leftProducer ≠ rightProducer) :
    ¬ (CapAcceptsAt S.cap leftProducer (.var p) ∧
        CapAcceptsAt S.cap rightProducer (.var p)) := by
  rintro ⟨leftMatch, rightMatch⟩
  exact hincompatible
    (shared_consumer_producers_agree leftMatch rightMatch)

/--
Turn executable capability matching into the witness-threaded runtime slot
rule.

Both indices in the conclusion are the indices after applying the retained
witness.  In particular, the raw consumer capability is not returned.
-/
theorem algorithmic_slot_resolves
    {spec : RuntimeSpec} {mode : Mode}
    {Ξ Ξ' : List (Cap × Ty)}
    {value : Value}
    {producer consumer : Cap}
    {producerTarget slotTarget : Ty}
    {bindings : CapMatch.Bindings}
    (hvalue :
      MatcherValueTy spec mode Ξ value producer producerTarget)
    (T : TySubst)
    (hadmissible :
      MatcherSubstAdmissible spec
        (bindings.toSubstWithin consumer.fcv) T value)
    (hmatch :
      CapMatch.matchCap producer consumer = some bindings)
    (hcoupled :
      CoupledSubstOK Ξ Ξ'
        (bindings.toSubstWithin consumer.fcv) T)
    (htarget :
      TargetCompatibleAt
        (Subst.mk (bindings.toSubstWithin consumer.fcv) T)
        producerTarget slotTarget) :
    SlotValueTy spec mode Ξ' value
      (consumer.apply (bindings.toSubstWithin consumer.fcv))
      ((Subst.mk
        (bindings.toSubstWithin consumer.fcv) T).apply slotTarget) :=
  (SlotCoercionAt.fromMatcher
    hvalue hadmissible (matchCap_oneWayAt hmatch) htarget).resolve hcoupled

/-! ## `something` at a flexible and a rigid consumer -/

/-- The retained witness when `something` is consumed through capability `p`. -/
def somethingConsumerSubst (p : CapVar) : Subst :=
  Subst.mk
    (CapMatch.Bindings.toSubstWithin
      [p] ([(p, Cap.none)] : CapMatch.Bindings))
    TySubst.id

@[simp] theorem something_matches_consumer_var (p : CapVar) :
    CapMatch.matchCap .none (.var p) =
      some [(p, .none)] := by
  simp [CapMatch.matchCap, CapMatch.matchCapAcc, CapMatch.bindVar,
    CapMatch.Bindings.lookup, Cap.apply]

/--
The flexible-consumer regression retains the actual raw coercion judgment and
its prevailing witness; it is not merely an inhabitance fact about
`something` at an arbitrary resolved target.
-/
theorem something_consumer_var_coercion
    {spec : RuntimeSpec} {mode : Mode}
    (p : CapVar) (target : Ty) :
    SlotCoercionAt spec mode [] (somethingConsumerSubst p)
      .something (.var p) target := by
  apply SlotCoercionAt.fromMatcher
  · exact MatcherValueTy.something (target := target)
  · trivial
  · simpa [somethingConsumerSubst, Cap.fcv] using
      matchCap_oneWayAt (something_matches_consumer_var p)
  · rfl

/--
`something` consumed through a flexible capability has resolved capability
`none`; its target is the target after applying the retained witness.
-/
theorem something_resolves_consumer_var
    {spec : RuntimeSpec} {mode : Mode}
    (p : CapVar) (target : Ty) :
    SlotValueTy spec mode [] .something .none
      ((somethingConsumerSubst p).apply target) := by
  have hslot :=
    (something_consumer_var_coercion
      (spec := spec) (mode := mode) p target).resolve
      (coupledSubstOK_nil _ _)
  simpa [somethingConsumerSubst, Cap.fcv, Cap.apply,
    CapMatch.Bindings.toSubstWithin, CapMatch.Bindings.toSubst,
    CapMatch.Bindings.lookup] using hslot

/-- A rigid structured consumer cannot accept `something`'s `none` producer. -/
theorem something_rejects_structured_consumer
    (name : String) (children : List Cap) :
    CapMatch.matchCap .none (.con name children) = none := by
  rfl

/-- Declarative form of `something_rejects_structured_consumer`. -/
theorem something_not_oneWay_structured
    (name : String) (children : List Cap) :
    ¬ OneWay .none (.con name children) :=
  not_oneWay_none_con name children

/-! ## Separate instantiation of the open List matcher combinator -/

/--
The P2 scheme
`forall p a. Slot p a -> Matcher (List p) (List a)`.
-/
def listSlotMatcherScheme : Scheme :=
  ⟨[0], [0],
    .fn
      (.slot (.var 0) (.var 0))
      (.matcher
        (.con "List" [.var 0])
        (.data "List" [.var 0]))⟩

/-- Instantiate the capability parameter `p` with `none`. -/
def pNoneSubst : CapSubst :=
  fun varId => if varId = 0 then .none else .var varId

/-- Instantiate the ordinary target parameter `a` with `int`. -/
def aIntSubst : TySubst :=
  fun varId => if varId = 0 then .int else .var varId

theorem pNoneSubst_support :
    pNoneSubst.SupportWithin [0] := by
  intro varId hnotmem
  have hne : varId ≠ 0 := by
    simpa using hnotmem
  simp [pNoneSubst, hne]

theorem aIntSubst_support :
    aIntSubst.SupportWithin [0] := by
  intro varId hnotmem
  have hne : varId ≠ 0 := by
    simpa using hnotmem
  simp [aIntSubst, hne]

/-- The complete result of substituting both quantified sorts. -/
@[simp] theorem listSlotMatcherScheme_apply_none_int :
    (Subst.mk pNoneSubst aIntSubst).apply
      listSlotMatcherScheme.body =
    Ty.fn
      (.slot .none .int)
      (.matcher
        (.con "List" [.none])
        (.data "List" [.int])) := by
  simp [listSlotMatcherScheme, pNoneSubst, aIntSubst,
    Subst.apply, Ty.applyTarget, Ty.applyTargetList,
    Ty.applyCapability, Ty.applyCapabilityList,
    Cap.apply, Cap.applyList]

/-- The scheme instantiation at `p = none` and `a = int`. -/
theorem listSlotMatcherScheme_inst_none_int :
    listSlotMatcherScheme.Inst
      (.fn
        (.slot .none .int)
        (.matcher
          (.con "List" [.none])
          (.data "List" [.int]))) := by
  refine ⟨pNoneSubst, aIntSubst,
    pNoneSubst_support, aIntSubst_support, ?_⟩
  exact listSlotMatcherScheme_apply_none_int

/-! ## Cross-layer regressions already established by the component proofs -/

/-- `something` cannot check the bad explicit capability-polymorphic scheme. -/
theorem bad_explicit_capability_annotation_rejected :
    ¬ Annotation.ChecksScheme Annotation.CheckScope.empty [] [1]
      (.matcher .none (.var 1))
      Annotation.badCapabilityScheme 0 0 :=
  Annotation.something_rejects_badCapabilityAnnotation

/--
Sharing an ordinary target variable cannot strengthen `something`'s
capability: every instance retains the same target on both occurrences and
keeps capability `none`.
-/
theorem shared_target_non_strengthening
    {instanceType : Ty}
    (hinst : sharedSomethingFunctionScheme.Inst instanceType) :
    ∃ target,
      instanceType = .fn target (.matcher .none target) :=
  sharedSomethingFunctionScheme_instance_retains_none hinst

end Correctness
end TypePM.P2
