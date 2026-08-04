import TypePM.Relation

/-!
# Executable one-way capability matching

The matcher is producer-first.  Only variables in the consumer capability are
bindable; every producer node is treated as input data.  Bindings are finite
association lists, and repeated consumer variables must receive exactly the
same producer subtree.  A successful raw match is rejected if those bindings
would rewrite the producer.
-/

namespace TypePM
namespace CapMatch

/-- A finite substitution for consumer capability variables. -/
abbrev Bindings := List (CapVar × Cap)

/-- Look up the first binding for a capability variable. -/
def Bindings.lookup (varId : CapVar) : Bindings → Option Cap
  | [] => none
  | (candidate, capability) :: rest =>
      if varId = candidate then some capability else lookup varId rest

/-- Interpret finite bindings as an identity-defaulting total substitution. -/
def Bindings.toSubst (bindings : Bindings) : CapSubst :=
  fun varId =>
    match bindings.lookup varId with
    | some capability => capability
    | none            => .var varId

/--
Restrict finite bindings to an explicit support, using the identity elsewhere.
-/
def Bindings.toSubstWithin
    (variables : List CapVar) (bindings : Bindings) : CapSubst :=
  fun varId =>
    if varId ∈ variables then bindings.toSubst varId else .var varId

/-- A total substitution agrees with every entry visible in finite bindings. -/
def Bindings.Agrees (S : CapSubst) (bindings : Bindings) : Prop :=
  ∀ varId capability,
    bindings.lookup varId = some capability → S varId = capability

/-- Every binding visible in `older` remains visible in `newer`. -/
def Bindings.Extends (newer older : Bindings) : Prop :=
  ∀ varId capability,
    older.lookup varId = some capability →
      newer.lookup varId = some capability

/--
Bind a consumer variable once, or check exact agreement with its prior
binding.
-/
def bindVar
    (varId : CapVar) (producer : Cap) (bindings : Bindings) :
    Option Bindings :=
  match bindings.lookup varId with
  | none =>
      some ((varId, producer) :: bindings)
  | some previous =>
      if previous = producer then some bindings else none

mutual

/-- Match a producer capability against a consumer capability. -/
def matchCapAcc : Cap → Cap → Bindings → Option Bindings
  | producer, .var varId, bindings =>
      bindVar varId producer bindings
  | .none, .none, bindings =>
      some bindings
  | .skolem producerId, .skolem consumerId, bindings =>
      if producerId = consumerId then some bindings else none
  | .con producerName producerChildren,
      .con consumerName consumerChildren, bindings =>
      if producerName = consumerName then
        matchCapListAcc producerChildren consumerChildren bindings
      else
        none
  | .prod producerComponents, .prod consumerComponents, bindings =>
      matchCapListAcc producerComponents consumerComponents bindings
  | _, _, _ =>
      none

/-- Match equal-length capability lists from left to right. -/
def matchCapListAcc : List Cap → List Cap → Bindings → Option Bindings
  | [], [], bindings =>
      some bindings
  | producer :: producers, consumer :: consumers, bindings =>
      match matchCapAcc producer consumer bindings with
      | some updated => matchCapListAcc producers consumers updated
      | none         => none
  | _, _, _ =>
      none

end

/--
Run one-way matching from an empty finite substitution.

The raw consumer match is accepted only if its support-restricted substitution
also leaves the producer unchanged.
-/
def matchCap (producer consumer : Cap) : Option Bindings :=
  match matchCapAcc producer consumer [] with
  | none =>
      none
  | some bindings =>
      let S := bindings.toSubstWithin consumer.fcv
      if producer.apply S = producer then some bindings else none

/-- Characterization of the producer-stability check performed by `matchCap`. -/
theorem matchCap_eq_some_iff
    (producer consumer : Cap) (bindings : Bindings) :
    matchCap producer consumer = some bindings ↔
      matchCapAcc producer consumer [] = some bindings ∧
      producer.apply (bindings.toSubstWithin consumer.fcv) = producer := by
  unfold matchCap
  split
  next hraw =>
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      rw [hraw] at h
      cases h
  next rawBindings hraw =>
    dsimp only
    split
    next hstable =>
      constructor
      · intro hresult
        have heq : rawBindings = bindings :=
          Option.some.inj hresult
        subst bindings
        exact ⟨hraw, hstable⟩
      · rintro ⟨hraw', hstable'⟩
        have heq : rawBindings = bindings := by
          rw [hraw] at hraw'
          exact Option.some.inj hraw'
        subst bindings
        rfl
    next hnotstable =>
      constructor
      · intro h
        cases h
      · rintro ⟨hraw', hstable⟩
        have heq : rawBindings = bindings := by
          rw [hraw] at hraw'
          exact Option.some.inj hraw'
        subst bindings
        exact (hnotstable hstable).elim

@[simp] theorem Bindings.lookup_self
    (varId : CapVar) (capability : Cap) (rest : Bindings) :
    Bindings.lookup varId ((varId, capability) :: rest) = some capability := by
  simp [Bindings.lookup]

theorem Bindings.lookup_cons_of_ne
    {varId candidate : CapVar} (h : varId ≠ candidate)
    (capability : Cap) (rest : Bindings) :
    Bindings.lookup varId ((candidate, capability) :: rest) =
      Bindings.lookup varId rest := by
  simp [Bindings.lookup, h]

theorem Bindings.extends_refl (bindings : Bindings) :
    bindings.Extends bindings := by
  intro varId capability h
  exact h

theorem Bindings.extends_trans
    {newest newer older : Bindings}
    (hnew : newest.Extends newer) (hold : newer.Extends older) :
    newest.Extends older := by
  intro varId capability h
  exact hnew varId capability (hold varId capability h)

theorem Bindings.agrees_of_extends
    {S : CapSubst} {newer older : Bindings}
    (hextends : newer.Extends older) (hagrees : newer.Agrees S) :
    older.Agrees S := by
  intro varId capability h
  exact hagrees varId capability (hextends varId capability h)

theorem Bindings.toSubst_agrees (bindings : Bindings) :
    bindings.Agrees bindings.toSubst := by
  intro varId capability h
  simp [Bindings.toSubst, h]

theorem Bindings.toSubstWithin_support
    (variables : List CapVar) (bindings : Bindings) :
    (bindings.toSubstWithin variables).SupportWithin variables := by
  intro varId hnotmem
  simp [Bindings.toSubstWithin, hnotmem]

theorem bindVar_extends_and_lookup
    {varId : CapVar} {producer : Cap} {bindings updated : Bindings}
    (hmatch : bindVar varId producer bindings = some updated) :
    updated.Extends bindings ∧
      updated.lookup varId = some producer := by
  unfold bindVar at hmatch
  split at hmatch
  next hnone =>
    simp only [Option.some.injEq] at hmatch
    subst updated
    constructor
    · intro candidate capability hlookup
      simp only [Bindings.lookup]
      split
      next heq =>
        subst candidate
        rw [hnone] at hlookup
        cases hlookup
      next _ =>
        exact hlookup
    · exact Bindings.lookup_self varId producer bindings
  next previous hsome =>
    split at hmatch
    next heq =>
      simp only [Option.some.injEq] at hmatch
      subst updated
      constructor
      · exact Bindings.extends_refl bindings
      · simpa [heq] using hsome
    next _ =>
      cases hmatch

theorem bindVar_complete
    (S : CapSubst) {varId : CapVar} {bindings : Bindings}
    (hagrees : bindings.Agrees S) :
    ∃ updated,
      bindVar varId (S varId) bindings = some updated ∧
      updated.Agrees S := by
  unfold bindVar
  split
  next hnone =>
    refine ⟨(varId, S varId) :: bindings, rfl, ?_⟩
    intro candidate capability hlookup
    simp only [Bindings.lookup] at hlookup
    split at hlookup
    next heq =>
      subst candidate
      exact Option.some.inj hlookup
    next _ =>
      exact hagrees candidate capability hlookup
  next previous hsome =>
    have heq : previous = S varId :=
      (hagrees varId previous hsome).symm
    refine ⟨bindings, ?_, hagrees⟩
    simp [heq]

mutual

/-- Successful matching preserves every incoming binding. -/
theorem matchCapAcc_extends :
    ∀ (producer consumer : Cap) (bindings updated : Bindings),
      matchCapAcc producer consumer bindings = some updated →
      updated.Extends bindings
  | producer, .var varId, bindings, updated, hmatch =>
      (bindVar_extends_and_lookup
        (by simpa only [matchCapAcc] using hmatch)).1
  | producer, .none, bindings, updated, hmatch => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case none =>
        subst updated
        exact Bindings.extends_refl bindings
  | producer, .skolem consumerId, bindings, updated, hmatch => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case skolem producerId =>
        rcases hmatch with ⟨_, hbindings⟩
        subst updated
        exact Bindings.extends_refl bindings
  | producer, .con consumerName consumerChildren, bindings, updated,
      hmatch => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case con producerName producerChildren =>
        exact matchCapListAcc_extends _ _ _ _ hmatch.2
  | producer, .prod consumerComponents, bindings, updated, hmatch => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case prod producerComponents =>
        exact matchCapListAcc_extends _ _ _ _ hmatch

/-- Successful list matching preserves every incoming binding. -/
theorem matchCapListAcc_extends :
    ∀ (producers consumers : List Cap) (bindings updated : Bindings),
      matchCapListAcc producers consumers bindings = some updated →
      updated.Extends bindings
  | [], [], bindings, updated, hmatch => by
      simp only [matchCapListAcc, Option.some.injEq] at hmatch
      subst updated
      exact Bindings.extends_refl bindings
  | [], _ :: _, _, _, hmatch => by
      simp [matchCapListAcc] at hmatch
  | _ :: _, [], _, _, hmatch => by
      simp [matchCapListAcc] at hmatch
  | producer :: producers, consumer :: consumers, bindings, updated,
      hmatch => by
      simp only [matchCapListAcc] at hmatch
      split at hmatch
      next intermediate hhead =>
        exact Bindings.extends_trans
          (matchCapListAcc_extends _ _ _ _ hmatch)
          (matchCapAcc_extends _ _ _ _ hhead)
      next _ =>
        cases hmatch

end

mutual

/--
Every successful capability match is respected by any total substitution that
agrees with the returned finite bindings.
-/
theorem matchCapAcc_apply_eq :
    ∀ (producer consumer : Cap) (bindings updated : Bindings),
      matchCapAcc producer consumer bindings = some updated →
      ∀ (S : CapSubst), updated.Agrees S →
        consumer.apply S = producer
  | producer, .var varId, bindings, updated, hmatch, S, hagrees => by
      have hbind :
          bindVar varId producer bindings = some updated := by
        simpa only [matchCapAcc] using hmatch
      have hlookup := (bindVar_extends_and_lookup hbind).2
      simpa only [Cap.apply] using hagrees varId producer hlookup
  | producer, .none, bindings, updated, hmatch, _, _ => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case none =>
        rfl
  | producer, .skolem consumerId, bindings, updated, hmatch, _, _ => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case skolem producerId =>
        exact congrArg Cap.skolem hmatch.1.symm
  | producer, .con consumerName consumerChildren, bindings, updated,
      hmatch, S, hagrees => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case con producerName producerChildren =>
        have hchildren :
            Cap.applyList S consumerChildren = producerChildren :=
          matchCapListAcc_apply_eq _ _ _ _ hmatch.2 S hagrees
        simp only [Cap.apply, Cap.con.injEq]
        exact ⟨hmatch.1.symm, hchildren⟩
  | producer, .prod consumerComponents, bindings, updated,
      hmatch, S, hagrees => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case prod producerComponents =>
        exact congrArg Cap.prod
          (matchCapListAcc_apply_eq _ _ _ _ hmatch S hagrees)

/-- List form of `matchCapAcc_apply_eq`. -/
theorem matchCapListAcc_apply_eq :
    ∀ (producers consumers : List Cap) (bindings updated : Bindings),
      matchCapListAcc producers consumers bindings = some updated →
      ∀ (S : CapSubst), updated.Agrees S →
        Cap.applyList S consumers = producers
  | [], [], bindings, updated, hmatch, _, _ => by
      rfl
  | [], _ :: _, _, _, hmatch, _, _ => by
      simp [matchCapListAcc] at hmatch
  | _ :: _, [], _, _, hmatch, _, _ => by
      simp [matchCapListAcc] at hmatch
  | producer :: producers, consumer :: consumers, bindings, updated,
      hmatch, S, hagrees => by
      simp only [matchCapListAcc] at hmatch
      split at hmatch
      next intermediate hhead =>
        have hextends :
            updated.Extends intermediate :=
          matchCapListAcc_extends _ _ _ _ hmatch
        have hagreesIntermediate : intermediate.Agrees S :=
          Bindings.agrees_of_extends hextends hagrees
        have hheadApply :
            consumer.apply S = producer :=
          matchCapAcc_apply_eq _ _ _ _ hhead S hagreesIntermediate
        have htailApply :
            Cap.applyList S consumers = producers :=
          matchCapListAcc_apply_eq _ _ _ _ hmatch S hagrees
        simp [Cap.applyList, hheadApply, htailApply]
      next _ =>
        cases hmatch

end

mutual

/--
Capability application depends only on the substitution's values at variables
that occur in the capability.
-/
theorem apply_congr_on_fcv (S₁ S₂ : CapSubst) :
    ∀ (capability : Cap),
      (∀ varId ∈ capability.fcv, S₁ varId = S₂ varId) →
      capability.apply S₁ = capability.apply S₂
  | .none, _ =>
      rfl
  | .var varId, hagrees => by
      simpa only [Cap.apply] using
        hagrees varId (by simp [Cap.fcv])
  | .skolem _, _ =>
      rfl
  | .con name children, hagrees => by
      simp only [Cap.apply]
      congr 1
      exact applyList_congr_on_fcv S₁ S₂ children
        (by
          intro varId hmem
          exact hagrees varId (by simpa [Cap.fcv] using hmem))
  | .prod components, hagrees => by
      simp only [Cap.apply]
      congr 1
      exact applyList_congr_on_fcv S₁ S₂ components
        (by
          intro varId hmem
          exact hagrees varId (by simpa [Cap.fcv] using hmem))

/-- List form of `apply_congr_on_fcv`. -/
theorem applyList_congr_on_fcv (S₁ S₂ : CapSubst) :
    ∀ (capabilities : List Cap),
      (∀ varId ∈ Cap.fcvList capabilities, S₁ varId = S₂ varId) →
      Cap.applyList S₁ capabilities = Cap.applyList S₂ capabilities
  | [], _ =>
      rfl
  | capability :: capabilities, hagrees => by
      simp only [Cap.applyList, List.cons.injEq]
      constructor
      · exact apply_congr_on_fcv S₁ S₂ capability
          (by
            intro varId hmem
            exact hagrees varId
              (by simp [Cap.fcvList, hmem]))
      · exact applyList_congr_on_fcv S₁ S₂ capabilities
          (by
            intro varId hmem
            exact hagrees varId
              (by simp [Cap.fcvList, hmem]))

end

/-- Algorithmic success is sound for the declarative one-way relation. -/
theorem matchCap_sound
    {producer consumer : Cap} {bindings : Bindings}
    (hmatch : matchCap producer consumer = some bindings) :
    OneWay producer consumer := by
  let unrestricted := bindings.toSubst
  let restricted := bindings.toSubstWithin consumer.fcv
  have hchecked :=
    (matchCap_eq_some_iff producer consumer bindings).mp hmatch
  have hacc :
      matchCapAcc producer consumer [] = some bindings := by
    exact hchecked.1
  have hunrestricted :
      consumer.apply unrestricted = producer :=
    matchCapAcc_apply_eq producer consumer [] bindings hacc
      unrestricted bindings.toSubst_agrees
  refine ⟨restricted,
    Bindings.toSubstWithin_support consumer.fcv bindings,
    hchecked.2, ?_⟩
  calc
    consumer.apply restricted =
        consumer.apply unrestricted := by
      apply apply_congr_on_fcv
      intro varId hmem
      simp [restricted, unrestricted, Bindings.toSubstWithin, hmem]
    _ = producer := hunrestricted

mutual

/--
Matching a capability obtained by applying `S` always succeeds when the
incoming finite bindings already agree with `S`.
-/
theorem matchCapAcc_apply_complete (S : CapSubst) :
    ∀ (consumer : Cap) (bindings : Bindings),
      bindings.Agrees S →
      ∃ updated,
        matchCapAcc (consumer.apply S) consumer bindings = some updated ∧
        updated.Agrees S
  | .none, bindings, hagrees =>
      ⟨bindings, rfl, hagrees⟩
  | .var varId, bindings, hagrees => by
      rcases bindVar_complete S hagrees with
        ⟨updated, hbind, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      simpa only [Cap.apply, matchCapAcc] using hbind
  | .skolem _, bindings, hagrees =>
      ⟨bindings, by simp [Cap.apply, matchCapAcc], hagrees⟩
  | .con name children, bindings, hagrees => by
      rcases matchCapListAcc_apply_complete S children bindings hagrees with
        ⟨updated, hmatch, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      simpa [Cap.apply, matchCapAcc] using hmatch
  | .prod components, bindings, hagrees => by
      rcases matchCapListAcc_apply_complete S components bindings hagrees with
        ⟨updated, hmatch, hagreesUpdated⟩
      exact ⟨updated, by simpa only [Cap.apply, matchCapAcc] using hmatch,
        hagreesUpdated⟩

/-- List form of `matchCapAcc_apply_complete`. -/
theorem matchCapListAcc_apply_complete (S : CapSubst) :
    ∀ (consumers : List Cap) (bindings : Bindings),
      bindings.Agrees S →
      ∃ updated,
        matchCapListAcc (Cap.applyList S consumers) consumers bindings =
          some updated ∧
        updated.Agrees S
  | [], bindings, hagrees =>
      ⟨bindings, rfl, hagrees⟩
  | consumer :: consumers, bindings, hagrees => by
      rcases matchCapAcc_apply_complete S consumer bindings hagrees with
        ⟨intermediate, hhead, hagreesIntermediate⟩
      rcases matchCapListAcc_apply_complete S consumers intermediate
          hagreesIntermediate with
        ⟨updated, htail, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      simp only [Cap.applyList, matchCapListAcc]
      rw [hhead]
      exact htail

end

/-- Every declarative one-way match is accepted by the executable matcher. -/
theorem matchCap_complete
    {producer consumer : Cap} (hmatch : OneWay producer consumer) :
    ∃ bindings, matchCap producer consumer = some bindings := by
  rcases hmatch with
    ⟨S, hsupport, hproducerStable, hconsumerApply⟩
  have hempty : Bindings.Agrees S [] := by
    intro varId capability hlookup
    simp [Bindings.lookup] at hlookup
  rcases matchCapAcc_apply_complete S consumer [] hempty with
    ⟨bindings, halgorithm, _⟩
  have hraw :
      matchCapAcc producer consumer [] = some bindings := by
    rw [← hconsumerApply]
    exact halgorithm
  have hfiniteApply :
      consumer.apply bindings.toSubst = producer :=
    matchCapAcc_apply_eq producer consumer [] bindings hraw
      bindings.toSubst bindings.toSubst_agrees
  have hagreesOnConsumer :
      ∀ varId ∈ consumer.fcv, bindings.toSubst varId = S varId :=
    Cap.apply_eq_on_fcv bindings.toSubst S consumer
      (hfiniteApply.trans hconsumerApply.symm)
  have hrestrictedStable :
      producer.apply (bindings.toSubstWithin consumer.fcv) = producer := by
    calc
      producer.apply (bindings.toSubstWithin consumer.fcv) =
          producer.apply S := by
        apply apply_congr_on_fcv
        intro varId hproducerMem
        by_cases hconsumerMem : varId ∈ consumer.fcv
        · simpa [Bindings.toSubstWithin, hconsumerMem] using
            hagreesOnConsumer varId hconsumerMem
        · have hfixed := hsupport varId hconsumerMem
          simp [Bindings.toSubstWithin, hconsumerMem, hfixed]
      _ = producer := hproducerStable
  refine ⟨bindings, ?_⟩
  exact (matchCap_eq_some_iff producer consumer bindings).mpr
    ⟨hraw, hrestrictedStable⟩

/-- Executable success is equivalent to declarative one-way matching. -/
theorem matchCap_succeeds_iff_oneWay (producer consumer : Cap) :
    (∃ bindings, matchCap producer consumer = some bindings) ↔
      OneWay producer consumer := by
  constructor
  · rintro ⟨bindings, hmatch⟩
    exact matchCap_sound hmatch
  · exact matchCap_complete

/--
The returned finite substitution agrees with every declarative witness on all
consumer variables.
-/
theorem matchCap_toSubst_unique_on_consumer
    {producer consumer : Cap} {bindings : Bindings} {S : CapSubst}
    (halgorithm : matchCap producer consumer = some bindings)
    (hdeclarative : OneWayAt S producer consumer) :
    ∀ varId ∈ consumer.fcv, bindings.toSubst varId = S varId := by
  have hacc :
      matchCapAcc producer consumer [] = some bindings := by
    exact
      ((matchCap_eq_some_iff producer consumer bindings).mp
        halgorithm).1
  have happly :
      consumer.apply bindings.toSubst = producer :=
    matchCapAcc_apply_eq producer consumer [] bindings hacc
      bindings.toSubst bindings.toSubst_agrees
  exact Cap.apply_eq_on_fcv bindings.toSubst S consumer
    (happly.trans hdeclarative.2.2.symm)

/-! ## Executable regressions -/

example :
    matchCap (.con "List" [.none]) (.var 0) =
      some [(0, .con "List" [.none])] := by
  rfl

example :
    matchCap .none (.con "List" [.none]) = none := by
  rfl

example :
    matchCap (.con "List" [.none]) .none = none := by
  rfl

example :
    matchCap
      (.prod [.none, .con "K" []])
      (.prod [.var 0, .var 0]) =
      none := by
  rfl

example :
    matchCap
      (.prod [.con "K" [], .con "K" []])
      (.prod [.var 0, .var 0]) =
      some [(0, .con "K" [])] := by
  rfl

example :
    matchCap (.var 7) (.var 0) = some [(0, .var 7)] := by
  rfl

example :
    matchCap (.var 0) (.var 0) = some [(0, .var 0)] := by
  rfl

example :
    matchCap (.con "List" [.var 0]) (.var 0) = none := by
  rfl

example :
    matchCap (.var 7) (.con "K" []) = none := by
  rfl

end CapMatch
end TypePM
