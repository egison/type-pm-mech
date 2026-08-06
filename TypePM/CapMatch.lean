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
  | _, .any, bindings =>
      some bindings
  | producer, .var varId, bindings =>
      bindVar varId producer bindings
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
  | producer, .any, bindings, updated, hmatch => by
      simp only [matchCapAcc, Option.some.injEq] at hmatch
      subst updated
      exact Bindings.extends_refl bindings
  | producer, .var varId, bindings, updated, hmatch =>
      (bindVar_extends_and_lookup
        (by simpa only [matchCapAcc] using hmatch)).1
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
theorem matchCapAcc_demandMatches :
    ∀ (producer consumer : Cap) (bindings updated : Bindings),
      matchCapAcc producer consumer bindings = some updated →
      ∀ (S : CapSubst), updated.Agrees S →
        DemandMatches S producer consumer
  | producer, .any, bindings, updated, hmatch, S, hagrees => by
      cases producer <;> trivial
  | producer, .var varId, bindings, updated, hmatch, S, hagrees => by
      have hbind :
          bindVar varId producer bindings = some updated := by
        simpa only [matchCapAcc] using hmatch
      have hlookup := (bindVar_extends_and_lookup hbind).2
      have equality := hagrees varId producer hlookup
      cases producer <;> simpa [DemandMatches] using equality
  | producer, .skolem consumerId, bindings, updated, hmatch, _, _ => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case skolem producerId =>
        change producerId = consumerId
        exact hmatch.1
  | producer, .con consumerName consumerChildren, bindings, updated,
      hmatch, S, hagrees => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case con producerName producerChildren =>
        change producerName = consumerName ∧
          DemandMatchesList S producerChildren consumerChildren
        exact ⟨hmatch.1,
          matchCapListAcc_demandMatches _ _ _ _ hmatch.2 S hagrees⟩
  | producer, .prod consumerComponents, bindings, updated,
      hmatch, S, hagrees => by
      cases producer <;> simp [matchCapAcc] at hmatch
      case prod producerComponents =>
        change DemandMatchesList S producerComponents consumerComponents
        exact matchCapListAcc_demandMatches _ _ _ _ hmatch S hagrees

/-- List form of `matchCapAcc_demandMatches`. -/
theorem matchCapListAcc_demandMatches :
    ∀ (producers consumers : List Cap) (bindings updated : Bindings),
      matchCapListAcc producers consumers bindings = some updated →
      ∀ (S : CapSubst), updated.Agrees S →
        DemandMatchesList S producers consumers
  | [], [], bindings, updated, hmatch, _, _ => by
      trivial
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
        exact ⟨
          matchCapAcc_demandMatches _ _ _ _ hhead S hagreesIntermediate,
          matchCapListAcc_demandMatches _ _ _ _ hmatch S hagrees⟩
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
  | .any, _ =>
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

/-- Demand matching depends only on substitution values visible in the
original consumer syntax. -/
theorem demandMatches_congr_on_consumer (S₁ S₂ : CapSubst) :
    ∀ (producer consumer : Cap),
      DemandMatches S₁ producer consumer →
      (∀ varId ∈ consumer.fcv, S₁ varId = S₂ varId) →
      DemandMatches S₂ producer consumer := by
  intro currentProducer currentConsumer
  exact Cap.rec
    (motive_1 := fun consumer => ∀ producer,
      DemandMatches S₁ producer consumer →
      (∀ varId ∈ consumer.fcv, S₁ varId = S₂ varId) →
      DemandMatches S₂ producer consumer)
    (motive_2 := fun consumers => ∀ producers,
      DemandMatchesList S₁ producers consumers →
      (∀ varId ∈ Cap.fcvList consumers, S₁ varId = S₂ varId) →
      DemandMatchesList S₂ producers consumers)
    (by
      intro producer _ _
      cases producer <;> trivial)
    (fun _ => by
      intro producer matching agrees
      cases producer <;> simp_all [DemandMatches, Cap.fcv])
    (fun _ => by
      intro producer matching _
      cases producer <;> exact matching)
    (fun consumerName consumers consumersIH => by
      intro producer matching agrees
      cases producer <;> try contradiction
      rename_i producerName producers
      change producerName = consumerName ∧
        DemandMatchesList S₁ producers consumers at matching
      change producerName = consumerName ∧
        DemandMatchesList S₂ producers consumers
      exact ⟨matching.1, consumersIH _ matching.2 (by
        intro varId membership
        exact agrees varId (by simpa [Cap.fcv] using membership))⟩)
    (fun consumers consumersIH => by
      intro producer matching agrees
      cases producer <;> try contradiction
      rename_i producers
      change DemandMatchesList S₁ producers consumers at matching
      change DemandMatchesList S₂ producers consumers
      exact consumersIH _ matching (by
        intro varId membership
        exact agrees varId (by simpa [Cap.fcv] using membership)))
    (by
      intro producers matching _
      cases producers <;> try contradiction
      trivial)
    (fun _ _ consumerIH consumersIH => by
      intro producers matching agrees
      cases producers with
      | nil => contradiction
      | cons producer producers =>
          simp only [DemandMatchesList] at matching ⊢
          exact ⟨
            consumerIH producer matching.1 (by
              intro varId membership
              exact agrees varId (by simp [Cap.fcvList, membership])),
            consumersIH producers matching.2 (by
              intro varId membership
              exact agrees varId (by simp [Cap.fcvList, membership]))⟩)
    currentConsumer currentProducer

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
      DemandMatches unrestricted producer consumer :=
    matchCapAcc_demandMatches producer consumer [] bindings hacc
      unrestricted bindings.toSubst_agrees
  refine ⟨restricted,
    Bindings.toSubstWithin_support consumer.fcv bindings,
    hchecked.2, ?_⟩
  exact demandMatches_congr_on_consumer unrestricted restricted
    producer consumer hunrestricted (by
      intro varId membership
      simp [restricted, unrestricted, Bindings.toSubstWithin, membership])

/-- Soundness at the exact support-restricted substitution returned by the
executable matcher. -/
theorem matchCap_restricted_sound
    {producer consumer : Cap} {bindings : Bindings}
    (hmatch : matchCap producer consumer = some bindings) :
    OneWayAt (bindings.toSubstWithin consumer.fcv) producer consumer := by
  let unrestricted := bindings.toSubst
  let restricted := bindings.toSubstWithin consumer.fcv
  have checked :=
    (matchCap_eq_some_iff producer consumer bindings).mp hmatch
  have rawMatching : DemandMatches unrestricted producer consumer :=
    matchCapAcc_demandMatches producer consumer [] bindings checked.1
      unrestricted bindings.toSubst_agrees
  refine ⟨Bindings.toSubstWithin_support consumer.fcv bindings,
    checked.2, ?_⟩
  exact demandMatches_congr_on_consumer unrestricted restricted
    producer consumer rawMatching (by
      intro varId membership
      simp [restricted, unrestricted, Bindings.toSubstWithin, membership])

mutual

/-- Declarative demand matching is complete for the accumulator matcher. -/
theorem matchCapAcc_complete (S : CapSubst) :
    ∀ (producer consumer : Cap) (bindings : Bindings),
      bindings.Agrees S → DemandMatches S producer consumer →
      ∃ updated,
        matchCapAcc producer consumer bindings = some updated ∧
        updated.Agrees S
  | producer, .any, bindings, hagrees, matching => by
      cases producer <;> exact ⟨bindings, rfl, hagrees⟩
  | producer, .var varId, bindings, hagrees, matching => by
      have matchingEq : S varId = producer := by
        cases producer <;> simpa [DemandMatches] using matching
      rcases bindVar_complete S hagrees with
        ⟨updated, hbind, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      rw [matchingEq] at hbind
      simpa only [matchCapAcc] using hbind
  | producer, .skolem consumerId, bindings, hagrees, matching => by
      cases producer <;> try contradiction
      rename_i producerId
      change producerId = consumerId at matching
      subst consumerId
      exact ⟨bindings, by simp [matchCapAcc], hagrees⟩
  | producer, .con consumerName consumerChildren, bindings, hagrees,
      matching => by
      cases producer <;> try contradiction
      rename_i producerName producerChildren
      change producerName = consumerName ∧
        DemandMatchesList S producerChildren consumerChildren at matching
      rcases matchCapListAcc_complete S producerChildren consumerChildren
          bindings hagrees matching.2 with
        ⟨updated, hmatch, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      rw [matching.1]
      simpa [matchCapAcc] using hmatch
  | producer, .prod consumerComponents, bindings, hagrees, matching => by
      cases producer <;> try contradiction
      rename_i producerComponents
      change DemandMatchesList S producerComponents consumerComponents at matching
      rcases matchCapListAcc_complete S producerComponents consumerComponents
          bindings hagrees matching with
        ⟨updated, hmatch, hagreesUpdated⟩
      exact ⟨updated, by simpa only [matchCapAcc] using hmatch,
        hagreesUpdated⟩

/-- List form of `matchCapAcc_complete`. -/
theorem matchCapListAcc_complete (S : CapSubst) :
    ∀ (producers consumers : List Cap) (bindings : Bindings),
      bindings.Agrees S → DemandMatchesList S producers consumers →
      ∃ updated,
        matchCapListAcc producers consumers bindings = some updated ∧
        updated.Agrees S
  | [], [], bindings, hagrees, matching =>
      ⟨bindings, rfl, hagrees⟩
  | [], _ :: _, bindings, hagrees, matching => by contradiction
  | _ :: _, [], bindings, hagrees, matching => by contradiction
  | producer :: producers, consumer :: consumers, bindings, hagrees,
      matching => by
      rcases matchCapAcc_complete S producer consumer bindings hagrees
          matching.1 with
        ⟨intermediate, hhead, hagreesIntermediate⟩
      rcases matchCapListAcc_complete S producers consumers intermediate
          hagreesIntermediate matching.2 with
        ⟨updated, htail, hagreesUpdated⟩
      refine ⟨updated, ?_, hagreesUpdated⟩
      simp only [matchCapListAcc]
      rw [hhead]
      exact htail

end

/-- Every declarative one-way match is accepted by the executable matcher. -/
theorem matchCap_complete
    {producer consumer : Cap} (hmatch : OneWay producer consumer) :
    ∃ bindings, matchCap producer consumer = some bindings := by
  rcases hmatch with
    ⟨S, hsupport, hproducerStable, hdemand⟩
  have hempty : Bindings.Agrees S [] := by
    intro varId capability hlookup
    simp [Bindings.lookup] at hlookup
  rcases matchCapAcc_complete S producer consumer [] hempty hdemand with
    ⟨bindings, hraw, _⟩
  have hfiniteDemand :
      DemandMatches bindings.toSubst producer consumer :=
    matchCapAcc_demandMatches producer consumer [] bindings hraw
      bindings.toSubst bindings.toSubst_agrees
  have hagreesOnConsumer :
      ∀ varId ∈ consumer.fcv, bindings.toSubst varId = S varId :=
    demandMatches_unique_on_consumer bindings.toSubst S producer consumer
      hfiniteDemand hdemand
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
  have hfinite :
      DemandMatches bindings.toSubst producer consumer :=
    matchCapAcc_demandMatches producer consumer [] bindings hacc
      bindings.toSubst bindings.toSubst_agrees
  exact demandMatches_unique_on_consumer bindings.toSubst S producer consumer
    hfinite hdeclarative.2.2

/-! ## Executable regressions -/

example :
    matchCap (.con "List" [.any]) (.var 0) =
      some [(0, .con "List" [.any])] := by
  rfl

example :
    matchCap .any (.con "List" [.any]) = none := by
  rfl

example :
    matchCap (.con "List" [.any]) .any = some [] := by
  rfl

example :
    matchCap
      (.prod [.any, .con "K" []])
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

/-- An explicit nested `Any` ignores exactly its producer subtree. -/
example :
    matchCap
      (.prod [.con "Ignored" [.skolem 9], .con "K" []])
      (.prod [.any, .var 0]) =
      some [(0, .con "K" [])] := by
  rfl

/-- A consumer variable may bind to the ground `Any` producer. -/
example : matchCap .any (.var 0) = some [(0, .any)] := by
  rfl

/-- Binding a repeated variable to `Any` does not make its next occurrence a
wildcard. -/
example :
    matchCap (.prod [.any, .con "K" []])
      (.prod [.var 0, .var 0]) = none := by
  rfl

/-- Explicit `Any` remains independent of repeated-variable sharing. -/
example :
    matchCap
      (.prod [.con "Ignored" [], .con "K" [], .con "K" []])
      (.prod [.any, .var 0, .var 0]) =
      some [(0, .con "K" [])] := by
  rfl

end CapMatch
end TypePM
