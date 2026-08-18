import TypePM.Substitution
import TypePM.FreeVars
import TypePM.UniqueVars

/-!
# Capability relations

This file keeps structural matcher capabilities separate from ordinary target
types.  In particular, one-way capability matching may instantiate only
variables occurring in the consumer capability.  `Any` is a wildcard only at
an explicit consumer node; all other ground heads are rigid.
-/

namespace TypePM

/-! ## Capability renaming -/

mutual

/-- Rename flexible capability variables; rigid nodes are unchanged. -/
def Cap.applyRen (r : CapVar → CapVar) : Cap → Cap
  | .any          => .any
  | .var a        => .var (r a)
  | .skolem a     => .skolem a
  | .con n caps   => .con n (Cap.applyRenList r caps)
  | .prod caps    => .prod (Cap.applyRenList r caps)

/-- List form of `Cap.applyRen`. -/
def Cap.applyRenList (r : CapVar → CapVar) : List Cap → List Cap
  | []          => []
  | cap :: caps => cap.applyRen r :: Cap.applyRenList r caps

end

/-- A capability is a renaming of another capability. -/
def Cap.RenamesTo (consumer renamed : Cap) : Prop :=
  ∃ r : CapVar → CapVar,
    (∀ a b, r a = r b → a = b) ∧ consumer.applyRen r = renamed

mutual

/-- The identity renaming changes no capability. -/
theorem Cap.applyRen_id : ∀ cap : Cap, cap.applyRen id = cap
  | .any          => rfl
  | .var _        => rfl
  | .skolem _     => rfl
  | .con n caps   => by
      simp only [Cap.applyRen]
      rw [Cap.applyRenList_id caps]
  | .prod caps    => by
      simp only [Cap.applyRen]
      rw [Cap.applyRenList_id caps]

/-- List form of `Cap.applyRen_id`. -/
theorem Cap.applyRenList_id :
    ∀ caps : List Cap, Cap.applyRenList id caps = caps
  | []          => rfl
  | cap :: caps => by
      simp only [Cap.applyRenList]
      rw [Cap.applyRen_id cap, Cap.applyRenList_id caps]

end

mutual

/-- An injective variable renaming is injective on complete capabilities. -/
theorem Cap.applyRen_injective
    {r : CapVar → CapVar}
    (injective : ∀ left right, r left = r right → left = right) :
    ∀ {left right : Cap},
      left.applyRen r = right.applyRen r → left = right
  | .any, .any, _ => rfl
  | .var left, .var right, equality => by
      simp only [Cap.applyRen, Cap.var.injEq] at equality ⊢
      exact injective left right equality
  | .skolem left, .skolem right, equality => by
      simpa only [Cap.applyRen, Cap.skolem.injEq] using equality
  | .con leftName leftChildren, .con rightName rightChildren, equality => by
      simp only [Cap.applyRen, Cap.con.injEq] at equality ⊢
      exact ⟨equality.1,
        Cap.applyRenList_injective injective equality.2⟩
  | .prod leftComponents, .prod rightComponents, equality => by
      simp only [Cap.applyRen, Cap.prod.injEq] at equality ⊢
      exact Cap.applyRenList_injective injective equality
  | .any, .var _, equality
  | .any, .skolem _, equality
  | .any, .con _ _, equality
  | .any, .prod _, equality
  | .var _, .any, equality
  | .var _, .skolem _, equality
  | .var _, .con _ _, equality
  | .var _, .prod _, equality
  | .skolem _, .any, equality
  | .skolem _, .var _, equality
  | .skolem _, .con _ _, equality
  | .skolem _, .prod _, equality
  | .con _ _, .any, equality
  | .con _ _, .var _, equality
  | .con _ _, .skolem _, equality
  | .con _ _, .prod _, equality
  | .prod _, .any, equality
  | .prod _, .var _, equality
  | .prod _, .skolem _, equality
  | .prod _, .con _ _, equality => by
      contradiction

/-- List form of `Cap.applyRen_injective`. -/
theorem Cap.applyRenList_injective
    {r : CapVar → CapVar}
    (injective : ∀ left right, r left = r right → left = right) :
    ∀ {left right : List Cap},
      Cap.applyRenList r left = Cap.applyRenList r right → left = right
  | [], [], _ => rfl
  | left :: lefts, right :: rights, equality => by
      simp only [Cap.applyRenList, List.cons.injEq] at equality ⊢
      exact ⟨Cap.applyRen_injective injective equality.1,
        Cap.applyRenList_injective injective equality.2⟩
  | [], _ :: _, equality
  | _ :: _, [], equality => by
      contradiction

end

/-- Capability renaming is reflexive. -/
theorem Cap.renamesTo_refl (cap : Cap) : cap.RenamesTo cap := by
  refine ⟨id, ?_, Cap.applyRen_id cap⟩
  intro a b h
  exact h

/-! ## Support-restricted substitutions -/

/--
A capability substitution is the identity away from the listed variables.

Substitutions are represented as total functions, so this predicate is their
finite-support discipline.
-/
def CapSubst.SupportWithin (S : CapSubst) (vars : List CapVar) : Prop :=
  ∀ a, a ∉ vars → S a = .var a

/-- A target substitution is the identity away from the listed variables. -/
def TySubst.SupportWithin (S : TySubst)
    (vars : List TypePM.TyVar) : Prop :=
  ∀ a, a ∉ vars → S a = .var a

/-- The identity capability substitution has support within every set. -/
theorem CapSubst.id_supportWithin (vars : List CapVar) :
    CapSubst.id.SupportWithin vars := by
  intro a _
  rfl

/-- The identity target substitution has support within every set. -/
theorem TySubst.id_supportWithin (vars : List TypePM.TyVar) :
    TySubst.id.SupportWithin vars := by
  intro a _
  rfl

/-- Finite support is closed under target-substitution composition. -/
theorem TySubst.SupportWithin.comp
    {later earlier : TySubst}
    {earlierVars laterVars : List TypePM.TyVar}
    (earlierSupport : earlier.SupportWithin earlierVars)
    (laterSupport : later.SupportWithin laterVars) :
    (TySubst.comp later earlier).SupportWithin
      (earlierVars ++ laterVars) := by
  intro varId outside
  simp only [List.mem_append, not_or] at outside
  simp only [TySubst.comp, earlierSupport varId outside.1,
    Ty.applyTarget]
  exact laterSupport varId outside.2

/-! ## One-way capability matching -/

mutual

/--
Match a producer against the original consumer syntax under `S`.

Only an explicit consumer `Any` is a wildcard.  Consumer variables use strict
equality with their substitution image.  Consequently, if the same variable
occurs twice, binding it to `Any` at the first occurrence does not turn its
second occurrence into a wildcard.
-/
def DemandMatches (S : CapSubst) : Cap → Cap → Prop
  | _, .any => True
  | producer, .var varId => S varId = producer
  | .skolem producerId, .skolem consumerId =>
      producerId = consumerId
  | .con producerName producerChildren,
      .con consumerName consumerChildren =>
      producerName = consumerName ∧
        DemandMatchesList S producerChildren consumerChildren
  | .prod producerComponents, .prod consumerComponents =>
      DemandMatchesList S producerComponents consumerComponents
  | _, _ => False

/-- Pointwise list form of `DemandMatches`. -/
def DemandMatchesList (S : CapSubst) : List Cap → List Cap → Prop
  | [], [] => True
  | producer :: producers, consumer :: consumers =>
      DemandMatches S producer consumer ∧
        DemandMatchesList S producers consumers
  | _, _ => False

end

/--
`OneWayAt S producer consumer` means that the consumer can accept the producer
after instantiating only flexible variables of the consumer.

The order is producer first, consumer second.  Producer variables are never
instantiated by this witness: applying the same substitution must leave the
producer unchanged.
-/
def OneWayAt (S : CapSubst) (producer consumer : Cap) : Prop :=
  S.SupportWithin consumer.fcv ∧
  producer.apply S = producer ∧
  DemandMatches S producer consumer

/-- Existential one-way capability matching. -/
def OneWay (producer consumer : Cap) : Prop :=
  ∃ S, OneWayAt S producer consumer

/-- Every capability one-way matches itself. -/
theorem oneWay_refl (cap : Cap) : OneWay cap cap := by
  refine ⟨CapSubst.id, CapSubst.id_supportWithin cap.fcv, ?_, ?_⟩
  · exact Cap.apply_id cap
  · induction cap using Cap.rec
      (motive_2 := fun caps => DemandMatchesList CapSubst.id caps caps) with
    | any => trivial
    | var varId => rfl
    | skolem name => rfl
    | con name children childrenIH => exact ⟨rfl, childrenIH⟩
    | prod components componentsIH => exact componentsIH
    | nil => trivial
    | cons cap caps capIH capsIH => exact ⟨capIH, capsIH⟩

mutual

/--
If two substitutions produce the same capability, they agree on every
flexible variable visible in the source capability.
-/
theorem Cap.apply_eq_on_fcv (S₁ S₂ : CapSubst) (cap : Cap)
    (h : cap.apply S₁ = cap.apply S₂) :
    ∀ a ∈ cap.fcv, S₁ a = S₂ a := by
  cases cap with
  | any =>
      intro a ha
      simp [Cap.fcv] at ha
  | var b =>
      intro a ha
      simp only [Cap.fcv, List.mem_singleton] at ha
      subst a
      simpa [Cap.apply] using h
  | skolem b =>
      intro a ha
      simp [Cap.fcv] at ha
  | con n caps =>
      intro a ha
      have hlist :
          Cap.applyList S₁ caps = Cap.applyList S₂ caps := by
        simpa only [Cap.apply, Cap.con.injEq, true_and] using h
      exact Cap.applyList_eq_on_fcv S₁ S₂ caps hlist a
        (by simpa [Cap.fcv] using ha)
  | prod caps =>
      intro a ha
      have hlist :
          Cap.applyList S₁ caps = Cap.applyList S₂ caps := by
        simpa only [Cap.apply, Cap.prod.injEq] using h
      exact Cap.applyList_eq_on_fcv S₁ S₂ caps hlist a
        (by simpa [Cap.fcv] using ha)

/-- List form of `Cap.apply_eq_on_fcv`. -/
theorem Cap.applyList_eq_on_fcv (S₁ S₂ : CapSubst) (caps : List Cap)
    (h : Cap.applyList S₁ caps = Cap.applyList S₂ caps) :
    ∀ a ∈ Cap.fcvList caps, S₁ a = S₂ a := by
  cases caps with
  | nil =>
      intro a ha
      simp [Cap.fcvList] at ha
  | cons cap caps =>
      intro a ha
      simp only [Cap.applyList, List.cons.injEq] at h
      simp only [Cap.fcvList, List.mem_append] at ha
      rcases ha with ha | ha
      · exact Cap.apply_eq_on_fcv S₁ S₂ cap h.1 a ha
      · exact Cap.applyList_eq_on_fcv S₁ S₂ caps h.2 a ha

end

/-- Two demand witnesses agree on every variable in the original consumer. -/
theorem demandMatches_unique_on_consumer
    (S₁ S₂ : CapSubst) : ∀ (producer consumer : Cap),
      DemandMatches S₁ producer consumer →
      DemandMatches S₂ producer consumer →
      ∀ a ∈ consumer.fcv, S₁ a = S₂ a := by
  intro currentProducer currentConsumer
  exact Cap.rec
    (motive_1 := fun consumer => ∀ producer,
      DemandMatches S₁ producer consumer →
      DemandMatches S₂ producer consumer →
      ∀ a ∈ consumer.fcv, S₁ a = S₂ a)
    (motive_2 := fun consumers => ∀ producers,
      DemandMatchesList S₁ producers consumers →
      DemandMatchesList S₂ producers consumers →
      ∀ a ∈ Cap.fcvList consumers, S₁ a = S₂ a)
    (by
      intro _ _ _ a membership
      simp [Cap.fcv] at membership)
    (fun varId => by
      intro producer first second a membership
      cases producer <;> simp_all [DemandMatches, Cap.fcv])
    (fun _ => by
      intro _ _ _ a membership
      simp [Cap.fcv] at membership)
    (fun _ _ consumersIH => by
      intro producer first second a membership
      cases producer <;> try contradiction
      exact consumersIH _ first.2 second.2 a
        (by simpa [Cap.fcv] using membership))
    (fun _ consumersIH => by
      intro producer first second a membership
      cases producer <;> try contradiction
      exact consumersIH _ first second a
        (by simpa [Cap.fcv] using membership))
    (by
      intro _ _ _ a membership
      simp [Cap.fcvList] at membership)
    (fun _ _ consumerIH consumersIH => by
      intro producers first second a membership
      cases producers with
      | nil => contradiction
      | cons producer producers =>
          simp only [DemandMatchesList] at first second
          simp only [Cap.fcvList, List.mem_append] at membership
          rcases membership with head | tail
          · exact consumerIH producer first.1 second.1 a head
          · exact consumersIH producers first.2 second.2 a tail)
    currentConsumer currentProducer

/--
One-way witnesses are pointwise unique on every free consumer variable.

They may differ away from the consumer because substitutions are total
functions; this is the strongest unconditional extensional uniqueness claim.
-/
theorem oneWayAt_unique {S₁ S₂ : CapSubst} {producer consumer : Cap}
    (h₁ : OneWayAt S₁ producer consumer)
    (h₂ : OneWayAt S₂ producer consumer) :
    ∀ a ∈ consumer.fcv, S₁ a = S₂ a :=
  demandMatches_unique_on_consumer S₁ S₂ producer consumer
    h₁.2.2 h₂.2.2

/-- The minimal consumer demand accepts every stable producer. -/
theorem oneWay_consumer_any (producer : Cap) : OneWay producer .any := by
  refine ⟨CapSubst.id, CapSubst.id_supportWithin [], Cap.apply_id producer, ?_⟩
  cases producer <;> trivial

/-- `Any` is not a wildcard in producer position. -/
theorem not_oneWay_any_con (name : String) (caps : List Cap) :
    ¬ OneWay .any (.con name caps) := by
  rintro ⟨S, _, _, matching⟩
  exact matching

/-- Matching two known constructor capabilities preserves their head name. -/
theorem oneWay_con_head_eq {producerCaps consumerCaps : List Cap}
    {producerName consumerName : String}
    (h : OneWay (.con producerName producerCaps)
      (.con consumerName consumerCaps)) :
    producerName = consumerName := by
  rcases h with ⟨S, _, _, matching⟩
  exact matching.1

end TypePM
