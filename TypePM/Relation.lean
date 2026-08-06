import TypePM.Substitution

/-!
# Relations and two-sorted schemes

This file keeps structural matcher capabilities separate from ordinary target
types.  In particular, one-way capability matching may instantiate only
variables occurring in the consumer capability.  `Any` is a wildcard only at
an explicit consumer node; all other ground heads are rigid.
-/

namespace TypePM

/-! ## Free variables -/

mutual

/-- Flexible capability variables occurring in a capability. -/
def Cap.fcv : Cap → List CapVar
  | .any          => []
  | .var a        => [a]
  | .skolem _     => []
  | .con _ caps   => Cap.fcvList caps
  | .prod caps    => Cap.fcvList caps

/-- Flexible capability variables occurring in a list of capabilities. -/
def Cap.fcvList : List Cap → List CapVar
  | []          => []
  | cap :: caps => cap.fcv ++ Cap.fcvList caps

end

mutual

/-- Flexible capability variables occurring anywhere in a two-sorted type. -/
def Ty.fcv : Ty → List CapVar
  | .var _         => []
  | .skolem _      => []
  | .unit          => []
  | .int           => []
  | .bool          => []
  | .data _ tys    => Ty.fcvList tys
  | .prod tys      => Ty.fcvList tys
  | .fn dom cod    => dom.fcv ++ cod.fcv
  | .matcher c τ   => c.fcv ++ τ.fcv
  | .slot c τ      => c.fcv ++ τ.fcv

/-- Flexible capability variables occurring in a list of two-sorted types. -/
def Ty.fcvList : List Ty → List CapVar
  | []        => []
  | τ :: tys  => τ.fcv ++ Ty.fcvList tys

end

mutual

/-- Ordinary target-type variables occurring in a two-sorted type. -/
def Ty.ftv : Ty → List TypePM.TyVar
  | .var a         => [a]
  | .skolem _      => []
  | .unit          => []
  | .int           => []
  | .bool          => []
  | .data _ tys    => Ty.ftvList tys
  | .prod tys      => Ty.ftvList tys
  | .fn dom cod    => dom.ftv ++ cod.ftv
  | .matcher _ τ   => τ.ftv
  | .slot _ τ      => τ.ftv

/-- Ordinary target-type variables occurring in a list of two-sorted types. -/
def Ty.ftvList : List Ty → List TypePM.TyVar
  | []        => []
  | τ :: tys  => τ.ftv ++ Ty.ftvList tys

end

/-- Free capability variables of a scheme, excluding its capability binders. -/
def Scheme.fcv (σ : Scheme) : List CapVar :=
  σ.body.fcv.filter fun a => a ∉ σ.capBinders

/-- Free ordinary type variables of a scheme, excluding its type binders. -/
def Scheme.ftv (σ : Scheme) : List TypePM.TyVar :=
  σ.body.ftv.filter fun a => a ∉ σ.tyBinders

/-- Every capability-variable name occurring in a scheme, including binders. -/
def Scheme.allCapVars (σ : Scheme) : List CapVar :=
  σ.capBinders ++ σ.body.fcv

/-- Every ordinary-variable name occurring in a scheme, including binders. -/
def Scheme.allTyVars (σ : Scheme) : List TypePM.TyVar :=
  σ.tyBinders ++ σ.body.ftv

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

/-! ## Two-sorted scheme instantiation -/

/--
An explicit instantiation witness.  Capability and target substitutions have
separate support conditions and separate binder lists.  The paired witness
also satisfies the paper's range-fixed condition.
-/
def Scheme.InstAt (C : CapSubst) (T : TySubst)
    (σ : Scheme) (τ : Ty) : Prop :=
  C.SupportWithin σ.capBinders ∧
  T.SupportWithin σ.tyBinders ∧
  (Subst.mk C T).RangeFixed ∧
  (Subst.mk C T).apply σ.body = τ

/-- Two-sorted scheme instantiation. -/
def Scheme.Inst (σ : Scheme) (τ : Ty) : Prop :=
  ∃ C T, σ.InstAt C T τ

/-- Every scheme instantiates to its body using identity substitutions. -/
theorem Scheme.inst_refl (σ : Scheme) : σ.Inst σ.body := by
  refine ⟨CapSubst.id, TySubst.id,
    CapSubst.id_supportWithin σ.capBinders,
    TySubst.id_supportWithin σ.tyBinders,
    Subst.id_rangeFixed, ?_⟩
  exact Subst.apply_id σ.body

/-- An instantiation cannot substitute an unbound capability variable. -/
theorem Scheme.InstAt.cap_fixed {C : CapSubst} {T : TySubst}
    {σ : Scheme} {τ : Ty} (h : σ.InstAt C T τ)
    {a : CapVar} (ha : a ∉ σ.capBinders) :
    C a = .var a :=
  h.1 a ha

/-- An instantiation cannot substitute an unbound ordinary type variable. -/
theorem Scheme.InstAt.target_fixed {C : CapSubst} {T : TySubst}
    {σ : Scheme} {τ : Ty} (h : σ.InstAt C T τ)
    {a : TypePM.TyVar} (ha : a ∉ σ.tyBinders) :
    T a = .var a :=
  h.2.1 a ha

/-- Every explicit instantiation witness is range-fixed. -/
theorem Scheme.InstAt.range_fixed {C : CapSubst} {T : TySubst}
    {σ : Scheme} {τ : Ty} (h : σ.InstAt C T τ) :
    (Subst.mk C T).RangeFixed :=
  h.2.2.1

/--
The two support facts exposed together make the sort separation of
instantiation explicit.
-/
theorem Scheme.InstAt.separate_support {C : CapSubst} {T : TySubst}
    {σ : Scheme} {τ : Ty} (h : σ.InstAt C T τ) :
    (∀ a, a ∉ σ.capBinders → C a = .var a) ∧
    (∀ a, a ∉ σ.tyBinders → T a = .var a) :=
  ⟨h.1, h.2.1⟩

/--
Ordinary target substitution preserves the root capability of a matcher.
-/
theorem targetSubst_preserves_matcher_cap (T : TySubst)
    (cap : Cap) (τ : Ty) :
    (Ty.matcher cap τ).applyTarget T =
      Ty.matcher cap (τ.applyTarget T) :=
  rfl

/-- The principal scheme for `something`. -/
def somethingScheme : Scheme :=
  ⟨[], [0], .matcher .any (.var 0)⟩

/--
Every instance of `∀a. Matcher Any a` retains `Any`, independently of its
ordinary target instance.
-/
theorem somethingScheme_instance_retains_any {τ : Ty}
    (h : somethingScheme.Inst τ) :
    ∃ target, τ = .matcher .any target := by
  rcases h with ⟨C, T, _, _, _, hbody⟩
  refine ⟨T 0, ?_⟩
  have hshape :
      Ty.matcher .any (T 0) = τ := by
    simpa [somethingScheme, Subst.apply, Ty.applyTarget,
      Ty.applyCapability, Cap.apply] using hbody
  exact hshape.symm

/-- The shared-target-variable scheme `∀a. a -> Matcher Any a`. -/
def sharedSomethingFunctionScheme : Scheme :=
  ⟨[], [0], .fn (.var 0) (.matcher .any (.var 0))⟩

/--
Every instance of `∀a. a -> Matcher Any a` keeps both occurrences of the
ordinary target equal while retaining the `Any` capability.
-/
theorem sharedSomethingFunctionScheme_instance_retains_any {τ : Ty}
    (h : sharedSomethingFunctionScheme.Inst τ) :
    ∃ target, τ = .fn target (.matcher .any target) := by
  rcases h with ⟨C, T, _, _, _, hbody⟩
  refine ⟨T 0, ?_⟩
  have hshape :
      Ty.fn (T 0) (.matcher .any (T 0)) = τ := by
    simpa [sharedSomethingFunctionScheme, Subst.apply, Ty.applyTarget,
      Ty.applyCapability, Cap.apply] using hbody
  exact hshape.symm

/-- A scheme binding only capability variable zero. -/
def capOnlyExampleScheme : Scheme :=
  ⟨[0], [], .matcher (.var 0) (.var 0)⟩

/--
Binding capability variable zero does not bind the ordinary type variable with
the same numeric name.
-/
theorem capOnlyExampleScheme_preserves_target_var {τ : Ty}
    (h : capOnlyExampleScheme.Inst τ) :
    ∃ cap, τ = .matcher cap (.var 0) := by
  rcases h with ⟨C, T, hC, hT, _, hbody⟩
  have hTid : T = TySubst.id := by
    funext a
    exact hT a (by simp [capOnlyExampleScheme])
  subst T
  refine ⟨C 0, ?_⟩
  have hshape : Ty.matcher (C 0) (.var 0) = τ := by
    simpa [capOnlyExampleScheme, Subst.apply, Ty.applyTarget_id,
      Ty.applyCapability, Cap.apply] using hbody
  exact hshape.symm

/-- A scheme binding only ordinary type variable zero. -/
def targetOnlyExampleScheme : Scheme :=
  ⟨[], [0], .matcher (.var 0) (.var 0)⟩

/--
Binding ordinary type variable zero does not bind the capability variable with
the same numeric name.
-/
theorem targetOnlyExampleScheme_preserves_cap_var {τ : Ty}
    (h : targetOnlyExampleScheme.Inst τ) :
    ∃ target, τ = .matcher (.var 0) target := by
  rcases h with ⟨C, T, hC, hT, _, hbody⟩
  have hCid : C = CapSubst.id := by
    funext a
    exact hC a (by simp [targetOnlyExampleScheme])
  subst C
  refine ⟨T 0, ?_⟩
  have hshape : Ty.matcher (.var 0) (T 0) = τ := by
    simpa [targetOnlyExampleScheme, Subst.apply,
      Ty.applyCapability_id, Ty.applyTarget, Cap.apply] using hbody
  exact hshape.symm

/-! ## Generalization relative to explicit environment free variables -/

/-- Keep one occurrence of every variable, retaining the last occurrence. -/
def uniqueVars {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | item :: items =>
      if item ∈ items then
        uniqueVars items
      else
        item :: uniqueVars items

@[simp] theorem mem_uniqueVars {α : Type} [DecidableEq α]
    {item : α} {items : List α} :
    item ∈ uniqueVars items ↔ item ∈ items := by
  induction items with
  | nil =>
      simp [uniqueVars]
  | cons head tail ih =>
      simp only [uniqueVars]
      split <;> simp_all

theorem uniqueVars_nodup {α : Type} [DecidableEq α]
    (items : List α) :
    (uniqueVars items).Nodup := by
  induction items with
  | nil =>
      simp [uniqueVars]
  | cons head tail ih =>
      simp only [uniqueVars]
      split <;> rename_i hmem
      · exact ih
      · constructor
        · intro item hitem heq
          subst item
          exact hmem (mem_uniqueVars.mp hitem)
        · exact ih

/--
Generalize exactly the body variables not free in the surrounding environment.
Binder lists are duplicate-free, matching their set-like role in the paper and
preventing annotation checking from allocating unused duplicate skolems.
-/
def generalize (envCaps : List CapVar) (envTypes : List TypePM.TyVar)
    (τ : Ty) : Scheme :=
  ⟨uniqueVars (τ.fcv.filter (fun a => a ∉ envCaps)),
    uniqueVars (τ.ftv.filter (fun a => a ∉ envTypes)),
    τ⟩

/-- A generalized capability binder is not free in the environment. -/
theorem mem_generalize_capBinders_not_env {envCaps : List CapVar}
    {envTypes : List TypePM.TyVar} {τ : Ty} {a : CapVar}
    (h : a ∈ (generalize envCaps envTypes τ).capBinders) :
    a ∉ envCaps := by
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp h)).2

/-- A generalized type binder is not free in the environment. -/
theorem mem_generalize_tyBinders_not_env {envCaps : List CapVar}
    {envTypes : List TypePM.TyVar} {τ : Ty} {a : TypePM.TyVar}
    (h : a ∈ (generalize envCaps envTypes τ).tyBinders) :
    a ∉ envTypes := by
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp h)).2

/-- Every non-environment capability variable of the body is generalized. -/
theorem mem_generalize_capBinders {envCaps : List CapVar}
    {envTypes : List TypePM.TyVar} {τ : Ty} {a : CapVar}
    (hbody : a ∈ τ.fcv) (henv : a ∉ envCaps) :
    a ∈ (generalize envCaps envTypes τ).capBinders := by
  exact mem_uniqueVars.mpr
    (List.mem_filter.mpr ⟨hbody, by simp [henv]⟩)

/-- Every non-environment ordinary type variable of the body is generalized. -/
theorem mem_generalize_tyBinders {envCaps : List CapVar}
    {envTypes : List TypePM.TyVar} {τ : Ty} {a : TypePM.TyVar}
    (hbody : a ∈ τ.ftv) (henv : a ∉ envTypes) :
    a ∈ (generalize envCaps envTypes τ).tyBinders := by
  exact mem_uniqueVars.mpr
    (List.mem_filter.mpr ⟨hbody, by simp [henv]⟩)

/-- Generalization never introduces duplicate capability binders. -/
theorem generalize_capBinders_nodup
    (envCaps : List CapVar) (envTypes : List TypePM.TyVar) (τ : Ty) :
    (generalize envCaps envTypes τ).capBinders.Nodup := by
  exact uniqueVars_nodup _

/-- Generalization never introduces duplicate ordinary binders. -/
theorem generalize_tyBinders_nodup
    (envCaps : List CapVar) (envTypes : List TypePM.TyVar) (τ : Ty) :
    (generalize envCaps envTypes τ).tyBinders.Nodup := by
  exact uniqueVars_nodup _

/--
If the environment already contains every free variable of the body,
generalization is the monomorphic scheme.
-/
theorem generalize_all_free_is_mono (τ : Ty) :
    generalize τ.fcv τ.ftv τ = Scheme.mono τ := by
  have hcap :
      uniqueVars (τ.fcv.filter (fun a => a ∉ τ.fcv)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have hfiltered := mem_uniqueVars.mp ha
    simp at hfiltered
  have hty :
      uniqueVars (τ.ftv.filter (fun a => a ∉ τ.ftv)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have hfiltered := mem_uniqueVars.mp ha
    simp at hfiltered
  simp only [generalize, Scheme.mono]
  rw [hcap, hty]

end TypePM
