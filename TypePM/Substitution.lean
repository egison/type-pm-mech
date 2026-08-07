import TypePM.Syntax

/-!
# Two-sorted substitutions

Capability substitutions and ordinary target substitutions are separate.
Ordinary substitution never rewrites an existing capability node.  Capability
substitution traverses every matcher and slot occurrence, including occurrences
nested in ordinary types.
-/

namespace TypePM

/-- A substitution for flexible capability variables. -/
abbrev CapSubst := CapVar → Cap

/-- A substitution for ordinary target-type variables. -/
abbrev TySubst := TypePM.TyVar → Ty

/-- The identity capability substitution. -/
def CapSubst.id : CapSubst :=
  Cap.var

/-- The identity target substitution. -/
def TySubst.id : TySubst :=
  Ty.var

mutual

/-- Apply a capability substitution to a capability. -/
def Cap.apply (S : CapSubst) : Cap → Cap
  | .any         => .any
  | .var a       => S a
  | .skolem a    => .skolem a
  | .con n caps  => .con n (Cap.applyList S caps)
  | .prod caps   => .prod (Cap.applyList S caps)

/-- Apply a capability substitution to a list of capabilities. -/
def Cap.applyList (S : CapSubst) : List Cap → List Cap
  | []          => []
  | cap :: caps => cap.apply S :: Cap.applyList S caps

end

mutual

/--
Apply an ordinary target substitution.

The capability argument of an existing matcher or slot is copied verbatim.
-/
def Ty.applyTarget (S : TySubst) : Ty → Ty
  | .var a        => S a
  | .skolem a     => .skolem a
  | .unit         => .unit
  | .int          => .int
  | .bool         => .bool
  | .data n tys   => .data n (Ty.applyTargetList S tys)
  | .prod tys     => .prod (Ty.applyTargetList S tys)
  | .fn dom cod   => .fn (dom.applyTarget S) (cod.applyTarget S)
  | .matcher c τ  => .matcher c (τ.applyTarget S)
  | .slot c τ     => .slot c (τ.applyTarget S)

/-- Apply an ordinary target substitution to a list of types. -/
def Ty.applyTargetList (S : TySubst) : List Ty → List Ty
  | []        => []
  | τ :: tys  => τ.applyTarget S :: Ty.applyTargetList S tys

end

mutual

/-- Apply a capability substitution throughout an ordinary type. -/
def Ty.applyCapability (S : CapSubst) : Ty → Ty
  | .var a        => .var a
  | .skolem a     => .skolem a
  | .unit         => .unit
  | .int          => .int
  | .bool         => .bool
  | .data n tys   => .data n (Ty.applyCapabilityList S tys)
  | .prod tys     => .prod (Ty.applyCapabilityList S tys)
  | .fn dom cod   => .fn (dom.applyCapability S) (cod.applyCapability S)
  | .matcher c τ  => .matcher (c.apply S) (τ.applyCapability S)
  | .slot c τ     => .slot (c.apply S) (τ.applyCapability S)

/-- Apply a capability substitution to a list of ordinary types. -/
def Ty.applyCapabilityList (S : CapSubst) : List Ty → List Ty
  | []        => []
  | τ :: tys  => τ.applyCapability S :: Ty.applyCapabilityList S tys

end

mutual

/--
Erase capability information while retaining the complete ordinary type
skeleton.
-/
def Ty.eraseCap : Ty → Ty
  | .var a        => .var a
  | .skolem a     => .skolem a
  | .unit         => .unit
  | .int          => .int
  | .bool         => .bool
  | .data n tys   => .data n (Ty.eraseCapList tys)
  | .prod tys     => .prod (Ty.eraseCapList tys)
  | .fn dom cod   => .fn dom.eraseCap cod.eraseCap
  | .matcher _ τ  => .matcher .any τ.eraseCap
  | .slot _ τ     => .slot .any τ.eraseCap

/-- Erase capability information from a list of types. -/
def Ty.eraseCapList : List Ty → List Ty
  | []        => []
  | τ :: tys  => τ.eraseCap :: Ty.eraseCapList tys

end

/-- Composition of capability substitutions, with `S₂` applied after `S₁`. -/
def CapSubst.comp (S₂ S₁ : CapSubst) : CapSubst :=
  fun a => (S₁ a).apply S₂

/-- Composition of target substitutions, with `S₂` applied after `S₁`. -/
def TySubst.comp (S₂ S₁ : TySubst) : TySubst :=
  fun a => (S₁ a).applyTarget S₂

/-- A pair of substitutions, one for each sort. -/
structure Subst where
  cap    : CapSubst
  target : TySubst

/-- The identity combined substitution. -/
def Subst.id : Subst :=
  ⟨CapSubst.id, TySubst.id⟩

/--
The target range of a paired substitution is fixed by its capability part.

This is the paper's explicit side condition `C (T α) = T α`.  It prevents a
target binding from smuggling in capability variables that the paired
capability substitution would still rewrite.
-/
def Subst.RangeFixed (S : Subst) : Prop :=
  ∀ a, (S.target a).applyCapability S.cap = S.target a

/--
Apply a combined substitution in capability-then-target order.

This is exactly the paper definition `S τ = T (C τ)`.
-/
def Subst.apply (S : Subst) (τ : Ty) : Ty :=
  (τ.applyCapability S.cap).applyTarget S.target

/--
Pointwise composition of the two sorted components.

Its semantic composition law requires the earlier target range to be fixed by
the later capability substitution; see `Subst.apply_comp`.
-/
def Subst.comp (S₂ S₁ : Subst) : Subst :=
  ⟨CapSubst.comp S₂.cap S₁.cap, TySubst.comp S₂.target S₁.target⟩

mutual

/-- Applying the identity capability substitution changes no capability. -/
theorem Cap.apply_id : ∀ (cap : Cap), cap.apply CapSubst.id = cap
  | .any        => rfl
  | .var _      => rfl
  | .skolem _   => rfl
  | .con n caps => by
      simp only [Cap.apply]
      rw [Cap.applyList_id caps]
  | .prod caps  => by
      simp only [Cap.apply]
      rw [Cap.applyList_id caps]

/-- List form of `Cap.apply_id`. -/
theorem Cap.applyList_id :
    ∀ (caps : List Cap), Cap.applyList CapSubst.id caps = caps
  | []          => rfl
  | cap :: caps => by
      simp only [Cap.applyList]
      rw [Cap.apply_id cap, Cap.applyList_id caps]

end

mutual

/-- Capability-substitution composition is respected by application. -/
theorem Cap.apply_comp (S₂ S₁ : CapSubst) :
    ∀ (cap : Cap),
      cap.apply (CapSubst.comp S₂ S₁) = (cap.apply S₁).apply S₂
  | .any        => rfl
  | .var _      => rfl
  | .skolem _   => rfl
  | .con n caps => by
      simp only [Cap.apply]
      rw [Cap.applyList_comp S₂ S₁ caps]
  | .prod caps  => by
      simp only [Cap.apply]
      rw [Cap.applyList_comp S₂ S₁ caps]

/-- List form of `Cap.apply_comp`. -/
theorem Cap.applyList_comp (S₂ S₁ : CapSubst) :
    ∀ (caps : List Cap),
      Cap.applyList (CapSubst.comp S₂ S₁) caps =
        Cap.applyList S₂ (Cap.applyList S₁ caps)
  | []          => rfl
  | cap :: caps => by
      simp only [Cap.applyList]
      rw [Cap.apply_comp S₂ S₁ cap, Cap.applyList_comp S₂ S₁ caps]

end

mutual

/-- Applying the identity target substitution changes no type. -/
theorem Ty.applyTarget_id : ∀ (τ : Ty), τ.applyTarget TySubst.id = τ
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_id tys]
  | .prod tys     => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_id tys]
  | .fn dom cod   => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_id dom, Ty.applyTarget_id cod]
  | .matcher c τ  => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_id τ]
  | .slot c τ     => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_id τ]

/-- List form of `Ty.applyTarget_id`. -/
theorem Ty.applyTargetList_id :
    ∀ (tys : List Ty), Ty.applyTargetList TySubst.id tys = tys
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyTargetList]
      rw [Ty.applyTarget_id τ, Ty.applyTargetList_id tys]

end

mutual

/-- Applying the identity capability substitution changes no type. -/
theorem Ty.applyCapability_id :
    ∀ (τ : Ty), τ.applyCapability CapSubst.id = τ
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapabilityList_id tys]
  | .prod tys     => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapabilityList_id tys]
  | .fn dom cod   => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapability_id dom, Ty.applyCapability_id cod]
  | .matcher c τ  => by
      simp only [Ty.applyCapability]
      rw [Cap.apply_id c, Ty.applyCapability_id τ]
  | .slot c τ     => by
      simp only [Ty.applyCapability]
      rw [Cap.apply_id c, Ty.applyCapability_id τ]

/-- List form of `Ty.applyCapability_id`. -/
theorem Ty.applyCapabilityList_id :
    ∀ (tys : List Ty), Ty.applyCapabilityList CapSubst.id tys = tys
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyCapabilityList]
      rw [Ty.applyCapability_id τ, Ty.applyCapabilityList_id tys]

end

mutual

/-- Target-substitution composition is respected by application. -/
theorem Ty.applyTarget_comp (S₂ S₁ : TySubst) :
    ∀ (τ : Ty),
      τ.applyTarget (TySubst.comp S₂ S₁) =
        (τ.applyTarget S₁).applyTarget S₂
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_comp S₂ S₁ tys]
  | .prod tys     => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_comp S₂ S₁ tys]
  | .fn dom cod   => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_comp S₂ S₁ dom, Ty.applyTarget_comp S₂ S₁ cod]
  | .matcher c τ  => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_comp S₂ S₁ τ]
  | .slot c τ     => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_comp S₂ S₁ τ]

/-- List form of `Ty.applyTarget_comp`. -/
theorem Ty.applyTargetList_comp (S₂ S₁ : TySubst) :
    ∀ (tys : List Ty),
      Ty.applyTargetList (TySubst.comp S₂ S₁) tys =
        Ty.applyTargetList S₂ (Ty.applyTargetList S₁ tys)
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyTargetList]
      rw [Ty.applyTarget_comp S₂ S₁ τ,
        Ty.applyTargetList_comp S₂ S₁ tys]

end

mutual

/-- Capability-substitution composition is respected throughout types. -/
theorem Ty.applyCapability_comp (S₂ S₁ : CapSubst) :
    ∀ (τ : Ty),
      τ.applyCapability (CapSubst.comp S₂ S₁) =
        (τ.applyCapability S₁).applyCapability S₂
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapabilityList_comp S₂ S₁ tys]
  | .prod tys     => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapabilityList_comp S₂ S₁ tys]
  | .fn dom cod   => by
      simp only [Ty.applyCapability]
      rw [Ty.applyCapability_comp S₂ S₁ dom,
        Ty.applyCapability_comp S₂ S₁ cod]
  | .matcher c τ  => by
      simp only [Ty.applyCapability]
      rw [Cap.apply_comp S₂ S₁ c, Ty.applyCapability_comp S₂ S₁ τ]
  | .slot c τ     => by
      simp only [Ty.applyCapability]
      rw [Cap.apply_comp S₂ S₁ c, Ty.applyCapability_comp S₂ S₁ τ]

/-- List form of `Ty.applyCapability_comp`. -/
theorem Ty.applyCapabilityList_comp (S₂ S₁ : CapSubst) :
    ∀ (tys : List Ty),
      Ty.applyCapabilityList (CapSubst.comp S₂ S₁) tys =
        Ty.applyCapabilityList S₂ (Ty.applyCapabilityList S₁ tys)
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyCapabilityList]
      rw [Ty.applyCapability_comp S₂ S₁ τ,
        Ty.applyCapabilityList_comp S₂ S₁ tys]

end

mutual

/--
Correct cross-sort naturality.

The capability substitution is applied to the range of the target
substitution.  Omitting this range transformation would be false when a target
substitution inserts a type containing capability variables.
-/
theorem Ty.applyCapability_applyTarget (C : CapSubst) (T : TySubst) :
    ∀ (τ : Ty),
      (τ.applyTarget T).applyCapability C =
        (τ.applyCapability C).applyTarget
          (fun a => (T a).applyCapability C)
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyTarget, Ty.applyCapability]
      rw [Ty.applyCapabilityList_applyTargetList C T tys]
  | .prod tys     => by
      simp only [Ty.applyTarget, Ty.applyCapability]
      rw [Ty.applyCapabilityList_applyTargetList C T tys]
  | .fn dom cod   => by
      simp only [Ty.applyTarget, Ty.applyCapability]
      rw [Ty.applyCapability_applyTarget C T dom,
        Ty.applyCapability_applyTarget C T cod]
  | .matcher c τ  => by
      simp only [Ty.applyTarget, Ty.applyCapability]
      rw [Ty.applyCapability_applyTarget C T τ]
  | .slot c τ     => by
      simp only [Ty.applyTarget, Ty.applyCapability]
      rw [Ty.applyCapability_applyTarget C T τ]

/-- List form of `Ty.applyCapability_applyTarget`. -/
theorem Ty.applyCapabilityList_applyTargetList (C : CapSubst) (T : TySubst) :
    ∀ (tys : List Ty),
      Ty.applyCapabilityList C (Ty.applyTargetList T tys) =
        Ty.applyTargetList (fun a => (T a).applyCapability C)
          (Ty.applyCapabilityList C tys)
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyTargetList, Ty.applyCapabilityList]
      rw [Ty.applyCapability_applyTarget C T τ,
        Ty.applyCapabilityList_applyTargetList C T tys]

end

mutual

/-- Capability substitution preserves the ordinary type skeleton. -/
theorem Ty.eraseCap_applyCapability (C : CapSubst) :
    ∀ (τ : Ty), (τ.applyCapability C).eraseCap = τ.eraseCap
  | .var _        => rfl
  | .skolem _     => rfl
  | .unit         => rfl
  | .int          => rfl
  | .bool         => rfl
  | .data n tys   => by
      simp only [Ty.applyCapability, Ty.eraseCap]
      rw [Ty.eraseCapList_applyCapabilityList C tys]
  | .prod tys     => by
      simp only [Ty.applyCapability, Ty.eraseCap]
      rw [Ty.eraseCapList_applyCapabilityList C tys]
  | .fn dom cod   => by
      simp only [Ty.applyCapability, Ty.eraseCap]
      rw [Ty.eraseCap_applyCapability C dom,
        Ty.eraseCap_applyCapability C cod]
  | .matcher c τ  => by
      simp only [Ty.applyCapability, Ty.eraseCap]
      rw [Ty.eraseCap_applyCapability C τ]
  | .slot c τ     => by
      simp only [Ty.applyCapability, Ty.eraseCap]
      rw [Ty.eraseCap_applyCapability C τ]

/-- List form of `Ty.eraseCap_applyCapability`. -/
theorem Ty.eraseCapList_applyCapabilityList (C : CapSubst) :
    ∀ (tys : List Ty),
      Ty.eraseCapList (Ty.applyCapabilityList C tys) =
        Ty.eraseCapList tys
  | []       => rfl
  | τ :: tys => by
      simp only [Ty.applyCapabilityList, Ty.eraseCapList]
      rw [Ty.eraseCap_applyCapability C τ,
        Ty.eraseCapList_applyCapabilityList C tys]

end

/--
An ordinary target substitution preserves an existing root matcher
capability.
-/
theorem Ty.applyTarget_matcher (T : TySubst) (cap : Cap) (τ : Ty) :
    (Ty.matcher cap τ).applyTarget T = Ty.matcher cap (τ.applyTarget T) :=
  rfl

/--
Target substitution commutes past capability substitution when every type in
the target-substitution range is fixed by that capability substitution.
-/
theorem Ty.applyTarget_applyCapability_of_range_fixed
    (C : CapSubst) (T : TySubst)
    (hfixed : ∀ a, (T a).applyCapability C = T a) (τ : Ty) :
    (τ.applyCapability C).applyTarget T =
      (τ.applyTarget T).applyCapability C := by
  have hT : (fun a => (T a).applyCapability C) = T := by
    funext a
    exact hfixed a
  rw [Ty.applyCapability_applyTarget C T τ, hT]

/-- The identity paired substitution satisfies the paper's range condition. -/
theorem Subst.id_rangeFixed : Subst.id.RangeFixed := by
  intro a
  rfl

/--
Under the range condition, the two cross-sort application orders coincide.
-/
theorem Subst.RangeFixed.apply_eq_target_then_capability
    {S : Subst} (hfixed : S.RangeFixed) (τ : Ty) :
    S.apply τ = (τ.applyTarget S.target).applyCapability S.cap := by
  unfold Subst.apply
  exact Ty.applyTarget_applyCapability_of_range_fixed
    S.cap S.target hfixed τ

/-!
The range condition above is substantive.  A target substitution may insert a
nested matcher containing a capability variable; a capability substitution
then reaches that newly inserted occurrence on only one side of the naive
commutation equation.
-/

private def commuteCounterCapSubst : CapSubst :=
  fun a => if a = 0 then .any else .var a

private def commuteCounterTySubst : TySubst :=
  fun a =>
    if a = 0 then .matcher (.var 0) .int else .var a

/-- Unconditional cross-sort commutation is false for open substitution ranges. -/
theorem target_capability_naive_commutation_counterexample :
    ((Ty.var 0).applyCapability commuteCounterCapSubst).applyTarget
        commuteCounterTySubst ≠
      ((Ty.var 0).applyTarget commuteCounterTySubst).applyCapability
        commuteCounterCapSubst := by
  simp [commuteCounterCapSubst, commuteCounterTySubst,
    Ty.applyTarget, Ty.applyCapability, Cap.apply]

/-- Applying the identity combined substitution changes no type. -/
theorem Subst.apply_id (τ : Ty) :
    Subst.id.apply τ = τ := by
  rw [Subst.apply, Subst.id, Ty.applyCapability_id, Ty.applyTarget_id]

/--
Semantic composition for combined substitutions.

The explicit hypothesis is necessary: the later capability substitution must
not rewrite capabilities inside types inserted earlier by `S₁.target`.
-/
theorem Subst.apply_comp (S₂ S₁ : Subst)
    (hfixed : (Subst.mk S₂.cap S₁.target).RangeFixed)
    (τ : Ty) :
    (Subst.comp S₂ S₁).apply τ = S₂.apply (S₁.apply τ) := by
  simp only [Subst.apply, Subst.comp]
  rw [Ty.applyCapability_comp, Ty.applyTarget_comp]
  rw [Ty.applyTarget_applyCapability_of_range_fixed
    S₂.cap S₁.target hfixed (τ.applyCapability S₁.cap)]

/--
Range-fixed pairs remain range-fixed under componentwise composition when
each capability component also fixes the other pair's target range.
-/
theorem Subst.RangeFixed.comp
    {S₂ S₁ : Subst}
    (h₂ : S₂.RangeFixed) (h₁ : S₁.RangeFixed)
    (h₂₁ : (Subst.mk S₂.cap S₁.target).RangeFixed)
    (h₁₂ : (Subst.mk S₁.cap S₂.target).RangeFixed) :
    (Subst.comp S₂ S₁).RangeFixed := by
  intro a
  have hC₁ :
      ((S₁.target a).applyTarget S₂.target).applyCapability S₁.cap =
        (S₁.target a).applyTarget S₂.target := by
    calc
      ((S₁.target a).applyTarget S₂.target).applyCapability S₁.cap =
          ((S₁.target a).applyCapability S₁.cap).applyTarget
            S₂.target :=
        (Ty.applyTarget_applyCapability_of_range_fixed
          S₁.cap S₂.target h₁₂ (S₁.target a)).symm
      _ = (S₁.target a).applyTarget S₂.target := by
        rw [h₁ a]
  have hC₂ :
      ((S₁.target a).applyTarget S₂.target).applyCapability S₂.cap =
        (S₁.target a).applyTarget S₂.target := by
    calc
      ((S₁.target a).applyTarget S₂.target).applyCapability S₂.cap =
          ((S₁.target a).applyCapability S₂.cap).applyTarget
            S₂.target :=
        (Ty.applyTarget_applyCapability_of_range_fixed
          S₂.cap S₂.target h₂ (S₁.target a)).symm
      _ = (S₁.target a).applyTarget S₂.target := by
        rw [h₂₁ a]
  change
    ((S₁.target a).applyTarget S₂.target).applyCapability
        (CapSubst.comp S₂.cap S₁.cap) =
      (S₁.target a).applyTarget S₂.target
  rw [Ty.applyCapability_comp, hC₁, hC₂]

/-! ## List application as `List.map`

The capability-list and paired forms already live beside the source syntax
(`Cap.applyList_eq_map`, `Subst.applyList_eq_map`); the two target-sort forms
below complete the kit. -/

/-- Applying a target substitution to a type list is `List.map`. -/
theorem Ty.applyTargetList_eq_map (S : TySubst) :
    ∀ types : List Ty,
      Ty.applyTargetList S types = types.map fun τ => τ.applyTarget S
  | [] => rfl
  | τ :: types => by
      simp only [Ty.applyTargetList, List.map_cons]
      rw [Ty.applyTargetList_eq_map S types]

/-- Applying a capability substitution throughout a type list is `List.map`. -/
theorem Ty.applyCapabilityList_eq_map (S : CapSubst) :
    ∀ types : List Ty,
      Ty.applyCapabilityList S types =
        types.map fun τ => τ.applyCapability S
  | [] => rfl
  | τ :: types => by
      simp only [Ty.applyCapabilityList, List.map_cons]
      rw [Ty.applyCapabilityList_eq_map S types]

end TypePM
