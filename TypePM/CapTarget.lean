import TypePM.Substitution

/-!
# Capability/target correspondence

`CapTargetOK` is the normalized-input syntactic core of a value invariant, not
a formation rule for every
`Matcher κ τ` type.  The assumption context records correspondence evidence
obtained from matcher or slot values that an open combinator actually
receives.  Constructor comparison is deliberately syntactic in this core
calculus.  Callers must first supply canonical former names and arities from a
frozen signature environment; raw alias validation is not discharged here.
CAS equivalence and semantic normalization are outside this module.
-/

namespace TypePM

/-- Apply both sorts to a target type, in the same order as `Subst.apply`. -/
def applyBoth (C : CapSubst) (T : TySubst) (τ : Ty) : Ty :=
  (τ.applyCapability C).applyTarget T

mutual

/--
Context-relative correspondence between a matcher capability and its target.

The assumption rule is what makes open combinators such as
`MatcherSlot p a -> Matcher (List p) (List a)` possible without adding a
user-visible `CapTargetOK p a` constraint.
-/
inductive CapTargetOK (Ξ : List (Cap × Ty)) : Cap → Ty → Prop where
  | assumption {cap target} :
      (cap, target) ∈ Ξ →
      CapTargetOK Ξ cap target
  | any {target} :
      CapTargetOK Ξ .any target
  | con {name caps targets} :
      CapTargetOKList Ξ caps targets →
      CapTargetOK Ξ (.con name caps) (.data name targets)
  | prod {caps targets} :
      CapTargetOKList Ξ caps targets →
      CapTargetOK Ξ (.prod caps) (.prod targets)

/-- Pointwise correspondence for constructor and product arguments. -/
inductive CapTargetOKList (Ξ : List (Cap × Ty)) : List Cap → List Ty → Prop where
  | nil :
      CapTargetOKList Ξ [] []
  | cons {cap target caps targets} :
      CapTargetOK Ξ cap target →
      CapTargetOKList Ξ caps targets →
      CapTargetOKList Ξ (cap :: caps) (target :: targets)

end

/--
A pair of substitutions preserves a correspondence context when every
assumption remains justified in the destination context.
-/
def CoupledSubstOK
    (Ξ Ξ' : List (Cap × Ty)) (C : CapSubst) (T : TySubst) : Prop :=
  ∀ cap target, (cap, target) ∈ Ξ →
    CapTargetOK Ξ' (cap.apply C) (applyBoth C T target)

/-- Apply a coupled substitution pointwise to a correspondence context. -/
def applyContext
    (C : CapSubst) (T : TySubst) (Ξ : List (Cap × Ty)) :
    List (Cap × Ty) :=
  Ξ.map fun entry =>
    (entry.1.apply C, applyBoth C T entry.2)

/--
The pointwise image context always validates transport of its source context.

This is the canonical destination when a prevailing substitution is applied to
an open matcher/slot environment.
-/
theorem coupledSubstOK_applyContext
    (Ξ : List (Cap × Ty)) (C : CapSubst) (T : TySubst) :
    CoupledSubstOK Ξ (applyContext C T Ξ) C T := by
  intro cap target hmem
  apply CapTargetOK.assumption
  exact List.mem_map.mpr ⟨(cap, target), hmem, rfl⟩

mutual

/--
The normalized-input coupled-substitution lemma.

Independent substitutions are intentionally not sufficient: correspondence
assumptions must be transported together.
-/
theorem CapTargetOK.subst
    {Ξ Ξ' : List (Cap × Ty)} {C : CapSubst} {T : TySubst}
    (hcoupled : CoupledSubstOK Ξ Ξ' C T)
    {cap : Cap} {target : Ty}
    (h : CapTargetOK Ξ cap target) :
    CapTargetOK Ξ' (cap.apply C) (applyBoth C T target) := by
  cases h with
  | assumption hmem =>
      exact hcoupled _ _ hmem
  | any =>
      exact CapTargetOK.any (Ξ := Ξ')
  | con hs =>
      exact CapTargetOK.con (Ξ := Ξ')
        (CapTargetOKList.subst
          (Ξ := Ξ) (Ξ' := Ξ') (C := C) (T := T) hcoupled hs)
  | prod hs =>
      exact CapTargetOK.prod (Ξ := Ξ')
        (CapTargetOKList.subst
          (Ξ := Ξ) (Ξ' := Ξ') (C := C) (T := T) hcoupled hs)

/-- List form of `CapTargetOK.subst`. -/
theorem CapTargetOKList.subst
    {Ξ Ξ' : List (Cap × Ty)} {C : CapSubst} {T : TySubst}
    (hcoupled : CoupledSubstOK Ξ Ξ' C T)
    {caps : List Cap} {targets : List Ty}
    (h : CapTargetOKList Ξ caps targets) :
    CapTargetOKList Ξ' (Cap.applyList C caps)
      (Ty.applyTargetList T (Ty.applyCapabilityList C targets)) := by
  cases h with
  | nil =>
      exact CapTargetOKList.nil (Ξ := Ξ')
  | cons hhead htail =>
      exact CapTargetOKList.cons (Ξ := Ξ')
        (CapTargetOK.subst
          (Ξ := Ξ) (Ξ' := Ξ') (C := C) (T := T) hcoupled hhead)
        (CapTargetOKList.subst
          (Ξ := Ξ) (Ξ' := Ξ') (C := C) (T := T) hcoupled htail)

end

/-- The empty assumption context is preserved by every substitution pair. -/
theorem coupledSubstOK_nil (C : CapSubst) (T : TySubst) :
    CoupledSubstOK [] [] C T := by
  intro cap target h
  cases h

/--
Target specialization cannot invalidate a closed capability/target
certificate and, in particular, cannot strengthen its capability.
-/
theorem CapTargetOK.targetSpecializeClosed
    {cap : Cap} {target : Ty}
    (h : CapTargetOK [] cap target) (T : TySubst) :
    CapTargetOK [] cap (target.applyTarget T) := by
  have hs := CapTargetOK.subst
    (coupledSubstOK_nil CapSubst.id T) h
  simpa [applyBoth, Cap.apply_id, Ty.applyCapability_id] using hs

/-- `Any` is compatible with every target, including specialized targets. -/
theorem capTargetOK_any (Ξ : List (Cap × Ty)) (target : Ty) :
    CapTargetOK Ξ .any target :=
  CapTargetOK.any

/-- A closed constructor certificate fixes the target's syntactic head. -/
theorem CapTargetOK.closedConHead
    {name : String} {caps : List Cap} {target : Ty}
    (h : CapTargetOK [] (.con name caps) target) :
    ∃ targets, target = .data name targets := by
  cases h with
  | assumption hmem =>
      cases hmem
  | con _ =>
      exact ⟨_, rfl⟩

/-- A closed product certificate fixes the target's product shape. -/
theorem CapTargetOK.closedProdHead
    {caps : List Cap} {target : Ty}
    (h : CapTargetOK [] (.prod caps) target) :
    ∃ targets, target = .prod targets := by
  cases h with
  | assumption hmem =>
      cases hmem
  | prod _ =>
      exact ⟨_, rfl⟩

end TypePM
