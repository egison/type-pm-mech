import TypePM.CapabilityOrigin

/-!
# Origin-aware paired unification

First kernel slice of the origin-aware recursive paired unifier (stage 2-4
of the roadmap).  The solver recurses through target-type structure and
solves the capability and target sorts together: capability annotations
reached inside `matcher`/`slot` nodes are dispatched to an origin-oriented
capability solver instead of being compared for syntactic equality, which is
the rigid-annotation behaviour of the symmetric `mguTy`.

Orientation follows the `CapabilityOrigin` ledger discipline:

- `rigid` variables are never bound;
- `renameOnly` variables may only be renamed, and only to a variable that is
  itself not structurally flexible;
- `structuralFlexible` variables may receive arbitrary capabilities
  (subject to the occurs check).

Every success is proof carrying: the returned substitution is sound for the
constraint and `AdmissiblePost`-admissible for the ledger, so origin
discipline is a certificate rather than a convention.  Composition across
the two sorts uses the cross-sort-aware `Subst.seq`, whose admissibility
closure is provided by `AdmissiblePost.seq`.

This module is not yet wired into Algorithm W: the ledger snapshots per
solve cut, the export freeze events, and the switch of the producer guard
to the ledger discipline remain future stages.  The wiring targets the
capability-freeze acceptance gap (`packProgram`); the nested-capability
boundary example (`nestedCapProgram`) is intended rejection under the
demand-directed coercion discipline and is not in scope.  Most generality,
monotonicity, and solvability completeness are not claimed for the
oriented kernels.
-/

namespace TypePM
namespace PairedUnification

/-! ## Admissible single bindings -/

/-- A structurally flexible variable may receive any image. -/
theorem admissible_single_structuralFlexible
    (ledger : CapabilityOriginLedger) (varId : CapVar) (image : Cap)
    (horigin : ledger.originOf varId = .structuralFlexible) :
    AdmissibleCapPost ledger (Unification.CapSubst.single varId image) := by
  intro candidate
  by_cases hcand : varId = candidate
  · subst hcand
    simp only [horigin]
  · cases horigin' : ledger.originOf candidate with
    | rigid =>
        simp [Unification.CapSubst.single, hcand]
    | renameOnly =>
        exact ⟨candidate, by simp [Unification.CapSubst.single, hcand],
          by simp [horigin']⟩
    | structuralFlexible =>
        trivial

/-- A rename-only variable may be renamed to a non-flexible variable. -/
theorem admissible_single_rename
    (ledger : CapabilityOriginLedger) (varId image : CapVar)
    (hvar : ledger.originOf varId = .renameOnly)
    (himage : ledger.originOf image ≠ .structuralFlexible) :
    AdmissibleCapPost ledger
      (Unification.CapSubst.single varId (.var image)) := by
  intro candidate
  by_cases hcand : varId = candidate
  · subst hcand
    simp only [hvar]
    exact ⟨image, by simp [Unification.CapSubst.single], himage⟩
  · cases horigin' : ledger.originOf candidate with
    | rigid =>
        simp [Unification.CapSubst.single, hcand]
    | renameOnly =>
        exact ⟨candidate, by simp [Unification.CapSubst.single, hcand],
          by simp [horigin']⟩
    | structuralFlexible =>
        trivial

/-! ## Proof-carrying oriented capability kernel -/

/-- Certificate of a successful oriented capability unification. -/
structure OrientedCapResult
    (ledger : CapabilityOriginLedger) (left right : Cap) where
  subst : CapSubst
  sound : left.apply subst = right.apply subst
  admissible : AdmissibleCapPost ledger subst

/-- Certificate of a successful oriented capability-list unification. -/
structure OrientedCapListResult
    (ledger : CapabilityOriginLedger) (left right : List Cap) where
  subst : CapSubst
  sound : Cap.applyList subst left = Cap.applyList subst right
  admissible : AdmissibleCapPost ledger subst

mutual

/-- Fuelled origin-oriented capability unification. -/
def solveCap :
    (fuel : Nat) → (ledger : CapabilityOriginLedger) →
      (left right : Cap) → Option (OrientedCapResult ledger left right)
  | 0, _, _, _ => none
  | fuel + 1, ledger, left, right =>
      if hequal : left = right then
        some {
          subst := CapSubst.id
          sound := by subst right; rfl
          admissible := AdmissibleCapPost.id ledger
        }
      else
        match left, right with
        | .var varId, .var otherId =>
            if hflexLeft : ledger.originOf varId = .structuralFlexible then
              some {
                subst := Unification.CapSubst.single varId (.var otherId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                admissible :=
                  admissible_single_structuralFlexible ledger varId _ hflexLeft
              }
            else if hflexRight :
                ledger.originOf otherId = .structuralFlexible then
              some {
                subst := Unification.CapSubst.single otherId (.var varId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                admissible :=
                  admissible_single_structuralFlexible ledger otherId _
                    hflexRight
              }
            else if hrenameLeft : ledger.originOf varId = .renameOnly then
              some {
                subst := Unification.CapSubst.single varId (.var otherId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                admissible :=
                  admissible_single_rename ledger varId otherId hrenameLeft
                    hflexRight
              }
            else if hrenameRight : ledger.originOf otherId = .renameOnly then
              some {
                subst := Unification.CapSubst.single otherId (.var varId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                admissible :=
                  admissible_single_rename ledger otherId varId hrenameRight
                    hflexLeft
              }
            else
              none
        | .var varId, right =>
            if hflex : ledger.originOf varId = .structuralFlexible then
              if hoccurs : varId ∈ right.fcv then
                none
              else
                some {
                  subst := Unification.CapSubst.single varId right
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact (Unification.Cap.apply_single_of_not_mem varId right
                      right hoccurs).symm
                  admissible :=
                    admissible_single_structuralFlexible ledger varId _ hflex
                }
            else
              none
        | left, .var varId =>
            if hflex : ledger.originOf varId = .structuralFlexible then
              if hoccurs : varId ∈ left.fcv then
                none
              else
                some {
                  subst := Unification.CapSubst.single varId left
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact Unification.Cap.apply_single_of_not_mem varId left
                      left hoccurs
                  admissible :=
                    admissible_single_structuralFlexible ledger varId _ hflex
                }
            else
              none
        | .con leftName leftChildren, .con rightName rightChildren =>
            if hname : leftName = rightName then
              match solveCapList fuel ledger leftChildren rightChildren with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    sound := by
                      simp only [Cap.apply]
                      rw [hname, result.sound]
                    admissible := result.admissible
                  }
            else
              none
        | .prod leftComponents, .prod rightComponents =>
            match solveCapList fuel ledger leftComponents rightComponents with
            | none => none
            | some result =>
                some {
                  subst := result.subst
                  sound := by
                    simp only [Cap.apply]
                    exact congrArg Cap.prod result.sound
                  admissible := result.admissible
                }
        | _, _ => none

/-- Fuelled origin-oriented capability-list unification. -/
def solveCapList :
    (fuel : Nat) → (ledger : CapabilityOriginLedger) →
      (left right : List Cap) →
      Option (OrientedCapListResult ledger left right)
  | 0, _, _, _ => none
  | _ + 1, ledger, [], [] =>
      some {
        subst := CapSubst.id
        sound := rfl
        admissible := AdmissibleCapPost.id ledger
      }
  | fuel + 1, ledger, leftHead :: leftTail, rightHead :: rightTail =>
      match solveCap fuel ledger leftHead rightHead with
      | none => none
      | some headResult =>
          match solveCapList fuel ledger
              (Cap.applyList headResult.subst leftTail)
              (Cap.applyList headResult.subst rightTail) with
          | none => none
          | some tailResult =>
              some {
                subst := CapSubst.comp tailResult.subst headResult.subst
                sound := by
                  rw [Cap.applyList_comp tailResult.subst headResult.subst,
                    Cap.applyList_comp tailResult.subst headResult.subst]
                  simp only [Cap.applyList]
                  have hhead := congrArg
                    (fun capability => capability.apply tailResult.subst)
                    headResult.sound
                  rw [hhead, tailResult.sound]
                admissible :=
                  AdmissibleCapPost.comp tailResult.admissible
                    headResult.admissible
              }
  | _ + 1, _, _, _ => none

end

/-! ## Paired substitution application shapes -/

private theorem subst_apply_fn (S : Subst) (domain codomain : Ty) :
    S.apply (.fn domain codomain) =
      .fn (S.apply domain) (S.apply codomain) := rfl

private theorem subst_apply_matcher (S : Subst) (capability : Cap) (τ : Ty) :
    S.apply (.matcher capability τ) =
      .matcher (capability.apply S.cap) (S.apply τ) := rfl

private theorem subst_apply_slot (S : Subst) (capability : Cap) (τ : Ty) :
    S.apply (.slot capability τ) =
      .slot (capability.apply S.cap) (S.apply τ) := rfl

private theorem subst_applyList (S : Subst) :
    ∀ types : List Ty,
      Ty.applyTargetList S.target (Ty.applyCapabilityList S.cap types) =
        types.map S.apply
  | [] => rfl
  | τ :: types => by
      simp only [Ty.applyCapabilityList, Ty.applyTargetList, List.map]
      exact congrArg _ (subst_applyList S types)

private theorem subst_apply_data (S : Subst) (name : String)
    (fields : List Ty) :
    S.apply (.data name fields) = .data name (fields.map S.apply) := by
  show Ty.applyTarget _ (Ty.applyCapability _ _) = _
  simp only [Ty.applyCapability, Ty.applyTarget]
  rw [subst_applyList]

private theorem subst_apply_prod (S : Subst) (components : List Ty) :
    S.apply (.prod components) = .prod (components.map S.apply) := by
  show Ty.applyTarget _ (Ty.applyCapability _ _) = _
  simp only [Ty.applyCapability, Ty.applyTarget]
  rw [subst_applyList]

/-- Applying a capability-only pair is capability application. -/
private theorem capOnly_apply (C : CapSubst) (τ : Ty) :
    (Subst.mk C TySubst.id).apply τ = τ.applyCapability C := by
  show (τ.applyCapability C).applyTarget TySubst.id = _
  exact Ty.applyTarget_id _

/-- Applying a target-only pair is target application. -/
private theorem targetOnly_apply (T : TySubst) (τ : Ty) :
    (Subst.mk CapSubst.id T).apply τ = τ.applyTarget T := by
  show (τ.applyCapability CapSubst.id).applyTarget T = _
  rw [Ty.applyCapability_id]

/-! ## Proof-carrying paired target kernel -/

/-- Certificate of a successful paired target unification. -/
structure PairedResult
    (ledger : CapabilityOriginLedger) (left right : Ty) where
  subst : Subst
  sound : subst.apply left = subst.apply right
  admissible : AdmissiblePost ledger subst

/-- Certificate of a successful paired target-list unification. -/
structure PairedListResult
    (ledger : CapabilityOriginLedger) (left right : List Ty) where
  subst : Subst
  sound : left.map subst.apply = right.map subst.apply
  admissible : AdmissiblePost ledger subst

/-- A capability-only pair is admissible when its capability part is. -/
private theorem admissiblePost_capOnly
    {ledger : CapabilityOriginLedger} {C : CapSubst}
    (hcap : AdmissibleCapPost ledger C) :
    AdmissiblePost ledger (Subst.mk C TySubst.id) :=
  { cap := hcap }

/-- A target-only pair is always admissible. -/
private theorem admissiblePost_targetOnly
    (ledger : CapabilityOriginLedger) (T : TySubst) :
    AdmissiblePost ledger (Subst.mk CapSubst.id T) :=
  { cap := AdmissibleCapPost.id ledger }

mutual

/-- Fuelled paired unification: recurse through target structure, solving
capability annotations with the oriented capability kernel. -/
def solvePairedTy :
    (fuel : Nat) → (ledger : CapabilityOriginLedger) →
      (left right : Ty) → Option (PairedResult ledger left right)
  | 0, _, _, _ => none
  | fuel + 1, ledger, left, right =>
      if hequal : left = right then
        some {
          subst := Subst.id
          sound := by subst right; rfl
          admissible := AdmissiblePost.id ledger
        }
      else
        match left, right with
        | .var varId, right =>
            if hoccurs : varId ∈ right.ftv then
              none
            else
              some {
                subst := Subst.mk CapSubst.id
                  (Unification.TySubst.single varId right)
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact (Unification.Ty.applyTarget_single_of_not_mem varId
                    right right hoccurs).symm
                admissible := admissiblePost_targetOnly ledger _
              }
        | left, .var varId =>
            if hoccurs : varId ∈ left.ftv then
              none
            else
              some {
                subst := Subst.mk CapSubst.id
                  (Unification.TySubst.single varId left)
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact Unification.Ty.applyTarget_single_of_not_mem varId
                    left left hoccurs
                admissible := admissiblePost_targetOnly ledger _
              }
        | .data leftName leftFields, .data rightName rightFields =>
            if hname : leftName = rightName then
              match solvePairedTyList fuel ledger leftFields rightFields with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    sound := by
                      rw [subst_apply_data, subst_apply_data, hname,
                        result.sound]
                    admissible := result.admissible
                  }
            else
              none
        | .prod leftComponents, .prod rightComponents =>
            match solvePairedTyList fuel ledger leftComponents
                rightComponents with
            | none => none
            | some result =>
                some {
                  subst := result.subst
                  sound := by
                    rw [subst_apply_prod, subst_apply_prod, result.sound]
                  admissible := result.admissible
                }
        | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
            match solvePairedTy fuel ledger leftDomain rightDomain with
            | none => none
            | some domainResult =>
                match solvePairedTy fuel ledger
                    (domainResult.subst.apply leftCodomain)
                    (domainResult.subst.apply rightCodomain) with
                | none => none
                | some codomainResult =>
                    some {
                      subst :=
                        Subst.seq codomainResult.subst domainResult.subst
                      sound := by
                        rw [subst_apply_fn, subst_apply_fn, Subst.seq_apply,
                          Subst.seq_apply, Subst.seq_apply, Subst.seq_apply,
                          domainResult.sound, codomainResult.sound]
                      admissible :=
                        AdmissiblePost.seq codomainResult.admissible
                          domainResult.admissible
                    }
        | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
            match solveCap fuel ledger leftCap rightCap with
            | none => none
            | some capResult =>
                match solvePairedTy fuel ledger
                    (leftTarget.applyCapability capResult.subst)
                    (rightTarget.applyCapability capResult.subst) with
                | none => none
                | some targetResult =>
                    some {
                      subst := Subst.seq targetResult.subst
                        (Subst.mk capResult.subst TySubst.id)
                      sound := by
                        rw [subst_apply_matcher, subst_apply_matcher]
                        have hcap :
                            leftCap.apply (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).cap =
                            rightCap.apply (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).cap := by
                          show leftCap.apply (CapSubst.comp
                              targetResult.subst.cap capResult.subst) =
                            rightCap.apply (CapSubst.comp
                              targetResult.subst.cap capResult.subst)
                          rw [Cap.apply_comp, Cap.apply_comp, capResult.sound]
                        have htarget :
                            (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).apply
                              leftTarget =
                            (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).apply
                              rightTarget := by
                          rw [Subst.seq_apply, Subst.seq_apply, capOnly_apply,
                            capOnly_apply]
                          exact targetResult.sound
                        rw [hcap, htarget]
                      admissible :=
                        AdmissiblePost.seq targetResult.admissible
                          (admissiblePost_capOnly capResult.admissible)
                    }
        | .slot leftCap leftTarget, .slot rightCap rightTarget =>
            match solveCap fuel ledger leftCap rightCap with
            | none => none
            | some capResult =>
                match solvePairedTy fuel ledger
                    (leftTarget.applyCapability capResult.subst)
                    (rightTarget.applyCapability capResult.subst) with
                | none => none
                | some targetResult =>
                    some {
                      subst := Subst.seq targetResult.subst
                        (Subst.mk capResult.subst TySubst.id)
                      sound := by
                        rw [subst_apply_slot, subst_apply_slot]
                        have hcap :
                            leftCap.apply (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).cap =
                            rightCap.apply (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).cap := by
                          show leftCap.apply (CapSubst.comp
                              targetResult.subst.cap capResult.subst) =
                            rightCap.apply (CapSubst.comp
                              targetResult.subst.cap capResult.subst)
                          rw [Cap.apply_comp, Cap.apply_comp, capResult.sound]
                        have htarget :
                            (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).apply
                              leftTarget =
                            (Subst.seq targetResult.subst
                              (Subst.mk capResult.subst TySubst.id)).apply
                              rightTarget := by
                          rw [Subst.seq_apply, Subst.seq_apply, capOnly_apply,
                            capOnly_apply]
                          exact targetResult.sound
                        rw [hcap, htarget]
                      admissible :=
                        AdmissiblePost.seq targetResult.admissible
                          (admissiblePost_capOnly capResult.admissible)
                    }
        | _, _ => none

/-- Fuelled paired target-list unification. -/
def solvePairedTyList :
    (fuel : Nat) → (ledger : CapabilityOriginLedger) →
      (left right : List Ty) →
      Option (PairedListResult ledger left right)
  | 0, _, _, _ => none
  | _ + 1, ledger, [], [] =>
      some {
        subst := Subst.id
        sound := rfl
        admissible := AdmissiblePost.id ledger
      }
  | fuel + 1, ledger, leftHead :: leftTail, rightHead :: rightTail =>
      match solvePairedTy fuel ledger leftHead rightHead with
      | none => none
      | some headResult =>
          match solvePairedTyList fuel ledger
              (leftTail.map headResult.subst.apply)
              (rightTail.map headResult.subst.apply) with
          | none => none
          | some tailResult =>
              some {
                subst := Subst.seq tailResult.subst headResult.subst
                sound := by
                  have hfun : (Subst.seq tailResult.subst
                        headResult.subst).apply =
                      fun τ => tailResult.subst.apply
                        (headResult.subst.apply τ) :=
                    funext fun τ => Subst.seq_apply _ _ τ
                  simp only [List.map, hfun]
                  have hhead := congrArg tailResult.subst.apply
                    headResult.sound
                  have htail := tailResult.sound
                  simp only [List.map_map, Function.comp_def] at htail
                  rw [hhead, htail]
                admissible :=
                  AdmissiblePost.seq tailResult.admissible
                    headResult.admissible
              }
  | _ + 1, _, _, _ => none

end

/-! ## Public wrappers -/

/-- Structural-fuel wrapper of the paired solver. -/
def mguPairedTy
    (ledger : CapabilityOriginLedger) (left right : Ty) : Option Subst :=
  (solvePairedTy (Unification.tyFuel left right) ledger left right).map
    PairedResult.subst

/-- Every substitution returned by the paired solver is sound. -/
theorem mguPairedTy_sound
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    S.apply left = S.apply right := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.sound

/-- Every substitution returned by the paired solver respects the origin
ledger. -/
theorem mguPairedTy_admissible
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    AdmissiblePost ledger S := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.admissible

/-! ## Executable regression checks

The first pair contrasts the paired solver with the rigid annotation
comparison of the symmetric target solver
(`Unification.mguTy_capability_annotation_regression`): the same constraint
that `mguTy` rejects is solved once the annotation variable is structurally
flexible. -/

/-- A flexible annotation variable is solved inside the matcher head. -/
theorem paired_solves_flexible_annotation :
    (mguPairedTy [(0, .structuralFlexible)]
      (.matcher (.var 0) .int) (.matcher .any .int)).isSome = true := by
  rfl

/-- The symmetric solver still rejects the same constraint. -/
theorem symmetric_still_rigid :
    Unification.mguTy (.matcher (.var 0) .int) (.matcher .any .int) =
      none := by
  rfl

/-- A rename-only annotation variable may be renamed to a frozen peer. -/
theorem paired_renames_frozen_annotation :
    (mguPairedTy [(0, .renameOnly), (5, .renameOnly)]
      (.matcher (.var 0) .int) (.matcher (.var 5) .int)).isSome = true := by
  rfl

/-- A rename-only annotation variable is never structured. -/
theorem paired_rejects_frozen_structuring :
    mguPairedTy [(0, .renameOnly)]
      (.matcher (.var 0) .int) (.matcher .any .int) = none := by
  rfl

/-- Unlisted variables default to rigid and are never bound. -/
theorem paired_rejects_rigid_default :
    mguPairedTy [] (.matcher (.var 0) .int) (.matcher .any .int) = none := by
  rfl

/-- Annotations are solved at any structural depth. -/
theorem paired_solves_nested_annotation :
    (mguPairedTy [(0, .structuralFlexible)]
      (.fn (.matcher (.var 0) .int) .int)
      (.fn (.matcher (.con "List" [.any]) .int) .int)).isSome = true := by
  rfl

/-- Capability and target metavariables are solved in the same pass. -/
theorem paired_solves_both_sorts :
    (mguPairedTy [(0, .structuralFlexible)]
      (.matcher (.var 0) (.var 3)) (.matcher .any .int)).isSome = true := by
  rfl

/-- Orientation binds the flexible side, never structuring the frozen
variable: a rename-only variable against a flexible one is solved by
absorbing into the flexible variable. -/
theorem paired_orients_toward_flexible :
    (mguPairedTy [(0, .renameOnly), (5, .structuralFlexible)]
      (.matcher (.var 0) .int) (.matcher (.var 5) .int)).isSome = true := by
  rfl

end PairedUnification
end TypePM
