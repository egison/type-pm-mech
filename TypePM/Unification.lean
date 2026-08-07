import TypePM.Relation

/-!
# Executable two-sorted unification

This module implements the two symmetric Robinson unifiers denoted by
`mguCap` and `mguTy` in the two-sorted specification.  They are deliberately separate
from `CapMatch`: unification may solve a flexible variable on either side,
whereas `CapMatch` is the producer-stable, consumer-only operation.

The target-sort solver treats capability annotations already present in a
`matcher` or `slot` node as rigid.  A two-sorted Algorithm W first applies the
capability solver to its capability constraint and then invokes the target
solver on the capability-zonked target types.

The certified kernels below recurse on explicit fuel and are proof carrying:
every success certifies both soundness and most generality of the returned
substitution.  Their public wrappers choose a structural fuel bound.  Failure
includes fuel exhaustion, an occurs check, unequal rigid skolems, unequal
constructor heads, unequal capability annotations in target types, and
unequal constructor/product arities.  Solvability completeness on unifiable
inputs is not claimed.
-/

namespace TypePM
namespace Unification

/-! ## Single bindings and their occurs-check laws -/

/-- The identity-defaulting substitution containing one capability binding. -/
def CapSubst.single (varId : CapVar) (replacement : Cap) : CapSubst :=
  fun candidate =>
    if varId = candidate then replacement else .var candidate

/-- The identity-defaulting substitution containing one target binding. -/
def TySubst.single
    (varId : TypePM.TyVar) (replacement : Ty) : TySubst :=
  fun candidate =>
    if varId = candidate then replacement else .var candidate

/-- A single target binding has exactly singleton support. -/
theorem TySubst.single_supportWithin
    (varId : TypePM.TyVar) (replacement : Ty) :
    (TySubst.single varId replacement).SupportWithin [varId] := by
  intro candidate outside
  simp only [List.mem_singleton] at outside
  have reverse : varId ≠ candidate := Ne.symm outside
  simp [TySubst.single, reverse]

mutual

/-- A capability not containing `varId` is fixed by its single binding. -/
theorem Cap.apply_single_of_not_mem
    (varId : CapVar) (replacement : Cap) :
    ∀ (capability : Cap),
      varId ∉ capability.fcv →
        capability.apply (CapSubst.single varId replacement) = capability
  | .any, _ => rfl
  | .var candidate, hnotmem => by
      simp only [Cap.fcv, List.mem_singleton] at hnotmem
      simp [Cap.apply, CapSubst.single, hnotmem]
  | .skolem _, _ => rfl
  | .con name children, hnotmem => by
      simp only [Cap.apply]
      rw [Cap.applyList_single_of_not_mem varId replacement children hnotmem]
  | .prod components, hnotmem => by
      simp only [Cap.apply]
      rw [Cap.applyList_single_of_not_mem varId replacement components hnotmem]

/-- List form of `Cap.apply_single_of_not_mem`. -/
theorem Cap.applyList_single_of_not_mem
    (varId : CapVar) (replacement : Cap) :
    ∀ (capabilities : List Cap),
      varId ∉ Cap.fcvList capabilities →
        Cap.applyList (CapSubst.single varId replacement) capabilities =
          capabilities
  | [], _ => rfl
  | capability :: capabilities, hnotmem => by
      simp only [Cap.fcvList, List.mem_append, not_or] at hnotmem
      simp only [Cap.applyList]
      rw [Cap.apply_single_of_not_mem varId replacement capability hnotmem.1,
        Cap.applyList_single_of_not_mem varId replacement capabilities
          hnotmem.2]

end

mutual

/-- A type not containing `varId` is fixed by its single target binding. -/
theorem Ty.applyTarget_single_of_not_mem
    (varId : TypePM.TyVar) (replacement : Ty) :
    ∀ (τ : Ty),
      varId ∉ τ.ftv →
        τ.applyTarget (TySubst.single varId replacement) = τ
  | .var candidate, hnotmem => by
      simp only [Ty.ftv, List.mem_singleton] at hnotmem
      simp [Ty.applyTarget, TySubst.single, hnotmem]
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data name fields, hnotmem => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_single_of_not_mem varId replacement fields hnotmem]
  | .prod components, hnotmem => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTargetList_single_of_not_mem varId replacement components
        hnotmem]
  | .fn domain codomain, hnotmem => by
      simp only [Ty.ftv, List.mem_append, not_or] at hnotmem
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_single_of_not_mem varId replacement domain hnotmem.1,
        Ty.applyTarget_single_of_not_mem varId replacement codomain hnotmem.2]
  | .matcher capability target, hnotmem => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_single_of_not_mem varId replacement target hnotmem]
  | .slot capability target, hnotmem => by
      simp only [Ty.applyTarget]
      rw [Ty.applyTarget_single_of_not_mem varId replacement target hnotmem]

/-- List form of `Ty.applyTarget_single_of_not_mem`. -/
theorem Ty.applyTargetList_single_of_not_mem
    (varId : TypePM.TyVar) (replacement : Ty) :
    ∀ (types : List Ty),
      varId ∉ Ty.ftvList types →
        Ty.applyTargetList (TySubst.single varId replacement) types = types
  | [], _ => rfl
  | τ :: types, hnotmem => by
      simp only [Ty.ftvList, List.mem_append, not_or] at hnotmem
      simp only [Ty.applyTargetList]
      rw [Ty.applyTarget_single_of_not_mem varId replacement τ hnotmem.1,
        Ty.applyTargetList_single_of_not_mem varId replacement types hnotmem.2]

end

/-! ## Structural fuel bounds -/

mutual

/-- A positive structural weight for a capability. -/
def Cap.unificationWeight : Cap → Nat
  | .any => 1
  | .var _ => 1
  | .skolem _ => 1
  | .con _ children => 1 + Cap.unificationWeightList children
  | .prod components => 1 + Cap.unificationWeightList components

/-- Structural weight of a capability list. -/
def Cap.unificationWeightList : List Cap → Nat
  | [] => 1
  | capability :: capabilities =>
      1 + Cap.unificationWeight capability +
        Cap.unificationWeightList capabilities

end


mutual

/-- A positive structural weight for a target type. -/
def Ty.unificationWeight : Ty → Nat
  | .var _ => 1
  | .skolem _ => 1
  | .unit => 1
  | .int => 1
  | .bool => 1
  | .data _ fields => 1 + Ty.unificationWeightList fields
  | .prod components => 1 + Ty.unificationWeightList components
  | .fn domain codomain =>
      1 + Ty.unificationWeight domain + Ty.unificationWeight codomain
  | .matcher _ target => 1 + Ty.unificationWeight target
  | .slot _ target => 1 + Ty.unificationWeight target

/-- Structural weight of a target-type list. -/
def Ty.unificationWeightList : List Ty → Nat
  | [] => 1
  | τ :: types =>
      1 + Ty.unificationWeight τ + Ty.unificationWeightList types

end

/-- Default fuel for one capability constraint. -/
def capFuel (left right : Cap) : Nat :=
  2 * (Cap.unificationWeight left + Cap.unificationWeight right + 1)

/-- Default fuel for one target constraint. -/
def tyFuel (left right : Ty) : Nat :=
  2 * (Ty.unificationWeight left + Ty.unificationWeight right + 1)

/-! ## Proof-carrying kernels -/

/-- Internal certificate returned by a successful capability unification.
Beyond soundness it certifies most generality: every unifier of the same
constraint factors through the returned substitution. -/
structure CapResult (left right : Cap) where
  subst : CapSubst
  sound : left.apply subst = right.apply subst
  universal :
    ∀ U : CapSubst, left.apply U = right.apply U →
      ∃ R : CapSubst, U = CapSubst.comp R subst

/-- Internal certificate returned by successful capability-list unification. -/
structure CapListResult (left right : List Cap) where
  subst : CapSubst
  sound : Cap.applyList subst left = Cap.applyList subst right
  universal :
    ∀ U : CapSubst, Cap.applyList U left = Cap.applyList U right →
      ∃ R : CapSubst, U = CapSubst.comp R subst

/-- Internal certificate returned by a successful target unification. -/
structure TyResult (left right : Ty) where
  subst : TySubst
  supportVars : List TypePM.TyVar
  support : subst.SupportWithin supportVars
  sound : left.applyTarget subst = right.applyTarget subst
  universal :
    ∀ U : TySubst, left.applyTarget U = right.applyTarget U →
      ∃ R : TySubst, U = TySubst.comp R subst

/-- Internal certificate returned by successful target-list unification. -/
structure TyListResult (left right : List Ty) where
  subst : TySubst
  supportVars : List TypePM.TyVar
  support : subst.SupportWithin supportVars
  sound : Ty.applyTargetList subst left = Ty.applyTargetList subst right
  universal :
    ∀ U : TySubst, Ty.applyTargetList U left = Ty.applyTargetList U right →
      ∃ R : TySubst, U = TySubst.comp R subst

mutual

/-- Fuelled, symmetric capability-unification kernel. -/
private def solveCap :
    (fuel : Nat) → (left right : Cap) → Option (CapResult left right)
  | 0, _, _ => none
  | fuel + 1, left, right =>
      if hequal : left = right then
        some {
          subst := CapSubst.id
          sound := by subst right; rfl
          universal := fun U _ => ⟨U, funext fun _ => rfl⟩
        }
      else
        match left, right with
        | .var varId, right =>
            if hoccurs : varId ∈ right.fcv then
              none
            else
              some {
                subst := CapSubst.single varId right
                sound := by
                  simp only [Cap.apply, CapSubst.single, if_pos]
                  exact
                    (Cap.apply_single_of_not_mem varId right right hoccurs).symm
                universal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, CapSubst.single, Cap.apply]
                      using hunify
                  · simp [CapSubst.comp, CapSubst.single, Cap.apply,
                      hcandidate]
              }
        | left, .var varId =>
            if hoccurs : varId ∈ left.fcv then
              none
            else
              some {
                subst := CapSubst.single varId left
                sound := by
                  simp only [Cap.apply, CapSubst.single, if_pos]
                  exact Cap.apply_single_of_not_mem varId left left hoccurs
                universal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, CapSubst.single, Cap.apply]
                      using hunify.symm
                  · simp [CapSubst.comp, CapSubst.single, Cap.apply,
                      hcandidate]
              }
        | .con leftName leftChildren, .con rightName rightChildren =>
            if hname : leftName = rightName then
              match solveCapList fuel leftChildren rightChildren with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    sound := by
                      simp only [Cap.apply]
                      rw [hname, result.sound]
                    universal := by
                      intro U hunify
                      simp only [Cap.apply, Cap.con.injEq] at hunify
                      exact result.universal U hunify.2
                  }
            else
              none
        | .prod leftComponents, .prod rightComponents =>
            match solveCapList fuel leftComponents rightComponents with
            | none => none
            | some result =>
                some {
                  subst := result.subst
                  sound := by
                    simp only [Cap.apply]
                    exact congrArg Cap.prod result.sound
                  universal := by
                    intro U hunify
                    simp only [Cap.apply, Cap.prod.injEq] at hunify
                    exact result.universal U hunify
                }
        | _, _ => none

/-- Fuelled left-to-right capability-list unification kernel. -/
private def solveCapList :
    (fuel : Nat) → (left right : List Cap) →
      Option (CapListResult left right)
  | 0, _, _ => none
  | _ + 1, [], [] =>
      some {
        subst := CapSubst.id
        sound := rfl
        universal := fun U _ => ⟨U, funext fun _ => rfl⟩
      }
  | fuel + 1, leftHead :: leftTail, rightHead :: rightTail =>
      match solveCap fuel leftHead rightHead with
      | none => none
      | some headResult =>
          match solveCapList fuel
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
                universal := by
                  intro U hunify
                  simp only [Cap.applyList, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  obtain ⟨R₁, hR₁⟩ := headResult.universal U hhead
                  have htail' :
                      Cap.applyList R₁
                          (Cap.applyList headResult.subst leftTail) =
                        Cap.applyList R₁
                          (Cap.applyList headResult.subst rightTail) := by
                    rw [← Cap.applyList_comp, ← Cap.applyList_comp, ← hR₁]
                    exact htail
                  obtain ⟨R₂, hR₂⟩ := tailResult.universal R₁ htail'
                  refine ⟨R₂, ?_⟩
                  rw [hR₁, hR₂]
                  funext candidate
                  simp [CapSubst.comp, Cap.apply_comp]
              }
  | _ + 1, _, _ => none

end


mutual

/-- Fuelled, symmetric target-sort unification kernel. -/
private def solveTy :
    (fuel : Nat) → (left right : Ty) → Option (TyResult left right)
  | 0, _, _ => none
  | fuel + 1, left, right =>
      if hequal : left = right then
        some {
          subst := TySubst.id
          supportVars := []
          support := TySubst.id_supportWithin []
          sound := by subst right; rfl
          universal := fun U _ => ⟨U, funext fun _ => rfl⟩
        }
      else
        match left, right with
        | .var varId, right =>
            if hoccurs : varId ∈ right.ftv then
              none
            else
              some {
                subst := TySubst.single varId right
                supportVars := [varId]
                support := TySubst.single_supportWithin varId right
                sound := by
                  simp only [Ty.applyTarget, TySubst.single, if_pos]
                  exact
                    (Ty.applyTarget_single_of_not_mem varId right right
                      hoccurs).symm
                universal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [TySubst.comp, TySubst.single, Ty.applyTarget]
                      using hunify
                  · simp [TySubst.comp, TySubst.single, Ty.applyTarget,
                      hcandidate]
              }
        | left, .var varId =>
            if hoccurs : varId ∈ left.ftv then
              none
            else
              some {
                subst := TySubst.single varId left
                supportVars := [varId]
                support := TySubst.single_supportWithin varId left
                sound := by
                  simp only [Ty.applyTarget, TySubst.single, if_pos]
                  exact Ty.applyTarget_single_of_not_mem varId left left hoccurs
                universal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [TySubst.comp, TySubst.single, Ty.applyTarget]
                      using hunify.symm
                  · simp [TySubst.comp, TySubst.single, Ty.applyTarget,
                      hcandidate]
              }
        | .data leftName leftFields, .data rightName rightFields =>
            if hname : leftName = rightName then
              match solveTyList fuel leftFields rightFields with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    supportVars := result.supportVars
                    support := result.support
                    sound := by
                      simp only [Ty.applyTarget]
                      rw [hname, result.sound]
                    universal := by
                      intro U hunify
                      simp only [Ty.applyTarget, Ty.data.injEq] at hunify
                      exact result.universal U hunify.2
                  }
            else
              none
        | .prod leftComponents, .prod rightComponents =>
            match solveTyList fuel leftComponents rightComponents with
            | none => none
            | some result =>
                some {
                  subst := result.subst
                  supportVars := result.supportVars
                  support := result.support
                  sound := by
                    simp only [Ty.applyTarget]
                    exact congrArg Ty.prod result.sound
                  universal := by
                    intro U hunify
                    simp only [Ty.applyTarget, Ty.prod.injEq] at hunify
                    exact result.universal U hunify
                }
        | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
            match solveTy fuel leftDomain rightDomain with
            | none => none
            | some domainResult =>
                match solveTy fuel
                    (leftCodomain.applyTarget domainResult.subst)
                    (rightCodomain.applyTarget domainResult.subst) with
                | none => none
                | some codomainResult =>
                    some {
                      subst :=
                        TySubst.comp codomainResult.subst domainResult.subst
                      supportVars :=
                        domainResult.supportVars ++ codomainResult.supportVars
                      support := domainResult.support.comp
                        codomainResult.support
                      sound := by
                        simp only [Ty.applyTarget]
                        rw [Ty.applyTarget_comp codomainResult.subst
                            domainResult.subst leftDomain,
                          Ty.applyTarget_comp codomainResult.subst
                            domainResult.subst leftCodomain,
                          Ty.applyTarget_comp codomainResult.subst
                            domainResult.subst rightDomain,
                          Ty.applyTarget_comp codomainResult.subst
                            domainResult.subst rightCodomain]
                        have hdomain := congrArg
                          (fun τ => τ.applyTarget codomainResult.subst)
                          domainResult.sound
                        rw [hdomain, codomainResult.sound]
                      universal := by
                        intro U hunify
                        simp only [Ty.applyTarget, Ty.fn.injEq] at hunify
                        obtain ⟨hdomain, hcodomain⟩ := hunify
                        obtain ⟨R₁, hR₁⟩ := domainResult.universal U hdomain
                        have hcodomain' :
                            (leftCodomain.applyTarget
                                domainResult.subst).applyTarget R₁ =
                              (rightCodomain.applyTarget
                                domainResult.subst).applyTarget R₁ := by
                          rw [← Ty.applyTarget_comp, ← Ty.applyTarget_comp,
                            ← hR₁]
                          exact hcodomain
                        obtain ⟨R₂, hR₂⟩ :=
                          codomainResult.universal R₁ hcodomain'
                        refine ⟨R₂, ?_⟩
                        rw [hR₁, hR₂]
                        funext candidate
                        simp [TySubst.comp, Ty.applyTarget_comp]
                    }
        | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
            if hcap : leftCap = rightCap then
              match solveTy fuel leftTarget rightTarget with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    supportVars := result.supportVars
                    support := result.support
                    sound := by
                      simp only [Ty.applyTarget]
                      rw [hcap, result.sound]
                    universal := by
                      intro U hunify
                      simp only [Ty.applyTarget, Ty.matcher.injEq] at hunify
                      exact result.universal U hunify.2
                  }
            else
              none
        | .slot leftCap leftTarget, .slot rightCap rightTarget =>
            if hcap : leftCap = rightCap then
              match solveTy fuel leftTarget rightTarget with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    supportVars := result.supportVars
                    support := result.support
                    sound := by
                      simp only [Ty.applyTarget]
                      rw [hcap, result.sound]
                    universal := by
                      intro U hunify
                      simp only [Ty.applyTarget, Ty.slot.injEq] at hunify
                      exact result.universal U hunify.2
                  }
            else
              none
        | _, _ => none

/-- Fuelled left-to-right target-list unification kernel. -/
private def solveTyList :
    (fuel : Nat) → (left right : List Ty) →
      Option (TyListResult left right)
  | 0, _, _ => none
  | _ + 1, [], [] =>
      some {
        subst := TySubst.id
        supportVars := []
        support := TySubst.id_supportWithin []
        sound := rfl
        universal := fun U _ => ⟨U, funext fun _ => rfl⟩
      }
  | fuel + 1, leftHead :: leftTail, rightHead :: rightTail =>
      match solveTy fuel leftHead rightHead with
      | none => none
      | some headResult =>
          match solveTyList fuel
              (Ty.applyTargetList headResult.subst leftTail)
              (Ty.applyTargetList headResult.subst rightTail) with
          | none => none
          | some tailResult =>
              some {
                subst := TySubst.comp tailResult.subst headResult.subst
                supportVars :=
                  headResult.supportVars ++ tailResult.supportVars
                support := headResult.support.comp tailResult.support
                sound := by
                  rw [Ty.applyTargetList_comp tailResult.subst headResult.subst,
                    Ty.applyTargetList_comp tailResult.subst headResult.subst]
                  simp only [Ty.applyTargetList]
                  have hhead := congrArg
                    (fun τ => τ.applyTarget tailResult.subst)
                    headResult.sound
                  rw [hhead, tailResult.sound]
                universal := by
                  intro U hunify
                  simp only [Ty.applyTargetList, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  obtain ⟨R₁, hR₁⟩ := headResult.universal U hhead
                  have htail' :
                      Ty.applyTargetList R₁
                          (Ty.applyTargetList headResult.subst leftTail) =
                        Ty.applyTargetList R₁
                          (Ty.applyTargetList headResult.subst rightTail) := by
                    rw [← Ty.applyTargetList_comp, ← Ty.applyTargetList_comp,
                      ← hR₁]
                    exact htail
                  obtain ⟨R₂, hR₂⟩ := tailResult.universal R₁ htail'
                  refine ⟨R₂, ?_⟩
                  rw [hR₁, hR₂]
                  funext candidate
                  simp [TySubst.comp, Ty.applyTarget_comp]
              }
  | _ + 1, _, _ => none

end


/-! ## Fuel monotonicity of the kernels

Branch selection in the kernels depends only on the constraint, never on the
remaining fuel, so a successful run replays verbatim with any larger fuel and
returns the same substitution.  These lemmas are the first half of the
solvability programme: they reduce "some fuel succeeds" to "every larger fuel
succeeds", leaving only the existence of one sufficient fuel open. -/

private theorem solveCapPair_mono_succ :
    ∀ fuel : Nat,
      (∀ (left right : Cap) (result : CapResult left right),
        solveCap fuel left right = some result →
          ∃ result' : CapResult left right,
            solveCap (fuel + 1) left right = some result' ∧
              result'.subst = result.subst) ∧
      (∀ (left right : List Cap) (result : CapListResult left right),
        solveCapList fuel left right = some result →
          ∃ result' : CapListResult left right,
            solveCapList (fuel + 1) left right = some result' ∧
              result'.subst = result.subst)
  | 0 => by
      constructor
      · intro left right result hrun
        simp [solveCap] at hrun
      · intro left right result hrun
        simp [solveCapList] at hrun
  | fuel + 1 => by
      obtain ⟨ihCap, ihList⟩ := solveCapPair_mono_succ fuel
      constructor
      · intro left right result hrun
        rw [solveCap] at hrun ⊢
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun ⊢
          exact ⟨_, rfl, by cases hrun; rfl⟩
        · rw [dif_neg hequal] at hrun ⊢
          match left, right with
          | .var varId, right =>
              exact ⟨result, hrun, rfl⟩
          | .con leftName leftChildren, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .prod leftComponents, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .any, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .skolem name, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .con leftName leftChildren, .con rightName rightChildren =>
              simp only [] at hrun ⊢
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun ⊢
                cases hchildren : solveCapList fuel leftChildren rightChildren
                  with
                | none => rw [hchildren] at hrun; cases hrun
                | some childResult =>
                    rw [hchildren] at hrun
                    obtain ⟨childResult', hchildren', hsubst⟩ :=
                      ihList leftChildren rightChildren childResult hchildren
                    rw [hchildren']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun ⊢
              cases hcomponents :
                  solveCapList fuel leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  obtain ⟨componentResult', hcomponents', hsubst⟩ :=
                    ihList leftComponents rightComponents componentResult
                      hcomponents
                  rw [hcomponents']
                  cases hrun
                  exact ⟨_, rfl, hsubst⟩
          | .any, .any => cases hrun
          | .any, .skolem _ => cases hrun
          | .any, .con _ _ => cases hrun
          | .any, .prod _ => cases hrun
          | .skolem _, .any => cases hrun
          | .skolem _, .skolem _ => cases hrun
          | .skolem _, .con _ _ => cases hrun
          | .skolem _, .prod _ => cases hrun
          | .con _ _, .any => cases hrun
          | .con _ _, .prod _ => cases hrun
          | .prod _, .any => cases hrun
          | .prod _, .skolem _ => cases hrun
          | .prod _, .con _ _ => cases hrun
      · intro left right result hrun
        match left, right with
        | [], [] =>
            exact ⟨result, hrun, rfl⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solveCapList] at hrun ⊢
            cases hhead : solveCap fuel leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                obtain ⟨headResult', hhead', hheadSubst⟩ :=
                  ihCap leftHead rightHead headResult hhead
                rw [hhead']
                simp only []
                cases htail : solveCapList fuel
                    (Cap.applyList headResult.subst leftTail)
                    (Cap.applyList headResult.subst rightTail) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    obtain ⟨tailResult', htail', htailSubst⟩ :=
                      ihList _ _ tailResult htail
                    have htailPrimed : ∃ tailResultP : CapListResult
                        (Cap.applyList headResult'.subst leftTail)
                        (Cap.applyList headResult'.subst rightTail),
                        solveCapList (fuel + 1)
                            (Cap.applyList headResult'.subst leftTail)
                            (Cap.applyList headResult'.subst rightTail) =
                          some tailResultP ∧
                        tailResultP.subst = tailResult.subst := by
                      rw [hheadSubst]
                      exact ⟨tailResult', htail', htailSubst⟩
                    obtain ⟨tailResultP, htailP, htailPSubst⟩ := htailPrimed
                    rw [htailP]
                    cases hrun
                    exact ⟨_, rfl, by
                      show CapSubst.comp tailResultP.subst headResult'.subst =
                        CapSubst.comp tailResult.subst headResult.subst
                      rw [htailPSubst, hheadSubst]⟩
        | [], _ :: _ =>
            cases hrun
        | _ :: _, [] =>
            cases hrun

private theorem solveTyPair_mono_succ :
    ∀ fuel : Nat,
      (∀ (left right : Ty) (result : TyResult left right),
        solveTy fuel left right = some result →
          ∃ result' : TyResult left right,
            solveTy (fuel + 1) left right = some result' ∧
              result'.subst = result.subst) ∧
      (∀ (left right : List Ty) (result : TyListResult left right),
        solveTyList fuel left right = some result →
          ∃ result' : TyListResult left right,
            solveTyList (fuel + 1) left right = some result' ∧
              result'.subst = result.subst)
  | 0 => by
      constructor
      · intro left right result hrun
        simp [solveTy] at hrun
      · intro left right result hrun
        simp [solveTyList] at hrun
  | fuel + 1 => by
      obtain ⟨ihTy, ihList⟩ := solveTyPair_mono_succ fuel
      constructor
      · intro left right result hrun
        rw [solveTy] at hrun ⊢
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun ⊢
          exact ⟨_, rfl, by cases hrun; rfl⟩
        · rw [dif_neg hequal] at hrun ⊢
          match left, right with
          | .var varId, right =>
              exact ⟨result, hrun, rfl⟩
          | .skolem name, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .unit, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .int, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .bool, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .data leftName leftFields, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .prod leftComponents, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .fn leftDomain leftCodomain, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .matcher leftCap leftTarget, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .slot leftCap leftTarget, .var varId =>
              exact ⟨result, hrun, rfl⟩
          | .data leftName leftFields, .data rightName rightFields =>
              simp only [] at hrun ⊢
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun ⊢
                cases hfields : solveTyList fuel leftFields rightFields with
                | none => rw [hfields] at hrun; cases hrun
                | some fieldResult =>
                    rw [hfields] at hrun
                    obtain ⟨fieldResult', hfields', hsubst⟩ :=
                      ihList leftFields rightFields fieldResult hfields
                    rw [hfields']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun ⊢
              cases hcomponents :
                  solveTyList fuel leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  obtain ⟨componentResult', hcomponents', hsubst⟩ :=
                    ihList leftComponents rightComponents componentResult
                      hcomponents
                  rw [hcomponents']
                  cases hrun
                  exact ⟨_, rfl, hsubst⟩
          | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
              simp only [] at hrun ⊢
              cases hdomain : solveTy fuel leftDomain rightDomain with
              | none => rw [hdomain] at hrun; cases hrun
              | some domainResult =>
                  rw [hdomain] at hrun
                  simp only [] at hrun
                  obtain ⟨domainResult', hdomain', hdomainSubst⟩ :=
                    ihTy leftDomain rightDomain domainResult hdomain
                  rw [hdomain']
                  simp only []
                  cases hcodomain : solveTy fuel
                      (leftCodomain.applyTarget domainResult.subst)
                      (rightCodomain.applyTarget domainResult.subst) with
                  | none => rw [hcodomain] at hrun; cases hrun
                  | some codomainResult =>
                      rw [hcodomain] at hrun
                      obtain ⟨codomainResult', hcodomain', hcodomainSubst⟩ :=
                        ihTy _ _ codomainResult hcodomain
                      have hcodomainPrimed : ∃ codomainResultP : TyResult
                          (leftCodomain.applyTarget domainResult'.subst)
                          (rightCodomain.applyTarget domainResult'.subst),
                          solveTy (fuel + 1)
                              (leftCodomain.applyTarget domainResult'.subst)
                              (rightCodomain.applyTarget domainResult'.subst) =
                            some codomainResultP ∧
                          codomainResultP.subst = codomainResult.subst := by
                        rw [hdomainSubst]
                        exact ⟨codomainResult', hcodomain', hcodomainSubst⟩
                      obtain ⟨codomainResultP, hcodomainP, hcodomainPSubst⟩ :=
                        hcodomainPrimed
                      rw [hcodomainP]
                      cases hrun
                      exact ⟨_, rfl, by
                        show TySubst.comp codomainResultP.subst
                            domainResult'.subst =
                          TySubst.comp codomainResult.subst domainResult.subst
                        rw [hcodomainPSubst, hdomainSubst]⟩
          | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
              simp only [] at hrun ⊢
              by_cases hcap : leftCap = rightCap
              · rw [dif_pos hcap] at hrun ⊢
                cases htarget : solveTy fuel leftTarget rightTarget with
                | none => rw [htarget] at hrun; cases hrun
                | some targetResult =>
                    rw [htarget] at hrun
                    obtain ⟨targetResult', htarget', hsubst⟩ :=
                      ihTy leftTarget rightTarget targetResult htarget
                    rw [htarget']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hcap] at hrun
                cases hrun
          | .slot leftCap leftTarget, .slot rightCap rightTarget =>
              simp only [] at hrun ⊢
              by_cases hcap : leftCap = rightCap
              · rw [dif_pos hcap] at hrun ⊢
                cases htarget : solveTy fuel leftTarget rightTarget with
                | none => rw [htarget] at hrun; cases hrun
                | some targetResult =>
                    rw [htarget] at hrun
                    obtain ⟨targetResult', htarget', hsubst⟩ :=
                      ihTy leftTarget rightTarget targetResult htarget
                    rw [htarget']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hcap] at hrun
                cases hrun
          | .skolem _, .skolem _ =>
              cases hrun
          | .skolem _, .unit =>
              cases hrun
          | .skolem _, .int =>
              cases hrun
          | .skolem _, .bool =>
              cases hrun
          | .skolem _, .data _ _ =>
              cases hrun
          | .skolem _, .prod _ =>
              cases hrun
          | .skolem _, .fn _ _ =>
              cases hrun
          | .skolem _, .matcher _ _ =>
              cases hrun
          | .skolem _, .slot _ _ =>
              cases hrun
          | .unit, .skolem _ =>
              cases hrun
          | .unit, .unit =>
              cases hrun
          | .unit, .int =>
              cases hrun
          | .unit, .bool =>
              cases hrun
          | .unit, .data _ _ =>
              cases hrun
          | .unit, .prod _ =>
              cases hrun
          | .unit, .fn _ _ =>
              cases hrun
          | .unit, .matcher _ _ =>
              cases hrun
          | .unit, .slot _ _ =>
              cases hrun
          | .int, .skolem _ =>
              cases hrun
          | .int, .unit =>
              cases hrun
          | .int, .int =>
              cases hrun
          | .int, .bool =>
              cases hrun
          | .int, .data _ _ =>
              cases hrun
          | .int, .prod _ =>
              cases hrun
          | .int, .fn _ _ =>
              cases hrun
          | .int, .matcher _ _ =>
              cases hrun
          | .int, .slot _ _ =>
              cases hrun
          | .bool, .skolem _ =>
              cases hrun
          | .bool, .unit =>
              cases hrun
          | .bool, .int =>
              cases hrun
          | .bool, .bool =>
              cases hrun
          | .bool, .data _ _ =>
              cases hrun
          | .bool, .prod _ =>
              cases hrun
          | .bool, .fn _ _ =>
              cases hrun
          | .bool, .matcher _ _ =>
              cases hrun
          | .bool, .slot _ _ =>
              cases hrun
          | .data _ _, .skolem _ =>
              cases hrun
          | .data _ _, .unit =>
              cases hrun
          | .data _ _, .int =>
              cases hrun
          | .data _ _, .bool =>
              cases hrun
          | .data _ _, .prod _ =>
              cases hrun
          | .data _ _, .fn _ _ =>
              cases hrun
          | .data _ _, .matcher _ _ =>
              cases hrun
          | .data _ _, .slot _ _ =>
              cases hrun
          | .prod _, .skolem _ =>
              cases hrun
          | .prod _, .unit =>
              cases hrun
          | .prod _, .int =>
              cases hrun
          | .prod _, .bool =>
              cases hrun
          | .prod _, .data _ _ =>
              cases hrun
          | .prod _, .fn _ _ =>
              cases hrun
          | .prod _, .matcher _ _ =>
              cases hrun
          | .prod _, .slot _ _ =>
              cases hrun
          | .fn _ _, .skolem _ =>
              cases hrun
          | .fn _ _, .unit =>
              cases hrun
          | .fn _ _, .int =>
              cases hrun
          | .fn _ _, .bool =>
              cases hrun
          | .fn _ _, .data _ _ =>
              cases hrun
          | .fn _ _, .prod _ =>
              cases hrun
          | .fn _ _, .matcher _ _ =>
              cases hrun
          | .fn _ _, .slot _ _ =>
              cases hrun
          | .matcher _ _, .skolem _ =>
              cases hrun
          | .matcher _ _, .unit =>
              cases hrun
          | .matcher _ _, .int =>
              cases hrun
          | .matcher _ _, .bool =>
              cases hrun
          | .matcher _ _, .data _ _ =>
              cases hrun
          | .matcher _ _, .prod _ =>
              cases hrun
          | .matcher _ _, .fn _ _ =>
              cases hrun
          | .matcher _ _, .slot _ _ =>
              cases hrun
          | .slot _ _, .skolem _ =>
              cases hrun
          | .slot _ _, .unit =>
              cases hrun
          | .slot _ _, .int =>
              cases hrun
          | .slot _ _, .bool =>
              cases hrun
          | .slot _ _, .data _ _ =>
              cases hrun
          | .slot _ _, .prod _ =>
              cases hrun
          | .slot _ _, .fn _ _ =>
              cases hrun
          | .slot _ _, .matcher _ _ =>
              cases hrun
      · intro left right result hrun
        match left, right with
        | [], [] =>
            exact ⟨result, hrun, rfl⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solveTyList] at hrun ⊢
            cases hhead : solveTy fuel leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                obtain ⟨headResult', hhead', hheadSubst⟩ :=
                  ihTy leftHead rightHead headResult hhead
                rw [hhead']
                simp only []
                cases htail : solveTyList fuel
                    (Ty.applyTargetList headResult.subst leftTail)
                    (Ty.applyTargetList headResult.subst rightTail) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    obtain ⟨tailResult', htail', htailSubst⟩ :=
                      ihList _ _ tailResult htail
                    have htailPrimed : ∃ tailResultP : TyListResult
                        (Ty.applyTargetList headResult'.subst leftTail)
                        (Ty.applyTargetList headResult'.subst rightTail),
                        solveTyList (fuel + 1)
                            (Ty.applyTargetList headResult'.subst leftTail)
                            (Ty.applyTargetList headResult'.subst rightTail) =
                          some tailResultP ∧
                        tailResultP.subst = tailResult.subst := by
                      rw [hheadSubst]
                      exact ⟨tailResult', htail', htailSubst⟩
                    obtain ⟨tailResultP, htailP, htailPSubst⟩ := htailPrimed
                    rw [htailP]
                    cases hrun
                    exact ⟨_, rfl, by
                      show TySubst.comp tailResultP.subst headResult'.subst =
                        TySubst.comp tailResult.subst headResult.subst
                      rw [htailPSubst, hheadSubst]⟩
        | [], _ :: _ =>
            cases hrun
        | _ :: _, [] =>
            cases hrun

/-! ## Executable public interfaces and soundness -/

/-- Run capability unification with caller-supplied fuel. -/
def mguCapFuel (fuel : Nat) (left right : Cap) : Option CapSubst :=
  (solveCap fuel left right).map CapResult.subst

/-- Run capability-list unification with caller-supplied fuel. -/
def mguCapListFuel
    (fuel : Nat) (left right : List Cap) : Option CapSubst :=
  (solveCapList fuel left right).map CapListResult.subst

/-- Run target-sort unification with caller-supplied fuel. -/
def mguTyFuel (fuel : Nat) (left right : Ty) : Option TySubst :=
  (solveTy fuel left right).map TyResult.subst

/-- The finite target-domain ledger produced by the same solver run. -/
def mguTySupportFuel (fuel : Nat) (left right : Ty) :
    List TypePM.TyVar :=
  match solveTy fuel left right with
  | none => []
  | some result => result.supportVars

/-- Run target-list unification with caller-supplied fuel. -/
def mguTyListFuel
    (fuel : Nat) (left right : List Ty) : Option TySubst :=
  (solveTyList fuel left right).map TyListResult.subst

/-- The specification-level capability unifier with a structural fuel bound. -/
def mguCap (left right : Cap) : Option CapSubst :=
  mguCapFuel (capFuel left right) left right

/-- Capability-list unification with a structural fuel bound. -/
def mguCapList (left right : List Cap) : Option CapSubst :=
  mguCapListFuel
    (2 * (Cap.unificationWeightList left +
      Cap.unificationWeightList right + 1)) left right

/-- The specification-level target unifier with a structural fuel bound. -/
def mguTy (left right : Ty) : Option TySubst :=
  mguTyFuel (tyFuel left right) left right

/-- Finite support of the specification-level target unifier. -/
def mguTySupport (left right : Ty) : List TypePM.TyVar :=
  mguTySupportFuel (tyFuel left right) left right

/-- Target-list unification with a structural fuel bound. -/
def mguTyList (left right : List Ty) : Option TySubst :=
  mguTyListFuel
    (2 * (Ty.unificationWeightList left +
      Ty.unificationWeightList right + 1)) left right

/-- Every substitution returned by fuelled capability unification is sound. -/
theorem mguCapFuel_sound
    {fuel : Nat} {left right : Cap} {S : CapSubst}
    (hsuccess : mguCapFuel fuel left right = some S) :
    left.apply S = right.apply S := by
  unfold mguCapFuel at hsuccess
  cases hsolve : solveCap fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.sound

/-- Every substitution returned by fuelled capability-list unification is sound. -/
theorem mguCapListFuel_sound
    {fuel : Nat} {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapListFuel fuel left right = some S) :
    Cap.applyList S left = Cap.applyList S right := by
  unfold mguCapListFuel at hsuccess
  cases hsolve : solveCapList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.sound

/-- Every substitution returned by fuelled target unification is sound. -/
theorem mguTyFuel_sound
    {fuel : Nat} {left right : Ty} {S : TySubst}
    (hsuccess : mguTyFuel fuel left right = some S) :
    left.applyTarget S = right.applyTarget S := by
  unfold mguTyFuel at hsuccess
  cases hsolve : solveTy fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.sound

/-- A successful target unifier is identity away from its executable finite
support ledger. -/
theorem mguTyFuel_support
    {fuel : Nat} {left right : Ty} {S : TySubst}
    (hsuccess : mguTyFuel fuel left right = some S) :
    S.SupportWithin (mguTySupportFuel fuel left right) := by
  unfold mguTyFuel at hsuccess
  unfold mguTySupportFuel
  cases hsolve : solveTy fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have equality : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      simpa [hsolve] using result.support

/-- Every substitution returned by fuelled target-list unification is sound. -/
theorem mguTyListFuel_sound
    {fuel : Nat} {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyListFuel fuel left right = some S) :
    Ty.applyTargetList S left = Ty.applyTargetList S right := by
  unfold mguTyListFuel at hsuccess
  cases hsolve : solveTyList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.sound

/-- Soundness of the specification-level capability unifier. -/
theorem mguCap_sound
    {left right : Cap} {S : CapSubst}
    (hsuccess : mguCap left right = some S) :
    left.apply S = right.apply S := by
  exact mguCapFuel_sound hsuccess

/-- Soundness of the specification-level capability-list unifier. -/
theorem mguCapList_sound
    {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapList left right = some S) :
    Cap.applyList S left = Cap.applyList S right := by
  exact mguCapListFuel_sound hsuccess

/-- Soundness of the specification-level target unifier. -/
theorem mguTy_sound
    {left right : Ty} {S : TySubst}
    (hsuccess : mguTy left right = some S) :
    left.applyTarget S = right.applyTarget S := by
  exact mguTyFuel_sound hsuccess

/-- Finite-support certificate for the public target unifier. -/
theorem mguTy_support
    {left right : Ty} {S : TySubst}
    (hsuccess : mguTy left right = some S) :
    S.SupportWithin (mguTySupport left right) := by
  exact mguTyFuel_support hsuccess

/-- Soundness of the specification-level target-list unifier. -/
theorem mguTyList_sound
    {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyList left right = some S) :
    Ty.applyTargetList S left = Ty.applyTargetList S right := by
  exact mguTyListFuel_sound hsuccess

/-! ## Most generality of returned unifiers

The kernels are proof carrying, so every successful run also certifies that
the returned substitution is a most general unifier: any unifier of the same
constraint factors through it.  These theorems hold at every fuel; they say
nothing about solvability, so completeness of the fuel-bounded wrappers on
unifiable inputs remains a separate open question. -/

/-- Every substitution returned by fuelled capability unification is most
general. -/
theorem mguCapFuel_universal
    {fuel : Nat} {left right : Cap} {S : CapSubst}
    (hsuccess : mguCapFuel fuel left right = some S)
    {U : CapSubst} (hunify : left.apply U = right.apply U) :
    ∃ R : CapSubst, U = CapSubst.comp R S := by
  unfold mguCapFuel at hsuccess
  cases hsolve : solveCap fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.universal U hunify

/-- Every substitution returned by fuelled capability-list unification is most
general. -/
theorem mguCapListFuel_universal
    {fuel : Nat} {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapListFuel fuel left right = some S)
    {U : CapSubst} (hunify : Cap.applyList U left = Cap.applyList U right) :
    ∃ R : CapSubst, U = CapSubst.comp R S := by
  unfold mguCapListFuel at hsuccess
  cases hsolve : solveCapList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.universal U hunify

/-- Every substitution returned by fuelled target unification is most
general. -/
theorem mguTyFuel_universal
    {fuel : Nat} {left right : Ty} {S : TySubst}
    (hsuccess : mguTyFuel fuel left right = some S)
    {U : TySubst} (hunify : left.applyTarget U = right.applyTarget U) :
    ∃ R : TySubst, U = TySubst.comp R S := by
  unfold mguTyFuel at hsuccess
  cases hsolve : solveTy fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.universal U hunify

/-- Every substitution returned by fuelled target-list unification is most
general. -/
theorem mguTyListFuel_universal
    {fuel : Nat} {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyListFuel fuel left right = some S)
    {U : TySubst}
    (hunify : Ty.applyTargetList U left = Ty.applyTargetList U right) :
    ∃ R : TySubst, U = TySubst.comp R S := by
  unfold mguTyListFuel at hsuccess
  cases hsolve : solveTyList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.universal U hunify

/-- Most generality of the specification-level capability unifier. -/
theorem mguCap_universal
    {left right : Cap} {S : CapSubst}
    (hsuccess : mguCap left right = some S)
    {U : CapSubst} (hunify : left.apply U = right.apply U) :
    ∃ R : CapSubst, U = CapSubst.comp R S :=
  mguCapFuel_universal hsuccess hunify

/-- Most generality of the specification-level capability-list unifier. -/
theorem mguCapList_universal
    {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapList left right = some S)
    {U : CapSubst} (hunify : Cap.applyList U left = Cap.applyList U right) :
    ∃ R : CapSubst, U = CapSubst.comp R S :=
  mguCapListFuel_universal hsuccess hunify

/-- Most generality of the specification-level target unifier. -/
theorem mguTy_universal
    {left right : Ty} {S : TySubst}
    (hsuccess : mguTy left right = some S)
    {U : TySubst} (hunify : left.applyTarget U = right.applyTarget U) :
    ∃ R : TySubst, U = TySubst.comp R S :=
  mguTyFuel_universal hsuccess hunify

/-- Most generality of the specification-level target-list unifier. -/
theorem mguTyList_universal
    {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyList left right = some S)
    {U : TySubst}
    (hunify : Ty.applyTargetList U left = Ty.applyTargetList U right) :
    ∃ R : TySubst, U = TySubst.comp R S :=
  mguTyListFuel_universal hsuccess hunify

/-! ## Fuel monotonicity of the public fuelled interfaces

Success of a fuelled kernel is stable under enlarging the fuel, with the same
returned substitution.  Together with the most-generality certificates this
sharpens the remaining solvability question to the existence of one
sufficient fuel: no larger fuel can change or lose an established solution. -/

/-- Success of fuelled capability unification is preserved by one more unit
of fuel. -/
theorem mguCapFuel_mono_succ
    {fuel : Nat} {left right : Cap} {S : CapSubst}
    (hsuccess : mguCapFuel fuel left right = some S) :
    mguCapFuel (fuel + 1) left right = some S := by
  unfold mguCapFuel at hsuccess ⊢
  cases hsolve : solveCap fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      obtain ⟨result', hsolve', hsubst⟩ :=
        (solveCapPair_mono_succ fuel).1 left right result hsolve
      rw [hsolve']
      rw [hsolve] at hsuccess
      simpa [hsubst] using hsuccess

/-- Success of fuelled capability-list unification is preserved by one more
unit of fuel. -/
theorem mguCapListFuel_mono_succ
    {fuel : Nat} {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapListFuel fuel left right = some S) :
    mguCapListFuel (fuel + 1) left right = some S := by
  unfold mguCapListFuel at hsuccess ⊢
  cases hsolve : solveCapList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      obtain ⟨result', hsolve', hsubst⟩ :=
        (solveCapPair_mono_succ fuel).2 left right result hsolve
      rw [hsolve']
      rw [hsolve] at hsuccess
      simpa [hsubst] using hsuccess

/-- Success of fuelled target unification is preserved by one more unit of
fuel. -/
theorem mguTyFuel_mono_succ
    {fuel : Nat} {left right : Ty} {S : TySubst}
    (hsuccess : mguTyFuel fuel left right = some S) :
    mguTyFuel (fuel + 1) left right = some S := by
  unfold mguTyFuel at hsuccess ⊢
  cases hsolve : solveTy fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      obtain ⟨result', hsolve', hsubst⟩ :=
        (solveTyPair_mono_succ fuel).1 left right result hsolve
      rw [hsolve']
      rw [hsolve] at hsuccess
      simpa [hsubst] using hsuccess

/-- Success of fuelled target-list unification is preserved by one more unit
of fuel. -/
theorem mguTyListFuel_mono_succ
    {fuel : Nat} {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyListFuel fuel left right = some S) :
    mguTyListFuel (fuel + 1) left right = some S := by
  unfold mguTyListFuel at hsuccess ⊢
  cases hsolve : solveTyList fuel left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      obtain ⟨result', hsolve', hsubst⟩ :=
        (solveTyPair_mono_succ fuel).2 left right result hsolve
      rw [hsolve']
      rw [hsolve] at hsuccess
      simpa [hsubst] using hsuccess

/-- Success of fuelled capability unification is preserved by any larger
fuel, with the same substitution. -/
theorem mguCapFuel_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {left right : Cap} {S : CapSubst}
    (hsuccess : mguCapFuel fuel left right = some S) :
    mguCapFuel fuel' left right = some S := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  induction gap with
  | zero => exact hsuccess
  | succ gap ih =>
      exact mguCapFuel_mono_succ (ih (Nat.le_add_right fuel gap))

/-- Success of fuelled capability-list unification is preserved by any larger
fuel, with the same substitution. -/
theorem mguCapListFuel_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {left right : List Cap} {S : CapSubst}
    (hsuccess : mguCapListFuel fuel left right = some S) :
    mguCapListFuel fuel' left right = some S := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  induction gap with
  | zero => exact hsuccess
  | succ gap ih =>
      exact mguCapListFuel_mono_succ (ih (Nat.le_add_right fuel gap))

/-- Success of fuelled target unification is preserved by any larger fuel,
with the same substitution. -/
theorem mguTyFuel_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {left right : Ty} {S : TySubst}
    (hsuccess : mguTyFuel fuel left right = some S) :
    mguTyFuel fuel' left right = some S := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  induction gap with
  | zero => exact hsuccess
  | succ gap ih =>
      exact mguTyFuel_mono_succ (ih (Nat.le_add_right fuel gap))

/-- Success of fuelled target-list unification is preserved by any larger
fuel, with the same substitution. -/
theorem mguTyListFuel_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {left right : List Ty} {S : TySubst}
    (hsuccess : mguTyListFuel fuel left right = some S) :
    mguTyListFuel fuel' left right = some S := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  induction gap with
  | zero => exact hsuccess
  | succ gap ih =>
      exact mguTyListFuel_mono_succ (ih (Nat.le_add_right fuel gap))

/-- Any fuelled capability success at fuel below the structural bound is
already the specification-level answer. -/
theorem mguCap_of_fuel_le
    {fuel : Nat} {left right : Cap} {S : CapSubst}
    (hle : fuel ≤ capFuel left right)
    (hsuccess : mguCapFuel fuel left right = some S) :
    mguCap left right = some S :=
  mguCapFuel_mono hle hsuccess

/-- Any fuelled target success at fuel below the structural bound is already
the specification-level answer. -/
theorem mguTy_of_fuel_le
    {fuel : Nat} {left right : Ty} {S : TySubst}
    (hle : fuel ≤ tyFuel left right)
    (hsuccess : mguTyFuel fuel left right = some S) :
    mguTy left right = some S :=
  mguTyFuel_mono hle hsuccess

/-! ## Variable accounting under substitution

Solvability completeness needs exact control of the variables occurring
after a substitution and the classical occurs-check contradiction.  These
lemmas characterise both sorts. -/

mutual

/-- Variables of an applied capability are the image variables of its
variables. -/
theorem Cap.fcv_apply :
    ∀ (cap : Cap) (S : CapSubst),
      (cap.apply S).fcv = cap.fcv.flatMap fun x => (S x).fcv
  | .any, _ => rfl
  | .var _, _ => by simp [Cap.apply, Cap.fcv]
  | .skolem _, _ => rfl
  | .con _ children, S => by
      simp only [Cap.apply, Cap.fcv]
      exact Cap.fcvList_applyList children S
  | .prod components, S => by
      simp only [Cap.apply, Cap.fcv]
      exact Cap.fcvList_applyList components S

/-- List form of `Cap.fcv_apply`. -/
theorem Cap.fcvList_applyList :
    ∀ (caps : List Cap) (S : CapSubst),
      Cap.fcvList (Cap.applyList S caps) =
        (Cap.fcvList caps).flatMap fun x => (S x).fcv
  | [], _ => rfl
  | cap :: caps, S => by
      simp only [Cap.applyList, Cap.fcvList, List.flatMap_append,
        Cap.fcv_apply cap S, Cap.fcvList_applyList caps S]

end

mutual

/-- Target variables of an applied type are the image variables of its
target variables. -/
theorem Ty.ftv_applyTarget :
    ∀ (τ : Ty) (S : TySubst),
      (τ.applyTarget S).ftv = τ.ftv.flatMap fun x => (S x).ftv
  | .var _, _ => by simp [Ty.applyTarget, Ty.ftv]
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data _ fields, S => by
      simp only [Ty.applyTarget, Ty.ftv]
      exact Ty.ftvList_applyTargetList fields S
  | .prod components, S => by
      simp only [Ty.applyTarget, Ty.ftv]
      exact Ty.ftvList_applyTargetList components S
  | .fn domain codomain, S => by
      simp only [Ty.applyTarget, Ty.ftv, List.flatMap_append,
        Ty.ftv_applyTarget domain S, Ty.ftv_applyTarget codomain S]
  | .matcher capability target, S => by
      simp only [Ty.applyTarget, Ty.ftv]
      exact Ty.ftv_applyTarget target S
  | .slot capability target, S => by
      simp only [Ty.applyTarget, Ty.ftv]
      exact Ty.ftv_applyTarget target S

/-- List form of `Ty.ftv_applyTarget`. -/
theorem Ty.ftvList_applyTargetList :
    ∀ (types : List Ty) (S : TySubst),
      Ty.ftvList (Ty.applyTargetList S types) =
        (Ty.ftvList types).flatMap fun x => (S x).ftv
  | [], _ => rfl
  | τ :: types, S => by
      simp only [Ty.applyTargetList, Ty.ftvList, List.flatMap_append,
        Ty.ftv_applyTarget τ S, Ty.ftvList_applyTargetList types S]

end

mutual

/-- The image of an occurring variable is no heavier than the whole
applied capability. -/
theorem Cap.weight_apply_le_of_mem :
    ∀ (cap : Cap) (S : CapSubst) (x : CapVar),
      x ∈ cap.fcv →
        Cap.unificationWeight (S x) ≤ Cap.unificationWeight (cap.apply S)
  | .var candidate, S, x, hmem => by
      simp only [Cap.fcv, List.mem_singleton] at hmem
      subst hmem
      simp [Cap.apply]
  | .con _ children, S, x, hmem => by
      simp only [Cap.fcv] at hmem
      have hlt := Cap.weightList_applyList_lt_of_mem children S x hmem
      simp only [Cap.apply, Cap.unificationWeight]
      omega
  | .prod components, S, x, hmem => by
      simp only [Cap.fcv] at hmem
      have hlt := Cap.weightList_applyList_lt_of_mem components S x hmem
      simp only [Cap.apply, Cap.unificationWeight]
      omega

/-- The image of a variable occurring in a list is strictly lighter than the
whole applied list. -/
theorem Cap.weightList_applyList_lt_of_mem :
    ∀ (caps : List Cap) (S : CapSubst) (x : CapVar),
      x ∈ Cap.fcvList caps →
        Cap.unificationWeight (S x) <
          Cap.unificationWeightList (Cap.applyList S caps)
  | cap :: caps, S, x, hmem => by
      simp only [Cap.fcvList, List.mem_append] at hmem
      simp only [Cap.applyList, Cap.unificationWeightList]
      cases hmem with
      | inl hhead =>
          have hle := Cap.weight_apply_le_of_mem cap S x hhead
          omega
      | inr htail =>
          have hlt := Cap.weightList_applyList_lt_of_mem caps S x htail
          omega

end

/-- Occurrence in a non-variable capability makes the image strictly
lighter. -/
theorem Cap.weight_apply_lt_of_mem_of_ne_var
    (cap : Cap) (S : CapSubst) (x : CapVar)
    (hmem : x ∈ cap.fcv) (hne : cap ≠ .var x) :
    Cap.unificationWeight (S x) < Cap.unificationWeight (cap.apply S) := by
  match cap with
  | .any => simp [Cap.fcv] at hmem
  | .skolem _ => simp [Cap.fcv] at hmem
  | .var candidate =>
      simp only [Cap.fcv, List.mem_singleton] at hmem
      subst hmem
      exact absurd rfl hne
  | .con name children =>
      simp only [Cap.fcv] at hmem
      have hlt := Cap.weightList_applyList_lt_of_mem children S x hmem
      simp only [Cap.apply, Cap.unificationWeight]
      omega
  | .prod components =>
      simp only [Cap.fcv] at hmem
      have hlt := Cap.weightList_applyList_lt_of_mem components S x hmem
      simp only [Cap.apply, Cap.unificationWeight]
      omega

/-- The classical occurs-check contradiction for the capability sort. -/
theorem Cap.not_unifiable_of_occurs
    (varId : CapVar) (cap : Cap)
    (hne : cap ≠ .var varId) (hmem : varId ∈ cap.fcv) (U : CapSubst) :
    (Cap.var varId).apply U ≠ cap.apply U := by
  intro hunify
  have hlt := Cap.weight_apply_lt_of_mem_of_ne_var cap U varId hmem hne
  have heq : U varId = cap.apply U := by simpa [Cap.apply] using hunify
  rw [heq] at hlt
  omega

mutual

/-- The image of an occurring target variable is no heavier than the whole
applied type. -/
theorem Ty.weight_applyTarget_le_of_mem :
    ∀ (τ : Ty) (S : TySubst) (x : TypePM.TyVar),
      x ∈ τ.ftv →
        Ty.unificationWeight (S x) ≤
          Ty.unificationWeight (τ.applyTarget S)
  | .var candidate, S, x, hmem => by
      simp only [Ty.ftv, List.mem_singleton] at hmem
      subst hmem
      simp [Ty.applyTarget]
  | .data _ fields, S, x, hmem => by
      simp only [Ty.ftv] at hmem
      have hlt := Ty.weightList_applyTargetList_lt_of_mem fields S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .prod components, S, x, hmem => by
      simp only [Ty.ftv] at hmem
      have hlt := Ty.weightList_applyTargetList_lt_of_mem components S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .fn domain codomain, S, x, hmem => by
      simp only [Ty.ftv, List.mem_append] at hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      cases hmem with
      | inl hdomain =>
          have hle := Ty.weight_applyTarget_le_of_mem domain S x hdomain
          omega
      | inr hcodomain =>
          have hle := Ty.weight_applyTarget_le_of_mem codomain S x hcodomain
          omega
  | .matcher _ target, S, x, hmem => by
      simp only [Ty.ftv] at hmem
      have hle := Ty.weight_applyTarget_le_of_mem target S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .slot _ target, S, x, hmem => by
      simp only [Ty.ftv] at hmem
      have hle := Ty.weight_applyTarget_le_of_mem target S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega

/-- The image of a target variable occurring in a list is strictly lighter
than the whole applied list. -/
theorem Ty.weightList_applyTargetList_lt_of_mem :
    ∀ (types : List Ty) (S : TySubst) (x : TypePM.TyVar),
      x ∈ Ty.ftvList types →
        Ty.unificationWeight (S x) <
          Ty.unificationWeightList (Ty.applyTargetList S types)
  | τ :: types, S, x, hmem => by
      simp only [Ty.ftvList, List.mem_append] at hmem
      simp only [Ty.applyTargetList, Ty.unificationWeightList]
      cases hmem with
      | inl hhead =>
          have hle := Ty.weight_applyTarget_le_of_mem τ S x hhead
          omega
      | inr htail =>
          have hlt := Ty.weightList_applyTargetList_lt_of_mem types S x htail
          omega

end

/-- Occurrence in a non-variable target type makes the image strictly
lighter. -/
theorem Ty.weight_applyTarget_lt_of_mem_of_ne_var
    (τ : Ty) (S : TySubst) (x : TypePM.TyVar)
    (hmem : x ∈ τ.ftv) (hne : τ ≠ .var x) :
    Ty.unificationWeight (S x) < Ty.unificationWeight (τ.applyTarget S) := by
  match τ with
  | .skolem _ => simp [Ty.ftv] at hmem
  | .unit => simp [Ty.ftv] at hmem
  | .int => simp [Ty.ftv] at hmem
  | .bool => simp [Ty.ftv] at hmem
  | .var candidate =>
      simp only [Ty.ftv, List.mem_singleton] at hmem
      subst hmem
      exact absurd rfl hne
  | .data name fields =>
      simp only [Ty.ftv] at hmem
      have hlt := Ty.weightList_applyTargetList_lt_of_mem fields S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .prod components =>
      simp only [Ty.ftv] at hmem
      have hlt := Ty.weightList_applyTargetList_lt_of_mem components S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .fn domain codomain =>
      simp only [Ty.ftv, List.mem_append] at hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      cases hmem with
      | inl hdomain =>
          have hle := Ty.weight_applyTarget_le_of_mem domain S x hdomain
          omega
      | inr hcodomain =>
          have hle := Ty.weight_applyTarget_le_of_mem codomain S x hcodomain
          omega
  | .matcher capability target =>
      simp only [Ty.ftv] at hmem
      have hle := Ty.weight_applyTarget_le_of_mem target S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega
  | .slot capability target =>
      simp only [Ty.ftv] at hmem
      have hle := Ty.weight_applyTarget_le_of_mem target S x hmem
      simp only [Ty.applyTarget, Ty.unificationWeight]
      omega

/-- The classical occurs-check contradiction for the target sort. -/
theorem Ty.not_unifiable_of_occurs
    (varId : TypePM.TyVar) (τ : Ty)
    (hne : τ ≠ .var varId) (hmem : varId ∈ τ.ftv) (U : TySubst) :
    (Ty.var varId).applyTarget U ≠ τ.applyTarget U := by
  intro hunify
  have hlt := Ty.weight_applyTarget_lt_of_mem_of_ne_var τ U varId hmem hne
  have heq : U varId = τ.applyTarget U := by
    simpa [Ty.applyTarget] using hunify
  rw [heq] at hlt
  omega

/-! ## Variable-elimination certificates for successful runs

A successful kernel run only mentions constraint variables in its images,
and on a genuinely unequal constraint it eliminates at least one constraint
variable outright.  These certificates drive the well-founded recursion of
solvability completeness. -/

/-- Every image variable is the preimage itself or drawn from `allowed`. -/
private def CapRange (S : CapSubst) (allowed : List CapVar) : Prop :=
  ∀ x y, y ∈ (S x).fcv → y = x ∨ y ∈ allowed

/-- No image of the substitution mentions `v`. -/
private def CapElim (S : CapSubst) (v : CapVar) : Prop :=
  ∀ x, v ∉ (S x).fcv

private theorem CapRange.id (allowed : List CapVar) :
    CapRange CapSubst.id allowed := by
  intro x y hy
  simp only [CapSubst.id, Cap.fcv, List.mem_singleton] at hy
  exact Or.inl hy

private theorem CapRange.single
    {varId : CapVar} {replacement : Cap} {allowed : List CapVar}
    (hrepl : ∀ y, y ∈ replacement.fcv → y ∈ allowed) :
    CapRange (CapSubst.single varId replacement) allowed := by
  intro x y hy
  by_cases hx : varId = x
  · subst hx
    simp only [CapSubst.single] at hy
    exact Or.inr (hrepl y hy)
  · simp only [CapSubst.single, if_neg hx, Cap.fcv,
      List.mem_singleton] at hy
    exact Or.inl hy

private theorem CapRange.mono
    {S : CapSubst} {allowed allowed' : List CapVar}
    (hrange : CapRange S allowed)
    (hsub : ∀ y, y ∈ allowed → y ∈ allowed') :
    CapRange S allowed' := by
  intro x y hy
  rcases hrange x y hy with rfl | hmem
  · exact Or.inl rfl
  · exact Or.inr (hsub y hmem)

private theorem CapRange.comp
    {S₂ S₁ : CapSubst} {outer inner : List CapVar}
    (hinner : CapRange S₁ inner) (houter : CapRange S₂ outer)
    (hsub : ∀ y, y ∈ outer → y ∈ inner) :
    CapRange (CapSubst.comp S₂ S₁) inner := by
  intro x y hy
  rw [show CapSubst.comp S₂ S₁ x = (S₁ x).apply S₂ from rfl,
    Cap.fcv_apply] at hy
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy
  rcases houter z y hyz with rfl | hyOuter
  · exact hinner x y hz
  · exact Or.inr (hsub y hyOuter)

private theorem CapElim.comp_outer
    {S₂ S₁ : CapSubst} {v : CapVar} (helim : CapElim S₂ v) :
    CapElim (CapSubst.comp S₂ S₁) v := by
  intro x hv
  rw [show CapSubst.comp S₂ S₁ x = (S₁ x).apply S₂ from rfl,
    Cap.fcv_apply] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem CapElim.comp_inner
    {S₂ S₁ : CapSubst} {v : CapVar} {outer : List CapVar}
    (helim : CapElim S₁ v) (hrange : CapRange S₂ outer)
    (hvOuter : v ∉ outer) :
    CapElim (CapSubst.comp S₂ S₁) v := by
  intro x hv
  rw [show CapSubst.comp S₂ S₁ x = (S₁ x).apply S₂ from rfl,
    Cap.fcv_apply] at hv
  obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.mp hv
  rcases hrange z v hvz with rfl | hvOuter'
  · exact helim x hz
  · exact hvOuter hvOuter'

private theorem CapElim.not_mem_applyList
    {S : CapSubst} {v : CapVar} (helim : CapElim S v)
    (caps : List Cap) :
    v ∉ Cap.fcvList (Cap.applyList S caps) := by
  intro hv
  rw [Cap.fcvList_applyList] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem CapRange.applyList_mem
    {S : CapSubst} {allowed : List CapVar} {caps : List Cap}
    {y : CapVar}
    (hrange : CapRange S allowed)
    (hmem : y ∈ Cap.fcvList (Cap.applyList S caps)) :
    y ∈ Cap.fcvList caps ∨ y ∈ allowed := by
  rw [Cap.fcvList_applyList] at hmem
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hmem
  rcases hrange z y hyz with rfl | hyAllowed
  · exact Or.inl hz
  · exact Or.inr hyAllowed

/-- A successful run on a syntactically equal pair returns the identity. -/
private theorem solveCap_eq_self
    {fuel : Nat} {cap : Cap} {result : CapResult cap cap}
    (hrun : solveCap fuel cap cap = some result) :
    result.subst = CapSubst.id := by
  match fuel with
  | 0 => simp [solveCap] at hrun
  | fuel + 1 =>
      rw [solveCap] at hrun
      rw [dif_pos rfl] at hrun
      cases hrun
      rfl

/-- Range and elimination certificates for the capability kernels. -/
private theorem solveCapPair_varCert :
    ∀ fuel : Nat,
      (∀ (left right : Cap) (result : CapResult left right),
        solveCap fuel left right = some result →
          CapRange result.subst (left.fcv ++ right.fcv) ∧
          (left ≠ right →
            ∃ v, v ∈ left.fcv ++ right.fcv ∧ CapElim result.subst v)) ∧
      (∀ (left right : List Cap) (result : CapListResult left right),
        solveCapList fuel left right = some result →
          CapRange result.subst (Cap.fcvList left ++ Cap.fcvList right) ∧
          (left ≠ right →
            ∃ v, v ∈ Cap.fcvList left ++ Cap.fcvList right ∧
              CapElim result.subst v))
  | 0 => by
      constructor
      · intro left right result hrun
        simp [solveCap] at hrun
      · intro left right result hrun
        simp [solveCapList] at hrun
  | fuel + 1 => by
      obtain ⟨ihCap, ihList⟩ := solveCapPair_varCert fuel
      constructor
      · intro left right result hrun
        rw [solveCap] at hrun
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun
          cases hrun
          exact ⟨CapRange.id _, fun hne => absurd hequal hne⟩
        · rw [dif_neg hequal] at hrun
          match left, right with
          | .var varId, right =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ right.fcv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨CapRange.single fun y hy =>
                  List.mem_append.mpr (Or.inr hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inl (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [CapSubst.single] at hz
                  exact hoccurs hz
                · simp only [CapSubst.single, if_neg hvz, Cap.fcv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .con leftName leftChildren, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Cap.con leftName leftChildren).fcv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨CapRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [CapSubst.single] at hz
                  exact hoccurs hz
                · simp only [CapSubst.single, if_neg hvz, Cap.fcv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .prod leftComponents, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Cap.prod leftComponents).fcv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨CapRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [CapSubst.single] at hz
                  exact hoccurs hz
                · simp only [CapSubst.single, if_neg hvz, Cap.fcv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .any, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ Cap.any.fcv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨CapRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [CapSubst.single] at hz
                  exact hoccurs hz
                · simp only [CapSubst.single, if_neg hvz, Cap.fcv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .skolem name, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Cap.skolem name).fcv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨CapRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [CapSubst.single] at hz
                  exact hoccurs hz
                · simp only [CapSubst.single, if_neg hvz, Cap.fcv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .con leftName leftChildren, .con rightName rightChildren =>
              simp only [] at hrun
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun
                cases hchildren : solveCapList fuel leftChildren rightChildren
                  with
                | none => rw [hchildren] at hrun; cases hrun
                | some childResult =>
                    rw [hchildren] at hrun
                    cases hrun
                    obtain ⟨ihRange, ihElim⟩ :=
                      ihList leftChildren rightChildren childResult hchildren
                    refine ⟨ihRange, fun hne => ?_⟩
                    have hchildrenNe : leftChildren ≠ rightChildren :=
                      fun hch => hne (by rw [hname, hch])
                    obtain ⟨v, hvmem, hvelim⟩ := ihElim hchildrenNe
                    exact ⟨v, hvmem, hvelim⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun
              cases hcomponents :
                  solveCapList fuel leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  cases hrun
                  obtain ⟨ihRange, ihElim⟩ :=
                    ihList leftComponents rightComponents componentResult
                      hcomponents
                  refine ⟨ihRange, fun hne => ?_⟩
                  have hcomponentsNe : leftComponents ≠ rightComponents :=
                    fun hch => hne (by rw [hch])
                  obtain ⟨v, hvmem, hvelim⟩ := ihElim hcomponentsNe
                  exact ⟨v, hvmem, hvelim⟩
          | .any, .any => cases hrun
          | .any, .skolem _ => cases hrun
          | .any, .con _ _ => cases hrun
          | .any, .prod _ => cases hrun
          | .skolem _, .any => cases hrun
          | .skolem _, .skolem _ => cases hrun
          | .skolem _, .con _ _ => cases hrun
          | .skolem _, .prod _ => cases hrun
          | .con _ _, .any => cases hrun
          | .con _ _, .prod _ => cases hrun
          | .prod _, .any => cases hrun
          | .prod _, .skolem _ => cases hrun
          | .prod _, .con _ _ => cases hrun
      · intro left right result hrun
        match left, right with
        | [], [] =>
            rw [solveCapList] at hrun
            cases hrun
            exact ⟨CapRange.id _, fun hne => absurd rfl hne⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solveCapList] at hrun
            cases hhead : solveCap fuel leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                cases htail : solveCapList fuel
                    (Cap.applyList headResult.subst leftTail)
                    (Cap.applyList headResult.subst rightTail) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    cases hrun
                    obtain ⟨headRange, headElim⟩ :=
                      ihCap leftHead rightHead headResult hhead
                    obtain ⟨tailRange, tailElim⟩ := ihList _ _ tailResult htail
                    have hallowed : ∀ y,
                        y ∈ Cap.fcvList (Cap.applyList headResult.subst
                            leftTail) ++
                          Cap.fcvList (Cap.applyList headResult.subst
                            rightTail) →
                        y ∈ Cap.fcvList (leftHead :: leftTail) ++
                          Cap.fcvList (rightHead :: rightTail) := by
                      intro y hy
                      simp only [Cap.fcvList, List.mem_append] at hy ⊢
                      rcases hy with hyl | hyr
                      · rcases headRange.applyList_mem hyl with hmem | hmem
                        · exact Or.inl (Or.inr hmem)
                        · rcases List.mem_append.mp hmem with h | h
                          · exact Or.inl (Or.inl h)
                          · exact Or.inr (Or.inl h)
                      · rcases headRange.applyList_mem hyr with hmem | hmem
                        · exact Or.inr (Or.inr hmem)
                        · rcases List.mem_append.mp hmem with h | h
                          · exact Or.inl (Or.inl h)
                          · exact Or.inr (Or.inl h)
                    have headRange' : CapRange headResult.subst
                        (Cap.fcvList (leftHead :: leftTail) ++
                          Cap.fcvList (rightHead :: rightTail)) := by
                      refine headRange.mono fun y hy => ?_
                      simp only [Cap.fcvList, List.mem_append] at hy ⊢
                      rcases hy with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
                    refine ⟨CapRange.comp headRange'
                      (tailRange.mono fun y hy => hy) hallowed, fun hne => ?_⟩
                    by_cases hheadEq : leftHead = rightHead
                    · subst hheadEq
                      have hid := solveCap_eq_self hhead
                      have htailNe : leftTail ≠ rightTail :=
                        fun hch => hne (by rw [hch])
                      have htailNe' :
                          Cap.applyList headResult.subst leftTail ≠
                            Cap.applyList headResult.subst rightTail := by
                        rw [hid, Cap.applyList_id, Cap.applyList_id]
                        exact htailNe
                      obtain ⟨v, hvmem, hvelim⟩ := tailElim htailNe'
                      rw [hid, Cap.applyList_id, Cap.applyList_id] at hvmem
                      refine ⟨v, ?_, hvelim.comp_outer⟩
                      simp only [Cap.fcvList, List.mem_append] at hvmem ⊢
                      rcases hvmem with h | h
                      · exact Or.inl (Or.inr h)
                      · exact Or.inr (Or.inr h)
                    · obtain ⟨v, hvmem, hvelim⟩ := headElim hheadEq
                      have hvOuter : v ∉
                          Cap.fcvList (Cap.applyList headResult.subst
                            leftTail) ++
                          Cap.fcvList (Cap.applyList headResult.subst
                            rightTail) := by
                        intro hv
                        rcases List.mem_append.mp hv with hv | hv
                        · exact hvelim.not_mem_applyList _ hv
                        · exact hvelim.not_mem_applyList _ hv
                      refine ⟨v, ?_,
                        hvelim.comp_inner (tailRange.mono fun y hy => hy)
                          hvOuter⟩
                      simp only [List.mem_append] at hvmem
                      simp only [Cap.fcvList, List.mem_append]
                      rcases hvmem with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
        | [], _ :: _ =>
            cases hrun
        | _ :: _, [] =>
            cases hrun

/-- Every image target variable is the preimage itself or drawn from
`allowed`. -/
private def TyRange (S : TySubst) (allowed : List TypePM.TyVar) : Prop :=
  ∀ x y, y ∈ (S x).ftv → y = x ∨ y ∈ allowed

/-- No image of the target substitution mentions `v`. -/
private def TyElim (S : TySubst) (v : TypePM.TyVar) : Prop :=
  ∀ x, v ∉ (S x).ftv

private theorem TyRange.id (allowed : List TypePM.TyVar) :
    TyRange TySubst.id allowed := by
  intro x y hy
  simp only [TySubst.id, Ty.ftv, List.mem_singleton] at hy
  exact Or.inl hy

private theorem TyRange.single
    {varId : TypePM.TyVar} {replacement : Ty} {allowed : List TypePM.TyVar}
    (hrepl : ∀ y, y ∈ replacement.ftv → y ∈ allowed) :
    TyRange (TySubst.single varId replacement) allowed := by
  intro x y hy
  by_cases hx : varId = x
  · subst hx
    simp only [TySubst.single] at hy
    exact Or.inr (hrepl y hy)
  · simp only [TySubst.single, if_neg hx, Ty.ftv,
      List.mem_singleton] at hy
    exact Or.inl hy

private theorem TyRange.mono
    {S : TySubst} {allowed allowed' : List TypePM.TyVar}
    (hrange : TyRange S allowed)
    (hsub : ∀ y, y ∈ allowed → y ∈ allowed') :
    TyRange S allowed' := by
  intro x y hy
  rcases hrange x y hy with rfl | hmem
  · exact Or.inl rfl
  · exact Or.inr (hsub y hmem)

private theorem TyRange.comp
    {S₂ S₁ : TySubst} {outer inner : List TypePM.TyVar}
    (hinner : TyRange S₁ inner) (houter : TyRange S₂ outer)
    (hsub : ∀ y, y ∈ outer → y ∈ inner) :
    TyRange (TySubst.comp S₂ S₁) inner := by
  intro x y hy
  rw [show TySubst.comp S₂ S₁ x = (S₁ x).applyTarget S₂ from rfl,
    Ty.ftv_applyTarget] at hy
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy
  rcases houter z y hyz with rfl | hyOuter
  · exact hinner x y hz
  · exact Or.inr (hsub y hyOuter)

private theorem TyElim.comp_outer
    {S₂ S₁ : TySubst} {v : TypePM.TyVar} (helim : TyElim S₂ v) :
    TyElim (TySubst.comp S₂ S₁) v := by
  intro x hv
  rw [show TySubst.comp S₂ S₁ x = (S₁ x).applyTarget S₂ from rfl,
    Ty.ftv_applyTarget] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem TyElim.comp_inner
    {S₂ S₁ : TySubst} {v : TypePM.TyVar} {outer : List TypePM.TyVar}
    (helim : TyElim S₁ v) (hrange : TyRange S₂ outer)
    (hvOuter : v ∉ outer) :
    TyElim (TySubst.comp S₂ S₁) v := by
  intro x hv
  rw [show TySubst.comp S₂ S₁ x = (S₁ x).applyTarget S₂ from rfl,
    Ty.ftv_applyTarget] at hv
  obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.mp hv
  rcases hrange z v hvz with rfl | hvOuter'
  · exact helim x hz
  · exact hvOuter hvOuter'

private theorem TyElim.not_mem_applyTarget
    {S : TySubst} {v : TypePM.TyVar} (helim : TyElim S v) (τ : Ty) :
    v ∉ (τ.applyTarget S).ftv := by
  intro hv
  rw [Ty.ftv_applyTarget] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem TyElim.not_mem_applyTargetList
    {S : TySubst} {v : TypePM.TyVar} (helim : TyElim S v)
    (types : List Ty) :
    v ∉ Ty.ftvList (Ty.applyTargetList S types) := by
  intro hv
  rw [Ty.ftvList_applyTargetList] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem TyRange.applyTarget_mem
    {S : TySubst} {allowed : List TypePM.TyVar} {τ : Ty}
    {y : TypePM.TyVar}
    (hrange : TyRange S allowed)
    (hmem : y ∈ (τ.applyTarget S).ftv) :
    y ∈ τ.ftv ∨ y ∈ allowed := by
  rw [Ty.ftv_applyTarget] at hmem
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hmem
  rcases hrange z y hyz with rfl | hyAllowed
  · exact Or.inl hz
  · exact Or.inr hyAllowed

private theorem TyRange.applyTargetList_mem
    {S : TySubst} {allowed : List TypePM.TyVar} {types : List Ty}
    {y : TypePM.TyVar}
    (hrange : TyRange S allowed)
    (hmem : y ∈ Ty.ftvList (Ty.applyTargetList S types)) :
    y ∈ Ty.ftvList types ∨ y ∈ allowed := by
  rw [Ty.ftvList_applyTargetList] at hmem
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hmem
  rcases hrange z y hyz with rfl | hyAllowed
  · exact Or.inl hz
  · exact Or.inr hyAllowed

/-- A successful target run on a syntactically equal pair returns the
identity. -/
private theorem solveTy_eq_self
    {fuel : Nat} {τ : Ty} {result : TyResult τ τ}
    (hrun : solveTy fuel τ τ = some result) :
    result.subst = TySubst.id := by
  match fuel with
  | 0 => simp [solveTy] at hrun
  | fuel + 1 =>
      rw [solveTy] at hrun
      rw [dif_pos rfl] at hrun
      cases hrun
      rfl

/-- Range and elimination certificates for the target kernels. -/
private theorem solveTyPair_varCert :
    ∀ fuel : Nat,
      (∀ (left right : Ty) (result : TyResult left right),
        solveTy fuel left right = some result →
          TyRange result.subst (left.ftv ++ right.ftv) ∧
          (left ≠ right →
            ∃ v, v ∈ left.ftv ++ right.ftv ∧ TyElim result.subst v)) ∧
      (∀ (left right : List Ty) (result : TyListResult left right),
        solveTyList fuel left right = some result →
          TyRange result.subst (Ty.ftvList left ++ Ty.ftvList right) ∧
          (left ≠ right →
            ∃ v, v ∈ Ty.ftvList left ++ Ty.ftvList right ∧
              TyElim result.subst v))
  | 0 => by
      constructor
      · intro left right result hrun
        simp [solveTy] at hrun
      · intro left right result hrun
        simp [solveTyList] at hrun
  | fuel + 1 => by
      obtain ⟨ihTy, ihList⟩ := solveTyPair_varCert fuel
      constructor
      · intro left right result hrun
        rw [solveTy] at hrun
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun
          cases hrun
          exact ⟨TyRange.id _, fun hne => absurd hequal hne⟩
        · rw [dif_neg hequal] at hrun
          match left, right with
          | .var varId, right =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ right.ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inr hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inl (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .skolem skName, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.skolem skName).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .unit, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.unit).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .int, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.int).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .bool, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.bool).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .data dName dFields, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.data dName dFields).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .prod pComponents, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.prod pComponents).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .fn fDomain fCodomain, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.fn fDomain fCodomain).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .matcher mCap mTarget, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.matcher mCap mTarget).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .slot sCap sTarget, .var varId =>
              simp only [] at hrun
              by_cases hoccurs : varId ∈ (Ty.slot sCap sTarget).ftv
              · rw [dif_pos hoccurs] at hrun
                cases hrun
              · rw [dif_neg hoccurs] at hrun
                cases hrun
                refine ⟨TyRange.single fun y hy =>
                  List.mem_append.mpr (Or.inl hy), fun _ => ?_⟩
                refine ⟨varId, List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl)), fun z hz => ?_⟩
                by_cases hvz : varId = z
                · subst hvz
                  simp only [TySubst.single] at hz
                  exact hoccurs hz
                · simp only [TySubst.single, if_neg hvz, Ty.ftv,
                    List.mem_singleton] at hz
                  exact hvz hz
          | .data leftName leftFields, .data rightName rightFields =>
              simp only [] at hrun
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun
                cases hfields : solveTyList fuel leftFields rightFields with
                | none => rw [hfields] at hrun; cases hrun
                | some fieldResult =>
                    rw [hfields] at hrun
                    cases hrun
                    obtain ⟨ihRange, ihElim⟩ :=
                      ihList leftFields rightFields fieldResult hfields
                    refine ⟨ihRange, fun hne => ?_⟩
                    have hfieldsNe : leftFields ≠ rightFields :=
                      fun hch => hne (by rw [hname, hch])
                    obtain ⟨v, hvmem, hvelim⟩ := ihElim hfieldsNe
                    exact ⟨v, hvmem, hvelim⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun
              cases hcomponents :
                  solveTyList fuel leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  cases hrun
                  obtain ⟨ihRange, ihElim⟩ :=
                    ihList leftComponents rightComponents componentResult
                      hcomponents
                  refine ⟨ihRange, fun hne => ?_⟩
                  have hcomponentsNe : leftComponents ≠ rightComponents :=
                    fun hch => hne (by rw [hch])
                  obtain ⟨v, hvmem, hvelim⟩ := ihElim hcomponentsNe
                  exact ⟨v, hvmem, hvelim⟩
          | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
              simp only [] at hrun
              cases hdomain : solveTy fuel leftDomain rightDomain with
              | none => rw [hdomain] at hrun; cases hrun
              | some domainResult =>
                  rw [hdomain] at hrun
                  simp only [] at hrun
                  cases hcodomain : solveTy fuel
                      (leftCodomain.applyTarget domainResult.subst)
                      (rightCodomain.applyTarget domainResult.subst) with
                  | none => rw [hcodomain] at hrun; cases hrun
                  | some codomainResult =>
                      rw [hcodomain] at hrun
                      cases hrun
                      obtain ⟨domainRange, domainElim⟩ :=
                        ihTy leftDomain rightDomain domainResult hdomain
                      obtain ⟨codomainRange, codomainElim⟩ :=
                        ihTy _ _ codomainResult hcodomain
                      have hallowed : ∀ y,
                          y ∈ (leftCodomain.applyTarget
                              domainResult.subst).ftv ++
                            (rightCodomain.applyTarget
                              domainResult.subst).ftv →
                          y ∈ (Ty.fn leftDomain leftCodomain).ftv ++
                            (Ty.fn rightDomain rightCodomain).ftv := by
                        intro y hy
                        simp only [Ty.ftv, List.mem_append] at hy ⊢
                        rcases hy with hyl | hyr
                        · rcases domainRange.applyTarget_mem hyl with h | h
                          · exact Or.inl (Or.inr h)
                          · rcases List.mem_append.mp h with h | h
                            · exact Or.inl (Or.inl h)
                            · exact Or.inr (Or.inl h)
                        · rcases domainRange.applyTarget_mem hyr with h | h
                          · exact Or.inr (Or.inr h)
                          · rcases List.mem_append.mp h with h | h
                            · exact Or.inl (Or.inl h)
                            · exact Or.inr (Or.inl h)
                      have domainRange' : TyRange domainResult.subst
                          ((Ty.fn leftDomain leftCodomain).ftv ++
                            (Ty.fn rightDomain rightCodomain).ftv) := by
                        refine domainRange.mono fun y hy => ?_
                        simp only [Ty.ftv, List.mem_append] at hy ⊢
                        rcases hy with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
                      refine ⟨TyRange.comp domainRange'
                        (codomainRange.mono fun y hy => hy) hallowed,
                        fun hne => ?_⟩
                      by_cases hdomainEq : leftDomain = rightDomain
                      · subst hdomainEq
                        have hid := solveTy_eq_self hdomain
                        have hcodomainNe : leftCodomain ≠ rightCodomain :=
                          fun hch => hne (by rw [hch])
                        have hcodomainNe' :
                            leftCodomain.applyTarget domainResult.subst ≠
                              rightCodomain.applyTarget domainResult.subst :=
                          by
                            rw [hid, Ty.applyTarget_id, Ty.applyTarget_id]
                            exact hcodomainNe
                        obtain ⟨v, hvmem, hvelim⟩ :=
                          codomainElim hcodomainNe'
                        rw [hid, Ty.applyTarget_id, Ty.applyTarget_id]
                          at hvmem
                        refine ⟨v, ?_, hvelim.comp_outer⟩
                        simp only [Ty.ftv, List.mem_append] at hvmem ⊢
                        rcases hvmem with h | h
                        · exact Or.inl (Or.inr h)
                        · exact Or.inr (Or.inr h)
                      · obtain ⟨v, hvmem, hvelim⟩ := domainElim hdomainEq
                        have hvOuter : v ∉
                            (leftCodomain.applyTarget
                              domainResult.subst).ftv ++
                            (rightCodomain.applyTarget
                              domainResult.subst).ftv := by
                          intro hv
                          rcases List.mem_append.mp hv with hv | hv
                          · exact hvelim.not_mem_applyTarget _ hv
                          · exact hvelim.not_mem_applyTarget _ hv
                        refine ⟨v, ?_,
                          hvelim.comp_inner
                            (codomainRange.mono fun y hy => hy) hvOuter⟩
                        simp only [List.mem_append] at hvmem
                        simp only [Ty.ftv, List.mem_append]
                        rcases hvmem with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
          | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
              simp only [] at hrun
              by_cases hcap : leftCap = rightCap
              · rw [dif_pos hcap] at hrun
                cases htarget : solveTy fuel leftTarget rightTarget with
                | none => rw [htarget] at hrun; cases hrun
                | some targetResult =>
                    rw [htarget] at hrun
                    cases hrun
                    obtain ⟨ihRange, ihElim⟩ :=
                      ihTy leftTarget rightTarget targetResult htarget
                    refine ⟨ihRange, fun hne => ?_⟩
                    have htargetNe : leftTarget ≠ rightTarget :=
                      fun hch => hne (by rw [hcap, hch])
                    obtain ⟨v, hvmem, hvelim⟩ := ihElim htargetNe
                    exact ⟨v, hvmem, hvelim⟩
              · rw [dif_neg hcap] at hrun
                cases hrun
          | .slot leftCap leftTarget, .slot rightCap rightTarget =>
              simp only [] at hrun
              by_cases hcap : leftCap = rightCap
              · rw [dif_pos hcap] at hrun
                cases htarget : solveTy fuel leftTarget rightTarget with
                | none => rw [htarget] at hrun; cases hrun
                | some targetResult =>
                    rw [htarget] at hrun
                    cases hrun
                    obtain ⟨ihRange, ihElim⟩ :=
                      ihTy leftTarget rightTarget targetResult htarget
                    refine ⟨ihRange, fun hne => ?_⟩
                    have htargetNe : leftTarget ≠ rightTarget :=
                      fun hch => hne (by rw [hcap, hch])
                    obtain ⟨v, hvmem, hvelim⟩ := ihElim htargetNe
                    exact ⟨v, hvmem, hvelim⟩
              · rw [dif_neg hcap] at hrun
                cases hrun
          | .skolem _, .skolem _ =>
              cases hrun
          | .skolem _, .unit =>
              cases hrun
          | .skolem _, .int =>
              cases hrun
          | .skolem _, .bool =>
              cases hrun
          | .skolem _, .data _ _ =>
              cases hrun
          | .skolem _, .prod _ =>
              cases hrun
          | .skolem _, .fn _ _ =>
              cases hrun
          | .skolem _, .matcher _ _ =>
              cases hrun
          | .skolem _, .slot _ _ =>
              cases hrun
          | .unit, .skolem _ =>
              cases hrun
          | .unit, .unit =>
              cases hrun
          | .unit, .int =>
              cases hrun
          | .unit, .bool =>
              cases hrun
          | .unit, .data _ _ =>
              cases hrun
          | .unit, .prod _ =>
              cases hrun
          | .unit, .fn _ _ =>
              cases hrun
          | .unit, .matcher _ _ =>
              cases hrun
          | .unit, .slot _ _ =>
              cases hrun
          | .int, .skolem _ =>
              cases hrun
          | .int, .unit =>
              cases hrun
          | .int, .int =>
              cases hrun
          | .int, .bool =>
              cases hrun
          | .int, .data _ _ =>
              cases hrun
          | .int, .prod _ =>
              cases hrun
          | .int, .fn _ _ =>
              cases hrun
          | .int, .matcher _ _ =>
              cases hrun
          | .int, .slot _ _ =>
              cases hrun
          | .bool, .skolem _ =>
              cases hrun
          | .bool, .unit =>
              cases hrun
          | .bool, .int =>
              cases hrun
          | .bool, .bool =>
              cases hrun
          | .bool, .data _ _ =>
              cases hrun
          | .bool, .prod _ =>
              cases hrun
          | .bool, .fn _ _ =>
              cases hrun
          | .bool, .matcher _ _ =>
              cases hrun
          | .bool, .slot _ _ =>
              cases hrun
          | .data _ _, .skolem _ =>
              cases hrun
          | .data _ _, .unit =>
              cases hrun
          | .data _ _, .int =>
              cases hrun
          | .data _ _, .bool =>
              cases hrun
          | .data _ _, .prod _ =>
              cases hrun
          | .data _ _, .fn _ _ =>
              cases hrun
          | .data _ _, .matcher _ _ =>
              cases hrun
          | .data _ _, .slot _ _ =>
              cases hrun
          | .prod _, .skolem _ =>
              cases hrun
          | .prod _, .unit =>
              cases hrun
          | .prod _, .int =>
              cases hrun
          | .prod _, .bool =>
              cases hrun
          | .prod _, .data _ _ =>
              cases hrun
          | .prod _, .fn _ _ =>
              cases hrun
          | .prod _, .matcher _ _ =>
              cases hrun
          | .prod _, .slot _ _ =>
              cases hrun
          | .fn _ _, .skolem _ =>
              cases hrun
          | .fn _ _, .unit =>
              cases hrun
          | .fn _ _, .int =>
              cases hrun
          | .fn _ _, .bool =>
              cases hrun
          | .fn _ _, .data _ _ =>
              cases hrun
          | .fn _ _, .prod _ =>
              cases hrun
          | .fn _ _, .matcher _ _ =>
              cases hrun
          | .fn _ _, .slot _ _ =>
              cases hrun
          | .matcher _ _, .skolem _ =>
              cases hrun
          | .matcher _ _, .unit =>
              cases hrun
          | .matcher _ _, .int =>
              cases hrun
          | .matcher _ _, .bool =>
              cases hrun
          | .matcher _ _, .data _ _ =>
              cases hrun
          | .matcher _ _, .prod _ =>
              cases hrun
          | .matcher _ _, .fn _ _ =>
              cases hrun
          | .matcher _ _, .slot _ _ =>
              cases hrun
          | .slot _ _, .skolem _ =>
              cases hrun
          | .slot _ _, .unit =>
              cases hrun
          | .slot _ _, .int =>
              cases hrun
          | .slot _ _, .bool =>
              cases hrun
          | .slot _ _, .data _ _ =>
              cases hrun
          | .slot _ _, .prod _ =>
              cases hrun
          | .slot _ _, .fn _ _ =>
              cases hrun
          | .slot _ _, .matcher _ _ =>
              cases hrun
      · intro left right result hrun
        match left, right with
        | [], [] =>
            rw [solveTyList] at hrun
            cases hrun
            exact ⟨TyRange.id _, fun hne => absurd rfl hne⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solveTyList] at hrun
            cases hhead : solveTy fuel leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                cases htail : solveTyList fuel
                    (Ty.applyTargetList headResult.subst leftTail)
                    (Ty.applyTargetList headResult.subst rightTail) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    cases hrun
                    obtain ⟨headRange, headElim⟩ :=
                      ihTy leftHead rightHead headResult hhead
                    obtain ⟨tailRange, tailElim⟩ := ihList _ _ tailResult htail
                    have hallowed : ∀ y,
                        y ∈ Ty.ftvList (Ty.applyTargetList headResult.subst
                            leftTail) ++
                          Ty.ftvList (Ty.applyTargetList headResult.subst
                            rightTail) →
                        y ∈ Ty.ftvList (leftHead :: leftTail) ++
                          Ty.ftvList (rightHead :: rightTail) := by
                      intro y hy
                      simp only [Ty.ftvList, List.mem_append] at hy ⊢
                      rcases hy with hyl | hyr
                      · rcases headRange.applyTargetList_mem hyl with h | h
                        · exact Or.inl (Or.inr h)
                        · rcases List.mem_append.mp h with h | h
                          · exact Or.inl (Or.inl h)
                          · exact Or.inr (Or.inl h)
                      · rcases headRange.applyTargetList_mem hyr with h | h
                        · exact Or.inr (Or.inr h)
                        · rcases List.mem_append.mp h with h | h
                          · exact Or.inl (Or.inl h)
                          · exact Or.inr (Or.inl h)
                    have headRange' : TyRange headResult.subst
                        (Ty.ftvList (leftHead :: leftTail) ++
                          Ty.ftvList (rightHead :: rightTail)) := by
                      refine headRange.mono fun y hy => ?_
                      simp only [Ty.ftvList, List.mem_append] at hy ⊢
                      rcases hy with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
                    refine ⟨TyRange.comp headRange'
                      (tailRange.mono fun y hy => hy) hallowed, fun hne => ?_⟩
                    by_cases hheadEq : leftHead = rightHead
                    · subst hheadEq
                      have hid := solveTy_eq_self hhead
                      have htailNe : leftTail ≠ rightTail :=
                        fun hch => hne (by rw [hch])
                      have htailNe' :
                          Ty.applyTargetList headResult.subst leftTail ≠
                            Ty.applyTargetList headResult.subst rightTail :=
                        by
                          rw [hid, Ty.applyTargetList_id,
                            Ty.applyTargetList_id]
                          exact htailNe
                      obtain ⟨v, hvmem, hvelim⟩ := tailElim htailNe'
                      rw [hid, Ty.applyTargetList_id, Ty.applyTargetList_id]
                        at hvmem
                      refine ⟨v, ?_, hvelim.comp_outer⟩
                      simp only [Ty.ftvList, List.mem_append] at hvmem ⊢
                      rcases hvmem with h | h
                      · exact Or.inl (Or.inr h)
                      · exact Or.inr (Or.inr h)
                    · obtain ⟨v, hvmem, hvelim⟩ := headElim hheadEq
                      have hvOuter : v ∉
                          Ty.ftvList (Ty.applyTargetList headResult.subst
                            leftTail) ++
                          Ty.ftvList (Ty.applyTargetList headResult.subst
                            rightTail) := by
                        intro hv
                        rcases List.mem_append.mp hv with hv | hv
                        · exact hvelim.not_mem_applyTargetList _ hv
                        · exact hvelim.not_mem_applyTargetList _ hv
                      refine ⟨v, ?_,
                        hvelim.comp_inner (tailRange.mono fun y hy => hy)
                          hvOuter⟩
                      simp only [List.mem_append] at hvmem
                      simp only [Ty.ftvList, List.mem_append]
                      rcases hvmem with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
        | [], _ :: _ =>
            cases hrun
        | _ :: _, [] =>
            cases hrun

/-! ## Solvability completeness

Any unifiable constraint is solved by the kernel at some fuel.  The
recursion is well founded on the pair (number of remaining budget
variables, structural weight): a genuinely unequal head eliminates a budget
variable from the applied tail, and all other recursions shrink the
constraint. -/

private theorem solveCap_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {left right : Cap}
    {result : CapResult left right}
    (hrun : solveCap fuel left right = some result) :
    ∃ result' : CapResult left right,
      solveCap fuel' left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveCapPair_mono_succ (fuel + gap)).1 _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

private theorem solveCapList_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {left right : List Cap}
    {result : CapListResult left right}
    (hrun : solveCapList fuel left right = some result) :
    ∃ result' : CapListResult left right,
      solveCapList fuel' left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveCapPair_mono_succ (fuel + gap)).2 _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

private theorem solveTy_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {left right : Ty}
    {result : TyResult left right}
    (hrun : solveTy fuel left right = some result) :
    ∃ result' : TyResult left right,
      solveTy fuel' left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveTyPair_mono_succ (fuel + gap)).1 _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

private theorem solveTyList_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {left right : List Ty}
    {result : TyListResult left right}
    (hrun : solveTyList fuel left right = some result) :
    ∃ result' : TyListResult left right,
      solveTyList fuel' left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveTyPair_mono_succ (fuel + gap)).2 _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

mutual

/-- Any unifiable capability constraint whose variables live in `budget`
succeeds at some fuel. -/
private theorem solveCap_complete
    (budget : List CapVar) (left right : Cap)
    (hbudget : ∀ v, v ∈ left.fcv ++ right.fcv → v ∈ budget)
    (U : CapSubst) (hunify : left.apply U = right.apply U) :
    ∃ (fuel : Nat) (result : CapResult left right),
      solveCap fuel left right = some result := by
  by_cases hequal : left = right
  · exact ⟨1, _, by rw [solveCap, dif_pos hequal]⟩
  · match left, right with
    | .var varId, right =>
        by_cases hoccurs : varId ∈ right.fcv
        · exact absurd hunify
            (Cap.not_unifiable_of_occurs varId right (Ne.symm hequal)
              hoccurs U)
        · exact ⟨1, _, by
            rw [solveCap, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .con leftName leftChildren, .var varId =>
        by_cases hoccurs : varId ∈ (Cap.con leftName leftChildren).fcv
        · exact absurd hunify.symm
            (Cap.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveCap, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .prod leftComponents, .var varId =>
        by_cases hoccurs : varId ∈ (Cap.prod leftComponents).fcv
        · exact absurd hunify.symm
            (Cap.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveCap, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .any, .var varId =>
        by_cases hoccurs : varId ∈ Cap.any.fcv
        · exact absurd hunify.symm
            (Cap.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveCap, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .skolem name, .var varId =>
        by_cases hoccurs : varId ∈ (Cap.skolem name).fcv
        · exact absurd hunify.symm
            (Cap.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveCap, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .con leftName leftChildren, .con rightName rightChildren =>
        simp only [Cap.apply, Cap.con.injEq] at hunify
        obtain ⟨hname, hchildrenU⟩ := hunify
        obtain ⟨fuelChildren, childResult, hchildren⟩ :=
          solveCapList_complete budget leftChildren rightChildren
            (fun v hv => hbudget v hv) U hchildrenU
        exact ⟨fuelChildren + 1, _, by
          rw [solveCap, dif_neg hequal]
          simp only []
          rw [dif_pos hname, hchildren]⟩
    | .prod leftComponents, .prod rightComponents =>
        simp only [Cap.apply, Cap.prod.injEq] at hunify
        obtain ⟨fuelComponents, componentResult, hcomponents⟩ :=
          solveCapList_complete budget leftComponents rightComponents
            (fun v hv => hbudget v hv) U hunify
        exact ⟨fuelComponents + 1, _, by
          rw [solveCap, dif_neg hequal]
          simp only []
          rw [hcomponents]⟩
    | .any, .any => exact absurd rfl hequal
    | .any, .skolem _ => simp [Cap.apply] at hunify
    | .any, .con _ _ => simp [Cap.apply] at hunify
    | .any, .prod _ => simp [Cap.apply] at hunify
    | .skolem _, .any => simp [Cap.apply] at hunify
    | .skolem _, .skolem _ => simp_all [Cap.apply]
    | .skolem _, .con _ _ => simp [Cap.apply] at hunify
    | .skolem _, .prod _ => simp [Cap.apply] at hunify
    | .con _ _, .any => simp [Cap.apply] at hunify
    | .con _ _, .prod _ => simp [Cap.apply] at hunify
    | .prod _, .any => simp [Cap.apply] at hunify
    | .prod _, .skolem _ => simp [Cap.apply] at hunify
    | .prod _, .con _ _ => simp [Cap.apply] at hunify
termination_by
  (budget.length, Cap.unificationWeight left + Cap.unificationWeight right)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Cap.unificationWeight]
  all_goals omega

/-- Any unifiable capability-list constraint whose variables live in
`budget` succeeds at some fuel. -/
private theorem solveCapList_complete
    (budget : List CapVar) (left right : List Cap)
    (hbudget : ∀ v, v ∈ Cap.fcvList left ++ Cap.fcvList right → v ∈ budget)
    (U : CapSubst)
    (hunify : Cap.applyList U left = Cap.applyList U right) :
    ∃ (fuel : Nat) (result : CapListResult left right),
      solveCapList fuel left right = some result := by
  match left, right with
  | [], [] => exact ⟨1, _, by rw [solveCapList]⟩
  | [], _ :: _ => simp [Cap.applyList] at hunify
  | _ :: _, [] => simp [Cap.applyList] at hunify
  | leftHead :: leftTail, rightHead :: rightTail =>
      simp only [Cap.applyList, List.cons.injEq] at hunify
      obtain ⟨hheadU, htailU⟩ := hunify
      obtain ⟨fuelHead, headResult, hheadRun⟩ :=
        solveCap_complete budget leftHead rightHead
          (fun v hv => hbudget v (by
            simp only [Cap.fcvList, List.mem_append] at hv ⊢
            rcases hv with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h))) U hheadU
      obtain ⟨headRange, headElim⟩ :=
        (solveCapPair_varCert fuelHead).1 _ _ headResult hheadRun
      obtain ⟨R, hR⟩ := headResult.universal U hheadU
      rw [hR, Cap.applyList_comp, Cap.applyList_comp] at htailU
      by_cases hheadEq : leftHead = rightHead
      · subst hheadEq
        have hid := solveCap_eq_self hheadRun
        rw [hid, Cap.applyList_id, Cap.applyList_id] at htailU
        obtain ⟨fuelTail, tailResult, htailRun⟩ :=
          solveCapList_complete budget leftTail rightTail
            (fun v hv => hbudget v (by
              simp only [Cap.fcvList, List.mem_append] at hv ⊢
              rcases hv with h | h
              · exact Or.inl (Or.inr h)
              · exact Or.inr (Or.inr h))) R htailU
        obtain ⟨headResult', hheadRun', hheadSubst'⟩ :=
          solveCap_mono_le (Nat.le_add_right fuelHead fuelTail) hheadRun
        have happlied : ∃ resultP : CapListResult
            (Cap.applyList headResult'.subst leftTail)
            (Cap.applyList headResult'.subst rightTail),
            solveCapList (fuelHead + fuelTail)
                (Cap.applyList headResult'.subst leftTail)
                (Cap.applyList headResult'.subst rightTail) =
              some resultP := by
          rw [hheadSubst', hid, Cap.applyList_id, Cap.applyList_id]
          obtain ⟨tailResult', htailRun', _⟩ :=
            solveCapList_mono_le (Nat.le_add_left fuelTail fuelHead) htailRun
          exact ⟨tailResult', htailRun'⟩
        obtain ⟨resultP, hrunP⟩ := happlied
        exact ⟨fuelHead + fuelTail + 1, _, by
          rw [solveCapList, hheadRun']
          simp only []
          rw [hrunP]⟩
      · obtain ⟨v, hvmem, hvelim⟩ := headElim hheadEq
        have hvBudget : v ∈ budget := by
          refine hbudget v ?_
          simp only [List.mem_append] at hvmem
          simp only [Cap.fcvList, List.mem_append]
          rcases hvmem with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        obtain ⟨fuelTail, tailResult, htailRun⟩ :=
          solveCapList_complete (budget.erase v)
            (Cap.applyList headResult.subst leftTail)
            (Cap.applyList headResult.subst rightTail)
            (fun w hw => by
              have hwne : w ≠ v := by
                rintro rfl
                rcases List.mem_append.mp hw with hw | hw
                · exact hvelim.not_mem_applyList _ hw
                · exact hvelim.not_mem_applyList _ hw
              have hwBudget : w ∈ budget := by
                refine hbudget w ?_
                rcases List.mem_append.mp hw with hw | hw
                · rcases headRange.applyList_mem hw with h | h
                  · simp only [Cap.fcvList, List.mem_append]
                    exact Or.inl (Or.inr h)
                  · simp only [Cap.fcvList, List.mem_append]
                    rcases List.mem_append.mp h with h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inr (Or.inl h)
                · rcases headRange.applyList_mem hw with h | h
                  · simp only [Cap.fcvList, List.mem_append]
                    exact Or.inr (Or.inr h)
                  · simp only [Cap.fcvList, List.mem_append]
                    rcases List.mem_append.mp h with h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inr (Or.inl h)
              exact (List.mem_erase_of_ne hwne).mpr hwBudget) R htailU
        obtain ⟨headResult', hheadRun', hheadSubst'⟩ :=
          solveCap_mono_le (Nat.le_add_right fuelHead fuelTail) hheadRun
        have happlied : ∃ resultP : CapListResult
            (Cap.applyList headResult'.subst leftTail)
            (Cap.applyList headResult'.subst rightTail),
            solveCapList (fuelHead + fuelTail)
                (Cap.applyList headResult'.subst leftTail)
                (Cap.applyList headResult'.subst rightTail) =
              some resultP := by
          rw [hheadSubst']
          obtain ⟨tailResult', htailRun', _⟩ :=
            solveCapList_mono_le (Nat.le_add_left fuelTail fuelHead) htailRun
          exact ⟨tailResult', htailRun'⟩
        obtain ⟨resultP, hrunP⟩ := happlied
        exact ⟨fuelHead + fuelTail + 1, _, by
          rw [solveCapList, hheadRun']
          simp only []
          rw [hrunP]⟩
termination_by
  (budget.length,
    Cap.unificationWeightList left + Cap.unificationWeightList right)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right
    simp only [Cap.unificationWeightList]
    omega
  · apply Prod.Lex.right
    simp only [Cap.unificationWeightList]
    omega
  · apply Prod.Lex.left
    have h1 := List.length_erase_of_mem hvBudget
    have h2 := List.length_pos_of_mem hvBudget
    omega

end

mutual

/-- Any unifiable target constraint whose variables live in `budget`
succeeds at some fuel. -/
private theorem solveTy_complete
    (budget : List TypePM.TyVar) (left right : Ty)
    (hbudget : ∀ v, v ∈ left.ftv ++ right.ftv → v ∈ budget)
    (U : TySubst) (hunify : left.applyTarget U = right.applyTarget U) :
    ∃ (fuel : Nat) (result : TyResult left right),
      solveTy fuel left right = some result := by
  by_cases hequal : left = right
  · exact ⟨1, _, by rw [solveTy, dif_pos hequal]⟩
  · match left, right with
    | .var varId, right =>
        by_cases hoccurs : varId ∈ right.ftv
        · exact absurd hunify
            (Ty.not_unifiable_of_occurs varId right (Ne.symm hequal)
              hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .skolem skName, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.skolem skName).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .unit, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.unit).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .int, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.int).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .bool, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.bool).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .data dName dFields, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.data dName dFields).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .prod pComponents, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.prod pComponents).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .fn fDomain fCodomain, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.fn fDomain fCodomain).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .matcher mCap mTarget, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.matcher mCap mTarget).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .slot sCap sTarget, .var varId =>
        by_cases hoccurs : varId ∈ (Ty.slot sCap sTarget).ftv
        · exact absurd hunify.symm
            (Ty.not_unifiable_of_occurs varId _ hequal hoccurs U)
        · exact ⟨1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [dif_neg hoccurs]⟩
    | .data leftName leftFields, .data rightName rightFields =>
        simp only [Ty.applyTarget, Ty.data.injEq] at hunify
        obtain ⟨hname, hfieldsU⟩ := hunify
        obtain ⟨fuelFields, fieldResult, hfields⟩ :=
          solveTyList_complete budget leftFields rightFields
            (fun v hv => hbudget v hv) U hfieldsU
        exact ⟨fuelFields + 1, _, by
          rw [solveTy, dif_neg hequal]
          simp only []
          rw [dif_pos hname, hfields]⟩
    | .prod leftComponents, .prod rightComponents =>
        simp only [Ty.applyTarget, Ty.prod.injEq] at hunify
        obtain ⟨fuelComponents, componentResult, hcomponents⟩ :=
          solveTyList_complete budget leftComponents rightComponents
            (fun v hv => hbudget v hv) U hunify
        exact ⟨fuelComponents + 1, _, by
          rw [solveTy, dif_neg hequal]
          simp only []
          rw [hcomponents]⟩
    | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
        simp only [Ty.applyTarget, Ty.fn.injEq] at hunify
        obtain ⟨hdomainU, hcodomainU⟩ := hunify
        obtain ⟨fuelDomain, domainResult, hdomainRun⟩ :=
          solveTy_complete budget leftDomain rightDomain
            (fun v hv => hbudget v (by
              simp only [Ty.ftv, List.mem_append] at hv ⊢
              rcases hv with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h))) U hdomainU
        obtain ⟨domainRange, domainElim⟩ :=
          (solveTyPair_varCert fuelDomain).1 _ _ domainResult hdomainRun
        obtain ⟨R, hR⟩ := domainResult.universal U hdomainU
        rw [hR, Ty.applyTarget_comp, Ty.applyTarget_comp] at hcodomainU
        by_cases hdomainEq : leftDomain = rightDomain
        · subst hdomainEq
          have hid := solveTy_eq_self hdomainRun
          rw [hid, Ty.applyTarget_id, Ty.applyTarget_id] at hcodomainU
          obtain ⟨fuelCodomain, codomainResult, hcodomainRun⟩ :=
            solveTy_complete budget leftCodomain rightCodomain
              (fun v hv => hbudget v (by
                simp only [Ty.ftv, List.mem_append] at hv ⊢
                rcases hv with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr (Or.inr h))) R hcodomainU
          obtain ⟨domainResult', hdomainRun', hdomainSubst'⟩ :=
            solveTy_mono_le (Nat.le_add_right fuelDomain fuelCodomain)
              hdomainRun
          have happlied : ∃ resultP : TyResult
              (leftCodomain.applyTarget domainResult'.subst)
              (rightCodomain.applyTarget domainResult'.subst),
              solveTy (fuelDomain + fuelCodomain)
                  (leftCodomain.applyTarget domainResult'.subst)
                  (rightCodomain.applyTarget domainResult'.subst) =
                some resultP := by
            rw [hdomainSubst', hid, Ty.applyTarget_id, Ty.applyTarget_id]
            obtain ⟨codomainResult', hcodomainRun', _⟩ :=
              solveTy_mono_le (Nat.le_add_left fuelCodomain fuelDomain)
                hcodomainRun
            exact ⟨codomainResult', hcodomainRun'⟩
          obtain ⟨resultP, hrunP⟩ := happlied
          exact ⟨fuelDomain + fuelCodomain + 1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [hdomainRun']
            simp only []
            rw [hrunP]⟩
        · obtain ⟨v, hvmem, hvelim⟩ := domainElim hdomainEq
          have hvBudget : v ∈ budget := by
            refine hbudget v ?_
            simp only [List.mem_append] at hvmem
            simp only [Ty.ftv, List.mem_append]
            rcases hvmem with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
          obtain ⟨fuelCodomain, codomainResult, hcodomainRun⟩ :=
            solveTy_complete (budget.erase v)
              (leftCodomain.applyTarget domainResult.subst)
              (rightCodomain.applyTarget domainResult.subst)
              (fun w hw => by
                have hwne : w ≠ v := by
                  rintro rfl
                  rcases List.mem_append.mp hw with hw | hw
                  · exact hvelim.not_mem_applyTarget _ hw
                  · exact hvelim.not_mem_applyTarget _ hw
                have hwBudget : w ∈ budget := by
                  refine hbudget w ?_
                  rcases List.mem_append.mp hw with hw | hw
                  · rcases domainRange.applyTarget_mem hw with h | h
                    · simp only [Ty.ftv, List.mem_append]
                      exact Or.inl (Or.inr h)
                    · simp only [Ty.ftv, List.mem_append]
                      rcases List.mem_append.mp h with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
                  · rcases domainRange.applyTarget_mem hw with h | h
                    · simp only [Ty.ftv, List.mem_append]
                      exact Or.inr (Or.inr h)
                    · simp only [Ty.ftv, List.mem_append]
                      rcases List.mem_append.mp h with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
                exact (List.mem_erase_of_ne hwne).mpr hwBudget) R hcodomainU
          obtain ⟨domainResult', hdomainRun', hdomainSubst'⟩ :=
            solveTy_mono_le (Nat.le_add_right fuelDomain fuelCodomain)
              hdomainRun
          have happlied : ∃ resultP : TyResult
              (leftCodomain.applyTarget domainResult'.subst)
              (rightCodomain.applyTarget domainResult'.subst),
              solveTy (fuelDomain + fuelCodomain)
                  (leftCodomain.applyTarget domainResult'.subst)
                  (rightCodomain.applyTarget domainResult'.subst) =
                some resultP := by
            rw [hdomainSubst']
            obtain ⟨codomainResult', hcodomainRun', _⟩ :=
              solveTy_mono_le (Nat.le_add_left fuelCodomain fuelDomain)
                hcodomainRun
            exact ⟨codomainResult', hcodomainRun'⟩
          obtain ⟨resultP, hrunP⟩ := happlied
          exact ⟨fuelDomain + fuelCodomain + 1, _, by
            rw [solveTy, dif_neg hequal]
            simp only []
            rw [hdomainRun']
            simp only []
            rw [hrunP]⟩
    | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
        simp only [Ty.applyTarget, Ty.matcher.injEq] at hunify
        obtain ⟨hcap, htargetU⟩ := hunify
        obtain ⟨fuelTarget, targetResult, htargetRun⟩ :=
          solveTy_complete budget leftTarget rightTarget
            (fun v hv => hbudget v hv) U htargetU
        exact ⟨fuelTarget + 1, _, by
          rw [solveTy, dif_neg hequal]
          simp only []
          rw [dif_pos hcap, htargetRun]⟩
    | .slot leftCap leftTarget, .slot rightCap rightTarget =>
        simp only [Ty.applyTarget, Ty.slot.injEq] at hunify
        obtain ⟨hcap, htargetU⟩ := hunify
        obtain ⟨fuelTarget, targetResult, htargetRun⟩ :=
          solveTy_complete budget leftTarget rightTarget
            (fun v hv => hbudget v hv) U htargetU
        exact ⟨fuelTarget + 1, _, by
          rw [solveTy, dif_neg hequal]
          simp only []
          rw [dif_pos hcap, htargetRun]⟩
    | .skolem _, .skolem _ => simp_all [Ty.applyTarget]
    | .skolem _, .unit => simp [Ty.applyTarget] at hunify
    | .skolem _, .int => simp [Ty.applyTarget] at hunify
    | .skolem _, .bool => simp [Ty.applyTarget] at hunify
    | .skolem _, .data _ _ => simp [Ty.applyTarget] at hunify
    | .skolem _, .prod _ => simp [Ty.applyTarget] at hunify
    | .skolem _, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .skolem _, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .skolem _, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .unit, .skolem _ => simp [Ty.applyTarget] at hunify
    | .unit, .unit => exact absurd rfl hequal
    | .unit, .int => simp [Ty.applyTarget] at hunify
    | .unit, .bool => simp [Ty.applyTarget] at hunify
    | .unit, .data _ _ => simp [Ty.applyTarget] at hunify
    | .unit, .prod _ => simp [Ty.applyTarget] at hunify
    | .unit, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .unit, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .unit, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .int, .skolem _ => simp [Ty.applyTarget] at hunify
    | .int, .unit => simp [Ty.applyTarget] at hunify
    | .int, .int => exact absurd rfl hequal
    | .int, .bool => simp [Ty.applyTarget] at hunify
    | .int, .data _ _ => simp [Ty.applyTarget] at hunify
    | .int, .prod _ => simp [Ty.applyTarget] at hunify
    | .int, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .int, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .int, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .bool, .skolem _ => simp [Ty.applyTarget] at hunify
    | .bool, .unit => simp [Ty.applyTarget] at hunify
    | .bool, .int => simp [Ty.applyTarget] at hunify
    | .bool, .bool => exact absurd rfl hequal
    | .bool, .data _ _ => simp [Ty.applyTarget] at hunify
    | .bool, .prod _ => simp [Ty.applyTarget] at hunify
    | .bool, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .bool, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .bool, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .data _ _, .skolem _ => simp [Ty.applyTarget] at hunify
    | .data _ _, .unit => simp [Ty.applyTarget] at hunify
    | .data _ _, .int => simp [Ty.applyTarget] at hunify
    | .data _ _, .bool => simp [Ty.applyTarget] at hunify
    | .data _ _, .prod _ => simp [Ty.applyTarget] at hunify
    | .data _ _, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .data _ _, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .data _ _, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .prod _, .skolem _ => simp [Ty.applyTarget] at hunify
    | .prod _, .unit => simp [Ty.applyTarget] at hunify
    | .prod _, .int => simp [Ty.applyTarget] at hunify
    | .prod _, .bool => simp [Ty.applyTarget] at hunify
    | .prod _, .data _ _ => simp [Ty.applyTarget] at hunify
    | .prod _, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .prod _, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .prod _, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .fn _ _, .skolem _ => simp [Ty.applyTarget] at hunify
    | .fn _ _, .unit => simp [Ty.applyTarget] at hunify
    | .fn _ _, .int => simp [Ty.applyTarget] at hunify
    | .fn _ _, .bool => simp [Ty.applyTarget] at hunify
    | .fn _ _, .data _ _ => simp [Ty.applyTarget] at hunify
    | .fn _ _, .prod _ => simp [Ty.applyTarget] at hunify
    | .fn _ _, .matcher _ _ => simp [Ty.applyTarget] at hunify
    | .fn _ _, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .skolem _ => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .unit => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .int => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .bool => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .data _ _ => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .prod _ => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .matcher _ _, .slot _ _ => simp [Ty.applyTarget] at hunify
    | .slot _ _, .skolem _ => simp [Ty.applyTarget] at hunify
    | .slot _ _, .unit => simp [Ty.applyTarget] at hunify
    | .slot _ _, .int => simp [Ty.applyTarget] at hunify
    | .slot _ _, .bool => simp [Ty.applyTarget] at hunify
    | .slot _ _, .data _ _ => simp [Ty.applyTarget] at hunify
    | .slot _ _, .prod _ => simp [Ty.applyTarget] at hunify
    | .slot _ _, .fn _ _ => simp [Ty.applyTarget] at hunify
    | .slot _ _, .matcher _ _ => simp [Ty.applyTarget] at hunify
termination_by
  (budget.length, Ty.unificationWeight left + Ty.unificationWeight right)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right
       simp only [Ty.unificationWeight]
       omega)
    | (apply Prod.Lex.left
       have h1 := List.length_erase_of_mem hvBudget
       have h2 := List.length_pos_of_mem hvBudget
       omega)

/-- Any unifiable target-list constraint whose variables live in `budget`
succeeds at some fuel. -/
private theorem solveTyList_complete
    (budget : List TypePM.TyVar) (left right : List Ty)
    (hbudget : ∀ v, v ∈ Ty.ftvList left ++ Ty.ftvList right → v ∈ budget)
    (U : TySubst)
    (hunify : Ty.applyTargetList U left = Ty.applyTargetList U right) :
    ∃ (fuel : Nat) (result : TyListResult left right),
      solveTyList fuel left right = some result := by
  match left, right with
  | [], [] => exact ⟨1, _, by rw [solveTyList]⟩
  | [], _ :: _ => simp [Ty.applyTargetList] at hunify
  | _ :: _, [] => simp [Ty.applyTargetList] at hunify
  | leftHead :: leftTail, rightHead :: rightTail =>
      simp only [Ty.applyTargetList, List.cons.injEq] at hunify
      obtain ⟨hheadU, htailU⟩ := hunify
      obtain ⟨fuelHead, headResult, hheadRun⟩ :=
        solveTy_complete budget leftHead rightHead
          (fun v hv => hbudget v (by
            simp only [Ty.ftvList, List.mem_append] at hv ⊢
            rcases hv with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h))) U hheadU
      obtain ⟨headRange, headElim⟩ :=
        (solveTyPair_varCert fuelHead).1 _ _ headResult hheadRun
      obtain ⟨R, hR⟩ := headResult.universal U hheadU
      rw [hR, Ty.applyTargetList_comp, Ty.applyTargetList_comp] at htailU
      by_cases hheadEq : leftHead = rightHead
      · subst hheadEq
        have hid := solveTy_eq_self hheadRun
        rw [hid, Ty.applyTargetList_id, Ty.applyTargetList_id] at htailU
        obtain ⟨fuelTail, tailResult, htailRun⟩ :=
          solveTyList_complete budget leftTail rightTail
            (fun v hv => hbudget v (by
              simp only [Ty.ftvList, List.mem_append] at hv ⊢
              rcases hv with h | h
              · exact Or.inl (Or.inr h)
              · exact Or.inr (Or.inr h))) R htailU
        obtain ⟨headResult', hheadRun', hheadSubst'⟩ :=
          solveTy_mono_le (Nat.le_add_right fuelHead fuelTail) hheadRun
        have happlied : ∃ resultP : TyListResult
            (Ty.applyTargetList headResult'.subst leftTail)
            (Ty.applyTargetList headResult'.subst rightTail),
            solveTyList (fuelHead + fuelTail)
                (Ty.applyTargetList headResult'.subst leftTail)
                (Ty.applyTargetList headResult'.subst rightTail) =
              some resultP := by
          rw [hheadSubst', hid, Ty.applyTargetList_id, Ty.applyTargetList_id]
          obtain ⟨tailResult', htailRun', _⟩ :=
            solveTyList_mono_le (Nat.le_add_left fuelTail fuelHead) htailRun
          exact ⟨tailResult', htailRun'⟩
        obtain ⟨resultP, hrunP⟩ := happlied
        exact ⟨fuelHead + fuelTail + 1, _, by
          rw [solveTyList, hheadRun']
          simp only []
          rw [hrunP]⟩
      · obtain ⟨v, hvmem, hvelim⟩ := headElim hheadEq
        have hvBudget : v ∈ budget := by
          refine hbudget v ?_
          simp only [List.mem_append] at hvmem
          simp only [Ty.ftvList, List.mem_append]
          rcases hvmem with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        obtain ⟨fuelTail, tailResult, htailRun⟩ :=
          solveTyList_complete (budget.erase v)
            (Ty.applyTargetList headResult.subst leftTail)
            (Ty.applyTargetList headResult.subst rightTail)
            (fun w hw => by
              have hwne : w ≠ v := by
                rintro rfl
                rcases List.mem_append.mp hw with hw | hw
                · exact hvelim.not_mem_applyTargetList _ hw
                · exact hvelim.not_mem_applyTargetList _ hw
              have hwBudget : w ∈ budget := by
                refine hbudget w ?_
                rcases List.mem_append.mp hw with hw | hw
                · rcases headRange.applyTargetList_mem hw with h | h
                  · simp only [Ty.ftvList, List.mem_append]
                    exact Or.inl (Or.inr h)
                  · simp only [Ty.ftvList, List.mem_append]
                    rcases List.mem_append.mp h with h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inr (Or.inl h)
                · rcases headRange.applyTargetList_mem hw with h | h
                  · simp only [Ty.ftvList, List.mem_append]
                    exact Or.inr (Or.inr h)
                  · simp only [Ty.ftvList, List.mem_append]
                    rcases List.mem_append.mp h with h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inr (Or.inl h)
              exact (List.mem_erase_of_ne hwne).mpr hwBudget) R htailU
        obtain ⟨headResult', hheadRun', hheadSubst'⟩ :=
          solveTy_mono_le (Nat.le_add_right fuelHead fuelTail) hheadRun
        have happlied : ∃ resultP : TyListResult
            (Ty.applyTargetList headResult'.subst leftTail)
            (Ty.applyTargetList headResult'.subst rightTail),
            solveTyList (fuelHead + fuelTail)
                (Ty.applyTargetList headResult'.subst leftTail)
                (Ty.applyTargetList headResult'.subst rightTail) =
              some resultP := by
          rw [hheadSubst']
          obtain ⟨tailResult', htailRun', _⟩ :=
            solveTyList_mono_le (Nat.le_add_left fuelTail fuelHead) htailRun
          exact ⟨tailResult', htailRun'⟩
        obtain ⟨resultP, hrunP⟩ := happlied
        exact ⟨fuelHead + fuelTail + 1, _, by
          rw [solveTyList, hheadRun']
          simp only []
          rw [hrunP]⟩
termination_by
  (budget.length,
    Ty.unificationWeightList left + Ty.unificationWeightList right)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right
    simp only [Ty.unificationWeightList]
    omega
  · apply Prod.Lex.right
    simp only [Ty.unificationWeightList]
    omega
  · apply Prod.Lex.left
    have h1 := List.length_erase_of_mem hvBudget
    have h2 := List.length_pos_of_mem hvBudget
    omega

end

/-- Any unifiable capability constraint is solved at some fuel. -/
theorem mguCapFuel_complete
    {left right : Cap} {U : CapSubst}
    (hunify : left.apply U = right.apply U) :
    ∃ (fuel : Nat) (S : CapSubst), mguCapFuel fuel left right = some S := by
  obtain ⟨fuel, result, hrun⟩ :=
    solveCap_complete (left.fcv ++ right.fcv) left right
      (fun v hv => hv) U hunify
  exact ⟨fuel, result.subst, by simp [mguCapFuel, hrun]⟩

/-- Any unifiable capability-list constraint is solved at some fuel. -/
theorem mguCapListFuel_complete
    {left right : List Cap} {U : CapSubst}
    (hunify : Cap.applyList U left = Cap.applyList U right) :
    ∃ (fuel : Nat) (S : CapSubst),
      mguCapListFuel fuel left right = some S := by
  obtain ⟨fuel, result, hrun⟩ :=
    solveCapList_complete (Cap.fcvList left ++ Cap.fcvList right) left right
      (fun v hv => hv) U hunify
  exact ⟨fuel, result.subst, by simp [mguCapListFuel, hrun]⟩

/-- Any unifiable target constraint is solved at some fuel. -/
theorem mguTyFuel_complete
    {left right : Ty} {U : TySubst}
    (hunify : left.applyTarget U = right.applyTarget U) :
    ∃ (fuel : Nat) (S : TySubst), mguTyFuel fuel left right = some S := by
  obtain ⟨fuel, result, hrun⟩ :=
    solveTy_complete (left.ftv ++ right.ftv) left right
      (fun v hv => hv) U hunify
  exact ⟨fuel, result.subst, by simp [mguTyFuel, hrun]⟩

/-- Any unifiable target-list constraint is solved at some fuel. -/
theorem mguTyListFuel_complete
    {left right : List Ty} {U : TySubst}
    (hunify : Ty.applyTargetList U left = Ty.applyTargetList U right) :
    ∃ (fuel : Nat) (S : TySubst),
      mguTyListFuel fuel left right = some S := by
  obtain ⟨fuel, result, hrun⟩ :=
    solveTyList_complete (Ty.ftvList left ++ Ty.ftvList right) left right
      (fun v hv => hv) U hunify
  exact ⟨fuel, result.subst, by simp [mguTyListFuel, hrun]⟩

/-- A capability constraint has a unifier iff some fuel solves it. -/
theorem mguCapFuel_isSome_iff_unifiable (left right : Cap) :
    (∃ (fuel : Nat) (S : CapSubst),
        mguCapFuel fuel left right = some S) ↔
      ∃ U : CapSubst, left.apply U = right.apply U := by
  constructor
  · rintro ⟨fuel, S, hsuccess⟩
    exact ⟨S, mguCapFuel_sound hsuccess⟩
  · rintro ⟨U, hunify⟩
    exact mguCapFuel_complete hunify

/-- A target constraint has a unifier iff some fuel solves it. -/
theorem mguTyFuel_isSome_iff_unifiable (left right : Ty) :
    (∃ (fuel : Nat) (S : TySubst),
        mguTyFuel fuel left right = some S) ↔
      ∃ U : TySubst, left.applyTarget U = right.applyTarget U := by
  constructor
  · rintro ⟨fuel, S, hsuccess⟩
    exact ⟨S, mguTyFuel_sound hsuccess⟩
  · rintro ⟨U, hunify⟩
    exact mguTyFuel_complete hunify

/-! ## Executable regression checks -/

/-- Capability unification solves variables on both sides and composes them. -/
theorem mguCap_composition_regression :
    (mguCap
      (.prod [.var 0, .var 1])
      (.prod [.con "List" [.any], .var 0])).isSome = true := by
  rfl

/-- Target unification propagates the domain solution into the codomain. -/
theorem mguTy_composition_regression :
    (mguTy
      (.fn (.var 0) (.var 1))
      (.fn .int (.var 0))).isSome = true := by
  rfl

/-- Capability occurs checks reject cyclic substitutions. -/
theorem mguCap_occurs_check_regression :
    mguCap (.var 0) (.con "List" [.var 0]) = none := by
  rfl

/-- Target occurs checks reject cyclic substitutions. -/
theorem mguTy_occurs_check_regression :
    mguTy (.var 0) (.fn (.var 0) .int) = none := by
  rfl

/-- Distinct rigid capability skolems cannot be solved. -/
theorem mguCap_skolem_regression :
    mguCap (.skolem 0) (.skolem 1) = none := by
  rfl

/-- Distinct rigid target skolems cannot be solved. -/
theorem mguTy_skolem_regression :
    mguTy (.skolem 0) (.skolem 1) = none := by
  rfl

/-- Capability constructor heads are checked before their arguments. -/
theorem mguCap_constructor_regression :
    mguCap (.con "List" [.any]) (.con "Tree" [.any]) = none := by
  rfl

/-- Capability constructor arity mismatches are rejected. -/
theorem mguCap_arity_regression :
    mguCap (.con "List" [.any]) (.con "List" [.any, .any]) = none := by
  rfl

/-- Target constructor heads are checked before their arguments. -/
theorem mguTy_constructor_regression :
    mguTy (.data "List" [.int]) (.data "Tree" [.int]) = none := by
  rfl

/-- Target constructor arity mismatches are rejected. -/
theorem mguTy_arity_regression :
    mguTy (.data "List" [.int]) (.data "List" [.int, .int]) = none := by
  rfl

/-- Capability annotations are rigid inputs to the target-sort solver. -/
theorem mguTy_capability_annotation_regression :
    mguTy (.matcher (.var 0) .int) (.matcher .any .int) = none := by
  rfl

/-- `Any` is a rigid ground constructor for symmetric capability MGU. -/
example : mguCap .any .any = some CapSubst.id := by
  rfl

example : mguCap .any (.con "K" []) = none := by
  rfl

example : mguCap (.var 0) .any = some (CapSubst.single 0 .any) := by
  rfl

end Unification
end TypePM
