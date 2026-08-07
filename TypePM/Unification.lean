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
