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

Algorithm W uses this kernel for capability and target equality, retains the
ledger snapshot at every solve cut, and freezes prevailing-image leaves at
constructor/primitive export.  This closes the capability-freeze acceptance
gap (`packProgram`).  The one-way `producerToSlot` branch still uses its
specialized matcher and legacy protected-producer bridge; the
nested-capability boundary example (`nestedCapProgram`) remains an intended
rejection under the demand-directed coercion discipline.  Both substitution
components carry finite-support certificates, and the kernels prove
factorization relative to admissible competitors.  Unrestricted most
generality and solvability completeness are not claimed; successful runs are
preserved by larger fuel.
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
  capSupportVars : List CapVar
  capSupport : subst.SupportWithin capSupportVars
  sound : left.apply subst = right.apply subst
  admissible : AdmissibleCapPost ledger subst
  /-- Every admissible competitor that solves the same constraint absorbs the
  returned substitution.  Taking the competitor itself as residual gives
  factorization without leaving the origin discipline. -/
  universal : ∀ U : CapSubst, AdmissibleCapPost ledger U →
    left.apply U = right.apply U → U = CapSubst.comp U subst

/-- Certificate of a successful oriented capability-list unification. -/
structure OrientedCapListResult
    (ledger : CapabilityOriginLedger) (left right : List Cap) where
  subst : CapSubst
  capSupportVars : List CapVar
  capSupport : subst.SupportWithin capSupportVars
  sound : Cap.applyList subst left = Cap.applyList subst right
  admissible : AdmissibleCapPost ledger subst
  universal : ∀ U : CapSubst, AdmissibleCapPost ledger U →
    Cap.applyList U left = Cap.applyList U right →
      U = CapSubst.comp U subst

/-- A single oriented capability binding has finite singleton support. -/
private theorem single_capSupport
    (varId : CapVar) (replacement : Cap) :
    (Unification.CapSubst.single varId replacement).SupportWithin [varId] := by
  intro candidate outside
  simp only [List.mem_singleton] at outside
  have reverse : varId ≠ candidate := Ne.symm outside
  simp [Unification.CapSubst.single, reverse]

/-- Capability-substitution composition preserves finite support. -/
private theorem comp_capSupport
    {later earlier : CapSubst} {earlierVars laterVars : List CapVar}
    (earlierSupport : earlier.SupportWithin earlierVars)
    (laterSupport : later.SupportWithin laterVars) :
    (CapSubst.comp later earlier).SupportWithin
      (earlierVars ++ laterVars) := by
  intro varId outside
  simp only [List.mem_append, not_or] at outside
  simp only [CapSubst.comp, earlierSupport varId outside.1, Cap.apply]
  exact laterSupport varId outside.2

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
          capSupportVars := []
          capSupport := CapSubst.id_supportWithin []
          sound := by subst right; rfl
          admissible := AdmissibleCapPost.id ledger
          universal := by
            intro U _ _
            funext candidate
            rfl
        }
      else
        match left, right with
        | .var varId, .var otherId =>
            if hflexLeft : ledger.originOf varId = .structuralFlexible then
              some {
                subst := Unification.CapSubst.single varId (.var otherId)
                capSupportVars := [varId]
                capSupport := single_capSupport varId (.var otherId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                admissible :=
                  admissible_single_structuralFlexible ledger varId _ hflexLeft
                universal := by
                  intro U _ hunify
                  funext candidate
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
              }
            else if hflexRight :
                ledger.originOf otherId = .structuralFlexible then
              some {
                subst := Unification.CapSubst.single otherId (.var varId)
                capSupportVars := [otherId]
                capSupport := single_capSupport otherId (.var varId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                admissible :=
                  admissible_single_structuralFlexible ledger otherId _
                    hflexRight
                universal := by
                  intro U _ hunify
                  funext candidate
                  by_cases hcandidate : otherId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify.symm
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
              }
            else if hrenameLeft : ledger.originOf varId = .renameOnly then
              some {
                subst := Unification.CapSubst.single varId (.var otherId)
                capSupportVars := [varId]
                capSupport := single_capSupport varId (.var otherId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                admissible :=
                  admissible_single_rename ledger varId otherId hrenameLeft
                    hflexRight
                universal := by
                  intro U _ hunify
                  funext candidate
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
              }
            else if hrenameRight : ledger.originOf otherId = .renameOnly then
              some {
                subst := Unification.CapSubst.single otherId (.var varId)
                capSupportVars := [otherId]
                capSupport := single_capSupport otherId (.var varId)
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                admissible :=
                  admissible_single_rename ledger otherId varId hrenameRight
                    hflexLeft
                universal := by
                  intro U _ hunify
                  funext candidate
                  by_cases hcandidate : otherId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify.symm
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
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
                  capSupportVars := [varId]
                  capSupport := single_capSupport varId right
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact (Unification.Cap.apply_single_of_not_mem varId right
                      right hoccurs).symm
                  admissible :=
                    admissible_single_structuralFlexible ledger varId _ hflex
                  universal := by
                    intro U _ hunify
                    funext candidate
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply] using hunify
                    · simp [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply, hcandidate]
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
                  capSupportVars := [varId]
                  capSupport := single_capSupport varId left
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact Unification.Cap.apply_single_of_not_mem varId left
                      left hoccurs
                  admissible :=
                    admissible_single_structuralFlexible ledger varId _ hflex
                  universal := by
                    intro U _ hunify
                    funext candidate
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply] using hunify.symm
                    · simp [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply, hcandidate]
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
                    capSupportVars := result.capSupportVars
                    capSupport := result.capSupport
                    sound := by
                      simp only [Cap.apply]
                      rw [hname, result.sound]
                    admissible := result.admissible
                    universal := by
                      intro U admissible hunify
                      simp only [Cap.apply, Cap.con.injEq] at hunify
                      exact result.universal U admissible hunify.2
                  }
            else
              none
        | .prod leftComponents, .prod rightComponents =>
            match solveCapList fuel ledger leftComponents rightComponents with
            | none => none
            | some result =>
                some {
                  subst := result.subst
                  capSupportVars := result.capSupportVars
                  capSupport := result.capSupport
                  sound := by
                    simp only [Cap.apply]
                    exact congrArg Cap.prod result.sound
                  admissible := result.admissible
                  universal := by
                    intro U admissible hunify
                    simp only [Cap.apply, Cap.prod.injEq] at hunify
                    exact result.universal U admissible hunify
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
        capSupportVars := []
        capSupport := CapSubst.id_supportWithin []
        sound := rfl
        admissible := AdmissibleCapPost.id ledger
        universal := by
          intro U _ _
          funext candidate
          rfl
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
                capSupportVars :=
                  headResult.capSupportVars ++ tailResult.capSupportVars
                capSupport :=
                  comp_capSupport headResult.capSupport tailResult.capSupport
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
                universal := by
                  intro U admissible hunify
                  simp only [Cap.applyList, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  have hheadFactor :=
                    headResult.universal U admissible hhead
                  have htail' :
                      Cap.applyList U
                          (Cap.applyList headResult.subst leftTail) =
                        Cap.applyList U
                          (Cap.applyList headResult.subst rightTail) := by
                    rw [← Cap.applyList_comp, ← Cap.applyList_comp,
                      ← hheadFactor]
                    exact htail
                  have htailFactor :=
                    tailResult.universal U admissible htail'
                  calc
                    U = CapSubst.comp U headResult.subst := hheadFactor
                    _ = CapSubst.comp
                        (CapSubst.comp U tailResult.subst)
                        headResult.subst :=
                      congrArg
                        (fun residual =>
                          CapSubst.comp residual headResult.subst)
                        htailFactor
                    _ = CapSubst.comp U
                        (CapSubst.comp tailResult.subst
                          headResult.subst) := by
                      funext candidate
                      simp only [CapSubst.comp, Cap.apply_comp]
              }
  | _ + 1, _, _, _ => none

end

/-! ## Fuel monotonicity of the oriented capability kernel -/

private theorem solveCapPair_mono_succ :
    ∀ fuel : Nat,
      (∀ (ledger : CapabilityOriginLedger) (left right : Cap)
          (result : OrientedCapResult ledger left right),
        solveCap fuel ledger left right = some result →
          ∃ result' : OrientedCapResult ledger left right,
            solveCap (fuel + 1) ledger left right = some result' ∧
              result'.subst = result.subst) ∧
      (∀ (ledger : CapabilityOriginLedger) (left right : List Cap)
          (result : OrientedCapListResult ledger left right),
        solveCapList fuel ledger left right = some result →
          ∃ result' : OrientedCapListResult ledger left right,
            solveCapList (fuel + 1) ledger left right = some result' ∧
              result'.subst = result.subst)
  | 0 => by
      constructor
      · intro ledger left right result hrun
        simp [solveCap] at hrun
      · intro ledger left right result hrun
        simp [solveCapList] at hrun
  | fuel + 1 => by
      obtain ⟨ihCap, ihList⟩ := solveCapPair_mono_succ fuel
      constructor
      · intro ledger left right result hrun
        rw [solveCap] at hrun ⊢
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun ⊢
          exact ⟨_, rfl, by cases hrun; rfl⟩
        · rw [dif_neg hequal] at hrun ⊢
          match left, right with
          | .var varId, .var otherId =>
              exact ⟨result, hrun, rfl⟩
          | .var varId, right =>
              cases right <;> exact ⟨result, hrun, rfl⟩
          | left, .var varId =>
              cases left <;> exact ⟨result, hrun, rfl⟩
          | .con leftName leftChildren, .con rightName rightChildren =>
              simp only [] at hrun ⊢
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun ⊢
                cases hchildren :
                    solveCapList fuel ledger leftChildren rightChildren with
                | none => rw [hchildren] at hrun; cases hrun
                | some childResult =>
                    rw [hchildren] at hrun
                    obtain ⟨childResult', hchildren', hsubst⟩ :=
                      ihList ledger leftChildren rightChildren childResult
                        hchildren
                    rw [hchildren']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun ⊢
              cases hcomponents :
                  solveCapList fuel ledger leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  obtain ⟨componentResult', hcomponents', hsubst⟩ :=
                    ihList ledger leftComponents rightComponents
                      componentResult hcomponents
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
          | .con _ _, .skolem _ => cases hrun
          | .con _ _, .prod _ => cases hrun
          | .prod _, .any => cases hrun
          | .prod _, .skolem _ => cases hrun
          | .prod _, .con _ _ => cases hrun
      · intro ledger left right result hrun
        match left, right with
        | [], [] =>
            exact ⟨result, hrun, rfl⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solveCapList] at hrun ⊢
            cases hhead : solveCap fuel ledger leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                obtain ⟨headResult', hhead', hheadSubst⟩ :=
                  ihCap ledger leftHead rightHead headResult hhead
                rw [hhead']
                simp only []
                cases htail : solveCapList fuel ledger
                    (Cap.applyList headResult.subst leftTail)
                    (Cap.applyList headResult.subst rightTail) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    obtain ⟨tailResult', htail', htailSubst⟩ :=
                      ihList ledger _ _ tailResult htail
                    have htailPrimed :
                        ∃ tailResultP : OrientedCapListResult ledger
                            (Cap.applyList headResult'.subst leftTail)
                            (Cap.applyList headResult'.subst rightTail),
                          solveCapList (fuel + 1) ledger
                              (Cap.applyList headResult'.subst leftTail)
                              (Cap.applyList headResult'.subst rightTail) =
                            some tailResultP ∧
                          tailResultP.subst = tailResult.subst := by
                      rw [hheadSubst]
                      exact ⟨tailResult', htail', htailSubst⟩
                    obtain ⟨tailResultP, htailP, htailPSubst⟩ :=
                      htailPrimed
                    rw [htailP]
                    cases hrun
                    exact ⟨_, rfl, by
                      show CapSubst.comp tailResultP.subst
                          headResult'.subst =
                        CapSubst.comp tailResult.subst headResult.subst
                      rw [htailPSubst, hheadSubst]⟩
        | [], _ :: _ => cases hrun
        | _ :: _, [] => cases hrun

private theorem solveCap_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : Cap}
    {result : OrientedCapResult ledger left right}
    (hrun : solveCap fuel ledger left right = some result) :
    ∃ result' : OrientedCapResult ledger left right,
      solveCap fuel' ledger left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveCapPair_mono_succ (fuel + gap)).1 ledger _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

private theorem solveCapList_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : List Cap}
    {result : OrientedCapListResult ledger left right}
    (hrun : solveCapList fuel ledger left right = some result) :
    ∃ result' : OrientedCapListResult ledger left right,
      solveCapList fuel' ledger left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solveCapPair_mono_succ (fuel + gap)).2 ledger _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

/-- A successful oriented capability run is preserved by any larger fuel,
with the same returned substitution. -/
theorem solveCap_success_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : Cap}
    {result : OrientedCapResult ledger left right}
    (hrun : solveCap fuel ledger left right = some result) :
    ∃ result' : OrientedCapResult ledger left right,
      solveCap fuel' ledger left right = some result' ∧
        result'.subst = result.subst :=
  solveCap_mono_le hle hrun

/-- A successful oriented capability-list run is preserved by any larger
fuel, with the same returned substitution. -/
theorem solveCapList_success_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : List Cap}
    {result : OrientedCapListResult ledger left right}
    (hrun : solveCapList fuel ledger left right = some result) :
    ∃ result' : OrientedCapListResult ledger left right,
      solveCapList fuel' ledger left right = some result' ∧
        result'.subst = result.subst :=
  solveCapList_mono_le hle hrun

/-! ## Variable accounting for oriented capability runs -/

private def CapRange (S : CapSubst) (allowed : List CapVar) : Prop :=
  ∀ x y, y ∈ (S x).fcv → y = x ∨ y ∈ allowed

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
    CapRange (Unification.CapSubst.single varId replacement) allowed := by
  intro x y hy
  by_cases hx : varId = x
  · subst hx
    simp only [Unification.CapSubst.single] at hy
    exact Or.inr (hrepl y hy)
  · simp only [Unification.CapSubst.single, if_neg hx, Cap.fcv,
      List.mem_singleton] at hy
    exact Or.inl hy

private theorem CapElim.single
    {varId : CapVar} {replacement : Cap}
    (hoccurs : varId ∉ replacement.fcv) :
    CapElim (Unification.CapSubst.single varId replacement) varId := by
  intro candidate hmem
  by_cases hcandidate : varId = candidate
  · subst hcandidate
    simp only [Unification.CapSubst.single] at hmem
    exact hoccurs hmem
  · simp only [Unification.CapSubst.single, if_neg hcandidate, Cap.fcv,
      List.mem_singleton] at hmem
    exact hcandidate hmem

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
    Unification.Cap.fcv_apply] at hy
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy
  rcases houter z y hyz with rfl | hyOuter
  · exact hinner x y hz
  · exact Or.inr (hsub y hyOuter)

private theorem CapElim.comp_outer
    {S₂ S₁ : CapSubst} {v : CapVar} (helim : CapElim S₂ v) :
    CapElim (CapSubst.comp S₂ S₁) v := by
  intro x hv
  rw [show CapSubst.comp S₂ S₁ x = (S₁ x).apply S₂ from rfl,
    Unification.Cap.fcv_apply] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem CapElim.comp_inner
    {S₂ S₁ : CapSubst} {v : CapVar} {outer : List CapVar}
    (helim : CapElim S₁ v) (hrange : CapRange S₂ outer)
    (hvOuter : v ∉ outer) :
    CapElim (CapSubst.comp S₂ S₁) v := by
  intro x hv
  rw [show CapSubst.comp S₂ S₁ x = (S₁ x).apply S₂ from rfl,
    Unification.Cap.fcv_apply] at hv
  obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.mp hv
  rcases hrange z v hvz with rfl | hvOuter'
  · exact helim x hz
  · exact hvOuter hvOuter'

private theorem CapElim.not_mem_applyList
    {S : CapSubst} {v : CapVar} (helim : CapElim S v)
    (caps : List Cap) :
    v ∉ Cap.fcvList (Cap.applyList S caps) := by
  intro hv
  rw [Unification.Cap.fcvList_applyList] at hv
  obtain ⟨z, _, hvz⟩ := List.mem_flatMap.mp hv
  exact helim z hvz

private theorem CapRange.applyList_mem
    {S : CapSubst} {allowed : List CapVar} {caps : List Cap}
    {y : CapVar}
    (hrange : CapRange S allowed)
    (hmem : y ∈ Cap.fcvList (Cap.applyList S caps)) :
    y ∈ Cap.fcvList caps ∨ y ∈ allowed := by
  rw [Unification.Cap.fcvList_applyList] at hmem
  obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hmem
  rcases hrange z y hyz with rfl | hyAllowed
  · exact Or.inl hz
  · exact Or.inr hyAllowed

private theorem solveCap_eq_self
    {fuel : Nat} {ledger : CapabilityOriginLedger} {cap : Cap}
    {result : OrientedCapResult ledger cap cap}
    (hrun : solveCap fuel ledger cap cap = some result) :
    result.subst = CapSubst.id := by
  match fuel with
  | 0 => simp [solveCap] at hrun
  | fuel + 1 =>
      rw [solveCap] at hrun
      rw [dif_pos rfl] at hrun
      cases hrun
      rfl

private theorem single_left_varCert
    (varId : CapVar) (right : Cap) (hoccurs : varId ∉ right.fcv) :
    CapRange (Unification.CapSubst.single varId right)
        ((Cap.var varId).fcv ++ right.fcv) ∧
      ∃ v, v ∈ (Cap.var varId).fcv ++ right.fcv ∧
        CapElim (Unification.CapSubst.single varId right) v := by
  refine ⟨CapRange.single (fun y hy => List.mem_append.mpr (Or.inr hy)),
    varId, ?_, CapElim.single hoccurs⟩
  exact List.mem_append.mpr
    (Or.inl (by simp only [Cap.fcv, List.mem_singleton]))

private theorem single_right_varCert
    (left : Cap) (varId : CapVar) (hoccurs : varId ∉ left.fcv) :
    CapRange (Unification.CapSubst.single varId left)
        (left.fcv ++ (Cap.var varId).fcv) ∧
      ∃ v, v ∈ left.fcv ++ (Cap.var varId).fcv ∧
        CapElim (Unification.CapSubst.single varId left) v := by
  refine ⟨CapRange.single (fun y hy => List.mem_append.mpr (Or.inl hy)),
    varId, ?_, CapElim.single hoccurs⟩
  exact List.mem_append.mpr
    (Or.inr (by simp only [Cap.fcv, List.mem_singleton]))

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
  /-- Finite support of the capability component. -/
  capSupportVars : List CapVar
  capSupport : subst.cap.SupportWithin capSupportVars
  /-- Finite support of the target component.  W retains this ledger for the
  same terminal range audits used by the symmetric target solver. -/
  targetSupportVars : List TypePM.TyVar
  targetSupport : subst.target.SupportWithin targetSupportVars
  sound : subst.apply left = subst.apply right
  admissible : AdmissiblePost ledger subst
  /-- Relative universality for the two-sorted solver.  An admissible competitor
  absorbs the returned paired substitution under cross-sort-aware sequencing. -/
  universal : ∀ U : Subst, AdmissiblePost ledger U →
    U.apply left = U.apply right → U = Subst.seq U subst

/-- Certificate of a successful paired target-list unification. -/
structure PairedListResult
    (ledger : CapabilityOriginLedger) (left right : List Ty) where
  subst : Subst
  capSupportVars : List CapVar
  capSupport : subst.cap.SupportWithin capSupportVars
  targetSupportVars : List TypePM.TyVar
  targetSupport : subst.target.SupportWithin targetSupportVars
  sound : left.map subst.apply = right.map subst.apply
  admissible : AdmissiblePost ledger subst
  universal : ∀ U : Subst, AdmissiblePost ledger U →
    left.map U.apply = right.map U.apply → U = Subst.seq U subst

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

/-- Cross-sort-aware sequencing preserves finite target support.  A variable
outside both component ledgers is fixed by the earlier target substitution,
then by the later paired substitution. -/
private theorem seq_targetSupport
    {later earlier : Subst}
    {earlierVars laterVars : List TypePM.TyVar}
    (earlierSupport : earlier.target.SupportWithin earlierVars)
    (laterSupport : later.target.SupportWithin laterVars) :
    (Subst.seq later earlier).target.SupportWithin
      (earlierVars ++ laterVars) := by
  intro varId outside
  simp only [List.mem_append, not_or] at outside
  simp only [Subst.seq, earlierSupport varId outside.1, Subst.apply,
    Ty.applyCapability, Ty.applyTarget]
  exact laterSupport varId outside.2

/-- Absorption of a capability-only phase lifts to paired substitution. -/
private theorem absorb_capOnly
    {U : Subst} {C : CapSubst}
    (capAbsorbs : U.cap = CapSubst.comp U.cap C) :
    U = Subst.seq U (Subst.mk C TySubst.id) := by
  apply PhasedPost.subst_ext
  · exact capAbsorbs
  · funext varId
    rfl

/-- Absorption composes in the same order as `Subst.seq`. -/
private theorem absorb_seq
    {U earlier later : Subst}
    (earlierAbsorbs : U = Subst.seq U earlier)
    (laterAbsorbs : U = Subst.seq U later) :
    U = Subst.seq U (Subst.seq later earlier) := by
  calc
    U = Subst.seq U earlier := earlierAbsorbs
    _ = Subst.seq (Subst.seq U later) earlier :=
      congrArg (fun residual => Subst.seq residual earlier)
        laterAbsorbs
    _ = Subst.seq U (Subst.seq later earlier) :=
      (PhasedPost.seq_assoc U later earlier).symm

/-- An absorbed substitution may be inserted before applying the competitor. -/
private theorem apply_of_absorbs
    {U solved : Subst} (absorbs : U = Subst.seq U solved) (target : Ty) :
    U.apply (solved.apply target) = U.apply target := by
  calc
    U.apply (solved.apply target) = (Subst.seq U solved).apply target :=
      (Subst.seq_apply U solved target).symm
    _ = U.apply target := congrArg (fun S => S.apply target) absorbs.symm

/-- List form of `apply_of_absorbs`. -/
private theorem map_apply_of_absorbs
    {U solved : Subst} (absorbs : U = Subst.seq U solved)
    (targets : List Ty) :
    (targets.map solved.apply).map U.apply = targets.map U.apply := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨apply_of_absorbs absorbs target, induction⟩

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
          capSupportVars := []
          capSupport := CapSubst.id_supportWithin []
          targetSupportVars := []
          targetSupport := TySubst.id_supportWithin []
          sound := by subst right; rfl
          admissible := AdmissiblePost.id ledger
          universal := by
            intro U _ _
            apply PhasedPost.subst_ext
            · funext varId
              rfl
            · funext varId
              rfl
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
                capSupportVars := []
                capSupport := CapSubst.id_supportWithin []
                targetSupportVars := [varId]
                targetSupport :=
                  Unification.TySubst.single_supportWithin varId right
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact (Unification.Ty.applyTarget_single_of_not_mem varId
                    right right hoccurs).symm
                admissible := admissiblePost_targetOnly ledger _
                universal := by
                  intro U _ hunify
                  apply PhasedPost.subst_ext
                  · funext candidate
                    rfl
                  · funext candidate
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [Subst.seq, Unification.TySubst.single,
                        Subst.apply, Ty.applyCapability, Ty.applyTarget]
                        using hunify
                    · simp [Subst.seq, Unification.TySubst.single,
                        Subst.apply, Ty.applyCapability, Ty.applyTarget,
                        hcandidate]
              }
        | left, .var varId =>
            if hoccurs : varId ∈ left.ftv then
              none
            else
              some {
                subst := Subst.mk CapSubst.id
                  (Unification.TySubst.single varId left)
                capSupportVars := []
                capSupport := CapSubst.id_supportWithin []
                targetSupportVars := [varId]
                targetSupport :=
                  Unification.TySubst.single_supportWithin varId left
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact Unification.Ty.applyTarget_single_of_not_mem varId
                    left left hoccurs
                admissible := admissiblePost_targetOnly ledger _
                universal := by
                  intro U _ hunify
                  apply PhasedPost.subst_ext
                  · funext candidate
                    rfl
                  · funext candidate
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [Subst.seq, Unification.TySubst.single,
                        Subst.apply, Ty.applyCapability, Ty.applyTarget]
                        using hunify.symm
                    · simp [Subst.seq, Unification.TySubst.single,
                        Subst.apply, Ty.applyCapability, Ty.applyTarget,
                        hcandidate]
              }
        | .data leftName leftFields, .data rightName rightFields =>
            if hname : leftName = rightName then
              match solvePairedTyList fuel ledger leftFields rightFields with
              | none => none
              | some result =>
                  some {
                    subst := result.subst
                    capSupportVars := result.capSupportVars
                    capSupport := result.capSupport
                    targetSupportVars := result.targetSupportVars
                    targetSupport := result.targetSupport
                    sound := by
                      rw [subst_apply_data, subst_apply_data, hname,
                        result.sound]
                    admissible := result.admissible
                    universal := by
                      intro U admissible hunify
                      rw [subst_apply_data, subst_apply_data] at hunify
                      simp only [Ty.data.injEq] at hunify
                      exact result.universal U admissible hunify.2
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
                  capSupportVars := result.capSupportVars
                  capSupport := result.capSupport
                  targetSupportVars := result.targetSupportVars
                  targetSupport := result.targetSupport
                  sound := by
                    rw [subst_apply_prod, subst_apply_prod, result.sound]
                  admissible := result.admissible
                  universal := by
                    intro U admissible hunify
                    rw [subst_apply_prod, subst_apply_prod] at hunify
                    simp only [Ty.prod.injEq] at hunify
                    exact result.universal U admissible hunify
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
                      capSupportVars :=
                        domainResult.capSupportVars ++
                          codomainResult.capSupportVars
                      capSupport :=
                        comp_capSupport domainResult.capSupport
                          codomainResult.capSupport
                      targetSupportVars :=
                        domainResult.targetSupportVars ++
                          codomainResult.targetSupportVars
                      targetSupport :=
                        seq_targetSupport domainResult.targetSupport
                          codomainResult.targetSupport
                      sound := by
                        rw [subst_apply_fn, subst_apply_fn, Subst.seq_apply,
                          Subst.seq_apply, Subst.seq_apply, Subst.seq_apply,
                          domainResult.sound, codomainResult.sound]
                      admissible :=
                        AdmissiblePost.seq codomainResult.admissible
                          domainResult.admissible
                      universal := by
                        intro U admissible hunify
                        rw [subst_apply_fn, subst_apply_fn] at hunify
                        simp only [Ty.fn.injEq] at hunify
                        obtain ⟨hdomain, hcodomain⟩ := hunify
                        have domainAbsorbs :=
                          domainResult.universal U admissible hdomain
                        have hcodomain' :
                            U.apply (domainResult.subst.apply leftCodomain) =
                              U.apply
                                (domainResult.subst.apply rightCodomain) := by
                          calc
                            U.apply
                                (domainResult.subst.apply leftCodomain) =
                              U.apply leftCodomain :=
                                apply_of_absorbs domainAbsorbs leftCodomain
                            _ = U.apply rightCodomain := hcodomain
                            _ = U.apply
                                (domainResult.subst.apply rightCodomain) :=
                              (apply_of_absorbs domainAbsorbs
                                rightCodomain).symm
                        have codomainAbsorbs :=
                          codomainResult.universal U admissible hcodomain'
                        exact absorb_seq domainAbsorbs codomainAbsorbs
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
                      capSupportVars :=
                        capResult.capSupportVars ++ targetResult.capSupportVars
                      capSupport :=
                        comp_capSupport capResult.capSupport
                          targetResult.capSupport
                      targetSupportVars := targetResult.targetSupportVars
                      targetSupport := by
                        simpa using seq_targetSupport
                          (later := targetResult.subst)
                          (earlier := Subst.mk capResult.subst TySubst.id)
                          (earlierVars := [])
                          (laterVars := targetResult.targetSupportVars)
                          (TySubst.id_supportWithin [])
                          targetResult.targetSupport
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
                      universal := by
                        intro U admissible hunify
                        rw [subst_apply_matcher, subst_apply_matcher] at hunify
                        simp only [Ty.matcher.injEq] at hunify
                        obtain ⟨hcap, htarget⟩ := hunify
                        have capAbsorbs := capResult.universal U.cap
                          admissible.cap hcap
                        have capPairAbsorbs := absorb_capOnly capAbsorbs
                        have htarget' :
                            U.apply
                                (leftTarget.applyCapability capResult.subst) =
                              U.apply
                                (rightTarget.applyCapability
                                  capResult.subst) := by
                          calc
                            U.apply
                                (leftTarget.applyCapability capResult.subst) =
                              U.apply
                                ((Subst.mk capResult.subst TySubst.id).apply
                                  leftTarget) :=
                              congrArg U.apply
                                (capOnly_apply capResult.subst leftTarget).symm
                            _ = U.apply leftTarget :=
                              apply_of_absorbs capPairAbsorbs leftTarget
                            _ = U.apply rightTarget := htarget
                            _ = U.apply
                                ((Subst.mk capResult.subst TySubst.id).apply
                                  rightTarget) :=
                              (apply_of_absorbs capPairAbsorbs
                                rightTarget).symm
                            _ = U.apply
                                (rightTarget.applyCapability capResult.subst) :=
                              congrArg U.apply
                                (capOnly_apply capResult.subst rightTarget)
                        have targetAbsorbs :=
                          targetResult.universal U admissible htarget'
                        exact absorb_seq capPairAbsorbs targetAbsorbs
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
                      capSupportVars :=
                        capResult.capSupportVars ++ targetResult.capSupportVars
                      capSupport :=
                        comp_capSupport capResult.capSupport
                          targetResult.capSupport
                      targetSupportVars := targetResult.targetSupportVars
                      targetSupport := by
                        simpa using seq_targetSupport
                          (later := targetResult.subst)
                          (earlier := Subst.mk capResult.subst TySubst.id)
                          (earlierVars := [])
                          (laterVars := targetResult.targetSupportVars)
                          (TySubst.id_supportWithin [])
                          targetResult.targetSupport
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
                      universal := by
                        intro U admissible hunify
                        rw [subst_apply_slot, subst_apply_slot] at hunify
                        simp only [Ty.slot.injEq] at hunify
                        obtain ⟨hcap, htarget⟩ := hunify
                        have capAbsorbs := capResult.universal U.cap
                          admissible.cap hcap
                        have capPairAbsorbs := absorb_capOnly capAbsorbs
                        have htarget' :
                            U.apply
                                (leftTarget.applyCapability capResult.subst) =
                              U.apply
                                (rightTarget.applyCapability
                                  capResult.subst) := by
                          calc
                            U.apply
                                (leftTarget.applyCapability capResult.subst) =
                              U.apply
                                ((Subst.mk capResult.subst TySubst.id).apply
                                  leftTarget) :=
                              congrArg U.apply
                                (capOnly_apply capResult.subst leftTarget).symm
                            _ = U.apply leftTarget :=
                              apply_of_absorbs capPairAbsorbs leftTarget
                            _ = U.apply rightTarget := htarget
                            _ = U.apply
                                ((Subst.mk capResult.subst TySubst.id).apply
                                  rightTarget) :=
                              (apply_of_absorbs capPairAbsorbs
                                rightTarget).symm
                            _ = U.apply
                                (rightTarget.applyCapability capResult.subst) :=
                              congrArg U.apply
                                (capOnly_apply capResult.subst rightTarget)
                        have targetAbsorbs :=
                          targetResult.universal U admissible htarget'
                        exact absorb_seq capPairAbsorbs targetAbsorbs
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
        capSupportVars := []
        capSupport := CapSubst.id_supportWithin []
        targetSupportVars := []
        targetSupport := TySubst.id_supportWithin []
        sound := rfl
        admissible := AdmissiblePost.id ledger
        universal := by
          intro U _ _
          apply PhasedPost.subst_ext
          · funext varId
            rfl
          · funext varId
            rfl
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
                capSupportVars :=
                  headResult.capSupportVars ++ tailResult.capSupportVars
                capSupport :=
                  comp_capSupport headResult.capSupport tailResult.capSupport
                targetSupportVars :=
                  headResult.targetSupportVars ++
                    tailResult.targetSupportVars
                targetSupport :=
                  seq_targetSupport headResult.targetSupport
                    tailResult.targetSupport
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
                universal := by
                  intro U admissible hunify
                  simp only [List.map, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  have headAbsorbs :=
                    headResult.universal U admissible hhead
                  have htail' :
                      (leftTail.map headResult.subst.apply).map U.apply =
                        (rightTail.map headResult.subst.apply).map U.apply := by
                    rw [map_apply_of_absorbs headAbsorbs,
                      map_apply_of_absorbs headAbsorbs]
                    exact htail
                  have tailAbsorbs :=
                    tailResult.universal U admissible htail'
                  exact absorb_seq headAbsorbs tailAbsorbs
              }
  | _ + 1, _, _, _ => none

end

/-! ## Fuel monotonicity of the paired target kernel -/

private theorem solvePairedTyPair_mono_succ :
    ∀ fuel : Nat,
      (∀ (ledger : CapabilityOriginLedger) (left right : Ty)
          (result : PairedResult ledger left right),
        solvePairedTy fuel ledger left right = some result →
          ∃ result' : PairedResult ledger left right,
            solvePairedTy (fuel + 1) ledger left right = some result' ∧
              result'.subst = result.subst) ∧
      (∀ (ledger : CapabilityOriginLedger) (left right : List Ty)
          (result : PairedListResult ledger left right),
        solvePairedTyList fuel ledger left right = some result →
          ∃ result' : PairedListResult ledger left right,
            solvePairedTyList (fuel + 1) ledger left right = some result' ∧
              result'.subst = result.subst)
  | 0 => by
      constructor
      · intro ledger left right result hrun
        simp [solvePairedTy] at hrun
      · intro ledger left right result hrun
        simp [solvePairedTyList] at hrun
  | fuel + 1 => by
      obtain ⟨ihTy, ihList⟩ := solvePairedTyPair_mono_succ fuel
      have ihCap := (solveCapPair_mono_succ fuel).1
      constructor
      · intro ledger left right result hrun
        rw [solvePairedTy] at hrun ⊢
        by_cases hequal : left = right
        · rw [dif_pos hequal] at hrun ⊢
          exact ⟨_, rfl, by cases hrun; rfl⟩
        · rw [dif_neg hequal] at hrun ⊢
          match left, right with
          | .var varId, right =>
              cases right <;> exact ⟨result, hrun, rfl⟩
          | left, .var varId =>
              cases left <;> exact ⟨result, hrun, rfl⟩
          | .data leftName leftFields, .data rightName rightFields =>
              simp only [] at hrun ⊢
              by_cases hname : leftName = rightName
              · rw [dif_pos hname] at hrun ⊢
                cases hfields : solvePairedTyList fuel ledger leftFields
                    rightFields with
                | none => rw [hfields] at hrun; cases hrun
                | some fieldResult =>
                    rw [hfields] at hrun
                    obtain ⟨fieldResult', hfields', hsubst⟩ :=
                      ihList ledger leftFields rightFields fieldResult hfields
                    rw [hfields']
                    cases hrun
                    exact ⟨_, rfl, hsubst⟩
              · rw [dif_neg hname] at hrun
                cases hrun
          | .prod leftComponents, .prod rightComponents =>
              simp only [] at hrun ⊢
              cases hcomponents : solvePairedTyList fuel ledger
                  leftComponents rightComponents with
              | none => rw [hcomponents] at hrun; cases hrun
              | some componentResult =>
                  rw [hcomponents] at hrun
                  obtain ⟨componentResult', hcomponents', hsubst⟩ :=
                    ihList ledger leftComponents rightComponents
                      componentResult hcomponents
                  rw [hcomponents']
                  cases hrun
                  exact ⟨_, rfl, hsubst⟩
          | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
              simp only [] at hrun ⊢
              cases hdomain : solvePairedTy fuel ledger leftDomain
                  rightDomain with
              | none => rw [hdomain] at hrun; cases hrun
              | some domainResult =>
                  rw [hdomain] at hrun
                  simp only [] at hrun
                  obtain ⟨domainResult', hdomain', hdomainSubst⟩ :=
                    ihTy ledger leftDomain rightDomain domainResult hdomain
                  rw [hdomain']
                  simp only []
                  cases hcodomain : solvePairedTy fuel ledger
                      (domainResult.subst.apply leftCodomain)
                      (domainResult.subst.apply rightCodomain) with
                  | none => rw [hcodomain] at hrun; cases hrun
                  | some codomainResult =>
                      rw [hcodomain] at hrun
                      obtain ⟨codomainResult', hcodomain',
                          hcodomainSubst⟩ :=
                        ihTy ledger _ _ codomainResult hcodomain
                      have hcodomainPrimed :
                          ∃ codomainResultP : PairedResult ledger
                              (domainResult'.subst.apply leftCodomain)
                              (domainResult'.subst.apply rightCodomain),
                            solvePairedTy (fuel + 1) ledger
                                (domainResult'.subst.apply leftCodomain)
                                (domainResult'.subst.apply rightCodomain) =
                              some codomainResultP ∧
                            codomainResultP.subst =
                              codomainResult.subst := by
                        rw [hdomainSubst]
                        exact ⟨codomainResult', hcodomain',
                          hcodomainSubst⟩
                      obtain ⟨codomainResultP, hcodomainP,
                          hcodomainPSubst⟩ := hcodomainPrimed
                      rw [hcodomainP]
                      cases hrun
                      exact ⟨_, rfl, by
                        show Subst.seq codomainResultP.subst
                            domainResult'.subst =
                          Subst.seq codomainResult.subst domainResult.subst
                        rw [hcodomainPSubst, hdomainSubst]⟩
          | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
              simp only [] at hrun ⊢
              cases hcap : solveCap fuel ledger leftCap rightCap with
              | none => rw [hcap] at hrun; cases hrun
              | some capResult =>
                  rw [hcap] at hrun
                  simp only [] at hrun
                  obtain ⟨capResult', hcap', hcapSubst⟩ :=
                    ihCap ledger leftCap rightCap capResult hcap
                  rw [hcap']
                  simp only []
                  cases htarget : solvePairedTy fuel ledger
                      (leftTarget.applyCapability capResult.subst)
                      (rightTarget.applyCapability capResult.subst) with
                  | none => rw [htarget] at hrun; cases hrun
                  | some targetResult =>
                      rw [htarget] at hrun
                      obtain ⟨targetResult', htarget', htargetSubst⟩ :=
                        ihTy ledger _ _ targetResult htarget
                      have htargetPrimed :
                          ∃ targetResultP : PairedResult ledger
                              (leftTarget.applyCapability capResult'.subst)
                              (rightTarget.applyCapability capResult'.subst),
                            solvePairedTy (fuel + 1) ledger
                                (leftTarget.applyCapability capResult'.subst)
                                (rightTarget.applyCapability capResult'.subst) =
                              some targetResultP ∧
                            targetResultP.subst = targetResult.subst := by
                        rw [hcapSubst]
                        exact ⟨targetResult', htarget', htargetSubst⟩
                      obtain ⟨targetResultP, htargetP, htargetPSubst⟩ :=
                        htargetPrimed
                      rw [htargetP]
                      cases hrun
                      exact ⟨_, rfl, by
                        show Subst.seq targetResultP.subst
                            (Subst.mk capResult'.subst TySubst.id) =
                          Subst.seq targetResult.subst
                            (Subst.mk capResult.subst TySubst.id)
                        rw [htargetPSubst, hcapSubst]⟩
          | .slot leftCap leftTarget, .slot rightCap rightTarget =>
              simp only [] at hrun ⊢
              cases hcap : solveCap fuel ledger leftCap rightCap with
              | none => rw [hcap] at hrun; cases hrun
              | some capResult =>
                  rw [hcap] at hrun
                  simp only [] at hrun
                  obtain ⟨capResult', hcap', hcapSubst⟩ :=
                    ihCap ledger leftCap rightCap capResult hcap
                  rw [hcap']
                  simp only []
                  cases htarget : solvePairedTy fuel ledger
                      (leftTarget.applyCapability capResult.subst)
                      (rightTarget.applyCapability capResult.subst) with
                  | none => rw [htarget] at hrun; cases hrun
                  | some targetResult =>
                      rw [htarget] at hrun
                      obtain ⟨targetResult', htarget', htargetSubst⟩ :=
                        ihTy ledger _ _ targetResult htarget
                      have htargetPrimed :
                          ∃ targetResultP : PairedResult ledger
                              (leftTarget.applyCapability capResult'.subst)
                              (rightTarget.applyCapability capResult'.subst),
                            solvePairedTy (fuel + 1) ledger
                                (leftTarget.applyCapability capResult'.subst)
                                (rightTarget.applyCapability capResult'.subst) =
                              some targetResultP ∧
                            targetResultP.subst = targetResult.subst := by
                        rw [hcapSubst]
                        exact ⟨targetResult', htarget', htargetSubst⟩
                      obtain ⟨targetResultP, htargetP, htargetPSubst⟩ :=
                        htargetPrimed
                      rw [htargetP]
                      cases hrun
                      exact ⟨_, rfl, by
                        show Subst.seq targetResultP.subst
                            (Subst.mk capResult'.subst TySubst.id) =
                          Subst.seq targetResult.subst
                            (Subst.mk capResult.subst TySubst.id)
                        rw [htargetPSubst, hcapSubst]⟩
          | .skolem _, .skolem _ => cases hrun
          | .skolem _, .unit => cases hrun
          | .skolem _, .int => cases hrun
          | .skolem _, .bool => cases hrun
          | .skolem _, .data _ _ => cases hrun
          | .skolem _, .prod _ => cases hrun
          | .skolem _, .fn _ _ => cases hrun
          | .skolem _, .matcher _ _ => cases hrun
          | .skolem _, .slot _ _ => cases hrun
          | .unit, .skolem _ => cases hrun
          | .unit, .unit => cases hrun
          | .unit, .int => cases hrun
          | .unit, .bool => cases hrun
          | .unit, .data _ _ => cases hrun
          | .unit, .prod _ => cases hrun
          | .unit, .fn _ _ => cases hrun
          | .unit, .matcher _ _ => cases hrun
          | .unit, .slot _ _ => cases hrun
          | .int, .skolem _ => cases hrun
          | .int, .unit => cases hrun
          | .int, .int => cases hrun
          | .int, .bool => cases hrun
          | .int, .data _ _ => cases hrun
          | .int, .prod _ => cases hrun
          | .int, .fn _ _ => cases hrun
          | .int, .matcher _ _ => cases hrun
          | .int, .slot _ _ => cases hrun
          | .bool, .skolem _ => cases hrun
          | .bool, .unit => cases hrun
          | .bool, .int => cases hrun
          | .bool, .bool => cases hrun
          | .bool, .data _ _ => cases hrun
          | .bool, .prod _ => cases hrun
          | .bool, .fn _ _ => cases hrun
          | .bool, .matcher _ _ => cases hrun
          | .bool, .slot _ _ => cases hrun
          | .data _ _, .skolem _ => cases hrun
          | .data _ _, .unit => cases hrun
          | .data _ _, .int => cases hrun
          | .data _ _, .bool => cases hrun
          | .data _ _, .prod _ => cases hrun
          | .data _ _, .fn _ _ => cases hrun
          | .data _ _, .matcher _ _ => cases hrun
          | .data _ _, .slot _ _ => cases hrun
          | .prod _, .skolem _ => cases hrun
          | .prod _, .unit => cases hrun
          | .prod _, .int => cases hrun
          | .prod _, .bool => cases hrun
          | .prod _, .data _ _ => cases hrun
          | .prod _, .fn _ _ => cases hrun
          | .prod _, .matcher _ _ => cases hrun
          | .prod _, .slot _ _ => cases hrun
          | .fn _ _, .skolem _ => cases hrun
          | .fn _ _, .unit => cases hrun
          | .fn _ _, .int => cases hrun
          | .fn _ _, .bool => cases hrun
          | .fn _ _, .data _ _ => cases hrun
          | .fn _ _, .prod _ => cases hrun
          | .fn _ _, .matcher _ _ => cases hrun
          | .fn _ _, .slot _ _ => cases hrun
          | .matcher _ _, .skolem _ => cases hrun
          | .matcher _ _, .unit => cases hrun
          | .matcher _ _, .int => cases hrun
          | .matcher _ _, .bool => cases hrun
          | .matcher _ _, .data _ _ => cases hrun
          | .matcher _ _, .prod _ => cases hrun
          | .matcher _ _, .fn _ _ => cases hrun
          | .matcher _ _, .slot _ _ => cases hrun
          | .slot _ _, .skolem _ => cases hrun
          | .slot _ _, .unit => cases hrun
          | .slot _ _, .int => cases hrun
          | .slot _ _, .bool => cases hrun
          | .slot _ _, .data _ _ => cases hrun
          | .slot _ _, .prod _ => cases hrun
          | .slot _ _, .fn _ _ => cases hrun
          | .slot _ _, .matcher _ _ => cases hrun
      · intro ledger left right result hrun
        match left, right with
        | [], [] =>
            exact ⟨result, hrun, rfl⟩
        | leftHead :: leftTail, rightHead :: rightTail =>
            simp only [solvePairedTyList] at hrun ⊢
            cases hhead : solvePairedTy fuel ledger leftHead rightHead with
            | none => rw [hhead] at hrun; cases hrun
            | some headResult =>
                rw [hhead] at hrun
                simp only [] at hrun
                obtain ⟨headResult', hhead', hheadSubst⟩ :=
                  ihTy ledger leftHead rightHead headResult hhead
                rw [hhead']
                simp only []
                cases htail : solvePairedTyList fuel ledger
                    (leftTail.map headResult.subst.apply)
                    (rightTail.map headResult.subst.apply) with
                | none => rw [htail] at hrun; cases hrun
                | some tailResult =>
                    rw [htail] at hrun
                    obtain ⟨tailResult', htail', htailSubst⟩ :=
                      ihList ledger _ _ tailResult htail
                    have htailPrimed :
                        ∃ tailResultP : PairedListResult ledger
                            (leftTail.map headResult'.subst.apply)
                            (rightTail.map headResult'.subst.apply),
                          solvePairedTyList (fuel + 1) ledger
                              (leftTail.map headResult'.subst.apply)
                              (rightTail.map headResult'.subst.apply) =
                            some tailResultP ∧
                          tailResultP.subst = tailResult.subst := by
                      rw [hheadSubst]
                      exact ⟨tailResult', htail', htailSubst⟩
                    obtain ⟨tailResultP, htailP, htailPSubst⟩ :=
                      htailPrimed
                    rw [htailP]
                    cases hrun
                    exact ⟨_, rfl, by
                      show Subst.seq tailResultP.subst headResult'.subst =
                        Subst.seq tailResult.subst headResult.subst
                      rw [htailPSubst, hheadSubst]⟩
        | [], _ :: _ => cases hrun
        | _ :: _, [] => cases hrun

private theorem solvePairedTy_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {result : PairedResult ledger left right}
    (hrun : solvePairedTy fuel ledger left right = some result) :
    ∃ result' : PairedResult ledger left right,
      solvePairedTy fuel' ledger left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solvePairedTyPair_mono_succ (fuel + gap)).1 ledger _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

private theorem solvePairedTyList_mono_le
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : List Ty}
    {result : PairedListResult ledger left right}
    (hrun : solvePairedTyList fuel ledger left right = some result) :
    ∃ result' : PairedListResult ledger left right,
      solvePairedTyList fuel' ledger left right = some result' ∧
        result'.subst = result.subst := by
  obtain ⟨gap, rfl⟩ : ∃ gap, fuel' = fuel + gap :=
    ⟨fuel' - fuel, (Nat.add_sub_cancel' hle).symm⟩
  clear hle
  induction gap with
  | zero => exact ⟨result, hrun, rfl⟩
  | succ gap ih =>
      obtain ⟨mid, hmid, hmidSubst⟩ := ih
      obtain ⟨fin, hfin, hfinSubst⟩ :=
        (solvePairedTyPair_mono_succ (fuel + gap)).2 ledger _ _ mid hmid
      exact ⟨fin, hfin, hfinSubst.trans hmidSubst⟩

/-- A successful paired target run is preserved by any larger fuel, with the
same returned substitution. -/
theorem solvePairedTy_success_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : Ty}
    {result : PairedResult ledger left right}
    (hrun : solvePairedTy fuel ledger left right = some result) :
    ∃ result' : PairedResult ledger left right,
      solvePairedTy fuel' ledger left right = some result' ∧
        result'.subst = result.subst :=
  solvePairedTy_mono_le hle hrun

/-- A successful paired target-list run is preserved by any larger fuel,
with the same returned substitution. -/
theorem solvePairedTyList_success_mono
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {ledger : CapabilityOriginLedger} {left right : List Ty}
    {result : PairedListResult ledger left right}
    (hrun : solvePairedTyList fuel ledger left right = some result) :
    ∃ result' : PairedListResult ledger left right,
      solvePairedTyList fuel' ledger left right = some result' ∧
        result'.subst = result.subst :=
  solvePairedTyList_mono_le hle hrun

private theorem solvePairedTy_eq_self
    {fuel : Nat} {ledger : CapabilityOriginLedger} {target : Ty}
    {result : PairedResult ledger target target}
    (hrun : solvePairedTy fuel ledger target target = some result) :
    result.subst = Subst.id := by
  match fuel with
  | 0 => simp [solvePairedTy] at hrun
  | fuel + 1 =>
      rw [solvePairedTy] at hrun
      rw [dif_pos rfl] at hrun
      cases hrun
      rfl

/-! ## Public wrappers -/

/-- Structural-fuel wrapper of the origin-oriented capability solver. -/
def mguOrientedCap
    (ledger : CapabilityOriginLedger) (left right : Cap) : Option CapSubst :=
  (solveCap (Unification.capFuel left right) ledger left right).map
    OrientedCapResult.subst

/-- Finite capability-support ledger returned by the same oriented run. -/
def mguOrientedCapSupport
    (ledger : CapabilityOriginLedger) (left right : Cap) : List CapVar :=
  match solveCap (Unification.capFuel left right) ledger left right with
  | none => []
  | some result => result.capSupportVars

/-- Any successful run within the public structural fuel bound is replayed by
the oriented capability wrapper with the same substitution. -/
theorem mguOrientedCap_of_fuel_le
    {fuel : Nat} {ledger : CapabilityOriginLedger} {left right : Cap}
    {result : OrientedCapResult ledger left right}
    (hle : fuel ≤ Unification.capFuel left right)
    (hrun : solveCap fuel ledger left right = some result) :
    mguOrientedCap ledger left right = some result.subst := by
  obtain ⟨result', hrun', hsubst⟩ := solveCap_mono_le hle hrun
  unfold mguOrientedCap
  rw [hrun']
  simp [hsubst]

/-- Reflexive oriented capability constraints succeed at the fixed public
fuel and return the identity substitution. -/
@[simp] theorem mguOrientedCap_self
    (ledger : CapabilityOriginLedger) (capability : Cap) :
    mguOrientedCap ledger capability capability = some CapSubst.id := by
  have hle : 1 ≤ Unification.capFuel capability capability := by
    simp only [Unification.capFuel]
    omega
  cases hrun : solveCap 1 ledger capability capability with
  | none => simp [solveCap] at hrun
  | some result =>
      have hsubst := solveCap_eq_self hrun
      simpa [hsubst] using mguOrientedCap_of_fuel_le hle hrun

/-- Every substitution returned by oriented capability unification is sound. -/
theorem mguOrientedCap_sound
    {ledger : CapabilityOriginLedger} {left right : Cap} {C : CapSubst}
    (hsuccess : mguOrientedCap ledger left right = some C) :
    left.apply C = right.apply C := by
  unfold mguOrientedCap at hsuccess
  cases hsolve : solveCap (Unification.capFuel left right) ledger left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = C := by
        simpa [hsolve] using hsuccess
      subst C
      exact result.sound

/-- Every oriented capability result respects its origin ledger. -/
theorem mguOrientedCap_admissible
    {ledger : CapabilityOriginLedger} {left right : Cap} {C : CapSubst}
    (hsuccess : mguOrientedCap ledger left right = some C) :
    AdmissibleCapPost ledger C := by
  unfold mguOrientedCap at hsuccess
  cases hsolve : solveCap (Unification.capFuel left right) ledger left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = C := by
        simpa [hsolve] using hsuccess
      subst C
      exact result.admissible

/-- Most-generality relative to the origin discipline: every admissible
competitor factors through the oriented result, with the competitor itself as
an admissible residual. -/
theorem mguOrientedCap_universal
    {ledger : CapabilityOriginLedger} {left right : Cap} {C U : CapSubst}
    (hsuccess : mguOrientedCap ledger left right = some C)
    (competitorAdmissible : AdmissibleCapPost ledger U)
    (competitorSound : left.apply U = right.apply U) :
    ∃ R : CapSubst,
      AdmissibleCapPost ledger R ∧ U = CapSubst.comp R C := by
  unfold mguOrientedCap at hsuccess
  cases hsolve : solveCap (Unification.capFuel left right) ledger left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = C := by
        simpa [hsolve] using hsuccess
      subst C
      exact ⟨U, competitorAdmissible,
        result.universal U competitorAdmissible competitorSound⟩

/-- The oriented capability result is identity outside its finite ledger. -/
theorem mguOrientedCap_support
    {ledger : CapabilityOriginLedger} {left right : Cap} {C : CapSubst}
    (hsuccess : mguOrientedCap ledger left right = some C) :
    C.SupportWithin (mguOrientedCapSupport ledger left right) := by
  unfold mguOrientedCap at hsuccess
  unfold mguOrientedCapSupport
  cases hsolve : solveCap (Unification.capFuel left right) ledger left right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = C := by
        simpa [hsolve] using hsuccess
      subst C
      simpa [hsolve] using result.capSupport

/-- Structural-fuel wrapper of the paired solver. -/
def mguPairedTy
    (ledger : CapabilityOriginLedger) (left right : Ty) : Option Subst :=
  (solvePairedTy (Unification.tyFuel left right) ledger left right).map
    PairedResult.subst

/-- Any successful run within the public structural fuel bound is replayed by
the paired target wrapper with the same substitution. -/
theorem mguPairedTy_of_fuel_le
    {fuel : Nat} {ledger : CapabilityOriginLedger} {left right : Ty}
    {result : PairedResult ledger left right}
    (hle : fuel ≤ Unification.tyFuel left right)
    (hrun : solvePairedTy fuel ledger left right = some result) :
    mguPairedTy ledger left right = some result.subst := by
  obtain ⟨result', hrun', hsubst⟩ := solvePairedTy_mono_le hle hrun
  unfold mguPairedTy
  rw [hrun']
  simp [hsubst]

/-- Reflexive paired target constraints succeed at the fixed public fuel and
return the identity substitution. -/
@[simp] theorem mguPairedTy_self
    (ledger : CapabilityOriginLedger) (target : Ty) :
    mguPairedTy ledger target target = some Subst.id := by
  have hle : 1 ≤ Unification.tyFuel target target := by
    simp only [Unification.tyFuel]
    omega
  cases hrun : solvePairedTy 1 ledger target target with
  | none => simp [solvePairedTy] at hrun
  | some result =>
      have hsubst := solvePairedTy_eq_self hrun
      simpa [hsubst] using mguPairedTy_of_fuel_le hle hrun

/-- Finite target-support ledger returned by the same paired-solver run. -/
def mguPairedTySupport
    (ledger : CapabilityOriginLedger) (left right : Ty) :
    List TypePM.TyVar :=
  match solvePairedTy (Unification.tyFuel left right) ledger left right with
  | none => []
  | some result => result.targetSupportVars

/-- Finite capability-support ledger returned by the same paired-solver run. -/
def mguPairedTyCapSupport
    (ledger : CapabilityOriginLedger) (left right : Ty) : List CapVar :=
  match solvePairedTy (Unification.tyFuel left right) ledger left right with
  | none => []
  | some result => result.capSupportVars

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

/-- Most-generality relative to the origin discipline: every admissible
competitor factors through the paired result under cross-sort-aware
sequencing, with the competitor itself as an admissible residual. -/
theorem mguPairedTy_universal
    {ledger : CapabilityOriginLedger} {left right : Ty} {S U : Subst}
    (hsuccess : mguPairedTy ledger left right = some S)
    (competitorAdmissible : AdmissiblePost ledger U)
    (competitorSound : U.apply left = U.apply right) :
    ∃ R : Subst,
      AdmissiblePost ledger R ∧ U = Subst.seq R S := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact ⟨U, competitorAdmissible,
        result.universal U competitorAdmissible competitorSound⟩

/-- The target component returned by paired unification is identity outside
its executable finite-support ledger. -/
theorem mguPairedTy_support
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    S.target.SupportWithin (mguPairedTySupport ledger left right) := by
  unfold mguPairedTy at hsuccess
  unfold mguPairedTySupport
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      simpa [hsolve] using result.targetSupport

/-- The capability component returned by paired unification is identity outside
its executable finite-support ledger. -/
theorem mguPairedTy_capSupport
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    S.cap.SupportWithin (mguPairedTyCapSupport ledger left right) := by
  unfold mguPairedTy at hsuccess
  unfold mguPairedTyCapSupport
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      simpa [hsolve] using result.capSupport

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
  native_decide

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
