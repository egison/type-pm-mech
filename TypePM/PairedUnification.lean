import TypePM.CapabilityOrigin
import TypePM.SourceSubstitution

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
  supportInput : ∀ varId, varId ∈ capSupportVars →
    varId ∈ left.fcv ++ right.fcv
  supportElim : ∀ varId, varId ∈ capSupportVars →
    ∀ candidate, varId ∉ (subst candidate).fcv
  inputRange : ∀ candidate varId, varId ∈ (subst candidate).fcv →
    varId = candidate ∨ varId ∈ left.fcv ++ right.fcv
  sound : left.apply subst = right.apply subst
  globalUniversal : ∀ U : CapSubst, left.apply U = right.apply U →
    ∃ R : CapSubst, U = CapSubst.comp R subst
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
  supportInput : ∀ varId, varId ∈ capSupportVars →
    varId ∈ Cap.fcvList left ++ Cap.fcvList right
  supportElim : ∀ varId, varId ∈ capSupportVars →
    ∀ candidate, varId ∉ (subst candidate).fcv
  inputRange : ∀ candidate varId, varId ∈ (subst candidate).fcv →
    varId = candidate ∨ varId ∈ Cap.fcvList left ++ Cap.fcvList right
  sound : Cap.applyList subst left = Cap.applyList subst right
  globalUniversal : ∀ U : CapSubst,
    Cap.applyList U left = Cap.applyList U right →
      ∃ R : CapSubst, U = CapSubst.comp R subst
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

private theorem orientedInputRange_id (allowed : List CapVar) :
    ∀ candidate varId, varId ∈ (CapSubst.id candidate).fcv →
      varId = candidate ∨ varId ∈ allowed := by
  intro candidate varId membership
  exact Or.inl (by simpa [CapSubst.id, Cap.fcv] using membership)

private theorem orientedInputRange_single
    (bound : CapVar) (replacement : Cap) (allowed : List CapVar)
    (replacementVars : ∀ varId, varId ∈ replacement.fcv →
      varId ∈ allowed) :
    ∀ candidate varId,
      varId ∈ (Unification.CapSubst.single bound replacement candidate).fcv →
        varId = candidate ∨ varId ∈ allowed := by
  intro candidate varId membership
  by_cases same : bound = candidate
  · subst candidate
    exact Or.inr (replacementVars varId (by
      simpa [Unification.CapSubst.single] using membership))
  · exact Or.inl (by
      simpa [Unification.CapSubst.single, same, Cap.fcv] using membership)

private theorem orientedInputRange_comp
    {inner outer : CapSubst} {innerVars outerVars : List CapVar}
    (innerRange : ∀ candidate varId, varId ∈ (inner candidate).fcv →
      varId = candidate ∨ varId ∈ innerVars)
    (outerRange : ∀ candidate varId, varId ∈ (outer candidate).fcv →
      varId = candidate ∨ varId ∈ outerVars)
    (outerWithin : ∀ varId, varId ∈ outerVars →
      varId ∈ innerVars) :
    ∀ candidate varId,
      varId ∈ (CapSubst.comp outer inner candidate).fcv →
        varId = candidate ∨ varId ∈ innerVars := by
  intro candidate varId membership
  rw [show CapSubst.comp outer inner candidate =
    (inner candidate).apply outer from rfl,
    Unification.Cap.fcv_apply] at membership
  obtain ⟨middle, middleMem, imageMem⟩ := List.mem_flatMap.mp membership
  rcases outerRange middle varId imageMem with equal | outerMem
  · subst varId
    exact innerRange candidate middle middleMem
  · exact Or.inr (outerWithin varId outerMem)

private theorem orientedInputRange_applyList_mem
    {subst : CapSubst} {allowed : List CapVar} {caps : List Cap}
    (range : ∀ candidate varId, varId ∈ (subst candidate).fcv →
      varId = candidate ∨ varId ∈ allowed)
    {varId : CapVar} (membership : varId ∈
      Cap.fcvList (Cap.applyList subst caps)) :
    varId ∈ Cap.fcvList caps ∨ varId ∈ allowed := by
  rw [Unification.Cap.fcvList_applyList] at membership
  obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp membership
  rcases range source varId imageMem with rfl | inAllowed
  · exact Or.inl sourceMem
  · exact Or.inr inAllowed

private theorem orientedSupportElim_single
    (bound : CapVar) (replacement : Cap) (notOccurs : bound ∉ replacement.fcv) :
    ∀ supportVar, supportVar ∈ [bound] → ∀ candidate,
      supportVar ∉
        (Unification.CapSubst.single bound replacement candidate).fcv := by
  intro supportVar supportMem candidate membership
  have supportEq : supportVar = bound := by simpa using supportMem
  subst supportVar
  by_cases same : bound = candidate
  · subst candidate
    exact notOccurs (by
      simpa [Unification.CapSubst.single] using membership)
  · have imageEq : Unification.CapSubst.single bound replacement candidate =
        .var candidate := by
      simp [Unification.CapSubst.single, same]
    rw [imageEq] at membership
    exact same (by simpa [Cap.fcv] using membership)

private theorem orientedSupportElim_comp
    {inner outer : CapSubst}
    {innerSupport outerSupport outerVars : List CapVar}
    (innerElim : ∀ varId, varId ∈ innerSupport →
      ∀ candidate, varId ∉ (inner candidate).fcv)
    (outerElim : ∀ varId, varId ∈ outerSupport →
      ∀ candidate, varId ∉ (outer candidate).fcv)
    (outerRange : ∀ candidate varId,
      varId ∈ (outer candidate).fcv →
        varId = candidate ∨ varId ∈ outerVars)
    (innerAvoidsOuter : ∀ varId, varId ∈ innerSupport →
      varId ∉ outerVars) :
    ∀ varId, varId ∈ innerSupport ++ outerSupport →
      ∀ candidate, varId ∉ (CapSubst.comp outer inner candidate).fcv := by
  intro varId supportMem candidate membership
  rw [show CapSubst.comp outer inner candidate =
    (inner candidate).apply outer from rfl,
    Unification.Cap.fcv_apply] at membership
  obtain ⟨middle, middleMem, imageMem⟩ := List.mem_flatMap.mp membership
  rcases List.mem_append.mp supportMem with innerMem | outerMem
  · rcases outerRange middle varId imageMem with equal | inOuter
    · subst middle
      exact innerElim varId innerMem candidate middleMem
    · exact innerAvoidsOuter varId innerMem inOuter
  · exact outerElim varId outerMem middle imageMem

private theorem orientedSupportElim_not_mem_applyList
    {subst : CapSubst} {support : List CapVar}
    (elim : ∀ varId, varId ∈ support →
      ∀ candidate, varId ∉ (subst candidate).fcv)
    {varId : CapVar} (supportMem : varId ∈ support) (caps : List Cap) :
    varId ∉ Cap.fcvList (Cap.applyList subst caps) := by
  intro membership
  rw [Unification.Cap.fcvList_applyList] at membership
  obtain ⟨source, _, imageMem⟩ := List.mem_flatMap.mp membership
  exact elim varId supportMem source imageMem

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
          supportInput := by simp
          supportElim := by simp
          inputRange := orientedInputRange_id _
          sound := by subst right; rfl
          globalUniversal := fun U _ => ⟨U, funext fun _ => rfl⟩
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
                supportInput := by simp [Cap.fcv]
                supportElim := by
                  apply orientedSupportElim_single
                  simpa [Cap.fcv] using
                    (show varId ≠ otherId from fun h => hequal (by rw [h]))
                inputRange := orientedInputRange_single varId (.var otherId) _
                  fun imageVar membership => by
                    simp only [Cap.fcv, List.mem_singleton, List.mem_append]
                      at membership ⊢
                    exact Or.inr membership
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
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
                supportInput := by simp [Cap.fcv]
                supportElim := by
                  apply orientedSupportElim_single
                  simpa [Cap.fcv] using
                    (show otherId ≠ varId from
                      fun h => hequal (by rw [h]))
                inputRange := orientedInputRange_single otherId (.var varId) _
                  fun imageVar membership => by
                    simp only [Cap.fcv, List.mem_singleton, List.mem_append]
                      at membership ⊢
                    exact Or.inl membership
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : otherId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify.symm
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
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
                supportInput := by simp [Cap.fcv]
                supportElim := by
                  apply orientedSupportElim_single
                  simpa [Cap.fcv] using
                    (show varId ≠ otherId from fun h => hequal (by rw [h]))
                inputRange := orientedInputRange_single varId (.var otherId) _
                  fun imageVar membership => by
                    simp only [Cap.fcv, List.mem_singleton, List.mem_append]
                      at membership ⊢
                    exact Or.inr membership
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, hne]
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : varId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
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
                supportInput := by simp [Cap.fcv]
                supportElim := by
                  apply orientedSupportElim_single
                  simpa [Cap.fcv] using
                    (show otherId ≠ varId from
                      fun h => hequal (by rw [h]))
                inputRange := orientedInputRange_single otherId (.var varId) _
                  fun imageVar membership => by
                    simp only [Cap.fcv, List.mem_singleton, List.mem_append]
                      at membership ⊢
                    exact Or.inl membership
                sound := by
                  have hne : varId ≠ otherId := fun h => hequal (by rw [h])
                  simp [Cap.apply, Unification.CapSubst.single, Ne.symm hne]
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, funext fun candidate => ?_⟩
                  by_cases hcandidate : otherId = candidate
                  · subst candidate
                    simpa [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply] using hunify.symm
                  · simp [CapSubst.comp, Unification.CapSubst.single,
                      Cap.apply, hcandidate]
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
                  supportInput := by simp [Cap.fcv]
                  supportElim := orientedSupportElim_single varId right hoccurs
                  inputRange := orientedInputRange_single varId right _
                    fun imageVar membership =>
                      List.mem_append.mpr (Or.inr membership)
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact (Unification.Cap.apply_single_of_not_mem varId right
                      right hoccurs).symm
                  globalUniversal := by
                    intro U hunify
                    refine ⟨U, funext fun candidate => ?_⟩
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply] using hunify
                    · simp [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply, hcandidate]
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
                  supportInput := by simp [Cap.fcv]
                  supportElim := orientedSupportElim_single varId left hoccurs
                  inputRange := orientedInputRange_single varId left _
                    fun imageVar membership =>
                      List.mem_append.mpr (Or.inl membership)
                  sound := by
                    simp only [Cap.apply, Unification.CapSubst.single, if_pos]
                    exact Unification.Cap.apply_single_of_not_mem varId left
                      left hoccurs
                  globalUniversal := by
                    intro U hunify
                    refine ⟨U, funext fun candidate => ?_⟩
                    by_cases hcandidate : varId = candidate
                    · subst candidate
                      simpa [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply] using hunify.symm
                    · simp [CapSubst.comp, Unification.CapSubst.single,
                        Cap.apply, hcandidate]
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
                    supportInput := by
                      simpa [Cap.fcv] using result.supportInput
                    supportElim := result.supportElim
                    inputRange := by
                      simpa [Cap.fcv] using result.inputRange
                    sound := by
                      simp only [Cap.apply]
                      rw [hname, result.sound]
                    globalUniversal := by
                      intro U hunify
                      simp only [Cap.apply, Cap.con.injEq] at hunify
                      exact result.globalUniversal U hunify.2
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
                  supportInput := by
                    simpa [Cap.fcv] using result.supportInput
                  supportElim := result.supportElim
                  inputRange := by
                    simpa [Cap.fcv] using result.inputRange
                  sound := by
                    simp only [Cap.apply]
                    exact congrArg Cap.prod result.sound
                  globalUniversal := by
                    intro U hunify
                    simp only [Cap.apply, Cap.prod.injEq] at hunify
                    exact result.globalUniversal U hunify
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
        supportInput := by simp
        supportElim := by simp
        inputRange := orientedInputRange_id _
        sound := rfl
        globalUniversal := fun U _ => ⟨U, funext fun _ => rfl⟩
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
                supportInput := by
                  intro varId membership
                  simp only [List.mem_append] at membership
                  rcases membership with headMem | tailMem
                  · have input := headResult.supportInput varId headMem
                    simp only [Cap.fcvList, List.mem_append] at input ⊢
                    rcases input with h | h
                    · exact Or.inl (Or.inl h)
                    · exact Or.inr (Or.inl h)
                  · have input := tailResult.supportInput varId tailMem
                    simp only [List.mem_append] at input
                    rcases input with leftMem | rightMem
                    · rcases orientedInputRange_applyList_mem
                        headResult.inputRange leftMem with own | headInput
                      · simp only [Cap.fcvList, List.mem_append]
                        exact Or.inl (Or.inr own)
                      · simp only [Cap.fcvList, List.mem_append]
                        rcases List.mem_append.mp headInput with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
                    · rcases orientedInputRange_applyList_mem
                        headResult.inputRange rightMem with own | headInput
                      · simp only [Cap.fcvList, List.mem_append]
                        exact Or.inr (Or.inr own)
                      · simp only [Cap.fcvList, List.mem_append]
                        rcases List.mem_append.mp headInput with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
                supportElim := by
                  apply orientedSupportElim_comp headResult.supportElim
                    tailResult.supportElim tailResult.inputRange
                  intro varId supportMem membership
                  simp only [List.mem_append] at membership
                  rcases membership with leftMem | rightMem
                  · exact (orientedSupportElim_not_mem_applyList
                      headResult.supportElim supportMem leftTail) leftMem
                  · exact (orientedSupportElim_not_mem_applyList
                      headResult.supportElim supportMem rightTail) rightMem
                inputRange := by
                  apply orientedInputRange_comp
                    (innerVars :=
                      Cap.fcvList (leftHead :: leftTail) ++
                        Cap.fcvList (rightHead :: rightTail))
                    (outerVars :=
                      Cap.fcvList (Cap.applyList headResult.subst leftTail) ++
                      Cap.fcvList (Cap.applyList headResult.subst rightTail))
                  · intro candidate varId membership
                    rcases headResult.inputRange candidate varId membership with
                      rfl | headInput
                    · exact Or.inl rfl
                    · apply Or.inr
                      simp only [Cap.fcvList, List.mem_append]
                      rcases List.mem_append.mp headInput with h | h
                      · exact Or.inl (Or.inl h)
                      · exact Or.inr (Or.inl h)
                  · exact tailResult.inputRange
                  · intro varId membership
                    simp only [List.mem_append] at membership
                    rcases membership with leftMem | rightMem
                    · rcases orientedInputRange_applyList_mem
                        headResult.inputRange leftMem with own | headInput
                      · simp only [Cap.fcvList, List.mem_append]
                        exact Or.inl (Or.inr own)
                      · simp only [Cap.fcvList, List.mem_append]
                        rcases List.mem_append.mp headInput with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
                    · rcases orientedInputRange_applyList_mem
                        headResult.inputRange rightMem with own | headInput
                      · simp only [Cap.fcvList, List.mem_append]
                        exact Or.inr (Or.inr own)
                      · simp only [Cap.fcvList, List.mem_append]
                        rcases List.mem_append.mp headInput with h | h
                        · exact Or.inl (Or.inl h)
                        · exact Or.inr (Or.inl h)
                sound := by
                  rw [Cap.applyList_comp tailResult.subst headResult.subst,
                    Cap.applyList_comp tailResult.subst headResult.subst]
                  simp only [Cap.applyList]
                  have hhead := congrArg
                    (fun capability => capability.apply tailResult.subst)
                    headResult.sound
                  rw [hhead, tailResult.sound]
                globalUniversal := by
                  intro U hunify
                  simp only [Cap.applyList, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  obtain ⟨R₁, hR₁⟩ := headResult.globalUniversal U hhead
                  have htail' :
                      Cap.applyList R₁
                          (Cap.applyList headResult.subst leftTail) =
                        Cap.applyList R₁
                          (Cap.applyList headResult.subst rightTail) := by
                    rw [← Cap.applyList_comp, ← Cap.applyList_comp, ← hR₁]
                    exact htail
                  obtain ⟨R₂, hR₂⟩ := tailResult.globalUniversal R₁ htail'
                  refine ⟨R₂, ?_⟩
                  rw [hR₁, hR₂]
                  funext candidate
                  simp [CapSubst.comp, Cap.apply_comp]
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
  capSupportInput : ∀ varId, varId ∈ capSupportVars →
    varId ∈ left.fcv ++ right.fcv
  /-- Finite support of the target component.  W retains this ledger for the
  same terminal range audits used by the symmetric target solver. -/
  targetSupportVars : List TypePM.TyVar
  targetSupport : subst.target.SupportWithin targetSupportVars
  targetSupportInput : ∀ varId, varId ∈ targetSupportVars →
    varId ∈ left.ftv ++ right.ftv
  capRange : Unification.CapRange subst.cap (left.fcv ++ right.fcv)
  targetRange : Unification.TyRange subst.target (left.ftv ++ right.ftv)
  targetCapRange : Unification.TyCapRange subst.target
    (left.fcv ++ right.fcv)
  idempotent : subst.Idempotent
  sound : subst.apply left = subst.apply right
  /-- Every paired competitor, independently of the origin ledger, factors
  through the returned substitution. -/
  globalUniversal : ∀ U : Subst, U.apply left = U.apply right →
    ∃ R : Subst, U = Subst.seq R subst
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
  capSupportInput : ∀ varId, varId ∈ capSupportVars →
    varId ∈ Ty.fcvList left ++ Ty.fcvList right
  targetSupportVars : List TypePM.TyVar
  targetSupport : subst.target.SupportWithin targetSupportVars
  targetSupportInput : ∀ varId, varId ∈ targetSupportVars →
    varId ∈ Ty.ftvList left ++ Ty.ftvList right
  capRange : Unification.CapRange subst.cap
    (Ty.fcvList left ++ Ty.fcvList right)
  targetRange : Unification.TyRange subst.target
    (Ty.ftvList left ++ Ty.ftvList right)
  targetCapRange : Unification.TyCapRange subst.target
    (Ty.fcvList left ++ Ty.fcvList right)
  idempotent : subst.Idempotent
  sound : left.map subst.apply = right.map subst.apply
  globalUniversal : ∀ U : Subst,
    left.map U.apply = right.map U.apply →
      ∃ R : Subst, U = Subst.seq R subst
  admissible : AdmissiblePost ledger subst
  universal : ∀ U : Subst, AdmissiblePost ledger U →
    left.map U.apply = right.map U.apply → U = Subst.seq U subst

/-! ## Paired variable-range accounting -/

private theorem pairedCapRange_id (allowed : List CapVar) :
    Unification.CapRange CapSubst.id allowed := by
  intro x y membership
  exact Or.inl (by simpa [CapSubst.id, Cap.fcv] using membership)

private theorem pairedCapRange_mono
    {S : CapSubst} {smaller larger : List CapVar}
    (range : Unification.CapRange S smaller)
    (included : ∀ varId, varId ∈ smaller → varId ∈ larger) :
    Unification.CapRange S larger := by
  intro source image membership
  rcases range source image membership with rfl | inputMem
  · exact Or.inl rfl
  · exact Or.inr (included image inputMem)

private theorem pairedCapRange_comp
    {later earlier : CapSubst} {outer inner : List CapVar}
    (earlierRange : Unification.CapRange earlier inner)
    (laterRange : Unification.CapRange later outer)
    (outerWithin : ∀ varId, varId ∈ outer → varId ∈ inner) :
    Unification.CapRange (CapSubst.comp later earlier) inner := by
  intro source image membership
  rw [show CapSubst.comp later earlier source =
      (earlier source).apply later from rfl,
    Unification.Cap.fcv_apply] at membership
  obtain ⟨middle, middleMem, imageMem⟩ := List.mem_flatMap.mp membership
  rcases laterRange middle image imageMem with rfl | outerMem
  · exact earlierRange source image middleMem
  · exact Or.inr (outerWithin image outerMem)

private theorem pairedTyRange_id (allowed : List TypePM.TyVar) :
    Unification.TyRange TySubst.id allowed := by
  intro x y membership
  exact Or.inl (by simpa [TySubst.id, Ty.ftv] using membership)

private theorem pairedTyRange_single
    (bound : TypePM.TyVar) (replacement : Ty)
    (allowed : List TypePM.TyVar)
    (replacementWithin : ∀ varId, varId ∈ replacement.ftv →
      varId ∈ allowed) :
    Unification.TyRange (Unification.TySubst.single bound replacement)
      allowed := by
  intro source image membership
  by_cases same : bound = source
  · subst source
    exact Or.inr (replacementWithin image (by
      simpa [Unification.TySubst.single] using membership))
  · exact Or.inl (by
      simpa [Unification.TySubst.single, same, Ty.ftv] using membership)

private theorem pairedTyRange_mono
    {S : TySubst} {smaller larger : List TypePM.TyVar}
    (range : Unification.TyRange S smaller)
    (included : ∀ varId, varId ∈ smaller → varId ∈ larger) :
    Unification.TyRange S larger := by
  intro source image membership
  rcases range source image membership with rfl | inputMem
  · exact Or.inl rfl
  · exact Or.inr (included image inputMem)

private theorem pairedTyCapRange_id (allowed : List CapVar) :
    Unification.TyCapRange TySubst.id allowed := by
  intro source image membership
  simp [TySubst.id, Ty.fcv] at membership

private theorem pairedTyCapRange_single
    (bound : TypePM.TyVar) (replacement : Ty) (allowed : List CapVar)
    (replacementWithin : ∀ varId, varId ∈ replacement.fcv →
      varId ∈ allowed) :
    Unification.TyCapRange
      (Unification.TySubst.single bound replacement) allowed := by
  intro source image membership
  by_cases same : bound = source
  · subst source
    exact replacementWithin image (by
      simpa [Unification.TySubst.single] using membership)
  · simp [Unification.TySubst.single, same, Ty.fcv] at membership

private theorem pairedTyCapRange_mono
    {S : TySubst} {smaller larger : List CapVar}
    (range : Unification.TyCapRange S smaller)
    (included : ∀ varId, varId ∈ smaller → varId ∈ larger) :
    Unification.TyCapRange S larger := by
  intro source image membership
  exact included image (range source image membership)

/-- Target variables in a paired-substituted type come either from its target
skeleton or from the target range of the substitution. -/
private theorem pairedTyRange_apply_mem
    {S : Subst} {allowed : List TypePM.TyVar}
    (range : Unification.TyRange S.target allowed)
    {target : Ty} {varId : TypePM.TyVar}
    (membership : varId ∈ (S.apply target).ftv) :
    varId ∈ target.ftv ∨ varId ∈ allowed := by
  rw [Subst.apply, Unification.Ty.ftv_applyTarget,
    Unification.Ty.ftv_applyCapability] at membership
  obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp membership
  rcases range source varId imageMem with rfl | allowedMem
  · exact Or.inl sourceMem
  · exact Or.inr allowedMem

private theorem pairedTyRange_map_apply_mem
    {S : Subst} {allowed : List TypePM.TyVar}
    (range : Unification.TyRange S.target allowed)
    {targets : List Ty} {varId : TypePM.TyVar}
    (membership : varId ∈ Ty.ftvList (targets.map S.apply)) :
    varId ∈ Ty.ftvList targets ∨ varId ∈ allowed := by
  induction targets with
  | nil => simp [Ty.ftvList] at membership
  | cons target targets induction =>
      simp only [List.map_cons, Ty.ftvList, List.mem_append] at membership ⊢
      rcases membership with headMem | tailMem
      · rcases pairedTyRange_apply_mem range headMem with own | allowedMem
        · exact Or.inl (Or.inl own)
        · exact Or.inr allowedMem
      · rcases induction tailMem with own | allowedMem
        · exact Or.inl (Or.inr own)
        · exact Or.inr allowedMem

/-- Capability variables in a paired-substituted type come either from its
capability skeleton or from one of the two capability ranges. -/
private theorem pairedCapRange_apply_mem
    {S : Subst} {allowed : List CapVar}
    (capRange : Unification.CapRange S.cap allowed)
    (targetCapRange : Unification.TyCapRange S.target allowed)
    {target : Ty} {varId : CapVar}
    (membership : varId ∈ (S.apply target).fcv) :
    varId ∈ target.fcv ∨ varId ∈ allowed := by
  rcases Unification.Ty.mem_fcv_applyTarget _ _ _ membership with own | image
  · rw [Unification.Ty.fcv_applyCapability] at own
    obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp own
    rcases capRange source varId imageMem with rfl | allowedMem
    · exact Or.inl sourceMem
    · exact Or.inr allowedMem
  · obtain ⟨source, sourceMem, imageMem⟩ := image
    rw [Unification.Ty.ftv_applyCapability] at sourceMem
    exact Or.inr (targetCapRange source varId imageMem)

private theorem pairedCapRange_map_apply_mem
    {S : Subst} {allowed : List CapVar}
    (capRange : Unification.CapRange S.cap allowed)
    (targetCapRange : Unification.TyCapRange S.target allowed)
    {targets : List Ty} {varId : CapVar}
    (membership : varId ∈ Ty.fcvList (targets.map S.apply)) :
    varId ∈ Ty.fcvList targets ∨ varId ∈ allowed := by
  induction targets with
  | nil => simp [Ty.fcvList] at membership
  | cons target targets induction =>
      simp only [List.map_cons, Ty.fcvList, List.mem_append] at membership ⊢
      rcases membership with headMem | tailMem
      · rcases pairedCapRange_apply_mem capRange targetCapRange headMem with
          own | allowedMem
        · exact Or.inl (Or.inl own)
        · exact Or.inr allowedMem
      · rcases induction tailMem with own | allowedMem
        · exact Or.inl (Or.inr own)
        · exact Or.inr allowedMem

private theorem pairedTyRange_seq
    {later earlier : Subst}
    {outer inner : List TypePM.TyVar}
    (earlierRange : Unification.TyRange earlier.target inner)
    (laterRange : Unification.TyRange later.target outer)
    (outerWithin : ∀ varId, varId ∈ outer → varId ∈ inner) :
    Unification.TyRange (Subst.seq later earlier).target inner := by
  intro source image membership
  rcases pairedTyRange_apply_mem laterRange membership with own | outerMem
  · exact earlierRange source image own
  · exact Or.inr (outerWithin image outerMem)

private theorem pairedTyCapRange_seq
    {later earlier : Subst} {outer inner : List CapVar}
    (earlierRange : Unification.TyCapRange earlier.target inner)
    (laterCapRange : Unification.CapRange later.cap outer)
    (laterTargetRange : Unification.TyCapRange later.target outer)
    (outerWithin : ∀ varId, varId ∈ outer → varId ∈ inner) :
    Unification.TyCapRange (Subst.seq later earlier).target inner := by
  intro source image membership
  rcases pairedCapRange_apply_mem laterCapRange laterTargetRange membership with
    own | outerMem
  · exact earlierRange source image own
  · exact outerWithin image outerMem

private theorem seq_supportInput
    {earlierVars laterVars inner outer : List α}
    (earlierInput : ∀ varId, varId ∈ earlierVars → varId ∈ inner)
    (laterInput : ∀ varId, varId ∈ laterVars → varId ∈ outer)
    (outerWithin : ∀ varId, varId ∈ outer → varId ∈ inner) :
    ∀ varId, varId ∈ earlierVars ++ laterVars → varId ∈ inner := by
  intro varId membership
  rcases List.mem_append.mp membership with earlierMem | laterMem
  · exact earlierInput varId earlierMem
  · exact outerWithin varId (laterInput varId laterMem)

/-- The support-elimination certificate of the oriented capability kernel is
its pointwise solved-form certificate. -/
private theorem orientedCapResult_idempotent
    {ledger : CapabilityOriginLedger} {left right : Cap}
    (result : OrientedCapResult ledger left right) :
    result.subst.Idempotent := by
  apply CapSubst.idempotent_of_pointwise
  intro source
  apply Cap.apply_eq_self_of_fcv_fixed
  intro image imageMem
  exact result.capSupport image fun supportMem =>
    result.supportElim image supportMem source imageMem

private theorem orientedCapPhase_idempotent
    {ledger : CapabilityOriginLedger} {left right : Cap}
    (result : OrientedCapResult ledger left right) :
    (Subst.mk result.subst TySubst.id).Idempotent :=
  Subst.idempotent_of_targetId (orientedCapResult_idempotent result)

private theorem orientedCapPhase_zonkedCapsFixed
    {ledger : CapabilityOriginLedger} {left right : Cap}
    (result : OrientedCapResult ledger left right)
    (leftTarget rightTarget : Ty) :
    ∀ varId,
      varId ∈ (leftTarget.applyCapability result.subst).fcv ++
        (rightTarget.applyCapability result.subst).fcv →
      result.subst varId = .var varId := by
  intro varId membership
  have phaseIdem := orientedCapPhase_idempotent result
  rcases List.mem_append.mp membership with leftMem | rightMem
  · apply phaseIdem.image_cap_fixed leftTarget varId
    simpa only [capOnly_apply] using leftMem
  · apply phaseIdem.image_cap_fixed rightTarget varId
    simpa only [capOnly_apply] using rightMem

private theorem idempotent_target_fixed_map
    {S : Subst} (idem : S.Idempotent) :
    ∀ (targets : List Ty) varId,
      varId ∈ Ty.ftvList (targets.map S.apply) →
      S.target varId = .var varId
  | [], _, membership => nomatch membership
  | target :: targets, varId, membership => by
      simp only [List.map_cons, Ty.ftvList, List.mem_append] at membership
      rcases membership with headMem | tailMem
      · exact idem.image_target_fixed target varId headMem
      · exact idempotent_target_fixed_map idem targets varId tailMem

private theorem idempotent_cap_fixed_map
    {S : Subst} (idem : S.Idempotent) :
    ∀ (targets : List Ty) varId,
      varId ∈ Ty.fcvList (targets.map S.apply) →
      S.cap varId = .var varId
  | [], _, membership => nomatch membership
  | target :: targets, varId, membership => by
      simp only [List.map_cons, Ty.fcvList, List.mem_append] at membership
      rcases membership with headMem | tailMem
      · exact idem.image_cap_fixed target varId headMem
      · exact idempotent_cap_fixed_map idem targets varId tailMem

/-- Sequential solver phases stay solved when the earlier solved phase fixes
the finite input ranges of the later phase. -/
private theorem pairedSeq_idempotent
    {earlier later : Subst}
    {outerCaps : List CapVar} {outerTargets : List TypePM.TyVar}
    (earlierIdem : earlier.Idempotent) (laterIdem : later.Idempotent)
    (laterCapRange : Unification.CapRange later.cap outerCaps)
    (laterTargetRange : Unification.TyRange later.target outerTargets)
    (laterTargetCapRange :
      Unification.TyCapRange later.target outerCaps)
    (outerTargetsFixed : ∀ varId, varId ∈ outerTargets →
      earlier.target varId = .var varId)
    (outerCapsFixed : ∀ varId, varId ∈ outerCaps →
      earlier.cap varId = .var varId) :
    (Subst.seq later earlier).Idempotent := by
  apply Subst.seq_idempotent laterIdem
  intro target
  apply Subst.apply_eq_self_of_fixed
  · intro varId membership
    rcases pairedTyRange_apply_mem laterTargetRange membership with
      imageMem | outerMem
    · exact earlierIdem.image_target_fixed target varId imageMem
    · exact outerTargetsFixed varId outerMem
  · intro varId membership
    rcases pairedCapRange_apply_mem laterCapRange laterTargetCapRange
        membership with imageMem | outerMem
    · exact earlierIdem.image_cap_fixed target varId imageMem
    · exact outerCapsFixed varId outerMem

private theorem fn_domainCapWithin
    {leftDomain leftCodomain rightDomain rightCodomain : Ty} :
    ∀ varId, varId ∈ leftDomain.fcv ++ rightDomain.fcv →
      varId ∈ (Ty.fn leftDomain leftCodomain).fcv ++
        (Ty.fn rightDomain rightCodomain).fcv := by
  intro varId membership
  simp only [Ty.fcv, List.mem_append] at membership ⊢
  rcases membership with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

private theorem fn_domainTargetWithin
    {leftDomain leftCodomain rightDomain rightCodomain : Ty} :
    ∀ varId, varId ∈ leftDomain.ftv ++ rightDomain.ftv →
      varId ∈ (Ty.fn leftDomain leftCodomain).ftv ++
        (Ty.fn rightDomain rightCodomain).ftv := by
  intro varId membership
  simp only [Ty.ftv, List.mem_append] at membership ⊢
  rcases membership with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

private theorem fn_codomainCapWithin
    {ledger : CapabilityOriginLedger}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    (domainResult : PairedResult ledger leftDomain rightDomain) :
    ∀ varId,
      varId ∈ (domainResult.subst.apply leftCodomain).fcv ++
        (domainResult.subst.apply rightCodomain).fcv →
      varId ∈ (Ty.fn leftDomain leftCodomain).fcv ++
        (Ty.fn rightDomain rightCodomain).fcv := by
  intro varId membership
  rcases List.mem_append.mp membership with leftMem | rightMem
  · rcases pairedCapRange_apply_mem domainResult.capRange
      domainResult.targetCapRange leftMem with own | domainInput
    · simp only [Ty.fcv, List.mem_append]
      exact Or.inl (Or.inr own)
    · exact fn_domainCapWithin varId domainInput
  · rcases pairedCapRange_apply_mem domainResult.capRange
      domainResult.targetCapRange rightMem with own | domainInput
    · simp only [Ty.fcv, List.mem_append]
      exact Or.inr (Or.inr own)
    · exact fn_domainCapWithin varId domainInput

private theorem fn_codomainTargetWithin
    {ledger : CapabilityOriginLedger}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    (domainResult : PairedResult ledger leftDomain rightDomain) :
    ∀ varId,
      varId ∈ (domainResult.subst.apply leftCodomain).ftv ++
        (domainResult.subst.apply rightCodomain).ftv →
      varId ∈ (Ty.fn leftDomain leftCodomain).ftv ++
        (Ty.fn rightDomain rightCodomain).ftv := by
  intro varId membership
  rcases List.mem_append.mp membership with leftMem | rightMem
  · rcases pairedTyRange_apply_mem domainResult.targetRange leftMem with
      own | domainInput
    · simp only [Ty.ftv, List.mem_append]
      exact Or.inl (Or.inr own)
    · exact fn_domainTargetWithin varId domainInput
  · rcases pairedTyRange_apply_mem domainResult.targetRange rightMem with
      own | domainInput
    · simp only [Ty.ftv, List.mem_append]
      exact Or.inr (Or.inr own)
    · exact fn_domainTargetWithin varId domainInput

private theorem annotated_capWithin
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty} :
    ∀ varId, varId ∈ leftCap.fcv ++ rightCap.fcv →
      varId ∈ (leftCap.fcv ++ leftTarget.fcv) ++
        (rightCap.fcv ++ rightTarget.fcv) := by
  intro varId membership
  simp only [List.mem_append] at membership ⊢
  rcases membership with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

private theorem annotated_targetWithin
    {leftTarget rightTarget : Ty}
    (C : CapSubst) :
    ∀ varId,
      varId ∈ (leftTarget.applyCapability C).ftv ++
        (rightTarget.applyCapability C).ftv →
      varId ∈ leftTarget.ftv ++ rightTarget.ftv := by
  intro varId membership
  simpa [Unification.Ty.ftv_applyCapability] using membership

private theorem annotated_zonkedCapWithin
    {ledger : CapabilityOriginLedger}
    {leftCap rightCap : Cap} {leftTarget rightTarget : Ty}
    (capResult : OrientedCapResult ledger leftCap rightCap) :
    ∀ varId,
      varId ∈ (leftTarget.applyCapability capResult.subst).fcv ++
        (rightTarget.applyCapability capResult.subst).fcv →
      varId ∈ (leftCap.fcv ++ leftTarget.fcv) ++
        (rightCap.fcv ++ rightTarget.fcv) := by
  intro varId membership
  simp only [List.mem_append] at membership
  rcases membership with leftMem | rightMem
  · rw [Unification.Ty.fcv_applyCapability] at leftMem
    obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp leftMem
    rcases capResult.inputRange source varId imageMem with rfl | capInput
    · exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr sourceMem)))
    · exact annotated_capWithin (leftTarget := leftTarget)
        (rightTarget := rightTarget) varId capInput
  · rw [Unification.Ty.fcv_applyCapability] at rightMem
    obtain ⟨source, sourceMem, imageMem⟩ := List.mem_flatMap.mp rightMem
    rcases capResult.inputRange source varId imageMem with rfl | capInput
    · exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr sourceMem)))
    · exact annotated_capWithin (leftTarget := leftTarget)
        (rightTarget := rightTarget) varId capInput

private theorem list_headCapWithin
    {leftHead rightHead : Ty} {leftTail rightTail : List Ty} :
    ∀ varId, varId ∈ leftHead.fcv ++ rightHead.fcv →
      varId ∈ Ty.fcvList (leftHead :: leftTail) ++
        Ty.fcvList (rightHead :: rightTail) := by
  intro varId membership
  simp only [Ty.fcvList, List.mem_append] at membership ⊢
  rcases membership with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

private theorem list_headTargetWithin
    {leftHead rightHead : Ty} {leftTail rightTail : List Ty} :
    ∀ varId, varId ∈ leftHead.ftv ++ rightHead.ftv →
      varId ∈ Ty.ftvList (leftHead :: leftTail) ++
        Ty.ftvList (rightHead :: rightTail) := by
  intro varId membership
  simp only [Ty.ftvList, List.mem_append] at membership ⊢
  rcases membership with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

private theorem list_tailCapWithin
    {ledger : CapabilityOriginLedger}
    {leftHead rightHead : Ty} {leftTail rightTail : List Ty}
    (headResult : PairedResult ledger leftHead rightHead) :
    ∀ varId,
      varId ∈ Ty.fcvList (leftTail.map headResult.subst.apply) ++
        Ty.fcvList (rightTail.map headResult.subst.apply) →
      varId ∈ Ty.fcvList (leftHead :: leftTail) ++
        Ty.fcvList (rightHead :: rightTail) := by
  intro varId membership
  rcases List.mem_append.mp membership with leftMem | rightMem
  · rcases pairedCapRange_map_apply_mem headResult.capRange
      headResult.targetCapRange leftMem with own | headInput
    · simp only [Ty.fcvList, List.mem_append]
      exact Or.inl (Or.inr own)
    · exact list_headCapWithin varId headInput
  · rcases pairedCapRange_map_apply_mem headResult.capRange
      headResult.targetCapRange rightMem with own | headInput
    · simp only [Ty.fcvList, List.mem_append]
      exact Or.inr (Or.inr own)
    · exact list_headCapWithin varId headInput

private theorem list_tailTargetWithin
    {ledger : CapabilityOriginLedger}
    {leftHead rightHead : Ty} {leftTail rightTail : List Ty}
    (headResult : PairedResult ledger leftHead rightHead) :
    ∀ varId,
      varId ∈ Ty.ftvList (leftTail.map headResult.subst.apply) ++
        Ty.ftvList (rightTail.map headResult.subst.apply) →
      varId ∈ Ty.ftvList (leftHead :: leftTail) ++
        Ty.ftvList (rightHead :: rightTail) := by
  intro varId membership
  rcases List.mem_append.mp membership with leftMem | rightMem
  · rcases pairedTyRange_map_apply_mem headResult.targetRange leftMem with
      own | headInput
    · simp only [Ty.ftvList, List.mem_append]
      exact Or.inl (Or.inr own)
    · exact list_headTargetWithin varId headInput
  · rcases pairedTyRange_map_apply_mem headResult.targetRange rightMem with
      own | headInput
    · simp only [Ty.ftvList, List.mem_append]
      exact Or.inr (Or.inr own)
    · exact list_headTargetWithin varId headInput

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

/-- A factorization through an earlier phase and then through a later phase
composes into a factorization through their sequential composition. -/
private theorem factor_seq
    {U residual₁ residual₂ earlier later : Subst}
    (earlierFactors : U = Subst.seq residual₁ earlier)
    (laterFactors : residual₁ = Subst.seq residual₂ later) :
    U = Subst.seq residual₂ (Subst.seq later earlier) := by
  calc
    U = Subst.seq residual₁ earlier := earlierFactors
    _ = Subst.seq (Subst.seq residual₂ later) earlier :=
      congrArg (fun residual => Subst.seq residual earlier) laterFactors
    _ = Subst.seq residual₂ (Subst.seq later earlier) :=
      (PhasedPost.seq_assoc residual₂ later earlier).symm

/-- A capability factorization lifts to the paired substitution whose target
residual is the competitor's original target component. -/
private theorem factor_capOnly
    {U : Subst} {C residualCap : CapSubst}
    (capFactors : U.cap = CapSubst.comp residualCap C) :
    U = Subst.seq (Subst.mk residualCap U.target)
      (Subst.mk C TySubst.id) := by
  apply PhasedPost.subst_ext
  · exact capFactors
  · funext varId
    rfl

/-- A residual acts on a solved input exactly as the original competitor when
the competitor factors through the solver result. -/
private theorem apply_of_factors
    {U residual solved : Subst}
    (factors : U = Subst.seq residual solved) (target : Ty) :
    residual.apply (solved.apply target) = U.apply target := by
  rw [← Subst.seq_apply, ← factors]

/-- List form of `apply_of_factors`. -/
private theorem map_apply_of_factors
    {U residual solved : Subst}
    (factors : U = Subst.seq residual solved) (targets : List Ty) :
    (targets.map solved.apply).map residual.apply = targets.map U.apply := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨apply_of_factors factors target, induction⟩

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
          capSupportInput := by simp
          targetSupportVars := []
          targetSupport := TySubst.id_supportWithin []
          targetSupportInput := by simp
          capRange := pairedCapRange_id _
          targetRange := pairedTyRange_id _
          targetCapRange := pairedTyCapRange_id _
          idempotent := Subst.id_idempotent
          sound := by subst right; rfl
          globalUniversal := by
            intro U _
            refine ⟨U, ?_⟩
            apply PhasedPost.subst_ext
            · funext varId
              rfl
            · funext varId
              rfl
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
                capSupportInput := by simp
                targetSupportVars := [varId]
                targetSupport :=
                  Unification.TySubst.single_supportWithin varId right
                targetSupportInput := by simp [Ty.ftv]
                capRange := pairedCapRange_id _
                targetRange := pairedTyRange_single varId right _ (by
                  intro image imageMem
                  exact List.mem_append.mpr (Or.inr imageMem))
                targetCapRange := pairedTyCapRange_single varId right _ (by
                  intro image imageMem
                  exact List.mem_append.mpr (Or.inr imageMem))
                idempotent := Subst.idempotent_of_capId
                  (Unification.tySingle_idempotent hoccurs)
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact (Unification.Ty.applyTarget_single_of_not_mem varId
                    right right hoccurs).symm
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, ?_⟩
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
                capSupportInput := by simp
                targetSupportVars := [varId]
                targetSupport :=
                  Unification.TySubst.single_supportWithin varId left
                targetSupportInput := by simp [Ty.ftv]
                capRange := pairedCapRange_id _
                targetRange := pairedTyRange_single varId left _ (by
                  intro image imageMem
                  exact List.mem_append.mpr (Or.inl imageMem))
                targetCapRange := pairedTyCapRange_single varId left _ (by
                  intro image imageMem
                  exact List.mem_append.mpr (Or.inl imageMem))
                idempotent := Subst.idempotent_of_capId
                  (Unification.tySingle_idempotent hoccurs)
                sound := by
                  rw [targetOnly_apply, targetOnly_apply]
                  simp only [Ty.applyTarget, Unification.TySubst.single,
                    if_pos]
                  exact Unification.Ty.applyTarget_single_of_not_mem varId
                    left left hoccurs
                globalUniversal := by
                  intro U hunify
                  refine ⟨U, ?_⟩
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
                    capSupportInput := by
                      simpa [Ty.fcv] using result.capSupportInput
                    targetSupportVars := result.targetSupportVars
                    targetSupport := result.targetSupport
                    targetSupportInput := by
                      simpa [Ty.ftv] using result.targetSupportInput
                    capRange := by simpa [Ty.fcv] using result.capRange
                    targetRange := by simpa [Ty.ftv] using result.targetRange
                    targetCapRange := by
                      simpa [Ty.fcv] using result.targetCapRange
                    idempotent := result.idempotent
                    sound := by
                      rw [subst_apply_data, subst_apply_data, hname,
                        result.sound]
                    globalUniversal := by
                      intro U hunify
                      rw [subst_apply_data, subst_apply_data] at hunify
                      simp only [Ty.data.injEq] at hunify
                      exact result.globalUniversal U hunify.2
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
                  capSupportInput := by
                    simpa [Ty.fcv] using result.capSupportInput
                  targetSupportVars := result.targetSupportVars
                  targetSupport := result.targetSupport
                  targetSupportInput := by
                    simpa [Ty.ftv] using result.targetSupportInput
                  capRange := by simpa [Ty.fcv] using result.capRange
                  targetRange := by simpa [Ty.ftv] using result.targetRange
                  targetCapRange := by
                    simpa [Ty.fcv] using result.targetCapRange
                  idempotent := result.idempotent
                  sound := by
                    rw [subst_apply_prod, subst_apply_prod, result.sound]
                  globalUniversal := by
                    intro U hunify
                    rw [subst_apply_prod, subst_apply_prod] at hunify
                    simp only [Ty.prod.injEq] at hunify
                    exact result.globalUniversal U hunify
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
                      capSupportInput :=
                        seq_supportInput
                          (fun varId membership => fn_domainCapWithin
                            varId (domainResult.capSupportInput varId
                              membership))
                          codomainResult.capSupportInput
                          (fn_codomainCapWithin domainResult)
                      targetSupportVars :=
                        domainResult.targetSupportVars ++
                          codomainResult.targetSupportVars
                      targetSupport :=
                        seq_targetSupport domainResult.targetSupport
                          codomainResult.targetSupport
                      targetSupportInput :=
                        seq_supportInput
                          (fun varId membership => fn_domainTargetWithin
                            varId (domainResult.targetSupportInput varId
                              membership))
                          codomainResult.targetSupportInput
                          (fn_codomainTargetWithin domainResult)
                      capRange :=
                        pairedCapRange_comp
                          (pairedCapRange_mono domainResult.capRange
                            fn_domainCapWithin)
                          codomainResult.capRange
                          (fn_codomainCapWithin domainResult)
                      targetRange :=
                        pairedTyRange_seq
                          (pairedTyRange_mono domainResult.targetRange
                            fn_domainTargetWithin)
                          codomainResult.targetRange
                          (fn_codomainTargetWithin domainResult)
                      targetCapRange :=
                        pairedTyCapRange_seq
                          (pairedTyCapRange_mono
                            domainResult.targetCapRange fn_domainCapWithin)
                          codomainResult.capRange
                          codomainResult.targetCapRange
                          (fn_codomainCapWithin domainResult)
                      idempotent := pairedSeq_idempotent
                        domainResult.idempotent codomainResult.idempotent
                        codomainResult.capRange codomainResult.targetRange
                        codomainResult.targetCapRange
                        (by
                          intro varId membership
                          rcases List.mem_append.mp membership with
                            leftMem | rightMem
                          · exact domainResult.idempotent.image_target_fixed
                              leftCodomain varId leftMem
                          · exact domainResult.idempotent.image_target_fixed
                              rightCodomain varId rightMem)
                        (by
                          intro varId membership
                          rcases List.mem_append.mp membership with
                            leftMem | rightMem
                          · exact domainResult.idempotent.image_cap_fixed
                              leftCodomain varId leftMem
                          · exact domainResult.idempotent.image_cap_fixed
                              rightCodomain varId rightMem)
                      sound := by
                        rw [subst_apply_fn, subst_apply_fn, Subst.seq_apply,
                          Subst.seq_apply, Subst.seq_apply, Subst.seq_apply,
                          domainResult.sound, codomainResult.sound]
                      globalUniversal := by
                        intro U hunify
                        rw [subst_apply_fn, subst_apply_fn] at hunify
                        simp only [Ty.fn.injEq] at hunify
                        obtain ⟨hdomain, hcodomain⟩ := hunify
                        obtain ⟨R₁, domainFactors⟩ :=
                          domainResult.globalUniversal U hdomain
                        have hcodomain' :
                            R₁.apply
                                (domainResult.subst.apply leftCodomain) =
                              R₁.apply
                                (domainResult.subst.apply rightCodomain) := by
                          rw [apply_of_factors domainFactors,
                            apply_of_factors domainFactors]
                          exact hcodomain
                        obtain ⟨R₂, codomainFactors⟩ :=
                          codomainResult.globalUniversal R₁ hcodomain'
                        exact ⟨R₂,
                          factor_seq domainFactors codomainFactors⟩
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
                      capSupportInput := by
                        intro varId membership
                        rcases List.mem_append.mp membership with
                          capMem | targetMem
                        · simpa [Ty.fcv] using annotated_capWithin varId
                            (capResult.supportInput varId capMem)
                        · simpa [Ty.fcv] using
                            annotated_zonkedCapWithin capResult varId
                              (targetResult.capSupportInput varId targetMem)
                      targetSupportVars := targetResult.targetSupportVars
                      targetSupport := by
                        simpa using seq_targetSupport
                          (later := targetResult.subst)
                          (earlier := Subst.mk capResult.subst TySubst.id)
                          (earlierVars := [])
                          (laterVars := targetResult.targetSupportVars)
                          (TySubst.id_supportWithin [])
                          targetResult.targetSupport
                      targetSupportInput := by
                        intro varId membership
                        simpa [Ty.ftv] using annotated_targetWithin
                          capResult.subst varId
                            (targetResult.targetSupportInput varId membership)
                      capRange := by
                        change Unification.CapRange
                          (CapSubst.comp targetResult.subst.cap
                            capResult.subst) _
                        simpa [Ty.fcv] using pairedCapRange_comp
                          (pairedCapRange_mono capResult.inputRange
                            (annotated_capWithin
                              (leftTarget := leftTarget)
                              (rightTarget := rightTarget)))
                          targetResult.capRange
                          (annotated_zonkedCapWithin capResult)
                      targetRange := by
                        simpa [Ty.ftv] using pairedTyRange_seq
                          (later := targetResult.subst)
                          (earlier :=
                            Subst.mk capResult.subst TySubst.id)
                          (pairedTyRange_id
                            (leftTarget.ftv ++ rightTarget.ftv))
                          targetResult.targetRange
                          (annotated_targetWithin capResult.subst)
                      targetCapRange := by
                        simpa [Ty.fcv] using pairedTyCapRange_seq
                          (later := targetResult.subst)
                          (earlier :=
                            Subst.mk capResult.subst TySubst.id)
                          (pairedTyCapRange_id
                            ((leftCap.fcv ++ leftTarget.fcv) ++
                              (rightCap.fcv ++ rightTarget.fcv)))
                          targetResult.capRange
                          targetResult.targetCapRange
                          (annotated_zonkedCapWithin capResult)
                      idempotent := pairedSeq_idempotent
                        (orientedCapPhase_idempotent capResult)
                        targetResult.idempotent targetResult.capRange
                        targetResult.targetRange targetResult.targetCapRange
                        (by intro varId _; rfl)
                        (orientedCapPhase_zonkedCapsFixed capResult
                          leftTarget rightTarget)
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
                      globalUniversal := by
                        intro U hunify
                        rw [subst_apply_matcher, subst_apply_matcher] at hunify
                        simp only [Ty.matcher.injEq] at hunify
                        obtain ⟨hcap, htarget⟩ := hunify
                        obtain ⟨residualCap, capFactors⟩ :=
                          capResult.globalUniversal U.cap hcap
                        let R₁ : Subst := Subst.mk residualCap U.target
                        have capPairFactors : U = Subst.seq R₁
                            (Subst.mk capResult.subst TySubst.id) := by
                          exact factor_capOnly capFactors
                        have htarget' :
                            R₁.apply
                                (leftTarget.applyCapability capResult.subst) =
                              R₁.apply
                                (rightTarget.applyCapability
                                  capResult.subst) := by
                          rw [← capOnly_apply capResult.subst leftTarget,
                            ← capOnly_apply capResult.subst rightTarget,
                            apply_of_factors capPairFactors,
                            apply_of_factors capPairFactors]
                          exact htarget
                        obtain ⟨R₂, targetFactors⟩ :=
                          targetResult.globalUniversal R₁ htarget'
                        exact ⟨R₂,
                          factor_seq capPairFactors targetFactors⟩
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
                      capSupportInput := by
                        intro varId membership
                        rcases List.mem_append.mp membership with
                          capMem | targetMem
                        · simpa [Ty.fcv] using annotated_capWithin varId
                            (capResult.supportInput varId capMem)
                        · simpa [Ty.fcv] using
                            annotated_zonkedCapWithin capResult varId
                              (targetResult.capSupportInput varId targetMem)
                      targetSupportVars := targetResult.targetSupportVars
                      targetSupport := by
                        simpa using seq_targetSupport
                          (later := targetResult.subst)
                          (earlier := Subst.mk capResult.subst TySubst.id)
                          (earlierVars := [])
                          (laterVars := targetResult.targetSupportVars)
                          (TySubst.id_supportWithin [])
                          targetResult.targetSupport
                      targetSupportInput := by
                        intro varId membership
                        simpa [Ty.ftv] using annotated_targetWithin
                          capResult.subst varId
                            (targetResult.targetSupportInput varId membership)
                      capRange := by
                        change Unification.CapRange
                          (CapSubst.comp targetResult.subst.cap
                            capResult.subst) _
                        simpa [Ty.fcv] using pairedCapRange_comp
                          (pairedCapRange_mono capResult.inputRange
                            (annotated_capWithin
                              (leftTarget := leftTarget)
                              (rightTarget := rightTarget)))
                          targetResult.capRange
                          (annotated_zonkedCapWithin capResult)
                      targetRange := by
                        simpa [Ty.ftv] using pairedTyRange_seq
                          (later := targetResult.subst)
                          (earlier :=
                            Subst.mk capResult.subst TySubst.id)
                          (pairedTyRange_id
                            (leftTarget.ftv ++ rightTarget.ftv))
                          targetResult.targetRange
                          (annotated_targetWithin capResult.subst)
                      targetCapRange := by
                        simpa [Ty.fcv] using pairedTyCapRange_seq
                          (later := targetResult.subst)
                          (earlier :=
                            Subst.mk capResult.subst TySubst.id)
                          (pairedTyCapRange_id
                            ((leftCap.fcv ++ leftTarget.fcv) ++
                              (rightCap.fcv ++ rightTarget.fcv)))
                          targetResult.capRange
                          targetResult.targetCapRange
                          (annotated_zonkedCapWithin capResult)
                      idempotent := pairedSeq_idempotent
                        (orientedCapPhase_idempotent capResult)
                        targetResult.idempotent targetResult.capRange
                        targetResult.targetRange targetResult.targetCapRange
                        (by intro varId _; rfl)
                        (orientedCapPhase_zonkedCapsFixed capResult
                          leftTarget rightTarget)
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
                      globalUniversal := by
                        intro U hunify
                        rw [subst_apply_slot, subst_apply_slot] at hunify
                        simp only [Ty.slot.injEq] at hunify
                        obtain ⟨hcap, htarget⟩ := hunify
                        obtain ⟨residualCap, capFactors⟩ :=
                          capResult.globalUniversal U.cap hcap
                        let R₁ : Subst := Subst.mk residualCap U.target
                        have capPairFactors : U = Subst.seq R₁
                            (Subst.mk capResult.subst TySubst.id) := by
                          exact factor_capOnly capFactors
                        have htarget' :
                            R₁.apply
                                (leftTarget.applyCapability capResult.subst) =
                              R₁.apply
                                (rightTarget.applyCapability
                                  capResult.subst) := by
                          rw [← capOnly_apply capResult.subst leftTarget,
                            ← capOnly_apply capResult.subst rightTarget,
                            apply_of_factors capPairFactors,
                            apply_of_factors capPairFactors]
                          exact htarget
                        obtain ⟨R₂, targetFactors⟩ :=
                          targetResult.globalUniversal R₁ htarget'
                        exact ⟨R₂,
                          factor_seq capPairFactors targetFactors⟩
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
        capSupportInput := by simp
        targetSupportVars := []
        targetSupport := TySubst.id_supportWithin []
        targetSupportInput := by simp
        capRange := pairedCapRange_id _
        targetRange := pairedTyRange_id _
        targetCapRange := pairedTyCapRange_id _
        idempotent := Subst.id_idempotent
        sound := rfl
        globalUniversal := by
          intro U _
          refine ⟨U, ?_⟩
          apply PhasedPost.subst_ext
          · funext varId
            rfl
          · funext varId
            rfl
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
                capSupportInput :=
                  seq_supportInput
                    (fun varId membership => list_headCapWithin varId
                      (headResult.capSupportInput varId membership))
                    tailResult.capSupportInput
                    (list_tailCapWithin headResult)
                targetSupportVars :=
                  headResult.targetSupportVars ++
                    tailResult.targetSupportVars
                targetSupport :=
                  seq_targetSupport headResult.targetSupport
                    tailResult.targetSupport
                targetSupportInput :=
                  seq_supportInput
                    (fun varId membership => list_headTargetWithin varId
                      (headResult.targetSupportInput varId membership))
                    tailResult.targetSupportInput
                    (list_tailTargetWithin headResult)
                capRange :=
                  pairedCapRange_comp
                    (pairedCapRange_mono headResult.capRange
                      list_headCapWithin)
                    tailResult.capRange
                    (list_tailCapWithin headResult)
                targetRange :=
                  pairedTyRange_seq
                    (pairedTyRange_mono headResult.targetRange
                      list_headTargetWithin)
                    tailResult.targetRange
                    (list_tailTargetWithin headResult)
                targetCapRange :=
                  pairedTyCapRange_seq
                    (pairedTyCapRange_mono headResult.targetCapRange
                      list_headCapWithin)
                    tailResult.capRange tailResult.targetCapRange
                    (list_tailCapWithin headResult)
                idempotent := pairedSeq_idempotent
                  headResult.idempotent tailResult.idempotent
                  tailResult.capRange tailResult.targetRange
                  tailResult.targetCapRange
                  (by
                    intro varId membership
                    rcases List.mem_append.mp membership with
                      leftMem | rightMem
                    · exact idempotent_target_fixed_map
                        headResult.idempotent leftTail varId leftMem
                    · exact idempotent_target_fixed_map
                        headResult.idempotent rightTail varId rightMem)
                  (by
                    intro varId membership
                    rcases List.mem_append.mp membership with
                      leftMem | rightMem
                    · exact idempotent_cap_fixed_map
                        headResult.idempotent leftTail varId leftMem
                    · exact idempotent_cap_fixed_map
                        headResult.idempotent rightTail varId rightMem)
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
                globalUniversal := by
                  intro U hunify
                  simp only [List.map, List.cons.injEq] at hunify
                  obtain ⟨hhead, htail⟩ := hunify
                  obtain ⟨R₁, headFactors⟩ :=
                    headResult.globalUniversal U hhead
                  have htail' :
                      (leftTail.map headResult.subst.apply).map R₁.apply =
                        (rightTail.map headResult.subst.apply).map
                          R₁.apply := by
                    rw [map_apply_of_factors headFactors,
                      map_apply_of_factors headFactors]
                    exact htail
                  obtain ⟨R₂, tailFactors⟩ :=
                    tailResult.globalUniversal R₁ htail'
                  exact ⟨R₂, factor_seq headFactors tailFactors⟩
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

/-- Every paired unifier, without an origin-ledger side condition, factors
through the substitution returned by the executable paired solver. -/
theorem mguPairedTy_globalUniversal
    {ledger : CapabilityOriginLedger} {left right : Ty} {S U : Subst}
    (hsuccess : mguPairedTy ledger left right = some S)
    (competitorSound : U.apply left = U.apply right) :
    ∃ R : Subst, U = Subst.seq R S := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by
        simpa [hsolve] using hsuccess
      subst S
      exact result.globalUniversal U competitorSound

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

/-- Every variable in the executable capability-support ledger comes from
the paired input constraint. -/
theorem mguPairedTy_capSupportInput
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    ∀ varId, varId ∈ mguPairedTyCapSupport ledger left right →
      varId ∈ left.fcv ++ right.fcv := by
  unfold mguPairedTy at hsuccess
  unfold mguPairedTyCapSupport
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      intro varId membership
      simpa [hsolve] using result.capSupportInput varId membership

/-- Every variable in the executable target-support ledger comes from the
paired input constraint. -/
theorem mguPairedTy_supportInput
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    ∀ varId, varId ∈ mguPairedTySupport ledger left right →
      varId ∈ left.ftv ++ right.ftv := by
  unfold mguPairedTy at hsuccess
  unfold mguPairedTySupport
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      intro varId membership
      simpa [hsolve] using result.targetSupportInput varId membership

/-- Capability images returned by paired unification mention only their
source variable or capability variables from the input constraint. -/
theorem mguPairedTy_capRange
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    Unification.CapRange S.cap (left.fcv ++ right.fcv) := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by simpa [hsolve] using hsuccess
      subst S
      exact result.capRange

/-- Target variables in target images returned by paired unification are the
source variable or target variables from the input constraint. -/
theorem mguPairedTy_targetRange
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    Unification.TyRange S.target (left.ftv ++ right.ftv) := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by simpa [hsolve] using hsuccess
      subst S
      exact result.targetRange

/-- Capability variables in target images returned by paired unification
come from the input constraint. -/
theorem mguPairedTy_targetCapRange
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) :
    Unification.TyCapRange S.target (left.fcv ++ right.fcv) := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by simpa [hsolve] using hsuccess
      subst S
      exact result.targetCapRange

/-- Every substitution returned by paired unification is in solved form. -/
theorem mguPairedTy_idempotent
    {ledger : CapabilityOriginLedger} {left right : Ty} {S : Subst}
    (hsuccess : mguPairedTy ledger left right = some S) : S.Idempotent := by
  unfold mguPairedTy at hsuccess
  cases hsolve : solvePairedTy (Unification.tyFuel left right) ledger left
      right with
  | none => simp [hsolve] at hsuccess
  | some result =>
      have heq : result.subst = S := by simpa [hsolve] using hsuccess
      subst S
      exact result.idempotent

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
