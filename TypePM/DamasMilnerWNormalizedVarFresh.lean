import TypePM.DamasMilnerWNormalizedOpening
import TypePM.DamasMilnerWRetired
import TypePM.DamasMilnerWNormalizedVar
import TypePM.DamasMilnerWGenerativeTransport

/-!
# Fresh-variable support of capability-free scheme openings

These syntax lemmas isolate the only support fact needed by the erased
variable case: opening a scheme with no capability binders introduces no
variables except ambient scheme metavariables and the selected target images.
-/

namespace TypePM
namespace DM

mutual

theorem PolyCap.mem_fcv_instantiate_zero (openCap : Fin 0 → Cap) :
    ∀ (body : PolyCap 0) (varId : CapVar),
      varId ∈ (body.instantiate openCap).fcv → varId ∈ body.fcv
  | .any, _, member => by simp [PolyCap.instantiate, Cap.fcv] at member
  | .mvar _, _, member => by
      simpa [PolyCap.instantiate, PolyCap.fcv, Cap.fcv] using member
  | .bound index, _, _ => Fin.elim0 index
  | .skolem _, _, member => by simp [PolyCap.instantiate, Cap.fcv] at member
  | .con _ children, varId, member => by
      exact PolyCap.mem_fcvList_instantiate_zero openCap children varId
        (by simpa [PolyCap.instantiate, PolyCap.fcv, Cap.fcv] using member)
  | .prod components, varId, member => by
      exact PolyCap.mem_fcvList_instantiate_zero openCap components varId
        (by simpa [PolyCap.instantiate, PolyCap.fcv, Cap.fcv] using member)

theorem PolyCap.mem_fcvList_instantiate_zero (openCap : Fin 0 → Cap) :
    ∀ (bodies : List (PolyCap 0)) (varId : CapVar),
      varId ∈ Cap.fcvList (bodies.map (PolyCap.instantiate openCap)) →
        varId ∈ PolyCap.fcvList bodies
  | [], _, member => by simp [Cap.fcvList] at member
  | body :: bodies, varId, member => by
      rcases List.mem_append.mp (by simpa [Cap.fcvList] using member) with
        head | tail
      · exact List.mem_append_left _
          (PolyCap.mem_fcv_instantiate_zero openCap body varId head)
      · exact List.mem_append_right _
          (PolyCap.mem_fcvList_instantiate_zero openCap bodies varId tail)

end


mutual

theorem PolyTy.mem_fcv_instantiate_zero
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty)
    (imagesCapFree : ∀ index, (openTy index).fcv = []) :
    ∀ (body : PolyTy 0 tyArity) (varId : CapVar),
      varId ∈ (body.instantiate openCap openTy).fcv → varId ∈ body.fcv
  | .mvar _, _, member => by simp [PolyTy.instantiate, Ty.fcv] at member
  | .bound index, _, member => by
      simp only [PolyTy.instantiate] at member
      rw [imagesCapFree index] at member
      exact False.elim (List.not_mem_nil member)
  | .skolem _, _, member => by simp [PolyTy.instantiate, Ty.fcv] at member
  | .unit, _, member => by simp [PolyTy.instantiate, Ty.fcv] at member
  | .int, _, member => by simp [PolyTy.instantiate, Ty.fcv] at member
  | .bool, _, member => by simp [PolyTy.instantiate, Ty.fcv] at member
  | .data _ children, varId, member => by
      exact PolyTy.mem_fcvList_instantiate_zero openCap openTy imagesCapFree
        children varId (by simpa [PolyTy.instantiate, PolyTy.fcv, Ty.fcv] using member)
  | .prod components, varId, member => by
      exact PolyTy.mem_fcvList_instantiate_zero openCap openTy imagesCapFree
        components varId (by simpa [PolyTy.instantiate, PolyTy.fcv, Ty.fcv] using member)
  | .fn domain codomain, varId, member => by
      rcases List.mem_append.mp (by simpa [PolyTy.instantiate, Ty.fcv] using member) with
        left | right
      · exact List.mem_append_left _
          (PolyTy.mem_fcv_instantiate_zero openCap openTy imagesCapFree
            domain varId left)
      · exact List.mem_append_right _
          (PolyTy.mem_fcv_instantiate_zero openCap openTy imagesCapFree
            codomain varId right)
  | .matcher capability target, varId, member => by
      rcases List.mem_append.mp (by simpa [PolyTy.instantiate, Ty.fcv] using member) with
        left | right
      · exact List.mem_append_left _
          (PolyCap.mem_fcv_instantiate_zero openCap capability varId left)
      · exact List.mem_append_right _
          (PolyTy.mem_fcv_instantiate_zero openCap openTy imagesCapFree
            target varId right)
  | .slot capability target, varId, member => by
      rcases List.mem_append.mp (by simpa [PolyTy.instantiate, Ty.fcv] using member) with
        left | right
      · exact List.mem_append_left _
          (PolyCap.mem_fcv_instantiate_zero openCap capability varId left)
      · exact List.mem_append_right _
          (PolyTy.mem_fcv_instantiate_zero openCap openTy imagesCapFree
            target varId right)

theorem PolyTy.mem_fcvList_instantiate_zero
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty)
    (imagesCapFree : ∀ index, (openTy index).fcv = []) :
    ∀ (bodies : List (PolyTy 0 tyArity)) (varId : CapVar),
      varId ∈ Ty.fcvList (bodies.map (PolyTy.instantiate openCap openTy)) →
        varId ∈ PolyTy.fcvList bodies
  | [], _, member => by simp [Ty.fcvList] at member
  | body :: bodies, varId, member => by
      rcases List.mem_append.mp (by simpa [Ty.fcvList] using member) with
        head | tail
      · exact List.mem_append_left _
          (PolyTy.mem_fcv_instantiate_zero openCap openTy imagesCapFree
            body varId head)
      · exact List.mem_append_right _
          (PolyTy.mem_fcvList_instantiate_zero openCap openTy imagesCapFree
            bodies varId tail)

end


mutual

theorem PolyTy.mem_ftv_instantiate_zero
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty) :
    ∀ (body : PolyTy 0 tyArity) (varId : TypePM.TyVar),
      varId ∈ (body.instantiate openCap openTy).ftv →
        varId ∈ body.ftv ∨ ∃ index, varId ∈ (openTy index).ftv
  | .mvar _, _, member => by
      exact Or.inl (by simpa [PolyTy.instantiate, PolyTy.ftv, Ty.ftv] using member)
  | .bound index, _, member => by
      exact Or.inr ⟨index, by simpa only [PolyTy.instantiate] using member⟩
  | .skolem _, _, member => by simp [PolyTy.instantiate, Ty.ftv] at member
  | .unit, _, member => by simp [PolyTy.instantiate, Ty.ftv] at member
  | .int, _, member => by simp [PolyTy.instantiate, Ty.ftv] at member
  | .bool, _, member => by simp [PolyTy.instantiate, Ty.ftv] at member
  | .data _ children, varId, member => by
      exact PolyTy.mem_ftvList_instantiate_zero openCap openTy children varId
        (by simpa [PolyTy.instantiate, PolyTy.ftv, Ty.ftv] using member)
  | .prod components, varId, member => by
      exact PolyTy.mem_ftvList_instantiate_zero openCap openTy components varId
        (by simpa [PolyTy.instantiate, PolyTy.ftv, Ty.ftv] using member)
  | .fn domain codomain, varId, member => by
      rcases List.mem_append.mp (by simpa [PolyTy.instantiate, Ty.ftv] using member) with
        left | right
      · rcases PolyTy.mem_ftv_instantiate_zero openCap openTy domain varId left with
          ambient | image
        · exact Or.inl (List.mem_append_left _ ambient)
        · exact Or.inr image
      · rcases PolyTy.mem_ftv_instantiate_zero openCap openTy codomain varId right with
          ambient | image
        · exact Or.inl (List.mem_append_right _ ambient)
        · exact Or.inr image
  | .matcher _ target, varId, member => by
      exact PolyTy.mem_ftv_instantiate_zero openCap openTy target varId
        (by simpa [PolyTy.instantiate, PolyTy.ftv, Ty.ftv] using member)
  | .slot _ target, varId, member => by
      exact PolyTy.mem_ftv_instantiate_zero openCap openTy target varId
        (by simpa [PolyTy.instantiate, PolyTy.ftv, Ty.ftv] using member)

theorem PolyTy.mem_ftvList_instantiate_zero
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty) :
    ∀ (bodies : List (PolyTy 0 tyArity)) (varId : TypePM.TyVar),
      varId ∈ Ty.ftvList (bodies.map (PolyTy.instantiate openCap openTy)) →
        varId ∈ PolyTy.ftvList bodies ∨
          ∃ index, varId ∈ (openTy index).ftv
  | [], _, member => by simp [Ty.ftvList] at member
  | body :: bodies, varId, member => by
      rcases List.mem_append.mp (by simpa [Ty.ftvList] using member) with
        head | tail
      · rcases PolyTy.mem_ftv_instantiate_zero openCap openTy body varId head with
          ambient | image
        · exact Or.inl (List.mem_append_left _ ambient)
        · exact Or.inr image
      · rcases PolyTy.mem_ftvList_instantiate_zero openCap openTy bodies varId tail with
          ambient | image
        · exact Or.inl (List.mem_append_right _ ambient)
        · exact Or.inr image

end


/-- Capability counterpart of `Context.mem_ftv_of_find?`. -/
theorem Context.mem_fcv_of_find?
    {context : Context} {name : String} {scheme : Scheme}
    (found : context.find? name = some scheme) {varId : CapVar}
    (free : varId ∈ scheme.fcv) : varId ∈ context.fcv := by
  unfold Context.find? at found
  rw [Option.map_eq_some_iff] at found
  obtain ⟨entry, selected, schemeEq⟩ := found
  have entryMember : entry ∈ context := List.mem_of_find?_eq_some selected
  unfold Context.fcv
  apply List.mem_flatMap.mpr
  refine ⟨entry, entryMember, ?_⟩
  simpa [schemeEq] using free

/-- Canonical fresh instantiation of a capability-free scheme selected from
a retired-fresh context is itself retired-fresh. -/
theorem Scheme.freshInstantiate_value_avoids_of_lookup
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {current : Subst} {pending : List PendingLetCut}
    {context : Context} {name : String} {scheme : Scheme}
    (empty : scheme.capArity = 0)
    (lookup : context.find? name = some scheme)
    (pendingBelow : PendingLetsBelow signature supply current pending)
    (contextFresh : ∀ cut ∈ pending,
      cut.AvoidsContext signature current context) :
    ∀ cut ∈ pending,
      cut.AvoidsTy signature current
        (InferenceBase.instantiateScheme supply scheme).value := by
  intro cut cutMember
  cases scheme with
  | mk capArity tyArity body =>
      simp only at empty
      subst capArity
      constructor
      · intro varId generalized free
        apply (contextFresh cut cutMember).caps varId generalized
        apply Context.mem_fcv_of_find? lookup
        exact PolyTy.mem_fcv_instantiate_zero
          (fun index : Fin 0 =>
            .var ((Scheme.canonicalFreshOpening supply
              { capArity := 0, tyArity := tyArity, body := body }).capImage index))
          (fun index => .var ((Scheme.canonicalFreshOpening supply
            { capArity := 0, tyArity := tyArity, body := body }).tyImage index))
          (fun index => by simp [Ty.fcv]) body varId
          (by simpa [InferenceBase.instantiateScheme, Scheme.freshInstantiate_value,
            Scheme.openValue, Scheme.instantiate,
            Scheme.FreshOpening.toValueOpening] using free)
      · intro varId generalized free
        have classified := PolyTy.mem_ftv_instantiate_zero
          (fun index : Fin 0 =>
            .var ((Scheme.canonicalFreshOpening supply
              { capArity := 0, tyArity := tyArity, body := body }).capImage index))
          (fun index => .var ((Scheme.canonicalFreshOpening supply
            { capArity := 0, tyArity := tyArity, body := body }).tyImage index))
          body varId
          (by simpa [InferenceBase.instantiateScheme, Scheme.freshInstantiate_value,
            Scheme.openValue, Scheme.instantiate,
            Scheme.FreshOpening.toValueOpening] using free)
        rcases classified with ambient | ⟨index, imageFree⟩
        · exact (contextFresh cut cutMember).targets varId generalized
            (Context.mem_ftv_of_find? lookup ambient)
        · have imageEq : varId =
              (Scheme.canonicalFreshOpening supply
                { capArity := 0, tyArity := tyArity, body := body }).tyImage
                  index := by
              simpa [Ty.ftv] using imageFree
          subst varId
          exact (Nat.not_lt_of_ge
            (Scheme.canonicalFreshOpening_ty_lower supply
              { capArity := 0, tyArity := tyArity, body := body } index))
            ((pendingBelow cut cutMember).2 _ generalized)

/-- The same support classification supplies the generative provenance used
by a variable result: every old variable of the fresh instance was already
owned by the selected environment. -/
theorem Scheme.freshInstantiate_value_oldFree_of_lookup
    {supply : InferenceBase.FreshSupply} {context : Context}
    {name : String} {scheme : Scheme}
    (empty : scheme.capArity = 0)
    (lookup : context.find? name = some scheme) :
    OldFreeInContextAt supply context
      (InferenceBase.instantiateScheme supply scheme).value := by
  cases scheme with
  | mk capArity tyArity body =>
      simp only at empty
      subst capArity
      constructor
      · intro varId free _below
        apply Context.mem_fcv_of_find? lookup
        exact PolyTy.mem_fcv_instantiate_zero
          (fun index : Fin 0 =>
            .var ((Scheme.canonicalFreshOpening supply
              { capArity := 0, tyArity := tyArity, body := body }).capImage index))
          (fun index => .var ((Scheme.canonicalFreshOpening supply
            { capArity := 0, tyArity := tyArity, body := body }).tyImage index))
          (fun index => by simp [Ty.fcv]) body varId
          (by simpa [InferenceBase.instantiateScheme, Scheme.freshInstantiate_value,
            Scheme.openValue, Scheme.instantiate,
            Scheme.FreshOpening.toValueOpening] using free)
      · intro varId free below
        have classified := PolyTy.mem_ftv_instantiate_zero
          (fun index : Fin 0 =>
            .var ((Scheme.canonicalFreshOpening supply
              { capArity := 0, tyArity := tyArity, body := body }).capImage index))
          (fun index => .var ((Scheme.canonicalFreshOpening supply
            { capArity := 0, tyArity := tyArity, body := body }).tyImage index))
          body varId
          (by simpa [InferenceBase.instantiateScheme, Scheme.freshInstantiate_value,
            Scheme.openValue, Scheme.instantiate,
            Scheme.FreshOpening.toValueOpening] using free)
        rcases classified with ambient | ⟨index, imageFree⟩
        · exact Context.mem_ftv_of_find? lookup ambient
        · have imageEq : varId =
              (Scheme.canonicalFreshOpening supply
                { capArity := 0, tyArity := tyArity, body := body }).tyImage
                  index := by
              simpa [Ty.ftv] using imageFree
          subst varId
          exact False.elim ((Nat.not_lt_of_ge
            (Scheme.canonicalFreshOpening_ty_lower supply
              { capArity := 0, tyArity := tyArity, body := body } index)) below)

/-- Owner-relative form used under local lambda bindings. -/
theorem Scheme.freshInstantiate_value_oldFree_of_lookup_owner
    {supply floor : InferenceBase.FreshSupply} {owner context : Context}
    {name : String} {scheme : Scheme}
    (empty : scheme.capArity = 0)
    (lookup : context.find? name = some scheme)
    (covered : OldContextCoveredAt floor owner context)
    (floorCaps : floor.nextCap ≤ supply.nextCap)
    (floorTargets : floor.nextTy ≤ supply.nextTy) :
    OldFreeInContextAt floor owner
      (InferenceBase.instantiateScheme supply scheme).value := by
  have activeOld := Scheme.freshInstantiate_value_oldFree_of_lookup
    (supply := supply) empty lookup
  constructor
  · intro varId free below
    exact covered.caps varId
      (activeOld.caps varId free
        (Nat.lt_of_lt_of_le below floorCaps)) below
  · intro varId free below
    exact covered.targets varId
      (activeOld.targets varId free
        (Nat.lt_of_lt_of_le below floorTargets)) below


end DM
end TypePM
