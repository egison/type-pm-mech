import TypePM.DamasMilnerWNormalized
import TypePM.DamasMilnerConservativity

/-!
# One-sort normalization of variable scheme openings

An arbitrary `ValueFlowInst` witness may assign a structurally non-DM type to
an unused target binder.  The executable variable branch needs a stronger
witness whose every target image is an embedded simple type, so that its
fresh-interval extension is exactly a paired one-sort substitution.  Unused
images are normalized by erasure (and hence ultimately to simple types such
as `int`) without changing the opened embedded result.
-/

namespace TypePM
namespace DM

/-- Canonical DM-image representative of an arbitrary core target.  Targets
outside the image are used only for unused binder positions and normalize to
`int`. -/
def normalizeCoreTy (target : Ty) : Ty :=
  match STy.ofTy? target with
  | some decoded => decoded.emb
  | none => .int

@[simp] theorem normalizeCoreTy_emb (target : STy) :
    normalizeCoreTy target.emb = target.emb := by
  simp [normalizeCoreTy]

mutual

/-- If opening an arbitrary polymorphic payload yields an embedded DM type,
normalizing every target-binder image preserves that exact result. -/
theorem PolyTy.instantiate_normalizeCoreTy_of_eq_emb
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty) : ∀ (body : PolyTy 0 tyArity)
      (target : STy),
    PolyTy.instantiate openCap openTy body = target.emb →
      PolyTy.instantiate openCap (fun index => normalizeCoreTy (openTy index))
        body = target.emb
  | .mvar varId, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality ⊢
      exact equality
  | .bound index, target, equality => by
      simp only [PolyTy.instantiate]
      have imageEq : openTy index = target.emb := by
        simpa [PolyTy.instantiate] using equality
      rw [imageEq]
      exact normalizeCoreTy_emb target
  | .skolem name, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality
  | .unit, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality
  | .int, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality ⊢
  | .bool, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality
  | .data name children, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality
  | .prod components, target, equality => by
      cases target with
      | prod targets =>
          simp only [PolyTy.instantiate, STy.emb] at equality ⊢
          congr 1
          exact PolyTy.instantiateList_normalizeCoreTy_of_eq_embList
            openCap openTy components targets (Ty.prod.inj equality)
      | var _ => simp [PolyTy.instantiate, STy.emb] at equality
      | int => simp [PolyTy.instantiate, STy.emb] at equality
      | fn _ _ => simp [PolyTy.instantiate, STy.emb] at equality
  | .fn domain codomain, target, equality => by
      cases target with
      | fn selectedDomain selectedCodomain =>
          simp only [PolyTy.instantiate, STy.emb] at equality ⊢
          injection equality with domainEq codomainEq
          rw [PolyTy.instantiate_normalizeCoreTy_of_eq_emb openCap openTy
              domain selectedDomain domainEq,
            PolyTy.instantiate_normalizeCoreTy_of_eq_emb openCap openTy
              codomain selectedCodomain codomainEq]
      | var _ => simp [PolyTy.instantiate, STy.emb] at equality
      | int => simp [PolyTy.instantiate, STy.emb] at equality
      | prod _ => simp [PolyTy.instantiate, STy.emb] at equality
  | .matcher capability body, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality
  | .slot capability body, target, equality => by
      cases target <;> simp [PolyTy.instantiate, STy.emb] at equality

theorem PolyTy.instantiateList_normalizeCoreTy_of_eq_embList
    {tyArity : Nat} (openCap : Fin 0 → Cap)
    (openTy : Fin tyArity → Ty) : ∀ (bodies : List (PolyTy 0 tyArity))
      (targets : List STy),
    bodies.map (PolyTy.instantiate openCap openTy) = STy.embList targets →
      bodies.map (PolyTy.instantiate openCap
        (fun index => normalizeCoreTy (openTy index))) =
          STy.embList targets
  | [], [], _ => rfl
  | [], _ :: _, equality => by simp [STy.embList] at equality
  | _ :: _, [], equality => by simp [STy.embList] at equality
  | body :: bodies, target :: targets, equality => by
      simp only [List.map_cons, STy.embList, List.cons.injEq] at equality ⊢
      exact ⟨
        PolyTy.instantiate_normalizeCoreTy_of_eq_emb openCap openTy
          body target equality.1,
        PolyTy.instantiateList_normalizeCoreTy_of_eq_embList openCap openTy
          bodies targets equality.2⟩

end

/-- Every use of a capability-free core scheme which produces an embedded DM
target admits an opening with all target images in the DM image. -/
theorem Scheme.normalized_valueFlowInst_of_capArity_zero
    (scheme : Scheme) (ambient : SSubst) (empty : scheme.capArity = 0)
    {target : STy}
    (instantiation :
      (scheme.applyMeta (SSubst.paired ambient)).ValueFlowInst target.emb) :
    ∃ opening : (scheme.applyMeta (SSubst.paired ambient)).ValueOpening,
      (scheme.applyMeta (SSubst.paired ambient)).openValue opening =
          target.emb ∧
      (∀ index, (eraseTy (opening.tyImage index)).emb =
        opening.tyImage index) := by
  rcases instantiation with ⟨opening, opened⟩
  cases scheme with
  | mk capArity tyArity body =>
      simp only at empty
      subst capArity
      let normalized :
          (Scheme.applyMeta (SSubst.paired ambient)
            { capArity := 0, tyArity := tyArity, body := body }).ValueOpening :=
        { capImage := fun index => Fin.elim0 index
          tyImage := fun index => normalizeCoreTy (opening.tyImage index) }
      refine ⟨normalized, ?_, ?_⟩
      · change PolyTy.instantiate
          (fun index : Fin 0 => Cap.var (normalized.capImage index))
          normalized.tyImage (body.applyMeta (SSubst.paired ambient)) =
            target.emb
        have capEq :
            (fun index : Fin 0 => Cap.var (normalized.capImage index)) =
              (fun index : Fin 0 => Cap.var (opening.capImage index)) := by
          funext index
          exact Fin.elim0 index
        rw [capEq]
        exact PolyTy.instantiate_normalizeCoreTy_of_eq_emb
          (fun index : Fin 0 => Cap.var (opening.capImage index))
          opening.tyImage (body.applyMeta (SSubst.paired ambient)) target
          opened
      · intro index
        change (eraseTy (normalizeCoreTy (opening.tyImage index))).emb =
          normalizeCoreTy (opening.tyImage index)
        unfold normalizeCoreTy
        cases decoded : STy.ofTy? (opening.tyImage index) with
        | none => rfl
        | some target => simp

/-- Read the target component of an arbitrary capability-free normalized
opening into a one-sort residual. -/
def SSubst.extendCoreOpening (ambient : SSubst)
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta (SSubst.paired ambient)).ValueOpening) :
    SSubst :=
  fun varId =>
    if bounds : supply.nextTy ≤ varId ∧
        varId - supply.nextTy < scheme.tyArity then
      eraseTy (opening.tyImage
        ⟨varId - supply.nextTy, bounds.2⟩)
    else ambient varId

theorem Scheme.extendSchemeOpening_eq_paired_of_capArity_zero
    (scheme : Scheme) (ambient : SSubst)
    (supply : InferenceBase.FreshSupply)
    (opening : (scheme.applyMeta (SSubst.paired ambient)).ValueOpening)
    (empty : scheme.capArity = 0)
    (images : ∀ index, (eraseTy (opening.tyImage index)).emb =
      opening.tyImage index) :
    extendSchemeOpening (SSubst.paired ambient) supply scheme opening =
      SSubst.paired
        (SSubst.extendCoreOpening ambient supply scheme opening) := by
  apply PhasedPost.subst_ext
  · funext varId
    simp [extendSchemeOpening, empty, SSubst.paired, CapSubst.id]
  · funext varId
    simp only [extendSchemeOpening, SSubst.paired, SSubst.emb,
      SSubst.extendCoreOpening]
    split <;> rename_i bounds
    · rw [images]
    · rfl

theorem Scheme.normalized_valueFlowInst_pairedExtension_of_capArity_zero
    (scheme : Scheme) (ambient : SSubst)
    (supply : InferenceBase.FreshSupply) (empty : scheme.capArity = 0)
    {target : STy}
    (instantiation :
      (scheme.applyMeta (SSubst.paired ambient)).ValueFlowInst target.emb) :
    ∃ (opening : (scheme.applyMeta
        (SSubst.paired ambient)).ValueOpening) (residual : SSubst),
      (scheme.applyMeta (SSubst.paired ambient)).openValue opening =
          target.emb ∧
      (∀ index, (eraseTy (opening.tyImage index)).emb =
          opening.tyImage index) ∧
      extendSchemeOpening (SSubst.paired ambient) supply scheme opening =
        SSubst.paired residual := by
  rcases Scheme.normalized_valueFlowInst_of_capArity_zero scheme ambient empty
    instantiation with ⟨opening, opened, images⟩
  refine ⟨opening, SSubst.extendCoreOpening ambient supply scheme opening,
    opened, images, ?_⟩
  exact Scheme.extendSchemeOpening_eq_paired_of_capArity_zero scheme ambient
    supply opening empty images

/-- Combine an ambient one-sort residual with the finite binder assignment
read back from a core value opening. -/
def SSubst.openingAction (binders : List TypePM.TyVar)
    (ambient : SSubst) (openTy : Fin binders.length → Ty) : SSubst :=
  fun varId =>
    match binders.finIdxOf? varId with
    | some index => eraseTy (openTy index)
    | none => ambient varId

mutual

/-- Normalizing every bound target image by erase-then-embed turns opening of
an ambient-substituted embedded body into the embedding of one one-sort
action. -/
theorem STy.instantiate_abstract_applyMeta_paired_normalized
    (binders : List TypePM.TyVar) (ambient : SSubst)
    (openCap : Fin 0 → Cap) (openTy : Fin binders.length → Ty) : ∀ target : STy,
    PolyTy.instantiate
        openCap
        (fun index => (eraseTy (openTy index)).emb)
        ((PolyTy.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)
          (fun varId => binders.finIdxOf? varId) target.emb).applyMeta
            (SSubst.paired ambient)) =
      (target.applySubst
        (SSubst.openingAction binders ambient openTy)).emb
  | .var varId => by
      simp only [STy.emb, PolyTy.abstract]
      cases found : binders.finIdxOf? varId with
      | some index =>
          simp [PolyTy.applyMeta, PolyTy.instantiate, STy.applySubst,
            SSubst.openingAction, found]
      | none =>
          simp only [PolyTy.applyMeta, STy.applySubst,
            SSubst.openingAction, found, SSubst.paired]
          rw [PolyTy.instantiate_lift]
          rfl
  | .int => by
      simp [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, STy.applySubst, SSubst.paired]
  | .fn domain codomain => by
      simp only [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, STy.applySubst]
      rw [STy.instantiate_abstract_applyMeta_paired_normalized
          binders ambient openCap openTy domain,
        STy.instantiate_abstract_applyMeta_paired_normalized
          binders ambient openCap openTy codomain]
  | .prod components => by
      simp only [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, STy.applySubst]
      congr 1
      exact STy.instantiateList_abstract_applyMeta_paired_normalized
        binders ambient openCap openTy components

/-- List form of
`STy.instantiate_abstract_applyMeta_paired_normalized`. -/
theorem STy.instantiateList_abstract_applyMeta_paired_normalized
    (binders : List TypePM.TyVar) (ambient : SSubst)
    (openCap : Fin 0 → Cap) (openTy : Fin binders.length → Ty) :
    ∀ targets : List STy,
    (((STy.embList targets).map
        (PolyTy.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)
          (fun varId => binders.finIdxOf? varId))).map
        (PolyTy.applyMeta (SSubst.paired ambient))).map
        (PolyTy.instantiate
          openCap
          (fun index => (eraseTy (openTy index)).emb)) =
      STy.embList (STy.applySubstList
        (SSubst.openingAction binders ambient openTy) targets)
  | [] => rfl
  | head :: tail => by
      simp only [STy.embList, List.map_cons, STy.applySubstList]
      rw [STy.instantiate_abstract_applyMeta_paired_normalized
          binders ambient openCap openTy head,
        STy.instantiateList_abstract_applyMeta_paired_normalized
          binders ambient openCap openTy tail]

end

mutual

/-- Erasing the same arbitrary core opening produces exactly the combined
one-sort action. -/
theorem STy.erase_instantiate_abstract_applyMeta_paired
    (binders : List TypePM.TyVar) (ambient : SSubst)
    (openCap : Fin 0 → Cap) (openTy : Fin binders.length → Ty) : ∀ target : STy,
    eraseTy (PolyTy.instantiate
        openCap openTy
        ((PolyTy.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)
          (fun varId => binders.finIdxOf? varId) target.emb).applyMeta
            (SSubst.paired ambient))) =
      target.applySubst (SSubst.openingAction binders ambient openTy)
  | .var varId => by
      simp only [STy.emb, PolyTy.abstract]
      cases found : binders.finIdxOf? varId with
      | some index =>
          simp [PolyTy.applyMeta, PolyTy.instantiate, STy.applySubst,
            SSubst.openingAction, found]
      | none =>
          simp only [PolyTy.applyMeta, STy.applySubst,
            SSubst.openingAction, found, SSubst.paired]
          rw [PolyTy.instantiate_lift]
          exact eraseTy_emb (ambient varId)
  | .int => by
      simp [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, STy.applySubst, SSubst.paired, eraseTy]
  | .fn domain codomain => by
      simp only [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, eraseTy, STy.applySubst]
      rw [STy.erase_instantiate_abstract_applyMeta_paired
          binders ambient openCap openTy domain,
        STy.erase_instantiate_abstract_applyMeta_paired
          binders ambient openCap openTy codomain]
  | .prod components => by
      simp only [STy.emb, PolyTy.abstract, PolyTy.applyMeta,
        PolyTy.instantiate, eraseTy, STy.applySubst]
      congr 1
      exact STy.eraseList_instantiate_abstract_applyMeta_paired
        binders ambient openCap openTy components

/-- List form of `STy.erase_instantiate_abstract_applyMeta_paired`. -/
theorem STy.eraseList_instantiate_abstract_applyMeta_paired
    (binders : List TypePM.TyVar) (ambient : SSubst)
    (openCap : Fin 0 → Cap) (openTy : Fin binders.length → Ty) :
    ∀ targets : List STy,
    eraseTys ((((STy.embList targets).map
        (PolyTy.abstract
          (fun varId => ([] : List CapVar).finIdxOf? varId)
          (fun varId => binders.finIdxOf? varId))).map
        (PolyTy.applyMeta (SSubst.paired ambient))).map
        (PolyTy.instantiate
          openCap openTy)) =
      STy.applySubstList
        (SSubst.openingAction binders ambient openTy) targets
  | [] => rfl
  | head :: tail => by
      simp only [STy.embList, List.map_cons, eraseTys, STy.applySubstList]
      rw [STy.erase_instantiate_abstract_applyMeta_paired
          binders ambient openCap openTy head,
        STy.eraseList_instantiate_abstract_applyMeta_paired
          binders ambient openCap openTy tail]

end

/-! ## Normalized witnesses and paired fresh-interval extensions -/

/-- Replace every target-binder image of a core opening by its one-sort
erasure re-embedded in core syntax.  An embedded scheme has no capability
binders, so the capability component is definitionally empty. -/
def SScheme.normalizeValueOpening (scheme : SScheme) (ambient : SSubst)
    (opening : (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening) :
    (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening where
  capImage := fun index => Fin.elim0 index
  tyImage := fun index => (eraseTy (opening.tyImage index)).emb

@[simp] theorem SScheme.normalizeValueOpening_tyImage
    (scheme : SScheme) (ambient : SSubst)
    (opening : (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening)
    (index : Fin scheme.binders.length) :
    (scheme.normalizeValueOpening ambient opening).tyImage index =
      (eraseTy (opening.tyImage index)).emb := rfl

/-- Erase-then-embed normalization preserves an embedded result of opening
an ambient-substituted embedded scheme. -/
theorem SScheme.normalizeValueOpening_openValue
    (scheme : SScheme) (ambient : SSubst) {target : STy}
    (opening : (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening)
    (opened : (scheme.emb.applyMeta (SSubst.paired ambient)).openValue
      opening = target.emb) :
    (scheme.emb.applyMeta (SSubst.paired ambient)).openValue
      (scheme.normalizeValueOpening ambient opening) = target.emb := by
  let openTy : Fin scheme.binders.length → Ty :=
    fun index => opening.tyImage index
  let canonical :
      (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening :=
    { capImage := fun index => Fin.elim0 index
      tyImage := openTy }
  have canonicalOpened :
      (scheme.emb.applyMeta (SSubst.paired ambient)).openValue canonical =
        target.emb := by
    rw [← opened]
    unfold Scheme.openValue
    congr 1
    funext index
    exact Fin.elim0 index
  have erased := congrArg eraseTy canonicalOpened
  simp only [Scheme.openValue, Scheme.instantiate, SScheme.emb,
    Scheme.close, Scheme.applyMeta, eraseTy_emb] at erased
  change eraseTy (PolyTy.instantiate
      (fun index : Fin 0 => Cap.var (Fin.elim0 index)) openTy
      ((PolyTy.abstract
        (fun varId => ([] : List CapVar).finIdxOf? varId)
        (fun varId => scheme.binders.finIdxOf? varId) scheme.body.emb).applyMeta
          (SSubst.paired ambient))) = target at erased
  rw [STy.erase_instantiate_abstract_applyMeta_paired
      scheme.binders ambient
      (fun index : Fin 0 => Cap.var (Fin.elim0 index))
      openTy scheme.body] at erased
  simp only [Scheme.openValue, Scheme.instantiate, SScheme.emb,
    Scheme.close, Scheme.applyMeta, SScheme.normalizeValueOpening] at ⊢
  change PolyTy.instantiate
      (fun index : Fin 0 => Cap.var (Fin.elim0 index))
      (fun index => (eraseTy (openTy index)).emb)
      ((PolyTy.abstract
        (fun varId => ([] : List CapVar).finIdxOf? varId)
        (fun varId => scheme.binders.finIdxOf? varId) scheme.body.emb).applyMeta
          (SSubst.paired ambient)) = target.emb
  rw [STy.instantiate_abstract_applyMeta_paired_normalized
      scheme.binders ambient
      (fun index : Fin 0 => Cap.var (Fin.elim0 index))
      openTy scheme.body, erased]

/-- A value-flow use of an ambient-substituted embedded scheme always has a
witness whose target images are embedded simple types. -/
theorem SScheme.normalized_valueFlowInst
    (scheme : SScheme) (ambient : SSubst) {target : STy}
    (instantiation :
      (scheme.emb.applyMeta (SSubst.paired ambient)).ValueFlowInst target.emb) :
    ∃ opening :
        (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening,
      (scheme.emb.applyMeta (SSubst.paired ambient)).openValue opening =
        target.emb ∧
      (∀ index, (eraseTy (opening.tyImage index)).emb =
        opening.tyImage index) := by
  rcases instantiation with ⟨opening, opened⟩
  refine ⟨scheme.normalizeValueOpening ambient opening,
    scheme.normalizeValueOpening_openValue ambient opening opened, ?_⟩
  intro index
  simp [SScheme.normalizeValueOpening]

/-- Read the target part of a normalized opening into the one-sort residual
which overrides precisely the canonical fresh interval. -/
def SSubst.extendValueOpening (ambient : SSubst)
    (supply : InferenceBase.FreshSupply) (scheme : SScheme)
    (opening : (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening) :
    SSubst :=
  fun varId =>
    if bounds : supply.nextTy ≤ varId ∧
        varId - supply.nextTy < scheme.binders.length then
      eraseTy (opening.tyImage
        ⟨varId - supply.nextTy, bounds.2⟩)
    else
      ambient varId

/-- Explicit-opening form of the relative principal-opening law.  Unlike the
existential convenience theorem, this preserves a caller-chosen normalized
witness. -/
theorem canonicalSchemeOpening_relative_of_opened
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (bounded : scheme.BoundedBy supply)
    (opening : (scheme.applyMeta base).ValueOpening) {target : Ty}
    (opened : (scheme.applyMeta base).openValue opening = target) :
    (extendSchemeOpening base supply scheme opening).apply
        (InferenceBase.instantiateScheme supply scheme).value = target := by
  let extended := extendSchemeOpening base supply scheme opening
  have transported := PolyTy.instantiate_applyMeta extended
    (Scheme.canonicalFreshOpening supply scheme).capImage opening.capImage
    (fun index => .var
      ((Scheme.canonicalFreshOpening supply scheme).tyImage index))
    (extendSchemeOpening_capImage base supply scheme opening) scheme.body
  have schemeEq :=
    Scheme.applyMeta_extendSchemeOpening_eq base supply scheme opening bounded
  have bodyEq : PolyTy.applyMeta extended scheme.body =
      (scheme.applyMeta base).body := by
    cases scheme with
    | mk capArity tyArity body =>
        simp only [Scheme.applyMeta] at schemeEq ⊢
        injection schemeEq
  rw [bodyEq] at transported
  have tyImages :
      (fun index => extended.apply
        (.var ((Scheme.canonicalFreshOpening supply scheme).tyImage index))) =
      opening.tyImage := by
    funext index
    exact extendSchemeOpening_tyImage base supply scheme opening index
  rw [tyImages] at transported
  calc
    extended.apply (InferenceBase.instantiateScheme supply scheme).value =
        (scheme.applyMeta base).openValue opening := by
      rw [InferenceBase.instantiateScheme_value]
      exact transported.symm
    _ = target := opened

private theorem Subst.eq_of_parts {left right : Subst}
    (caps : left.cap = right.cap) (targets : left.target = right.target) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Extending a paired residual with a normalized opening of an embedded
scheme is exactly another paired residual. -/
theorem SScheme.extendSchemeOpening_eq_paired
    (scheme : SScheme) (ambient : SSubst)
    (supply : InferenceBase.FreshSupply)
    (opening : (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening)
    (images : ∀ index, (eraseTy (opening.tyImage index)).emb =
      opening.tyImage index) :
    extendSchemeOpening (SSubst.paired ambient) supply scheme.emb opening =
      SSubst.paired
        (SSubst.extendValueOpening ambient supply scheme opening) := by
  cases scheme with
  | mk binders body =>
      apply Subst.eq_of_parts
      · funext varId
        simp [extendSchemeOpening, SScheme.emb, Scheme.close,
          SSubst.paired, CapSubst.id]
      · funext varId
        simp only [extendSchemeOpening, SScheme.emb, Scheme.close,
          SSubst.paired, SSubst.emb, SSubst.extendValueOpening]
        split <;> rename_i bounds
        · rw [images]
        · rfl

/-- Complete normalized-opening package used by the variable case of W:
the same embedded target is opened, every target image lies in the DM image,
and the fresh-interval post is exactly paired. -/
theorem SScheme.normalized_valueFlowInst_pairedExtension
    (scheme : SScheme) (ambient : SSubst)
    (supply : InferenceBase.FreshSupply) {target : STy}
    (instantiation :
      (scheme.emb.applyMeta (SSubst.paired ambient)).ValueFlowInst target.emb) :
    ∃ (opening :
        (scheme.emb.applyMeta (SSubst.paired ambient)).ValueOpening)
      (residual : SSubst),
      (scheme.emb.applyMeta (SSubst.paired ambient)).openValue opening =
          target.emb ∧
      (∀ index, (eraseTy (opening.tyImage index)).emb =
          opening.tyImage index) ∧
      extendSchemeOpening (SSubst.paired ambient) supply scheme.emb opening =
        SSubst.paired residual := by
  rcases scheme.normalized_valueFlowInst ambient instantiation with
    ⟨opening, opened, images⟩
  refine ⟨opening, SSubst.extendValueOpening ambient supply scheme opening,
    opened, images, ?_⟩
  exact scheme.extendSchemeOpening_eq_paired ambient supply opening images


end DM
end TypePM
