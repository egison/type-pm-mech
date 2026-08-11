import TypePM.DemandTypingErasure
import TypePM.SourceSubstitution
import TypePM.SourceGeneralization

/-!
# Residual-post transport for demand-typing erasure

This module isolates the non-structural part of state erasure: a value-flow
scheme instance may cross a later substitution only when the images of its
quantified capability binders remain capability variables.  Ordinary target
images may still be specialized structurally.

The lemmas below deliberately ask only for variable-valuedness of the binder
images used by the concrete instance.  They do not strengthen this local
condition to the global `VariablePost` premise used by the general source
substitution theorem.
-/

namespace TypePM

/-! ## Solved-form facts for capture-avoiding scheme application -/

/-- A capability occurring in the image of an occurring target variable also
occurs after target substitution.  This is the forward counterpart needed in
the capture-avoiding fixedness proof below. -/
theorem Ty.mem_fcv_applyTarget_of_image
    (target : Ty) (T : TySubst) {tyVar : TypePM.TyVar} {capVar : CapVar}
    (tyMem : tyVar ∈ target.ftv) (capMem : capVar ∈ (T tyVar).fcv) :
    capVar ∈ (target.applyTarget T).fcv := by
  induction target using Ty.rec
    (motive_2 := fun targets => tyVar ∈ Ty.ftvList targets →
      capVar ∈ Ty.fcvList (Ty.applyTargetList T targets)) with
  | var candidate =>
      have equality : tyVar = candidate := by
        simpa [Ty.ftv] using tyMem
      subst tyVar
      exact capMem
  | skolem name => nomatch tyMem
  | unit => nomatch tyMem
  | int => nomatch tyMem
  | bool => nomatch tyMem
  | data name fields fieldsIH => exact fieldsIH tyMem
  | prod fields fieldsIH => exact fieldsIH tyMem
  | fn domain codomain domainIH codomainIH =>
      rcases List.mem_append.mp tyMem with here | there
      · exact List.mem_append.mpr (Or.inl (domainIH here))
      · exact List.mem_append.mpr (Or.inr (codomainIH there))
  | matcher capability payload payloadIH =>
      exact List.mem_append.mpr (Or.inr (payloadIH tyMem))
  | slot capability payload payloadIH =>
      exact List.mem_append.mpr (Or.inr (payloadIH tyMem))
  | nil => contradiction
  | cons head tail headIH tailIH =>
      rename_i tyMem
      rcases List.mem_append.mp tyMem with here | there
      · exact List.mem_append.mpr (Or.inl (headIH here))
      · exact List.mem_append.mpr (Or.inr (tailIH there))

/-- Free capability variables of a capture-avoiding image of a scheme are
fixed by the solved-form substitution that produced that image. -/
theorem Scheme.applySubst_fcv_fixed_of_idempotent
    {S : Subst} (idem : S.Idempotent) (raw : Scheme) :
    ∀ varId, varId ∈ (raw.applySubst S).fcv →
      S.cap varId = .var varId := by
  intro varId membership
  rcases raw with ⟨capBinders, tyBinders, body⟩
  have bodyMem : varId ∈
      ((Subst.mk (S.cap.mask capBinders)
        (S.target.mask tyBinders)).apply body).fcv :=
    (List.mem_filter.mp membership).1
  have notCapBinder : varId ∉ capBinders :=
    of_decide_eq_true (List.mem_filter.mp membership).2
  rcases Ty.mem_fcv_applyTarget _ _ varId bodyMem with own | targetImage
  · rw [Ty.fcv_applyCapability] at own
    rcases List.mem_flatMap.mp own with
      ⟨sourceVar, sourceMem, imageMem⟩
    by_cases bound : sourceVar ∈ capBinders
    · have equality : varId = sourceVar := by
        simpa [CapSubst.mask, bound, Cap.fcv] using imageMem
      subst varId
      exact False.elim (notCapBinder bound)
    · have imageMem' : varId ∈ (S.cap sourceVar).fcv := by
        simpa [CapSubst.mask, bound] using imageMem
      have inCapApplied : varId ∈ (body.applyCapability S.cap).fcv := by
        rw [Ty.fcv_applyCapability]
        exact List.mem_flatMap.mpr ⟨sourceVar, sourceMem, imageMem'⟩
      exact idem.image_cap_fixed body varId
        (Ty.mem_fcv_applyTarget_of_mem _ _ _ inCapApplied)
  · rcases targetImage with ⟨sourceVar, sourceMem, imageMem⟩
    rw [Ty.ftv_applyCapability] at sourceMem
    by_cases bound : sourceVar ∈ tyBinders
    · simp [TySubst.mask, bound, Ty.fcv] at imageMem
    · have imageMem' : varId ∈ (S.target sourceVar).fcv := by
        simpa [TySubst.mask, bound] using imageMem
      have sourceMem' : sourceVar ∈ (body.applyCapability S.cap).ftv := by
        simpa [Ty.ftv_applyCapability] using sourceMem
      exact idem.image_cap_fixed body varId
        (Ty.mem_fcv_applyTarget_of_image _ _ sourceMem' imageMem')

/-- Ordinary free variables satisfy the analogous solved-form property. -/
theorem Scheme.applySubst_ftv_fixed_of_idempotent
    {S : Subst} (idem : S.Idempotent) (raw : Scheme) :
    ∀ varId, varId ∈ (raw.applySubst S).ftv →
      S.target varId = .var varId := by
  intro varId membership
  rcases raw with ⟨capBinders, tyBinders, body⟩
  have bodyMem : varId ∈
      ((Subst.mk (S.cap.mask capBinders)
        (S.target.mask tyBinders)).apply body).ftv :=
    (List.mem_filter.mp membership).1
  have notTyBinder : varId ∉ tyBinders :=
    of_decide_eq_true (List.mem_filter.mp membership).2
  change varId ∈
    (((body.applyCapability (S.cap.mask capBinders)).applyTarget
      (S.target.mask tyBinders))).ftv at bodyMem
  rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability] at bodyMem
  rcases List.mem_flatMap.mp bodyMem with
    ⟨sourceVar, sourceMem, imageMem⟩
  by_cases bound : sourceVar ∈ tyBinders
  · have equality : varId = sourceVar := by
      simpa [TySubst.mask, bound, Ty.ftv] using imageMem
    subst varId
    exact False.elim (notTyBinder bound)
  · have imageMem' : varId ∈ (S.target sourceVar).ftv := by
      simpa [TySubst.mask, bound] using imageMem
    have finalMem : varId ∈ (S.apply body).ftv := by
      change varId ∈
        ((body.applyCapability S.cap).applyTarget S.target).ftv
      rw [Unification.Ty.ftv_applyTarget, Ty.ftv_applyCapability]
      exact List.mem_flatMap.mpr ⟨sourceVar, sourceMem, imageMem'⟩
    exact idem.image_target_fixed body varId finalMem

/-- A context lookup after capture-avoiding substitution has a unique source
lookup witness.  No typing evidence is stored in this provenance fact. -/
theorem Context.find?_applySubst_some_origin
    (S : Subst) (context : Context) (name : String) (scheme : Scheme)
    (lookup : (context.applySubst S).find? name = some scheme) :
    ∃ rawScheme,
      context.find? name = some rawScheme ∧
      rawScheme.applySubst S = scheme := by
  have mapped : (context.find? name).map (Scheme.applySubst S) =
      some scheme := by
    rw [← Context.find?_applySubst]
    exact lookup
  cases sourceLookup : context.find? name with
  | none => simp [sourceLookup] at mapped
  | some rawScheme =>
      refine ⟨rawScheme, rfl, ?_⟩
      simpa [sourceLookup] using mapped

/--
The canonical fresh instance of a scheme is fixed by a solved, bounded
prevailing substitution once that substitution fixes the scheme's free
variables.  Boundedness fixes the newly allocated binder images; the two
free-variable premises handle the already-zonked body.
-/
theorem Scheme.instantiate_value_fixed_of_free_fixed
    {S : Subst} {q : InferenceBase.FreshSupply} {scheme : Scheme}
    (bounded : S.BoundedBy q)
    (capFixed : ∀ varId, varId ∈ scheme.fcv →
      S.cap varId = .var varId)
    (targetFixed : ∀ varId, varId ∈ scheme.ftv →
      S.target varId = .var varId) :
    S.apply (InferenceBase.instantiateScheme q scheme).value =
      (InferenceBase.instantiateScheme q scheme).value := by
  let fresh := (InferenceBase.instantiateScheme q scheme).subst
  have capEquation : scheme.postCap S fresh.cap = fresh.cap := by
    funext candidate
    by_cases binder : candidate ∈ scheme.capBinders
    · have freshEquation : fresh.cap candidate =
          .var ⟨q.nextCap + candidate.id⟩ := by
        simp [fresh, InferenceBase.instantiateScheme,
          InferenceBase.instantiateBinders,
          InferenceBase.freshCapSubst, binder]
      simp only [Scheme.postCap, binder, if_true, freshEquation, Cap.apply]
      exact bounded.capFixedAbove _ (Nat.le_add_right _ _)
    · simp [Scheme.postCap, fresh, InferenceBase.instantiateScheme,
        InferenceBase.instantiateBinders,
        InferenceBase.freshCapSubst, binder]
  have targetEquation : scheme.postTarget S fresh.target = fresh.target := by
    funext candidate
    by_cases binder : candidate ∈ scheme.tyBinders
    · have freshEquation : fresh.target candidate =
          .var (q.nextTy + candidate) := by
        simp [fresh, InferenceBase.instantiateScheme,
          InferenceBase.instantiateBinders,
          InferenceBase.freshTySubst, binder]
      simp only [Scheme.postTarget, binder, if_true, freshEquation,
        Subst.apply, Ty.applyCapability, Ty.applyTarget]
      exact bounded.targetFixedAbove _ (Nat.le_add_right _ _)
    · simp [Scheme.postTarget, fresh, InferenceBase.instantiateScheme,
        InferenceBase.instantiateBinders,
        InferenceBase.freshTySubst, binder]
  have composed := Scheme.post_apply
    (external := S) (scheme := scheme)
    (originalCap := fresh.cap) (originalTarget := fresh.target)
    (InferenceBase.instantiateBinders_cap_support q
      scheme.capBinders scheme.tyBinders)
    (InferenceBase.instantiateBinders_ty_support q
      scheme.capBinders scheme.tyBinders)
    capFixed targetFixed
  change
    (Subst.mk (scheme.postCap S fresh.cap)
      (scheme.postTarget S fresh.target)).apply scheme.body =
      S.apply (fresh.apply scheme.body) at composed
  change S.apply (fresh.apply scheme.body) = fresh.apply scheme.body
  rw [← composed, capEquation, targetEquation]

/-- A solved and bounded substitution fixes the canonical instance of every
scheme that it has itself produced by capture-avoiding application. -/
theorem Scheme.instantiate_applySubst_value_fixed
    {S : Subst} {q : InferenceBase.FreshSupply} (raw : Scheme)
    (bounded : S.BoundedBy q) (idem : S.Idempotent) :
    S.apply
        (InferenceBase.instantiateScheme q (raw.applySubst S)).value =
      (InferenceBase.instantiateScheme q (raw.applySubst S)).value :=
  Scheme.instantiate_value_fixed_of_free_fixed bounded
    (Scheme.applySubst_fcv_fixed_of_idempotent idem raw)
    (Scheme.applySubst_ftv_fixed_of_idempotent idem raw)

/-! ## Minimal context certificate for canonical lookup transport -/

/--
Algebraic context transport needed by a canonical DD variable leaf.

This certificate mentions neither `RuntimeTyping` nor a recursively erased
expression.  It says only that each selected source scheme has a selected
target scheme which admits the post-image of the canonical instance allocated
at this cut.  It is strictly weaker than `Context.FlowsUnder`, whose scheme
component quantifies over every value-flow instance and every agreeing post.
-/
def Context.CanonicalInstanceFlowAt
    (q : InferenceBase.FreshSupply) (post : Subst)
    (source target : Context) : Prop :=
  ∀ {name scheme}, source.find? name = some scheme →
    ∃ targetScheme,
      target.find? name = some targetScheme ∧
      targetScheme.ValueFlowInst
        (post.apply (InferenceBase.instantiateScheme q scheme).value)

/-- The stronger existing context-flow invariant supplies the canonical
lookup certificate whenever the post is globally variable-valued. -/
theorem Context.FlowsUnder.toCanonicalInstanceFlowAt
    {q : InferenceBase.FreshSupply} {post : Subst}
    {source target : Context}
    (flow : Context.FlowsUnder post source target)
    (postVariable : VariablePost post) :
    Context.CanonicalInstanceFlowAt q post source target := by
  intro name scheme lookup
  rcases flow.find? lookup with ⟨targetScheme, targetLookup, schemeFlow⟩
  refine ⟨targetScheme, targetLookup, ?_⟩
  apply schemeFlow postVariable
  · intros
    rfl
  · intros
    rfl
  · refine ⟨(InferenceBase.instantiateScheme q scheme).subst.cap,
      (InferenceBase.instantiateScheme q scheme).subst.target, ?_⟩
    refine
      { capSupport := InferenceBase.instantiateBinders_cap_support q
          scheme.capBinders scheme.tyBinders
        tySupport := InferenceBase.instantiateBinders_ty_support q
          scheme.capBinders scheme.tyBinders
        capBinderVariable := ?_
        result := rfl }
    intro binder binderMem
    exact ⟨⟨q.nextCap + binder.id⟩, by
      simp [InferenceBase.instantiateScheme,
        InferenceBase.instantiateBinders,
        InferenceBase.freshCapSubst, binderMem]⟩

/-- A canonical context-flow certificate is exactly sufficient to construct
the transported runtime variable leaf. -/
theorem Context.CanonicalInstanceFlowAt.runtimeVar
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {post : Subst}
    {source targetContext : Context} {name : String} {scheme : Scheme}
    (flow : Context.CanonicalInstanceFlowAt q post source targetContext)
    (lookup : source.find? name = some scheme) :
    RuntimeTyping signature targetContext (.var name)
      (post.apply (InferenceBase.instantiateScheme q scheme).value) := by
  rcases flow lookup with ⟨targetScheme, targetLookup, instanceTyping⟩
  exact RuntimeTyping.var targetLookup instanceTyping

/-! ## Binder-image-local value-flow transport -/

/--
Transport one explicit expression-scheme instance through an external post.

Unlike `Scheme.ValueFlowInst.transport`, variable-valuedness is required only
for the capability images selected by this instance.  This is the exact
condition recorded by `markSchemeInstance` in an origin derivation.
-/
theorem Scheme.VariableInstAt.transportResult
    {external : Subst} {scheme : Scheme} {target : Ty}
    {C : CapSubst} {T : TySubst}
    (typing : scheme.VariableInstAt C T target)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    (binderImagesVariable : ∀ binder, binder ∈ scheme.capBinders →
      ∀ image, C binder = .var image →
        ∃ finalImage, external.cap image = .var finalImage) :
    scheme.ValueFlowInst (external.apply target) := by
  refine ⟨scheme.postCap external C, scheme.postTarget external T, ?_⟩
  refine
    { capSupport := scheme.postCap_support external C
      tySupport := scheme.postTarget_support external T
      capBinderVariable := ?_
      result := ?_ }
  · intro binder binderMem
    rcases typing.capBinderVariable binder binderMem with
      ⟨image, imageEquation⟩
    rcases binderImagesVariable binder binderMem image imageEquation with
      ⟨finalImage, finalEquation⟩
    exact ⟨finalImage, by
      simp [Scheme.postCap, binderMem, imageEquation, Cap.apply,
        finalEquation]⟩
  · rw [Scheme.post_apply typing.capSupport typing.tySupport
      externalCapFixed externalTargetFixed, typing.result]

/-- Dual-scheme counterpart of `Scheme.VariableInstAt.transportResult`. -/
theorem DualScheme.VariableInstAt.transportResult
    {external : Subst} {scheme : DualScheme}
    {args : List Dual} {result : Dual}
    {C : CapSubst} {T : TySubst}
    (typing : scheme.VariableInstAt C T args result)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      external.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      external.target varId = .var varId)
    (binderImagesVariable : ∀ binder, binder ∈ scheme.capBinders →
      ∀ image, C binder = .var image →
        ∃ finalImage, external.cap image = .var finalImage) :
    scheme.ValueFlowInst (args.map (Dual.applySubst external))
      (result.applySubst external) := by
  refine ⟨scheme.postCap external C, scheme.postTarget external T, ?_⟩
  refine
    { capSupport := scheme.postCap_support external C
      tySupport := scheme.postTarget_support external T
      capBinderVariable := ?_
      argsResult := ?_
      resultResult := ?_ }
  · intro binder binderMem
    rcases typing.capBinderVariable binder binderMem with
      ⟨image, imageEquation⟩
    rcases binderImagesVariable binder binderMem image imageEquation with
      ⟨finalImage, finalEquation⟩
    exact ⟨finalImage, by
      simp [DualScheme.postCap, binderMem, imageEquation, Cap.apply,
        finalEquation]⟩
  · rw [← typing.argsResult, List.map_map]
    apply List.map_congr_left
    intro dual dualMem
    apply DualScheme.post_apply typing.capSupport typing.tySupport
        externalCapFixed externalTargetFixed
    · intro varId membership
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMem, membership⟩)
    · intro varId membership
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨dual, dualMem, membership⟩)
  · rw [← typing.resultResult]
    apply DualScheme.post_apply typing.capSupport typing.tySupport
        externalCapFixed externalTargetFixed
    · intro varId membership
      exact List.mem_append_right _ membership
    · intro varId membership
      exact List.mem_append_right _ membership

/-! ## Canonical DD instances -/

/-- The supply-indexed expression-scheme instance is a declarative
variable-only capability instance, without any terminal-post assumption. -/
def Scheme.instantiateVariableInstAt
    (q : InferenceBase.FreshSupply) (scheme : Scheme) :
    scheme.VariableInstAt
      (InferenceBase.instantiateScheme q scheme).subst.cap
      (InferenceBase.instantiateScheme q scheme).subst.target
      (InferenceBase.instantiateScheme q scheme).value where
  capSupport := InferenceBase.instantiateBinders_cap_support q
    scheme.capBinders scheme.tyBinders
  tySupport := InferenceBase.instantiateBinders_ty_support q
    scheme.capBinders scheme.tyBinders
  capBinderVariable := by
    intro binder binderMem
    exact ⟨⟨q.nextCap + binder.id⟩, by
      simp [InferenceBase.instantiateScheme,
        InferenceBase.instantiateBinders,
        InferenceBase.freshCapSubst, binderMem]⟩
  result := rfl

/-- The supply-indexed dual-scheme instance has the same variable-only
capability boundary. -/
def DualScheme.instantiateVariableInstAt
    (q : InferenceBase.FreshSupply) (scheme : DualScheme) :
    scheme.VariableInstAt
      (InferenceBase.instantiateDualScheme q scheme).subst.cap
      (InferenceBase.instantiateDualScheme q scheme).subst.target
      (InferenceBase.instantiateDualScheme q scheme).value.1
      (InferenceBase.instantiateDualScheme q scheme).value.2 where
  capSupport := InferenceBase.instantiateBinders_cap_support q
    scheme.capBinders scheme.tyBinders
  tySupport := InferenceBase.instantiateBinders_ty_support q
    scheme.capBinders scheme.tyBinders
  capBinderVariable := by
    intro binder binderMem
    exact ⟨⟨q.nextCap + binder.id⟩, by
      simp [InferenceBase.instantiateDualScheme,
        InferenceBase.instantiateBinders,
        InferenceBase.freshCapSubst, binderMem]⟩
  argsResult := rfl
  resultResult := rfl

/-! ## Origin-ledger discharge of the local condition -/

namespace DDErasure.AdmissiblePostBetween

/-- A canonical expression-scheme binder image is variable-valued under every
admissible suffix starting at its post-instantiation cut. -/
theorem schemeInstanceImageVariable
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : Scheme} {post : Subst}
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateScheme q scheme).supply final
      (DDLedger.markSchemeInstance ledger q scheme) finalLedger post)
    {binder : CapVar} (binderMem : binder ∈ scheme.capBinders) :
    ∃ finalImage,
      post.cap ⟨q.nextCap + binder.id⟩ = .var finalImage := by
  let view := SchemeInstanceCapView.ofBinder ledger q scheme binderMem
  have imageBelow : q.nextCap + binder.id <
      (InferenceBase.instantiateScheme q scheme).supply.nextCap := by
    change q.nextCap + binder.id <
      q.nextCap + InferenceBase.binderSpan
        (scheme.capBinders.map CapVar.id)
    exact Nat.add_lt_add_left
      (InferenceBase.mem_lt_binderSpan
        (List.mem_map.mpr ⟨binder, binderMem, rfl⟩)) q.nextCap
  have policy := admissible.cap ⟨q.nextCap + binder.id⟩ imageBelow
  have markedOrigin :
      (DDLedger.markSchemeInstance ledger q scheme).originOf
        ⟨q.nextCap + binder.id⟩ = .renameOnly :=
    view.markedOrigin
  rw [markedOrigin] at policy
  rcases policy with ⟨finalImage, imageEquation, _imageBelow, _imageSafe⟩
  exact ⟨finalImage, imageEquation⟩

/-- Dual-scheme counterpart for pattern-function lookup. -/
theorem dualInstanceImageVariable
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : DualScheme} {post : Subst}
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateDualScheme q scheme).supply final
      (DDLedger.markDualInstance ledger q scheme) finalLedger post)
    {binder : CapVar} (binderMem : binder ∈ scheme.capBinders) :
    ∃ finalImage,
      post.cap ⟨q.nextCap + binder.id⟩ = .var finalImage := by
  have imageBelow : q.nextCap + binder.id <
      (InferenceBase.instantiateDualScheme q scheme).supply.nextCap := by
    change q.nextCap + binder.id <
      q.nextCap + InferenceBase.binderSpan
        (scheme.capBinders.map CapVar.id)
    exact Nat.add_lt_add_left
      (InferenceBase.mem_lt_binderSpan
        (List.mem_map.mpr ⟨binder, binderMem, rfl⟩)) q.nextCap
  have policy := admissible.cap ⟨q.nextCap + binder.id⟩ imageBelow
  have imageMem : ⟨q.nextCap + binder.id⟩ ∈
      Inference.freshCapImages q scheme.capBinders :=
    List.mem_map.mpr ⟨binder, binderMem, rfl⟩
  have markedOrigin :
      (DDLedger.markDualInstance ledger q scheme).originOf
        ⟨q.nextCap + binder.id⟩ = .renameOnly :=
    DDLedger.markDualInstance_origin_of_mem ledger q scheme _ imageMem
  rw [markedOrigin] at policy
  rcases policy with ⟨finalImage, imageEquation, _imageBelow, _imageSafe⟩
  exact ⟨finalImage, imageEquation⟩

end DDErasure.AdmissiblePostBetween

/-! ## Canonical instance transport through an origin-safe suffix -/

/-- Transport the canonical expression-scheme instance when the external
post fixes the scheme's free variables.  Origin admissibility discharges the
only variable-only obligation, binder by binder. -/
theorem Scheme.instantiateValueFlowUnderAdmissible
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : Scheme} {post : Subst}
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateScheme q scheme).supply final
      (DDLedger.markSchemeInstance ledger q scheme) finalLedger post)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      post.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      post.target varId = .var varId) :
    scheme.ValueFlowInst
      (post.apply (InferenceBase.instantiateScheme q scheme).value) := by
  apply (Scheme.instantiateVariableInstAt q scheme).transportResult
      externalCapFixed externalTargetFixed
  intro binder binderMem image imageEquation
  have canonicalEquation :
      (InferenceBase.instantiateScheme q scheme).subst.cap binder =
        .var ⟨q.nextCap + binder.id⟩ := by
    simp [InferenceBase.instantiateScheme,
      InferenceBase.instantiateBinders,
      InferenceBase.freshCapSubst, binderMem]
  have imageEquality : image = ⟨q.nextCap + binder.id⟩ := by
    rw [canonicalEquation] at imageEquation
    exact Cap.var.inj imageEquation.symm
  subst image
  exact admissible.schemeInstanceImageVariable binderMem

/-- Canonical pattern-function instance transport under the corresponding
rename-only origin policy. -/
theorem DualScheme.instantiateValueFlowUnderAdmissible
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : DualScheme} {post : Subst}
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateDualScheme q scheme).supply final
      (DDLedger.markDualInstance ledger q scheme) finalLedger post)
    (externalCapFixed : ∀ varId, varId ∈ scheme.fcv →
      post.cap varId = .var varId)
    (externalTargetFixed : ∀ varId, varId ∈ scheme.ftv →
      post.target varId = .var varId) :
    scheme.ValueFlowInst
      ((InferenceBase.instantiateDualScheme q scheme).value.1.map
        (Dual.applySubst post))
      ((InferenceBase.instantiateDualScheme q scheme).value.2.applySubst
        post) := by
  apply (DualScheme.instantiateVariableInstAt q scheme).transportResult
      externalCapFixed externalTargetFixed
  intro binder binderMem image imageEquation
  have canonicalEquation :
      (InferenceBase.instantiateDualScheme q scheme).subst.cap binder =
        .var ⟨q.nextCap + binder.id⟩ := by
    simp [InferenceBase.instantiateDualScheme,
      InferenceBase.instantiateBinders,
      InferenceBase.freshCapSubst, binderMem]
  have imageEquality : image = ⟨q.nextCap + binder.id⟩ := by
    rw [canonicalEquation] at imageEquation
    exact Cap.var.inj imageEquation.symm
  subst image
  exact admissible.dualInstanceImageVariable binderMem

/-! ## Leaf erasure -/

namespace DDSynthOrigin

/-- Variable lookup erases at its own terminal cut.  The later-parent suffix
is intentionally absent here; transporting the lookup through that suffix
also has to transport the selected capture-avoiding context scheme. -/
theorem runtimeErasure_var_of_instanceFixed
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (name : String) (scheme : Scheme)
    (ledger : CapabilityOriginLedger)
    (lookup : (context.applySubst S).find? name = some scheme)
    (instanceFixed : S.apply
      (InferenceBase.instantiateScheme q scheme).value =
        (InferenceBase.instantiateScheme q scheme).value) :
    RuntimeErasure
      (DDSynthOrigin.var (signature := signature) (q := q)
        (ledger := ledger) lookup) := by
  unfold RuntimeErasure
  rw [instanceFixed]
  exact RuntimeTyping.var lookup
    ⟨_, _, Scheme.instantiateVariableInstAt q scheme⟩

/-- The fixedness cut above follows from the two invariants maintained by a
solved DD traversal: the prevailing substitution is bounded by its current
supply and is in solved (idempotent) form.  Lookup provenance is recovered
algebraically from `Context.applySubst`; no terminal typing premise is used. -/
theorem runtimeErasure_var_of_bounded_idempotent
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (name : String) (scheme : Scheme)
    (ledger : CapabilityOriginLedger)
    (lookup : (context.applySubst S).find? name = some scheme)
    (bounded : S.BoundedBy q) (idem : S.Idempotent) :
    RuntimeErasure
      (DDSynthOrigin.var (signature := signature) (q := q)
        (ledger := ledger) lookup) := by
  rcases Context.find?_applySubst_some_origin S context name scheme lookup with
    ⟨rawScheme, _rawLookup, schemeEquation⟩
  have fixed : S.apply
      (InferenceBase.instantiateScheme q scheme).value =
        (InferenceBase.instantiateScheme q scheme).value := by
    rw [← schemeEquation]
    exact Scheme.instantiate_applySubst_value_fixed rawScheme bounded idem
  exact runtimeErasure_var_of_instanceFixed signature q S context name scheme
    ledger lookup fixed

/-- Transport a canonical variable leaf across one accumulated parent suffix.
The only context-side premise is the algebraic canonical-instance certificate;
the source instance's absorption into `S' = post ∘ S` follows from the same
bounded/solved invariants as local variable erasure. -/
theorem runtimeVar_afterPost_of_canonicalContextFlow
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S post S' : Subst}
    {context targetContext : Context} {name : String} {scheme : Scheme}
    (lookup : (context.applySubst S).find? name = some scheme)
    (bounded : S.BoundedBy q) (idem : S.Idempotent)
    (terminalEquation : S' = Subst.seq post S)
    (contextFlow : Context.CanonicalInstanceFlowAt q post
      (context.applySubst S) targetContext) :
    RuntimeTyping signature targetContext (.var name)
      (S'.apply (InferenceBase.instantiateScheme q scheme).value) := by
  have sourceFixed : S.apply
      (InferenceBase.instantiateScheme q scheme).value =
        (InferenceBase.instantiateScheme q scheme).value := by
    rcases Context.find?_applySubst_some_origin S context name scheme lookup with
      ⟨rawScheme, _rawLookup, schemeEquation⟩
    rw [← schemeEquation]
    exact Scheme.instantiate_applySubst_value_fixed rawScheme bounded idem
  have transported := contextFlow.runtimeVar (signature := signature) lookup
  rw [terminalEquation, Subst.seq_apply, sourceFixed]
  exact transported

end DDSynthOrigin

namespace DDTyping

/-- End-to-end state erasure for a public variable expression.  The public
judgment starts from identity, so boundedness and solved-form are discharged
without any caller premise. -/
theorem var_toRuntimeTyping
    {signature : FrozenSig} {context : Context} {name : String} {target : Ty}
    (typing : DDTyping signature context (.var name) target) :
    RuntimeTyping signature context (.var name) target := by
  rcases typing with
    ⟨rawTarget, q', S', raw, ledger', origin, published⟩
  cases origin with
  | var lookup =>
      have erased := DDSynthOrigin.runtimeErasure_var_of_bounded_idempotent
        signature (Inference.initialSupply signature context) Subst.id
        context name _ [] lookup
        (Subst.boundedBy_id _)
        Subst.id_idempotent
      simpa only [DDSynthOrigin.RuntimeErasure, Context.applySubst_id,
        Subst.apply_id, published] using erased

end DDTyping

end TypePM
