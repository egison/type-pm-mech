import TypePM.DemandTypingErasureCore
import TypePM.PolyInstantiationTransport
import TypePM.SourceSubstitution

/-!
# Residual-post transport for demand-typing erasure

Expression schemes use finite, capture-free openings.  Their transport laws
live in `PolyInstantiationTransport`; no binder-masked solver substitution or
`NoCapture` side condition is required here.

Pattern-function schemes still use the source calculus's named declaration
format.  This module retains only the two local facts needed by user-pattern
erasure: transport of a variable-valued instance and the canonical
supply-indexed witness for such an instance.
-/

namespace TypePM

/-- Transport one variable-valued dual-scheme instance through a later
substitution.  Only the capability images selected for quantified binders must
remain variables; ordinary target images may specialize structurally. -/
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

/-- The canonical supply-indexed dual-scheme instance maps every quantified
capability binder to its freshly allocated capability variable. -/
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

namespace DDErasure.AdmissiblePostBetween

/-- A canonical expression-scheme capability image remains variable-valued
across an origin-admissible suffix from its post-instantiation cut. -/
theorem schemeInstanceImageVariable
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : Scheme} {post : Subst}
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateScheme q scheme).supply final
      (DDLedger.markSchemeInstance ledger q scheme) finalLedger post)
    (index : Fin scheme.capArity) :
    ∃ finalImage,
      post.cap ((Scheme.canonicalFreshOpening q scheme).capImage index) =
        .var finalImage := by
  let image := (Scheme.canonicalFreshOpening q scheme).capImage index
  have imageMem : image ∈ Scheme.canonicalCapImages q scheme := by
    rw [Scheme.canonicalCapImages, Scheme.FreshOpening.capImages,
      List.mem_ofFn]
    exact ⟨index, rfl⟩
  have imageBelow : image.id <
      (InferenceBase.instantiateScheme q scheme).supply.nextCap :=
    (Scheme.mem_canonicalCapImages_bounds imageMem).2
  have policy := admissible.cap image imageBelow
  have markedOrigin :
      (DDLedger.markSchemeInstance ledger q scheme).originOf image =
        .renameOnly :=
    DDLedger.markSchemeInstance_origin_of_mem ledger q scheme image imageMem
  rw [markedOrigin] at policy
  rcases policy with ⟨finalImage, imageEquation, _imageBelow, _imageSafe⟩
  exact ⟨finalImage, imageEquation⟩

/-- A canonical pattern-function binder remains variable-valued across an
origin-admissible suffix from its post-instantiation cut. -/
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

end TypePM
