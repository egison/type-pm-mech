import TypePM.DemandTypingErasureTransport

/-!
# Experimental no-capture boundary for scheme substitution

This module isolates the range-hygiene condition under which the current
identifier-based `NamedScheme.applySubst` really composes sequentially.  It is an
experiment rather than a new public DD premise: arbitrary source contexts do
not currently carry this provenance, and the DD solver does not preserve it.
-/

namespace TypePM

/-- Images substituted for a scheme's ambient free variables do not mention
any of that scheme's locally quantified identifiers.  The target-image
capability clause is essential because an ordinary type image may contain
matcher or slot capabilities. -/
structure NamedScheme.NoCapture (scheme : NamedScheme) (S : Subst) : Prop where
  capRange : ∀ ambient, ambient ∈ scheme.fcv →
    ∀ binder, binder ∈ scheme.capBinders → binder ∉ (S.cap ambient).fcv
  targetCapRange : ∀ ambient, ambient ∈ scheme.ftv →
    ∀ binder, binder ∈ scheme.capBinders →
      binder ∉ (S.target ambient).fcv
  targetTyRange : ∀ ambient, ambient ∈ scheme.ftv →
    ∀ binder, binder ∈ scheme.tyBinders →
      binder ∉ (S.target ambient).ftv

/-- Identity introduces no binder occurrence into an ambient image. -/
theorem NamedScheme.NoCapture.id (scheme : NamedScheme) :
    scheme.NoCapture Subst.id := by
  constructor
  · intro ambient ambientFree binder binderMem binderImage
    simp [Subst.id, CapSubst.id, Cap.fcv] at binderImage
    subst binder
    have outside : ambient ∉ scheme.capBinders := by
      simpa using (List.mem_filter.mp ambientFree).2
    exact outside binderMem
  · intro ambient ambientFree binder binderMem binderImage
    simp [Subst.id, TySubst.id, Ty.fcv] at binderImage
  · intro ambient ambientFree binder binderMem binderImage
    simp [Subst.id, TySubst.id, Ty.ftv] at binderImage
    subst binder
    have outside : ambient ∉ scheme.tyBinders := by
      simpa using (List.mem_filter.mp ambientFree).2
    exact outside binderMem

/-- Range hygiene is precisely enough for masking to commute with one
sequential extension.  No restriction on the later substitution's range is
needed: only identifiers already present in the earlier images can be hidden
by the later mask. -/
theorem NamedScheme.applySubst_seq_of_noCapture
    (scheme : NamedScheme) (earlier later : Subst)
    (hygiene : scheme.NoCapture earlier) :
    scheme.applySubst (Subst.seq later earlier) =
      (scheme.applySubst earlier).applySubst later := by
  cases scheme with
  | mk capBinders tyBinders body =>
      change NamedScheme.mk capBinders tyBinders _ =
        NamedScheme.mk capBinders tyBinders _
      congr 1
      change
        (Subst.mk ((Subst.seq later earlier).cap.mask capBinders)
          ((Subst.seq later earlier).target.mask tyBinders)).apply body =
        (Subst.mk (later.cap.mask capBinders)
          (later.target.mask tyBinders)).apply
            ((Subst.mk (earlier.cap.mask capBinders)
              (earlier.target.mask tyBinders)).apply body)
      rw [← Subst.seq_apply]
      apply Subst.apply_eq_of_free_agree
      · intro ambient ambientMem
        by_cases bound : ambient ∈ capBinders
        · simp [Subst.seq, CapSubst.comp, CapSubst.mask, bound, Cap.apply]
        · simp only [Subst.seq, CapSubst.mask, bound, if_false,
            CapSubst.comp]
          apply Cap.apply_eq_of_fcv_agree
          intro image imageMem
          have ambientFree : ambient ∈
              (NamedScheme.mk capBinders tyBinders body).fcv :=
            List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
          have outside : image ∉ capBinders := by
            intro imageBound
            exact hygiene.capRange ambient ambientFree image imageBound imageMem
          simp [CapSubst.mask, outside]
      · intro ambient ambientMem
        by_cases bound : ambient ∈ tyBinders
        · simp [Subst.seq, TySubst.mask, bound, Subst.apply,
            Ty.applyCapability, Ty.applyTarget]
        · simp only [Subst.seq, TySubst.mask, bound, if_false]
          apply Subst.apply_eq_of_free_agree
          · intro image imageMem
            have ambientFree : ambient ∈
                (NamedScheme.mk capBinders tyBinders body).ftv :=
              List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
            have outside : image ∉ capBinders := by
              intro imageBound
              exact hygiene.targetCapRange ambient ambientFree image
                imageBound imageMem
            simp [CapSubst.mask, outside]
          · intro image imageMem
            have ambientFree : ambient ∈
                (NamedScheme.mk capBinders tyBinders body).ftv :=
              List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
            have outside : image ∉ tyBinders := by
              intro imageBound
              exact hygiene.targetTyRange ambient ambientFree image
                imageBound imageMem
            simp [TySubst.mask, outside]

/-! ## Context lifting -/

/-- Every selected context scheme is capture-free under the same prevailing
substitution. -/
def Context.NoCapture (context : Context) (S : Subst) : Prop :=
  ∀ entry, entry ∈ context → entry.2.NoCapture S

theorem Context.NoCapture.id (context : Context) :
    context.NoCapture Subst.id := by
  intro entry membership
  exact NamedScheme.NoCapture.id entry.2

/-- Entry-wise range hygiene restores the sequential substitution law for a
whole polymorphic context. -/
theorem Context.applySubst_seq_of_noCapture
    (context : Context) (earlier later : Subst)
    (hygiene : context.NoCapture earlier) :
    context.applySubst (Subst.seq later earlier) =
      (context.applySubst earlier).applySubst later := by
  induction context with
  | nil => rfl
  | cons entry context induction =>
      change
        (entry.1, entry.2.applySubst (Subst.seq later earlier)) ::
            Context.applySubst (Subst.seq later earlier) context =
          (entry.1, (entry.2.applySubst earlier).applySubst later) ::
            Context.applySubst later (Context.applySubst earlier context)
      congr 1
      · congr 1
        exact NamedScheme.applySubst_seq_of_noCapture entry.2 earlier later
          (hygiene entry (by simp))
      · exact induction (by
        intro tailEntry tailMem
        exact hygiene tailEntry (by simp [tailMem]))

/-! ## Binder-local instance composition -/

/-- Range hygiene allows an arbitrary binder-supported instance to commute
past the external scheme substitution.  This is the body equation needed by
value-flow transport; unlike `NamedScheme.post_apply`, ambient free variables may
change. -/
theorem NamedScheme.post_apply_of_noCapture
    {scheme : NamedScheme} {post : Subst}
    {originalCap : CapSubst} {originalTarget : TySubst}
    (capSupport : originalCap.SupportWithin scheme.capBinders)
    (targetSupport : originalTarget.SupportWithin scheme.tyBinders)
    (hygiene : scheme.NoCapture post) :
    (Subst.mk (scheme.postCap post originalCap)
        (scheme.postTarget post originalTarget)).apply
          (scheme.applySubst post).body =
      post.apply ((Subst.mk originalCap originalTarget).apply scheme.body) := by
  let maskedPost := Subst.mk (post.cap.mask scheme.capBinders)
    (post.target.mask scheme.tyBinders)
  let composed := Subst.mk (scheme.postCap post originalCap)
    (scheme.postTarget post originalTarget)
  change composed.apply (maskedPost.apply scheme.body) =
    post.apply ((Subst.mk originalCap originalTarget).apply scheme.body)
  rw [← Subst.seq_apply, ← Subst.seq_apply]
  apply Subst.apply_eq_of_free_agree
  · intro ambient ambientMem
    by_cases bound : ambient ∈ scheme.capBinders
    · simp [composed, maskedPost, NamedScheme.postCap, Subst.seq,
        CapSubst.comp, CapSubst.mask, bound, Cap.apply]
    · simp only [Subst.seq, CapSubst.comp, composed, maskedPost,
        CapSubst.mask, bound, if_false,
        capSupport ambient bound, Cap.apply]
      apply Cap.apply_eq_self_of_fcv_fixed
      intro image imageMem
      apply NamedScheme.postCap_support post scheme originalCap image
      intro imageBound
      have ambientFree : ambient ∈ scheme.fcv :=
        List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
      exact hygiene.capRange ambient ambientFree image imageBound imageMem
  · intro ambient ambientMem
    by_cases bound : ambient ∈ scheme.tyBinders
    · simp [composed, maskedPost, NamedScheme.postTarget, Subst.seq,
        TySubst.mask, bound, Subst.apply, Ty.applyCapability, Ty.applyTarget]
    · simp only [Subst.seq, composed, maskedPost,
        TySubst.mask, bound, if_false, targetSupport ambient bound,
        Subst.apply, Ty.applyCapability, Ty.applyTarget]
      apply Subst.apply_eq_self_of_free_fixed composed (post.target ambient)
      · intro image imageMem
        apply NamedScheme.postCap_support post scheme originalCap image
        intro imageBound
        have ambientFree : ambient ∈ scheme.ftv :=
          List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
        exact hygiene.targetCapRange ambient ambientFree image imageBound
          imageMem
      · intro image imageMem
        apply NamedScheme.postTarget_support post scheme originalTarget image
        intro imageBound
        have ambientFree : ambient ∈ scheme.ftv :=
          List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
        exact hygiene.targetTyRange ambient ambientFree image imageBound
          imageMem

/-- The binder-local substitution used to replay one canonical instance
through a later post. -/
def NamedScheme.canonicalPostSubst
    (q : InferenceBase.FreshSupply) (scheme : NamedScheme) (post : Subst) : Subst :=
  Subst.mk
    (scheme.postCap post
      (InferenceBase.instantiateScheme q scheme).subst.cap)
    (scheme.postTarget post
      (InferenceBase.instantiateScheme q scheme).subst.target)

@[simp] theorem NamedScheme.canonicalPostSubst_cap_binder
    {q : InferenceBase.FreshSupply} {scheme : NamedScheme} {post : Subst}
    {binder : CapVar} (binderMem : binder ∈ scheme.capBinders) :
    (scheme.canonicalPostSubst q post).cap binder =
      ((InferenceBase.instantiateScheme q scheme).subst.cap binder).apply
        post.cap := by
  simp [NamedScheme.canonicalPostSubst, NamedScheme.postCap, binderMem]

/-- `NoCapture` supplies every field of the ordinary instantiation-
composition certificate except its legacy `RangeFixed` field. -/
def NamedScheme.instantiateCompositionAt_of_noCapture
    {q : InferenceBase.FreshSupply} {scheme : NamedScheme} {post : Subst}
    (hygiene : scheme.NoCapture post)
    (rangeFixed : (scheme.canonicalPostSubst q post).RangeFixed) :
    scheme.InstCompositionAt post
      (InferenceBase.instantiateScheme q scheme).subst.cap
      (InferenceBase.instantiateScheme q scheme).subst.target where
  composedCap := (scheme.canonicalPostSubst q post).cap
  composedTarget := (scheme.canonicalPostSubst q post).target
  capSupport := scheme.postCap_support post _
  targetSupport := scheme.postTarget_support post _
  rangeFixed := rangeFixed
  bodyEquation := by
    exact NamedScheme.post_apply_of_noCapture
      (InferenceBase.instantiateBinders_cap_support q
        scheme.capBinders scheme.tyBinders)
      (InferenceBase.instantiateBinders_ty_support q
        scheme.capBinders scheme.tyBinders)
      hygiene

/-- Future range hygiene and the exact marked-ledger suffix are sufficient
for canonical value-flow transport.  `RangeFixed` is absent because
`ValueFlowInst` intentionally does not require it. -/
theorem NamedScheme.instantiateAppliedValueFlowUnderNoCapture
    {ledger finalLedger : CapabilityOriginLedger}
    {q final : InferenceBase.FreshSupply} {scheme : NamedScheme} {post : Subst}
    (hygiene : scheme.NoCapture post)
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateScheme q scheme).supply final
      (DDLedger.markSchemeInstance ledger q scheme) finalLedger post) :
    (scheme.applySubst post).ValueFlowInst
      (post.apply (InferenceBase.instantiateScheme q scheme).value) := by
  refine ⟨(scheme.canonicalPostSubst q post).cap,
    (scheme.canonicalPostSubst q post).target, ?_⟩
  refine
    { capSupport := scheme.postCap_support post _
      tySupport := scheme.postTarget_support post _
      capBinderVariable := ?_
      result := ?_ }
  · intro binder binderMem
    have binderMem' : binder ∈ scheme.capBinders := by simpa using binderMem
    rcases admissible.schemeInstanceImageVariable binderMem' with
      ⟨finalImage, finalEquation⟩
    refine ⟨finalImage, ?_⟩
    rw [NamedScheme.canonicalPostSubst_cap_binder
      (q := q) (scheme := scheme) (post := post) binderMem']
    simp [InferenceBase.instantiateScheme,
      InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
      binderMem', Cap.apply, finalEquation]
  · exact NamedScheme.post_apply_of_noCapture
      (InferenceBase.instantiateBinders_cap_support q
        scheme.capBinders scheme.tyBinders)
      (InferenceBase.instantiateBinders_ty_support q
        scheme.capBinders scheme.tyBinders)
      hygiene

/-- The variable-leaf residuals reduce to capture hygiene at the two relevant
cuts: the raw scheme under the prevailing substitution, and the selected
source scheme under the future suffix. -/
theorem DDSynthOrigin.runtimeVar_afterPost_of_noCapture
    {signature : FrozenSig} {q final : InferenceBase.FreshSupply}
    {S post S' : Subst} {context : Context} {name : String}
    {rawScheme scheme : NamedScheme}
    {ledger finalLedger : CapabilityOriginLedger}
    (rawLookup : context.find? name = some rawScheme)
    (sourceSchemeEquation : rawScheme.applySubst S = scheme)
    (sourceHygiene : rawScheme.NoCapture S)
    (futureHygiene : scheme.NoCapture post)
    (bounded : S.BoundedBy q) (idem : S.Idempotent)
    (terminalEquation : S' = Subst.seq post S)
    (admissible : DDErasure.AdmissiblePostBetween
      (InferenceBase.instantiateScheme q scheme).supply final
      (DDLedger.markSchemeInstance ledger q scheme) finalLedger post) :
    RuntimeTyping signature (context.applySubst S') (.var name)
      (S'.apply (InferenceBase.instantiateScheme q scheme).value) := by
  subst S'
  have terminalSchemeEquation :
      rawScheme.applySubst (Subst.seq post S) = scheme.applySubst post := by
    rw [NamedScheme.applySubst_seq_of_noCapture rawScheme S post sourceHygiene,
      sourceSchemeEquation]
  have terminalLookup :
      (context.applySubst (Subst.seq post S)).find? name =
        some (scheme.applySubst post) := by
    rw [Context.find?_applySubst, rawLookup]
    simpa using congrArg some terminalSchemeEquation
  have instanceTyping := NamedScheme.instantiateAppliedValueFlowUnderNoCapture
    futureHygiene admissible
  have sourceFixed : S.apply
      (InferenceBase.instantiateScheme q scheme).value =
        (InferenceBase.instantiateScheme q scheme).value := by
    rw [← sourceSchemeEquation]
    exact NamedScheme.instantiate_applySubst_value_fixed rawScheme bounded idem
  have transported : RuntimeTyping signature
      (context.applySubst (Subst.seq post S)) (.var name)
      (post.apply (InferenceBase.instantiateScheme q scheme).value) :=
    RuntimeTyping.var terminalLookup instanceTyping
  rw [Subst.seq_apply, sourceFixed]
  exact transported

end TypePM
