import TypePM.DamasMilnerWApp

/-!
# Lambda and direct-self recursion boundaries for Damas--Milner W

This module isolates the fresh monomorphic binders used by `lam` and the
ordinary direct-self `fix` form.  Both helpers install the selected one-sort
types only in the shared residual, protect the body context, and leave the
executable traversal's prevailing substitution untouched until the final
ordinary body/codomain cut.
-/

namespace TypePM
namespace DM

/-! ## Lambda bodies -/

/-- Allocate the fresh lambda domain in the residual and protect the body
context.  Older frames and type equations remain available to the recursive
body traversal. -/
theorem WProtectedFrameAt.prepareLamBody
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {rawContext : Context} {selectedContext : SCtx}
    {name : String}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (outer : WContextRel post
      (rawContext.applySubst prevailing) selectedContext)
    (outerBounded : (rawContext.applySubst prevailing).BoundedBy supply)
    (prevailingBounded : prevailing.BoundedBy supply)
    (domain : STy) :
    WProtectedFrameAt { supply with nextTy := supply.nextTy + 1 }
      (DM.extendFreshTarget post supply.nextTy domain) prevailing
      ((((name, Scheme.mono (.var supply.nextTy)) :: rawContext,
          (name, SScheme.mono domain) :: selectedContext)) :: frames)
      ((.var supply.nextTy, domain) :: frontier) := by
  let successor : InferenceBase.FreshSupply :=
    { supply with nextTy := supply.nextTy + 1 }
  have extended := frame.extendFreshTarget domain
  have outerExtended : WContextRel
      (DM.extendFreshTarget post supply.nextTy domain)
      (rawContext.applySubst prevailing) selectedContext :=
    WContextRel.extendFreshTarget domain outer outerBounded
  have freshFixed : prevailing.apply (.var supply.nextTy) =
      .var supply.nextTy :=
    Subst.BoundedBy.apply_freshTarget prevailingBounded
  have domainEquation :
      (DM.extendFreshTarget post supply.nextTy domain).apply
          (prevailing.apply (.var supply.nextTy)) = domain.emb := by
    rw [freshFixed]
    exact DM.extendFreshTarget_at post supply.nextTy domain
  have bodyRelated : WContextRel
      (DM.extendFreshTarget post supply.nextTy domain)
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext))
      ((name, SScheme.mono domain) :: selectedContext) := by
    simp only [Context.applySubst, List.map_cons,
      Scheme.applyMeta_mono, freshFixed]
    exact WContextRel.cons (name := name) rfl
      (SScheme.mono_realizedBy
        (DM.extendFreshTarget_at post supply.nextTy domain)) outerExtended
  have bodyBounded :
      (Context.applySubst prevailing
        ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)).BoundedBy
        successor := by
    simpa only [Context.applySubst, List.map_cons,
      Scheme.applyMeta_mono, freshFixed] using
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono
          (Ty.BoundedBy.varOf (Nat.lt_succ_self supply.nextTy)))
        (outerBounded.mono (SupplyExtends.bumpTy supply 1)))
  exact extended.protect bodyRelated bodyBounded

/-- Forget the innermost protected context after a binder body has finished.
Every older context remains protected with exactly the same residual and
prevailing substitution. -/
theorem WProtectedFrameAt.dropContextHead
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {rawContext : Context} {selectedContext : SCtx}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply post prevailing
      ((rawContext, selectedContext) :: frames) frontier) :
    WProtectedFrameAt supply post prevailing frames frontier := by
  refine
    { contexts := ?_
      types := frame.types
      contextsBounded := ?_
      frontierBounded := frame.frontierBounded }
  · intro raw selected membership
    exact frame.contexts (List.mem_cons_of_mem _ membership)
  · intro raw selected membership
    exact frame.contextsBounded (List.mem_cons_of_mem _ membership)

/-- Collapse the protected body/domain equations to the function equation
required when returning from a lambda body.  The two temporary frontier
entries are discarded; all older entries are preserved. -/
theorem WProtectedFrameAt.finishLamTarget
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {bodyRaw domainRaw : Ty} {codomain domain : STy}
    (frame : WProtectedFrameAt supply post prevailing frames
      ((bodyRaw, codomain) :: (domainRaw, domain) :: frontier)) :
    WProtectedFrameAt supply post prevailing frames
      ((.fn domainRaw bodyRaw, .fn domain codomain) :: frontier) := by
  have bodyEquation : post.apply bodyRaw = codomain.emb :=
    frame.types (by simp)
  have domainEquation : post.apply domainRaw = domain.emb :=
    frame.types (by simp)
  refine
    { contexts := frame.contexts
      types := ?_
      contextsBounded := frame.contextsBounded
      frontierBounded := ?_ }
  · apply WTypeFrame.cons
    · simp only [Subst.apply_fn, bodyEquation, domainEquation, STy.emb]
    · intro algorithm selected membership
      exact frame.types (by simp [membership])
  · intro pair membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact Ty.BoundedBy.fnOf
        (frame.frontierBounded (domainRaw, domain) (by simp))
        (frame.frontierBounded (bodyRaw, codomain) (by simp))
    · exact frame.frontierBounded pair (by simp [membership])

/-- Certified lambda composition at the exact boundary consumed by the
mutual W theorem.  The recursive result protects its body context and the
body/domain equations; returning from the binder removes that local context,
collapses the temporary frontier pairs to the lambda result, and wraps the
origin and terminal-audit trees. -/
theorem w_lam_certified_complete
    {terminal : Subst} {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {initial prevailing' post : Subst}
    {rawContext bodyContext : Context} {selectedBodyContext : SCtx}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {name : String} {body : Expr} {bodyRaw : Ty}
    {domain codomain : STy}
    {bodyRun : DemandSynth signature
      { supply with nextTy := supply.nextTy + 1 } initial
      ((name, Scheme.mono (.var supply.nextTy)) :: rawContext)
      body bodyRaw successor prevailing'}
    (bodyOrigin : DemandSynthOrigin signature bodyRun [] [])
    (bodyAudit : Nonempty
      (DemandSynthTerminalAudit terminal signature bodyOrigin))
    (frame : WProtectedFrameAt successor post prevailing'
      ((bodyContext, selectedBodyContext) :: frames)
      ((prevailing'.apply bodyRaw, codomain) ::
        (prevailing'.apply (.var supply.nextTy), domain) :: frontier)) :
    ∃ (derived : DemandSynth signature supply initial rawContext
          (.lam name body) (.fn (.var supply.nextTy) bodyRaw)
          successor prevailing')
        (origin : DemandSynthOrigin signature derived [] []),
      Nonempty (DemandSynthTerminalAudit terminal signature origin) ∧
      WProtectedFrameAt successor post prevailing' frames
        ((prevailing'.apply (.fn (.var supply.nextTy) bodyRaw),
            .fn domain codomain) :: frontier) := by
  rcases bodyAudit with ⟨bodyAudit⟩
  let derived : DemandSynth signature supply initial rawContext
      (.lam name body) (.fn (.var supply.nextTy) bodyRaw)
      successor prevailing' := DemandSynth.lam bodyRun
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.lam bodyOrigin
  have collapsed := frame.dropContextHead.finishLamTarget
  simpa only [Subst.apply_fn] using
    ⟨derived, origin, ⟨DemandSynthTerminalAudit.lam bodyAudit⟩, collapsed⟩

/-! ## Direct-self fix bodies -/

/-- Extending at the fresh recursive domain/codomain pair preserves an
arbitrary outer context relation bounded by the incoming supply. -/
theorem WContextRel.extendFixTargets
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {rawContext : Context} {selectedContext : SCtx}
    (domain codomain : STy)
    (outer : WContextRel base rawContext selectedContext)
    (bounded : rawContext.BoundedBy supply) :
    WContextRel (DM.extendAppTargets base supply domain codomain)
      rawContext selectedContext := by
  intro name selectedScheme found
  obtain ⟨generalScheme, generalFound, capArity, realizes⟩ := outer found
  refine ⟨generalScheme, generalFound, capArity, ?_⟩
  intro target instantiation
  rw [Scheme.applyMeta_extendAppTargets_eq base supply domain codomain
    (bounded.find? generalFound)]
  exact realizes instantiation

/-- Install the selected recursive function's domain and codomain in the
residual and protect the exact two-binder body context used by
`DemandSynth.fix`. -/
theorem WProtectedFrameAt.prepareFixBody
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {rawContext : Context} {selectedContext : SCtx}
    {self argument : String}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (outer : WContextRel post
      (rawContext.applySubst prevailing) selectedContext)
    (outerBounded : (rawContext.applySubst prevailing).BoundedBy supply)
    (prevailingBounded : prevailing.BoundedBy supply)
    (domain codomain : STy) :
    WProtectedFrameAt { supply with nextTy := supply.nextTy + 2 }
      (DM.extendAppTargets post supply domain codomain) prevailing
      (((
        (argument, Scheme.mono (.var supply.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
          rawContext,
        (argument, SScheme.mono domain) ::
          (self, SScheme.mono (.fn domain codomain)) :: selectedContext)) ::
        frames)
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) := by
  let successor : InferenceBase.FreshSupply :=
    { supply with nextTy := supply.nextTy + 2 }
  have extended := frame.protectAppTargets domain codomain
  have outerExtended : WContextRel
      (DM.extendAppTargets post supply domain codomain)
      (rawContext.applySubst prevailing) selectedContext :=
    WContextRel.extendFixTargets domain codomain outer outerBounded
  have domainFixed : prevailing.apply (.var supply.nextTy) =
      .var supply.nextTy :=
    Subst.BoundedBy.apply_freshTarget prevailingBounded
  have codomainFixed : prevailing.apply (.var (supply.nextTy + 1)) =
      .var (supply.nextTy + 1) :=
    Subst.BoundedBy.apply_targetAbove prevailingBounded (Nat.le_succ _)
  have domainEquation :
      (DM.extendAppTargets post supply domain codomain).apply
          (prevailing.apply (.var supply.nextTy)) = domain.emb := by
    rw [domainFixed]
    exact DM.extendAppTargets_apply_domain post supply domain codomain
  have functionEquation :
      (DM.extendAppTargets post supply domain codomain).apply
          (prevailing.apply
            (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) =
        (STy.fn domain codomain).emb := by
    rw [Subst.apply_fn, domainFixed, codomainFixed]
    simp [Subst.apply_fn, STy.emb]
  have rawFunctionEquation :
      (DM.extendAppTargets post supply domain codomain).apply
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1))) =
        (STy.fn domain codomain).emb := by
    simp [Subst.apply_fn, STy.emb]
  have bodyRelated : WContextRel
      (DM.extendAppTargets post supply domain codomain)
      (Context.applySubst prevailing
        ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext))
      ((argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: selectedContext) := by
    simp only [Context.applySubst, List.map_cons, Scheme.applyMeta_mono,
      Subst.apply_fn, domainFixed, codomainFixed]
    exact WContextRel.cons (name := argument) rfl
      (SScheme.mono_realizedBy
        (DM.extendAppTargets_apply_domain post supply domain codomain))
      (WContextRel.cons (name := self) rfl
        (SScheme.mono_realizedBy rawFunctionEquation) outerExtended)
  have bodyBounded :
      (Context.applySubst prevailing
        ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext)).BoundedBy successor := by
    simpa only [Context.applySubst, List.map_cons, Scheme.applyMeta_mono,
      Subst.apply_fn, domainFixed, codomainFixed] using
      (Context.BoundedBy.cons
        (Scheme.BoundedBy.ofMono
          (Ty.BoundedBy.varOf (by simp)))
        (Context.BoundedBy.cons
          (Scheme.BoundedBy.ofMono
            (Ty.BoundedBy.fnOf
              (Ty.BoundedBy.varOf (by simp))
              (Ty.BoundedBy.varOf (by simp))))
          (outerBounded.mono (SupplyExtends.bumpTy supply 2))))
  exact extended.protect bodyRelated bodyBounded

/-! ## The terminal fix cut -/

/-- Factor the body/codomain equality through the executable ordinary cut
and package the raw direct-self synthesis constructor. -/
theorem w_finishFix
    {signature : FrozenSig}
    {supply bodySupply : InferenceBase.FreshSupply}
    {initial prevailing : Subst} {post : Subst}
    {rawContext : Context} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)}
    {self argument : String} {body : Expr} {bodyRaw : Ty}
    {_domain codomain : STy}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (bodyRun : DemandSynth signature
      { supply with nextTy := supply.nextTy + 2 } initial
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext)
      body bodyRaw bodySupply prevailing)
    (frame : WProtectedFrameAt bodySupply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (bodyBounded : (prevailing.apply bodyRaw).BoundedBy bodySupply)
    (codomainBounded :
      (prevailing.apply (.var (supply.nextTy + 1))).BoundedBy bodySupply)
    (bodyEquation :
      post.apply (prevailing.apply bodyRaw) = codomain.emb)
    (codomainEquation :
      post.apply (prevailing.apply (.var (supply.nextTy + 1))) =
        codomain.emb) :
    ∃ delta residual : Subst,
      OriginSafeExactPairedMGU []
        (prevailing.apply bodyRaw)
        (prevailing.apply (.var (supply.nextTy + 1))) delta ∧
      AdmissiblePost [] residual ∧
      post = Subst.seq residual delta ∧
      DemandSynth signature supply initial rawContext
        (.fix self argument body)
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
        bodySupply (Subst.seq delta prevailing) ∧
      WProtectedFrameAt bodySupply residual
        (Subst.seq delta prevailing) frames
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  have ordinaryClass : alignPairClass
      (prevailing.apply bodyRaw)
      (prevailing.apply (.var (supply.nextTy + 1))) = .ordinary :=
    alignPairClass_ordinary_of_realized_emb bodyEquation codomainEquation
  obtain ⟨delta, residual, cut, residualAdmissible, factor, aligned,
      moved⟩ :=
    w_factorOrdinaryCut frame postAdmissible bodyBounded codomainBounded
      bodyEquation codomainEquation ordinaryClass
  exact ⟨delta, residual, cut, residualAdmissible, factor,
    DemandSynth.fix distinct direct nonMatcher bodyRun aligned, moved⟩

/-- The same structural finalizer with the empty-ledger origin certificate
and recursive terminal audit packaged alongside the raw run. -/
theorem w_finishFix_certified
    {terminal : Subst} {signature : FrozenSig}
    {supply bodySupply : InferenceBase.FreshSupply}
    {initial prevailing : Subst} {post : Subst}
    {rawContext : Context} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)}
    {self argument : String} {body : Expr} {bodyRaw : Ty}
    {_domain codomain : STy}
    {bodyRun : DemandSynth signature
      { supply with nextTy := supply.nextTy + 2 } initial
      ((argument, Scheme.mono (.var supply.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))) ::
        rawContext)
      body bodyRaw bodySupply prevailing}
    {bodyOrigin : DemandSynthOrigin signature bodyRun [] []}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (frame : WProtectedFrameAt bodySupply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (bodyBounded : (prevailing.apply bodyRaw).BoundedBy bodySupply)
    (codomainBounded :
      (prevailing.apply (.var (supply.nextTy + 1))).BoundedBy bodySupply)
    (bodyEquation :
      post.apply (prevailing.apply bodyRaw) = codomain.emb)
    (codomainEquation :
      post.apply (prevailing.apply (.var (supply.nextTy + 1))) =
        codomain.emb) :
    ∃ (delta residual : Subst)
        (derived : DemandSynth signature supply initial rawContext
          (.fix self argument body)
          (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
          bodySupply (Subst.seq delta prevailing))
        (origin : DemandSynthOrigin signature derived [] []),
      Nonempty (DemandSynthTerminalAudit terminal signature origin) ∧
      OriginSafeExactPairedMGU []
        (prevailing.apply bodyRaw)
        (prevailing.apply (.var (supply.nextTy + 1))) delta ∧
      AdmissiblePost [] residual ∧
      post = Subst.seq residual delta ∧
      WProtectedFrameAt bodySupply residual
        (Subst.seq delta prevailing) frames
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  have ordinaryClass : alignPairClass
      (prevailing.apply bodyRaw)
      (prevailing.apply (.var (supply.nextTy + 1))) = .ordinary :=
    alignPairClass_ordinary_of_realized_emb bodyEquation codomainEquation
  obtain ⟨delta, residual, cut, residualAdmissible, factor, aligned,
      moved⟩ :=
    w_factorOrdinaryCut frame postAdmissible bodyBounded codomainBounded
      bodyEquation codomainEquation ordinaryClass
  let alignedOrigin : DemandAlignTypesWithLedger [] prevailing bodyRaw
      (.var (supply.nextTy + 1)) (Subst.seq delta prevailing) :=
    DemandAlignTypesWithLedger.ordinary ordinaryClass cut
  let derived : DemandSynth signature supply initial rawContext
      (.fix self argument body)
      (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
      bodySupply (Subst.seq delta prevailing) :=
    DemandSynth.fix distinct direct nonMatcher bodyRun aligned
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin alignedOrigin
  have audit : DemandSynthTerminalAudit terminal signature origin := by
    exact DemandSynthTerminalAudit.fix (distinct := distinct)
      (direct := direct) (nonMatcher := nonMatcher)
      (aligned := alignedOrigin) bodyAudit
  exact ⟨delta, residual, derived, origin,
    ⟨audit⟩,
    cut, residualAdmissible, factor, moved⟩

end DM
end TypePM
