import TypePM.DamasMilnerW

/-!
# Application cuts for Damas--Milner Algorithm W completeness

This module isolates the algebra shared by the two ordinary cuts in the
application constructor.  A shared W residual which realizes both normalized
algorithm types as the same simple type is an admissible solver competitor.
Exact paired-unification completeness then supplies the executable cut and a
new residual, while the protected contexts and frontier are transported in
one step.
-/

namespace TypePM
namespace DM

/-! ## The fresh application domain/codomain pair -/

/-- Extend only the two target variables allocated by the application
constructor.  The incoming W residual is left unchanged below the current
supply. -/
def extendAppTargets (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) : Subst :=
  { cap := base.cap
    target := fun name =>
      if name = supply.nextTy then domain.emb
      else if name = supply.nextTy + 1 then codomain.emb
      else base.target name }

@[simp] theorem extendAppTargets_cap
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    (extendAppTargets base supply domain codomain).cap = base.cap := rfl

theorem extendAppTargets_target_below
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) {name : TypePM.TyVar}
    (below : name < supply.nextTy) :
    (extendAppTargets base supply domain codomain).target name =
      base.target name := by
  simp [extendAppTargets, Nat.ne_of_lt below,
    Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_succ_self _))]

theorem extendAppTargets_apply_eq
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) {target : Ty}
    (bounded : target.BoundedBy supply) :
    (extendAppTargets base supply domain codomain).apply target =
      base.apply target := by
  apply Subst.apply_eq_of_free_agree
  · intro varId _membership
    rfl
  · intro name membership
    exact extendAppTargets_target_below base supply domain codomain
      (bounded.targets name membership)

@[simp] theorem extendAppTargets_apply_domain
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    (extendAppTargets base supply domain codomain).apply
        (.var supply.nextTy) = domain.emb := by
  simp [extendAppTargets, Subst.apply, Ty.applyCapability, Ty.applyTarget]

@[simp] theorem extendAppTargets_apply_codomain
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    (extendAppTargets base supply domain codomain).apply
        (.var (supply.nextTy + 1)) = codomain.emb := by
  simp [extendAppTargets, Subst.apply, Ty.applyCapability, Ty.applyTarget]

theorem Scheme.applyMeta_extendAppTargets_eq
    (base : Subst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) {scheme : Scheme}
    (bounded : scheme.BoundedBy supply) :
    scheme.applyMeta (extendAppTargets base supply domain codomain) =
      scheme.applyMeta base := by
  apply Scheme.applyMeta_eq_of_free_agree
  · intro varId _membership
    rfl
  · intro name membership
    exact extendAppTargets_target_below base supply domain codomain
      (bounded.targets name membership)

/-- Installing the selected application domain and codomain at the two fresh
variables preserves every older protected context and type equation. -/
theorem WProtectedFrameAt.extendAppTargets
    {supply : InferenceBase.FreshSupply} {base prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply base prevailing frames frontier)
    (domain codomain : STy) :
    WProtectedFrameAt { supply with nextTy := supply.nextTy + 2 }
      (DM.extendAppTargets base supply domain codomain) prevailing
      frames frontier := by
  let extended := DM.extendAppTargets base supply domain codomain
  have supplyExtends : SupplyExtends supply
      { supply with nextTy := supply.nextTy + 2 } :=
    SupplyExtends.bumpTy supply 2
  refine
    { contexts := ?_
      types := ?_
      contextsBounded := fun membership =>
        (frame.contextsBounded membership).mono supplyExtends
      frontierBounded := fun pair membership =>
        (frame.frontierBounded pair membership).mono supplyExtends }
  · intro rawContext selectedContext membership
    intro name selectedScheme found
    obtain ⟨generalScheme, generalFound, capArity, realizes⟩ :=
      frame.contexts membership found
    refine ⟨generalScheme, generalFound, capArity, ?_⟩
    intro target instantiation
    rw [Scheme.applyMeta_extendAppTargets_eq base supply domain codomain
      ((frame.contextsBounded membership).find? generalFound)]
    exact realizes instantiation
  · intro algorithm selected membership
    rw [extendAppTargets_apply_eq base supply domain codomain
      (frame.frontierBounded (algorithm, selected) membership)]
    exact frame.types membership

/-- Add the two fresh application variables to the protected frontier. -/
theorem WProtectedFrameAt.protectAppTargets
    {supply : InferenceBase.FreshSupply} {base prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply base prevailing frames frontier)
    (domain codomain : STy) :
    WProtectedFrameAt { supply with nextTy := supply.nextTy + 2 }
      (DM.extendAppTargets base supply domain codomain) prevailing frames
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) := by
  have extended := frame.extendAppTargets domain codomain
  refine
    { contexts := extended.contexts
      types := WTypeFrame.cons
        (extendAppTargets_apply_domain base supply domain codomain)
        (WTypeFrame.cons
          (extendAppTargets_apply_codomain base supply domain codomain)
          extended.types)
      contextsBounded := extended.contextsBounded
      frontierBounded := ?_ }
  intro pair membership
  rcases List.mem_cons.mp membership with rfl | membership
  · apply Ty.BoundedBy.varOf
    show supply.nextTy < supply.nextTy + 2
    omega
  rcases List.mem_cons.mp membership with rfl | membership
  · apply Ty.BoundedBy.varOf
    show supply.nextTy + 1 < supply.nextTy + 2
    omega
  · exact extended.frontierBounded pair membership

theorem AdmissiblePost.extendAppTargets
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {domain codomain : STy}
    (admissible : AdmissiblePost [] base) :
    AdmissiblePost [] (DM.extendAppTargets base supply domain codomain) := by
  exact ⟨admissible.cap⟩

theorem Subst.BoundedBy.apply_freshTarget
    {supply : InferenceBase.FreshSupply} {subst : Subst}
    (bounded : subst.BoundedBy supply) :
    subst.apply (.var supply.nextTy) = .var supply.nextTy := by
  simp [Subst.apply, Ty.applyCapability, Ty.applyTarget,
    bounded.targetFixedAbove supply.nextTy (Nat.le_refl _)]

theorem Subst.BoundedBy.apply_targetAbove
    {supply : InferenceBase.FreshSupply} {subst : Subst}
    (bounded : subst.BoundedBy supply) {name : TypePM.TyVar}
    (above : supply.nextTy ≤ name) :
    subst.apply (.var name) = .var name := by
  simp [Subst.apply, Ty.applyCapability, Ty.applyTarget,
    bounded.targetFixedAbove name above]

/-- Any two embedded simple types whose heads are not both annotated matcher
forms use the ordinary paired-unification branch.  In particular, the
function and domain cuts of the DM application fragment satisfy this premise
definitionally. -/
theorem alignPairClass_emb_fn
    (domain codomain : STy) (other : Ty) :
    alignPairClass (.fn domain.emb codomain.emb) other = .ordinary := by
  cases other <;> rfl

theorem alignPairClass_emb_left
    (left : STy) {right : Ty}
    (rightPlain : (match right with
      | .matcher _ _ | .slot _ _ => False
      | _ => True)) :
    alignPairClass left.emb right = .ordinary := by
  cases left <;> cases right <;> simp_all [STy.emb, alignPairClass]

/-- A residual cannot erase a matcher/slot head.  Consequently, if both
normalized sides realize the same capability-inert simple type, neither the
annotated paired branch nor a coercion-demand branch can be selected. -/
theorem alignPairClass_ordinary_of_realized_emb
    {post : Subst} {left right : Ty} {selected : STy}
    (leftEquation : post.apply left = selected.emb)
    (rightEquation : post.apply right = selected.emb) :
    alignPairClass left right = .ordinary := by
  cases left <;> cases right <;> cases selected <;>
    simp_all [Subst.apply, Ty.applyCapability, Ty.applyTarget, STy.emb,
      alignPairClass]

theorem demandClass_ordinary_of_expected_realized_emb
    {post : Subst} {raw expected : Ty} {selected : STy}
    (expectedEquation : post.apply expected = selected.emb) :
    demandClass raw expected = .ordinary := by
  cases raw <;> cases expected <;> cases selected <;>
    simp_all [Subst.apply, Ty.applyCapability, Ty.applyTarget, STy.emb,
      demandClass]

/-- Factor one ordinary application cut through the exact executable solver
and transport every protected W equation to the solver output.

The two equation premises are deliberately stated on the normalized views
`prevailing.apply left/right`: recursive W results protect exactly those
views, and `WProtectedFrameAt.applySubst` then changes the prevailing state to
`Subst.seq delta prevailing` without losing any older equation. -/
theorem w_factorOrdinaryCut
    {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {left right : Ty} {selected : STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (leftBounded : (prevailing.apply left).BoundedBy supply)
    (rightBounded : (prevailing.apply right).BoundedBy supply)
    (leftEquation : post.apply (prevailing.apply left) = selected.emb)
    (rightEquation : post.apply (prevailing.apply right) = selected.emb)
    (ordinaryClass : alignPairClass
      (prevailing.apply left) (prevailing.apply right) = .ordinary) :
    ∃ delta residual : Subst,
      OriginSafeExactPairedMGU []
        (prevailing.apply left) (prevailing.apply right) delta ∧
      AdmissiblePost [] residual ∧
      post = Subst.seq residual delta ∧
      DemandAlignTypes prevailing left right
        (Subst.seq delta prevailing) ∧
      WProtectedFrameAt supply residual (Subst.seq delta prevailing) frames
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  have competitorSound :
      post.apply (prevailing.apply left) =
        post.apply (prevailing.apply right) := by
    rw [leftEquation, rightEquation]
  obtain ⟨delta, residual, cut, residualAdmissible, factor⟩ :=
    factorOrdinaryCutOfCompetitor postAdmissible competitorSound
  have deltaBounded : delta.BoundedBy supply :=
    cut.exact.boundedBy leftBounded rightBounded
  exact ⟨delta, residual, cut, residualAdmissible, factor,
    DemandAlignTypes.ordinary ordinaryClass cut.exact,
    frame.applySubst factor deltaBounded⟩

/-- Checking uses the same factored ordinary cut as synthesis alignment. -/
theorem w_factorOrdinaryCheck
    {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {raw expected : Ty} {selected : STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (rawBounded : (prevailing.apply raw).BoundedBy supply)
    (expectedBounded : (prevailing.apply expected).BoundedBy supply)
    (rawEquation : post.apply (prevailing.apply raw) = selected.emb)
    (expectedEquation : post.apply (prevailing.apply expected) = selected.emb)
    (ordinaryPair : alignPairClass
      (prevailing.apply raw) (prevailing.apply expected) = .ordinary)
    (ordinaryDemand : demandClass
      (prevailing.apply raw) (prevailing.apply expected) = .ordinary) :
    ∃ delta residual : Subst,
      OriginSafeExactPairedMGU []
        (prevailing.apply raw) (prevailing.apply expected) delta ∧
      AdmissiblePost [] residual ∧
      post = Subst.seq residual delta ∧
      DemandAlign prevailing raw expected
        (Subst.seq delta prevailing) ∧
      WProtectedFrameAt supply residual (Subst.seq delta prevailing) frames
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  obtain ⟨delta, residual, cut, residualAdmissible, factor, aligned, moved⟩ :=
    w_factorOrdinaryCut frame postAdmissible rawBounded expectedBounded
      rawEquation expectedEquation ordinaryPair
  exact ⟨delta, residual, cut, residualAdmissible, factor,
    DemandAlign.ordinary ordinaryDemand aligned, moved⟩

/-- Application argument checking needs no explicit selector premises: a
shared residual realizing both sides as the same simple type rules out every
matcher/slot-specific branch. -/
theorem w_factorRealizedArgumentCheck
    {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {raw expected : Ty} {domain : STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (rawBounded : (prevailing.apply raw).BoundedBy supply)
    (expectedBounded : (prevailing.apply expected).BoundedBy supply)
    (rawEquation : post.apply (prevailing.apply raw) = domain.emb)
    (expectedEquation : post.apply (prevailing.apply expected) = domain.emb) :
    ∃ delta residual : Subst,
      OriginSafeExactPairedMGU []
        (prevailing.apply raw) (prevailing.apply expected) delta ∧
      AdmissiblePost [] residual ∧
      post = Subst.seq residual delta ∧
      DemandAlign prevailing raw expected
        (Subst.seq delta prevailing) ∧
      WProtectedFrameAt supply residual (Subst.seq delta prevailing) frames
        (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  apply w_factorOrdinaryCheck frame postAdmissible rawBounded expectedBounded
    rawEquation expectedEquation
  · exact alignPairClass_ordinary_of_realized_emb rawEquation expectedEquation
  · exact demandClass_ordinary_of_expected_realized_emb expectedEquation

/-! ## The first application cut -/

/-- Prepare and discharge the function-shape cut of `DemandSynth.app`.

The two application metavariables are allocated above `supply`; boundedness
of the prevailing substitution proves that it cannot anticipate them.  The
selected DM domain and codomain are installed only in the residual, the
function equation is factored through the executable exact solver, and the
transported frame retains both fresh pairs for the later argument cut. -/
theorem w_prepareAppFunctionCut
    {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {functionRaw : Ty} {domain codomain : STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing.BoundedBy supply)
    (functionBounded : (prevailing.apply functionRaw).BoundedBy supply)
    (functionEquation :
      post.apply (prevailing.apply functionRaw) =
        (STy.fn domain codomain).emb) :
    ∃ delta residual : Subst,
      OriginSafeExactPairedMGU []
        (prevailing.apply functionRaw)
        (prevailing.apply (.fn (.var supply.nextTy)
          (.var (supply.nextTy + 1)))) delta ∧
      AdmissiblePost [] residual ∧
      DM.extendAppTargets post supply domain codomain =
        Subst.seq residual delta ∧
      DemandAlignTypes prevailing functionRaw
        (.fn (.var supply.nextTy) (.var (supply.nextTy + 1)))
        (Subst.seq delta prevailing) ∧
      WProtectedFrameAt { supply with nextTy := supply.nextTy + 2 }
        residual (Subst.seq delta prevailing) frames
        (((.var supply.nextTy, domain) ::
          (.var (supply.nextTy + 1), codomain) :: frontier).map
            fun pair => (delta.apply pair.1, pair.2)) := by
  let bumped : InferenceBase.FreshSupply :=
    { supply with nextTy := supply.nextTy + 2 }
  let extended := DM.extendAppTargets post supply domain codomain
  have preparedFrame : WProtectedFrameAt bumped extended prevailing frames
      ((.var supply.nextTy, domain) ::
        (.var (supply.nextTy + 1), codomain) :: frontier) := by
    exact frame.protectAppTargets domain codomain
  have leftBounded : (prevailing.apply functionRaw).BoundedBy bumped :=
    functionBounded.mono (SupplyExtends.bumpTy supply 2)
  have freshDomainFixed :
      prevailing.apply (.var supply.nextTy) = .var supply.nextTy :=
    DM.Subst.BoundedBy.apply_freshTarget prevailingBounded
  have freshCodomainFixed :
      prevailing.apply (.var (supply.nextTy + 1)) =
        .var (supply.nextTy + 1) :=
    DM.Subst.BoundedBy.apply_targetAbove prevailingBounded (Nat.le_succ _)
  have rightNormalized :
      prevailing.apply (.fn (.var supply.nextTy)
        (.var (supply.nextTy + 1))) =
      .fn (.var supply.nextTy) (.var (supply.nextTy + 1)) := by
    simp only [Subst.apply_fn, freshDomainFixed, freshCodomainFixed]
  have rightBounded :
      (prevailing.apply (.fn (.var supply.nextTy)
        (.var (supply.nextTy + 1)))).BoundedBy bumped := by
    rw [rightNormalized]
    apply Ty.BoundedBy.fnOf
    · apply Ty.BoundedBy.varOf
      show supply.nextTy < supply.nextTy + 2
      omega
    · apply Ty.BoundedBy.varOf
      show supply.nextTy + 1 < supply.nextTy + 2
      omega
  have leftEquation :
      extended.apply (prevailing.apply functionRaw) =
        (STy.fn domain codomain).emb := by
    rw [extendAppTargets_apply_eq post supply domain codomain functionBounded]
    exact functionEquation
  have rightEquation :
      extended.apply
        (prevailing.apply (.fn (.var supply.nextTy)
          (.var (supply.nextTy + 1)))) =
        (STy.fn domain codomain).emb := by
    rw [rightNormalized]
    simp [extended, Subst.apply_fn, STy.emb]
  have ordinaryClass : alignPairClass
      (prevailing.apply functionRaw)
      (prevailing.apply (.fn (.var supply.nextTy)
        (.var (supply.nextTy + 1)))) = .ordinary := by
    rw [rightNormalized]
    cases prevailing.apply functionRaw <;> rfl
  exact w_factorOrdinaryCut preparedFrame
    (DM.AdmissiblePost.extendAppTargets postAdmissible)
    leftBounded rightBounded leftEquation rightEquation ordinaryClass

/-! ## Certified application composition -/

/-- Assemble the application origin and terminal-audit nodes after the two
ordinary solver cuts have been constructed.  Both child audits are indexed
by the same eventual terminal: an audit local to the function result is not
enough when argument traversal performs a later solver step. -/
theorem w_app_certified_complete
    {terminal : Subst} {signature : FrozenSig}
    {supply functionSupply argumentSupply : InferenceBase.FreshSupply}
    {initial functionSubst alignedSubst argumentSubst finalSubst : Subst}
    {rawContext : Context} {function argument : Expr}
    {functionTarget argumentTarget : Ty}
    {functionRaw : DemandSynth signature supply initial rawContext function
      functionTarget functionSupply functionSubst}
    {functionOrigin : DemandSynthOrigin signature functionRaw [] []}
    {functionAlignedOrigin : DemandAlignTypesWithLedger [] functionSubst
      functionTarget
      (.fn (.var functionSupply.nextTy)
        (.var (functionSupply.nextTy + 1))) alignedSubst}
    {argumentRaw : DemandSynth signature
      { functionSupply with nextTy := functionSupply.nextTy + 2 }
      alignedSubst rawContext argument argumentTarget argumentSupply
      argumentSubst}
    {argumentOrigin : DemandSynthOrigin signature argumentRaw [] []}
    {argumentAlignedOrigin : DemandAlignWithLedger [] argumentSubst
      argumentTarget (.var functionSupply.nextTy) finalSubst}
    (functionAudit :
      DemandSynthTerminalAudit terminal signature functionOrigin)
    (argumentAudit :
      DemandSynthTerminalAudit terminal signature argumentOrigin) :
    ∃ (derived : DemandSynth signature supply initial rawContext
          (.app function argument) (.var (functionSupply.nextTy + 1))
          argumentSupply finalSubst)
        (origin : DemandSynthOrigin signature derived [] []),
      Nonempty (DemandSynthTerminalAudit terminal signature origin) := by
  let checked : DemandCheck signature
      { functionSupply with nextTy := functionSupply.nextTy + 2 }
      alignedSubst rawContext argument (.var functionSupply.nextTy)
      argumentSupply finalSubst :=
    DemandCheck.mk argumentRaw argumentAlignedOrigin.erase
  let checkedOrigin : DemandCheckOrigin signature checked [] [] :=
    DemandCheckOrigin.mk argumentOrigin argumentAlignedOrigin
  let checkedAudit : DemandCheckTerminalAudit terminal signature
      checkedOrigin := DemandCheckTerminalAudit.mk
        (aligned := argumentAlignedOrigin) argumentAudit
  let derived : DemandSynth signature supply initial rawContext
      (.app function argument) (.var (functionSupply.nextTy + 1))
      argumentSupply finalSubst :=
    DemandSynth.app functionRaw functionAlignedOrigin.erase checked
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.app functionOrigin functionAlignedOrigin checkedOrigin
  exact ⟨derived, origin,
    ⟨DemandSynthTerminalAudit.app
      (aligned := functionAlignedOrigin) functionAudit checkedAudit⟩⟩

end DM
end TypePM
