import TypePM.DamasMilnerWCapFree
import TypePM.DamasMilnerWAuditPlan
import TypePM.DamasMilnerWFix

/-!
# Coupled completion steps for Damas--Milner Algorithm W

These lemmas connect the one-sort normalized residual to the retired-variable
frame at each ordinary application/fix cut.  They deliberately stay below the
final mutual result package, so constructor induction can consume them without
duplicating solver, generalization-stability, and frontier transport proofs.
-/

namespace TypePM
namespace DM

/-- A raw synthesis packaged with its empty-ledger origin and deferred audit
plan.  The structure lives in `Type`, while its dependent derivation fields
remain proof-irrelevant propositions. -/
structure PlannedSynth (signature : FrozenSig)
    (q : InferenceBase.FreshSupply) (S : Subst) (context : Context)
    (expression : Expr) (target : Ty)
    (q' : InferenceBase.FreshSupply) (S' : Subst) where
  derived : DemandSynth signature q S context expression target q' S'
  origin : DemandSynthOrigin signature derived [] []
  plan : WSynthAuditPlan signature (origin := origin)

/-- One-sort counterpart of the two fresh target bindings allocated by
application and direct-self fix. -/
def SSubst.extendAppTargets (base : SSubst)
    (supply : InferenceBase.FreshSupply) (domain codomain : STy) : SSubst :=
  fun name =>
    if name = supply.nextTy then domain
    else if name = supply.nextTy + 1 then codomain
    else base name

@[simp] theorem SSubst.extendAppTargets_at_domain
    (base : SSubst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    SSubst.extendAppTargets base supply domain codomain supply.nextTy =
      domain := by
  simp [SSubst.extendAppTargets]

@[simp] theorem SSubst.extendAppTargets_at_codomain
    (base : SSubst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    SSubst.extendAppTargets base supply domain codomain
        (supply.nextTy + 1) = codomain := by
  simp [SSubst.extendAppTargets]

/-- Core and one-sort spellings of fresh application-target installation are
definitionally the same substitution after embedding. -/
theorem SSubst.paired_extendAppTargets
    (base : SSubst) (supply : InferenceBase.FreshSupply)
    (domain codomain : STy) :
    SSubst.paired (SSubst.extendAppTargets base supply domain codomain) =
      DM.extendAppTargets (SSubst.paired base) supply domain codomain := by
  apply PhasedPost.subst_ext
  · rfl
  · funext name
    simp only [SSubst.paired, SSubst.emb, SSubst.extendAppTargets,
      DM.extendAppTargets]
    split
    · rfl
    · split <;> rfl

/-- The two fresh bindings do not change an older one-sort target. -/
theorem STy.applySubst_extendAppTargets_eq
    (base : SSubst) (supply : InferenceBase.FreshSupply)
    (domain codomain target : STy)
    (below : TyVarsBelow supply.nextTy target.ftv) :
    target.applySubst
        (SSubst.extendAppTargets base supply domain codomain) =
      target.applySubst base := by
  apply STy.applySubst_eq_of_ftv_agree
  intro name member
  have nameBelow := below name member
  simp [SSubst.extendAppTargets, Nat.ne_of_lt nameBelow,
    Nat.ne_of_lt (Nat.lt_trans nameBelow (Nat.lt_succ_self _))]

/-- Protect the compound function target formed from two already-protected
domain/codomain pairs.  Application/fix allocates the components separately,
while the first/final exact cut uses their function combination. -/
theorem WRetiredStableFrameAt.protectFnOfMembers
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {algorithmDomain algorithmCodomain : Ty}
    {selectedDomain selectedCodomain : STy}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (domainMember : (algorithmDomain, selectedDomain) ∈ frontier)
    (codomainMember : (algorithmCodomain, selectedCodomain) ∈ frontier) :
    WRetiredStableFrameAt signature supply post prevailing frames
      ((.fn algorithmDomain algorithmCodomain,
        .fn selectedDomain selectedCodomain) :: frontier) pending := by
  refine
    { stable :=
        { frame :=
            { contexts := state.stable.frame.contexts
              types := WTypeFrame.cons ?_ state.stable.frame.types
              contextsBounded := state.stable.frame.contextsBounded
              frontierBounded := ?_ }
          lets := state.stable.lets }
      retired := RetiredFrontierFresh.cons ?_ state.retired
      contextsRetired := state.contextsRetired
      pendingBelow := state.pendingBelow }
  · simp only [Subst.apply_fn, STy.emb]
    rw [state.stable.frame.types domainMember,
      state.stable.frame.types codomainMember]
  · intro pair member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact Ty.BoundedBy.fnOf
        (state.stable.frame.frontierBounded _ domainMember)
        (state.stable.frame.frontierBounded _ codomainMember)
    · exact state.stable.frame.frontierBounded pair oldMember
  · intro cut cutMember
    exact PendingLetCut.AvoidsTy.fn
      (state.retired cut cutMember _ domainMember)
      (state.retired cut cutMember _ codomainMember)

/-- A generalized binding constructed over the already-normalized W state can
be used at the prevailing state when that generalized scheme is fixed there. -/
theorem WLetBindingRel.atFixedPrevailing
    {post prevailing : Subst} {algorithmScheme : Scheme}
    {selectedScheme : SScheme}
    (binding : WLetBindingRel post Subst.id algorithmScheme selectedScheme)
    (fixed : algorithmScheme.applyMeta prevailing = algorithmScheme) :
    WLetBindingRel post prevailing algorithmScheme selectedScheme := by
  refine ⟨binding.capArity, ?_⟩
  intro target instantiation
  rw [fixed]
  simpa only [Scheme.applyMeta_id] using binding.realizes instantiation

/-- Consume a normalized value result at a let boundary: construct the
semantic generalized binding, drop the value target from the continuation,
and register the closed variables as retired. -/
theorem w_prepareLetBindingAndRetire
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing : Subst}
    {frames : List (Context × SCtx)}
    {larger smaller : List (Ty × STy)} {pending : List PendingLetCut}
    {rawContext : Context} {selectedContext algorithmContext : SCtx}
    {rawTarget : Ty} {selectedTarget algorithmTarget : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames larger pending)
    (signatureClosed : signature.SchemesClosed)
    (view : NormalizedDMView residual algorithmContext selectedContext
      algorithmTarget selectedTarget (rawContext.applySubst prevailing)
      (prevailing.apply rawTarget))
    (separated :
      ∀ {algorithmVar selectedBinder : TypePM.TyVar},
        algorithmVar ∈ SCtx.ftv algorithmContext →
        selectedBinder ∈
          (SCtx.generalize selectedContext selectedTarget).binders →
        selectedBinder ∉ (residual algorithmVar).ftv)
    (schemeFixed :
      (signature.generalize (rawContext.applySubst prevailing)
        (prevailing.apply rawTarget)).applyMeta prevailing =
      signature.generalize (rawContext.applySubst prevailing)
        (prevailing.apply rawTarget))
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (newFresh : ∀ pair ∈ smaller,
      (PendingLetCut.mk rawContext rawTarget prevailing).AvoidsTy
        signature prevailing pair.1)
    (newContextsFresh : ∀ pair ∈ frames,
      (PendingLetCut.mk rawContext rawTarget prevailing).AvoidsContext
        signature prevailing (pair.1.applySubst prevailing))
    (newBelow :
      (∀ varId, varId ∈ signature.generalizedCapVars
          (rawContext.applySubst prevailing) (prevailing.apply rawTarget) →
        varId.id < supply.nextCap) ∧
      (∀ varId, varId ∈ signature.generalizedTyVars
          (rawContext.applySubst prevailing) (prevailing.apply rawTarget) →
        varId < supply.nextTy))
    (idempotent : prevailing.Idempotent) :
    WLetBindingRel (SSubst.paired residual) prevailing
        (signature.generalize (rawContext.applySubst prevailing)
          (prevailing.apply rawTarget))
        (SCtx.generalize selectedContext selectedTarget) ∧
      WRetiredStableFrameAt signature supply (SSubst.paired residual)
        prevailing frames smaller
        (PendingLetCut.mk rawContext rawTarget prevailing :: pending) := by
  have bindingAtId := view.letBinding signatureClosed.signatureTargets separated
  have binding := bindingAtId.atFixedPrevailing schemeFixed
  exact ⟨binding,
    state.registerLetAfterDrop subset newFresh newContextsFresh newBelow
      idempotent⟩

/-- Install the generalized let binding as the active protected context for
the body, retaining the registered retired-variable invariant. -/
theorem WRetiredStableFrameAt.protectLetBody
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {pending : List PendingLetCut}
    {rawContext : Context} {selectedContext : SCtx}
    {name : String} {algorithmScheme : Scheme}
    {selectedScheme : SScheme}
    (state : WRetiredStableFrameAt signature supply post prevailing frames
      frontier pending)
    (outer : WContextRel post (rawContext.applySubst prevailing)
      selectedContext)
    (binding : WLetBindingRel post prevailing algorithmScheme selectedScheme)
    (bounded : Context.BoundedBy supply
      (Context.applySubst prevailing
        ((name, algorithmScheme) :: rawContext)))
    (bodyFresh : ∀ cut ∈ pending,
      cut.AvoidsContext signature prevailing
        (Context.applySubst prevailing
          ((name, algorithmScheme) :: rawContext))) :
    WRetiredStableFrameAt signature supply post prevailing
      ((((name, algorithmScheme) :: rawContext,
          (name, selectedScheme) :: selectedContext)) :: frames)
      frontier pending := by
  refine
    { stable :=
        { frame := state.stable.frame.protectLetBody outer binding bounded
          lets := state.stable.lets }
      retired := state.retired
      contextsRetired := ?_
      pendingBelow := state.pendingBelow }
  intro cut cutMember pair pairMember
  rcases List.mem_cons.mp pairMember with rfl | oldMember
  · exact bodyFresh cut cutMember
  · exact state.contextsRetired cut cutMember pair oldMember

/-- Exact ordinary cut between two normalized DM targets.  The same one-sort
competitor is retained as residual by MGU absorption; no arbitrary core
residual has to be decoded after the cut. -/
theorem w_factorNormalizedRetiredCut
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    {left right : Ty} {algorithmLeft algorithmRight : STy}
    {selectedLeft selectedRight : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames frontier pending)
    (signatureClosed : signature.SchemesClosed)
    (leftNormalized : left = algorithmLeft.emb)
    (rightNormalized : right = algorithmRight.emb)
    (leftMember : (left, selectedLeft) ∈ frontier)
    (rightMember : (right, selectedRight) ∈ frontier)
    (sound : algorithmLeft.applySubst residual =
      algorithmRight.applySubst residual)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    ∃ (delta : Subst),
      LetStableExactPairedCut signature prevailing pending left right delta ∧
        SSubst.paired residual =
          Subst.seq (SSubst.paired residual) delta ∧
        WRetiredStableFrameAt signature supply (SSubst.paired residual)
          (Subst.seq delta prevailing) frames
          (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  obtain ⟨chosenDelta, exact, factor⟩ :=
    factorOrdinaryCutOfSSubst residual sound
  have normalizedExact : OriginSafeExactPairedMGU [] left right chosenDelta := by
    simpa only [leftNormalized, rightNormalized] using exact
  have solverCut : LetStableExactPairedCut signature prevailing pending
      left right chosenDelta := pendingCapFree.letStableExactPairedCut
    normalizedExact (by rw [leftNormalized, STy.emb_fcv])
    (by rw [rightNormalized, STy.emb_fcv])
    (state.retired.separated leftMember rightMember)
  exact ⟨chosenDelta, solverCut, factor,
    state.applyLetStableExactPairedCut solverCut signatureClosed
      leftMember rightMember factor⟩

/-- Solver transport plus the ordinary `DemandAlignTypes` node used by the
first application cut and the final direct-self fix cut. -/
theorem w_alignNormalizedRetired
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    {rawLeft rawRight : Ty} {algorithmLeft algorithmRight selected : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames frontier pending)
    (signatureClosed : signature.SchemesClosed)
    (leftNormalized : prevailing.apply rawLeft = algorithmLeft.emb)
    (rightNormalized : prevailing.apply rawRight = algorithmRight.emb)
    (leftSelected : algorithmLeft.applySubst residual = selected)
    (rightSelected : algorithmRight.applySubst residual = selected)
    (leftMember : (prevailing.apply rawLeft, selected) ∈ frontier)
    (rightMember : (prevailing.apply rawRight, selected) ∈ frontier)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    ∃ (delta : Subst),
      LetStableExactPairedCut signature prevailing pending
          (prevailing.apply rawLeft) (prevailing.apply rawRight) delta ∧
        SSubst.paired residual =
          Subst.seq (SSubst.paired residual) delta ∧
        DemandAlignTypes prevailing rawLeft rawRight
          (Subst.seq delta prevailing) ∧
        WRetiredStableFrameAt signature supply (SSubst.paired residual)
          (Subst.seq delta prevailing) frames
          (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  have sound : algorithmLeft.applySubst residual =
      algorithmRight.applySubst residual := leftSelected.trans rightSelected.symm
  obtain ⟨delta, solverCut, factor, moved⟩ :=
    w_factorNormalizedRetiredCut state signatureClosed leftNormalized
      rightNormalized leftMember rightMember sound pendingCapFree
  have leftEquation : (SSubst.paired residual).apply
      (prevailing.apply rawLeft) = selected.emb := by
    rw [leftNormalized, SSubst.paired_apply_emb, leftSelected]
  have rightEquation : (SSubst.paired residual).apply
      (prevailing.apply rawRight) = selected.emb := by
    rw [rightNormalized, SSubst.paired_apply_emb, rightSelected]
  have ordinary := alignPairClass_ordinary_of_realized_emb
    leftEquation rightEquation
  exact ⟨delta, solverCut, factor,
    DemandAlignTypes.ordinary ordinary solverCut.exact.exact, moved⟩

/-- The second application cut, adding the ordinary demand-class witness on
top of the same normalized retired-state transport. -/
theorem w_checkNormalizedRetired
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {residual : SSubst} {prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {pending : List PendingLetCut}
    {raw expected : Ty} {algorithmRaw algorithmExpected selected : STy}
    (state : WRetiredStableFrameAt signature supply
      (SSubst.paired residual) prevailing frames frontier pending)
    (signatureClosed : signature.SchemesClosed)
    (rawNormalized : prevailing.apply raw = algorithmRaw.emb)
    (expectedNormalized : prevailing.apply expected = algorithmExpected.emb)
    (rawSelected : algorithmRaw.applySubst residual = selected)
    (expectedSelected : algorithmExpected.applySubst residual = selected)
    (rawMember : (prevailing.apply raw, selected) ∈ frontier)
    (expectedMember : (prevailing.apply expected, selected) ∈ frontier)
    (pendingCapFree : PendingLetsCapFree prevailing pending) :
    ∃ (delta : Subst),
      LetStableExactPairedCut signature prevailing pending
          (prevailing.apply raw) (prevailing.apply expected) delta ∧
        SSubst.paired residual =
          Subst.seq (SSubst.paired residual) delta ∧
        DemandAlign prevailing raw expected (Subst.seq delta prevailing) ∧
        WRetiredStableFrameAt signature supply (SSubst.paired residual)
          (Subst.seq delta prevailing) frames
          (frontier.map fun pair => (delta.apply pair.1, pair.2)) pending := by
  obtain ⟨delta, solverCut, factor, aligned, moved⟩ :=
    w_alignNormalizedRetired state signatureClosed rawNormalized
      expectedNormalized rawSelected expectedSelected rawMember expectedMember
      pendingCapFree
  have expectedEquation : (SSubst.paired residual).apply
      (prevailing.apply expected) = selected.emb := by
    rw [expectedNormalized, SSubst.paired_apply_emb, expectedSelected]
  have ordinaryDemand :=
    demandClass_ordinary_of_expected_realized_emb
      (raw := prevailing.apply raw) expectedEquation
  exact ⟨delta, solverCut, factor,
    DemandAlign.ordinary ordinaryDemand aligned, moved⟩

/-! ## Constructor and deferred-audit packaging -/

/-- Package the two application children and their ordinary cuts into the raw
synthesis, empty-ledger origin, and eventual-terminal audit plan. -/
theorem w_app_planned_complete
    {signature : FrozenSig}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S₂ S₃ S' : Subst}
    {context : Context} {function argument : Expr} {functionTarget : Ty}
    {functionRaw : DemandSynth signature q S context function functionTarget
      q₁ S₁}
    {functionOrigin : DemandSynthOrigin signature functionRaw [] []}
    {functionAligned : DemandAlignTypesWithLedger [] S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂}
    {argumentTarget : Ty}
    {argumentRaw : DemandSynth signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ context argument
      argumentTarget q' S₃}
    {argumentOrigin : DemandSynthOrigin signature argumentRaw [] []}
    {argumentAligned : DemandAlignWithLedger [] S₃ argumentTarget
      (.var q₁.nextTy) S'}
    (functionPlan : WSynthAuditPlan signature (origin := functionOrigin))
    (argumentPlan : WSynthAuditPlan signature (origin := argumentOrigin)) :
    Nonempty (PlannedSynth signature q S context (.app function argument)
      (.var (q₁.nextTy + 1)) q' S') := by
  let checked : DemandCheck signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ context argument
      (.var q₁.nextTy) q' S' :=
    DemandCheck.mk argumentRaw argumentAligned.erase
  let checkedOrigin : DemandCheckOrigin signature checked [] [] :=
    DemandCheckOrigin.mk argumentOrigin argumentAligned
  let checkedPlan : WCheckAuditPlan signature (origin := checkedOrigin) :=
    WSynthAuditPlan.check (aligned := argumentAligned) argumentPlan
  let derived : DemandSynth signature q S context (.app function argument)
      (.var (q₁.nextTy + 1)) q' S' :=
    DemandSynth.app functionRaw functionAligned.erase checked
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.app functionOrigin functionAligned checkedOrigin
  exact ⟨⟨derived, origin, WSynthAuditPlan.app
    (aligned := functionAligned) functionPlan checkedPlan⟩⟩

/-- Package direct-self fix after its terminal codomain cut. -/
theorem w_fix_planned_complete
    {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {context : Context} {self argument : String} {body : Expr}
    {bodyTarget : Ty}
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
      body bodyTarget q' S₁}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw [] []}
    {aligned : DemandAlignTypesWithLedger [] S₁ bodyTarget
      (.var (q.nextTy + 1)) S'}
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    (bodyPlan : WSynthAuditPlan signature (origin := bodyOrigin)) :
    Nonempty (PlannedSynth signature q S context (.fix self argument body)
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) q' S') := by
  let derived : DemandSynth signature q S context (.fix self argument body)
      (.fn (.var q.nextTy) (.var (q.nextTy + 1))) q' S' :=
    DemandSynth.fix distinct direct nonMatcher bodyRaw aligned.erase
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned
  exact ⟨⟨derived, origin, WSynthAuditPlan.fix
    (distinct := distinct) (direct := direct) (nonMatcher := nonMatcher)
    (aligned := aligned) bodyPlan⟩⟩

/-- Package let after its normalized generalized binding has been installed
for the body traversal.  The plan registers the value cut and delays exact
`LetFacts` construction to the eventual terminal. -/
theorem w_let_planned_complete
    {signature : FrozenSig}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {context : Context} {name : String} {value body : Expr}
    {valueTarget bodyTarget : Ty}
    {valueRaw : DemandSynth signature q S context value valueTarget q₁ S₁}
    {valueOrigin : DemandSynthOrigin signature valueRaw [] []}
    {bodyRaw : DemandSynth signature q₁ S₁
      ((name, signature.generalize (context.applySubst S₁)
        (S₁.apply valueTarget)) :: context) body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw [] []}
    (valuePlan : WSynthAuditPlan signature (origin := valueOrigin))
    (bodyPlan : WSynthAuditPlan signature (origin := bodyOrigin)) :
    Nonempty (PlannedSynth signature q S context (.letE name value body)
      bodyTarget q' S') := by
  let derived : DemandSynth signature q S context (.letE name value body)
      bodyTarget q' S' := DemandSynth.letE valueRaw bodyRaw
  let origin : DemandSynthOrigin signature derived [] [] :=
    DemandSynthOrigin.letE valueOrigin bodyOrigin
  exact ⟨⟨derived, origin, WSynthAuditPlan.letE valuePlan bodyPlan⟩⟩

end DM
end TypePM
