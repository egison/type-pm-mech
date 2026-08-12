import TypePM.DamasMilnerGeneralization
import TypePM.DemandTypingInferenceCompletenessContext
import TypePM.DemandTypingInferenceCompletenessTraversal

/-!
# Algorithm W completeness for the Damas--Milner fragment

This module turns the residual-relative algebra into demand-directed runs.
The first layer below is the generic principal-opening fact needed by the
variable constructor: every declarative use of a bounded canonical scheme is
obtained by specializing its supply-indexed fresh opening.
-/

namespace TypePM
namespace DM

/-! ## Principal finite openings -/

/-- Rewrite exactly the fresh interval allocated by one canonical scheme
opening.  Variables below the incoming supply are left untouched. -/
def schemeOpeningPost (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) (opening : scheme.ValueOpening) : Subst :=
  { cap := fun varId =>
      if bounds : supply.nextCap ≤ varId.id ∧
          varId.id - supply.nextCap < scheme.capArity then
        .var (opening.capImage
          ⟨varId.id - supply.nextCap, bounds.2⟩)
      else
        .var varId
    target := fun varId =>
      if bounds : supply.nextTy ≤ varId ∧
          varId - supply.nextTy < scheme.tyArity then
        opening.tyImage ⟨varId - supply.nextTy, bounds.2⟩
      else
        .var varId }

theorem schemeOpeningPost_cap_below
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : scheme.ValueOpening) (varId : CapVar)
    (below : varId.id < supply.nextCap) :
    (schemeOpeningPost supply scheme opening).cap varId = Cap.var varId := by
  simp [schemeOpeningPost, Nat.not_le_of_gt below]

theorem schemeOpeningPost_target_below
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : scheme.ValueOpening) (varId : TypePM.TyVar)
    (below : varId < supply.nextTy) :
    (schemeOpeningPost supply scheme opening).target varId = Ty.var varId := by
  simp [schemeOpeningPost, Nat.not_le_of_gt below]

theorem schemeOpeningPost_capImage
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : scheme.ValueOpening) (index : Fin scheme.capArity) :
    (schemeOpeningPost supply scheme opening).cap
        ((Scheme.canonicalFreshOpening supply scheme).capImage index) =
      Cap.var (opening.capImage index) := by
  simp [schemeOpeningPost, Scheme.canonicalFreshOpening]

theorem schemeOpeningPost_tyImage
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : scheme.ValueOpening) (index : Fin scheme.tyArity) :
    (schemeOpeningPost supply scheme opening).apply
        (.var ((Scheme.canonicalFreshOpening supply scheme).tyImage index)) =
      opening.tyImage index := by
  simp [schemeOpeningPost, Scheme.canonicalFreshOpening,
    Subst.apply, Ty.applyCapability, Ty.applyTarget]

/-- The opening post cannot rewrite any free metavariable of a scheme bounded
at the incoming supply. -/
theorem applyMeta_schemeOpeningPost_eq_self
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : scheme.ValueOpening) (bounded : scheme.BoundedBy supply) :
    scheme.applyMeta (schemeOpeningPost supply scheme opening) = scheme := by
  have equality := Scheme.applyMeta_eq_of_free_agree
    (schemeOpeningPost supply scheme opening) Subst.id scheme
    (by
      intro varId membership
      exact schemeOpeningPost_cap_below supply scheme opening varId
        (bounded.caps varId membership))
    (by
      intro varId membership
      exact schemeOpeningPost_target_below supply scheme opening varId
        (bounded.targets varId membership))
  simpa using equality

/-- Every value-flow use of a bounded scheme is a specialization of the
executable canonical fresh opening at the same supply. -/
theorem canonicalSchemeOpening_principal
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (bounded : scheme.BoundedBy supply) {target : Ty}
    (instantiation : scheme.ValueFlowInst target) :
    (schemeOpeningPost supply scheme (Classical.choose instantiation)).apply
        (InferenceBase.instantiateScheme supply scheme).value = target := by
  let opening := Classical.choose instantiation
  have opened : scheme.openValue opening = target :=
    Classical.choose_spec instantiation
  have transported := PolyTy.instantiate_applyMeta
    (schemeOpeningPost supply scheme opening)
    (Scheme.canonicalFreshOpening supply scheme).capImage
    opening.capImage
    (fun index => .var
      ((Scheme.canonicalFreshOpening supply scheme).tyImage index))
    (schemeOpeningPost_capImage supply scheme opening)
    scheme.body
  have schemeFixed :=
    applyMeta_schemeOpeningPost_eq_self supply scheme opening bounded
  have bodyFixed : PolyTy.applyMeta
      (schemeOpeningPost supply scheme opening) scheme.body = scheme.body := by
    cases scheme with
    | mk capArity tyArity body =>
      simp only [Scheme.applyMeta] at schemeFixed ⊢
      injection schemeFixed
  rw [bodyFixed] at transported
  simp only [schemeOpeningPost_tyImage] at transported
  calc
    (schemeOpeningPost supply scheme opening).apply
        (InferenceBase.instantiateScheme supply scheme).value =
        scheme.openValue opening := by
      rw [InferenceBase.instantiateScheme_value]
      exact transported.symm
    _ = target := opened

/-- Override only the fresh interval of a canonical opening, retaining an
arbitrary pre-existing residual everywhere else.  Unlike sequential
composition, this cannot accidentally rewrite an old residual image which
happens to use an identifier in the new fresh interval. -/
def extendSchemeOpening (base : Subst)
    (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) (opening : (scheme.applyMeta base).ValueOpening) : Subst :=
  { cap := fun varId =>
      if bounds : supply.nextCap ≤ varId.id ∧
          varId.id - supply.nextCap < scheme.capArity then
        .var (opening.capImage
          ⟨varId.id - supply.nextCap, bounds.2⟩)
      else
        base.cap varId
    target := fun varId =>
      if bounds : supply.nextTy ≤ varId ∧
          varId - supply.nextTy < scheme.tyArity then
        opening.tyImage ⟨varId - supply.nextTy, bounds.2⟩
      else
        base.target varId }

theorem extendSchemeOpening_cap_below
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening) (varId : CapVar)
    (below : varId.id < supply.nextCap) :
    (extendSchemeOpening base supply scheme opening).cap varId =
      base.cap varId := by
  simp [extendSchemeOpening, Nat.not_le_of_gt below]

theorem extendSchemeOpening_target_below
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening)
    (varId : TypePM.TyVar) (below : varId < supply.nextTy) :
    (extendSchemeOpening base supply scheme opening).target varId =
      base.target varId := by
  simp [extendSchemeOpening, Nat.not_le_of_gt below]

theorem extendSchemeOpening_capImage
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening)
    (index : Fin scheme.capArity) :
    (extendSchemeOpening base supply scheme opening).cap
        ((Scheme.canonicalFreshOpening supply scheme).capImage index) =
      .var (opening.capImage index) := by
  simp [extendSchemeOpening, Scheme.canonicalFreshOpening]

theorem extendSchemeOpening_tyImage
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening)
    (index : Fin scheme.tyArity) :
    (extendSchemeOpening base supply scheme opening).apply
        (.var ((Scheme.canonicalFreshOpening supply scheme).tyImage index)) =
      opening.tyImage index := by
  simp [extendSchemeOpening, Scheme.canonicalFreshOpening,
    Subst.apply, Ty.applyCapability, Ty.applyTarget]

/-- The override agrees with the old residual on all free scheme metas. -/
theorem Scheme.applyMeta_extendSchemeOpening_eq
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening)
    (bounded : scheme.BoundedBy supply) :
    scheme.applyMeta (extendSchemeOpening base supply scheme opening) =
      scheme.applyMeta base := by
  apply Scheme.applyMeta_eq_of_free_agree
  · intro varId membership
    exact extendSchemeOpening_cap_below base supply scheme opening varId
      (bounded.caps varId membership)
  · intro varId membership
    exact extendSchemeOpening_target_below base supply scheme opening varId
      (bounded.targets varId membership)

/-- Relative principal-opening theorem: an arbitrary use of the scheme after
the old residual is obtained by a pointwise fresh-interval extension, while
the extension still agrees with the old residual below the supply. -/
theorem canonicalSchemeOpening_principal_relative
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (bounded : scheme.BoundedBy supply) {target : Ty}
    (instantiation : (scheme.applyMeta base).ValueFlowInst target) :
    (extendSchemeOpening base supply scheme
      (Classical.choose instantiation)).apply
        (InferenceBase.instantiateScheme supply scheme).value = target := by
  let opening := Classical.choose instantiation
  have opened : (scheme.applyMeta base).openValue opening = target :=
    Classical.choose_spec instantiation
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

/-! ## The shared residual frame -/

/-- A finite list of algorithm/DM type pairs is interpreted by one shared
residual.  Structural W cases add temporary domain/codomain pairs to this
frontier so recursive calls cannot lose equations needed by later cuts. -/
def WTypeFrame (post : Subst) (frontier : List (Ty × STy)) : Prop :=
  ∀ {algorithm : Ty} {selected : STy},
    (algorithm, selected) ∈ frontier →
      post.apply algorithm = selected.emb

theorem WTypeFrame.nil (post : Subst) : WTypeFrame post [] := by
  intro algorithm selected member
  simp at member

theorem WTypeFrame.cons
    {post : Subst} {frontier : List (Ty × STy)}
    {algorithm : Ty} {selected : STy}
    (head : post.apply algorithm = selected.emb)
    (tail : WTypeFrame post frontier) :
    WTypeFrame post ((algorithm, selected) :: frontier) := by
  intro candidate specific member
  rcases List.mem_cons.mp member with equality | member
  · cases equality
    exact head
  · exact tail member

/-- Solver factorization transports every protected equation to the
normalized algorithm types. -/
theorem WTypeFrame.applySubst
    {post delta residual : Subst} {frontier : List (Ty × STy)}
    (frame : WTypeFrame post frontier)
    (factor : post = Subst.seq residual delta) :
    WTypeFrame residual
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  intro algorithm selected member
  rw [List.mem_map] at member
  obtain ⟨pair, pairMember, equality⟩ := member
  cases equality
  rw [← Subst.seq_apply, ← factor]
  exact frame pairMember

/-- Context realization and protected type equations form the W induction
frame. -/
structure WFrame (post : Subst) (algorithmContext : Context)
    (selectedContext : SCtx) (frontier : List (Ty × STy)) : Prop where
  contexts : WContextRel post algorithmContext selectedContext
  types : WTypeFrame post frontier

/-- The algorithm side of a W frame lies below the current fresh supply.
This is the precise scope fact which makes pointwise extension at newly
allocated identifiers preserve every older equation. -/
structure WFrameAt (supply : InferenceBase.FreshSupply) (post : Subst)
    (algorithmContext : Context) (selectedContext : SCtx)
    (frontier : List (Ty × STy)) : Prop extends
    WFrame post algorithmContext selectedContext frontier where
  contextBounded : algorithmContext.BoundedBy supply
  frontierBounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply

/-- Several raw contexts can be protected simultaneously.  The active
context is pushed before descending under a shadowing binder; older entries
remain available when the recursive call returns. -/
def WContextFrames (post prevailing : Subst)
    (frames : List (Context × SCtx)) : Prop :=
  ∀ {rawContext : Context} {selectedContext : SCtx},
    (rawContext, selectedContext) ∈ frames →
      WContextRel post (rawContext.applySubst prevailing) selectedContext

def WContextFrames.BoundedBy (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (frames : List (Context × SCtx)) : Prop :=
  ∀ {rawContext : Context} {selectedContext : SCtx},
    (rawContext, selectedContext) ∈ frames →
      (rawContext.applySubst prevailing).BoundedBy supply

/-- Protected multi-context form of the W frame. -/
structure WProtectedFrameAt (supply : InferenceBase.FreshSupply)
    (post prevailing : Subst) (frames : List (Context × SCtx))
    (frontier : List (Ty × STy)) : Prop where
  contexts : WContextFrames post prevailing frames
  types : WTypeFrame post frontier
  contextsBounded : WContextFrames.BoundedBy supply prevailing frames
  frontierBounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply

/-- Project one active context out of a protected multi-context frame.  This
is the adapter used by the variable completeness lemma, whose canonical
opening argument only needs the current context while the surrounding W
induction must retain every older context. -/
theorem WProtectedFrameAt.project
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    {rawContext : Context} {selectedContext : SCtx}
    (member : (rawContext, selectedContext) ∈ frames) :
    WFrameAt supply post (rawContext.applySubst prevailing)
      selectedContext frontier :=
  { contexts := frame.contexts member
    types := frame.types
    contextBounded := frame.contextsBounded member
    frontierBounded := frame.frontierBounded }

theorem WContextFrames.nil (post prevailing : Subst) :
    WContextFrames post prevailing [] := by
  intro rawContext selectedContext member
  simp at member

theorem WContextFrames.cons
    {post prevailing : Subst} {frames : List (Context × SCtx)}
    {rawContext : Context} {selectedContext : SCtx}
    (head : WContextRel post (rawContext.applySubst prevailing) selectedContext)
    (tail : WContextFrames post prevailing frames) :
    WContextFrames post prevailing
      ((rawContext, selectedContext) :: frames) := by
  intro candidate specific member
  rcases List.mem_cons.mp member with equality | member
  · cases equality
    exact head
  · exact tail member

theorem WContextFrames.BoundedBy.cons
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    {frames : List (Context × SCtx)} {rawContext : Context}
    {selectedContext : SCtx}
    (head : (rawContext.applySubst prevailing).BoundedBy supply)
    (tail : WContextFrames.BoundedBy supply prevailing frames) :
    WContextFrames.BoundedBy supply prevailing
      ((rawContext, selectedContext) :: frames) := by
  intro candidate specific member
  rcases List.mem_cons.mp member with equality | member
  · cases equality
    exact head
  · exact tail member

theorem WProtectedFrameAt.protect
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {rawContext : Context} {selectedContext : SCtx}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (related : WContextRel post (rawContext.applySubst prevailing)
      selectedContext)
    (bounded : (rawContext.applySubst prevailing).BoundedBy supply) :
    WProtectedFrameAt supply post prevailing
      ((rawContext, selectedContext) :: frames) frontier :=
  ⟨WContextFrames.cons related frame.contexts, frame.types,
    WContextFrames.BoundedBy.cons bounded frame.contextsBounded,
    frame.frontierBounded⟩

/-- An exact solver cut normalizes all protected raw contexts and frontier
types while replacing the shared residual by its factor. -/
theorem WContextFrames.applySubst
    {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)}
    (contexts : WContextFrames post prevailing frames)
    (factor : post = Subst.seq residual delta) :
    WContextFrames residual (Subst.seq delta prevailing) frames := by
  intro rawContext selectedContext member
  have transported : WContextRel residual
      ((rawContext.applySubst prevailing).applySubst delta)
      selectedContext := by
    intro name scheme found
    exact WContextRel.applySubst (contexts member) factor found
  rw [Context.applySubst_seq]
  intro name scheme found
  exact transported found

theorem WContextFrames.BoundedBy.applySubst
    {supply : InferenceBase.FreshSupply} {prevailing delta : Subst}
    {frames : List (Context × SCtx)}
    (contexts : WContextFrames.BoundedBy supply prevailing frames)
    (deltaBounded : delta.BoundedBy supply) :
    WContextFrames.BoundedBy supply (Subst.seq delta prevailing) frames := by
  intro rawContext selectedContext member
  rw [Context.applySubst_seq]
  exact (contexts member).applySubst deltaBounded

theorem WProtectedFrameAt.applySubst
    {supply : InferenceBase.FreshSupply} {post prevailing delta residual : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (factor : post = Subst.seq residual delta)
    (deltaBounded : delta.BoundedBy supply) :
    WProtectedFrameAt supply residual (Subst.seq delta prevailing) frames
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  refine
    { contexts := WContextFrames.applySubst frame.contexts factor
      types := WTypeFrame.applySubst frame.types factor
      contextsBounded := WContextFrames.BoundedBy.applySubst
        frame.contextsBounded deltaBounded
      frontierBounded := ?_ }
  intro pair member
  rw [List.mem_map] at member
  obtain ⟨oldPair, oldMember, equality⟩ := member
  cases equality
  exact deltaBounded.apply (frame.frontierBounded oldPair oldMember)

/-! ## Pointwise fresh monomorphic binders -/

/-- Override one freshly allocated target metavariable without composing
through the old residual range. -/
def extendFreshTarget (base : Subst) (fresh : TypePM.TyVar)
    (selected : STy) : Subst :=
  { cap := base.cap
    target := fun varId => if fresh = varId then selected.emb else base.target varId }

@[simp] theorem extendFreshTarget_at (base : Subst)
    (fresh : TypePM.TyVar) (selected : STy) :
    (extendFreshTarget base fresh selected).apply (.var fresh) = selected.emb := by
  simp [extendFreshTarget, Subst.apply, Ty.applyCapability, Ty.applyTarget]

theorem extendFreshTarget_apply_below
    (base : Subst) (supply : InferenceBase.FreshSupply) (selected : STy)
    {target : Ty} (bounded : target.BoundedBy supply) :
    (extendFreshTarget base supply.nextTy selected).apply target =
      base.apply target := by
  apply Subst.apply_eq_of_free_agree
  · intro varId _membership
    rfl
  · intro varId membership
    have distinct : supply.nextTy ≠ varId :=
      Nat.ne_of_gt (bounded.targets varId membership)
    simp [extendFreshTarget, distinct]

theorem WContextRel.extendFreshTarget
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx}
    (selected : STy)
    (contexts : WContextRel base algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply) :
    WContextRel (DM.extendFreshTarget base supply.nextTy selected)
      algorithmContext selectedContext := by
  intro name specificScheme found
  obtain ⟨generalScheme, generalFound, capArity, realizes⟩ := contexts found
  refine ⟨generalScheme, generalFound, capArity, ?_⟩
  intro target instantiation
  have use := realizes instantiation
  have schemeEq : generalScheme.applyMeta
      (DM.extendFreshTarget base supply.nextTy selected) =
      generalScheme.applyMeta base := by
    apply Scheme.applyMeta_eq_of_free_agree
    · intro _ _
      rfl
    · intro varId membership
      have distinct : supply.nextTy ≠ varId :=
        Nat.ne_of_gt ((bounded.find? generalFound).targets varId membership)
      simp [DM.extendFreshTarget, distinct]
  rw [schemeEq]
  exact use

theorem WTypeFrame.extendFreshTarget
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {frontier : List (Ty × STy)} (selected : STy)
    (frame : WTypeFrame base frontier)
    (bounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply) :
    WTypeFrame (extendFreshTarget base supply.nextTy selected) frontier := by
  intro algorithm specific member
  rw [extendFreshTarget_apply_below base supply selected
    (bounded (algorithm, specific) member)]
  exact frame member

theorem WContextFrames.extendFreshTarget
    {base prevailing : Subst} {supply : InferenceBase.FreshSupply}
    {frames : List (Context × SCtx)} (selected : STy)
    (contexts : WContextFrames base prevailing frames)
    (bounded : WContextFrames.BoundedBy supply prevailing frames) :
    WContextFrames (extendFreshTarget base supply.nextTy selected)
      prevailing frames := by
  intro rawContext selectedContext member
  exact WContextRel.extendFreshTarget selected (contexts member)
    (bounded member)

theorem WProtectedFrameAt.extendFreshTarget
    {base prevailing : Subst} {supply : InferenceBase.FreshSupply}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply base prevailing frames frontier)
    (selected : STy) :
    WProtectedFrameAt { supply with nextTy := supply.nextTy + 1 }
      (extendFreshTarget base supply.nextTy selected)
      prevailing frames ((.var supply.nextTy, selected) :: frontier) :=
  ⟨WContextFrames.extendFreshTarget selected frame.contexts
      frame.contextsBounded,
    WTypeFrame.cons (extendFreshTarget_at base supply.nextTy selected)
      (WTypeFrame.extendFreshTarget selected frame.types frame.frontierBounded),
    fun member => (frame.contextsBounded member).mono
      (SupplyExtends.bumpTy supply 1),
    fun pair member => by
      rcases List.mem_cons.mp member with equality | oldMember
      · cases equality
        exact Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      · exact (frame.frontierBounded pair oldMember).mono
          (SupplyExtends.bumpTy supply 1)⟩

theorem WFrame.emb_id (context : SCtx) :
    WFrame Subst.id context.emb context [] :=
  ⟨WContextRel.emb_id context, WTypeFrame.nil Subst.id⟩

theorem WFrame.applySubst
    {post delta residual : Subst} {algorithmContext : Context}
    {selectedContext : SCtx} {frontier : List (Ty × STy)}
    (frame : WFrame post algorithmContext selectedContext frontier)
    (factor : post = Subst.seq residual delta) :
    WFrame residual (algorithmContext.applySubst delta) selectedContext
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) :=
  ⟨WContextRel.applySubst frame.contexts factor,
    WTypeFrame.applySubst frame.types factor⟩

/-- A fresh-interval opening extension is observationally equal to its base
residual on every type bounded by the incoming supply. -/
theorem extendSchemeOpening_apply_eq
    (base : Subst) (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (opening : (scheme.applyMeta base).ValueOpening) {target : Ty}
    (bounded : target.BoundedBy supply) :
    (extendSchemeOpening base supply scheme opening).apply target =
      base.apply target := by
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    exact extendSchemeOpening_cap_below base supply scheme opening varId
      (bounded.caps varId membership)
  · intro varId membership
    exact extendSchemeOpening_target_below base supply scheme opening varId
      (bounded.targets varId membership)

/-- Pointwise fresh extension preserves every context scheme realization. -/
theorem WContextRel.extendSchemeOpening
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx}
    {scheme : Scheme} (opening : (scheme.applyMeta base).ValueOpening)
    (contexts : WContextRel base algorithmContext selectedContext)
    (bounded : algorithmContext.BoundedBy supply) :
    WContextRel (DM.extendSchemeOpening base supply scheme opening)
      algorithmContext selectedContext := by
  intro name specificScheme found
  obtain ⟨generalScheme, generalFound, capArity, realizes⟩ := contexts found
  refine ⟨generalScheme, generalFound, capArity, ?_⟩
  intro target instantiation
  have use := realizes instantiation
  have generalBounded := bounded.find? generalFound
  have schemeEq : generalScheme.applyMeta
      (DM.extendSchemeOpening base supply scheme opening) =
      generalScheme.applyMeta base := by
    apply Scheme.applyMeta_eq_of_free_agree
    · intro varId membership
      exact DM.extendSchemeOpening_cap_below base supply scheme opening varId
        (generalBounded.caps varId membership)
    · intro varId membership
      exact DM.extendSchemeOpening_target_below base supply scheme opening varId
        (generalBounded.targets varId membership)
  rw [schemeEq]
  exact use

/-- Pointwise fresh extension also preserves every protected frontier pair. -/
theorem WTypeFrame.extendSchemeOpening
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {frontier : List (Ty × STy)} {scheme : Scheme}
    (opening : (scheme.applyMeta base).ValueOpening)
    (frame : WTypeFrame base frontier)
    (bounded : ∀ pair ∈ frontier, pair.1.BoundedBy supply) :
    WTypeFrame (extendSchemeOpening base supply scheme opening) frontier := by
  intro algorithm selected member
  rw [extendSchemeOpening_apply_eq base supply scheme opening
    (bounded (algorithm, selected) member)]
  exact frame member

/-- Fresh-interval extension preserves every protected context. -/
theorem WContextFrames.extendSchemeOpening
    {base prevailing : Subst} {supply : InferenceBase.FreshSupply}
    {frames : List (Context × SCtx)} {scheme : Scheme}
    (opening : (scheme.applyMeta base).ValueOpening)
    (contexts : WContextFrames base prevailing frames)
    (bounded : WContextFrames.BoundedBy supply prevailing frames) :
    WContextFrames (DM.extendSchemeOpening base supply scheme opening)
      prevailing frames := by
  intro rawContext selectedContext member
  exact WContextRel.extendSchemeOpening opening (contexts member)
    (bounded member)

theorem WProtectedFrameAt.extendSchemeOpening
    {base prevailing : Subst} {supply : InferenceBase.FreshSupply}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {scheme : Scheme}
    (frame : WProtectedFrameAt supply base prevailing frames frontier)
    (opening : (scheme.applyMeta base).ValueOpening) :
    WProtectedFrameAt supply
      (DM.extendSchemeOpening base supply scheme opening) prevailing
      frames frontier :=
  ⟨WContextFrames.extendSchemeOpening opening frame.contexts
      frame.contextsBounded,
    WTypeFrame.extendSchemeOpening opening frame.types frame.frontierBounded,
    frame.contextsBounded, frame.frontierBounded⟩

/-- Extend the residual at one canonical opening without invalidating the W
frame that preceded the variable occurrence. -/
theorem WFrameAt.extendSchemeOpening
    {base : Subst} {supply : InferenceBase.FreshSupply}
    {algorithmContext : Context} {selectedContext : SCtx}
    {frontier : List (Ty × STy)} {scheme : Scheme}
    (frame : WFrameAt supply base algorithmContext selectedContext frontier)
    (opening : (scheme.applyMeta base).ValueOpening) :
    WFrame (extendSchemeOpening base supply scheme opening)
      algorithmContext selectedContext frontier :=
  ⟨WContextRel.extendSchemeOpening opening frame.contexts frame.contextBounded,
    WTypeFrame.extendSchemeOpening opening frame.types frame.frontierBounded⟩

/-- Monomorphic schemes are related exactly when their displayed types are
related by the residual. -/
theorem SScheme.mono_realizedBy
    {post : Subst} {algorithm : Ty} {selected : STy}
    (equation : post.apply algorithm = selected.emb) :
    (SScheme.mono selected).RealizedBy post (Scheme.mono algorithm) := by
  intro target instantiation
  have targetEq : target = selected := by
    rcases instantiation with ⟨chosen, support, result⟩
    have chosenId : selected.applySubst chosen = selected := by
      calc
        selected.applySubst chosen = selected.applySubst SSubst.id := by
          apply STy.applySubst_eq_of_ftv_agree
          intro name _free
          exact support name (by simp [SScheme.mono])
        _ = selected := STy.applySubst_id selected
    simpa [SScheme.mono, chosenId] using result.symm
  subst target
  rw [Scheme.applyMeta_mono]
  rw [equation]
  exact Scheme.mono_valueFlowInst selected.emb

/-- Extend a W frame by a monomorphic binder and protect the same type pair
for the recursive call. -/
theorem WFrame.consMono
    {post : Subst} {algorithmContext : Context} {selectedContext : SCtx}
    {frontier : List (Ty × STy)} {name : String}
    {algorithm : Ty} {selected : STy}
    (equation : post.apply algorithm = selected.emb)
    (frame : WFrame post algorithmContext selectedContext frontier) :
    WFrame post
      ((name, Scheme.mono algorithm) :: algorithmContext)
      ((name, SScheme.mono selected) :: selectedContext)
      ((algorithm, selected) :: frontier) :=
  ⟨WContextRel.cons rfl (SScheme.mono_realizedBy equation) frame.contexts,
    WTypeFrame.cons equation frame.types⟩

/-! ## Structural W constructors -/

/-- The variable constructor opens the algorithm scheme canonically and
extends the shared residual only at the newly allocated opening interval. -/
theorem w_var_complete
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext normalizedContext : Context}
    {selectedContext : SCtx} {frontier : List (Ty × STy)}
    {post : Subst} {name : String} {selectedScheme : SScheme}
    {selectedTarget : STy}
    (frame : WFrameAt supply post normalizedContext selectedContext frontier)
    (normalized : rawContext.applySubst prevailing = normalizedContext)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget) :
    ∃ (rawTarget : Ty) (successor : InferenceBase.FreshSupply)
        (post' : Subst),
      DemandSynth signature supply prevailing rawContext (.var name)
        rawTarget successor prevailing ∧
      WFrameAt successor post' normalizedContext selectedContext
        ((prevailing.apply rawTarget, selectedTarget) :: frontier) := by
  obtain ⟨scheme, lookup, schemeCapArity, realizes⟩ := frame.contexts found
  have selectedUse := realizes instantiation
  let opening := Classical.choose selectedUse
  let post' := extendSchemeOpening post supply scheme opening
  let rawTarget := (InferenceBase.instantiateScheme supply scheme).value
  let successor := (InferenceBase.instantiateScheme supply scheme).supply
  have schemeBounded := frame.contextBounded.find? lookup
  have normalizedFixed : normalizedContext.applySubst prevailing =
      normalizedContext := by
    rw [← normalized, ← Context.applySubst_seq,
      DemandTypingInferenceCompletenessTraversal.subst_seq_self_eq_of_idempotent
        prevailingIdempotent]
  have schemeFixed : scheme.applyMeta prevailing = scheme := by
    have lookupAfter := congrArg (Context.find? · name) normalizedFixed
    rw [Context.find?_applySubst, lookup] at lookupAfter
    exact Option.some.inj (by simpa using lookupAfter)
  have rawFixed : prevailing.apply rawTarget = rawTarget := by
    have transported :=
      DemandTypingInferenceCompletenessContext.instantiateScheme_applyMeta_bounded
        supply scheme prevailing prevailingBounded
    rw [schemeFixed] at transported
    exact transported.symm
  have targetEquation : post'.apply (prevailing.apply rawTarget) =
      selectedTarget.emb := by
    rw [rawFixed]
    exact canonicalSchemeOpening_principal_relative post supply scheme
      schemeBounded selectedUse
  have oldFrame : WFrame post' normalizedContext selectedContext frontier := by
    exact frame.extendSchemeOpening opening
  have supplyExtends : SupplyExtends supply successor :=
    SupplyExtends.instantiateScheme supply scheme
  have rawBounded : rawTarget.BoundedBy successor := by
    exact Scheme.freshInstantiate_value_boundedBy schemeBounded
  refine ⟨rawTarget, successor, post', ?_, ?_⟩
  · subst normalizedContext
    exact DemandSynth.var lookup
  · refine
      { contexts := oldFrame.contexts
        types := WTypeFrame.cons targetEquation oldFrame.types
        contextBounded := frame.contextBounded.mono supplyExtends
        frontierBounded := ?_ }
    intro pair member
    rcases List.mem_cons.mp member with equality | oldMember
    · cases equality
      rw [rawFixed]
      exact rawBounded
    · exact (frame.frontierBounded pair oldMember).mono supplyExtends

/-- Multi-context form of `w_var_complete`.  Canonical opening changes the
shared residual only on the fresh interval, so all protected contexts (not
just the active one) survive the variable occurrence. -/
theorem w_var_protected_complete
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext : Context}
    {selectedContext : SCtx} {frames : List (Context × SCtx)}
    {frontier : List (Ty × STy)} {post : Subst}
    {name : String} {selectedScheme : SScheme} {selectedTarget : STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (active : (rawContext, selectedContext) ∈ frames)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget) :
    ∃ (rawTarget : Ty) (successor : InferenceBase.FreshSupply)
        (post' : Subst),
      DemandSynth signature supply prevailing rawContext (.var name)
        rawTarget successor prevailing ∧
      WProtectedFrameAt successor post' prevailing frames
        ((prevailing.apply rawTarget, selectedTarget) :: frontier) := by
  let activeFrame := frame.project active
  obtain ⟨scheme, lookup, _schemeCapArity, realizes⟩ :=
    activeFrame.contexts found
  have selectedUse := realizes instantiation
  let opening := Classical.choose selectedUse
  let post' := extendSchemeOpening post supply scheme opening
  let rawTarget := (InferenceBase.instantiateScheme supply scheme).value
  let successor := (InferenceBase.instantiateScheme supply scheme).supply
  have schemeBounded := activeFrame.contextBounded.find? lookup
  have normalizedFixed :
      (rawContext.applySubst prevailing).applySubst prevailing =
        rawContext.applySubst prevailing := by
    rw [← Context.applySubst_seq,
      DemandTypingInferenceCompletenessTraversal.subst_seq_self_eq_of_idempotent
        prevailingIdempotent]
  have schemeFixed : scheme.applyMeta prevailing = scheme := by
    have lookupAfter :=
      congrArg (Context.find? · name) normalizedFixed
    rw [Context.find?_applySubst, lookup] at lookupAfter
    exact Option.some.inj (by simpa using lookupAfter)
  have rawFixed : prevailing.apply rawTarget = rawTarget := by
    have transported :=
      DemandTypingInferenceCompletenessContext.instantiateScheme_applyMeta_bounded
        supply scheme prevailing prevailingBounded
    rw [schemeFixed] at transported
    exact transported.symm
  have targetEquation : post'.apply (prevailing.apply rawTarget) =
      selectedTarget.emb := by
    rw [rawFixed]
    exact canonicalSchemeOpening_principal_relative post supply scheme
      schemeBounded selectedUse
  have oldFrame : WProtectedFrameAt supply post' prevailing frames frontier :=
    frame.extendSchemeOpening opening
  have supplyExtends : SupplyExtends supply successor :=
    SupplyExtends.instantiateScheme supply scheme
  have rawBounded : rawTarget.BoundedBy successor :=
    Scheme.freshInstantiate_value_boundedBy schemeBounded
  refine ⟨rawTarget, successor, post', DemandSynth.var lookup, ?_⟩
  refine
    { contexts := oldFrame.contexts
      types := WTypeFrame.cons targetEquation oldFrame.types
      contextsBounded := fun member =>
        (oldFrame.contextsBounded member).mono supplyExtends
      frontierBounded := ?_ }
  intro pair member
  rcases List.mem_cons.mp member with equality | oldMember
  · cases equality
    rw [rawFixed]
    exact rawBounded
  · exact (oldFrame.frontierBounded pair oldMember).mono supplyExtends

@[simp] theorem DDLedger.markSchemeInstance_eq_self_of_capArity_zero
    (ledger : CapabilityOriginLedger) (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) (empty : scheme.capArity = 0) :
    DDLedger.markSchemeInstance ledger supply scheme = ledger := by
  unfold DDLedger.markSchemeInstance
  rw [Scheme.canonicalCapImages_eq_nil_of_capArity_zero supply scheme empty]
  simp [CapabilityOriginLedger.setOrigins]

/-- Certified variable branch, including the origin and terminal-audit
pieces required by public `SourceTyping`. -/
theorem w_var_certified_complete
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext normalizedContext : Context}
    {selectedContext : SCtx} {frontier : List (Ty × STy)}
    {post : Subst} {name : String} {selectedScheme : SScheme}
    {selectedTarget : STy}
    (frame : WFrameAt supply post normalizedContext selectedContext frontier)
    (normalized : rawContext.applySubst prevailing = normalizedContext)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent)
    (found : selectedContext.find? name = some selectedScheme)
    (instantiation : selectedScheme.Inst selectedTarget) :
    ∃ (rawTarget : Ty) (successor : InferenceBase.FreshSupply)
        (post' : Subst)
        (derived : DemandSynth signature supply prevailing rawContext
          (.var name) rawTarget successor prevailing)
        (origin : DemandSynthOrigin signature derived [] []),
      Nonempty (DemandSynthTerminalAudit prevailing signature origin) ∧
      WFrameAt successor post' normalizedContext selectedContext
        ((prevailing.apply rawTarget, selectedTarget) :: frontier) := by
  obtain ⟨scheme, lookup, schemeCapArity, _realizes⟩ := frame.contexts found
  obtain ⟨rawTarget, successor, post', derived, resultFrame⟩ :=
    w_var_complete (signature := signature) frame normalized
      prevailingBounded prevailingIdempotent
      found instantiation
  cases derived with
  | @var _ _ _ _ inferredScheme inferredLookup =>
      have inferredNormalized : normalizedContext.find? name =
          some inferredScheme := by
        rw [← normalized]
        exact inferredLookup
      have schemeEq : inferredScheme = scheme := by
        exact Option.some.inj (inferredNormalized.symm.trans lookup)
      subst inferredScheme
      have ledgerEq : DDLedger.markSchemeInstance [] supply scheme = [] :=
        DDLedger.markSchemeInstance_eq_self_of_capArity_zero
          [] supply scheme schemeCapArity
      let canonical : DemandSynth signature supply prevailing rawContext
          (.var name) (InferenceBase.instantiateScheme supply scheme).value
          (InferenceBase.instantiateScheme supply scheme).supply prevailing :=
        DemandSynth.var inferredLookup
      let OriginAudit := fun (ledger : CapabilityOriginLedger) =>
        ∃ origin : DemandSynthOrigin signature
            canonical [] ledger,
          Nonempty (DemandSynthTerminalAudit prevailing signature origin)
      let originMarked := DemandSynthOrigin.var (signature := signature)
        (q := supply) (S := prevailing) (context := rawContext)
        (ledger := []) inferredLookup
      let auditMarked : DemandSynthTerminalAudit prevailing signature
          originMarked := DemandSynthTerminalAudit.var
            (lookup := inferredLookup)
      let pkgMarked : OriginAudit
          (DDLedger.markSchemeInstance [] supply scheme) :=
        ⟨originMarked, ⟨auditMarked⟩⟩
      let pkg : OriginAudit [] := ledgerEq ▸ pkgMarked
      obtain ⟨origin, audit⟩ := pkg
      exact ⟨(InferenceBase.instantiateScheme supply scheme).value,
        (InferenceBase.instantiateScheme supply scheme).supply, post',
        canonical, origin, audit,
        resultFrame⟩

/-- Literals consume no supply and preserve the whole residual frame. -/
theorem w_lit_complete
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing : Subst} {rawContext normalizedContext : Context}
    {selectedContext : SCtx} {frontier : List (Ty × STy)}
    {post : Subst} {value : Int}
    (frame : WFrameAt supply post normalizedContext selectedContext frontier) :
    ∃ rawTarget post',
      DemandSynth signature supply prevailing rawContext (.lit value)
        rawTarget supply prevailing ∧
      WFrameAt supply post' normalizedContext selectedContext
        ((rawTarget, STy.int) :: frontier) := by
  refine ⟨Ty.int, post, DemandSynth.lit, ?_⟩
  refine
    { contexts := frame.contexts
      types := WTypeFrame.cons (by rfl) frame.types
      contextBounded := frame.contextBounded
      frontierBounded := ?_ }
  intro pair member
  rcases List.mem_cons.mp member with equality | oldMember
  · cases equality
    exact Ty.BoundedBy.int
  · exact frame.frontierBounded pair oldMember

end DM
end TypePM
