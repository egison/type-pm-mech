import TypePM.DamasMilnerW

/-!
# Tuple traversal for Damas--Milner Algorithm W completeness

Tuple synthesis is left-to-right and therefore cannot be reduced to a
collection of independent expression runs.  This module isolates the small
structural layer needed by the mutual completeness proof: the final residual
must realize every raw component at the final prevailing substitution, after
which the component equations can be folded into the product equation added
to the protected W frame.
-/

namespace TypePM
namespace DM

/-! ## Pointwise terminal equations -/

/-- A raw target list and a selected simple-type list are realized pointwise
by one final prevailing substitution and one final W residual.  The inductive
shape records exact order and arity, matching `DM.Typings` and
`DemandSynths`. -/
inductive WTargetListRel (post prevailing : Subst) :
    List Ty → List STy → Prop where
  | nil : WTargetListRel post prevailing [] []
  | cons {raw : Ty} {selected : STy}
      {rawTargets : List Ty} {selectedTargets : List STy} :
      post.apply (prevailing.apply raw) = selected.emb →
      WTargetListRel post prevailing rawTargets selectedTargets →
      WTargetListRel post prevailing
        (raw :: rawTargets) (selected :: selectedTargets)

/-- Pointwise realization fixes the common list length. -/
theorem WTargetListRel.length_eq
    {post prevailing : Subst} {rawTargets : List Ty}
    {selectedTargets : List STy}
    (relation : WTargetListRel post prevailing rawTargets selectedTargets) :
    rawTargets.length = selectedTargets.length := by
  induction relation with
  | nil => rfl
  | cons _ _ induction => simp [induction]

/-- A solver factorization transports all earlier tuple-component equations
to the new prevailing substitution and residual.  This is the algebraic step
used between successive left-to-right components. -/
theorem WTargetListRel.applySubst
    {post prevailing delta residual : Subst}
    {rawTargets : List Ty} {selectedTargets : List STy}
    (relation : WTargetListRel post prevailing rawTargets selectedTargets)
    (factor : post = Subst.seq residual delta) :
    WTargetListRel residual (Subst.seq delta prevailing)
      rawTargets selectedTargets := by
  induction relation with
  | nil => exact WTargetListRel.nil
  | cons head tail induction =>
      apply WTargetListRel.cons
      · rw [Subst.seq_apply, ← Subst.seq_apply, ← factor]
        exact head
      · exact induction

/-- Pointwise terminal equations fold to the terminal product equation. -/
theorem WTargetListRel.productEquation
    {post prevailing : Subst} {rawTargets : List Ty}
    {selectedTargets : List STy}
    (relation : WTargetListRel post prevailing rawTargets selectedTargets) :
    post.apply (prevailing.apply (.prod rawTargets)) =
      (STy.prod selectedTargets).emb := by
  induction relation with
  | nil => simp [STy.emb, STy.embList]
  | @cons raw selected rawTargets selectedTargets head tail induction =>
      simp only [Subst.apply_prod, List.map_cons, STy.emb, STy.embList]
      rw [head]
      apply congrArg Ty.prod
      apply congrArg (List.cons selected.emb)
      simp only [Subst.apply_prod, STy.emb] at induction
      have tailEquality := Ty.prod.inj induction
      simpa only [List.map_map, Function.comp_def] using tailEquality

/-- A bounded final prevailing substitution maps every bounded raw component
to a bounded normalized component. -/
theorem normalizedTargets_bounded
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    {rawTargets : List Ty}
    (prevailingBounded : prevailing.BoundedBy supply)
    (rawBounded : ∀ raw ∈ rawTargets, raw.BoundedBy supply) :
    ∀ raw ∈ rawTargets, (prevailing.apply raw).BoundedBy supply := by
  intro raw membership
  exact prevailingBounded.apply (rawBounded raw membership)

/-! ## Mutual-completeness list results -/

/-- Output package for the `DM.Typings` half of the raw Algorithm W
completeness induction.  The input execution state and syntax are indices;
the final state, raw targets, residual, and protected frontier are genuine
outputs.  Origin ledgers are empty throughout the DM fragment. -/
structure WTypingsCompleteResult
    (signature : FrozenSig) (supply : InferenceBase.FreshSupply)
    (prevailing : Subst) (rawContext : Context)
    (expressions : List Expr) (selectedTargets : List STy)
    (frames : List (Context × SCtx)) where
  successor : InferenceBase.FreshSupply
  prevailing' : Subst
  rawTargets : List Ty
  post : Subst
  frontier : List (Ty × STy)
  derived : DemandSynths signature supply prevailing rawContext
    expressions rawTargets successor prevailing'
  origin : DemandSynthsOrigin signature derived [] []
  equations : WTargetListRel post prevailing' rawTargets selectedTargets
  postAdmissible : AdmissiblePost [] post
  prevailingBounded : prevailing'.BoundedBy successor
  prevailingIdempotent : prevailing'.Idempotent
  frame : WProtectedFrameAt successor post prevailing' frames frontier

/-- Empty-list output package.  It preserves the incoming W frame and state
verbatim and creates the empty chronological origin tree. -/
def WTypingsCompleteResult.nil
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (postAdmissible : AdmissiblePost [] post)
    (prevailingBounded : prevailing.BoundedBy supply)
    (prevailingIdempotent : prevailing.Idempotent) :
    WTypingsCompleteResult signature supply prevailing rawContext [] []
      frames where
  successor := supply
  prevailing' := prevailing
  rawTargets := []
  post := post
  frontier := frontier
  derived := DemandSynths.nil
  origin := DemandSynthsOrigin.nil
  equations := WTargetListRel.nil
  postAdmissible := postAdmissible
  prevailingBounded := prevailingBounded
  prevailingIdempotent := prevailingIdempotent
  frame := frame

/-- Package one completed head followed by a completed chronological tail.
The tail owns the final state and frame.  Its traversal has already
transported the protected head equation, which is exposed as the single
`headEquation` premise and prepended to the tail's pointwise relation. -/
def WTypingsCompleteResult.cons
    {signature : FrozenSig}
    {supply middle : InferenceBase.FreshSupply}
    {prevailing middleSubst : Subst} {rawContext : Context}
    {expression : Expr} {expressions : List Expr}
    {raw : Ty} {selected : STy} {selectedTargets : List STy}
    {head : DemandSynth signature supply prevailing rawContext expression raw
      middle middleSubst}
    (headOrigin : DemandSynthOrigin signature head [] [])
    (tail : WTypingsCompleteResult signature middle middleSubst rawContext
      expressions selectedTargets frames)
    (headEquation :
      tail.post.apply (tail.prevailing'.apply raw) = selected.emb) :
    WTypingsCompleteResult signature supply prevailing rawContext
      (expression :: expressions) (selected :: selectedTargets) frames where
  successor := tail.successor
  prevailing' := tail.prevailing'
  rawTargets := raw :: tail.rawTargets
  post := tail.post
  frontier := tail.frontier
  derived := DemandSynths.cons head tail.derived
  origin := DemandSynthsOrigin.cons headOrigin tail.origin
  equations := WTargetListRel.cons headEquation tail.equations
  postAdmissible := tail.postAdmissible
  prevailingBounded := tail.prevailingBounded
  prevailingIdempotent := tail.prevailingIdempotent
  frame := tail.frame

/-! ## Product protection -/

/-- Protect the product target assembled from a terminally realized component
list.  Component boundedness is stated on the final normalized views because
that is exactly what the chronological list traversal establishes. -/
theorem WProtectedFrameAt.protectTupleTarget
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {rawTargets : List Ty} {selectedTargets : List STy}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (relation : WTargetListRel post prevailing rawTargets selectedTargets)
    (bounded : ∀ raw ∈ rawTargets,
      (prevailing.apply raw).BoundedBy supply) :
    WProtectedFrameAt supply post prevailing frames
      ((prevailing.apply (.prod rawTargets), .prod selectedTargets) ::
        frontier) := by
  refine
    { contexts := frame.contexts
      types := WTypeFrame.cons relation.productEquation frame.types
      contextsBounded := frame.contextsBounded
      frontierBounded := ?_ }
  intro pair membership
  rcases List.mem_cons.mp membership with equality | oldMember
  · cases equality
    rw [Subst.apply_prod]
    exact Ty.BoundedBy.prodOfForall (by
      intro normalized normalizedMember
      rw [List.mem_map] at normalizedMember
      obtain ⟨raw, rawMember, rfl⟩ := normalizedMember
      exact bounded raw rawMember)
  · exact frame.frontierBounded pair oldMember

/-! ## Executable tuple constructor -/

/-- Finish the tuple constructor once the mutual list-completeness induction
has produced its chronological `DemandSynths` run and the final pointwise W
equations.  This is the frame-threading combinator used by the `Typing.tuple`
case; it performs no additional solver cut and preserves the final supply and
prevailing substitution exactly. -/
theorem w_tuple_complete
    {signature : FrozenSig} {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' post : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {expressions : List Expr} {rawTargets : List Ty}
    {selectedTargets : List STy}
    (components : DemandSynths signature supply prevailing rawContext
      expressions rawTargets successor prevailing')
    (frame : WProtectedFrameAt successor post prevailing' frames frontier)
    (relation : WTargetListRel post prevailing'
      rawTargets selectedTargets)
    (bounded : ∀ raw ∈ rawTargets,
      (prevailing'.apply raw).BoundedBy successor) :
    DemandSynth signature supply prevailing rawContext
        (.tuple expressions) (.prod rawTargets) successor prevailing' ∧
      WProtectedFrameAt successor post prevailing' frames
        ((prevailing'.apply (.prod rawTargets), .prod selectedTargets) ::
          frontier) := by
  exact ⟨DemandSynth.tuple components,
    frame.protectTupleTarget relation bounded⟩

/-- Empty list traversal, with the pointwise terminal relation needed by the
tuple finalizer. -/
theorem w_typings_nil
    {signature : FrozenSig} {supply : InferenceBase.FreshSupply}
    {prevailing post : Subst} {rawContext : Context} :
    DemandSynths signature supply prevailing rawContext [] []
        supply prevailing ∧
      WTargetListRel post prevailing [] [] := by
  exact ⟨DemandSynths.nil, WTargetListRel.nil⟩

/-- Generic chronological cons packaging.  The recursive completeness proof
supplies the final head equation after the tail run has transported the
protected head pair; this combinator records that equation together with the
tail equations without changing their execution evidence. -/
theorem w_typings_cons
    {signature : FrozenSig}
    {supply middle successor : InferenceBase.FreshSupply}
    {prevailing middleSubst prevailing' post : Subst}
    {rawContext : Context} {expression : Expr} {expressions : List Expr}
    {raw : Ty} {rawTargets : List Ty} {selected : STy}
    {selectedTargets : List STy}
    (head : DemandSynth signature supply prevailing rawContext expression raw
      middle middleSubst)
    (tail : DemandSynths signature middle middleSubst rawContext expressions
      rawTargets successor prevailing')
    (headEquation : post.apply (prevailing'.apply raw) = selected.emb)
    (tailEquations : WTargetListRel post prevailing'
      rawTargets selectedTargets) :
    DemandSynths signature supply prevailing rawContext
        (expression :: expressions) (raw :: rawTargets)
        successor prevailing' ∧
      WTargetListRel post prevailing' (raw :: rawTargets)
        (selected :: selectedTargets) := by
  exact ⟨DemandSynths.cons head tail,
    WTargetListRel.cons headEquation tailEquations⟩

/-! ## Origin and terminal-audit composition -/

/-- The empty chronological traversal carries the empty origin and terminal
audit trees.  This is stated with `Nonempty`, matching the public certified
run interface and keeping proof-relevant audit witnesses opaque in `Prop`. -/
theorem w_typings_nil_certified
    {terminal : Subst} {signature : FrozenSig}
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    {rawContext : Context} {ledger : CapabilityOriginLedger} :
    ∃ origin : DemandSynthsOrigin signature
        (DemandSynths.nil (q := supply) (S := prevailing) (Γ := rawContext))
        ledger ledger,
      Nonempty (DemandSynthsTerminalAudit terminal signature origin) := by
  let origin := DemandSynthsOrigin.nil (signature := signature)
    (q := supply) (S := prevailing) (context := rawContext) (ledger := ledger)
  exact ⟨origin, ⟨DemandSynthsTerminalAudit.nil⟩⟩

/-- Compose the provenance and recursive terminal audit of one synthesized
head with those of the chronological tail. -/
theorem w_typings_cons_certified
    {terminal : Subst} {signature : FrozenSig}
    {supply middle successor : InferenceBase.FreshSupply}
    {prevailing middleSubst prevailing' : Subst}
    {rawContext : Context} {expression : Expr} {expressions : List Expr}
    {raw : Ty} {rawTargets : List Ty}
    {ledger middleLedger finalLedger : CapabilityOriginLedger}
    {head : DemandSynth signature supply prevailing rawContext expression raw
      middle middleSubst}
    {tail : DemandSynths signature middle middleSubst rawContext expressions
      rawTargets successor prevailing'}
    (headOrigin : DemandSynthOrigin signature head ledger middleLedger)
    (tailOrigin : DemandSynthsOrigin signature tail middleLedger finalLedger)
    (headAudit : Nonempty
      (DemandSynthTerminalAudit terminal signature headOrigin))
    (tailAudit : Nonempty
      (DemandSynthsTerminalAudit terminal signature tailOrigin)) :
    ∃ origin : DemandSynthsOrigin signature
        (DemandSynths.cons head tail) ledger finalLedger,
      Nonempty (DemandSynthsTerminalAudit terminal signature origin) := by
  rcases headAudit with ⟨headAudit⟩
  rcases tailAudit with ⟨tailAudit⟩
  let origin := DemandSynthsOrigin.cons headOrigin tailOrigin
  exact ⟨origin, ⟨DemandSynthsTerminalAudit.cons headAudit tailAudit⟩⟩

/-- One-stop constructor for the mutual `DM.Typings.cons` branch.  It keeps
the execution, W equations, provenance, and terminal audit synchronized at
the same dependent `DemandSynths.cons` witness. -/
theorem w_typings_cons_complete
    {terminal : Subst} {signature : FrozenSig}
    {supply middle successor : InferenceBase.FreshSupply}
    {prevailing middleSubst prevailing' post : Subst}
    {rawContext : Context} {expression : Expr} {expressions : List Expr}
    {raw : Ty} {rawTargets : List Ty} {selected : STy}
    {selectedTargets : List STy}
    {ledger middleLedger finalLedger : CapabilityOriginLedger}
    {head : DemandSynth signature supply prevailing rawContext expression raw
      middle middleSubst}
    {tail : DemandSynths signature middle middleSubst rawContext expressions
      rawTargets successor prevailing'}
    (headEquation : post.apply (prevailing'.apply raw) = selected.emb)
    (tailEquations : WTargetListRel post prevailing'
      rawTargets selectedTargets)
    (headOrigin : DemandSynthOrigin signature head ledger middleLedger)
    (tailOrigin : DemandSynthsOrigin signature tail middleLedger finalLedger)
    (headAudit : Nonempty
      (DemandSynthTerminalAudit terminal signature headOrigin))
    (tailAudit : Nonempty
      (DemandSynthsTerminalAudit terminal signature tailOrigin)) :
    ∃ derived : DemandSynths signature supply prevailing rawContext
        (expression :: expressions) (raw :: rawTargets)
        successor prevailing',
      WTargetListRel post prevailing' (raw :: rawTargets)
          (selected :: selectedTargets) ∧
        ∃ origin : DemandSynthsOrigin signature derived ledger finalLedger,
          Nonempty
            (DemandSynthsTerminalAudit terminal signature origin) := by
  let derived := DemandSynths.cons head tail
  obtain ⟨origin, audit⟩ := w_typings_cons_certified
    headOrigin tailOrigin headAudit tailAudit
  exact ⟨derived, WTargetListRel.cons headEquation tailEquations,
    origin, audit⟩

/-- Certified tuple finalization.  Since tuple syntax introduces no origin or
terminal-sensitive event of its own, both certificates are exactly wrappers
around the already-certified left-to-right child traversal. -/
theorem w_tuple_certified_complete
    {terminal : Subst} {signature : FrozenSig}
    {supply successor : InferenceBase.FreshSupply}
    {prevailing prevailing' post : Subst} {rawContext : Context}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {expressions : List Expr} {rawTargets : List Ty}
    {selectedTargets : List STy}
    {ledger finalLedger : CapabilityOriginLedger}
    {components : DemandSynths signature supply prevailing rawContext
      expressions rawTargets successor prevailing'}
    (childrenOrigin : DemandSynthsOrigin signature components
      ledger finalLedger)
    (childrenAudit : Nonempty
      (DemandSynthsTerminalAudit terminal signature childrenOrigin))
    (frame : WProtectedFrameAt successor post prevailing' frames frontier)
    (relation : WTargetListRel post prevailing'
      rawTargets selectedTargets)
    (bounded : ∀ raw ∈ rawTargets,
      (prevailing'.apply raw).BoundedBy successor) :
    ∃ origin : DemandSynthOrigin signature
        (DemandSynth.tuple components) ledger finalLedger,
      Nonempty (DemandSynthTerminalAudit terminal signature origin) ∧
        WProtectedFrameAt successor post prevailing' frames
          ((prevailing'.apply (.prod rawTargets), .prod selectedTargets) ::
            frontier) := by
  rcases childrenAudit with ⟨childrenAudit⟩
  let origin := DemandSynthOrigin.tuple childrenOrigin
  exact ⟨origin, ⟨DemandSynthTerminalAudit.tuple childrenAudit⟩,
    frame.protectTupleTarget relation bounded⟩

end DM
end TypePM
