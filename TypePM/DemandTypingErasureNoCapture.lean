import TypePM.DemandTypingErasureTransport

/-!
# Experimental no-capture boundary for scheme substitution

This module isolates the range-hygiene condition under which the current
identifier-based `Scheme.applySubst` really composes sequentially.  It is an
experiment rather than a new public DD premise: arbitrary source contexts do
not currently carry this provenance, and the DD solver does not preserve it.
-/

namespace TypePM

/-- Images substituted for a scheme's ambient free variables do not mention
any of that scheme's locally quantified identifiers.  The target-image
capability clause is essential because an ordinary type image may contain
matcher or slot capabilities. -/
structure Scheme.NoCapture (scheme : Scheme) (S : Subst) : Prop where
  capRange : ∀ ambient, ambient ∈ scheme.fcv →
    ∀ binder, binder ∈ scheme.capBinders → binder ∉ (S.cap ambient).fcv
  targetCapRange : ∀ ambient, ambient ∈ scheme.ftv →
    ∀ binder, binder ∈ scheme.capBinders →
      binder ∉ (S.target ambient).fcv
  targetTyRange : ∀ ambient, ambient ∈ scheme.ftv →
    ∀ binder, binder ∈ scheme.tyBinders →
      binder ∉ (S.target ambient).ftv

/-- Identity introduces no binder occurrence into an ambient image. -/
theorem Scheme.NoCapture.id (scheme : Scheme) :
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
theorem Scheme.applySubst_seq_of_noCapture
    (scheme : Scheme) (earlier later : Subst)
    (hygiene : scheme.NoCapture earlier) :
    scheme.applySubst (Subst.seq later earlier) =
      (scheme.applySubst earlier).applySubst later := by
  cases scheme with
  | mk capBinders tyBinders body =>
      change Scheme.mk capBinders tyBinders _ =
        Scheme.mk capBinders tyBinders _
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
              (Scheme.mk capBinders tyBinders body).fcv :=
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
                (Scheme.mk capBinders tyBinders body).ftv :=
              List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
            have outside : image ∉ capBinders := by
              intro imageBound
              exact hygiene.targetCapRange ambient ambientFree image
                imageBound imageMem
            simp [CapSubst.mask, outside]
          · intro image imageMem
            have ambientFree : ambient ∈
                (Scheme.mk capBinders tyBinders body).ftv :=
              List.mem_filter.mpr ⟨ambientMem, by simpa using bound⟩
            have outside : image ∉ tyBinders := by
              intro imageBound
              exact hygiene.targetTyRange ambient ambientFree image
                imageBound imageMem
            simp [TySubst.mask, outside]

end TypePM
