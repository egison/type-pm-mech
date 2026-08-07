import TypePM.InferenceTraceFactorization

/-!
# Residual transport across capability-export freezing

`freezeCapabilityExport` selectively changes the surviving structural leaves
of one exported payload to `renameOnly`; it does not freeze the whole current
ledger.  Consequently, residual admissibility cannot be transported across
that state change without inspecting the residual at the selected leaves.

This module states the exact local condition.  Every selected leaf must already
have a variable-valued residual image, and that image must be non-structural in
the updated ledger.  Existing non-selected obligations are preserved because a
`renameOnly` override can remove, but never introduce, structural flexibility.
The stronger legacy terminal condition `FixesCapVars` discharges the local
condition as a corollary; the executable guard itself is not weakened here.
-/

namespace TypePM

namespace CapabilityOriginLedger

/-- A batch override leaves every variable outside the batch unchanged. -/
theorem originOf_setOrigins_of_not_mem
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (queried : CapVar) (origin : CapabilityOrigin)
    (notMember : queried ∉ varIds) :
    (ledger.setOrigins varIds origin).originOf queried =
      ledger.originOf queried := by
  induction varIds generalizing ledger with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have headDifferent : head ≠ queried := by
        intro same
        subst head
        exact notMember (by simp)
      have restNotMember : queried ∉ rest := by
        intro membership
        exact notMember (by simp [membership])
      rw [setOrigins,
        originOf_setOrigin_of_ne _ head queried headDifferent]
      exact inductionHypothesis ledger restNotMember

/-- Selectively overriding entries by `renameOnly` cannot turn an already
non-structural origin into a structural one. -/
theorem originOf_setOrigins_renameOnly_ne_structuralFlexible
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (varId : CapVar)
    (nonStructural :
      ledger.originOf varId ≠ .structuralFlexible) :
    (ledger.setOrigins varIds .renameOnly).originOf varId ≠
      .structuralFlexible := by
  by_cases membership : varId ∈ varIds
  · rw [originOf_setOrigins_of_mem ledger varIds varId .renameOnly membership]
    simp
  · rw [originOf_setOrigins_of_not_mem ledger varIds varId .renameOnly
      membership]
    exact nonStructural

end CapabilityOriginLedger

namespace AdmissibleCapPost

/-- Transport an admissible capability residual across a selective export
freeze.  The premise records exactly what was unconstrained at a selected
structurally-flexible leaf before the freeze: its residual image must now be a
safe rename in the updated ledger. -/
theorem setOrigins_renameOnly
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {varIds : List CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (selectedImages :
      ∀ varId, varId ∈ varIds →
        ∃ image,
          post varId = .var image ∧
            (ledger.setOrigins varIds .renameOnly).originOf image ≠
              .structuralFlexible) :
    AdmissibleCapPost
      (ledger.setOrigins varIds .renameOnly) post := by
  intro varId
  by_cases selected : varId ∈ varIds
  · have selectedOrigin :
        (ledger.setOrigins varIds .renameOnly).originOf varId =
          .renameOnly :=
      CapabilityOriginLedger.originOf_setOrigins_of_mem
        ledger varIds varId .renameOnly selected
    simpa only [selectedOrigin] using selectedImages varId selected
  · have unchanged :
        (ledger.setOrigins varIds .renameOnly).originOf varId =
          ledger.originOf varId :=
      CapabilityOriginLedger.originOf_setOrigins_of_not_mem
        ledger varIds varId .renameOnly selected
    rw [unchanged]
    cases oldOrigin : ledger.originOf varId with
    | rigid =>
        exact admissible.rigid oldOrigin
    | renameOnly =>
        rcases admissible.renameOnly oldOrigin with
          ⟨image, imageEquation, imageSafe⟩
        exact ⟨image, imageEquation,
          CapabilityOriginLedger.originOf_setOrigins_renameOnly_ne_structuralFlexible
            ledger varIds image imageSafe⟩
    | structuralFlexible =>
        trivial

/-- The legacy pointwise-fixing condition is a sufficient, deliberately
stronger bridge across a selective rename-only freeze. -/
theorem setOrigins_renameOnly_of_fixes
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {varIds : List CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (fixes : Inference.FixesCapVars post varIds) :
    AdmissibleCapPost
      (ledger.setOrigins varIds .renameOnly) post := by
  apply admissible.setOrigins_renameOnly
  intro varId membership
  refine ⟨varId, fixes varId membership, ?_⟩
  rw [CapabilityOriginLedger.originOf_setOrigins_of_mem
    ledger varIds varId .renameOnly membership]
  simp

end AdmissibleCapPost

namespace AdmissiblePost

/-- Paired residual transport across a selective export freeze.  The target
component remains unrestricted, as in `AdmissiblePost` itself. -/
theorem setOrigins_renameOnly
    {ledger : CapabilityOriginLedger} {post : Subst}
    {varIds : List CapVar}
    (admissible : AdmissiblePost ledger post)
    (selectedImages :
      ∀ varId, varId ∈ varIds →
        ∃ image,
          post.cap varId = .var image ∧
            (ledger.setOrigins varIds .renameOnly).originOf image ≠
              .structuralFlexible) :
    AdmissiblePost (ledger.setOrigins varIds .renameOnly) post :=
  { cap := admissible.cap.setOrigins_renameOnly selectedImages }

/-- Paired form of the fixed-leaf bridge used by the current terminal audit. -/
theorem setOrigins_renameOnly_of_fixes
    {ledger : CapabilityOriginLedger} {post : Subst}
    {varIds : List CapVar}
    (admissible : AdmissiblePost ledger post)
    (fixes : Inference.FixesCapVars post.cap varIds) :
    AdmissiblePost (ledger.setOrigins varIds .renameOnly) post :=
  { cap := admissible.cap.setOrigins_renameOnly_of_fixes fixes }

end AdmissiblePost

namespace Inference

/-- Export freezing performs precisely the selective rename-only ledger
override used by the generic transport theorem. -/
@[simp] theorem InferState.freezeCapabilityExport_capabilityOrigins
    (state : InferState) (capImages : List CapVar)
    (exportedPayload : Ty) :
    (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins =
      state.capabilityOrigins.setOrigins
        (capabilityExportLeaves state capImages exportedPayload)
        .renameOnly := by
  rfl

/-- Transport a residual across the exact state transition performed by
`freezeCapabilityExport`.  Safety of a rename is checked in the post-freeze
ledger, so it cannot target an unexported structural local. -/
theorem InferState.freezeCapabilityExport_admissiblePost
    {state : InferState} {post : Subst}
    {capImages : List CapVar} {exportedPayload : Ty}
    (admissible : AdmissiblePost state.capabilityOrigins post)
    (selectedImages :
      ∀ varId,
        varId ∈ capabilityExportLeaves state capImages exportedPayload →
          ∃ image,
            post.cap varId = .var image ∧
              ((state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
                  ).originOf image ≠ CapabilityOrigin.structuralFlexible) :
    AdmissiblePost
      (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
      post := by
  rw [InferState.freezeCapabilityExport_capabilityOrigins] at selectedImages ⊢
  exact admissible.setOrigins_renameOnly selectedImages

/-- The existing fixed-producer condition is sufficient for residual
admissibility after export freezing.  This theorem does not replace or relax
the terminal check; it only exposes its ledger-transport consequence. -/
theorem InferState.freezeCapabilityExport_admissiblePost_of_fixes
    {state : InferState} {post : Subst}
    {capImages : List CapVar} {exportedPayload : Ty}
    (admissible : AdmissiblePost state.capabilityOrigins post)
    (fixes : FixesCapVars post.cap
      (capabilityExportLeaves state capImages exportedPayload)) :
    AdmissiblePost
      (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
      post := by
  rw [InferState.freezeCapabilityExport_capabilityOrigins]
  exact admissible.setOrigins_renameOnly_of_fixes fixes

/-- Admissibility in the post-freeze ledger exposes a safe variable rename at
each selected leaf.  This is the selective counterpart of the global
`VariablePost` bridge for `freezeAll`. -/
theorem InferState.freezeCapabilityExport_leaf_safeRename
    {state : InferState} {post : Subst}
    {capImages : List CapVar} {exportedPayload : Ty} {varId : CapVar}
    (admissible : AdmissiblePost
      (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
      post)
    (membership :
      varId ∈ capabilityExportLeaves state capImages exportedPayload) :
    ∃ image,
      post.cap varId = .var image ∧
        ((state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
            ).originOf image ≠ CapabilityOrigin.structuralFlexible := by
  exact admissible.cap.renameOnly
    (InferState.freezeCapabilityExport_origin_of_mem
      state capImages exportedPayload varId membership)

/-- Export freezing emits no solve, so a scoped trace factorization is
unchanged; the explicit selected-image premise simultaneously transports its
residual to the new ledger. -/
theorem InferState.ScopedTraceFactorization.freezeCapabilityExport
    {state : InferState} {competitor residual : Subst}
    {capImages : List CapVar} {exportedPayload : Ty}
    (factorization :
      state.ScopedTraceFactorization competitor residual)
    (residualAdmissible :
      AdmissiblePost state.capabilityOrigins residual)
    (selectedImages :
      ∀ varId,
        varId ∈ capabilityExportLeaves state capImages exportedPayload →
          ∃ image,
            residual.cap varId = .var image ∧
              ((state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
                  ).originOf image ≠ CapabilityOrigin.structuralFlexible) :
    AdmissiblePost
        (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
        residual ∧
      InferState.ScopedTraceFactorization
        (state.freezeCapabilityExport capImages exportedPayload)
        competitor residual := by
  constructor
  · exact state.freezeCapabilityExport_admissiblePost
      residualAdmissible selectedImages
  · simpa [InferState.ScopedTraceFactorization,
      InferState.freezeCapabilityExport, InferState.recordEvent] using
      factorization

/-- Fixed selected leaves give the terminal-guard specialization of scoped
factorization transport. -/
theorem InferState.ScopedTraceFactorization.freezeCapabilityExport_of_fixes
    {state : InferState} {competitor residual : Subst}
    {capImages : List CapVar} {exportedPayload : Ty}
    (factorization :
      state.ScopedTraceFactorization competitor residual)
    (residualAdmissible :
      AdmissiblePost state.capabilityOrigins residual)
    (fixes : FixesCapVars residual.cap
      (capabilityExportLeaves state capImages exportedPayload)) :
    AdmissiblePost
        (state.freezeCapabilityExport capImages exportedPayload).capabilityOrigins
        residual ∧
      InferState.ScopedTraceFactorization
        (state.freezeCapabilityExport capImages exportedPayload)
        competitor residual := by
  constructor
  · exact state.freezeCapabilityExport_admissiblePost_of_fixes
      residualAdmissible fixes
  · simpa [InferState.ScopedTraceFactorization,
      InferState.freezeCapabilityExport, InferState.recordEvent] using
      factorization

end Inference
end TypePM
