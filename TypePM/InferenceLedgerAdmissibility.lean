import TypePM.Inference

/-!
# Ledger admissibility for the one-way inference branch

Equality constraints carry admissibility directly from the origin-aware
paired kernels.  `producerToSlot` deliberately keeps the specialized
one-way `CapMatch` certificate used by reconstruction.  This module supplies
the finite-support bridge for that branch and proves that the exact restricted
`CapMatch` substitution of every emitted ledger-aware step is
origin-admissible.  A structural-domain lemma remains available as a simple
sufficient condition independent of the executable solver.
-/

namespace TypePM
namespace Inference

/-- Every variable in a finite domain is structural at this ledger cut. -/
def StructuralDomain
    (ledger : CapabilityOriginLedger) (variables : List CapVar) : Prop :=
  ∀ varId, varId ∈ variables →
    ledger.originOf varId = .structuralFlexible

/-- A substitution restricted to a structural domain respects the entire
ledger: members are unconstrained by policy, while nonmembers are fixed by
the support certificate. -/
theorem CapMatch.Bindings.toSubstWithin_admissible_of_structural
    (ledger : CapabilityOriginLedger) (variables : List CapVar)
    (bindings : CapMatch.Bindings)
    (structural : StructuralDomain ledger variables) :
    AdmissibleCapPost ledger (bindings.toSubstWithin variables) := by
  intro varId
  by_cases member : varId ∈ variables
  · rw [structural varId member]
    trivial
  · have fixed :=
      CapMatch.Bindings.toSubstWithin_support variables bindings varId member
    rw [fixed]
    cases origin : ledger.originOf varId with
    | rigid => rfl
    | renameOnly =>
        exact ⟨varId, rfl, by simp [origin]⟩
    | structuralFlexible => trivial

/-- The one-way certificate exposes the exact finite capability support used
by `CapMatch`, independently of the target mgu that follows it. -/
theorem SolveCertificate.producerToSlot_capSupport
    {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {delta : Subst}
    (certificate : SolveCertificate ledger
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget)
      delta) :
    delta.cap.SupportWithin consumerCap.fcv := by
  cases certificate with
  | producerToSlot _ _ =>
      exact CapMatch.Bindings.toSubstWithin_support _ _

/-- A successful finite check turns the unchanged one-way certificate into
an origin-admissible paired post. -/
theorem SolveCertificate.producerToSlot_admissible_of_check
    {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {delta : Subst}
    (certificate : SolveCertificate ledger
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget)
      delta)
    (checked :
      admissibleCapPostCheck ledger delta.cap consumerCap.fcv = true) :
    AdmissiblePost ledger delta :=
  { cap := AdmissibleCapPost.check_sound
      certificate.producerToSlot_capSupport checked }

/-- Under the call-site invariant that consumer variables are local
structural metas, the unchanged one-way solver also has a paired
origin-admissibility certificate. -/
theorem SolveCertificate.producerToSlot_admissible_of_structural
    {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {delta : Subst}
    (certificate : SolveCertificate ledger
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget)
      delta)
    (structural : StructuralDomain ledger consumerCap.fcv) :
    AdmissiblePost ledger delta := by
  cases certificate with
  | producerToSlot _ _ =>
      exact
        { cap :=
            CapMatch.Bindings.toSubstWithin_admissible_of_structural
              ledger consumerCap.fcv _ structural }

/-- Every producer-to-slot step returned by the ledger-aware solver has passed
the finite admissibility check on the exact restricted `CapMatch`
substitution. -/
theorem solveResolvedWithLedger_producerToSlot_admissible
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget) =
        some step) :
    AdmissiblePost ledger step.delta := by
  change solveProducerToSlotWithLedger ledger solveCount origin producerCap
      producerTarget consumerCap consumerTarget = some step at success
  unfold solveProducerToSlotWithLedger at success
  split at success
  · contradiction
  · rename_i bindings hmatch
    simp only at success
    split at success
    · rename_i checked
      split at success
      · contradiction
      · rename_i targetSubst hsolve
        have stepEquation := Option.some.inj success
        subst step
        exact
          { cap := AdmissibleCapPost.check_sound
              (CapMatch.Bindings.toSubstWithin_support _ _) checked }
    · contradiction

/-- Every local step emitted by the ledger-aware solver respects the ledger
captured at that solve cut. -/
theorem solveResolvedWithLedger_admissible
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (success : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    AdmissiblePost ledger step.delta := by
  cases constraint with
  | capEq left right =>
      change solveCapEqWithLedger ledger solveCount origin left right =
        some step at success
      unfold solveCapEqWithLedger at success
      split at success
      · contradiction
      · rename_i result hsolve
        have stepEquation := Option.some.inj success
        subst step
        exact { cap := result.admissible }
  | targetEq left right =>
      change solveTargetEqWithLedger ledger solveCount origin left right =
        some step at success
      unfold solveTargetEqWithLedger at success
      split at success
      · contradiction
      · rename_i result hsolve
        have stepEquation := Option.some.inj success
        subst step
        exact result.admissible
  | producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      exact solveResolvedWithLedger_producerToSlot_admissible success

end Inference
end TypePM
