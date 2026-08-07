import TypePM.InferenceLedgerAdmissibility

/-!
# Local factorization for ledger-aware solver steps

The legacy `SolveCertificate.capEq` and `SolveCertificate.targetEq` constructors
remain available for specification-level inspection, but executable inference
emits the origin-aware constructors.  This module states factorization only for
results returned by `solveResolvedWithLedger`; it therefore cannot silently
attribute origin-relative universality to a legacy symmetric certificate.
-/

namespace TypePM
namespace Inference

/-- A paired substitution solves the semantic part of one already-resolved
constraint.  Unlike `LocallySound`, capability equality does not require an
irrelevant identity target component from a competitor. -/
def Constraint.SolvedBy (constraint : Constraint) (post : Subst) : Prop :=
  match constraint with
  | .capEq left right => left.apply post.cap = right.apply post.cap
  | .targetEq left right => post.apply left = post.apply right
  | .producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      OneWayAt post.cap producerCap consumerCap ∧
      (producerTarget.applyCapability post.cap).applyTarget post.target =
        (consumerTarget.applyCapability post.cap).applyTarget post.target

/-- Explicitly classify the certificate constructors emitted by the
ledger-aware solver.  The two legacy symmetric constructors are intentionally
excluded. -/
inductive SolveCertificate.LedgerAware
    {ledger : CapabilityOriginLedger} :
    {constraint : Constraint} → {delta : Subst} →
      SolveCertificate ledger constraint delta → Prop where
  | capEqOriented {left right result}
      (run : PairedUnification.solveCap
        (Unification.capFuel left right) ledger left right = some result) :
      LedgerAware (.capEqOriented run)
  | targetEqPaired {left right result}
      (run : PairedUnification.solvePairedTy
        (Unification.tyFuel left right) ledger left right = some result) :
      LedgerAware (.targetEqPaired run)
  | producerToSlot
      {producerCap consumerCap : Cap}
      {producerTarget consumerTarget : Ty}
      {bindings : CapMatch.Bindings} {targetSubst : TySubst}
      (matched : CapMatch.matchCap producerCap consumerCap = some bindings)
      (unified : Unification.mguTy
        (producerTarget.applyCapability
          (bindings.toSubstWithin consumerCap.fcv))
        (consumerTarget.applyCapability
          (bindings.toSubstWithin consumerCap.fcv)) = some targetSubst) :
      LedgerAware (.producerToSlot matched unified)

/-- Lift absorption by a capability substitution to cross-sort-aware paired
sequencing with an identity target phase. -/
private theorem absorbCapOnly
    {U : Subst} {C : CapSubst}
    (capAbsorbs : U.cap = CapSubst.comp U.cap C) :
    U = Subst.seq U (Subst.mk C TySubst.id) := by
  apply PhasedPost.subst_ext
  · exact capAbsorbs
  · funext varId
    rfl

/-- Relative universality of one proof-carrying oriented capability result,
lifted to paired substitution. -/
theorem orientedCapResult_factorization
    {ledger : CapabilityOriginLedger} {left right : Cap}
    (result : PairedUnification.OrientedCapResult ledger left right)
    (U : Subst) (competitorAdmissible : AdmissiblePost ledger U)
    (competitorSound : left.apply U.cap = right.apply U.cap) :
    ∃ R : Subst,
      AdmissiblePost ledger R ∧
        U = Subst.seq R (Subst.mk result.subst TySubst.id) := by
  refine ⟨U, competitorAdmissible, ?_⟩
  exact absorbCapOnly
    (result.universal U.cap competitorAdmissible.cap competitorSound)

/-- Relative universality of one proof-carrying paired target result. -/
theorem pairedResult_factorization
    {ledger : CapabilityOriginLedger} {left right : Ty}
    (result : PairedUnification.PairedResult ledger left right)
    (U : Subst) (competitorAdmissible : AdmissiblePost ledger U)
    (competitorSound : U.apply left = U.apply right) :
    ∃ R : Subst,
      AdmissiblePost ledger R ∧ U = Subst.seq R result.subst := by
  exact ⟨U, competitorAdmissible,
    result.universal U competitorAdmissible competitorSound⟩

/-! ## Dedicated producer-to-slot factorization -/

/-- The exact support-restricted matcher substitution is extensionally equal
to every declarative one-way witness.  `oneWayAt_unique` handles the consumer
support; both substitutions are identity outside it. -/
theorem capMatchRestricted_eq_of_oneWayAt
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    {witness : CapSubst}
    (algorithm : CapMatch.matchCap producer consumer = some bindings)
    (declarative : OneWayAt witness producer consumer) :
    bindings.toSubstWithin consumer.fcv = witness := by
  funext varId
  by_cases member : varId ∈ consumer.fcv
  · exact oneWayAt_unique
      (CapMatch.matchCap_restricted_sound algorithm) declarative varId member
  · rw [CapMatch.Bindings.toSubstWithin_support _ _ varId member]
    exact (declarative.1 varId member).symm

/-- A target-only residual is admissible for every capability-origin ledger. -/
private theorem targetOnlyAdmissible
    (ledger : CapabilityOriginLedger) (target : TySubst) :
    AdmissiblePost ledger (Subst.mk CapSubst.id target) :=
  { cap := AdmissibleCapPost.id ledger }

/-- The specialized one-way branch factors an admissible declarative
competitor through the exact `CapMatch` capability substitution and the target
MGU.  Capability uniqueness makes the residual capability phase identity. -/
theorem producerToSlot_factorization
    {ledger : CapabilityOriginLedger}
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {targetSubst : TySubst} {U : Subst}
    (matchSuccess : CapMatch.matchCap producerCap consumerCap = some bindings)
    (targetSuccess : Unification.mguTy
      (producerTarget.applyCapability
        (bindings.toSubstWithin consumerCap.fcv))
      (consumerTarget.applyCapability
        (bindings.toSubstWithin consumerCap.fcv)) = some targetSubst)
    (_competitorAdmissible : AdmissiblePost ledger U)
    (competitorSound :
      (.producerToSlot producerCap producerTarget consumerCap consumerTarget
        : Constraint).SolvedBy U) :
    ∃ R : Subst,
      AdmissiblePost ledger R ∧
        U = Subst.seq R
          (Subst.mk (bindings.toSubstWithin consumerCap.fcv) targetSubst) := by
  rcases competitorSound with ⟨oneWay, targetSound⟩
  let capabilitySubst := bindings.toSubstWithin consumerCap.fcv
  have capEquation : U.cap = capabilitySubst :=
    (capMatchRestricted_eq_of_oneWayAt matchSuccess oneWay).symm
  have targetSound' :
      (producerTarget.applyCapability capabilitySubst).applyTarget U.target =
        (consumerTarget.applyCapability capabilitySubst).applyTarget U.target := by
    simpa [capEquation] using targetSound
  obtain ⟨residualTarget, targetEquation⟩ :=
    Unification.mguTy_universal targetSuccess targetSound'
  let residual : Subst := Subst.mk CapSubst.id residualTarget
  refine ⟨residual, targetOnlyAdmissible ledger residualTarget, ?_⟩
  apply PhasedPost.subst_ext
  · change U.cap = CapSubst.comp residual.cap capabilitySubst
    rw [capEquation]
    funext varId
    simpa [residual, CapSubst.comp] using
      (Cap.apply_id (capabilitySubst varId)).symm
  · funext varId
    calc
      U.target varId =
          TySubst.comp residualTarget targetSubst varId :=
        congrFun targetEquation varId
      _ = (Subst.seq residual
            (Subst.mk capabilitySubst targetSubst)).target varId := by
        simp [Subst.seq, residual, Subst.apply, TySubst.comp,
          Ty.applyCapability_id]

/-! ## Safe certificate-level interface -/

/-- A certificate has local factorization when every admissible solution of
its resolved constraint factors through its exact delta. -/
def SolveCertificate.HasLocalFactorization
    {ledger : CapabilityOriginLedger} {constraint : Constraint}
    {delta : Subst} (_certificate : SolveCertificate ledger constraint delta) :
    Prop :=
  ∀ U : Subst, AdmissiblePost ledger U → constraint.SolvedBy U →
    ∃ R : Subst, AdmissiblePost ledger R ∧ U = Subst.seq R delta

/-- Every explicitly ledger-aware certificate has local factorization.  This
theorem cannot be applied to the legacy `capEq` and `targetEq` constructors,
because neither constructor can produce a `LedgerAware` witness. -/
theorem SolveCertificate.hasLocalFactorization_of_ledgerAware
    {ledger : CapabilityOriginLedger} {constraint : Constraint}
    {delta : Subst} {certificate : SolveCertificate ledger constraint delta}
    (ledgerAware : certificate.LedgerAware) :
    certificate.HasLocalFactorization := by
  intro U competitorAdmissible competitorSound
  cases ledgerAware with
  | capEqOriented run =>
      exact orientedCapResult_factorization _ U
        competitorAdmissible competitorSound
  | targetEqPaired run =>
      exact pairedResult_factorization _ U
        competitorAdmissible competitorSound
  | producerToSlot matched unified =>
      exact producerToSlot_factorization matched unified
        competitorAdmissible competitorSound

/-- Step-level packaging of local factorization at the exact captured ledger,
resolved constraint, and emitted delta. -/
def SolveStep.HasLocalFactorization (step : SolveStep) : Prop :=
  step.certificate.HasLocalFactorization

/-- Every successful ledger-aware local solve exposes one of the three
non-legacy certificate constructors. -/
theorem solveResolvedWithLedger_certificate_ledgerAware
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (stepSuccess : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    step.certificate.LedgerAware := by
  cases constraint with
  | capEq left right =>
      change solveCapEqWithLedger ledger solveCount origin left right =
        some step at stepSuccess
      unfold solveCapEqWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i result run
        have stepEquation := Option.some.inj stepSuccess
        subst step
        exact .capEqOriented run
  | targetEq left right =>
      change solveTargetEqWithLedger ledger solveCount origin left right =
        some step at stepSuccess
      unfold solveTargetEqWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i result run
        have stepEquation := Option.some.inj stepSuccess
        subst step
        exact .targetEqPaired run
  | producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      change solveProducerToSlotWithLedger ledger solveCount origin producerCap
          producerTarget consumerCap consumerTarget = some step at stepSuccess
      unfold solveProducerToSlotWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i bindings matched
        simp only at stepSuccess
        split at stepSuccess
        · split at stepSuccess
          · contradiction
          · rename_i targetSubst unified
            have stepEquation := Option.some.inj stepSuccess
            subst step
            exact .producerToSlot matched unified
        · contradiction

/-- Consequently, every step emitted by the ledger-aware local solver carries
the step-level factorization property. -/
theorem solveResolvedWithLedger_hasLocalFactorization
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (stepSuccess : solveResolvedWithLedger ledger solveCount origin constraint =
      some step) :
    step.HasLocalFactorization :=
  SolveCertificate.hasLocalFactorization_of_ledgerAware
    (solveResolvedWithLedger_certificate_ledgerAware stepSuccess)

/-! ## Factorization of emitted local steps -/

/-- Every admissible competitor solving the same resolved constraint factors
through the exact delta of the ledger-aware emitted step. -/
theorem solveResolvedWithLedger_factorization
    {ledger : CapabilityOriginLedger} {solveCount : Nat}
    {origin : ConstraintOrigin} {constraint : Constraint} {step : SolveStep}
    (stepSuccess : solveResolvedWithLedger ledger solveCount origin constraint =
      some step)
    {U : Subst} (competitorAdmissible : AdmissiblePost ledger U)
    (competitorSound : constraint.SolvedBy U) :
    ∃ R : Subst,
      AdmissiblePost ledger R ∧ U = Subst.seq R step.delta := by
  cases constraint with
  | capEq left right =>
      change solveCapEqWithLedger ledger solveCount origin left right =
        some step at stepSuccess
      unfold solveCapEqWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i result runEquation
        have stepEquation := Option.some.inj stepSuccess
        subst step
        exact orientedCapResult_factorization result U competitorAdmissible
          competitorSound
  | targetEq left right =>
      change solveTargetEqWithLedger ledger solveCount origin left right =
        some step at stepSuccess
      unfold solveTargetEqWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i result runEquation
        have stepEquation := Option.some.inj stepSuccess
        subst step
        exact pairedResult_factorization result U competitorAdmissible
          competitorSound
  | producerToSlot producerCap producerTarget consumerCap consumerTarget =>
      change solveProducerToSlotWithLedger ledger solveCount origin producerCap
          producerTarget consumerCap consumerTarget = some step at stepSuccess
      unfold solveProducerToSlotWithLedger at stepSuccess
      split at stepSuccess
      · contradiction
      · rename_i bindings matchSuccess
        simp only at stepSuccess
        split at stepSuccess
        · split at stepSuccess
          · contradiction
          · rename_i targetSubst targetSuccess
            have stepEquation := Option.some.inj stepSuccess
            subst step
            exact producerToSlot_factorization matchSuccess targetSuccess
              competitorAdmissible competitorSound
        · contradiction

end Inference
end TypePM
