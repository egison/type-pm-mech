import TypePM.DemandTypingInferenceCompletenessContextBisimulation

/-!
# Paired traversal data for inference completeness

Expression synthesis tracks one raw type.  Pattern and matcher traversal also
threads duals and monomorphic binding contexts.  This module lifts the same
fixed forward/reverse state residuals to those products, so the eventual
mutual completeness proof does not duplicate substitution algebra at every
syntax constructor.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessDataBisimulation

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation

/-- Capability correspondence encoded through the ordinary type relation.
Using a matcher shell avoids a second copy of the two-sort substitution
factorization proof. -/
def CapBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (declarativeCap executableCap : Cap) : Prop :=
  TyBisimulation relation (.matcher declarativeCap .unit)
    (.matcher executableCap .unit)

/-- A pattern dual corresponds componentwise in the capability and target
sorts, under one shared pair of state residuals. -/
structure DualBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (declarativeDual executableDual : Dual) : Prop where
  cap : CapBisimulation relation declarativeDual.cap executableDual.cap
  target : TyBisimulation relation declarativeDual.target executableDual.target

/-- Pointwise dual-list correspondence. -/
inductive DualListBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    List Dual -> List Dual -> Prop where
  | nil : DualListBisimulation relation [] []
  | cons
      (head : DualBisimulation relation declarativeDual executableDual)
      (tail : DualListBisimulation relation declarativeDuals executableDuals) :
      DualListBisimulation relation
        (declarativeDual :: declarativeDuals)
        (executableDual :: executableDuals)

/-- Monomorphic contexts correspond positionally, including binder names. -/
inductive MonoCtxBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    MonoCtx -> MonoCtx -> Prop where
  | nil : MonoCtxBisimulation relation [] []
  | cons
      (target : TyBisimulation relation declarativeTarget executableTarget)
      (tail : MonoCtxBisimulation relation declarativeContext
        executableContext) :
      MonoCtxBisimulation relation
        ((name, declarativeTarget) :: declarativeContext)
        ((name, executableTarget) :: executableContext)

/-- Pattern-parameter contexts correspond positionally. -/
inductive PatternCtxBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) :
    PatternCtx -> PatternCtx -> Prop where
  | nil : PatternCtxBisimulation relation [] []
  | cons
      (dual : DualBisimulation relation declarativeDual executableDual)
      (tail : PatternCtxBisimulation relation declarativeContext
        executableContext) :
      PatternCtxBisimulation relation
        ((name, declarativeDual) :: declarativeContext)
        ((name, executableDual) :: executableContext)

/-- The same capability is related under every state bisimulation. -/
theorem CapBisimulation.same
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) (capability : Cap) :
    CapBisimulation relation capability capability :=
  relation.sameTarget (.matcher capability .unit)

/-- The same dual is related componentwise. -/
theorem DualBisimulation.same
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state) (dual : Dual) :
    DualBisimulation relation dual dual :=
  ⟨CapBisimulation.same relation dual.cap,
    relation.sameTarget dual.target⟩

/-- State extensions transport capability correspondence. -/
theorem BisimulationExtension.transportCap
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeCap executableCap : Cap}
    (related : CapBisimulation before declarativeCap executableCap) :
    CapBisimulation extension.after declarativeCap executableCap :=
  extension.transportTy related

/-- State extensions transport dual correspondence componentwise. -/
theorem BisimulationExtension.transportDual
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeDual executableDual : Dual}
    (related : DualBisimulation before declarativeDual executableDual) :
    DualBisimulation extension.after declarativeDual executableDual :=
  ⟨DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportCap
      extension related.cap,
    extension.transportTy related.target⟩

/-- Pointwise dual-list transport. -/
theorem BisimulationExtension.transportDualList
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeDuals executableDuals : List Dual}
    (related : DualListBisimulation before declarativeDuals executableDuals) :
    DualListBisimulation extension.after declarativeDuals executableDuals := by
  induction related with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          extension head) induction

/-- Pointwise monomorphic-context transport. -/
theorem BisimulationExtension.transportMonoCtx
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeContext executableContext : MonoCtx}
    (related : MonoCtxBisimulation before declarativeContext executableContext) :
    MonoCtxBisimulation extension.after declarativeContext executableContext := by
  induction related with
  | nil => exact .nil
  | cons target tail induction =>
      exact .cons (extension.transportTy target) induction

/-- Pointwise pattern-context transport. -/
theorem BisimulationExtension.transportPatternCtx
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeContext executableContext : PatternCtx}
    (related : PatternCtxBisimulation before declarativeContext
      executableContext) :
    PatternCtxBisimulation extension.after declarativeContext
      executableContext := by
  induction related with
  | nil => exact .nil
  | cons dual tail induction =>
      exact .cons
        (DemandTypingInferenceCompletenessDataBisimulation.BisimulationExtension.transportDual
          extension dual) induction

/-- A paired monomorphic context induces the corresponding ordinary source
contexts used while checking pattern bodies. -/
theorem MonoCtxBisimulation.toContext
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : MonoCtx}
    (related : MonoCtxBisimulation relation declarativeContext
      executableContext) :
    ContextBisimulation relation declarativeContext.toContext
      executableContext.toContext := by
  induction related with
  | nil => exact ContextBisimulation.same relation []
  | cons target tail induction =>
      exact induction.consMono _ target

/-- Paired monomorphic contexts have literally the same binder-name list. -/
theorem MonoCtxBisimulation.names_eq
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : MonoCtx}
    (related : MonoCtxBisimulation relation declarativeContext
      executableContext) :
    declarativeContext.names = executableContext.names := by
  induction related with
  | nil => rfl
  | cons _ _ induction => exact congrArg (List.cons _) induction

end DemandTypingInferenceCompletenessDataBisimulation
end TypePM
