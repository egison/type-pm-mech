import TypePM.DemandTypingInferenceCompletenessStateMutual
import TypePM.PolyInstantiationTransport

/-!
# Context and scheme transport for inference completeness

These lemmas isolate the two facts needed by the variable and `let` cases of
raw-traversal completeness.  Context lookup transports through the forward
state residual unconditionally.  Canonical scheme instantiation additionally
needs that residual to fix the fresh images allocated at the current supply;
this local premise exposes the freshness invariant that the traversal
correspondence must retain.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessContext

open Inference
open DemandTypingInferenceCompletenessStateMutual

/-- The declarative normalized context is the executable normalized context
followed by the forward residual of the state bisimulation. -/
theorem normalizedContext_forward
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (context : Context) :
    context.applySubst declarative =
      (context.applySubst state.prevailing).applySubst relation.forward := by
  calc
    context.applySubst declarative =
        context.applySubst (Subst.seq relation.forward state.prevailing) :=
      congrArg (Context.applySubst · context) relation.forwardEquation
    _ = (context.applySubst state.prevailing).applySubst relation.forward :=
      Context.applySubst_seq relation.forward state.prevailing context

/-- A successful executable context lookup determines the corresponding demand-directed
lookup: its scheme is ambiently rewritten by the forward residual. -/
theorem lookup_forward
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (context : Context) (name : String) :
    (context.applySubst declarative).find? name =
      ((context.applySubst state.prevailing).find? name).map
        (Scheme.applyMeta relation.forward) := by
  rw [normalizedContext_forward relation context,
    Context.find?_applySubst]

/-- Pointed lookup transport, in the shape consumed by `DemandSynth.var`. -/
theorem lookup_forward_of_eq
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    {context : Context} {name : String} {scheme : Scheme}
    (lookup : (context.applySubst state.prevailing).find? name = some scheme) :
    (context.applySubst declarative).find? name =
      some (scheme.applyMeta relation.forward) := by
  rw [lookup_forward relation context name, lookup]
  rfl

/-! ## Fresh-image fixation from bounded prevailing states -/

/-- If both prevailing substitutions are bounded at the current supply, the
forward residual cannot act on a capability variable at or above that cut. -/
theorem StateBisimulation.forward_capFixedAbove
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (relation : StateBisimulation ledger declarative state)
    (declarativeBounded : declarative.BoundedBy supply)
    (executableBounded : state.prevailing.BoundedBy supply)
    (varId : CapVar) (above : supply.nextCap ≤ varId.id) :
    relation.forward.cap varId = .var varId := by
  have equation := congrArg (fun substitution : Subst =>
    substitution.cap varId) relation.forwardEquation
  rw [declarativeBounded.capFixedAbove varId above] at equation
  change Cap.var varId =
    (state.prevailing.cap varId).apply relation.forward.cap at equation
  rw [executableBounded.capFixedAbove varId above, Cap.apply] at equation
  exact equation.symm

/-- Target-variable counterpart of `forward_capFixedAbove`. -/
theorem StateBisimulation.forward_targetFixedAbove
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (relation : StateBisimulation ledger declarative state)
    (declarativeBounded : declarative.BoundedBy supply)
    (executableBounded : state.prevailing.BoundedBy supply)
    (varId : TypePM.TyVar) (above : supply.nextTy ≤ varId) :
    relation.forward.target varId = .var varId := by
  have equation := congrArg (fun substitution : Subst =>
    substitution.apply (.var varId)) relation.forwardEquation
  have declarativeApply : declarative.apply (.var varId) = .var varId := by
    change declarative.target varId = .var varId
    exact declarativeBounded.targetFixedAbove varId above
  have executableApply : state.prevailing.apply (.var varId) = .var varId := by
    change state.prevailing.target varId = .var varId
    exact executableBounded.targetFixedAbove varId above
  rw [declarativeApply, Subst.seq_apply, executableApply] at equation
  change Ty.var varId = relation.forward.target varId at equation
  exact equation.symm

/-- The reverse residual is equally fixed above a cut when both prevailing
substitutions are bounded there. -/
theorem StateBisimulation.reverse_targetFixedAbove
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (relation : StateBisimulation ledger declarative state)
    (declarativeBounded : declarative.BoundedBy supply)
    (executableBounded : state.prevailing.BoundedBy supply)
    (varId : TypePM.TyVar) (above : supply.nextTy ≤ varId) :
    relation.reverse.target varId = .var varId := by
  have equation := congrArg (fun substitution : Subst =>
    substitution.apply (.var varId)) relation.reverseEquation
  have executableApply : state.prevailing.apply (.var varId) = .var varId := by
    change state.prevailing.target varId = .var varId
    exact executableBounded.targetFixedAbove varId above
  have declarativeApply : declarative.apply (.var varId) = .var varId := by
    change declarative.target varId = .var varId
    exact declarativeBounded.targetFixedAbove varId above
  rw [executableApply, Subst.seq_apply, declarativeApply] at equation
  change Ty.var varId = relation.reverse.target varId at equation
  exact equation.symm

/-- Capability counterpart for the reverse residual. -/
theorem StateBisimulation.reverse_capFixedAbove
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} {supply : InferenceBase.FreshSupply}
    (relation : StateBisimulation ledger declarative state)
    (declarativeBounded : declarative.BoundedBy supply)
    (executableBounded : state.prevailing.BoundedBy supply)
    (varId : CapVar) (above : supply.nextCap ≤ varId.id) :
    relation.reverse.cap varId = .var varId := by
  have equation := congrArg (fun substitution : Subst =>
    substitution.cap varId) relation.reverseEquation
  rw [executableBounded.capFixedAbove varId above] at equation
  change Cap.var varId =
    (declarative.cap varId).apply relation.reverse.cap at equation
  rw [declarativeBounded.capFixedAbove varId above, Cap.apply] at equation
  exact equation.symm

/-- Ambient meta substitution does not change the canonical capability-image
batch selected from a supply. -/
@[simp] theorem canonicalCapImages_applyMeta
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (substitution : Subst) :
    Scheme.canonicalCapImages supply (scheme.applyMeta substitution) =
      Scheme.canonicalCapImages supply scheme := by
  cases scheme
  rfl

/-- Ambient meta substitution likewise preserves the canonical target-image
batch. -/
@[simp] theorem canonicalTyImages_applyMeta
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (substitution : Subst) :
    Scheme.canonicalTyImages supply (scheme.applyMeta substitution) =
      Scheme.canonicalTyImages supply scheme := by
  cases scheme
  rfl

/-- Consequently demand-directed and executable variable instantiation perform the same
origin-ledger transition even though their looked-up schemes differ by the
forward residual. -/
@[simp] theorem markSchemeInstance_applyMeta
    (ledger : CapabilityOriginLedger) (supply : InferenceBase.FreshSupply)
    (scheme : Scheme) (substitution : Subst) :
    DDLedger.markSchemeInstance ledger supply
        (scheme.applyMeta substitution) =
      DDLedger.markSchemeInstance ledger supply scheme := by
  simp [DDLedger.markSchemeInstance]

/-- Canonical fresh instantiation commutes with an ambient residual that is
bounded at the incoming supply.  Boundedness is exactly what prevents the
residual from rewriting the fresh images allocated for bound positions. -/
theorem instantiateScheme_applyMeta_bounded
    (supply : InferenceBase.FreshSupply) (scheme : Scheme)
    (substitution : Subst) (bounded : substitution.BoundedBy supply) :
    (InferenceBase.instantiateScheme supply
      (scheme.applyMeta substitution)).value =
      substitution.apply
        (InferenceBase.instantiateScheme supply scheme).value := by
  cases scheme with
  | mk capArity tyArity body =>
      simp only [InferenceBase.instantiateScheme,
        Scheme.freshInstantiate_value, Scheme.openValue, Scheme.instantiate,
        Scheme.FreshOpening.toValueOpening, Scheme.applyMeta]
      let capImage : Fin capArity → CapVar := fun index =>
        ⟨supply.nextCap + index.val⟩
      let tyImage : Fin tyArity → Ty := fun index =>
        .var (supply.nextTy + index.val)
      have capFixed : ∀ index,
          substitution.cap (capImage index) = .var (capImage index) := by
        intro index
        exact bounded.capFixedAbove _ (by
          dsimp [capImage]
          omega)
      have targetFixed : ∀ index,
          substitution.apply (tyImage index) = tyImage index := by
        intro index
        change substitution.target (supply.nextTy + index.val) =
          .var (supply.nextTy + index.val)
        exact bounded.targetFixedAbove _ (by omega)
      have transported := PolyTy.instantiate_applyMeta substitution
        capImage capImage tyImage capFixed body
      simpa [capImage, tyImage, Scheme.canonicalFreshOpening, targetFixed]
        using transported

/-- Canonical instances of two normalized schemes form the exact target
bisimulation needed by the variable branch.  The four boundedness premises
fix newly allocated binder images; the scheme equations describe transport
of the already-normalized free metas in both directions. -/
theorem canonicalInstantiation_tyBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState} (relation : StateBisimulation ledger declarative state)
    (supply : InferenceBase.FreshSupply)
    (declarativeScheme executableScheme : Scheme)
    (declarativeBounded : declarative.BoundedBy supply)
    (executableBounded : state.prevailing.BoundedBy supply)
    (forwardBounded : relation.forward.BoundedBy supply)
    (reverseBounded : relation.reverse.BoundedBy supply)
    (forwardScheme : declarativeScheme =
      executableScheme.applyMeta relation.forward)
    (reverseScheme : executableScheme =
      declarativeScheme.applyMeta relation.reverse)
    (declarativeNormalized :
      declarativeScheme.applyMeta declarative = declarativeScheme)
    (executableNormalized :
      executableScheme.applyMeta state.prevailing = executableScheme) :
    TyBisimulation relation
      (InferenceBase.instantiateScheme supply declarativeScheme).value
      (InferenceBase.instantiateScheme supply executableScheme).value := by
  have declarativeFixed : declarative.apply
        (InferenceBase.instantiateScheme supply declarativeScheme).value =
      (InferenceBase.instantiateScheme supply declarativeScheme).value := by
    have transported := instantiateScheme_applyMeta_bounded supply
      declarativeScheme declarative declarativeBounded
    rw [declarativeNormalized] at transported
    exact transported.symm
  have executableFixed : state.prevailing.apply
        (InferenceBase.instantiateScheme supply executableScheme).value =
      (InferenceBase.instantiateScheme supply executableScheme).value := by
    have transported := instantiateScheme_applyMeta_bounded supply
      executableScheme state.prevailing executableBounded
    rw [executableNormalized] at transported
    exact transported.symm
  have forwardInstance :
      (InferenceBase.instantiateScheme supply declarativeScheme).value =
        relation.forward.apply
          (InferenceBase.instantiateScheme supply executableScheme).value := by
    rw [forwardScheme]
    exact instantiateScheme_applyMeta_bounded supply executableScheme
      relation.forward forwardBounded
  have reverseInstance :
      (InferenceBase.instantiateScheme supply executableScheme).value =
        relation.reverse.apply
          (InferenceBase.instantiateScheme supply declarativeScheme).value := by
    rw [reverseScheme]
    exact instantiateScheme_applyMeta_bounded supply declarativeScheme
      relation.reverse reverseBounded
  constructor
  · rw [declarativeFixed, executableFixed]
    exact forwardInstance
  · rw [executableFixed, declarativeFixed]
    exact reverseInstance

/-! ## Executable solve-result boundedness -/

/-- The proof-carrying paired solver result is bounded whenever both resolved
operands are bounded at the solve cut. -/
theorem pairedResult_boundedBy
    {ledger : CapabilityOriginLedger} {left right : Ty}
    (result : PairedUnification.PairedResult ledger left right)
    {supply : InferenceBase.FreshSupply}
    (leftBounded : left.BoundedBy supply)
    (rightBounded : right.BoundedBy supply) :
    result.subst.BoundedBy supply :=
  result.exactPairedMGU.boundedBy leftBounded rightBounded

/-- Capability-only executable results have the analogous paired
boundedness, with identity target action. -/
theorem orientedCapResult_boundedByPair
    {ledger : CapabilityOriginLedger} {left right : Cap}
    (result : PairedUnification.OrientedCapResult ledger left right)
    {supply : InferenceBase.FreshSupply}
    (leftBounded : left.BoundedBy supply)
    (rightBounded : right.BoundedBy supply) :
    (Subst.mk result.subst TySubst.id).BoundedBy supply :=
  result.exactCapMGU.boundedBy_pair leftBounded rightBounded

/-- A paired result over prevailing-resolved bounded operands is bounded at
the same cut.  This is the form needed by traversal state transitions. -/
theorem pairedResult_boundedByResolved
    {ledger : CapabilityOriginLedger} {left right : Ty}
    (result : PairedUnification.PairedResult ledger left right)
    {supply : InferenceBase.FreshSupply} {prevailing : Subst}
    (prevailingBounded : prevailing.BoundedBy supply)
    {rawLeft rawRight : Ty}
    (leftEq : left = prevailing.apply rawLeft)
    (rightEq : right = prevailing.apply rawRight)
    (rawLeftBounded : rawLeft.BoundedBy supply)
    (rawRightBounded : rawRight.BoundedBy supply) :
    result.subst.BoundedBy supply := by
  subst left
  subst right
  exact result.exactPairedMGU.boundedBy
    (prevailingBounded.apply rawLeftBounded)
    (prevailingBounded.apply rawRightBounded)

/-- A completed value traversal already supplies the forward equation between
the two normalized value types used at the `let` generalization cut. -/
theorem normalizedLetTarget_forward
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {declarativeTarget executableTarget : Ty}
    {relation : StateBisimulation ledger declarative state}
    (target : TyBisimulation relation declarativeTarget executableTarget) :
    declarative.apply declarativeTarget =
      relation.forward.apply (state.prevailing.apply executableTarget) :=
  target.forward

end DemandTypingInferenceCompletenessContext
end TypePM
