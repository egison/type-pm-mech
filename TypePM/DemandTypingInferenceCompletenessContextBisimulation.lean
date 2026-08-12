import TypePM.DemandTypingInferenceCompletenessContext
import TypePM.DemandTypingInferenceCompletenessLocalRenaming

/-!
# Paired contexts for inference completeness

DD and executable traversal may use different raw contexts after a `let` or
pattern binding.  The invariant required by variable lookup is only that the
contexts agree after their respective prevailing substitutions, up to the
same forward and reverse residuals as the state relation.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessContextBisimulation

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContext

/-- Two raw contexts correspond after normalization by their respective
prevailing substitutions. -/
structure ContextBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (declarativeContext executableContext : Context) : Prop where
  forward :
    declarativeContext.applySubst declarative =
      (executableContext.applySubst state.prevailing).applySubst
        relation.forward
  reverse :
    executableContext.applySubst state.prevailing =
      (declarativeContext.applySubst declarative).applySubst relation.reverse

/-- The same raw context is related under every state bisimulation. -/
theorem ContextBisimulation.same
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (context : Context) :
    ContextBisimulation relation context context := by
  constructor
  · exact normalizedContext_forward relation context
  · calc
      context.applySubst state.prevailing =
          context.applySubst (Subst.seq relation.reverse declarative) :=
        congrArg (Context.applySubst · context) relation.reverseEquation
      _ = (context.applySubst declarative).applySubst relation.reverse :=
        Context.applySubst_seq relation.reverse declarative context

/-- The normalized schemes returned by corresponding lookups inherit the
same forward and reverse residuals. -/
theorem ContextBisimulation.lookup
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    {name : String} {declarativeScheme executableScheme : Scheme}
    (declarativeLookup :
      (declarativeContext.applySubst declarative).find? name =
        some declarativeScheme)
    (executableLookup :
      (executableContext.applySubst state.prevailing).find? name =
        some executableScheme) :
    declarativeScheme = executableScheme.applyMeta relation.forward ∧
      executableScheme = declarativeScheme.applyMeta relation.reverse := by
  have forwardAt := congrArg (fun context : Context => context.find? name)
    contexts.forward
  have reverseAt := congrArg (fun context : Context => context.find? name)
    contexts.reverse
  rw [declarativeLookup, Context.find?_applySubst, executableLookup] at forwardAt
  rw [executableLookup, Context.find?_applySubst, declarativeLookup] at reverseAt
  exact ⟨Option.some.inj forwardAt, Option.some.inj reverseAt⟩

/-- Normalized head schemes sufficient to extend a paired context. -/
structure NormalizedSchemeBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (declarativeScheme executableScheme : Scheme) : Prop where
  forward : declarativeScheme.applyMeta declarative =
    (executableScheme.applyMeta state.prevailing).applyMeta relation.forward
  reverse : executableScheme.applyMeta state.prevailing =
    (declarativeScheme.applyMeta declarative).applyMeta relation.reverse

/-- Extending corresponding contexts with corresponding schemes preserves
the context invariant. -/
theorem ContextBisimulation.cons
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    (name : String) {declarativeScheme executableScheme : Scheme}
    (schemes : NormalizedSchemeBisimulation relation declarativeScheme
      executableScheme) :
    ContextBisimulation relation
      ((name, declarativeScheme) :: declarativeContext)
      ((name, executableScheme) :: executableContext) := by
  constructor
  · simpa only [Context.applySubst, List.map_cons, schemes.forward]
      using congrArg (List.cons
        (name, (executableScheme.applyMeta state.prevailing).applyMeta
          relation.forward)) contexts.forward
  · simpa only [Context.applySubst, List.map_cons, schemes.reverse]
      using congrArg (List.cons
        (name, (declarativeScheme.applyMeta declarative).applyMeta
          relation.reverse)) contexts.reverse

/-- Monomorphic pattern/lambda bindings are transported directly by the
tracked type bisimulation. -/
theorem NormalizedSchemeBisimulation.mono
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeTarget executableTarget : Ty}
    (targets : TyBisimulation relation declarativeTarget executableTarget) :
    NormalizedSchemeBisimulation relation
      (Scheme.mono declarativeTarget) (Scheme.mono executableTarget) := by
  constructor
  · simpa only [Scheme.applyMeta_mono] using congrArg Scheme.mono targets.forward
  · simpa only [Scheme.applyMeta_mono] using congrArg Scheme.mono targets.reverse

/-- Convenient context extension for monomorphic binders. -/
theorem ContextBisimulation.consMono
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    (name : String) {declarativeTarget executableTarget : Ty}
    (targets : TyBisimulation relation declarativeTarget executableTarget) :
    ContextBisimulation relation
      ((name, Scheme.mono declarativeTarget) :: declarativeContext)
      ((name, Scheme.mono executableTarget) :: executableContext) :=
  contexts.cons name (NormalizedSchemeBisimulation.mono targets)

/-- Generalizing an image of an idempotent substitution produces a scheme
already stable under that substitution. -/
theorem FrozenSig.generalize_image_fixed
    (signature : FrozenSig) (context : Context) (rawTarget : Ty)
    (substitution : Subst) (idempotent : substitution.Idempotent) :
    (signature.generalize (context.applySubst substitution)
        (substitution.apply rawTarget)).applyMeta substitution =
      signature.generalize (context.applySubst substitution)
        (substitution.apply rawTarget) := by
  unfold FrozenSig.generalize Scheme.generalize
  apply Scheme.close_applyMeta_eq_self
  · intro varId free _
    exact idempotent.image_cap_fixed rawTarget varId free
  · intro varId free _
    exact idempotent.image_target_fixed rawTarget varId free

/-- The exact alpha-normalized transport obligation at a `let` cut.  It is
kept separate from context algebra: its proof is the equivariance of
`Scheme.generalize` under the scoped two-sort renaming extracted from mutual
state factorization. -/
structure GeneralizationBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (declarativeScheme executableScheme : Scheme) : Prop where
  forward : declarativeScheme =
    executableScheme.applyMeta relation.forward
  reverse : executableScheme =
    declarativeScheme.applyMeta relation.reverse

/-- A proved generalization transport extends paired contexts.  Idempotence
from the state bisimulation discharges the otherwise easy but essential
re-normalization of the freshly constructed schemes. -/
theorem ContextBisimulation.consGeneralized
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    (signature : FrozenSig) (name : String)
    (declarativeTarget executableTarget : Ty)
    (generalizations : GeneralizationBisimulation relation
      (signature.generalize (declarativeContext.applySubst declarative)
        (declarative.apply declarativeTarget))
      (signature.generalize (executableContext.applySubst state.prevailing)
        (state.prevailing.apply executableTarget))) :
    ContextBisimulation relation
      ((name, signature.generalize
        (declarativeContext.applySubst declarative)
        (declarative.apply declarativeTarget)) :: declarativeContext)
      ((name, signature.generalize
        (executableContext.applySubst state.prevailing)
        (state.prevailing.apply executableTarget)) :: executableContext) := by
  apply contexts.cons name
  constructor
  · rw [FrozenSig.generalize_image_fixed signature declarativeContext
      declarativeTarget declarative relation.declarativeIdempotent]
    rw [FrozenSig.generalize_image_fixed signature executableContext
      executableTarget state.prevailing relation.executableIdempotent]
    exact generalizations.forward
  · rw [FrozenSig.generalize_image_fixed signature executableContext
      executableTarget state.prevailing relation.executableIdempotent]
    rw [FrozenSig.generalize_image_fixed signature declarativeContext
      declarativeTarget declarative relation.declarativeIdempotent]
    exact generalizations.reverse

end DemandTypingInferenceCompletenessContextBisimulation
end TypePM
