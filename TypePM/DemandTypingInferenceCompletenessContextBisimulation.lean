import TypePM.DemandTypingInferenceCompletenessContext
import TypePM.DemandTypingInferenceCompletenessLocalRenaming
import TypePM.DemandTypingInferenceCompletenessGeneralizationTransport

/-!
# Paired contexts for inference completeness

demand-directed and executable traversal may use different raw contexts after a `let` or
pattern binding.  The invariant required by variable lookup is only that the
contexts agree after their respective prevailing substitutions, up to the
same forward and reverse residuals as the state relation.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessContextBisimulation

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContext
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance

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

/-- A chronological state extension transports every already-related
polymorphic context without opening its binders. -/
theorem ContextBisimulation.transport
    {ledger ledger' : CapabilityOriginLedger}
    {declarative declarative' : Subst} {state state' : InferState}
    {before : StateBisimulation ledger declarative state}
    (extension : BisimulationExtension before ledger' declarative' state')
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation before declarativeContext
      executableContext) :
    ContextBisimulation extension.after declarativeContext
      executableContext := by
  induction declarativeContext generalizing executableContext with
  | nil =>
      cases executableContext with
      | nil => exact ⟨rfl, rfl⟩
      | cons head tail =>
          have impossible := congrArg List.length contexts.forward
          simp [Context.applySubst] at impossible
  | cons declarativeEntry declarativeTail induction =>
      cases executableContext with
      | nil =>
          have impossible := congrArg List.length contexts.forward
          simp [Context.applySubst] at impossible
      | cons executableEntry executableTail =>
          rcases declarativeEntry with ⟨declarativeName, declarativeScheme⟩
          rcases executableEntry with ⟨executableName, executableScheme⟩
          have forwardCons := List.cons.inj (by
            simpa only [Context.applySubst, List.map_cons] using
              contexts.forward)
          have reverseCons := List.cons.inj (by
            simpa only [Context.applySubst, List.map_cons] using
              contexts.reverse)
          have nameEq : declarativeName = executableName :=
            congrArg Prod.fst forwardCons.1
          have schemeForward : declarativeScheme.applyMeta declarative =
              (executableScheme.applyMeta state.prevailing).applyMeta
                before.forward := congrArg Prod.snd forwardCons.1
          have schemeReverse : executableScheme.applyMeta state.prevailing =
              (declarativeScheme.applyMeta declarative).applyMeta
                before.reverse := congrArg Prod.snd reverseCons.1
          have tails := induction
            ⟨forwardCons.2, reverseCons.2⟩
          subst executableName
          have schemes := extension.transportScheme schemeForward schemeReverse
          constructor
          · simpa only [Context.applySubst, List.map_cons, schemes.1]
              using congrArg (List.cons
                (declarativeName,
                  (executableScheme.applyMeta state'.prevailing).applyMeta
                    extension.after.forward)) tails.forward
          · simpa only [Context.applySubst, List.map_cons, schemes.2]
              using congrArg (List.cons
                (declarativeName,
                  (declarativeScheme.applyMeta declarative').applyMeta
                    extension.after.reverse)) tails.reverse

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

/-- Mutual state, context, and value correspondence determine the canonical
generalization transport.  Local renaming is derived internally from the
idempotent prevailing states; callers do not choose or maintain a separate
renaming witness. -/
theorem GeneralizationBisimulation.ofBisimulation
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    (signature : FrozenSig) (signatureClosed : signature.SchemesClosed)
    {declarativeTarget executableTarget : Ty}
    (targets : TyBisimulation relation declarativeTarget executableTarget) :
    GeneralizationBisimulation relation
      (signature.generalize (declarativeContext.applySubst declarative)
        (declarative.apply declarativeTarget))
      (signature.generalize (executableContext.applySubst state.prevailing)
        (state.prevailing.apply executableTarget)) := by
  let declarativeContext' := declarativeContext.applySubst declarative
  let executableContext' := executableContext.applySubst state.prevailing
  let declarativeTarget' := declarative.apply declarativeTarget
  let executableTarget' := state.prevailing.apply executableTarget
  have contextForward : declarativeContext' =
      executableContext'.applySubst relation.forward := by
    simpa [declarativeContext', executableContext'] using contexts.forward
  have contextReverse : executableContext' =
      declarativeContext'.applySubst relation.reverse := by
    simpa [declarativeContext', executableContext'] using contexts.reverse
  have targetForward : declarativeTarget' =
      relation.forward.apply executableTarget' := by
    simpa [declarativeTarget', executableTarget'] using targets.forward
  have targetReverse : executableTarget' =
      relation.reverse.apply declarativeTarget' := by
    simpa [declarativeTarget', executableTarget'] using targets.reverse
  constructor
  · let localMap :=
      DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.localRenamingOn_image
        relation executableTarget
    have capEnvironment : ∀ varId, varId ∈ executableTarget'.fcv →
        (localMap.capImage varId ∈ signature.fcv ++ declarativeContext'.fcv ↔
          varId ∈ signature.fcv ++ executableContext'.fcv) := by
      intro varId free
      rw [signatureClosed.signatureCaps]
      simp only [List.nil_append]
      constructor
      · intro membership
        rw [contextReverse]
        exact Context.mem_fcv_applySubst_of_cap declarativeContext'
          relation.reverse membership (localMap.cap_reverse free)
      · intro membership
        rw [contextForward]
        exact Context.mem_fcv_applySubst_of_cap executableContext'
          relation.forward membership (localMap.cap_forward free)
    have targetEnvironment : ∀ varId, varId ∈ executableTarget'.ftv →
        (localMap.targetImage varId ∈ signature.ftv ++ declarativeContext'.ftv ↔
          varId ∈ signature.ftv ++ executableContext'.ftv) := by
      intro varId free
      rw [signatureClosed.signatureTargets]
      simp only [List.nil_append]
      constructor
      · intro membership
        rw [contextReverse]
        exact Context.mem_ftv_applySubst_of_target declarativeContext'
          relation.reverse membership (localMap.target_reverse free)
      · intro membership
        rw [contextForward]
        exact Context.mem_ftv_applySubst_of_target executableContext'
          relation.forward membership (localMap.target_forward free)
    change signature.generalize declarativeContext' declarativeTarget' =
      (signature.generalize executableContext' executableTarget').applyMeta
        relation.forward
    rw [targetForward]
    unfold FrozenSig.generalize
    exact Scheme.generalize_forward localMap
      (signature.fcv ++ declarativeContext'.fcv)
      (signature.fcv ++ executableContext'.fcv)
      (signature.ftv ++ declarativeContext'.ftv)
      (signature.ftv ++ executableContext'.ftv) executableTarget'
      (fun _ member => member) (fun _ member => member)
      capEnvironment targetEnvironment
  · let localMap :=
      DemandTypingInferenceCompletenessLocalRenaming.StateBisimulation.reverseLocalRenamingOn_image
        relation declarativeTarget
    have capEnvironment : ∀ varId, varId ∈ declarativeTarget'.fcv →
        (localMap.capImage varId ∈ signature.fcv ++ executableContext'.fcv ↔
          varId ∈ signature.fcv ++ declarativeContext'.fcv) := by
      intro varId free
      rw [signatureClosed.signatureCaps]
      simp only [List.nil_append]
      constructor
      · intro membership
        rw [contextForward]
        exact Context.mem_fcv_applySubst_of_cap executableContext'
          relation.forward membership (localMap.cap_reverse free)
      · intro membership
        rw [contextReverse]
        exact Context.mem_fcv_applySubst_of_cap declarativeContext'
          relation.reverse membership (localMap.cap_forward free)
    have targetEnvironment : ∀ varId, varId ∈ declarativeTarget'.ftv →
        (localMap.targetImage varId ∈ signature.ftv ++ executableContext'.ftv ↔
          varId ∈ signature.ftv ++ declarativeContext'.ftv) := by
      intro varId free
      rw [signatureClosed.signatureTargets]
      simp only [List.nil_append]
      constructor
      · intro membership
        rw [contextForward]
        exact Context.mem_ftv_applySubst_of_target executableContext'
          relation.forward membership (localMap.target_reverse free)
      · intro membership
        rw [contextReverse]
        exact Context.mem_ftv_applySubst_of_target declarativeContext'
          relation.reverse membership (localMap.target_forward free)
    change signature.generalize executableContext' executableTarget' =
      (signature.generalize declarativeContext' declarativeTarget').applyMeta
        relation.reverse
    rw [targetReverse]
    unfold FrozenSig.generalize
    exact Scheme.generalize_forward localMap
      (signature.fcv ++ executableContext'.fcv)
      (signature.fcv ++ declarativeContext'.fcv)
      (signature.ftv ++ executableContext'.ftv)
      (signature.ftv ++ declarativeContext'.ftv) declarativeTarget'
      (fun _ member => member) (fun _ member => member)
      capEnvironment targetEnvironment

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

/-- Complete `let`-context extension: state, context, and value
bisimulations plus public signature closedness discharge every canonical
generalization and local-renaming obligation. -/
theorem ContextBisimulation.consGeneralized_complete
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    {relation : StateBisimulation ledger declarative state}
    {declarativeContext executableContext : Context}
    (contexts : ContextBisimulation relation declarativeContext
      executableContext)
    (signature : FrozenSig) (signatureClosed : signature.SchemesClosed)
    (name : String) {declarativeTarget executableTarget : Ty}
    (targets : TyBisimulation relation declarativeTarget executableTarget) :
    ContextBisimulation relation
      ((name, signature.generalize
        (declarativeContext.applySubst declarative)
        (declarative.apply declarativeTarget)) :: declarativeContext)
      ((name, signature.generalize
        (executableContext.applySubst state.prevailing)
        (state.prevailing.apply executableTarget)) :: executableContext) :=
  contexts.consGeneralized signature name declarativeTarget executableTarget
    (GeneralizationBisimulation.ofBisimulation contexts signature
      signatureClosed targets)

end DemandTypingInferenceCompletenessContextBisimulation
end TypePM
