import TypePM.DamasMilnerWLetStability

/-!
# Derived let-registration obligations

Two of the four facts needed when registering a completed W value are
already consequences of the ordinary output invariant.  This file exposes
them separately so the remaining generative freshness obligations cannot be
hidden in a catch-all certificate.
-/

namespace TypePM
namespace DM

open DemandTypingInferenceCompletenessContextBisimulation

/-- Context-independent spelling matching the actual W let cut.  The
environment affects which free variables are removed, never which target
they originated from. -/
theorem letGeneralizedVarsBelow_of_targetBounded
    (signature : FrozenSig) (context : Context) (target : Ty)
    (supply : InferenceBase.FreshSupply)
    (targetBounded : target.BoundedBy supply) :
    (∀ varId, varId ∈ signature.generalizedCapVars context target →
        varId.id < supply.nextCap) ∧
      (∀ varId, varId ∈ signature.generalizedTyVars context target →
        varId < supply.nextTy) := by
  constructor
  · intro varId generalized
    apply targetBounded.caps varId
    unfold FrozenSig.generalizedCapVars generalizedCapVars at generalized
    exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1
  · intro varId generalized
    apply targetBounded.targets varId
    unfold FrozenSig.generalizedTyVars generalizedTyVars at generalized
    exact (List.mem_filter.mp (mem_uniqueVars.mp generalized)).1

/-- At the value terminal, idempotence makes the freshly generalized scheme
stable under the same prevailing substitution. -/
theorem letGeneralizedScheme_fixed
    (signature : FrozenSig) (rawContext : Context) (rawTarget : Ty)
    (prevailing : Subst) (idempotent : prevailing.Idempotent) :
    (signature.generalize (rawContext.applySubst prevailing)
      (prevailing.apply rawTarget)).applyMeta prevailing =
      signature.generalize (rawContext.applySubst prevailing)
        (prevailing.apply rawTarget) :=
  FrozenSig.generalize_image_fixed signature rawContext rawTarget prevailing
    idempotent

end DM
end TypePM
