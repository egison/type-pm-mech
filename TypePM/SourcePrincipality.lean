import TypePM.TypeInstance
import TypePM.DemandTypingTargetUniqueness
import TypePM.DemandTypingInferenceEquivalence

/-!
# Principal source types

The existing target-uniqueness theorem sends every audited source target to
one deterministic executable representative by a locally invertible
two-sorted renaming.  A renaming is a special case of the scoped instance
relation, and its recorded inverse maps the common representative back.
Thus the type returned by `inferType` is principal in the instance preorder.
-/

namespace TypePM
namespace DemandTypingTargetUniqueness

/-- A target renaming is, after finite restriction, an ordinary type
instance. -/
theorem TargetRenaming.toTypeInstance {source target : Ty}
    (certificate : TargetRenaming source target) :
    TypeInstance source target := by
  rcases certificate with ⟨forward, _reverse, _local, applied, _restored⟩
  exact TypeInstance.of_apply forward applied

/-- The inverse retained by a target-renaming certificate makes the source
an instance of the renamed target as well. -/
theorem TargetRenaming.reverseTypeInstance {source target : Ty}
    (certificate : TargetRenaming source target) :
    TypeInstance target source := by
  rcases certificate with ⟨_forward, reverse, _local, _applied, restored⟩
  exact TypeInstance.of_apply reverse restored

/-- Equality modulo residual renaming implies mutual instantiation. -/
theorem TargetRenamingEquivalent.typeInstances {left right : Ty}
    (equivalent : TargetRenamingEquivalent left right) :
    TypeInstance left right ∧ TypeInstance right left := by
  rcases equivalent with ⟨common, leftRenaming, rightRenaming⟩
  exact
    ⟨TypeInstance.trans leftRenaming.toTypeInstance
        rightRenaming.reverseTypeInstance,
      TypeInstance.trans rightRenaming.toTypeInstance
        leftRenaming.reverseTypeInstance⟩

theorem TargetRenamingEquivalent.toTypeInstance {left right : Ty}
    (equivalent : TargetRenamingEquivalent left right) :
    TypeInstance left right :=
  equivalent.typeInstances.1

end DemandTypingTargetUniqueness

namespace Inference

open DemandTypingTargetUniqueness

/-- The public inference result is principal among all audited source targets.

This theorem is context-general.  It compares targets while keeping the raw
source context fixed; the stronger open-term theorem which simultaneously
compares normalized contexts is a separate relation. -/
theorem inferType_principal
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {principal : Ty}
    (signatureWF : FrozenSigWF signature)
    (returned : inferType signature context expression = some principal) :
    SourceTyping signature context expression principal ∧
      ∀ target, SourceTyping signature context expression target →
        TypeInstance principal target := by
  have principalTyped :
      SourceTyping signature context expression principal :=
    inferType_success_sourceTyping returned
  refine ⟨principalTyped, ?_⟩
  intro target targetTyped
  exact
    (SourceTyping.target_unique_modulo_renaming principalTyped targetTyped
      signatureWF).toTypeInstance

/-- Closed-program specialization of `inferType_principal`. -/
theorem inferType_closed_principal
    {signature : FrozenSig} {expression : Expr} {principal : Ty}
    (signatureWF : FrozenSigWF signature)
    (returned : inferType signature [] expression = some principal) :
    SourceTyping signature [] expression principal ∧
      ∀ target, SourceTyping signature [] expression target →
        TypeInstance principal target :=
  inferType_principal signatureWF returned

end Inference
end TypePM
