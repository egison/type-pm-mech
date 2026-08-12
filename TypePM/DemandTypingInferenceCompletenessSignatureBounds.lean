import TypePM.DemandTyping

/-!
# Signature-variable supply bounds

Validator coverage for fresh pattern leaves refers to every variable reserved
by the frozen signature, including quantified scheme binders.  Raw traversal
boundedness tracks only free program data, so certified completeness carries
this small monotone supply invariant separately.  The public root discharges
it from `Inference.initialSupply`.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessSignatureBounds

/-- Both sorts of variables reserved by a frozen signature lie below the
current fresh supply. -/
structure SignatureVarsBelow
    (q : InferenceBase.FreshSupply) (signature : FrozenSig) : Prop where
  caps : InferenceBase.CapVarsBelow q signature.capVars
  targets : InferenceBase.TyVarsBelow q signature.tyVars

theorem SignatureVarsBelow.mono
    {q q' : InferenceBase.FreshSupply} {signature : FrozenSig}
    (bounded : SignatureVarsBelow q signature)
    (extension : SupplyExtends q q') : SignatureVarsBelow q' signature := by
  constructor
  · intro varId membership
    exact Nat.lt_of_lt_of_le (bounded.caps varId membership) extension.1
  · intro varId membership
    exact Nat.lt_of_lt_of_le (bounded.targets varId membership) extension.2

/-- The canonical initial supply reserves the complete signature scope. -/
theorem initial
    (signature : FrozenSig) (context : Context) :
    SignatureVarsBelow (Inference.initialSupply signature context) signature := by
  constructor
  · intro varId membership
    simpa [Inference.initialSupply] using
      InferenceBase.mem_lt_binderSpan
        (List.mem_map.mpr ⟨varId, List.mem_append.mpr (Or.inl membership),
          rfl⟩)
  · intro varId membership
    simpa [Inference.initialSupply] using
      InferenceBase.mem_lt_binderSpan
        (List.mem_append.mpr (Or.inl membership))

end DemandTypingInferenceCompletenessSignatureBounds
end TypePM
