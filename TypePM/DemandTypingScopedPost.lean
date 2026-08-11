import TypePM.DemandTypingErasureTransport

/-!
# Totalizing a supply-scoped variable post

`DDErasure.VariablePostBetween` constrains only variables allocated before an
input cut.  Source-level transport instead consumes a total `VariablePost`.
This module bridges the two notions without strengthening the actual post:
above the input cut, only its capability component is masked to identity.
The masked post agrees with the actual post on every input-bounded object.
-/

namespace TypePM
namespace DDErasure.VariablePostBetween

/-- Mask the capability action above `input`; the target action is unchanged. -/
def totalize (input : InferenceBase.FreshSupply) (post : Subst) : Subst :=
  { cap := fun varId =>
      if varId.id < input.nextCap then post.cap varId else .var varId
    target := post.target }

/-- Totalization preserves the actual capability action below the cut. -/
theorem totalize_cap_of_below
    (input : InferenceBase.FreshSupply) (post : Subst)
    (varId : CapVar) (below : varId.id < input.nextCap) :
    (totalize input post).cap varId = post.cap varId := by
  simp [totalize, below]

/-- A scoped variable-only post becomes a genuine total `VariablePost` after
masking above its input cut. -/
def totalize_variable
    {input output : InferenceBase.FreshSupply} {post : Subst}
    (between : VariablePostBetween input output post) :
    VariablePost (totalize input post) where
  capVariable := by
    intro varId
    by_cases below : varId.id < input.nextCap
    · rcases between varId below with ⟨image, equation, imageBelow⟩
      exact ⟨image, by simp [totalize, below, equation]⟩
    · exact ⟨varId, by simp [totalize, below]⟩

/-- Totalization is observationally equal to the actual post on a bounded
capability. -/
theorem totalize_applyCap_of_bounded
    {input : InferenceBase.FreshSupply} {post : Subst} {capability : Cap}
    (bounded : capability.BoundedBy input) :
    capability.apply (totalize input post).cap =
      capability.apply post.cap := by
  apply Cap.apply_eq_of_fcv_agree
  intro varId membership
  exact totalize_cap_of_below input post varId
    (bounded varId membership)

/-- Totalization is observationally equal to the actual post on a bounded
type. -/
theorem totalize_apply_of_bounded
    {input : InferenceBase.FreshSupply} {post : Subst} {target : Ty}
    (bounded : target.BoundedBy input) :
    (totalize input post).apply target = post.apply target := by
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    exact totalize_cap_of_below input post varId
      (bounded.caps varId membership)
  · intro varId membership
    rfl

/-- Ambient scheme application agrees on an input-bounded canonical scheme.
Bound positions are finite indices, so only free capability metavariables
need the below-cut agreement. -/
theorem totalize_applyScheme_of_bounded
    {input : InferenceBase.FreshSupply} {post : Subst} {scheme : Scheme}
    (bounded : scheme.BoundedBy input) :
    scheme.applyMeta (totalize input post) = scheme.applyMeta post := by
  apply Scheme.applyMeta_eq_of_free_agree
  · intro varId membership
    exact totalize_cap_of_below input post varId
      (bounded.caps varId membership)
  · intro _ _
    rfl

/-- Pointwise context application agrees on an input-bounded context. -/
theorem totalize_applyContext_of_bounded
    {input : InferenceBase.FreshSupply} {post : Subst} {context : Context}
    (bounded : Context.BoundedBy input context) :
    context.applySubst (totalize input post) = context.applySubst post := by
  induction context with
  | nil => rfl
  | cons entry context induction =>
      rcases entry with ⟨name, scheme⟩
      have headBounded := bounded (name, scheme) (by simp)
      have tailBounded : Context.BoundedBy input context := by
        intro entry membership
        exact bounded entry (by simp [membership])
      simp only [Context.applySubst, List.map_cons]
      congr 1
      · exact congrArg (fun item => (name, item))
          (totalize_applyScheme_of_bounded headBounded)
      · exact induction tailBounded

end DDErasure.VariablePostBetween

namespace DDErasure.AdmissiblePostBetween

/-- A frozen input ledger is exactly the extra fact needed to totalize an
admissible suffix as a source-level variable post.  No condition is imposed
on capability variables allocated at or after the input cut. -/
def totalizedVariable
    {input output : InferenceBase.FreshSupply}
    {before after : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePostBetween input output before after post)
    (frozen : FrozenBelow input before) :
    VariablePost (VariablePostBetween.totalize input post) :=
  VariablePostBetween.totalize_variable
    (admissible.toVariablePostBetween frozen)

end DDErasure.AdmissiblePostBetween
end TypePM
