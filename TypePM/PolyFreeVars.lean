import TypePM.PolyScheme
import TypePM.PolySubstitutionLaws
import TypePM.FreeVars

/-!
# Free solver metavariables of capture-free scheme payloads

Bound indices and free solver metavariables are different constructors, so
free-variable collection is a direct syntax traversal.  It never subtracts a
binder list and cannot confuse a numerically equal bound index with a free
metavariable.
-/

namespace TypePM

namespace PolyCap

mutual

/-- Free capability solver metavariables of a polymorphic capability. -/
def fcv {capArity : Nat} : PolyCap capArity → List CapVar
  | .any => []
  | .mvar varId => [varId]
  | .bound _ => []
  | .skolem _ => []
  | .con _ children => fcvList children
  | .prod components => fcvList components

/-- List form of `PolyCap.fcv`. -/
def fcvList {capArity : Nat} : List (PolyCap capArity) → List CapVar
  | [] => []
  | capability :: capabilities => capability.fcv ++ fcvList capabilities

end

end PolyCap

namespace PolyTy

mutual

/-- Free capability solver metavariables occurring in a polymorphic type. -/
def fcv {capArity tyArity : Nat} :
    PolyTy capArity tyArity → List CapVar
  | .mvar _ => []
  | .bound _ => []
  | .skolem _ => []
  | .unit => []
  | .int => []
  | .bool => []
  | .data _ children => fcvList children
  | .prod components => fcvList components
  | .fn domain codomain => domain.fcv ++ codomain.fcv
  | .matcher capability target => capability.fcv ++ target.fcv
  | .slot capability target => capability.fcv ++ target.fcv

/-- List form of `PolyTy.fcv`. -/
def fcvList {capArity tyArity : Nat} :
    List (PolyTy capArity tyArity) → List CapVar
  | [] => []
  | target :: targets => target.fcv ++ fcvList targets

end


mutual

/-- Free ordinary-type solver metavariables of a polymorphic type. -/
def ftv {capArity tyArity : Nat} :
    PolyTy capArity tyArity → List TypePM.TyVar
  | .mvar varId => [varId]
  | .bound _ => []
  | .skolem _ => []
  | .unit => []
  | .int => []
  | .bool => []
  | .data _ children => ftvList children
  | .prod components => ftvList components
  | .fn domain codomain => domain.ftv ++ codomain.ftv
  | .matcher _ target => target.ftv
  | .slot _ target => target.ftv

/-- List form of `PolyTy.ftv`. -/
def ftvList {capArity tyArity : Nat} :
    List (PolyTy capArity tyArity) → List TypePM.TyVar
  | [] => []
  | target :: targets => target.ftv ++ ftvList targets

end

end PolyTy

/-! ## Closing introduces no free solver metavariables -/

/-- Abstracting capability metavariables can only remove free occurrences. -/
theorem PolyCap.mem_fcv_abstract {capArity : Nat}
    (closing : CapVar → Option (Fin capArity)) :
    ∀ (capability : Cap) (varId : CapVar),
      varId ∈ (PolyCap.abstract closing capability).fcv →
        varId ∈ capability.fcv := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities => ∀ varId,
        varId ∈ PolyCap.fcvList
          (capabilities.map (PolyCap.abstract closing)) →
        varId ∈ Cap.fcvList capabilities) with
  | any => simp [PolyCap.abstract, PolyCap.fcv, Cap.fcv]
  | var original =>
      intro varId membership
      cases equation : closing original <;>
        simp [PolyCap.abstract, PolyCap.fcv, Cap.fcv, equation] at membership ⊢
      exact membership
  | skolem name => simp [PolyCap.abstract, PolyCap.fcv, Cap.fcv]
  | con name children induction =>
      simpa [PolyCap.abstract, PolyCap.fcv, Cap.fcv] using induction
  | prod components induction =>
      simpa [PolyCap.abstract, PolyCap.fcv, Cap.fcv] using induction
  | nil varId membership => nomatch membership
  | cons capability capabilities headInduction tailInduction varId membership =>
      simp only [List.map_cons, PolyCap.fcvList, Cap.fcvList,
        List.mem_append] at membership ⊢
      exact membership.elim (Or.inl ∘ headInduction varId)
        (Or.inr ∘ tailInduction varId)

/-- A capability metavariable that remains free after abstraction was not
selected by the closing map. -/
theorem PolyCap.closing_none_of_mem_fcv_abstract {capArity : Nat}
    (closing : CapVar → Option (Fin capArity)) :
    ∀ (capability : Cap) (varId : CapVar),
      varId ∈ (PolyCap.abstract closing capability).fcv →
        closing varId = none := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities => ∀ varId,
        varId ∈ PolyCap.fcvList
          (capabilities.map (PolyCap.abstract closing)) →
        closing varId = none) with
  | any => simp [PolyCap.abstract, PolyCap.fcv]
  | var original =>
      intro varId membership
      cases equation : closing original <;>
        simp [PolyCap.abstract, PolyCap.fcv, equation] at membership
      subst varId
      exact equation
  | skolem name => simp [PolyCap.abstract, PolyCap.fcv]
  | con name children induction =>
      simpa [PolyCap.abstract, PolyCap.fcv] using induction
  | prod components induction =>
      simpa [PolyCap.abstract, PolyCap.fcv] using induction
  | nil varId membership => nomatch membership
  | cons capability capabilities headInduction tailInduction varId membership =>
      simp only [List.map_cons, PolyCap.fcvList, List.mem_append] at membership
      exact membership.elim (headInduction varId) (tailInduction varId)

/-- Closing an ordinary type can only remove free solver metavariables;
it never creates a free capability or target metavariable. -/
theorem PolyTy.abstract_free_subset {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) :
    ∀ target : Ty,
      (∀ varId, varId ∈ (PolyTy.abstract closeCap closeTy target).fcv →
        varId ∈ target.fcv) ∧
      (∀ varId, varId ∈ (PolyTy.abstract closeCap closeTy target).ftv →
        varId ∈ target.ftv) := by
  intro target
  induction target using Ty.rec
      (motive_2 := fun targets =>
        (∀ varId, varId ∈ PolyTy.fcvList
            (targets.map (PolyTy.abstract closeCap closeTy)) →
          varId ∈ Ty.fcvList targets) ∧
        (∀ varId, varId ∈ PolyTy.ftvList
            (targets.map (PolyTy.abstract closeCap closeTy)) →
          varId ∈ Ty.ftvList targets)) with
  | var original =>
      cases equation : closeTy original <;>
        simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv,
          equation]
  | skolem name => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
  | unit => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
  | int => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
  | bool => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
  | data name children induction =>
      simpa [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
        using induction
  | prod components induction =>
      simpa [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv]
        using induction
  | fn domain codomain domainInduction codomainInduction =>
      constructor <;> intro varId membership <;>
        simp only [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, Ty.fcv, Ty.ftv,
          List.mem_append] at membership ⊢
      · exact membership.elim
          (Or.inl ∘ domainInduction.1 varId)
          (Or.inr ∘ codomainInduction.1 varId)
      · exact membership.elim
          (Or.inl ∘ domainInduction.2 varId)
          (Or.inr ∘ codomainInduction.2 varId)
  | matcher capability payload payloadInduction =>
      constructor
      · intro varId membership
        simp only [PolyTy.abstract, PolyTy.fcv, Ty.fcv,
          List.mem_append] at membership ⊢
        exact membership.elim
          (Or.inl ∘ PolyCap.mem_fcv_abstract closeCap capability varId)
          (Or.inr ∘ payloadInduction.1 varId)
      · simpa [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
          using payloadInduction.2
  | slot capability payload payloadInduction =>
      constructor
      · intro varId membership
        simp only [PolyTy.abstract, PolyTy.fcv, Ty.fcv,
          List.mem_append] at membership ⊢
        exact membership.elim
          (Or.inl ∘ PolyCap.mem_fcv_abstract closeCap capability varId)
          (Or.inr ∘ payloadInduction.1 varId)
      · simpa [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
          using payloadInduction.2
  | nil => simp [PolyTy.fcvList, PolyTy.ftvList, Ty.fcvList, Ty.ftvList]
  | cons target targets headInduction tailInduction =>
      constructor <;> intro varId membership <;>
        simp only [List.map_cons, PolyTy.fcvList, PolyTy.ftvList,
          Ty.fcvList, Ty.ftvList, List.mem_append] at membership ⊢
      · exact membership.elim
          (Or.inl ∘ headInduction.1 varId)
          (Or.inr ∘ tailInduction.1 varId)
      · exact membership.elim
          (Or.inl ∘ headInduction.2 varId)
          (Or.inr ∘ tailInduction.2 varId)

mutual

/-- A capability metavariable not selected by the closing map remains free
after abstraction. -/
theorem PolyCap.mem_abstract_fcv_of_closing_none {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) :
    ∀ capability : Cap, ∀ varId,
      varId ∈ capability.fcv → closeCap varId = none →
        varId ∈ (PolyCap.abstract closeCap capability).fcv
  | .any, _, membership, _ => by simp [Cap.fcv] at membership
  | .var original, varId, membership, closing => by
      simp only [Cap.fcv, List.mem_singleton] at membership
      subst original
      simp [PolyCap.abstract, PolyCap.fcv, closing]
  | .skolem _, _, membership, _ => by simp [Cap.fcv] at membership
  | .con _ children, varId, membership, closing => by
      simpa [Cap.fcv, PolyCap.abstract, PolyCap.fcv] using
        PolyCap.mem_abstract_fcvList_of_closing_none closeCap children
          varId membership closing
  | .prod components, varId, membership, closing => by
      simpa [Cap.fcv, PolyCap.abstract, PolyCap.fcv] using
        PolyCap.mem_abstract_fcvList_of_closing_none closeCap components
          varId membership closing

/-- List form of `PolyCap.mem_abstract_fcv_of_closing_none`. -/
theorem PolyCap.mem_abstract_fcvList_of_closing_none {capArity : Nat}
    (closeCap : CapVar → Option (Fin capArity)) :
    ∀ capabilities : List Cap, ∀ varId,
      varId ∈ Cap.fcvList capabilities → closeCap varId = none →
        varId ∈ PolyCap.fcvList
          (capabilities.map (PolyCap.abstract closeCap))
  | [], _, membership, _ => by simp [Cap.fcvList] at membership
  | head :: tail, varId, membership, closing => by
      simp only [Cap.fcvList, List.mem_append] at membership
      simp only [List.map_cons, PolyCap.fcvList, List.mem_append]
      exact membership.elim
        (Or.inl ∘ fun member =>
          PolyCap.mem_abstract_fcv_of_closing_none closeCap head varId
            member closing)
        (Or.inr ∘ fun member =>
          PolyCap.mem_abstract_fcvList_of_closing_none closeCap tail varId
            member closing)

end

/-- A source metavariable whose closing map is undefined remains free after
two-sorted abstraction. -/
theorem PolyTy.mem_abstract_free_of_closing_none {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) :
    ∀ target : Ty,
      (∀ varId, varId ∈ target.fcv → closeCap varId = none →
        varId ∈ (PolyTy.abstract closeCap closeTy target).fcv) ∧
      (∀ varId, varId ∈ target.ftv → closeTy varId = none →
        varId ∈ (PolyTy.abstract closeCap closeTy target).ftv) := by
  intro target
  induction target using Ty.rec
      (motive_2 := fun targets =>
        (∀ varId, varId ∈ Ty.fcvList targets → closeCap varId = none →
          varId ∈ PolyTy.fcvList
            (targets.map (PolyTy.abstract closeCap closeTy))) ∧
        (∀ varId, varId ∈ Ty.ftvList targets → closeTy varId = none →
          varId ∈ PolyTy.ftvList
            (targets.map (PolyTy.abstract closeCap closeTy)))) with
  | var original =>
      constructor
      · simp [Ty.fcv]
      · intro varId membership closing
        simp only [Ty.ftv, List.mem_singleton] at membership
        subst varId
        simp [PolyTy.abstract, PolyTy.ftv, closing]
  | skolem name => simp [Ty.fcv, Ty.ftv]
  | unit => simp [Ty.fcv, Ty.ftv]
  | int => simp [Ty.fcv, Ty.ftv]
  | bool => simp [Ty.fcv, Ty.ftv]
  | data name children induction =>
      simpa [Ty.fcv, Ty.ftv, PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
        using induction
  | prod components induction =>
      simpa [Ty.fcv, Ty.ftv, PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
        using induction
  | fn domain codomain domainInduction codomainInduction =>
      constructor <;> intro varId membership closing <;>
        simp only [Ty.fcv, Ty.ftv, PolyTy.abstract, PolyTy.fcv, PolyTy.ftv,
          List.mem_append] at membership ⊢
      · exact membership.elim
          (Or.inl ∘ fun member => domainInduction.1 varId member closing)
          (Or.inr ∘ fun member => codomainInduction.1 varId member closing)
      · exact membership.elim
          (Or.inl ∘ fun member => domainInduction.2 varId member closing)
          (Or.inr ∘ fun member => codomainInduction.2 varId member closing)
  | matcher capability payload payloadInduction =>
      constructor
      · intro varId membership closing
        simp only [Ty.fcv, List.mem_append] at membership
        simp only [PolyTy.abstract, PolyTy.fcv, List.mem_append]
        exact membership.elim
          (Or.inl ∘ fun member =>
            PolyCap.mem_abstract_fcv_of_closing_none closeCap capability
              varId member closing)
          (Or.inr ∘ fun member => payloadInduction.1 varId member closing)
      · simpa [Ty.ftv, PolyTy.abstract, PolyTy.ftv] using
          payloadInduction.2
  | slot capability payload payloadInduction =>
      constructor
      · intro varId membership closing
        simp only [Ty.fcv, List.mem_append] at membership
        simp only [PolyTy.abstract, PolyTy.fcv, List.mem_append]
        exact membership.elim
          (Or.inl ∘ fun member =>
            PolyCap.mem_abstract_fcv_of_closing_none closeCap capability
              varId member closing)
          (Or.inr ∘ fun member => payloadInduction.1 varId member closing)
      · simpa [Ty.ftv, PolyTy.abstract, PolyTy.ftv] using
          payloadInduction.2
  | nil => simp [Ty.fcvList, Ty.ftvList, PolyTy.fcvList, PolyTy.ftvList]
  | cons target targets headInduction tailInduction =>
      constructor <;> intro varId membership closing <;>
        simp only [Ty.fcvList, Ty.ftvList, List.mem_append, List.map_cons,
          PolyTy.fcvList, PolyTy.ftvList] at membership ⊢
      · exact membership.elim
          (Or.inl ∘ fun member => headInduction.1 varId member closing)
          (Or.inr ∘ fun member => tailInduction.1 varId member closing)
      · exact membership.elim
          (Or.inl ∘ fun member => headInduction.2 varId member closing)
          (Or.inr ∘ fun member => tailInduction.2 varId member closing)

/-- Free metavariables remaining after two-sorted abstraction were not
selected by the corresponding closing maps. -/
theorem PolyTy.closing_none_of_abstract_free {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) :
    ∀ target : Ty,
      (∀ varId, varId ∈ (PolyTy.abstract closeCap closeTy target).fcv →
        closeCap varId = none) ∧
      (∀ varId, varId ∈ (PolyTy.abstract closeCap closeTy target).ftv →
        closeTy varId = none) := by
  intro target
  induction target using Ty.rec
      (motive_2 := fun targets =>
        (∀ varId, varId ∈ PolyTy.fcvList
            (targets.map (PolyTy.abstract closeCap closeTy)) →
          closeCap varId = none) ∧
        (∀ varId, varId ∈ PolyTy.ftvList
            (targets.map (PolyTy.abstract closeCap closeTy)) →
          closeTy varId = none)) with
  | var original =>
      cases equation : closeTy original <;>
        simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv, equation]
  | skolem name => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
  | unit => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
  | int => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
  | bool => simp [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv]
  | data name children induction =>
      simpa [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv] using induction
  | prod components induction =>
      simpa [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv] using induction
  | fn domain codomain domainInduction codomainInduction =>
      constructor <;> intro varId membership <;>
        simp only [PolyTy.abstract, PolyTy.fcv, PolyTy.ftv,
          List.mem_append] at membership
      · exact membership.elim (domainInduction.1 varId)
          (codomainInduction.1 varId)
      · exact membership.elim (domainInduction.2 varId)
          (codomainInduction.2 varId)
  | matcher capability payload payloadInduction =>
      constructor
      · intro varId membership
        simp only [PolyTy.abstract, PolyTy.fcv, List.mem_append] at membership
        exact membership.elim
          (PolyCap.closing_none_of_mem_fcv_abstract closeCap capability varId)
          (payloadInduction.1 varId)
      · simpa [PolyTy.abstract, PolyTy.ftv] using payloadInduction.2
  | slot capability payload payloadInduction =>
      constructor
      · intro varId membership
        simp only [PolyTy.abstract, PolyTy.fcv, List.mem_append] at membership
        exact membership.elim
          (PolyCap.closing_none_of_mem_fcv_abstract closeCap capability varId)
          (payloadInduction.1 varId)
      · simpa [PolyTy.abstract, PolyTy.ftv] using payloadInduction.2
  | nil => simp [PolyTy.fcvList, PolyTy.ftvList]
  | cons target targets headInduction tailInduction =>
      constructor <;> intro varId membership <;>
        simp only [List.map_cons, PolyTy.fcvList, PolyTy.ftvList,
          List.mem_append] at membership
      · exact membership.elim (headInduction.1 varId)
          (tailInduction.1 varId)
      · exact membership.elim (headInduction.2 varId)
          (tailInduction.2 varId)

/-! ## Extensionality over free metavariables -/

mutual

/-- Ambient capability substitutions that agree on all free metavariables of
a polymorphic capability produce the same result. -/
theorem PolyCap.applyMeta_eq_of_fcv_agree {capArity : Nat}
    (left right : CapSubst) :
    ∀ capability : PolyCap capArity,
      (∀ varId, varId ∈ capability.fcv → left varId = right varId) →
      capability.applyMeta left = capability.applyMeta right
  | .any, _ => by simp [PolyCap.applyMeta]
  | .mvar varId, agree => by
      simp only [PolyCap.applyMeta]
      exact congrArg PolyCap.lift (agree varId (by simp [PolyCap.fcv]))
  | .bound _, _ => by simp [PolyCap.applyMeta]
  | .skolem _, _ => by simp [PolyCap.applyMeta]
  | .con name children, agree => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_eq_of_fcvList_agree left right children
        (fun varId membership => agree varId (by
          simpa [PolyCap.fcv] using membership))
  | .prod components, agree => by
      simp only [PolyCap.applyMeta]
      congr 1
      exact PolyCap.map_applyMeta_eq_of_fcvList_agree left right components
        (fun varId membership => agree varId (by
          simpa [PolyCap.fcv] using membership))

/-- List form of `PolyCap.applyMeta_eq_of_fcv_agree`. -/
theorem PolyCap.map_applyMeta_eq_of_fcvList_agree {capArity : Nat}
    (left right : CapSubst) :
    ∀ capabilities : List (PolyCap capArity),
      (∀ varId, varId ∈ PolyCap.fcvList capabilities →
        left varId = right varId) →
      capabilities.map (PolyCap.applyMeta left) =
        capabilities.map (PolyCap.applyMeta right)
  | [], _ => by simp
  | capability :: capabilities, agree => by
      simp only [List.map_cons]
      congr 1
      · exact PolyCap.applyMeta_eq_of_fcv_agree left right capability
          (fun varId membership => agree varId (by
            simp [PolyCap.fcvList, membership]))
      · exact PolyCap.map_applyMeta_eq_of_fcvList_agree left right
          capabilities (fun varId membership => agree varId (by
            simp [PolyCap.fcvList, membership]))

end

mutual

/-- Ambient paired substitutions that agree on every free metavariable of a
polymorphic type produce the same result. -/
theorem PolyTy.applyMeta_eq_of_free_agree {capArity tyArity : Nat}
    (left right : Subst) :
    ∀ target : PolyTy capArity tyArity,
      (∀ varId, varId ∈ target.fcv → left.cap varId = right.cap varId) →
      (∀ varId, varId ∈ target.ftv →
        left.target varId = right.target varId) →
      target.applyMeta left = target.applyMeta right
  | .mvar varId, _, tyAgree => by
      simp only [PolyTy.applyMeta]
      exact congrArg PolyTy.lift (tyAgree varId (by simp [PolyTy.ftv]))
  | .bound _, _, _ => by simp [PolyTy.applyMeta]
  | .skolem _, _, _ => by simp [PolyTy.applyMeta]
  | .unit, _, _ => by simp [PolyTy.applyMeta]
  | .int, _, _ => by simp [PolyTy.applyMeta]
  | .bool, _, _ => by simp [PolyTy.applyMeta]
  | .data name children, capAgree, tyAgree => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_eq_of_freeList_agree left right children
        (fun varId membership => capAgree varId (by
          simpa [PolyTy.fcv] using membership))
        (fun varId membership => tyAgree varId (by
          simpa [PolyTy.ftv] using membership))
  | .prod components, capAgree, tyAgree => by
      simp only [PolyTy.applyMeta]
      congr 1
      exact PolyTy.map_applyMeta_eq_of_freeList_agree left right components
        (fun varId membership => capAgree varId (by
          simpa [PolyTy.fcv] using membership))
        (fun varId membership => tyAgree varId (by
          simpa [PolyTy.ftv] using membership))
  | .fn domain codomain, capAgree, tyAgree => by
      simp only [PolyTy.applyMeta]
      congr 1
      · exact PolyTy.applyMeta_eq_of_free_agree left right domain
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simp [PolyTy.ftv, membership]))
      · exact PolyTy.applyMeta_eq_of_free_agree left right codomain
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simp [PolyTy.ftv, membership]))
  | .matcher capability target, capAgree, tyAgree => by
      simp only [PolyTy.applyMeta]
      congr 1
      · exact PolyCap.applyMeta_eq_of_fcv_agree left.cap right.cap capability
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
      · exact PolyTy.applyMeta_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simpa [PolyTy.ftv] using membership))
  | .slot capability target, capAgree, tyAgree => by
      simp only [PolyTy.applyMeta]
      congr 1
      · exact PolyCap.applyMeta_eq_of_fcv_agree left.cap right.cap capability
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
      · exact PolyTy.applyMeta_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcv, membership]))
          (fun varId membership => tyAgree varId (by
            simpa [PolyTy.ftv] using membership))

/-- List form of `PolyTy.applyMeta_eq_of_free_agree`. -/
theorem PolyTy.map_applyMeta_eq_of_freeList_agree {capArity tyArity : Nat}
    (left right : Subst) :
    ∀ targets : List (PolyTy capArity tyArity),
      (∀ varId, varId ∈ PolyTy.fcvList targets →
        left.cap varId = right.cap varId) →
      (∀ varId, varId ∈ PolyTy.ftvList targets →
        left.target varId = right.target varId) →
      targets.map (PolyTy.applyMeta left) =
        targets.map (PolyTy.applyMeta right)
  | [], _, _ => by simp
  | target :: targets, capAgree, tyAgree => by
      simp only [List.map_cons]
      congr 1
      · exact PolyTy.applyMeta_eq_of_free_agree left right target
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcvList, membership]))
          (fun varId membership => tyAgree varId (by
            simp [PolyTy.ftvList, membership]))
      · exact PolyTy.map_applyMeta_eq_of_freeList_agree left right targets
          (fun varId membership => capAgree varId (by
            simp [PolyTy.fcvList, membership]))
          (fun varId membership => tyAgree varId (by
            simp [PolyTy.ftvList, membership]))

end

namespace Scheme

/-- Free capability solver metavariables of a scheme.

No binder filtering is required: bound occurrences are already distinct
`PolyCap.bound` nodes. -/
def fcv (scheme : Scheme) : List CapVar :=
  scheme.body.fcv

/-- Free ordinary-type solver metavariables of a scheme. -/
def ftv (scheme : Scheme) : List TypePM.TyVar :=
  scheme.body.ftv

/-- A source capability metavariable not selected for closing remains a free
metavariable of the resulting scheme. -/
theorem mem_fcv_close_of_not_mem
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (source : Ty) {varId : CapVar}
    (free : varId ∈ source.fcv) (outside : varId ∉ capBinders) :
    varId ∈ (Scheme.close capBinders tyBinders source).fcv := by
  exact (PolyTy.mem_abstract_free_of_closing_none
    (fun candidate => capBinders.finIdxOf? candidate)
    (fun candidate => tyBinders.finIdxOf? candidate) source).1
      varId free (List.finIdxOf?_eq_none_iff.mpr outside)

/-- A source target metavariable not selected for closing remains a free
metavariable of the resulting scheme. -/
theorem mem_ftv_close_of_not_mem
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (source : Ty) {varId : TypePM.TyVar}
    (free : varId ∈ source.ftv) (outside : varId ∉ tyBinders) :
    varId ∈ (Scheme.close capBinders tyBinders source).ftv := by
  exact (PolyTy.mem_abstract_free_of_closing_none
    (fun candidate => capBinders.finIdxOf? candidate)
    (fun candidate => tyBinders.finIdxOf? candidate) source).2
      varId free (List.finIdxOf?_eq_none_iff.mpr outside)

/-- Scheme ambient substitution depends only on the free solver
metavariables appearing in the body. -/
theorem applyMeta_eq_of_free_agree (left right : Subst) (scheme : Scheme)
    (capAgree : ∀ varId, varId ∈ scheme.fcv →
      left.cap varId = right.cap varId)
    (tyAgree : ∀ varId, varId ∈ scheme.ftv →
      left.target varId = right.target varId) :
    scheme.applyMeta left = scheme.applyMeta right := by
  cases scheme with
  | mk capArity tyArity body =>
      simp only [Scheme.applyMeta]
      congr 1
      exact PolyTy.applyMeta_eq_of_free_agree left right body
        (by simpa [Scheme.fcv] using capAgree)
        (by simpa [Scheme.ftv] using tyAgree)

/-- An ambient substitution that fixes every source metavariable not selected
for closing leaves the resulting canonical scheme unchanged. -/
theorem close_applyMeta_eq_self
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (source : Ty) (substitution : Subst)
    (capFixed : ∀ varId, varId ∈ source.fcv → varId ∉ capBinders →
      substitution.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ source.ftv → varId ∉ tyBinders →
      substitution.target varId = .var varId) :
    (Scheme.close capBinders tyBinders source).applyMeta substitution =
      Scheme.close capBinders tyBinders source := by
  calc
    (Scheme.close capBinders tyBinders source).applyMeta substitution =
        (Scheme.close capBinders tyBinders source).applyMeta Subst.id := by
      apply Scheme.applyMeta_eq_of_free_agree
      · intro varId membership
        have sourceFree :=
          (PolyTy.abstract_free_subset
            (fun candidate => capBinders.finIdxOf? candidate)
            (fun candidate => tyBinders.finIdxOf? candidate) source).1
            varId membership
        have closingNone :=
          (PolyTy.closing_none_of_abstract_free
            (fun candidate => capBinders.finIdxOf? candidate)
            (fun candidate => tyBinders.finIdxOf? candidate) source).1
            varId membership
        have outside : varId ∉ capBinders := by
          simpa only [List.finIdxOf?_eq_none_iff] using closingNone
        simpa only [Subst.id, CapSubst.id] using
          capFixed varId sourceFree outside
      · intro varId membership
        have sourceFree :=
          (PolyTy.abstract_free_subset
            (fun candidate => capBinders.finIdxOf? candidate)
            (fun candidate => tyBinders.finIdxOf? candidate) source).2
            varId membership
        have closingNone :=
          (PolyTy.closing_none_of_abstract_free
            (fun candidate => capBinders.finIdxOf? candidate)
            (fun candidate => tyBinders.finIdxOf? candidate) source).2
            varId membership
        have outside : varId ∉ tyBinders := by
          simpa only [List.finIdxOf?_eq_none_iff] using closingNone
        simpa only [Subst.id, TySubst.id] using
          tyFixed varId sourceFree outside
    _ = Scheme.close capBinders tyBinders source :=
      Scheme.applyMeta_id _

end Scheme

namespace PolyFreeVarsRegression

/-- The former collision shape has a bound capability at its first position
and a free solver metavariable with numeric identifier zero at its second. -/
def collisionBody : PolyTy 1 0 :=
  .prod [.matcher (.bound 0) .int, .matcher (.mvar 0) .int]

/-- The bound index is absent from the free set; only the explicitly free
metavariable remains. -/
theorem collisionBody_fcv : collisionBody.fcv = [0] := by
  rfl

/-- The representative collision body contains no free target metavariable. -/
theorem collisionBody_ftv : collisionBody.ftv = [] := by
  rfl

/-- Scheme-level collection is the same direct body traversal and performs no
numeric binder subtraction. -/
theorem collisionScheme_fcv :
    ({ capArity := 1
       tyArity := 0
       body := collisionBody } : Scheme).fcv = [0] := by
  rfl

end PolyFreeVarsRegression

end TypePM
