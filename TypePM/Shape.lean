import TypePM.Relation

/-!
# ShapeCap evidence

This module isolates the evidence algebra used to infer a matcher literal's
structural capability.  Evidence is generated from matcher clauses, never from
the matcher target or a result annotation.

`Evidence.unseen` is the neutral element of exact merge.  It is deliberately
different from the complete minimal capability `Cap.any`: an observable
position that remains unseen is rejected during finalization, while an
unobservable position with ordinary evidence is canonicalized to `Cap.any`.
Evidence reconstructed from a non-root hole instead retains the exact
capability consumed by that hole's next matcher.
-/

namespace TypePM
namespace Shape

/-- Complete capability leaves that may occur in partial evidence. -/
inductive Leaf where
  | any
  | var    : CapVar → Leaf
  | skolem : Nat → Leaf
  /-- A complete capability whose value is inspected by a delegated matcher,
  not by the matcher whose clause evidence contains this leaf. -/
  | delegated : Cap → Leaf
deriving Repr, DecidableEq

/-- Embed a complete leaf back into the capability sort. -/
def Leaf.toCap : Leaf → Cap
  | .any       => .any
  | .var x     => .var x
  | .skolem x  => .skolem x
  | .delegated capability => capability

/--
Partial ShapeCap evidence.

Constructor and product nodes retain partial evidence independently in every
child.  Ordinary structured capabilities have one canonical tree
representation.  A `known (.delegated capability)` leaf is the explicit
exception: it records that a complete subtree is handled by the next matcher
and must not be recursively interpreted as observation by this matcher.
-/
inductive Evidence where
  | unseen
  | known : Leaf → Evidence
  | con   : String → List Evidence → Evidence
  | prod  : List Evidence → Evidence
deriving Repr

/-- Rename the flexible capability variables in a complete evidence leaf. -/
def Leaf.applyRen (r : CapVar → CapVar) : Leaf → Leaf
  | .any => .any
  | .var varId => .var (r varId)
  | .skolem name => .skolem name
  | .delegated capability => .delegated (capability.applyRen r)

mutual

/-- Rename every flexible capability variable in partial evidence. -/
def Evidence.applyRen
    (r : CapVar → CapVar) : Evidence → Evidence
  | .unseen => .unseen
  | .known leaf => .known (leaf.applyRen r)
  | .con name children => .con name (applyRenList r children)
  | .prod components => .prod (applyRenList r components)

/-- List form of `Evidence.applyRen`. -/
def Evidence.applyRenList
    (r : CapVar → CapVar) : List Evidence → List Evidence
  | [] => []
  | evidence :: rest =>
      evidence.applyRen r :: applyRenList r rest

end

/--
Frozen observability masks, indexed by canonical constructor former.

`none` means that the former is opaque.  `some mask` supplies one Boolean for
each constructor parameter; malformed arities are rejected.
-/
abbrev Observability := String → Option (List Bool)

/-- Canonical embedding of a complete capability into evidence. -/
def ofCap : Cap → Evidence
  | .any        => .known .any
  | .var x      => .known (.var x)
  | .skolem x   => .known (.skolem x)
  | .con k cs   => .con k (cs.map ofCap)
  | .prod cs    => .prod (cs.map ofCap)

/-- Atomic evidence for a hidden delegated constructor parameter.  `Any` keeps
its ordinary canonical representation so it can exact-merge with direct
canonical evidence from another clause. -/
def hiddenDelegatedCap : Cap → Evidence
  | .any => .known .any
  | capability => .known (.delegated capability)

/-- Hidden delegated evidence commutes with capability alpha-renaming. -/
theorem hiddenDelegatedCap_applyRen
    (r : CapVar → CapVar) (capability : Cap) :
    hiddenDelegatedCap (capability.applyRen r) =
      (hiddenDelegatedCap capability).applyRen r := by
  cases capability <;> rfl

mutual

  /--
  Embed the capability of a non-root primitive-pattern hole.

  Products and observable constructor formers retain the structure needed by
  signature projection.  An opaque constructor subtree, a hidden constructor
  parameter, or a constructor with a malformed observability arity is instead
  a complete delegated leaf.  The next matcher consumes that value, so the
  enclosing matcher must not claim to observe its internal structure during
  finalization.
  -/
  def ofDelegatedCap (observable : Observability) : Cap → Evidence
    | .any        => .known .any
    | .var x      => .known (.var x)
    | .skolem x   => .known (.skolem x)
    | capability@(.con name children) =>
        match observable name with
        | none => .known (.delegated capability)
        | some mask =>
            match ofDelegatedCapsMasked observable mask children with
            | some evidence => .con name evidence
            | none => .known (.delegated capability)
    | .prod components =>
        .prod (components.map (ofDelegatedCap observable))

  /-- Embed constructor children according to their observability mask.
  Hidden children remain complete delegated leaves. -/
  def ofDelegatedCapsMasked
      (observable : Observability) :
      List Bool → List Cap → Option (List Evidence)
    | [], [] => some []
    | isObservable :: mask, capability :: capabilities =>
        let head :=
          if isObservable then ofDelegatedCap observable capability
          else hiddenDelegatedCap capability
        match ofDelegatedCapsMasked observable mask capabilities with
        | some tail => some (head :: tail)
        | none => none
    | _, _ => none

end

/-- Embedding a capability commutes with a capability alpha-renaming. -/
theorem ofCap_applyRen (r : CapVar → CapVar) :
    ∀ capability,
      ofCap (capability.applyRen r) =
        (ofCap capability).applyRen r := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities =>
        (Cap.applyRenList r capabilities).map ofCap =
          Evidence.applyRenList r (capabilities.map ofCap)) with
  | any => simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen, ofCap]
  | var varId => simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen, ofCap]
  | skolem name =>
      simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen, ofCap]
  | con name children childrenInduction =>
      simp only [Cap.applyRen, ofCap, Evidence.applyRen,
        childrenInduction]
  | prod components componentsInduction =>
      simp only [Cap.applyRen, ofCap, Evidence.applyRen,
        componentsInduction]
  | nil => rfl
  | cons capability capabilities capabilityInduction capabilitiesInduction =>
      simp only [Cap.applyRenList, List.map_cons, Evidence.applyRenList,
        capabilityInduction, capabilitiesInduction]

/-- Delegated embedding commutes with capability alpha-renaming. -/
theorem ofDelegatedCap_applyRen
    (r : CapVar → CapVar) (observable : Observability) :
    ∀ capability,
      ofDelegatedCap observable (capability.applyRen r) =
        (ofDelegatedCap observable capability).applyRen r := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities =>
        (Cap.applyRenList r capabilities).map
              (ofDelegatedCap observable) =
            Evidence.applyRenList r
              (capabilities.map (ofDelegatedCap observable)) ∧
          ∀ mask,
            ofDelegatedCapsMasked observable mask
                (Cap.applyRenList r capabilities) =
              (ofDelegatedCapsMasked observable mask capabilities).map
                (Evidence.applyRenList r)) with
  | any =>
      simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen,
        ofDelegatedCap]
  | var varId =>
      simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen,
        ofDelegatedCap]
  | skolem name =>
      simp [Cap.applyRen, Evidence.applyRen, Leaf.applyRen,
        ofDelegatedCap]
  | con name children childrenInduction =>
      simp only [Cap.applyRen, ofDelegatedCap]
      cases observableResult : observable name with
      | none =>
          simp [Evidence.applyRen, Leaf.applyRen, Cap.applyRen]
      | some mask =>
          simp only [childrenInduction.2 mask]
          cases embedded :
              ofDelegatedCapsMasked observable mask children <;>
            simp [Evidence.applyRen, Leaf.applyRen, Cap.applyRen]
  | prod components componentsInduction =>
      simp only [Cap.applyRen, ofDelegatedCap, Evidence.applyRen,
        componentsInduction.1]
  | nil =>
      constructor
      · rfl
      · intro mask
        cases mask <;>
          simp [Cap.applyRenList, ofDelegatedCapsMasked,
            Evidence.applyRenList]
  | cons capability capabilities capabilityInduction
      capabilitiesInduction =>
      constructor
      · simp only [Cap.applyRenList, List.map_cons,
          Evidence.applyRenList, capabilityInduction,
          capabilitiesInduction.1]
      · intro mask
        cases mask with
        | nil =>
            simp [Cap.applyRenList, ofDelegatedCapsMasked]
        | cons isObservable mask =>
            simp only [Cap.applyRenList, ofDelegatedCapsMasked,
              capabilitiesInduction.2 mask]
            cases tailEmbedded :
                ofDelegatedCapsMasked observable mask capabilities <;>
              cases isObservable <;>
              simp [Evidence.applyRenList,
                hiddenDelegatedCap_applyRen, capabilityInduction]

mutual
  /--
  Exact evidence merge.

  The operation neither unifies distinct variables nor weakens a structured
  node to `Cap.any`.  Constructor names, node kinds, and arities must agree.
  -/
  def merge : Evidence → Evidence → Option Evidence
    | .unseen, evidence => some evidence
    | evidence, .unseen => some evidence
    | .known left, .known right =>
        if left = right then some (.known left) else none
    | .con leftName leftChildren, .con rightName rightChildren =>
        if leftName = rightName then
          match mergeList leftChildren rightChildren with
          | some children => some (.con leftName children)
          | none => none
        else
          none
    | .prod leftComponents, .prod rightComponents =>
        match mergeList leftComponents rightComponents with
        | some components => some (.prod components)
        | none => none
    | _, _ => none

  /-- Exact pointwise merge for equal-length evidence lists. -/
  def mergeList : List Evidence → List Evidence → Option (List Evidence)
    | [], [] => some []
    | left :: leftRest, right :: rightRest =>
        match merge left right, mergeList leftRest rightRest with
        | some head, some tail => some (head :: tail)
        | _, _ => none
    | _, _ => none
end

/-- Fold exact merge over all clause evidence, starting from unseen evidence. -/
def mergeAll : List Evidence → Option Evidence
  | [] => some .unseen
  | evidence :: rest =>
      match mergeAll rest with
      | some accumulated => merge evidence accumulated
      | none => none

/-- Complete one hidden constructor parameter.  Ordinary evidence is
canonicalized to `Any`; a delegated leaf retains the exact capability consumed
by the next matcher. -/
def finalizeHidden : Evidence → Cap
  | .known (.delegated capability) => capability
  | _ => .any

/-- Hidden delegated evidence completes to its exact capability. -/
@[simp] theorem finalizeHidden_hiddenDelegatedCap (capability : Cap) :
    finalizeHidden (hiddenDelegatedCap capability) = capability := by
  cases capability <;> rfl

/-- Hidden-parameter completion commutes with alpha-renaming. -/
theorem finalizeHidden_applyRen
    (r : CapVar → CapVar) (evidence : Evidence) :
    finalizeHidden (evidence.applyRen r) =
      (finalizeHidden evidence).applyRen r := by
  cases evidence with
  | unseen => rfl
  | known leaf => cases leaf <;> rfl
  | con name children => rfl
  | prod components => rfl

mutual
  /--
  Finalize partial evidence to a complete capability.

  Every observable unseen position is rejected.  An unobservable constructor
  parameter is canonicalized to `Cap.any` unless it is a complete delegated
  leaf consumed by the next matcher.  Product components are always
  observable.
  -/
  def finalize (observable : Observability) : Evidence → Option Cap
    | .unseen => none
    | .known leaf => some leaf.toCap
    | .con name children =>
        match observable name with
        | none => none
        | some mask =>
            match finalizeMasked observable mask children with
            | some capabilities => some (.con name capabilities)
            | none => none
    | .prod components =>
        match finalizeList observable components with
        | some capabilities => some (.prod capabilities)
        | none => none

  /-- Finalize a list whose positions are all observable. -/
  def finalizeList
      (observable : Observability) :
      List Evidence → Option (List Cap)
    | [] => some []
    | evidence :: rest =>
        match finalize observable evidence, finalizeList observable rest with
        | some capability, some capabilities =>
            some (capability :: capabilities)
        | _, _ => none

  /-- Finalize constructor children according to an exact-arity mask. -/
  def finalizeMasked
      (observable : Observability) :
      List Bool → List Evidence → Option (List Cap)
    | [], [] => some []
    | isObservable :: mask, evidence :: rest =>
      let head :=
          if isObservable then finalize observable evidence
          else some (finalizeHidden evidence)
      match head, finalizeMasked observable mask rest with
        | some capability, some capabilities =>
            some (capability :: capabilities)
        | _, _ => none
    | _, _ => none
end

/-- A capability delegated through a non-root hole always finalizes exactly,
including opaque constructors, hidden parameters, and malformed observable
arities.  Those cases are atomic because the next matcher, not the enclosing
matcher, consumes the corresponding value. -/
theorem finalize_ofDelegatedCap (observable : Observability) :
    ∀ capability,
      finalize observable (ofDelegatedCap observable capability) =
        some capability := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities =>
        finalizeList observable
              (capabilities.map (ofDelegatedCap observable)) =
            some capabilities ∧
          ∀ mask evidence,
            ofDelegatedCapsMasked observable mask capabilities =
                some evidence →
              finalizeMasked observable mask evidence = some capabilities) with
  | any =>
      simp [ofDelegatedCap, finalize, Leaf.toCap]
  | var varId =>
      simp [ofDelegatedCap, finalize, Leaf.toCap]
  | skolem name =>
      simp [ofDelegatedCap, finalize, Leaf.toCap]
  | con name children childrenInduction =>
      simp only [ofDelegatedCap]
      cases observableResult : observable name with
      | none =>
          rfl
      | some mask =>
          cases embedded :
              ofDelegatedCapsMasked observable mask children with
          | none =>
              simp [embedded, finalize, Leaf.toCap]
          | some evidence =>
              simp [embedded, finalize, observableResult,
                childrenInduction.2 mask evidence embedded]
  | prod components componentsInduction =>
      simp only [ofDelegatedCap, finalize, componentsInduction.1]
  | nil =>
      constructor
      · rfl
      · intro mask evidence success
        cases mask with
        | nil =>
            simp [ofDelegatedCapsMasked] at success
            subst evidence
            rfl
        | cons _ _ =>
            simp [ofDelegatedCapsMasked] at success
  | cons capability capabilities capabilityInduction
      capabilitiesInduction =>
      constructor
      · simp only [List.map_cons, finalizeList, capabilityInduction,
          capabilitiesInduction.1]
      · intro mask evidence success
        cases mask with
        | nil =>
            simp [ofDelegatedCapsMasked] at success
        | cons isObservable mask =>
            simp only [ofDelegatedCapsMasked] at success
            cases tailEmbedded :
                ofDelegatedCapsMasked observable mask capabilities with
            | none =>
                simp [tailEmbedded] at success
            | some tail =>
                have evidenceEquality :
                    evidence =
                      (if isObservable then
                          ofDelegatedCap observable capability
                        else hiddenDelegatedCap capability) :: tail := by
                  simpa [tailEmbedded] using success.symm
                subst evidence
                cases isObservable <;>
                  simp only [Bool.false_eq_true, if_false, if_true,
                    finalizeMasked, finalizeHidden_hiddenDelegatedCap,
                    capabilityInduction,
                    capabilitiesInduction.2 mask tail tailEmbedded]

/--
Infer a matcher literal's root capability from its clause evidence.

A literal with no structured root evidence has merged evidence `unseen` and
therefore receives the complete catch-all capability `Cap.any`.  Any other
partial tree is checked by observability-aware finalization.
-/
def inferShape
    (observable : Observability) (clauses : List Evidence) : Option Cap :=
  match mergeAll clauses with
  | none => none
  | some .unseen => some .any
  | some evidence => finalize observable evidence

@[simp] theorem merge_unseen_left (evidence : Evidence) :
    merge .unseen evidence = some evidence := rfl

@[simp] theorem merge_unseen_right (evidence : Evidence) :
    merge evidence .unseen = some evidence := by
  cases evidence <;> rfl

/-- An injective capability renaming is injective on complete leaves. -/
theorem Leaf.applyRen_injective
    {r : CapVar → CapVar}
    (injective : ∀ left right, r left = r right → left = right) :
    Function.Injective (Leaf.applyRen r) := by
  intro left right equality
  cases left <;> cases right <;> simp_all [Leaf.applyRen]
  · exact injective _ _ equality
  · exact Cap.applyRen_injective injective equality

mutual

/-- Exact merge commutes with every injective capability renaming. -/
theorem merge_applyRen
    {r : CapVar → CapVar}
    (injective : ∀ left right, r left = r right → left = right)
    (left right : Evidence) :
    merge (left.applyRen r) (right.applyRen r) =
      (merge left right).map (Evidence.applyRen r) := by
  cases left <;> cases right <;>
    simp [merge, Evidence.applyRen, mergeList_applyRen injective,
      (Leaf.applyRen_injective injective).eq_iff]
  case con.con =>
    rename_i leftName leftChildren rightName rightChildren
    by_cases namesEqual : leftName = rightName
    · subst rightName
      cases merged : mergeList leftChildren rightChildren <;>
        simp [Evidence.applyRen]
    · simp [namesEqual]
  case prod.prod =>
    rename_i leftComponents rightComponents
    cases merged : mergeList leftComponents rightComponents <;>
      simp [Evidence.applyRen]

/-- List form of `merge_applyRen`. -/
theorem mergeList_applyRen
    {r : CapVar → CapVar}
    (injective : ∀ left right, r left = r right → left = right)
    (left right : List Evidence) :
    mergeList (Evidence.applyRenList r left)
        (Evidence.applyRenList r right) =
      (mergeList left right).map (Evidence.applyRenList r) := by
  cases left <;> cases right <;>
    simp [mergeList, Evidence.applyRenList, merge_applyRen injective,
      mergeList_applyRen injective]
  case cons.cons =>
    rename_i leftHead leftTail rightHead rightTail
    cases headMerged : merge leftHead rightHead <;>
      cases tailMerged : mergeList leftTail rightTail <;>
        simp [Evidence.applyRenList]

end

/-- Exact merge is symmetric, including its failure cases. -/
theorem merge_comm (left right : Evidence) :
    merge left right = merge right left := by
  induction left, right using merge.induct
    (motive_2 := fun left right =>
      mergeList left right = mergeList right left) <;>
    simp_all [merge, mergeList, eq_comm]
  case case10 left right _ _ _ hCon _ =>
    cases left <;> cases right <;> simp_all [merge]
    case con.con =>
      exact (hCon _ _ _ _ rfl rfl rfl rfl).elim
  case case14 left right _ _ =>
    cases left <;> cases right <;> simp_all [mergeList]

/-- The inferred merge of two clauses is independent of their order. -/
theorem mergeAll_pair_comm (left right : Evidence) :
    mergeAll [left, right] = mergeAll [right, left] := by
  simp [mergeAll, merge_comm]

private def conOption (name : String) :
    Option (List Evidence) → Option Evidence
  | none => none
  | some children => some (.con name children)

private def prodOption : Option (List Evidence) → Option Evidence
  | none => none
  | some components => some (.prod components)

private def consOption :
    Option Evidence → Option (List Evidence) → Option (List Evidence)
  | some head, some tail => some (head :: tail)
  | _, _ => none

@[simp] private theorem option_bind_some_identity
    {α : Type} (value : Option α) :
    value.bind some = value := by
  cases value <;> rfl

private theorem merge_known_eq (left right : Leaf) :
    merge (.known left) (.known right) =
      if left = right then some (.known left) else none := rfl

@[simp] private theorem merge_known_con
    (leaf : Leaf) (name : String) (children : List Evidence) :
    merge (.known leaf) (.con name children) = none := rfl

@[simp] private theorem merge_con_known
    (name : String) (children : List Evidence) (leaf : Leaf) :
    merge (.con name children) (.known leaf) = none := rfl

@[simp] private theorem merge_known_prod
    (leaf : Leaf) (components : List Evidence) :
    merge (.known leaf) (.prod components) = none := rfl

@[simp] private theorem merge_prod_known
    (components : List Evidence) (leaf : Leaf) :
    merge (.prod components) (.known leaf) = none := rfl

@[simp] private theorem merge_con_prod
    (name : String) (children components : List Evidence) :
    merge (.con name children) (.prod components) = none := rfl

@[simp] private theorem merge_prod_con
    (components : List Evidence) (name : String)
    (children : List Evidence) :
    merge (.prod components) (.con name children) = none := rfl

private theorem merge_con_eq
    (leftName rightName : String)
    (leftChildren rightChildren : List Evidence) :
    merge (.con leftName leftChildren) (.con rightName rightChildren) =
      if leftName = rightName then
        conOption leftName (mergeList leftChildren rightChildren)
      else none := by
  by_cases names_eq : leftName = rightName
  · subst rightName
    cases children_eq : mergeList leftChildren rightChildren <;>
      simp [merge, conOption, children_eq]
  · simp [merge, names_eq]

private theorem merge_prod_eq
    (left right : List Evidence) :
    merge (.prod left) (.prod right) =
      prodOption (mergeList left right) := by
  cases components_eq : mergeList left right <;>
    simp [merge, prodOption, components_eq]

@[simp] private theorem conOption_bind_known_right
  (name : String) (children : Option (List Evidence)) (leaf : Leaf) :
    (conOption name children).bind
        (fun merged => merge merged (.known leaf)) = none := by
  cases children <;> simp [conOption, merge_con_known]

@[simp] private theorem conOption_bind_known_left
    (name : String) (children : Option (List Evidence)) (leaf : Leaf) :
    (conOption name children).bind
        (fun merged => merge (.known leaf) merged) = none := by
  cases children <;> simp [conOption, merge_known_con]

@[simp] private theorem conOption_bind_prod_right
    (name : String) (children : Option (List Evidence))
    (components : List Evidence) :
    (conOption name children).bind
        (fun merged => merge merged (.prod components)) = none := by
  cases children <;> simp [conOption, merge_con_prod]

@[simp] private theorem conOption_bind_prod_left
    (name : String) (children : Option (List Evidence))
    (components : List Evidence) :
    (conOption name children).bind
        (fun merged => merge (.prod components) merged) = none := by
  cases children <;> simp [conOption, merge_prod_con]

@[simp] private theorem prodOption_bind_known_right
    (components : Option (List Evidence)) (leaf : Leaf) :
    (prodOption components).bind
        (fun merged => merge merged (.known leaf)) = none := by
  cases components <;> simp [prodOption, merge_prod_known]

@[simp] private theorem prodOption_bind_known_left
    (components : Option (List Evidence)) (leaf : Leaf) :
    (prodOption components).bind
        (fun merged => merge (.known leaf) merged) = none := by
  cases components <;> simp [prodOption, merge_known_prod]

@[simp] private theorem prodOption_bind_con_right
    (components : Option (List Evidence))
    (name : String) (children : List Evidence) :
    (prodOption components).bind
        (fun merged => merge merged (.con name children)) = none := by
  cases components <;> simp [prodOption, merge_prod_con]

@[simp] private theorem prodOption_bind_con_left
    (components : Option (List Evidence))
    (name : String) (children : List Evidence) :
    (prodOption components).bind
        (fun merged => merge (.con name children) merged) = none := by
  cases components <;> simp [prodOption, merge_con_prod]

private theorem conOption_bind_right
    (name : String) (children : Option (List Evidence))
    (right : List Evidence) :
    (conOption name children).bind
        (fun merged => merge merged (.con name right)) =
      conOption name
        (children.bind (fun left => mergeList left right)) := by
  cases children <;> simp [conOption, merge_con_eq]

private theorem conOption_bind_left
    (name : String) (children : Option (List Evidence))
    (left : List Evidence) :
    (conOption name children).bind
        (fun merged => merge (.con name left) merged) =
      conOption name
        (children.bind (fun right => mergeList left right)) := by
  cases children <;> simp [conOption, merge_con_eq]

private theorem conOption_bind_right_ne
    {leftName rightName : String} (names_ne : leftName ≠ rightName)
    (children : Option (List Evidence)) (right : List Evidence) :
    (conOption leftName children).bind
        (fun merged => merge merged (.con rightName right)) = none := by
  cases children <;> simp [conOption, merge_con_eq, names_ne]

private theorem conOption_bind_left_ne
    {leftName rightName : String} (names_ne : leftName ≠ rightName)
    (children : Option (List Evidence)) (left : List Evidence) :
    (conOption rightName children).bind
        (fun merged => merge (.con leftName left) merged) = none := by
  cases children <;> simp [conOption, merge_con_eq, names_ne]

private theorem prodOption_bind_right
    (components : Option (List Evidence)) (right : List Evidence) :
    (prodOption components).bind
        (fun merged => merge merged (.prod right)) =
      prodOption
        (components.bind (fun left => mergeList left right)) := by
  cases components <;> simp [prodOption, merge_prod_eq]

private theorem prodOption_bind_left
    (components : Option (List Evidence)) (left : List Evidence) :
    (prodOption components).bind
        (fun merged => merge (.prod left) merged) =
      prodOption
        (components.bind (fun right => mergeList left right)) := by
  cases components <;> simp [prodOption, merge_prod_eq]

private theorem consOption_bind_right
    (head : Option Evidence) (tail : Option (List Evidence))
    (rightHead : Evidence) (rightTail : List Evidence) :
    (consOption head tail).bind
        (fun merged => mergeList merged (rightHead :: rightTail)) =
      consOption
        (head.bind (fun left => merge left rightHead))
        (tail.bind (fun left => mergeList left rightTail)) := by
  cases head <;> cases tail <;> simp [consOption, mergeList]

private theorem consOption_bind_left
    (head : Option Evidence) (tail : Option (List Evidence))
    (leftHead : Evidence) (leftTail : List Evidence) :
    (consOption head tail).bind
        (fun merged => mergeList (leftHead :: leftTail) merged) =
      consOption
        (head.bind (fun right => merge leftHead right))
        (tail.bind (fun right => mergeList leftTail right)) := by
  cases head <;> cases tail <;> simp [consOption, mergeList]

private theorem mergeList_cons_eq
    (leftHead rightHead : Evidence)
    (leftTail rightTail : List Evidence) :
    mergeList (leftHead :: leftTail) (rightHead :: rightTail) =
      consOption (merge leftHead rightHead)
        (mergeList leftTail rightTail) := by
  cases head_eq : merge leftHead rightHead <;>
    cases tail_eq : mergeList leftTail rightTail <;>
      simp [mergeList, consOption, head_eq, tail_eq]

@[simp] private theorem consOption_bind_nil_right
    (head : Option Evidence) (tail : Option (List Evidence)) :
    (consOption head tail).bind
        (fun merged => mergeList merged []) = none := by
  cases head <;> cases tail <;> simp [consOption, mergeList]

@[simp] private theorem consOption_bind_nil_left
    (head : Option Evidence) (tail : Option (List Evidence)) :
    (consOption head tail).bind
        (fun merged => mergeList [] merged) = none := by
  cases head <;> cases tail <;> simp [consOption, mergeList]

set_option linter.unusedSimpArgs false in
/-- Exact partial merge is associative, including failure on either side. -/
theorem merge_assoc (left middle right : Evidence) :
    (merge left middle).bind (fun merged => merge merged right) =
      (merge middle right).bind (fun merged => merge left merged) := by
  revert middle right
  induction left using Evidence.rec
    (motive_2 := fun left =>
      ∀ middle right,
        (mergeList left middle).bind
            (fun merged => mergeList merged right) =
          (mergeList middle right).bind
            (fun merged => mergeList left merged))
  case unseen =>
    intro middle right
    cases middle <;> cases right <;>
      simp [merge_known_eq, merge_con_eq, merge_prod_eq]
  case known left =>
    intro middle right
    cases middle <;> cases right <;>
      try simp [merge_known_eq, merge_con_eq, merge_prod_eq]
    case known.known =>
      rename_i middle right
      by_cases left_middle : left = middle <;>
        by_cases middle_right : middle = right <;>
          simp_all [merge_known_eq]
    case con.con =>
      rename_i middleName middleChildren rightName rightChildren
      by_cases names_eq : middleName = rightName
      · subst rightName
        simp [merge_con_eq, conOption_bind_known_left]
      · simp [merge_con_eq, names_eq]
  case con leftName leftChildren children_ih =>
    intro middle right
    cases middle <;> cases right <;>
      try simp_all [merge_known_eq, merge_con_eq, merge_prod_eq,
        conOption_bind_right, conOption_bind_left,
        conOption_bind_right_ne, conOption_bind_left_ne]
    case known.known =>
      rename_i middle right
      by_cases leaves_eq : middle = right <;>
        simp [merge_known_eq, leaves_eq]
    case con.known =>
      rename_i middleName middleChildren right
      by_cases names_eq : leftName = middleName
      · subst middleName
        cases children_eq :
            mergeList leftChildren middleChildren <;>
          simp [merge_con_eq, conOption, children_eq]
      · simp [merge_con_eq, names_eq]
    case con.con =>
      rename_i middleName middleChildren rightName rightChildren
      by_cases left_middle : leftName = middleName
      · subst middleName
        by_cases left_right : leftName = rightName
        · subst rightName
          simpa [merge_con_eq, conOption_bind_right,
            conOption_bind_left] using
            congrArg (conOption leftName)
              (children_ih middleChildren rightChildren)
        · simp [merge_con_eq, left_right, conOption_bind_right_ne]
      · by_cases middle_right : middleName = rightName
        · subst rightName
          simp [merge_con_eq, left_middle, conOption_bind_left_ne]
        · simp [merge_con_eq, left_middle, middle_right]
    case con.prod =>
      rename_i middleName middleChildren rightComponents
      by_cases names_eq : leftName = middleName
      · subst middleName
        cases children_eq :
            mergeList leftChildren middleChildren <;>
          simp [merge_con_eq, conOption, children_eq]
      · simp [merge_con_eq, names_eq]
  case prod leftComponents components_ih =>
    intro middle right
    cases middle <;> cases right <;>
      try simp_all [merge_known_eq, merge_con_eq, merge_prod_eq,
        prodOption_bind_right, prodOption_bind_left]
    case known.known =>
      rename_i middle right
      by_cases leaves_eq : middle = right <;>
        simp [merge_known_eq, leaves_eq]
    case con.con =>
      rename_i middleName middleChildren rightName rightChildren
      by_cases names_eq : middleName = rightName
      · subst rightName
        simp [merge_con_eq, conOption_bind_prod_left]
      · simp [merge_con_eq, names_eq]
  case nil middle right =>
    cases middle with
    | nil =>
        cases right <;> rfl
    | cons middleHead middleTail =>
        cases right with
        | nil => rfl
        | cons rightHead rightTail =>
            rw [mergeList_cons_eq, consOption_bind_nil_left]
            simp [mergeList]
  case cons left leftRest head_ih tail_ih middle right =>
    cases middle with
    | nil =>
        cases right <;> rfl
    | cons middleHead middleTail =>
        cases right with
        | nil =>
            rw [mergeList_cons_eq, consOption_bind_nil_right]
            simp [mergeList]
        | cons rightHead rightTail =>
            simp only [mergeList_cons_eq, consOption_bind_right,
              consOption_bind_left]
            rw [head_ih middleHead rightHead,
              tail_ih middleTail rightTail]

/--
Two pieces of evidence may be exchanged while merging into an accumulated
suffix result.
-/
theorem merge_swap_over_right
    (left middle right : Evidence) :
    (merge middle right).bind (fun merged => merge left merged) =
      (merge left right).bind (fun merged => merge middle merged) := by
  calc
    (merge middle right).bind (fun merged => merge left merged)
        = (merge left middle).bind
            (fun merged => merge merged right) :=
          (merge_assoc left middle right).symm
    _ = (merge middle left).bind
            (fun merged => merge merged right) := by
          rw [merge_comm left middle]
    _ = (merge left right).bind
            (fun merged => merge middle merged) :=
          merge_assoc middle left right

/-- Swapping the first two clauses does not change their exact fold. -/
theorem mergeAll_swap_head
    (left middle : Evidence) (rest : List Evidence) :
    mergeAll (left :: middle :: rest) =
      mergeAll (middle :: left :: rest) := by
  cases rest_eq : mergeAll rest with
  | none => simp [mergeAll, rest_eq]
  | some accumulated =>
      simp only [mergeAll, rest_eq]
      have swap := merge_swap_over_right left middle accumulated
      cases middle_eq : merge middle accumulated <;>
        cases left_eq : merge left accumulated <;>
          simp [middle_eq, left_eq] at swap ⊢
      all_goals exact swap

/-- An adjacent swap at any list position preserves `mergeAll`. -/
theorem mergeAll_swap_adjacent
    (before : List Evidence) (left middle : Evidence)
    (suffix : List Evidence) :
    mergeAll (before ++ left :: middle :: suffix) =
      mergeAll (before ++ middle :: left :: suffix) := by
  induction before with
  | nil =>
      simpa using mergeAll_swap_head left middle suffix
  | cons evidence before before_ih =>
      simp only [List.cons_append, mergeAll, before_ih]

/-- Exact clause evidence folding is invariant under every permutation. -/
theorem mergeAll_perm
    {left right : List Evidence} (permutation : left.Perm right) :
    mergeAll left = mergeAll right := by
  induction permutation with
  | nil => rfl
  | cons evidence permutation permutation_ih =>
      simp only [mergeAll, permutation_ih]
  | swap first second rest =>
      exact (mergeAll_swap_head first second rest).symm
  | trans left_middle middle_right left_ih right_ih =>
      exact left_ih.trans right_ih

/-- Shape inference is independent of the order in which clause evidence is collected. -/
theorem inferShape_perm
    (observable : Observability)
    {left right : List Evidence} (permutation : left.Perm right) :
    inferShape observable left = inferShape observable right := by
  unfold inferShape
  rw [mergeAll_perm permutation]

theorem merge_known_vars_ne {left right : CapVar} (h : left ≠ right) :
    merge (.known (.var left)) (.known (.var right)) = none := by
  simp [merge, h]

theorem merge_constructor_names_ne
    {leftName rightName : String} {leftChildren rightChildren : List Evidence}
    (h : leftName ≠ rightName) :
    merge (.con leftName leftChildren) (.con rightName rightChildren) = none := by
  simp [merge, h]

/-- Lists with different arities cannot be pointwise merged. -/
theorem mergeList_length_ne
    {left right : List Evidence} (h : left.length ≠ right.length) :
    mergeList left right = none := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact (h rfl).elim
      | cons right rightRest => rfl
  | cons evidence rest rest_ih =>
      cases right with
      | nil => rfl
      | cons right rightRest =>
          have tailLengthNe : rest.length ≠ rightRest.length := by
            intro lengths_eq
            exact h (congrArg Nat.succ lengths_eq)
          simp [mergeList, rest_ih tailLengthNe]

theorem merge_constructor_arity_ne
    {name : String} {leftChildren rightChildren : List Evidence}
    (h : leftChildren.length ≠ rightChildren.length) :
    merge (.con name leftChildren) (.con name rightChildren) = none := by
  simp [merge, mergeList_length_ne h]

theorem merge_product_arity_ne
    {leftComponents rightComponents : List Evidence}
    (h : leftComponents.length ≠ rightComponents.length) :
    merge (.prod leftComponents) (.prod rightComponents) = none := by
  simp [merge, mergeList_length_ne h]

@[simp] theorem merge_constructor_product_mismatch
    (name : String) (children components : List Evidence) :
    merge (.con name children) (.prod components) = none := rfl

@[simp] theorem inferShape_empty (observable : Observability) :
    inferShape observable [] = some .any := rfl

@[simp] theorem inferShape_catchAll (observable : Observability) :
    inferShape observable [.unseen] = some .any := rfl

@[simp] theorem finalize_unseen (observable : Observability) :
    finalize observable .unseen = none := rfl

theorem finalize_observable_unseen
    {observable : Observability} {name : String}
    (h : observable name = some [true]) :
    finalize observable (.con name [.unseen]) = none := by
  simp [finalize, finalizeMasked, h]

theorem finalize_unobservable_child
    {observable : Observability} {name : String} {evidence : Evidence}
    (h : observable name = some [false])
    (ordinary : finalizeHidden evidence = .any) :
    finalize observable (.con name [evidence]) =
      some (.con name [.any]) := by
  simp [finalize, finalizeMasked, h, ordinary]

/-- A hidden delegated child retains the exact capability handled by its next
matcher. -/
theorem finalize_unobservable_delegated_child
    {observable : Observability} {name : String} {capability : Cap}
    (h : observable name = some [false]) :
    finalize observable
        (.con name [.known (.delegated capability)]) =
      some (.con name [capability]) := by
  simp [finalize, finalizeMasked, finalizeHidden, h]

set_option linter.unusedSimpArgs false in
/--
Canonical complete capabilities merge precisely when they are equal.

In particular, exact merge never treats two distinct capability variables as
unification variables.
-/
theorem merge_ofCap_exact (left right : Cap) :
    merge (ofCap left) (ofCap right) =
      if left = right then some (ofCap left) else none := by
  revert right
  induction left using Cap.rec
    (motive_2 := fun lefts =>
      ∀ rights,
        mergeList (lefts.map ofCap) (rights.map ofCap) =
          if lefts = rights then some (lefts.map ofCap) else none)
  case any =>
    intro right
    cases right <;> simp [ofCap, merge]
  case var left =>
    intro right
    cases right <;> simp [ofCap, merge]
  case skolem left =>
    intro right
    cases right <;> simp [ofCap, merge]
  case con leftName leftChildren children_ih =>
    intro right
    cases right with
    | any => simp [ofCap, merge]
    | var right => simp [ofCap, merge]
    | skolem right => simp [ofCap, merge]
    | prod rightComponents => simp [ofCap]
    | con rightName rightChildren =>
        by_cases names_eq : leftName = rightName
        · subst rightName
          by_cases children_eq : leftChildren = rightChildren
          · subst rightChildren
            simp [ofCap, merge, children_ih]
          · simp [ofCap, merge, children_eq, children_ih]
        · simp [ofCap, merge, names_eq]
  case prod leftComponents components_ih =>
    intro right
    cases right with
    | any => simp [ofCap, merge]
    | var right => simp [ofCap, merge]
    | skolem right => simp [ofCap, merge]
    | con rightName rightChildren => simp [ofCap, merge]
    | prod rightComponents =>
        by_cases components_eq : leftComponents = rightComponents
        · subst rightComponents
          simp [ofCap, merge, components_ih]
        · simp [ofCap, merge, components_eq, components_ih]
  case nil rights =>
    cases rights <;> simp [mergeList]
  case cons left leftRest head_ih tail_ih rights =>
    cases rights with
    | nil => simp [mergeList]
    | cons right rightRest =>
        by_cases head_eq : left = right
        · subst right
          by_cases tail_eq : leftRest = rightRest
          · subst rightRest
            simp [mergeList, head_ih, tail_ih]
          · simp [mergeList, head_ih, tail_ih, tail_eq]
        · simp [mergeList, head_ih, tail_ih, head_eq]

/-! ## Capability alpha-transport -/

mutual

/-- Finalization commutes with capability alpha-renaming. -/
theorem finalize_applyRen
    (observable : Observability) (r : CapVar → CapVar)
    (evidence : Evidence) :
    finalize observable (evidence.applyRen r) =
      (finalize observable evidence).map (Cap.applyRen r) := by
  cases evidence with
  | unseen => simp [Evidence.applyRen, finalize]
  | known leaf =>
      cases leaf <;>
        simp [Evidence.applyRen, Leaf.applyRen, finalize, Leaf.toCap,
          Cap.applyRen]
  | con name children =>
      simp only [Evidence.applyRen, finalize]
      cases observableAtName : observable name with
      | none => simp
      | some mask =>
          simp only
          rw [finalizeMasked_applyRen]
          cases finalized : finalizeMasked observable mask children <;>
            simp [Cap.applyRen]
  | prod components =>
      simp only [Evidence.applyRen, finalize]
      rw [finalizeList_applyRen]
      cases finalized : finalizeList observable components <;>
        simp [Cap.applyRen]

/-- List form of `finalize_applyRen`. -/
theorem finalizeList_applyRen
    (observable : Observability) (r : CapVar → CapVar)
    (evidence : List Evidence) :
    finalizeList observable (Evidence.applyRenList r evidence) =
      (finalizeList observable evidence).map (Cap.applyRenList r) := by
  cases evidence with
  | nil => rfl
  | cons head tail =>
      simp only [Evidence.applyRenList, finalizeList]
      rw [finalize_applyRen, finalizeList_applyRen]
      cases headFinalized : finalize observable head <;>
        cases tailFinalized : finalizeList observable tail <;>
          simp [Cap.applyRenList]

/-- Masked form of `finalize_applyRen`. -/
theorem finalizeMasked_applyRen
    (observable : Observability) (r : CapVar → CapVar)
    (mask : List Bool) (evidence : List Evidence) :
    finalizeMasked observable mask (Evidence.applyRenList r evidence) =
      (finalizeMasked observable mask evidence).map (Cap.applyRenList r) := by
  cases mask with
  | nil =>
      cases evidence <;> rfl
  | cons isObservable mask =>
      cases evidence with
      | nil => rfl
      | cons head tail =>
          cases isObservable <;>
            simp only [Evidence.applyRenList, finalizeMasked]
          · rw [finalizeHidden_applyRen, finalizeMasked_applyRen]
            cases tailFinalized : finalizeMasked observable mask tail <;>
              simp [Cap.applyRenList]
          · rw [finalize_applyRen, finalizeMasked_applyRen]
            cases headFinalized : finalize observable head <;>
              cases tailFinalized : finalizeMasked observable mask tail <;>
                simp [Cap.applyRenList]

end

/-! ## Flexible capability variables of partial evidence -/

/-- Flexible capability variables of a complete evidence leaf. -/
def Leaf.fcv : Leaf → List CapVar
  | .any => []
  | .var varId => [varId]
  | .skolem _ => []
  | .delegated capability => capability.fcv

/-- Leaf embedding preserves flexible capability variables. -/
theorem Leaf.fcv_toCap : ∀ leaf : Leaf, leaf.toCap.fcv = leaf.fcv
  | .any => rfl
  | .var _ => rfl
  | .skolem _ => rfl
  | .delegated _ => rfl

mutual

/-- Flexible capability variables occurring in partial evidence. -/
def Evidence.fcv : Evidence → List CapVar
  | .unseen => []
  | .known leaf => leaf.fcv
  | .con _ children => Evidence.fcvList children
  | .prod components => Evidence.fcvList components

/-- Flexible capability variables of an evidence list. -/
def Evidence.fcvList : List Evidence → List CapVar
  | [] => []
  | evidence :: rest => evidence.fcv ++ Evidence.fcvList rest

end

/-- Hidden delegated evidence preserves the complete capability's variables. -/
@[simp] theorem fcv_hiddenDelegatedCap (capability : Cap) :
    (hiddenDelegatedCap capability).fcv = capability.fcv := by
  cases capability <;> rfl

/-- Hidden-parameter completion introduces no flexible variable absent from
its evidence. -/
theorem finalizeHidden_fcv (evidence : Evidence) :
    (finalizeHidden evidence).fcv ⊆ evidence.fcv := by
  cases evidence with
  | unseen =>
      intro varId membership
      exact nomatch membership
  | known leaf =>
      cases leaf with
      | delegated capability =>
          exact fun _ membership => membership
      | any | var | skolem =>
          intro varId membership
          exact nomatch membership
  | con name children =>
      intro varId membership
      exact nomatch membership
  | prod components =>
      intro varId membership
      exact nomatch membership

/-- Membership in the variables of an evidence list is membership in the
variables of one member. -/
theorem Evidence.mem_fcvList {varId : CapVar} :
    ∀ {evidences : List Evidence},
      varId ∈ Evidence.fcvList evidences ↔
        ∃ evidence ∈ evidences, varId ∈ evidence.fcv
  | [] => by simp [Evidence.fcvList]
  | evidence :: rest => by
      simp [Evidence.fcvList, List.mem_append,
        Evidence.mem_fcvList (evidences := rest)]

/-- Capability embedding preserves flexible capability variables. -/
theorem fcv_ofCap :
    ∀ capability : Cap, (ofCap capability).fcv = capability.fcv := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities =>
        Evidence.fcvList (capabilities.map ofCap) =
          Cap.fcvList capabilities) with
  | any => simp [ofCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | var varId => simp [ofCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | skolem name => simp [ofCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | con name children childrenInduction =>
      simp only [ofCap, Evidence.fcv, Cap.fcv, childrenInduction]
  | prod components componentsInduction =>
      simp only [ofCap, Evidence.fcv, Cap.fcv, componentsInduction]
  | nil => simp [Evidence.fcvList, Cap.fcvList]
  | cons capability capabilities capabilityInduction
      capabilitiesInduction =>
      simp only [List.map_cons, Evidence.fcvList, Cap.fcvList,
        capabilityInduction, capabilitiesInduction]

/-- Delegated embedding preserves every flexible capability variable. -/
theorem fcv_ofDelegatedCap (observable : Observability) :
    ∀ capability : Cap,
      (ofDelegatedCap observable capability).fcv = capability.fcv := by
  intro capability
  induction capability using Cap.rec
      (motive_2 := fun capabilities =>
        Evidence.fcvList
              (capabilities.map (ofDelegatedCap observable)) =
            Cap.fcvList capabilities ∧
          ∀ mask evidence,
            ofDelegatedCapsMasked observable mask capabilities =
                some evidence →
              Evidence.fcvList evidence = Cap.fcvList capabilities) with
  | any =>
      simp [ofDelegatedCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | var varId =>
      simp [ofDelegatedCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | skolem name =>
      simp [ofDelegatedCap, Evidence.fcv, Leaf.fcv, Cap.fcv]
  | con name children childrenInduction =>
      simp only [ofDelegatedCap]
      cases observableResult : observable name with
      | none =>
          simp [Evidence.fcv, Leaf.fcv, Cap.fcv]
      | some mask =>
          cases embedded :
              ofDelegatedCapsMasked observable mask children with
          | none =>
              simp [embedded, Evidence.fcv, Leaf.fcv, Cap.fcv]
          | some evidence =>
              simpa [embedded, Evidence.fcv, Cap.fcv] using
                childrenInduction.2 mask evidence embedded
  | prod components componentsInduction =>
      simpa [ofDelegatedCap, Evidence.fcv, Cap.fcv] using
        componentsInduction.1
  | nil =>
      constructor
      · rfl
      · intro mask evidence success
        cases mask with
        | nil =>
            simp [ofDelegatedCapsMasked] at success
            subst evidence
            rfl
        | cons _ _ =>
            simp [ofDelegatedCapsMasked] at success
  | cons capability capabilities capabilityInduction
      capabilitiesInduction =>
      constructor
      · simp only [List.map_cons, Evidence.fcvList, Cap.fcvList,
          capabilityInduction, capabilitiesInduction.1]
      · intro mask evidence success
        cases mask with
        | nil =>
            simp [ofDelegatedCapsMasked] at success
        | cons isObservable mask =>
            simp only [ofDelegatedCapsMasked] at success
            cases tailEmbedded :
                ofDelegatedCapsMasked observable mask capabilities with
            | none =>
                simp [tailEmbedded] at success
            | some tail =>
                have evidenceEquality :
                    evidence =
                      (if isObservable then
                          ofDelegatedCap observable capability
                        else hiddenDelegatedCap capability) :: tail := by
                  simpa [tailEmbedded] using success.symm
                subst evidence
                cases isObservable <;>
                  simp only [Bool.false_eq_true, if_false, if_true,
                    Evidence.fcvList, Cap.fcvList,
                    fcv_hiddenDelegatedCap,
                    capabilityInduction,
                    capabilitiesInduction.2 mask tail tailEmbedded]

/-- Variables of an embedded capability list are the original variables. -/
theorem fcvList_map_ofCap :
    ∀ capabilities : List Cap,
      Evidence.fcvList (capabilities.map ofCap) = Cap.fcvList capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp only [List.map_cons, Evidence.fcvList, Cap.fcvList,
        fcv_ofCap capability, fcvList_map_ofCap capabilities]

mutual

/-- Exact merge introduces no flexible variables beyond its operands. -/
theorem merge_fcv :
    ∀ {left right merged : Evidence},
      merge left right = some merged →
      merged.fcv ⊆ left.fcv ++ right.fcv
  | .unseen, _, _, h => by
      cases h
      intro varId mem
      exact List.mem_append.mpr (Or.inr mem)
  | .known _, .unseen, _, h => by
      cases h
      intro varId mem
      exact List.mem_append.mpr (Or.inl mem)
  | .con _ _, .unseen, _, h => by
      cases h
      intro varId mem
      exact List.mem_append.mpr (Or.inl mem)
  | .prod _, .unseen, _, h => by
      cases h
      intro varId mem
      exact List.mem_append.mpr (Or.inl mem)
  | .known left, .known right, merged, h => by
      simp only [merge] at h
      by_cases heq : left = right
      · rw [if_pos heq] at h
        cases h
        intro varId mem
        exact List.mem_append.mpr (Or.inl mem)
      · rw [if_neg heq] at h
        exact nomatch h
  | .con leftName leftChildren, .con rightName rightChildren, merged,
      h => by
      simp only [merge] at h
      by_cases hname : leftName = rightName
      · rw [if_pos hname] at h
        cases hchildren : mergeList leftChildren rightChildren with
        | none => rw [hchildren] at h; exact nomatch h
        | some children =>
            rw [hchildren] at h
            cases h
            intro varId mem
            have mem' : varId ∈ Evidence.fcvList children := mem
            rcases List.mem_append.mp (mergeList_fcv hchildren mem') with
              hl | hr
            · exact List.mem_append.mpr (Or.inl hl)
            · exact List.mem_append.mpr (Or.inr hr)
      · rw [if_neg hname] at h
        exact nomatch h
  | .prod leftComponents, .prod rightComponents, merged, h => by
      simp only [merge] at h
      cases hcomponents : mergeList leftComponents rightComponents with
      | none => rw [hcomponents] at h; exact nomatch h
      | some components =>
          rw [hcomponents] at h
          cases h
          intro varId mem
          have mem' : varId ∈ Evidence.fcvList components := mem
          rcases List.mem_append.mp (mergeList_fcv hcomponents mem') with
            hl | hr
          · exact List.mem_append.mpr (Or.inl hl)
          · exact List.mem_append.mpr (Or.inr hr)
  | .known _, .con _ _, _, h => nomatch h
  | .known _, .prod _, _, h => nomatch h
  | .con _ _, .known _, _, h => nomatch h
  | .con _ _, .prod _, _, h => nomatch h
  | .prod _, .known _, _, h => nomatch h
  | .prod _, .con _ _, _, h => nomatch h

/-- List form of `merge_fcv`. -/
theorem mergeList_fcv :
    ∀ {lefts rights merged : List Evidence},
      mergeList lefts rights = some merged →
      Evidence.fcvList merged ⊆
        Evidence.fcvList lefts ++ Evidence.fcvList rights
  | [], [], _, h => by
      cases h
      intro varId mem
      simp only [Evidence.fcvList] at mem
      exact nomatch mem
  | left :: leftRest, right :: rightRest, merged, h => by
      simp only [mergeList] at h
      cases hhead : merge left right with
      | none => rw [hhead] at h; exact nomatch h
      | some head =>
          cases htail : mergeList leftRest rightRest with
          | none => rw [hhead, htail] at h; exact nomatch h
          | some tail =>
              rw [hhead, htail] at h
              cases h
              intro varId mem
              simp only [Evidence.fcvList, List.mem_append] at mem ⊢
              rcases mem with hh | ht
              · rcases List.mem_append.mp (merge_fcv hhead hh) with
                  hl | hr
                · exact Or.inl (Or.inl hl)
                · exact Or.inr (Or.inl hr)
              · rcases List.mem_append.mp (mergeList_fcv htail ht) with
                  hl | hr
                · exact Or.inl (Or.inr hl)
                · exact Or.inr (Or.inr hr)
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

end

/-- Folded exact merge introduces no flexible variables beyond its inputs. -/
theorem mergeAll_fcv :
    ∀ {evidences : List Evidence} {merged : Evidence},
      mergeAll evidences = some merged →
      merged.fcv ⊆ Evidence.fcvList evidences
  | [], _, h => by
      cases h
      intro varId mem
      simp only [Evidence.fcv] at mem
      exact nomatch mem
  | evidence :: rest, merged, h => by
      simp only [mergeAll] at h
      cases haccum : mergeAll rest with
      | none => rw [haccum] at h; exact nomatch h
      | some accumulated =>
          rw [haccum] at h
          intro varId mem
          simp only [Evidence.fcvList, List.mem_append]
          rcases List.mem_append.mp (merge_fcv h mem) with hl | hr
          · exact Or.inl hl
          · exact Or.inr (mergeAll_fcv haccum hr)

mutual

/-- Finalization introduces no flexible variables beyond its evidence. -/
theorem finalize_fcv {observable : Observability} :
    ∀ {evidence : Evidence} {capability : Cap},
      finalize observable evidence = some capability →
      capability.fcv ⊆ evidence.fcv
  | .unseen, _, h => nomatch h
  | .known leaf, _, h => by
      cases h
      intro varId mem
      rw [Leaf.fcv_toCap] at mem
      exact mem
  | .con name children, capability, h => by
      simp only [finalize] at h
      split at h
      · exact nomatch h
      · split at h
        · rename_i capabilities hmasked
          cases h
          intro varId mem
          exact finalizeMasked_fcv hmasked mem
        · exact nomatch h
  | .prod components, capability, h => by
      simp only [finalize] at h
      split at h
      · rename_i capabilities hlist
        cases h
        intro varId mem
        exact finalizeList_fcv hlist mem
      · exact nomatch h

/-- List form of `finalize_fcv`. -/
theorem finalizeList_fcv {observable : Observability} :
    ∀ {evidences : List Evidence} {capabilities : List Cap},
      finalizeList observable evidences = some capabilities →
      Cap.fcvList capabilities ⊆ Evidence.fcvList evidences
  | [], _, h => by
      cases h
      intro varId mem
      simp only [Cap.fcvList] at mem
      exact nomatch mem
  | evidence :: rest, capabilities, h => by
      simp only [finalizeList] at h
      cases hhead : finalize observable evidence with
      | none => rw [hhead] at h; exact nomatch h
      | some capability =>
          cases htail : finalizeList observable rest with
          | none => rw [hhead, htail] at h; exact nomatch h
          | some rest' =>
              rw [hhead, htail] at h
              cases h
              intro varId mem
              simp only [Cap.fcvList, List.mem_append] at mem
              simp only [Evidence.fcvList, List.mem_append]
              rcases mem with hh | ht
              · exact Or.inl (finalize_fcv hhead hh)
              · exact Or.inr (finalizeList_fcv htail ht)

/-- Masked form of `finalize_fcv`. -/
theorem finalizeMasked_fcv {observable : Observability} :
    ∀ {mask : List Bool} {evidences : List Evidence}
      {capabilities : List Cap},
      finalizeMasked observable mask evidences = some capabilities →
      Cap.fcvList capabilities ⊆ Evidence.fcvList evidences
  | [], [], _, h => by
      cases h
      intro varId mem
      simp only [Cap.fcvList] at mem
      exact nomatch mem
  | isObservable :: mask, evidence :: rest, capabilities, h => by
      simp only [finalizeMasked] at h
      cases isObservable with
      | true =>
          simp only [if_pos] at h
          cases hhead : finalize observable evidence with
          | none => rw [hhead] at h; exact nomatch h
          | some capability =>
              cases htail : finalizeMasked observable mask rest with
              | none => rw [hhead, htail] at h; exact nomatch h
              | some rest' =>
                  rw [hhead, htail] at h
                  cases h
                  intro varId mem
                  simp only [Cap.fcvList, List.mem_append] at mem
                  simp only [Evidence.fcvList, List.mem_append]
                  rcases mem with hh | ht
                  · exact Or.inl (finalize_fcv hhead hh)
                  · exact Or.inr (finalizeMasked_fcv htail ht)
      | false =>
          simp only [Bool.false_eq_true, if_neg, not_false_eq_true] at h
          cases htail : finalizeMasked observable mask rest with
          | none => rw [htail] at h; exact nomatch h
          | some rest' =>
              rw [htail] at h
              cases h
              intro varId mem
              simp only [Cap.fcvList, List.mem_append] at mem
              simp only [Evidence.fcvList, List.mem_append]
              rcases mem with headMem | tailMem
              · exact Or.inl (finalizeHidden_fcv evidence headMem)
              · exact Or.inr (finalizeMasked_fcv htail tailMem)
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

end

/-- Shape inference introduces no flexible variables beyond its clause
evidence. -/
theorem inferShape_fcv {observable : Observability}
    {clauses : List Evidence} {capability : Cap}
    (h : inferShape observable clauses = some capability) :
    capability.fcv ⊆ Evidence.fcvList clauses := by
  unfold inferShape at h
  split at h
  · exact nomatch h
  · rename_i hmerged
    cases h
    intro varId mem
    simp only [Cap.fcv] at mem
    exact nomatch mem
  · rename_i evidence _ hmerged
    intro varId mem
    exact mergeAll_fcv hmerged (finalize_fcv h mem)

end Shape
end TypePM
