import TypePM.ClauseEvidence
import TypePM.CapTarget

/-!
# Executable List-former clause-evidence examples

These examples instantiate the paper core's frozen `List` pattern signature:
`nil` has arity zero, while `cons` and `join` have arity two.  The sole List
parameter is observable.  All clauses below are actual `Clause` values; their
expression and arm bodies are intentionally inert because this module tests
only evidence, coverage, ordering, and dispatch.
-/

namespace TypePM

namespace Shape

mutual

/-- Executable equality used by the concrete evidence regressions. -/
def Evidence.eqb : Evidence → Evidence → Bool
  | .unseen, .unseen => true
  | .known left, .known right => decide (left = right)
  | .con leftName leftChildren, .con rightName rightChildren =>
      leftName == rightName && Evidence.eqbList leftChildren rightChildren
  | .prod left, .prod right => Evidence.eqbList left right
  | _, _ => false

/-- Executable componentwise equality for concrete evidence lists. -/
def Evidence.eqbList : List Evidence → List Evidence → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.eqb right && Evidence.eqbList lefts rights
  | _, _ => false

end

mutual

theorem Evidence.eqb_eq_true : ∀ (left right : Evidence),
    left.eqb right = true ↔ left = right
  | .unseen, right => by
      cases right <;> simp [Evidence.eqb]
  | .known left, right => by
      cases right <;> simp [Evidence.eqb]
  | .con name children, right => by
      cases right <;>
        simp [Evidence.eqb, Evidence.eqbList_eq_true]
  | .prod components, right => by
      cases right <;>
        simp [Evidence.eqb, Evidence.eqbList_eq_true]

theorem Evidence.eqbList_eq_true : ∀ (left right : List Evidence),
    Evidence.eqbList left right = true ↔ left = right
  | [], right => by
      cases right <;> simp [Evidence.eqbList]
  | left :: lefts, right => by
      cases right <;>
        simp [Evidence.eqbList, Evidence.eqb_eq_true,
          Evidence.eqbList_eq_true]

end

instance : BEq Evidence := ⟨Evidence.eqb⟩

instance : LawfulBEq Evidence where
  eq_of_beq h := (Evidence.eqb_eq_true _ _).mp h
  rfl := (Evidence.eqb_eq_true _ _).mpr rfl

instance : DecidableEq Evidence :=
  instDecidableEqOfLawfulBEq

end Shape

namespace ClauseEvidenceExamples

open Shape

/-! ## Frozen List signature -/

/-- Only the parameter of the canonical `List` former is observable. -/
def listObservability : Shape.Observability :=
  fun former => if former = "List" then some [true] else none

/-- Fresh target variable used by all three concrete signature instances. -/
def elementTarget : Ty := .var 0

/-- Canonical `List a` target of the concrete signature instances. -/
def listTarget : Ty := .data "List" [elementTarget]

/-- `nil : () =>_P List a`. -/
def nilProjection : Projection.ProjectionSignature listObservability where
  fieldTypes := []
  resultType := listTarget
  resultRoot := .data (mask := [true]) (by
    simp [listObservability]) (by simp)

/-- `cons : (a, List a) =>_P List a`. -/
def consProjection : Projection.ProjectionSignature listObservability where
  fieldTypes := [elementTarget, listTarget]
  resultType := listTarget
  resultRoot := .data (mask := [true]) (by
    simp [listObservability]) (by simp)

/-- `join : (List a, List a) =>_P List a`. -/
def joinProjection : Projection.ProjectionSignature listObservability where
  fieldTypes := [listTarget, listTarget]
  resultType := listTarget
  resultRoot := .data (mask := [true]) (by
    simp [listObservability]) (by simp)

/-- General pattern constructors belonging to the canonical List former. -/
def listGeneralConstructors : List GeneralCtor :=
  [("nil", 0), ("cons", 2), ("join", 2)]

/-- Frozen matcher signature used by all examples in this module. -/
def listSignature : FrozenMatcherSig where
  observability := listObservability
  patternConstructors :=
    [("nil", nilProjection),
      ("cons", consProjection),
      ("join", joinProjection)]
  constructorsByFormer := [("List", listGeneralConstructors)]

/-! ## Actual clauses -/

/-- Inert expression used where clause typing is intentionally out of scope. -/
def dummy : Expr := .something

/-- General `nil` clause. -/
def nilClause : Clause :=
  .mk (generalPP "nil" 0) dummy []

/-- General `cons $ $` clause. -/
def consClause : Clause :=
  .mk (generalPP "cons" 2) dummy []

/-- General `join $ $` clause. -/
def joinClause : Clause :=
  .mk (generalPP "join" 2) dummy []

/-- Final bare-hole catch-all with its single variable arm. -/
def catchAllClause : Clause :=
  .mk .hole dummy [.mk (.var "target") dummy]

/-- The ordinary List matcher and paper-complete multiset share root coverage. -/
def listClauses : List Clause :=
  [nilClause, consClause, joinClause, catchAllClause]

/-- Paper-complete multiset interface, including the general `join` clause. -/
def paperMultisetClauses : List Clause :=
  [nilClause, consClause, joinClause, catchAllClause]

/-- The known-incomplete multiset interface, with no general `join` clause. -/
def simplifiedMultisetClauses : List Clause :=
  [nilClause, consClause, catchAllClause]

/-! ## Concrete evidence -/

/-- Flexible producer capability used by the List matcher. -/
def elementCap : Cap := .var 0

/-- Expected inferred producer capability `List p`. -/
def listCap : Cap := .con "List" [elementCap]

/-- Evidence computed from each actual List clause, in source order. -/
def actualListEvidence : Option (List Shape.Evidence) := do
  let nilEvidence ← clauseEvidence listSignature nilClause.pp []
  let consEvidence ←
    clauseEvidence listSignature consClause.pp [elementCap, listCap]
  let joinEvidence ←
    clauseEvidence listSignature joinClause.pp [listCap, listCap]
  let catchEvidence ←
    clauseEvidence listSignature catchAllClause.pp [listCap]
  pure [nilEvidence, consEvidence, joinEvidence, catchEvidence]

/-- The four actual clauses compute the expected partial evidence trees. -/
theorem actualListEvidence_expected :
    actualListEvidence =
      some
        [.con "List" [.unseen],
          .con "List" [Shape.ofCap elementCap],
          .con "List" [Shape.ofCap elementCap],
          .unseen] := by
  native_decide

/-- Actual clause evidence infers exactly the complete capability `List p`. -/
theorem actualListEvidence_infers_list :
    ∃ evidence,
      actualListEvidence = some evidence ∧
        Shape.inferShape listObservability evidence = some listCap := by
  let expected : List Shape.Evidence :=
    [.con "List" [.unseen],
      .con "List" [Shape.ofCap elementCap],
      .con "List" [Shape.ofCap elementCap],
      .unseen]
  refine ⟨expected, actualListEvidence_expected, ?_⟩
  native_decide

/-! ## Concrete coverage -/

/-- Reusable explicit coverage proof for the three List general clauses. -/
theorem completeListCoverage
    (clauses : List Clause)
    (hnil : HasClausePP clauses (generalPP "nil" 0))
    (hcons : HasClausePP clauses (generalPP "cons" 2))
    (hjoin : HasClausePP clauses (generalPP "join" 2)) :
    CoverageOK listSignature clauses listCap := by
  refine ⟨listGeneralConstructors, rfl, ?_⟩
  intro constructor hmember
  simp [listGeneralConstructors] at hmember
  rcases hmember with rfl | rfl | rfl
  · exact hnil
  · exact hcons
  · exact hjoin

/-- The List matcher covers all frozen List pattern constructors. -/
theorem listCoverageOK :
    CoverageOK listSignature listClauses listCap := by
  apply completeListCoverage
  · exact ⟨nilClause, by simp [listClauses], rfl⟩
  · exact ⟨consClause, by simp [listClauses], rfl⟩
  · exact ⟨joinClause, by simp [listClauses], rfl⟩

/-- The paper-complete multiset interface has the same complete coverage. -/
theorem paperMultisetCoverageOK :
    CoverageOK listSignature paperMultisetClauses listCap := by
  apply completeListCoverage
  · exact ⟨nilClause, by simp [paperMultisetClauses], rfl⟩
  · exact ⟨consClause, by simp [paperMultisetClauses], rfl⟩
  · exact ⟨joinClause, by simp [paperMultisetClauses], rfl⟩

/-- Omitting `join $ $` makes the simplified multiset interface incomplete. -/
theorem simplifiedMultiset_not_coverageOK :
    ¬ CoverageOK listSignature simplifiedMultisetClauses listCap := by
  intro hcoverage
  rcases hcoverage with ⟨constructors, hlookup, hall⟩
  have hconstructors : constructors = listGeneralConstructors := by
    exact Option.some.inj (hlookup.symm.trans rfl)
  subst constructors
  have hjoin :
      HasClausePP simplifiedMultisetClauses (generalPP "join" 2) :=
    hall ("join", 2) (by simp [listGeneralConstructors])
  rcases hjoin with ⟨clause, hmember, hpattern⟩
  simp [simplifiedMultisetClauses] at hmember
  rcases hmember with rfl | rfl | rfl
  · simp [nilClause, Clause.pp, generalPP] at hpattern
  · simp [consClause, Clause.pp, generalPP] at hpattern
  · simp [catchAllClause, Clause.pp, generalPP] at hpattern

/-! ## Catch-all ordering and dispatch -/

/-- The List matcher has the required unique final catch-all. -/
theorem listCatchAllLast : CatchAllLast listClauses := by
  refine ⟨[nilClause, consClause, joinClause], dummy,
    "target", dummy, rfl, ?_⟩
  intro clause hmember
  simp at hmember
  rcases hmember with rfl | rfl | rfl
  · simp [nilClause, Clause.pp, generalPP]
  · simp [consClause, Clause.pp, generalPP]
  · simp [joinClause, Clause.pp, generalPP]

/-- Complete List coverage dispatches before the final catch-all. -/
theorem listDispatchOK :
    DispatchOK listSignature listClauses listCap :=
  coverageOK_catchAllLast_dispatchOK
    listSignature listClauses listCap listCoverageOK listCatchAllLast

/-- The paper-complete multiset has the same final catch-all discipline. -/
theorem paperMultisetCatchAllLast :
    CatchAllLast paperMultisetClauses := by
  simpa [paperMultisetClauses, listClauses] using listCatchAllLast

/-- Paper-complete multiset coverage also yields pre-catch-all dispatch. -/
theorem paperMultisetDispatchOK :
    DispatchOK listSignature paperMultisetClauses listCap :=
  coverageOK_catchAllLast_dispatchOK listSignature paperMultisetClauses
    listCap paperMultisetCoverageOK paperMultisetCatchAllLast

/-! ## Target non-seeding regression -/

/-- A target-indexed view of one concrete clause checker. -/
def consEvidenceAtTarget (_target : Ty) : Option Shape.Evidence :=
  clauseEvidence listSignature consClause.pp [elementCap, listCap]

/-- Changing an external target cannot change actual clause evidence. -/
theorem consEvidence_target_invariant :
    consEvidenceAtTarget .int =
      consEvidenceAtTarget (.data "Unrelated" [.bool]) :=
  rfl

/-- The generic target-nonseeding theorem applies to the concrete cons clause. -/
theorem consEvidence_target_nonseeding :
    TargetNonseeding consEvidenceAtTarget := by
  intro _ _
  rfl

/-! ## Closed structured field-head validation -/

/-- `Matcher Any (List Int)` remains a valid capability/target pairing. -/
theorem matcher_none_closed_list_is_well_corresponded :
    CapTargetOK [] .any (.data "List" [.int]) :=
  .any

/-- Both the closed result former and the List field former are observable. -/
def closedBoxObservability : Shape.Observability :=
  fun former =>
    if former = "Box" then some []
    else if former = "List" then some [true]
    else none

/-- `box : List Int =>_P Box` has no result target variable to receive evidence. -/
def closedBoxProjection :
    Projection.ProjectionSignature closedBoxObservability where
  fieldTypes := [.data "List" [.int]]
  resultType := .data "Box" []
  resultRoot := .data (mask := []) (by
    simp [closedBoxObservability]) rfl

/-- Frozen signature fragment for the unary `box` pattern constructor. -/
def closedBoxSignature : FrozenMatcherSig where
  observability := closedBoxObservability
  patternConstructors := [("box", closedBoxProjection)]
  constructorsByFormer := [("Box", [("box", 1)])]

/-- `box $` rejects a next matcher with capability `Any`. -/
theorem closed_box_hole_rejects_none :
    clauseEvidence closedBoxSignature
        (.ctor "box" [.hole]) [.any] =
      none := by
  native_decide

/-- `box $` accepts a next matcher with the required List head. -/
theorem closed_box_hole_accepts_list :
    clauseEvidence closedBoxSignature
        (.ctor "box" [.hole]) [.con "List" [.any]] =
      some (.con "Box" []) := by
  native_decide

/-- A wildcard child is `unseen` and has no next-matcher obligation. -/
theorem closed_box_wildcard_is_allowed :
    clauseEvidence closedBoxSignature
        (.ctor "box" [.wild]) [] =
      some (.con "Box" []) := by
  native_decide

/-- A value-pattern-pattern child is likewise `unseen` and remains allowed. -/
theorem closed_box_value_pattern_is_allowed :
    clauseEvidence closedBoxSignature
        (.ctor "box" [.pval "value"]) [] =
      some (.con "Box" []) := by
  native_decide

/-! ## Core order of holes and primitive value patterns -/

/-- A value-pattern-pattern may precede a later hole in depth-first,
left-to-right order. -/
theorem value_before_hole_is_core_ordered :
    (PPat.ctor "cons" [.pval "head", .hole]).coreOrderCheck = true := by
  native_decide

/-- The core rejects the convenient surface-language form whose value
pattern-pattern occurs to the right of an earlier hole. -/
theorem hole_before_value_is_not_core_ordered :
    (PPat.ctor "cons" [.hole, .pval "head"]).coreOrderCheck = false := by
  native_decide

/-- The same restriction traverses tuple nesting, not merely constructor
children. -/
theorem nested_hole_before_value_is_not_core_ordered :
    (PPat.tuple [.wild, .tuple [.hole, .pval "key"]]).coreOrderCheck =
      false := by
  native_decide

/-- Clause evidence is the executable gate used by reconstruction, so an
out-of-order PP cannot acquire certified evidence even if its remaining
shape and hole capability would otherwise be accepted. -/
theorem clause_evidence_rejects_hole_before_value :
    clauseEvidence listSignature
      (.ctor "cons" [.hole, .pval "head"]) [.con "List" [.any]] = none := by
  native_decide

end ClauseEvidenceExamples
end TypePM
