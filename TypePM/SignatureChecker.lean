import TypePM.Preservation
import TypePM.Unification
import TypePM.SourceSubstitution

/-!
# Executable frozen-signature well-formedness checker

`FrozenSigWF` is the single global condition assumed by the dynamic safety
theorem.  This module makes the paper's reading of that condition precise: it
is established, not assumed, for every signature accepted by a finite
executable checker.

`frozenSigWFCheck` traverses only the frozen lookup tables.  Its soundness
theorem `frozenSigWFCheck_sound` discharges every semantic field of
`FrozenSigWF`:

* every scheme in every complete table is closed outside its own binders;
* generic instantiation uniqueness follows from a syntactic binder-coverage
  check via the substitution-agreement converse lemmas below;
* the canonical `nil`/`cons` declarations witness `ListSigWF`;
* primitive delta preservation is proved once per primitive operation
  (`append`, `splits`) against its canonical scheme;
* pattern constructors are restricted to the canonical single-parameter
  collection family (`nil`/`cons`/`join` over one observable former), for
  which capability projection is inverted explicitly.

The checker is conservative: a signature outside this family is rejected,
never accepted unsoundly.  The one remaining field, `armExhaustive`, is a
function-valued component fixed at signature construction time; the soundness
theorem consumes it as the definitional equation
`signature.armExhaustive = basicArmExhaustive`.
-/

namespace TypePM

/-! ## Canonical schemes -/

/-- The canonical polymorphic `nil` constructor scheme. -/
def nilCanonicalScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := []
  result := .data "List" [.var 0]

/-- The canonical polymorphic `cons` constructor scheme. -/
def consCanonicalScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [.var 0, .data "List" [.var 0]]
  result := .data "List" [.var 0]

/-- The canonical `nil` scheme produces every instantiated list type. -/
theorem nilCanonicalScheme_inst (target : Ty) :
    nilCanonicalScheme.Inst [] (Ty.listT target) := by
  refine ⟨CapSubst.id, Unification.TySubst.single 0 target,
    CapSubst.id_supportWithin [],
    Unification.TySubst.single_supportWithin 0 target, rfl, ?_⟩
  simp [nilCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
    Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
    Unification.TySubst.single]

/-- The canonical `cons` scheme consumes a head and a tail list. -/
theorem consCanonicalScheme_inst (target : Ty) :
    consCanonicalScheme.Inst [target, Ty.listT target] (Ty.listT target) := by
  refine ⟨CapSubst.id, Unification.TySubst.single 0 target,
    CapSubst.id_supportWithin [],
    Unification.TySubst.single_supportWithin 0 target, ?_, ?_⟩
  · simp [consCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
      Unification.TySubst.single]
  · simp [consCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
      Unification.TySubst.single]

/-! ## Substitution-agreement converse lemmas -/

mutual

/-- Equal capability application forces agreement on every free leaf. -/
theorem Cap.agree_of_apply_eq {left right : CapSubst} :
    ∀ capability : Cap,
      capability.apply left = capability.apply right →
      ∀ varId ∈ capability.fcv, left varId = right varId
  | .any, _, varId, membership => by
      simp [Cap.fcv] at membership
  | .var name, equal, varId, membership => by
      simp only [Cap.fcv, List.mem_singleton] at membership
      subst membership
      simpa [Cap.apply] using equal
  | .skolem _, _, varId, membership => by
      simp [Cap.fcv] at membership
  | .con name children, equal, varId, membership => by
      simp only [Cap.apply, Cap.con.injEq, true_and] at equal
      exact Cap.agreeList_of_apply_eq children equal varId
        (by simpa [Cap.fcv] using membership)
  | .prod components, equal, varId, membership => by
      simp only [Cap.apply, Cap.prod.injEq] at equal
      exact Cap.agreeList_of_apply_eq components equal varId
        (by simpa [Cap.fcv] using membership)

/-- List form of `Cap.agree_of_apply_eq`. -/
theorem Cap.agreeList_of_apply_eq {left right : CapSubst} :
    ∀ capabilities : List Cap,
      Cap.applyList left capabilities = Cap.applyList right capabilities →
      ∀ varId ∈ Cap.fcvList capabilities, left varId = right varId
  | [], _, varId, membership => by
      simp [Cap.fcvList] at membership
  | capability :: capabilities, equal, varId, membership => by
      simp only [Cap.applyList, List.cons.injEq] at equal
      rw [Cap.fcvList, List.mem_append] at membership
      rcases membership with headMem | tailMem
      · exact Cap.agree_of_apply_eq capability equal.1 varId headMem
      · exact Cap.agreeList_of_apply_eq capabilities equal.2 varId tailMem

end

mutual

/-- Equal paired application forces agreement on both free-variable sorts. -/
theorem Subst.agree_of_apply_eq {left right : Subst} :
    ∀ target : Ty,
      left.apply target = right.apply target →
      (∀ varId ∈ target.fcv, left.cap varId = right.cap varId) ∧
      (∀ varId ∈ target.ftv, left.target varId = right.target varId)
  | .var name, equal => by
      refine ⟨fun varId membership => by simp [Ty.fcv] at membership,
        fun varId membership => ?_⟩
      simp only [Ty.ftv, List.mem_singleton] at membership
      subst membership
      simpa [Subst.apply, Ty.applyCapability, Ty.applyTarget] using equal
  | .skolem _, _ => by
      exact ⟨fun varId membership => by simp [Ty.fcv] at membership,
        fun varId membership => by simp [Ty.ftv] at membership⟩
  | .unit, _ => by
      exact ⟨fun varId membership => by simp [Ty.fcv] at membership,
        fun varId membership => by simp [Ty.ftv] at membership⟩
  | .int, _ => by
      exact ⟨fun varId membership => by simp [Ty.fcv] at membership,
        fun varId membership => by simp [Ty.ftv] at membership⟩
  | .bool, _ => by
      exact ⟨fun varId membership => by simp [Ty.fcv] at membership,
        fun varId membership => by simp [Ty.ftv] at membership⟩
  | .data name arguments, equal => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.data.injEq, true_and] at equal
      have listAgree := Subst.agreeList_of_apply_eq arguments equal
      exact ⟨fun varId membership =>
          listAgree.1 varId (by simpa [Ty.fcv] using membership),
        fun varId membership =>
          listAgree.2 varId (by simpa [Ty.ftv] using membership)⟩
  | .prod components, equal => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.prod.injEq] at equal
      have listAgree := Subst.agreeList_of_apply_eq components equal
      exact ⟨fun varId membership =>
          listAgree.1 varId (by simpa [Ty.fcv] using membership),
        fun varId membership =>
          listAgree.2 varId (by simpa [Ty.ftv] using membership)⟩
  | .fn domain codomain, equal => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.fn.injEq] at equal
      have domainAgree := Subst.agree_of_apply_eq domain equal.1
      have codomainAgree := Subst.agree_of_apply_eq codomain equal.2
      refine ⟨fun varId membership => ?_, fun varId membership => ?_⟩
      · rw [Ty.fcv, List.mem_append] at membership
        exact membership.elim (domainAgree.1 varId) (codomainAgree.1 varId)
      · rw [Ty.ftv, List.mem_append] at membership
        exact membership.elim (domainAgree.2 varId) (codomainAgree.2 varId)
  | .matcher capability target, equal => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.matcher.injEq] at equal
      have targetAgree := Subst.agree_of_apply_eq target equal.2
      refine ⟨fun varId membership => ?_,
        fun varId membership => targetAgree.2 varId (by
          simpa [Ty.ftv] using membership)⟩
      rw [Ty.fcv, List.mem_append] at membership
      exact membership.elim
        (Cap.agree_of_apply_eq capability equal.1 varId)
        (targetAgree.1 varId)
  | .slot capability target, equal => by
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.slot.injEq] at equal
      have targetAgree := Subst.agree_of_apply_eq target equal.2
      refine ⟨fun varId membership => ?_,
        fun varId membership => targetAgree.2 varId (by
          simpa [Ty.ftv] using membership)⟩
      rw [Ty.fcv, List.mem_append] at membership
      exact membership.elim
        (Cap.agree_of_apply_eq capability equal.1 varId)
        (targetAgree.1 varId)

/-- List form of `Subst.agree_of_apply_eq`. -/
theorem Subst.agreeList_of_apply_eq {left right : Subst} :
    ∀ targets : List Ty,
      Ty.applyTargetList left.target
          (Ty.applyCapabilityList left.cap targets) =
        Ty.applyTargetList right.target
          (Ty.applyCapabilityList right.cap targets) →
      (∀ varId ∈ Ty.fcvList targets, left.cap varId = right.cap varId) ∧
      (∀ varId ∈ Ty.ftvList targets, left.target varId = right.target varId)
  | [], _ => by
      exact ⟨fun varId membership => by simp [Ty.fcvList] at membership,
        fun varId membership => by simp [Ty.ftvList] at membership⟩
  | target :: targets, equal => by
      simp only [Ty.applyCapabilityList, Ty.applyTargetList,
        List.cons.injEq] at equal
      have headAgree := Subst.agree_of_apply_eq target equal.1
      have tailAgree := Subst.agreeList_of_apply_eq targets equal.2
      refine ⟨fun varId membership => ?_, fun varId membership => ?_⟩
      · rw [Ty.fcvList, List.mem_append] at membership
        exact membership.elim (headAgree.1 varId) (tailAgree.1 varId)
      · rw [Ty.ftvList, List.mem_append] at membership
        exact membership.elim (headAgree.2 varId) (tailAgree.2 varId)

end

/-! ## Generic instantiation lemmas from syntactic conditions -/

/--
Instantiated field targets are unique once every quantified variable that is
free in the fields also reaches the instantiated result.  This is the
syntactic binder-coverage condition checked by `frozenSigWFCheck`.
-/
theorem CtorScheme.instArgsUnique_of_coverage
    {scheme : CtorScheme}
    (capCovered : ∀ varId ∈ Ty.fcvList scheme.args,
      varId ∈ scheme.capBinders → varId ∈ scheme.result.fcv)
    (tyCovered : ∀ varId ∈ Ty.ftvList scheme.args,
      varId ∈ scheme.tyBinders → varId ∈ scheme.result.ftv)
    {leftTargets rightTargets : List Ty} {result : Ty}
    (leftInst : scheme.Inst leftTargets result)
    (rightInst : scheme.Inst rightTargets result) :
    leftTargets = rightTargets := by
  obtain ⟨leftCap, leftTy, leftCapSupport, leftTySupport, leftArgs,
    leftResult⟩ := leftInst
  obtain ⟨rightCap, rightTy, rightCapSupport, rightTySupport, rightArgs,
    rightResult⟩ := rightInst
  have resultAgree :=
    Subst.agree_of_apply_eq (left := Subst.mk leftCap leftTy)
      (right := Subst.mk rightCap rightTy) scheme.result
      (leftResult.trans rightResult.symm)
  subst leftArgs
  subst rightArgs
  refine List.map_congr_left fun argument argMem => ?_
  refine Subst.apply_eq_of_free_agree _ _ argument
    (fun varId varMem => ?_) (fun varId varMem => ?_)
  · by_cases binder : varId ∈ scheme.capBinders
    · exact resultAgree.1 varId
        (capCovered varId (Ty.mem_fcvList_of_mem argMem varMem) binder)
    · exact (leftCapSupport varId binder).trans
        (rightCapSupport varId binder).symm
  · by_cases binder : varId ∈ scheme.tyBinders
    · exact resultAgree.2 varId
        (tyCovered varId (Ty.mem_ftvList_of_mem argMem varMem) binder)
    · exact (leftTySupport varId binder).trans
        (rightTySupport varId binder).symm

/-- A scheme whose result is a data former only produces data roots. -/
theorem CtorScheme.instDataRoot
    {scheme : CtorScheme} {former : String} {resultArgs : List Ty}
    (resultShape : scheme.result = .data former resultArgs)
    {targets : List Ty} {result : Ty}
    (instanceTyping : scheme.Inst targets result) :
    ∃ arguments, result = .data former arguments := by
  obtain ⟨capSubst, tySubst, _, _, _, resultEq⟩ := instanceTyping
  refine ⟨Ty.applyTargetList tySubst
    (Ty.applyCapabilityList capSubst resultArgs), ?_⟩
  rw [← resultEq, resultShape]
  simp [Subst.apply, Ty.applyCapability, Ty.applyTarget]

/-! ## Complete evidence -/

namespace Shape

/-- Embedded capabilities are never `unseen`. -/
theorem ofCap_ne_unseen (capability : Cap) :
    ofCap capability ≠ .unseen := by
  cases capability <;> simp [ofCap]

mutual

/-- The evidence embedding of capabilities is injective. -/
theorem ofCap_injective :
    ∀ {left right : Cap}, ofCap left = ofCap right → left = right
  | .any, right, equal => by
      cases right <;> simp_all [ofCap]
  | .var _, right, equal => by
      cases right <;> simp_all [ofCap]
  | .skolem _, right, equal => by
      cases right <;> simp_all [ofCap]
  | .con name children, right, equal => by
      cases right <;> simp_all [ofCap]
      exact ofCapList_injective equal.2
  | .prod components, right, equal => by
      cases right <;> simp_all [ofCap]
      exact ofCapList_injective equal

/-- List form of `ofCap_injective`. -/
theorem ofCapList_injective :
    ∀ {left right : List Cap},
      left.map ofCap = right.map ofCap → left = right
  | [], right, equal => by
      cases right <;> simp_all
  | left :: lefts, right, equal => by
      cases right <;> simp_all
      exact ⟨ofCap_injective equal.1, ofCapList_injective equal.2⟩

end

mutual

/-- Exact merge of two embedded capabilities forces them to coincide. -/
theorem merge_ofCap_eq :
    ∀ {left right : Cap} {merged : Evidence},
      merge (ofCap left) (ofCap right) = some merged →
      left = right ∧ merged = ofCap left
  | .any, right, merged, success => by
      cases right <;> simp_all [ofCap, merge]
  | .var _, right, merged, success => by
      cases right <;> simp_all [ofCap, merge]
  | .skolem _, right, merged, success => by
      cases right <;> simp_all [ofCap, merge]
  | .con name children, right, merged, success => by
      cases right with
      | con rightName rightChildren =>
          simp only [ofCap, merge] at success
          by_cases nameEq : name = rightName
          · subst nameEq
            rw [if_pos rfl] at success
            cases listSuccess :
                mergeList (children.map ofCap)
                  (rightChildren.map ofCap) with
            | none => rw [listSuccess] at success; cases success
            | some mergedChildren =>
                rw [listSuccess] at success
                obtain ⟨childrenEq, mergedEq⟩ :=
                  mergeList_ofCap_eq listSuccess
                cases success
                exact ⟨by rw [childrenEq], by
                  simp [ofCap, mergedEq]⟩
          · simp [if_neg nameEq] at success
      | any => simp [ofCap] at success
      | var _ => simp [ofCap] at success
      | skolem _ => simp [ofCap] at success
      | prod _ => simp [ofCap] at success
  | .prod components, right, merged, success => by
      cases right with
      | prod rightComponents =>
          simp only [ofCap, merge] at success
          cases listSuccess :
              mergeList (components.map ofCap)
                (rightComponents.map ofCap) with
          | none => rw [listSuccess] at success; cases success
          | some mergedComponents =>
              rw [listSuccess] at success
              obtain ⟨componentsEq, mergedEq⟩ :=
                mergeList_ofCap_eq listSuccess
              cases success
              exact ⟨by rw [componentsEq], by simp [ofCap, mergedEq]⟩
      | any => simp [ofCap] at success
      | var _ => simp [ofCap] at success
      | skolem _ => simp [ofCap] at success
      | con _ _ => simp [ofCap] at success

/-- List form of `merge_ofCap_eq`. -/
theorem mergeList_ofCap_eq :
    ∀ {left right : List Cap} {merged : List Evidence},
      mergeList (left.map ofCap) (right.map ofCap) = some merged →
      left = right ∧ merged = left.map ofCap
  | [], right, merged, success => by
      cases right <;> simp_all [mergeList]
  | left :: lefts, right, merged, success => by
      cases right with
      | nil => simp [mergeList] at success
      | cons rightHead rightTail =>
          simp only [List.map_cons, mergeList] at success
          cases headSuccess :
              merge (ofCap left) (ofCap rightHead) with
          | none => rw [headSuccess] at success; cases success
          | some mergedHead =>
              cases tailSuccess :
                  mergeList (lefts.map ofCap) (rightTail.map ofCap) with
              | none => rw [headSuccess, tailSuccess] at success; cases success
              | some mergedTail =>
                  rw [headSuccess, tailSuccess] at success
                  obtain ⟨headEq, mergedHeadEq⟩ := merge_ofCap_eq headSuccess
                  obtain ⟨tailEq, mergedTailEq⟩ :=
                    mergeList_ofCap_eq tailSuccess
                  cases success
                  exact ⟨by rw [headEq, tailEq], by
                    simp [mergedHeadEq, mergedTailEq]⟩

end

/-- Merging an embedded capability into `unseen` retains it. -/
theorem merge_ofCap_unseen (capability : Cap) :
    merge (ofCap capability) .unseen = some (ofCap capability) := by
  cases capability <;> simp [ofCap]

/-- A successful fold of embedded capabilities identifies them all. -/
theorem mergeAll_ofCap :
    ∀ {caps : List Cap} {merged : Evidence},
      mergeAll (caps.map ofCap) = some merged →
      (caps = [] ∧ merged = .unseen) ∨
      (∃ witness, merged = ofCap witness ∧ ∀ c ∈ caps, c = witness)
  | [], merged, success => by
      simp only [List.map_nil, mergeAll, Option.some.injEq] at success
      exact .inl ⟨rfl, success.symm⟩
  | cap :: caps, merged, success => by
      simp only [List.map_cons, mergeAll] at success
      cases tailSuccess : mergeAll (caps.map ofCap) with
      | none => rw [tailSuccess] at success; cases success
      | some accumulated =>
          simp only [tailSuccess] at success
          rcases mergeAll_ofCap tailSuccess with
            ⟨capsEmpty, accUnseen⟩ | ⟨witness, accEq, allEq⟩
          · subst capsEmpty
            rw [accUnseen, merge_ofCap_unseen] at success
            cases success
            exact .inr ⟨cap, rfl, by simp⟩
          · rw [accEq] at success
            obtain ⟨capEq, mergedEq⟩ := merge_ofCap_eq success
            refine .inr ⟨witness, by rw [mergedEq, capEq], ?_⟩
            intro candidate membership
            rcases List.mem_cons.mp membership with rfl | tailMem
            · exact capEq
            · exact allEq candidate tailMem

end Shape

/-! ## Canonical collection-family projection -/

/--
The unique child capability demanded at one field of a canonical
collection-family pattern constructor, given the element capability of the
surrounding matcher.
-/
def familyChild (former : String) (t : TypePM.TyVar) (elem : Cap)
    (arg : Ty) : Cap :=
  if arg = .var t then elem else .con former [elem]

namespace Projection

/-- Successful pairing recovers the zip and forces equal lengths. -/
theorem pairFields_eq_some :
    ∀ {fieldTypes : List Ty} {childEvidence : List Shape.Evidence}
      {pairs : List FieldEvidence},
      pairFields fieldTypes childEvidence = some pairs →
      fieldTypes.length = childEvidence.length ∧
        pairs = fieldTypes.zip childEvidence
  | [], [], pairs, success => by
      simp only [pairFields, Option.some.injEq] at success
      exact ⟨rfl, success.symm⟩
  | [], _ :: _, pairs, success => by
      simp [pairFields] at success
  | _ :: _, [], pairs, success => by
      simp [pairFields] at success
  | fieldType :: fieldTypes, evidence :: childEvidence, pairs, success => by
      simp only [pairFields] at success
      cases tailSuccess : pairFields fieldTypes childEvidence with
      | none => rw [tailSuccess] at success; cases success
      | some tailPairs =>
          rw [tailSuccess] at success
          obtain ⟨lengthEq, zipEq⟩ := pairFields_eq_some tailSuccess
          cases success
          exact ⟨by simp [lengthEq], by simp [zipEq]⟩

/-- A relevant-variable query on a variable field is a membership test. -/
theorem relevantVars_var
    {observable : Shape.Observability} {candidates : List TypePM.TyVar}
    {t : TypePM.TyVar} (tMem : t ∈ candidates) :
    relevantVars observable candidates (.var t) = some [t] := by
  simp [relevantVars, tMem]

/-- The family result type reaches exactly its element variable. -/
theorem relevantVars_family
    {observable : Shape.Observability} {candidates : List TypePM.TyVar}
    {former : String} {t : TypePM.TyVar}
    (maskOK : observable former = some [true]) (tMem : t ∈ candidates) :
    relevantVars observable candidates (.data former [.var t]) =
      some [t] := by
  simp [relevantVars, relevantVarsMasked, maskOK, tMem]

/-- Non-`unseen` evidence at a relevant variable field is one assignment. -/
theorem collectAssignments_var
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar} {t : TypePM.TyVar}
    (tMem : t ∈ resultVariables) {evidence : Shape.Evidence}
    (notUnseen : evidence ≠ .unseen) :
    collectAssignments observable resultVariables (.var t) evidence =
      some [(t, evidence)] := by
  cases evidence with
  | unseen => exact absurd rfl notUnseen
  | known leaf =>
      simp [collectAssignments, relevantVars, tMem]
  | con name children =>
      simp [collectAssignments, relevantVars, tMem]
  | prod components =>
      simp [collectAssignments, relevantVars, tMem]

/-- A `known` leaf cannot satisfy a relevant family data field. -/
theorem collectAssignments_data_known
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar} {t : TypePM.TyVar}
    (tMem : t ∈ resultVariables) {former : String}
    (maskOK : observable former = some [true]) (leaf : Shape.Leaf) :
    collectAssignments observable resultVariables
      (.data former [.var t]) (.known leaf) = none := by
  have reduce :
      collectAssignments observable resultVariables
        (.data former [.var t]) (.known leaf) =
      (match relevantVars observable resultVariables
          (.data former [.var t]) with
        | none => none
        | some [] => some []
        | some (_ :: _) => none) := rfl
  rw [reduce, relevantVars_family maskOK tMem]

/-- Product evidence cannot satisfy a relevant family data field. -/
theorem collectAssignments_data_prod
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar} {t : TypePM.TyVar}
    (tMem : t ∈ resultVariables) {former : String}
    (maskOK : observable former = some [true])
    (components : List Shape.Evidence) :
    collectAssignments observable resultVariables
      (.data former [.var t]) (.prod components) = none := by
  have reduce :
      collectAssignments observable resultVariables
        (.data former [.var t]) (.prod components) =
      (match relevantVars observable resultVariables
          (.data former [.var t]) with
        | none => none
        | some [] => some []
        | some (_ :: _) => none) := rfl
  rw [reduce, relevantVars_family maskOK tMem]

/-- Constructor evidence at a family data field reduces to its one child. -/
theorem collectAssignments_data_con
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar} {t : TypePM.TyVar}
    (tMem : t ∈ resultVariables) {former : String}
    (maskOK : observable former = some [true])
    (evidenceName : String) (children : List Shape.Evidence) :
    collectAssignments observable resultVariables
      (.data former [.var t]) (.con evidenceName children) =
      (if former = evidenceName then
        collectAssignmentsMasked observable resultVariables
          [true] [.var t] children
      else none) := by
  have reduce :
      collectAssignments observable resultVariables
        (.data former [.var t]) (.con evidenceName children) =
      (match relevantVars observable resultVariables
          (.data former [.var t]) with
        | none => none
        | some [] => some []
        | some (_ :: _) =>
            if former = evidenceName then
              match observable former with
              | some mask =>
                  collectAssignmentsMasked observable resultVariables
                    mask [.var t] children
              | none => none
            else none) := rfl
  rw [reduce, relevantVars_family maskOK tMem]
  by_cases nameEq : former = evidenceName
  · rw [if_pos nameEq, if_pos nameEq, maskOK]
  · rw [if_neg nameEq, if_neg nameEq]

/-- An embedded child at a family data field is a one-element constructor. -/
theorem collectAssignments_family_data
    {observable : Shape.Observability}
    {resultVariables : List TypePM.TyVar} {t : TypePM.TyVar}
    (tMem : t ∈ resultVariables) {former : String}
    (maskOK : observable former = some [true]) {child : Cap}
    {chunk : Assignments}
    (success : collectAssignments observable resultVariables
      (.data former [.var t]) (Shape.ofCap child) = some chunk) :
    ∃ inner, child = .con former [inner] ∧
      chunk = [(t, Shape.ofCap inner)] := by
  cases child with
  | any =>
      rw [show Shape.ofCap Cap.any = Shape.Evidence.known .any by
          simp [Shape.ofCap],
        collectAssignments_data_known tMem maskOK] at success
      cases success
  | var varId =>
      rw [show Shape.ofCap (Cap.var varId) =
          Shape.Evidence.known (.var varId) by simp [Shape.ofCap],
        collectAssignments_data_known tMem maskOK] at success
      cases success
  | skolem name =>
      rw [show Shape.ofCap (Cap.skolem name) =
          Shape.Evidence.known (.skolem name) by simp [Shape.ofCap],
        collectAssignments_data_known tMem maskOK] at success
      cases success
  | prod components =>
      rw [show Shape.ofCap (Cap.prod components) =
          Shape.Evidence.prod (components.map Shape.ofCap) by
          simp [Shape.ofCap],
        collectAssignments_data_prod tMem maskOK] at success
      cases success
  | con name grandchildren =>
      rw [show Shape.ofCap (Cap.con name grandchildren) =
          Shape.Evidence.con name (grandchildren.map Shape.ofCap) by
          simp [Shape.ofCap],
        collectAssignments_data_con tMem maskOK] at success
      by_cases nameEq : former = name
      · subst nameEq
        rw [if_pos rfl] at success
        cases grandchildren with
        | nil => simp [collectAssignmentsMasked] at success
        | cons inner rest =>
            cases rest with
            | nil =>
                simp only [List.map_cons, List.map_nil,
                  collectAssignmentsMasked, if_true,
                  collectAssignments_var tMem
                    (Shape.ofCap_ne_unseen inner)] at success
                simp only [mergeAssignments, Option.some.injEq] at success
                exact ⟨inner, rfl, success.symm⟩
            | cons _ _ =>
                simp [collectAssignmentsMasked,
                  collectAssignments_var tMem
                    (Shape.ofCap_ne_unseen inner)] at success
      · rw [if_neg nameEq] at success
        cases success

/--
Per-field correspondence of a canonical collection-family constructor: each
argument type receives an embedded child capability and contributes exactly
one piece of element evidence.
-/
inductive FamilyFields (former : String) (t : TypePM.TyVar) :
    List Ty → List Cap → List Cap → Prop where
  | nil : FamilyFields former t [] [] []
  | var {args children contributions} (child : Cap) :
      FamilyFields former t args children contributions →
      FamilyFields former t (.var t :: args) (child :: children)
        (child :: contributions)
  | data {args children contributions} (inner : Cap) :
      FamilyFields former t args children contributions →
      FamilyFields former t (.data former [.var t] :: args)
        (.con former [inner] :: children) (inner :: contributions)

/-- Family field validation yields exactly one contribution per field. -/
theorem collectFieldAssignments_family
    {observable : Shape.Observability} {t : TypePM.TyVar} {former : String}
    (maskOK : observable former = some [true]) :
    ∀ {args : List Ty} {children : List Cap} {chunks : List Assignments},
      (∀ arg ∈ args, arg = .var t ∨ arg = .data former [.var t]) →
      args.length = children.length →
      collectFieldAssignments observable [t]
        (args.zip (children.map Shape.ofCap)) = some chunks →
      ∃ contributions : List Cap,
        chunks = contributions.map (fun c => [(t, Shape.ofCap c)]) ∧
        FamilyFields former t args children contributions
  | [], [], chunks, _, _, success => by
      simp only [List.map_nil, List.zip_nil_right, collectFieldAssignments,
        Option.some.injEq] at success
      exact ⟨[], by simp [success.symm], .nil⟩
  | [], _ :: _, chunks, _, lengths, _ => by
      simp at lengths
  | _ :: _, [], chunks, _, lengths, _ => by
      simp at lengths
  | arg :: args, child :: children, chunks, argsOK, lengths, success => by
      simp only [List.map_cons, List.zip_cons_cons,
        collectFieldAssignments] at success
      cases headSuccess :
          collectAssignments observable [t] arg (Shape.ofCap child) with
      | none => rw [headSuccess] at success; cases success
      | some headChunk =>
          cases tailSuccess :
              collectFieldAssignments observable [t]
                (args.zip (children.map Shape.ofCap)) with
          | none => rw [headSuccess, tailSuccess] at success; cases success
          | some tailChunks =>
              rw [headSuccess, tailSuccess] at success
              cases success
              have tailLengths : args.length = children.length := by
                simpa using lengths
              obtain ⟨contributions, chunksEq, related⟩ :=
                collectFieldAssignments_family maskOK
                  (fun candidate mem => argsOK candidate (by simp [mem]))
                  tailLengths tailSuccess
              rcases argsOK arg (by simp) with argVar | argData
              · subst argVar
                rw [collectAssignments_var (by simp)
                  (Shape.ofCap_ne_unseen child)] at headSuccess
                cases headSuccess
                exact ⟨child :: contributions, by simp [chunksEq],
                  .var child related⟩
              · subst argData
                obtain ⟨inner, childEq, chunkEq⟩ :=
                  collectAssignments_family_data (by simp) maskOK headSuccess
                subst childEq chunkEq
                exact ⟨inner :: contributions, by simp [chunksEq],
                  .data inner related⟩

/-- Contributions of singleton family chunks are their stored evidence. -/
theorem evidenceContributions_family
    (t : TypePM.TyVar) (contributions : List Cap) :
    evidenceContributions t
      (contributions.map fun c => [(t, Shape.ofCap c)]) =
      contributions.map Shape.ofCap := by
  induction contributions with
  | nil => rfl
  | cons contribution contributions induction =>
      have lookupEq :
          lookupAssignment t [(t, Shape.ofCap contribution)] =
            some (Shape.ofCap contribution) := by
        simp [lookupAssignment]
      simp only [List.map_cons, evidenceContributions,
        List.filterMap_cons, lookupEq]
      exact congrArg _ induction

/-- Aggregation over one result variable reduces to one exact-merge fold. -/
theorem canonicalAssignments_single
    (t : TypePM.TyVar) (chunks : List Assignments) :
    canonicalAssignments [t] chunks =
      match Shape.mergeAll (evidenceContributions t chunks) with
      | none => none
      | some .unseen => some []
      | some evidence => some [(t, evidence)] := by
  cases mergeResult : Shape.mergeAll (evidenceContributions t chunks) with
  | none => simp [canonicalAssignments, mergeResult]
  | some evidence =>
      cases evidence <;> simp [canonicalAssignments, mergeResult]

/-- The family result root with no collected evidence. -/
theorem buildResultRoot_family_empty
    {observable : Shape.Observability} {former : String}
    {t : TypePM.TyVar} (maskOK : observable former = some [true]) :
    buildResultRoot observable [t] [] (.data former [.var t]) =
      some (.con former [.unseen]) := by
  simp [buildResultRoot, maskOK, buildResultSlotsMasked, buildResultSlot,
    relevantVars, hasAssignment, lookupAssignment]

/-- The family result root after its element variable received evidence. -/
theorem buildResultRoot_family_single
    {observable : Shape.Observability} {former : String}
    {t : TypePM.TyVar} (maskOK : observable former = some [true])
    (evidence : Shape.Evidence) :
    buildResultRoot observable [t] [(t, evidence)]
      (.data former [.var t]) = some (.con former [evidence]) := by
  simp [buildResultRoot, maskOK, buildResultSlotsMasked, buildResultSlot,
    relevantVars, hasAssignment, lookupAssignment, buildResultTemplate]

end Projection

namespace Shape

/-- Absorbing the projected family root determines the outer capability. -/
theorem merge_family_root
    {former : String} {slot : Evidence} {outer : Cap}
    (success : merge (.con former [slot]) (ofCap outer) =
      some (ofCap outer)) :
    ∃ elem, outer = .con former [elem] ∧
      merge slot (ofCap elem) = some (ofCap elem) := by
  cases outer with
  | any =>
      rw [show ofCap Cap.any = Evidence.known .any by simp [ofCap],
        merge.eq_def] at success
      cases success
  | var varId =>
      rw [show ofCap (Cap.var varId) = Evidence.known (.var varId) by
          simp [ofCap],
        merge.eq_def] at success
      cases success
  | skolem name =>
      rw [show ofCap (Cap.skolem name) = Evidence.known (.skolem name) by
          simp [ofCap],
        merge.eq_def] at success
      cases success
  | prod components =>
      rw [show ofCap (Cap.prod components) =
          Evidence.prod (components.map ofCap) by simp [ofCap],
        merge.eq_def] at success
      cases success
  | con name caps =>
      rw [show ofCap (Cap.con name caps) =
          Evidence.con name (caps.map ofCap) by simp [ofCap],
        merge.eq_def] at success
      dsimp only [] at success
      by_cases nameEq : former = name
      · subst nameEq
        rw [if_pos rfl] at success
        cases caps with
        | nil => simp [mergeList] at success
        | cons elem rest =>
            cases rest with
            | nil =>
                refine ⟨elem, rfl, ?_⟩
                simp only [List.map_cons, List.map_nil, mergeList] at success
                cases elemSuccess : merge slot (ofCap elem) with
                | none => rw [elemSuccess] at success; cases success
                | some merged =>
                    rw [elemSuccess] at success
                    have mergedEq : merged = ofCap elem := by
                      simpa using success
                    subst mergedEq
                    rfl
            | cons _ _ =>
                simp only [List.map_cons, mergeList] at success
                cases elemSuccess : merge slot (ofCap elem) with
                | none => rw [elemSuccess] at success; cases success
                | some merged => rw [elemSuccess] at success; cases success
      · rw [if_neg nameEq] at success
        cases success

end Shape

/-- Identified contributions determine every family child from the element. -/
theorem FamilyFields.children_eq_map
    {former : String} {t : TypePM.TyVar} {elem : Cap}
    {args : List Ty} {children contributions : List Cap}
    (related : Projection.FamilyFields former t args children contributions)
    (allEq : ∀ contribution ∈ contributions, contribution = elem) :
    children = args.map (familyChild former t elem) := by
  induction related with
  | nil => rfl
  | var child related induction =>
      have childEq : child = elem := allEq child (by simp)
      subst childEq
      have tailEq :=
        induction fun candidate mem => allEq candidate (by simp [mem])
      simp [familyChild, tailEq]
  | data inner related induction =>
      have innerEq : inner = elem := allEq inner (by simp)
      subst innerEq
      have tailEq :=
        induction fun candidate mem => allEq candidate (by simp [mem])
      simp [familyChild, tailEq]

/-- Contribution lists of family fields track the children lists. -/
theorem FamilyFields.length_eq
    {former : String} {t : TypePM.TyVar}
    {args : List Ty} {children contributions : List Cap}
    (related : Projection.FamilyFields former t args children contributions) :
    args.length = children.length ∧
      contributions.length = children.length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | var child related induction => simpa using induction
  | data inner related induction => simpa using induction

/-! ## Family capability-compatibility inversion -/

/--
For a canonical collection-family constructor, capability compatibility
pins the outer capability to a one-parameter constructor head and each
child to the demand of its field.
-/
theorem PatternCtorScheme.capCompatible_family_inversion
    {observability : Shape.Observability}
    {entry : PatternCtorScheme observability}
    {former : String} {t : TypePM.TyVar}
    (resultShape : entry.scheme.result = .data former [.var t])
    (maskOK : observability former = some [true])
    (argsOK : ∀ arg ∈ entry.scheme.args,
      arg = .var t ∨ arg = .data former [.var t])
    {children : List Cap} {outer : Cap}
    (compatible : entry.CapCompatible children outer) :
    ∃ elem, outer = .con former [elem] ∧
      children = entry.scheme.args.map (familyChild former t elem) := by
  obtain ⟨projected, projSuccess, mergeSuccess⟩ := compatible
  rw [Projection.projectSignature_eq_some_iff] at projSuccess
  cases projSuccess with
  | run pairSuccess varsSuccess chunksSuccess assignSuccess rootSuccess =>
      rename_i fields resultVariables chunks assignments
      rw [entry.projectionFields] at pairSuccess
      rw [entry.projectionResult, resultShape] at varsSuccess rootSuccess
      have targetVarsEq :
          Projection.targetVars (Ty.data former [Ty.var t]) = [t] := by
        simp [Projection.targetVars, Projection.targetVarsList]
      rw [targetVarsEq,
        Projection.relevantVars_family maskOK (by simp)] at varsSuccess
      cases varsSuccess
      obtain ⟨lengthEq, pairsEq⟩ := Projection.pairFields_eq_some pairSuccess
      rw [List.length_map] at lengthEq
      subst pairsEq
      obtain ⟨contributions, chunksEq, related⟩ :=
        Projection.collectFieldAssignments_family maskOK argsOK lengthEq
          chunksSuccess
      subst chunksEq
      rw [Projection.canonicalAssignments_single,
        Projection.evidenceContributions_family] at assignSuccess
      cases mergeAllResult :
          Shape.mergeAll (contributions.map Shape.ofCap) with
      | none => rw [mergeAllResult] at assignSuccess; cases assignSuccess
      | some mergedEvidence =>
          rw [mergeAllResult] at assignSuccess
          have assignShape :
              (mergedEvidence = .unseen ∧ assignments = []) ∨
              (mergedEvidence ≠ .unseen ∧
                assignments = [(t, mergedEvidence)]) := by
            cases mergedEvidence with
            | unseen =>
                cases assignSuccess
                exact .inl ⟨rfl, rfl⟩
            | known leaf =>
                cases assignSuccess
                exact .inr ⟨by simp, rfl⟩
            | con name grandchildren =>
                cases assignSuccess
                exact .inr ⟨by simp, rfl⟩
            | prod components =>
                cases assignSuccess
                exact .inr ⟨by simp, rfl⟩
          rcases Shape.mergeAll_ofCap mergeAllResult with
            ⟨contribEmpty, mergedUnseen⟩ | ⟨witness, mergedEq, allEq⟩
          · subst contribEmpty
            rcases assignShape with
              ⟨_, assignEmpty⟩ | ⟨notUnseen, _⟩
            · subst assignEmpty
              rw [Projection.buildResultRoot_family_empty maskOK]
                at rootSuccess
              cases rootSuccess
              obtain ⟨elem, outerEq, _⟩ :=
                Shape.merge_family_root mergeSuccess
              obtain ⟨argsLength, contributionsLength⟩ :=
                FamilyFields.length_eq related
              have childrenEmpty : children = [] :=
                List.eq_nil_of_length_eq_zero (by
                  simpa using contributionsLength.symm)
              have argsEmpty : entry.scheme.args = [] :=
                List.eq_nil_of_length_eq_zero (by
                  simp [argsLength, childrenEmpty])
              exact ⟨elem, outerEq, by simp [childrenEmpty, argsEmpty]⟩
            · exact absurd mergedUnseen notUnseen
          · rcases assignShape with
              ⟨mergedUnseen, _⟩ | ⟨_, assignSingle⟩
            · rw [mergedEq] at mergedUnseen
              exact absurd mergedUnseen (Shape.ofCap_ne_unseen witness)
            · subst assignSingle
              rw [mergedEq] at rootSuccess
              rw [Projection.buildResultRoot_family_single maskOK]
                at rootSuccess
              cases rootSuccess
              obtain ⟨elem, outerEq, slotMerge⟩ :=
                Shape.merge_family_root mergeSuccess
              obtain ⟨witnessEq, _⟩ := Shape.merge_ofCap_eq slotMerge
              refine ⟨elem, outerEq, ?_⟩
              exact FamilyFields.children_eq_map related
                fun candidate mem => (allEq candidate mem).trans witnessEq

/-! ## Primitive delta preservation for the canonical schemes -/

/-- `Ty.listT` is injective. -/
theorem Ty.listT_injective {left right : Ty}
    (equal : Ty.listT left = Ty.listT right) : left = right := by
  simpa [Ty.listT] using equal

/-- Inversion of instantiating the canonical `nil` scheme. -/
theorem nilCanonicalScheme_inst_inversion
    {targets : List Ty} {result : Ty}
    (instanceTyping : nilCanonicalScheme.Inst targets result) :
    ∃ target, targets = [] ∧ result = Ty.listT target := by
  rcases instanceTyping with
    ⟨capSubst, tySubst, capSupport, tySupport, argsEq, resultEq⟩
  refine ⟨tySubst 0, ?_, ?_⟩
  · simpa [nilCanonicalScheme] using argsEq.symm
  · simpa [nilCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEq.symm

/-- Inversion of instantiating the canonical `cons` scheme. -/
theorem consCanonicalScheme_inst_inversion
    {targets : List Ty} {result : Ty}
    (instanceTyping : consCanonicalScheme.Inst targets result) :
    ∃ target,
      targets = [target, Ty.listT target] ∧ result = Ty.listT target := by
  rcases instanceTyping with
    ⟨capSubst, tySubst, capSupport, tySupport, argsEq, resultEq⟩
  refine ⟨tySubst 0, ?_, ?_⟩
  · simpa [consCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      argsEq.symm
  · simpa [consCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEq.symm

/-- Inversion of instantiating the canonical `append` scheme. -/
theorem appendCanonicalScheme_inst_inversion
    {targets : List Ty} {result : Ty}
    (instanceTyping : appendCanonicalScheme.Inst targets result) :
    ∃ target,
      targets = [Ty.listT target, Ty.listT target] ∧
        result = Ty.listT target := by
  rcases instanceTyping with
    ⟨capSubst, tySubst, capSupport, tySupport, argsEq, resultEq⟩
  refine ⟨tySubst 0, ?_, ?_⟩
  · simpa [appendCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      argsEq.symm
  · simpa [appendCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEq.symm

/-- Inversion of instantiating the canonical `splits` scheme. -/
theorem splitsCanonicalScheme_inst_inversion
    {targets : List Ty} {result : Ty}
    (instanceTyping : splitsCanonicalScheme.Inst targets result) :
    ∃ target,
      targets = [Ty.listT target] ∧
        result =
          Ty.listT (.prod [Ty.listT target, Ty.listT target]) := by
  rcases instanceTyping with
    ⟨capSubst, tySubst, capSupport, tySupport, argsEq, resultEq⟩
  refine ⟨tySubst 0, ?_, ?_⟩
  · simpa [splitsCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      argsEq.symm
  · simpa [splitsCanonicalScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEq.symm

/-- Decoded elements of a canonically typed list value keep the element type. -/
theorem listOfV_valueTy {signature : FrozenSig}
    (consFound : signature.findDataCtor "cons" = some consCanonicalScheme) :
    ∀ {value : Value} {elements : List Value} {target : Ty},
      ValueTy signature value (Ty.listT target) →
      listOfV value = some elements →
      ∀ element ∈ elements, ValueTy signature element target := by
  intro value
  induction value using listOfV.induct with
  | case1 =>
      intro elements target typing decode element membership
      simp only [listOfV, Option.some.injEq] at decode
      subst decode
      simp at membership
  | case2 head tail induction =>
      intro elements target typing decode element membership
      simp only [listOfV] at decode
      cases tailDecode : listOfV tail with
      | none => rw [tailDecode] at decode; cases decode
      | some tailElements =>
          rw [tailDecode] at decode
          simp only [Option.map_some, Option.some.injEq] at decode
          subst decode
          cases typing with
          | ctor consLookup consInst valuesTyped =>
              rw [consFound] at consLookup
              cases consLookup
              obtain ⟨elementTarget, targetsEq, resultEq⟩ :=
                consCanonicalScheme_inst_inversion consInst
              have elementEq : elementTarget = target :=
                Ty.listT_injective resultEq.symm
              subst elementEq
              subst targetsEq
              cases valuesTyped with
              | cons headTyped restTyped =>
                  cases restTyped with
                  | cons tailTyped nilTyped =>
                      rcases List.mem_cons.mp membership with rfl | tailMem
                      · exact headTyped
                      · exact induction tailTyped tailDecode element tailMem
  | case3 value nilNe consNe =>
      intro elements target typing decode element membership
      rw [listOfV] at decode
      · cases decode
      · exact nilNe
      · exact consNe

/-- Encoded lists of canonically typed elements have the list type. -/
theorem mkListV_valueTy {signature : FrozenSig}
    (nilFound : signature.findDataCtor "nil" = some nilCanonicalScheme)
    (consFound : signature.findDataCtor "cons" = some consCanonicalScheme)
    {target : Ty} :
    ∀ {elements : List Value},
      (∀ element ∈ elements, ValueTy signature element target) →
      ValueTy signature (mkListV elements) (Ty.listT target)
  | [], _ =>
      ValueTy.ctor nilFound (nilCanonicalScheme_inst target) .nil
  | element :: elements, typed =>
      ValueTy.ctor consFound (consCanonicalScheme_inst target)
        (.cons (typed element (by simp))
          (.cons (mkListV_valueTy nilFound consFound
            fun candidate mem => typed candidate (by simp [mem])) .nil))

/-- Canonical primitive declarations preserve their declared result types. -/
theorem primEvalTyped_of_canonical {signature : FrozenSig}
    (nilFound : signature.findDataCtor "nil" = some nilCanonicalScheme)
    (consFound : signature.findDataCtor "cons" = some consCanonicalScheme)
    {op : PrimOp} {scheme : CtorScheme}
    {values : List Value} {targets : List Ty} {result : Ty} {value : Value}
    (found : signature.findPrimitive op = some scheme)
    (schemeCanonical : scheme = primCanonicalScheme op)
    (instanceTyping : scheme.Inst targets result)
    (valuesTyped : ValueTys signature values targets)
    (evaluated : primEval op values = some value) :
    ValueTy signature value result := by
  subst schemeCanonical
  cases op with
  | append =>
      obtain ⟨target, targetsEq, resultEq⟩ :=
        appendCanonicalScheme_inst_inversion instanceTyping
      subst targetsEq resultEq
      cases valuesTyped with
      | @cons leftValue _ restValues _ leftTyped restTyped =>
          cases restTyped with
          | @cons rightValue _ nilValues _ rightTyped nilTyped =>
              cases nilTyped
              have evaluatedBind :
                  ((listOfV leftValue).bind fun leftElements =>
                    (listOfV rightValue).bind fun rightElements =>
                      some (mkListV (leftElements ++ rightElements))) =
                    some value := evaluated
              cases leftDecode : listOfV leftValue with
              | none => rw [leftDecode] at evaluatedBind; cases evaluatedBind
              | some leftElements =>
                  cases rightDecode : listOfV rightValue with
                  | none =>
                      rw [leftDecode, rightDecode] at evaluatedBind
                      cases evaluatedBind
                  | some rightElements =>
                      rw [leftDecode, rightDecode] at evaluatedBind
                      have valueEq :
                          mkListV (leftElements ++ rightElements) = value := by
                        simpa using evaluatedBind
                      subst valueEq
                      refine mkListV_valueTy nilFound consFound ?_
                      intro element membership
                      rcases List.mem_append.mp membership with
                        leftMem | rightMem
                      · exact listOfV_valueTy consFound leftTyped
                          leftDecode element leftMem
                      · exact listOfV_valueTy consFound rightTyped
                          rightDecode element rightMem
  | splits =>
      obtain ⟨target, targetsEq, resultEq⟩ :=
        splitsCanonicalScheme_inst_inversion instanceTyping
      subst targetsEq resultEq
      cases valuesTyped with
      | @cons argValue _ nilValues _ argTyped nilTyped =>
          cases nilTyped
          have evaluatedBind :
              ((listOfV argValue).bind fun elements =>
                some (mkListV ((List.range (elements.length + 1)).map
                  fun index =>
                    .tuple [mkListV (elements.take index),
                      mkListV (elements.drop index)]))) =
                some value := evaluated
          cases argDecode : listOfV argValue with
          | none => rw [argDecode] at evaluatedBind; cases evaluatedBind
          | some elements =>
              rw [argDecode] at evaluatedBind
              have valueEq :
                  mkListV ((List.range (elements.length + 1)).map
                    fun index =>
                      Value.tuple [mkListV (elements.take index),
                        mkListV (elements.drop index)]) = value := by
                simpa using evaluatedBind
              subst valueEq
              refine mkListV_valueTy nilFound consFound ?_
              intro splitValue splitMem
              obtain ⟨index, _, splitEq⟩ := List.mem_map.mp splitMem
              subst splitEq
              refine ValueTy.tuple ?_
              refine .cons (mkListV_valueTy nilFound consFound ?_)
                (.cons (mkListV_valueTy nilFound consFound ?_) .nil)
              · intro element membership
                exact listOfV_valueTy consFound argTyped argDecode element
                  (List.mem_of_mem_take membership)
              · intro element membership
                exact listOfV_valueTy consFound argTyped argDecode element
                  (List.mem_of_mem_drop membership)

/-! ## The executable checker -/

/-- Data-root shape and binder coverage for one data-constructor scheme. -/
def dataCtorCheck (scheme : CtorScheme) : Bool :=
  (match scheme.result with
    | .data _ _ => true
    | _ => false) &&
  (Ty.fcvList scheme.args).all (fun varId =>
    !decide (varId ∈ scheme.capBinders) ||
      decide (varId ∈ scheme.result.fcv)) &&
  (Ty.ftvList scheme.args).all (fun varId =>
    !decide (varId ∈ scheme.tyBinders) ||
      decide (varId ∈ scheme.result.ftv))

/-- Collection-family shape check for one pattern-constructor entry. -/
def patternCtorCheck (signature : FrozenSig) (name : String)
    (entry : PatternCtorScheme signature.observability) : Bool :=
  match entry.scheme.result with
  | .data former [.var t] =>
      decide (signature.observability former = some [true]) &&
      entry.scheme.args.all (fun arg =>
        decide (arg = .var t) || decide (arg = .data former [.var t])) &&
      (match signature.toMatcherSig.constructorsFor? former with
        | some constructors =>
            decide ((name, entry.scheme.args.length) ∈ constructors)
        | none => false)
  | _ => false

/-- Exclusivity of the canonical list constructors: a data-constructor entry
whose scheme has a `List` result root must be the canonical `nil` or `cons`
declaration.  Any other entry passes vacuously. -/
def listCtorCheck (entry : String × CtorScheme) : Bool :=
  match entry.2.result with
  | .data "List" _ =>
      decide (entry.1 = "nil" ∧ entry.2 = nilCanonicalScheme) ||
        decide (entry.1 = "cons" ∧ entry.2 = consCanonicalScheme)
  | _ => true

/-- Executable closedness check for every entry in the complete frozen
tables.  Inspecting entries directly is intentional: lookup alone would miss
a malformed scheme shadowed by an earlier key. -/
def schemesClosedCheck (signature : FrozenSig) : Bool :=
  signature.dataCtors.all (fun entry => decide entry.2.Closed) &&
  signature.patternCtors.all (fun entry => decide entry.2.scheme.Closed) &&
  signature.patternFuns.all (fun entry => decide entry.2.Closed) &&
  signature.primitives.all (fun entry => decide entry.2.Closed)

/-- The executable table check establishes common signature closedness. -/
theorem schemesClosedCheck_sound {signature : FrozenSig}
    (checked : schemesClosedCheck signature = true) :
    signature.SchemesClosed := by
  simp only [schemesClosedCheck, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at checked
  obtain ⟨⟨⟨dataClosed, patternClosed⟩, funClosed⟩, primClosed⟩ := checked
  exact FrozenSig.SchemesClosed.of_entries dataClosed patternClosed
    funClosed primClosed

/--
Executable frozen-signature well-formedness checker.

The checker is conservative: closed schemes, canonical `nil`/`cons`
declarations, syntactic data roots with binder coverage, collection-family
pattern constructors, canonical primitive schemes, and an unshadowed
pattern-function namespace.
A signature outside this fragment is rejected, never accepted unsoundly.
-/
def frozenSigWFCheck (signature : FrozenSig) : Bool :=
  schemesClosedCheck signature &&
  decide (signature.findDataCtor "nil" = some nilCanonicalScheme) &&
  decide (signature.findDataCtor "cons" = some consCanonicalScheme) &&
  decide ((signature.patternFuns.map Prod.fst).Nodup) &&
  signature.dataCtors.all (fun entry => dataCtorCheck entry.2) &&
  signature.patternCtors.all (fun entry =>
    patternCtorCheck signature entry.1 entry.2) &&
  signature.primitives.all (fun entry =>
    decide (entry.2 = primCanonicalScheme entry.1)) &&
  signature.dataCtors.all listCtorCheck

/-! ## Closedness boundary regression -/

namespace SignatureCheckerRegression

/-- An otherwise admissible pattern-function scheme whose result leaks one
ambient target metavariable. -/
def openPatternFunScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := ⟨.any, .var 17⟩

/-- The public checker rejects open schemes even when all older dynamic
shape checks would accept the surrounding signature. -/
def openPatternFunSignature : FrozenSig where
  observability := fun _ => none
  dataCtors :=
    [("nil", nilCanonicalScheme), ("cons", consCanonicalScheme)]
  patternCtors := []
  patternFuns := [("open", openPatternFunScheme)]
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

theorem openPatternFunSignature_checker_rejects :
    frozenSigWFCheck openPatternFunSignature = false := by
  decide

/-- A closed entry shadows an open entry with the same lookup key.  The
closedness checker still inspects the complete table rather than only the
entry returned by lookup. -/
def shadowedOpenPatternFunSignature : FrozenSig :=
  { openPatternFunSignature with
    patternFuns :=
      [("shadowed",
          { capBinders := []
            tyBinders := [17]
            args := []
            result := ⟨.any, .var 17⟩ }),
        ("shadowed", openPatternFunScheme)] }

theorem shadowedOpenPatternFunSignature_closedness_rejects :
    schemesClosedCheck shadowedOpenPatternFunSignature = false := by
  decide

end SignatureCheckerRegression

/-! ## Lookup membership -/

/-- A successful data-constructor lookup is a table entry. -/
theorem findDataCtor_mem
    {signature : FrozenSig} {name : String} {scheme : CtorScheme}
    (found : signature.findDataCtor name = some scheme) :
    (name, scheme) ∈ signature.dataCtors := by
  unfold FrozenSig.findDataCtor at found
  cases findResult :
      signature.dataCtors.find? (fun entry => entry.1 == name) with
  | none => rw [findResult] at found; cases found
  | some entry =>
      rw [findResult] at found
      simp only [Option.map_some, Option.some.injEq] at found
      have entryMem := List.mem_of_find?_eq_some findResult
      have nameEq : entry.1 = name := by
        simpa using List.find?_some findResult
      rw [← nameEq, ← found]
      exact entryMem

/-- A successful pattern-constructor lookup is a table entry. -/
theorem findPatternCtor_mem
    {signature : FrozenSig} {name : String}
    {entry : PatternCtorScheme signature.observability}
    (found : signature.findPatternCtor name = some entry) :
    (name, entry) ∈ signature.patternCtors := by
  unfold FrozenSig.findPatternCtor at found
  cases findResult :
      signature.patternCtors.find? (fun entry => entry.1 == name) with
  | none => rw [findResult] at found; cases found
  | some tableEntry =>
      rw [findResult] at found
      simp only [Option.map_some, Option.some.injEq] at found
      have entryMem := List.mem_of_find?_eq_some findResult
      have nameEq : tableEntry.1 = name := by
        simpa using List.find?_some findResult
      rw [← nameEq, ← found]
      exact entryMem

/-- A successful primitive lookup is a table entry. -/
theorem findPrimitive_mem
    {signature : FrozenSig} {op : PrimOp} {scheme : CtorScheme}
    (found : signature.findPrimitive op = some scheme) :
    (op, scheme) ∈ signature.primitives := by
  unfold FrozenSig.findPrimitive at found
  cases findResult :
      signature.primitives.find? (fun entry => entry.1 == op) with
  | none => rw [findResult] at found; cases found
  | some entry =>
      rw [findResult] at found
      simp only [Option.map_some, Option.some.injEq] at found
      have entryMem := List.mem_of_find?_eq_some findResult
      have opEq : entry.1 = op := by
        have beqTrue := List.find?_some findResult
        cases h : entry.1 <;> cases op <;> rw [h] at beqTrue
        · exact absurd beqTrue (by decide)
        · exact absurd beqTrue (by decide)
      rw [← opEq, ← found]
      exact entryMem

/-! ## Checker soundness -/

/-- A checked data scheme has a syntactic data root. -/
theorem dataCtorCheck_result {scheme : CtorScheme}
    (checked : dataCtorCheck scheme = true) :
    ∃ former resultArgs, scheme.result = .data former resultArgs := by
  simp only [dataCtorCheck, Bool.and_eq_true] at checked
  obtain ⟨⟨resultChecked, _⟩, _⟩ := checked
  cases resultShape : scheme.result <;> rw [resultShape] at resultChecked <;>
    simp at resultChecked
  case data former resultArgs => exact ⟨former, resultArgs, rfl⟩

/-- A checked data scheme covers its capability binders. -/
theorem dataCtorCheck_capCoverage {scheme : CtorScheme}
    (checked : dataCtorCheck scheme = true) :
    ∀ varId ∈ Ty.fcvList scheme.args,
      varId ∈ scheme.capBinders → varId ∈ scheme.result.fcv := by
  simp only [dataCtorCheck, Bool.and_eq_true, List.all_eq_true] at checked
  obtain ⟨⟨_, capChecked⟩, _⟩ := checked
  intro varId varMem binderMem
  have := capChecked varId varMem
  simpa [binderMem] using this

/-- A checked data scheme covers its ordinary binders. -/
theorem dataCtorCheck_tyCoverage {scheme : CtorScheme}
    (checked : dataCtorCheck scheme = true) :
    ∀ varId ∈ Ty.ftvList scheme.args,
      varId ∈ scheme.tyBinders → varId ∈ scheme.result.ftv := by
  simp only [dataCtorCheck, Bool.and_eq_true, List.all_eq_true] at checked
  obtain ⟨_, tyChecked⟩ := checked
  intro varId varMem binderMem
  have := tyChecked varId varMem
  simpa [binderMem] using this

/-- A checked pattern-constructor entry is in the collection family. -/
theorem patternCtorCheck_sound
    {signature : FrozenSig} {name : String}
    {entry : PatternCtorScheme signature.observability}
    (checked : patternCtorCheck signature name entry = true) :
    ∃ former t,
      entry.scheme.result = .data former [.var t] ∧
      signature.observability former = some [true] ∧
      (∀ arg ∈ entry.scheme.args,
        arg = .var t ∨ arg = .data former [.var t]) ∧
      ∃ constructors,
        signature.toMatcherSig.constructorsFor? former = some constructors ∧
        (name, entry.scheme.args.length) ∈ constructors := by
  unfold patternCtorCheck at checked
  cases resultShape : entry.scheme.result with
  | data former resultArgs =>
      rw [resultShape] at checked
      cases resultArgs with
      | nil => simp at checked
      | cons headArg restArgs =>
          cases restArgs with
          | cons _ _ => cases headArg <;> simp at checked
          | nil =>
              cases headArg with
              | var t =>
                  simp only [Bool.and_eq_true, decide_eq_true_eq,
                    List.all_eq_true] at checked
                  obtain ⟨⟨maskOK, argsOK⟩, indexOK⟩ := checked
                  refine ⟨former, t, rfl, maskOK, ?_, ?_⟩
                  · intro arg argMem
                    have := argsOK arg argMem
                    simpa using this
                  · cases indexFound :
                        signature.toMatcherSig.constructorsFor? former with
                    | none =>
                        rw [indexFound] at indexOK
                        simp at indexOK
                    | some constructors =>
                        refine ⟨constructors, rfl, ?_⟩
                        rw [indexFound] at indexOK
                        simpa using indexOK
              | skolem _ => simp at checked
              | unit => simp at checked
              | int => simp at checked
              | bool => simp at checked
              | data _ _ => simp at checked
              | prod _ => simp at checked
              | fn _ _ => simp at checked
              | matcher _ _ => simp at checked
              | slot _ _ => simp at checked
  | var _ => rw [resultShape] at checked; simp at checked
  | skolem _ => rw [resultShape] at checked; simp at checked
  | unit => rw [resultShape] at checked; simp at checked
  | int => rw [resultShape] at checked; simp at checked
  | bool => rw [resultShape] at checked; simp at checked
  | prod _ => rw [resultShape] at checked; simp at checked
  | fn _ _ => rw [resultShape] at checked; simp at checked
  | matcher _ _ => rw [resultShape] at checked; simp at checked
  | slot _ _ => rw [resultShape] at checked; simp at checked

/-- Family arguments have no capability variables. -/
theorem family_fcvList_nil {former : String} {t : TypePM.TyVar} :
    ∀ {args : List Ty},
      (∀ arg ∈ args, arg = .var t ∨ arg = .data former [.var t]) →
      Ty.fcvList args = []
  | [], _ => rfl
  | arg :: args, argsOK => by
      have tailEq : Ty.fcvList args = [] :=
        family_fcvList_nil fun candidate mem =>
          argsOK candidate (List.mem_cons_of_mem _ mem)
      rcases argsOK arg (by simp) with rfl | rfl <;>
        simp [Ty.fcvList, Ty.fcv, tailEq]

/-- Family arguments mention only the element variable. -/
theorem family_ftvList_mem {former : String} {t : TypePM.TyVar} :
    ∀ {args : List Ty},
      (∀ arg ∈ args, arg = .var t ∨ arg = .data former [.var t]) →
      ∀ varId ∈ Ty.ftvList args, varId = t
  | [], _, varId, varMem => by simp [Ty.ftvList] at varMem
  | arg :: args, argsOK, varId, varMem => by
      rw [Ty.ftvList, List.mem_append] at varMem
      rcases varMem with headMem | tailMem
      · rcases argsOK arg (by simp) with rfl | rfl <;>
          simpa [Ty.ftv, Ty.ftvList] using headMem
      · exact family_ftvList_mem
          (fun candidate mem => argsOK candidate (by simp [mem]))
          varId tailMem

/-- A demand between collection element capabilities lifts pointwise through
the canonical family-field projection. -/
theorem familyChild_demands
    {former : String} {t : TypePM.TyVar}
    {producer consumer : Cap} {args : List Ty}
    (argsOK : ∀ arg ∈ args,
      arg = .var t ∨ arg = .data former [.var t])
    (demand : CapabilityDemand producer consumer) :
    CapabilityDemands
      (args.map (familyChild former t producer))
      (args.map (familyChild former t consumer)) := by
  induction args with
  | nil => exact .nil
  | cons arg args induction =>
      have tailOK : ∀ candidate ∈ args,
          candidate = .var t ∨ candidate = .data former [.var t] :=
        fun candidate membership =>
          argsOK candidate (List.mem_cons_of_mem arg membership)
      have tailDemand := induction tailOK
      rcases argsOK arg (by simp) with rfl | rfl
      · simpa [familyChild] using
          CapabilityDemands.cons demand tailDemand
      · simpa [familyChild] using
          CapabilityDemands.cons
            (CapabilityDemand.con
              (CapabilityDemands.cons demand CapabilityDemands.nil))
            tailDemand

/-- A checked table entry whose scheme has a `List` result root is one of the
two canonical list declarations. -/
theorem listCtorCheck_sound
    {name : String} {scheme : CtorScheme}
    (checked : listCtorCheck (name, scheme) = true)
    {resultArgs : List Ty}
    (resultShape : scheme.result = .data "List" resultArgs) :
    (name = "nil" ∧ scheme = nilCanonicalScheme) ∨
      (name = "cons" ∧ scheme = consCanonicalScheme) := by
  unfold listCtorCheck at checked
  rw [resultShape] at checked
  simpa using checked

/-- A positive executable check establishes every dynamic obligation. -/
theorem frozenSigWFCheck_sound
    {signature : FrozenSig}
    (checked : frozenSigWFCheck signature = true)
    (armBasic : signature.armExhaustive = basicArmExhaustive) :
    FrozenSigWF signature := by
  simp only [frozenSigWFCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨closedChecked, nilFound⟩, consFound⟩, funsNodup⟩,
    dataChecked⟩, patternChecked⟩, primChecked⟩, listChecked⟩ := checked
  refine
    { schemesClosed := schemesClosedCheck_sound closedChecked
      listSigWF :=
        ⟨⟨nilCanonicalScheme, nilFound, nilCanonicalScheme_inst⟩,
          ⟨consCanonicalScheme, consFound, consCanonicalScheme_inst⟩⟩
      patternFunNamesNodup := funsNodup
      armExhaustiveBasic := armBasic
      dataResult := ?_
      dataInstArgsUnique := ?_
      patternInstArgsUnique := ?_
      patternCapArgsUnique := ?_
      patternCapDemands := ?_
      patternCtorIndexed := ?_
      primEvalTyped := ?_
      listCtorsExclusive := ?_
      primitivesCanonical := ?_ }
  · intro name scheme targets result found instanceTyping
    have entryChecked := dataChecked _ (findDataCtor_mem found)
    obtain ⟨former, resultArgs, resultShape⟩ :=
      dataCtorCheck_result entryChecked
    obtain ⟨arguments, resultEq⟩ :=
      CtorScheme.instDataRoot resultShape instanceTyping
    exact ⟨former, arguments, resultEq⟩
  · intro name scheme leftTargets rightTargets result found left right
    have entryChecked := dataChecked _ (findDataCtor_mem found)
    exact CtorScheme.instArgsUnique_of_coverage
      (dataCtorCheck_capCoverage entryChecked)
      (dataCtorCheck_tyCoverage entryChecked) left right
  · intro name entry leftTargets rightTargets result found left right
    have entryChecked := patternChecked _ (findPatternCtor_mem found)
    obtain ⟨former, t, resultShape, maskOK, argsOK, _⟩ :=
      patternCtorCheck_sound entryChecked
    refine CtorScheme.instArgsUnique_of_coverage ?_ ?_ left right
    · rw [family_fcvList_nil argsOK]
      intro varId varMem
      cases varMem
    · intro varId varMem _
      rw [family_ftvList_mem argsOK varId varMem, resultShape]
      simp [Ty.ftv, Ty.ftvList]
  · intro name entry leftCaps rightCaps result found left right
    have entryChecked := patternChecked _ (findPatternCtor_mem found)
    obtain ⟨former, t, resultShape, maskOK, argsOK, _⟩ :=
      patternCtorCheck_sound entryChecked
    obtain ⟨leftElem, leftOuter, leftChildren⟩ :=
      PatternCtorScheme.capCompatible_family_inversion resultShape maskOK
        argsOK left
    obtain ⟨rightElem, rightOuter, rightChildren⟩ :=
      PatternCtorScheme.capCompatible_family_inversion resultShape maskOK
        argsOK right
    have elemEq : leftElem = rightElem := by
      have outerEq := leftOuter.symm.trans rightOuter
      simpa using outerEq
    rw [leftChildren, rightChildren, elemEq]
  · intro name entry producerCaps consumerCaps producerResult consumerResult
      found producerCompatible consumerCompatible demand
    have entryChecked := patternChecked _ (findPatternCtor_mem found)
    obtain ⟨former, t, resultShape, maskOK, argsOK, _⟩ :=
      patternCtorCheck_sound entryChecked
    obtain ⟨producerElem, producerOuter, producerChildren⟩ :=
      PatternCtorScheme.capCompatible_family_inversion resultShape maskOK
        argsOK producerCompatible
    obtain ⟨consumerElem, consumerOuter, consumerChildren⟩ :=
      PatternCtorScheme.capCompatible_family_inversion resultShape maskOK
        argsOK consumerCompatible
    rw [producerOuter, consumerOuter] at demand
    have elementDemand : CapabilityDemand producerElem consumerElem := by
      have childrenDemand := demand.con_children
      cases childrenDemand with
      | cons head tail =>
          cases tail
          exact head
    rw [producerChildren, consumerChildren]
    exact familyChild_demands argsOK elementDemand
  · intro name entry childCaps capability found compatible
    have entryChecked := patternChecked _ (findPatternCtor_mem found)
    obtain ⟨former, t, resultShape, maskOK, argsOK,
      constructors, indexFound, indexed⟩ :=
      patternCtorCheck_sound entryChecked
    obtain ⟨elem, outerEq, childrenEq⟩ :=
      PatternCtorScheme.capCompatible_family_inversion resultShape maskOK
        argsOK compatible
    refine ⟨former, [elem], constructors, outerEq, indexFound, ?_⟩
    have lengthEq : childCaps.length = entry.scheme.args.length := by
      rw [childrenEq, List.length_map]
    rw [lengthEq]
    exact indexed
  · intro op scheme values targets result value found instanceTyping
      valuesTyped evaluated
    have schemeCanonical := primChecked _ (findPrimitive_mem found)
    exact primEvalTyped_of_canonical nilFound consFound found
      schemeCanonical instanceTyping valuesTyped evaluated
  · intro name scheme targets element found instanceTyping
    have memEntry := findDataCtor_mem found
    obtain ⟨former, resultArgs, resultShape⟩ :=
      dataCtorCheck_result (dataChecked _ memEntry)
    obtain ⟨arguments, resultEq⟩ :=
      CtorScheme.instDataRoot resultShape instanceTyping
    simp only [Ty.listT] at resultEq
    injection resultEq with formerEq argumentsEq
    subst formerEq
    rcases listCtorCheck_sound (listChecked _ memEntry) resultShape with
      ⟨nameEq, schemeEq⟩ | ⟨nameEq, schemeEq⟩
    · subst schemeEq
      obtain ⟨elem, targetsEq, _⟩ :=
        nilCanonicalScheme_inst_inversion instanceTyping
      exact .inl ⟨nameEq, targetsEq⟩
    · subst schemeEq
      obtain ⟨elem, targetsEq, resultElemEq⟩ :=
        consCanonicalScheme_inst_inversion instanceTyping
      have elemEq : element = elem := Ty.listT_injective resultElemEq
      subst elemEq
      exact .inr ⟨nameEq, targetsEq⟩
  · intro op scheme found
    exact primChecked _ (findPrimitive_mem found)
