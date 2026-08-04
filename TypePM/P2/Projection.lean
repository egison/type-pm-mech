import TypePM.P2.Shape
import TypePM.P2.Substitution

/-!
# Signature-directed evidence projection

This module implements non-CAS, normalized-input constructor
projection.  Child evidence is collected along paths exposed by a frozen
observability mask, then rebuilt in the result signature's argument order.
The field/result types must be a freshly instantiated and zonked constructor
signature; re-running the low-level function after arbitrarily substituting
the result type is outside this API boundary.
-/

namespace TypePM.P2
namespace Projection

open Shape

/-- Evidence assigned to freshly instantiated ordinary signature variables. -/
abbrev Assignments := List (TypePM.TyVar × Evidence)

mutual

/-- Ordinary variables occurring anywhere in a P2 type. -/
def targetVars : Ty → List TypePM.TyVar
  | .var a       => [a]
  | .skolem _    => []
  | .unit        => []
  | .int         => []
  | .bool        => []
  | .data _ tys  => targetVarsList tys
  | .prod tys    => targetVarsList tys
  | .fn dom cod  => targetVars dom ++ targetVars cod
  | .matcher _ τ => targetVars τ
  | .slot _ τ    => targetVars τ

/-- Ordinary variables occurring in a list of P2 types. -/
def targetVarsList : List Ty → List TypePM.TyVar
  | []       => []
  | τ :: tys => targetVars τ ++ targetVarsList tys

end

mutual

/--
Find candidate variables reachable through capability-visible type paths.

Products expose every component.  A data former exposes exactly the positions
selected by its mask.  Functions, matchers, slots, and unknown data formers are
barriers.  A present mask with the wrong arity is malformed and causes failure.
-/
def relevantVars
    (observable : Observability) (candidates : List TypePM.TyVar) :
    Ty → Option (List TypePM.TyVar)
  | .var a =>
      if a ∈ candidates then some [a] else some []
  | .skolem _ =>
      some []
  | .unit =>
      some []
  | .int =>
      some []
  | .bool =>
      some []
  | .data name tys =>
      match observable name with
      | none      => some []
      | some mask => relevantVarsMasked observable candidates mask tys
  | .prod tys =>
      relevantVarsList observable candidates tys
  | .fn _ _ =>
      some []
  | .matcher _ _ =>
      some []
  | .slot _ _ =>
      some []

/-- Collect reachable variables from positions that are all observable. -/
def relevantVarsList
    (observable : Observability) (candidates : List TypePM.TyVar) :
    List Ty → Option (List TypePM.TyVar)
  | [] => some []
  | τ :: tys =>
      match relevantVars observable candidates τ,
            relevantVarsList observable candidates tys with
      | some head, some tail => some (head ++ tail)
      | _, _                 => none

/-- Collect reachable variables under an exact-arity observability mask. -/
def relevantVarsMasked
    (observable : Observability) (candidates : List TypePM.TyVar) :
    List Bool → List Ty → Option (List TypePM.TyVar)
  | [], [] =>
      some []
  | isObservable :: mask, τ :: tys =>
      let head :=
        if isObservable
          then relevantVars observable candidates τ
          else some []
      match head, relevantVarsMasked observable candidates mask tys with
      | some headVars, some tailVars => some (headVars ++ tailVars)
      | _, _                         => none
  | _, _ =>
      none

end

/-- Look up evidence already assigned to a signature variable. -/
def lookupAssignment
    (varId : TypePM.TyVar) : Assignments → Option Evidence
  | [] => none
  | (candidate, evidence) :: rest =>
      if varId = candidate then some evidence
      else lookupAssignment varId rest

/--
Insert one assignment, merging a duplicate only when its evidence agrees
exactly according to `Shape.merge`.
-/
def insertAssignment
    (varId : TypePM.TyVar) (evidence : Evidence) :
    Assignments → Option Assignments
  | [] =>
      some [(varId, evidence)]
  | (candidate, previous) :: rest =>
      if varId = candidate then
        match Shape.merge previous evidence with
        | some merged => some ((candidate, merged) :: rest)
        | none        => none
      else
        match insertAssignment varId evidence rest with
        | some updated => some ((candidate, previous) :: updated)
        | none         => none

/-- Exact-merge every assignment on the right into the left environment. -/
def mergeAssignments (left : Assignments) : Assignments → Option Assignments
  | [] => some left
  | (varId, evidence) :: rest =>
      match insertAssignment varId evidence left with
      | some updated => mergeAssignments updated rest
      | none         => none

/-- Test whether at least one variable has collected evidence. -/
def hasAssignment : List TypePM.TyVar → Assignments → Bool
  | [], _ => false
  | varId :: variables, assignments =>
      match lookupAssignment varId assignments with
      | some _ => true
      | none   => hasAssignment variables assignments

mutual

/--
Collect assignments contributed by one field.

`unseen` is checked first and contributes no assignment.  Consequently, a
target type—substituted or otherwise—cannot seed capability evidence by itself.
Known or structured evidence is checked only when the field has a path to a
relevant result variable.
-/
def collectAssignments
    (observable : Observability) (resultVariables : List TypePM.TyVar) :
    Ty → Evidence → Option Assignments
  | _, .unseen =>
      some []
  | fieldType, evidence =>
      match relevantVars observable resultVariables fieldType with
      | none =>
          none
      | some [] =>
          some []
      | some (_ :: _) =>
          match fieldType, evidence with
          | .var varId, evidence =>
              if varId ∈ resultVariables
                then some [(varId, evidence)]
                else some []
          | .prod componentTypes, .prod componentEvidence =>
              collectAssignmentsList observable resultVariables
                componentTypes componentEvidence
          | .data name arguments, .con evidenceName children =>
              if name = evidenceName then
                match observable name with
                | some mask =>
                    collectAssignmentsMasked observable resultVariables
                      mask arguments children
                | none =>
                    none
              else
                none
          | _, _ =>
              none

/-- Collect and exact-merge assignments from equal-length parallel lists. -/
def collectAssignmentsList
    (observable : Observability) (resultVariables : List TypePM.TyVar) :
    List Ty → List Evidence → Option Assignments
  | [], [] =>
      some []
  | fieldType :: fieldTypes, evidence :: restEvidence =>
      match collectAssignments observable resultVariables fieldType evidence,
            collectAssignmentsList observable resultVariables
              fieldTypes restEvidence with
      | some head, some tail => mergeAssignments head tail
      | _, _                 => none
  | _, _ =>
      none

/-- Collect assignments under an exact-arity observability mask. -/
def collectAssignmentsMasked
    (observable : Observability) (resultVariables : List TypePM.TyVar) :
    List Bool → List Ty → List Evidence → Option Assignments
  | [], [], [] =>
      some []
  | isObservable :: mask, argument :: arguments, child :: children =>
      let head :=
        if isObservable
          then collectAssignments observable resultVariables argument child
          else some []
      match head,
            collectAssignmentsMasked observable resultVariables
              mask arguments children with
      | some headAssignments, some tailAssignments =>
          mergeAssignments headAssignments tailAssignments
      | _, _ =>
          none
  | _, _, _ =>
      none

end

mutual

/--
Build a structured result-slot template after at least one variable in the
slot has received evidence.
-/
def buildResultTemplate
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    Ty → Option Evidence
  | .var varId =>
      if varId ∈ resultVariables then
        match lookupAssignment varId assignments with
        | some evidence => some evidence
        | none          => some .unseen
      else
        some (.known .none)
  | .prod componentTypes =>
      match relevantVars observable resultVariables (.prod componentTypes) with
      | none =>
          none
      | some [] =>
          some (.known .none)
      | some (_ :: _) =>
          match buildResultTemplateList observable resultVariables assignments
                  componentTypes with
          | some components => some (.prod components)
          | none            => none
  | .data name arguments =>
      match relevantVars observable resultVariables (.data name arguments) with
      | none =>
          none
      | some [] =>
          some (.known .none)
      | some (_ :: _) =>
          match observable name with
          | none =>
              some (.known .none)
          | some mask =>
              match buildResultTemplateMasked observable resultVariables
                      assignments mask arguments with
              | some children => some (.con name children)
              | none          => none
  | .int =>
      some (.known .none)
  | .skolem _ =>
      some (.known .none)
  | .unit =>
      some (.known .none)
  | .bool =>
      some (.known .none)
  | .fn _ _ =>
      some (.known .none)
  | .matcher _ _ =>
      some (.known .none)
  | .slot _ _ =>
      some (.known .none)

/-- Build a template list whose positions are all structurally exposed. -/
def buildResultTemplateList
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    List Ty → Option (List Evidence)
  | [] =>
      some []
  | componentType :: componentTypes =>
      match buildResultTemplate observable resultVariables assignments
              componentType,
            buildResultTemplateList observable resultVariables assignments
              componentTypes with
      | some head, some tail => some (head :: tail)
      | _, _                 => none

/-- Build a structured template under an exact-arity mask. -/
def buildResultTemplateMasked
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    List Bool → List Ty → Option (List Evidence)
  | [], [] =>
      some []
  | isObservable :: mask, argument :: arguments =>
      let head :=
        if isObservable
          then buildResultTemplate observable resultVariables assignments
                 argument
          else some (.known .none)
      match head,
            buildResultTemplateMasked observable resultVariables assignments
              mask arguments with
      | some headEvidence, some tailEvidence =>
          some (headEvidence :: tailEvidence)
      | _, _ =>
          none
  | _, _ =>
      none

end

/--
Build one result argument slot.

A ground or structurally hidden slot has canonical `known none` evidence.  An
observable slot that received no assignment remains `unseen`.
-/
def buildResultSlot
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments)
    (slotType : Ty) : Option Evidence :=
  match relevantVars observable resultVariables slotType with
  | none =>
      none
  | some [] =>
      some (.known .none)
  | some variables =>
      if hasAssignment variables assignments then
        buildResultTemplate observable resultVariables assignments slotType
      else
        some .unseen

mutual

/-- Build every result argument slot in its declared order. -/
def buildResultSlots
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    List Ty → Option (List Evidence)
  | [] =>
      some []
  | slotType :: slotTypes =>
      match buildResultSlot observable resultVariables assignments slotType,
            buildResultSlots observable resultVariables assignments
              slotTypes with
      | some head, some tail => some (head :: tail)
      | _, _                 => none

/-- Build result slots selected by an exact-arity root mask. -/
def buildResultSlotsMasked
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    List Bool → List Ty → Option (List Evidence)
  | [], [] =>
      some []
  | isObservable :: mask, argument :: arguments =>
      let head :=
        if isObservable
          then buildResultSlot observable resultVariables assignments argument
          else some (.known .none)
      match head,
            buildResultSlotsMasked observable resultVariables assignments
              mask arguments with
      | some headEvidence, some tailEvidence =>
          some (headEvidence :: tailEvidence)
      | _, _ =>
          none
  | _, _ =>
      none

end

/--
Build the result's structural root.

A constructor result must have a known, well-formed mask.  A product result
exposes all components.  Every other root is a projection barrier.
-/
def buildResultRoot
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Assignments) :
    Ty → Option Evidence
  | .prod componentTypes =>
      match buildResultSlots observable resultVariables assignments
              componentTypes with
      | some components => some (.prod components)
      | none            => none
  | .data name arguments =>
      match observable name with
      | none =>
          none
      | some mask =>
          match buildResultSlotsMasked observable resultVariables assignments
                  mask arguments with
          | some children => some (.con name children)
          | none          => none
  | _ =>
      none

/-! ## Order-independent certified projection -/

/-- One constructor field paired with the evidence produced by that child. -/
abbrev FieldEvidence := Ty × Evidence

/-- Pair parallel field/evidence lists, rejecting an arity mismatch. -/
def pairFields : List Ty → List Evidence → Option (List FieldEvidence)
  | [], [] =>
      some []
  | fieldType :: fieldTypes, evidence :: childEvidence =>
      match pairFields fieldTypes childEvidence with
      | some pairs => some ((fieldType, evidence) :: pairs)
      | none       => none
  | _, _ =>
      none

/-- Pairing the two projections of an existing pair list recovers that list. -/
@[simp] theorem pairFields_map (fields : List FieldEvidence) :
    pairFields (fields.map Prod.fst) (fields.map Prod.snd) =
      some fields := by
  induction fields with
  | nil =>
      rfl
  | cons field fields ih =>
      rcases field with ⟨fieldType, evidence⟩
      simp [pairFields, ih]

/--
Validate every paired field independently and retain its assignment chunk.

Chunks are not merged here.  Keeping the field boundary makes simultaneous
field/evidence permutation explicit and permits an order-independent
aggregation stage.
-/
def collectFieldAssignments
    (observable : Observability)
    (resultVariables : List TypePM.TyVar) :
    List FieldEvidence → Option (List Assignments)
  | [] =>
      some []
  | (fieldType, evidence) :: fields =>
      match collectAssignments observable resultVariables fieldType evidence,
            collectFieldAssignments observable resultVariables fields with
      | some head, some tail => some (head :: tail)
      | _, _                 => none

/-- Evidence chunks that assign one particular result variable. -/
def evidenceContributions
    (varId : TypePM.TyVar) (chunks : List Assignments) :
    List Evidence :=
  chunks.filterMap (lookupAssignment varId)

/--
Aggregate chunks in fixed result-variable order.

For each variable, exact evidence merge is a commutative/associative fold.
An `unseen` fold means that no field supplied evidence and is omitted from the
finite assignment environment.
-/
def canonicalAssignments
    (resultVariables : List TypePM.TyVar)
    (chunks : List Assignments) : Option Assignments :=
  match resultVariables with
  | [] =>
      some []
  | varId :: variables =>
      match Shape.mergeAll (evidenceContributions varId chunks),
            canonicalAssignments variables chunks with
      | some .unseen, some tail =>
          some tail
      | some evidence, some tail =>
          some ((varId, evidence) :: tail)
      | _, _ =>
          none
termination_by resultVariables

/--
Order-independent projection from already paired constructor fields.

The result-variable order comes solely from the result signature.  Field order
affects only a commutative exact-merge fold.
-/
def projectPaired
    (observable : Observability)
    (resultType : Ty)
    (fields : List FieldEvidence) : Option Evidence := do
  let resultVariables ←
    relevantVars observable (targetVars resultType) resultType
  let chunks ←
    collectFieldAssignments observable resultVariables fields
  let assignments ←
    canonicalAssignments resultVariables chunks
  buildResultRoot observable resultVariables assignments resultType

/--
Successful paired-field validation is transported by every simultaneous
field/evidence permutation, and the resulting chunks have the same
permutation.
-/
theorem collectFieldAssignments_eq_some_of_perm
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    {left right : List FieldEvidence}
    (permutation : left.Perm right)
    {leftChunks : List Assignments}
    (hleft :
      collectFieldAssignments observable resultVariables left =
        some leftChunks) :
    ∃ rightChunks,
      collectFieldAssignments observable resultVariables right =
        some rightChunks ∧
      leftChunks.Perm rightChunks := by
  induction permutation generalizing leftChunks with
  | nil =>
      simp only [collectFieldAssignments, Option.some.injEq] at hleft
      subst leftChunks
      exact ⟨[], rfl, List.Perm.nil⟩
  | @cons field leftFields rightFields permutation ih =>
      rcases field with ⟨fieldType, evidence⟩
      simp only [collectFieldAssignments] at hleft ⊢
      cases hfield :
          collectAssignments observable resultVariables fieldType evidence with
      | none =>
          simp [hfield] at hleft
      | some head =>
          cases htail :
              collectFieldAssignments observable resultVariables leftFields with
          | none =>
              simp [hfield, htail] at hleft
          | some tail =>
              have left_eq : head :: tail = leftChunks := by
                simpa [hfield, htail] using hleft
              obtain ⟨rightTail, hright, tail_perm⟩ := ih htail
              subst leftChunks
              exact ⟨head :: rightTail, by
                simp [hright], tail_perm.cons head⟩
  | swap first second rest =>
      rcases first with ⟨firstType, firstEvidence⟩
      rcases second with ⟨secondType, secondEvidence⟩
      simp only [collectFieldAssignments] at hleft ⊢
      cases hfirst :
          collectAssignments observable resultVariables
            firstType firstEvidence with
      | none =>
          simp [hfirst] at hleft
      | some firstChunk =>
          cases hsecond :
              collectAssignments observable resultVariables
                secondType secondEvidence with
          | none =>
              simp [hfirst, hsecond] at hleft
          | some secondChunk =>
              cases hrest :
                  collectFieldAssignments observable resultVariables rest with
              | none =>
                  simp [hfirst, hsecond, hrest] at hleft
              | some restChunks =>
                  have left_eq :
                      secondChunk :: firstChunk :: restChunks = leftChunks := by
                    simpa [hfirst, hsecond, hrest] using hleft
                  subst leftChunks
                  exact ⟨firstChunk :: secondChunk :: restChunks, by
                    rfl,
                    List.Perm.swap _ _ _⟩
  | trans leftMiddle middleRight left_ih right_ih =>
      obtain ⟨middleChunks, hmiddle, left_perm⟩ :=
        left_ih hleft
      obtain ⟨rightChunks, hright, right_perm⟩ :=
        right_ih hmiddle
      exact ⟨rightChunks, hright, left_perm.trans right_perm⟩

/-- Canonical aggregation depends only on the multiset of field chunks. -/
theorem canonicalAssignments_perm
    (resultVariables : List TypePM.TyVar)
    {left right : List Assignments}
    (permutation : left.Perm right) :
    canonicalAssignments resultVariables left =
      canonicalAssignments resultVariables right := by
  induction resultVariables with
  | nil =>
      simp [canonicalAssignments]
  | cons varId variables ih =>
      have merge_eq :=
        Shape.mergeAll_perm
          (permutation.filterMap (lookupAssignment varId))
      simp [canonicalAssignments, evidenceContributions, merge_eq, ih]

/--
Signature-directed paired projection is invariant under simultaneous
permutation of field types and their corresponding evidence.

The equality includes rejection: if one ordering detects malformed or
conflicting evidence, every ordering rejects.
-/
theorem projectPaired_perm
    (observable : Observability) (resultType : Ty)
    {left right : List FieldEvidence}
    (permutation : left.Perm right) :
    projectPaired observable resultType left =
      projectPaired observable resultType right := by
  cases hvars :
      relevantVars observable (targetVars resultType) resultType with
  | none =>
      simp [projectPaired, hvars]
  | some resultVariables =>
      cases hleft :
          collectFieldAssignments observable resultVariables left with
      | none =>
          cases hright :
              collectFieldAssignments observable resultVariables right with
          | none =>
              simp [projectPaired, hvars, hleft, hright]
          | some rightChunks =>
              obtain ⟨leftChunks, leftSuccess, _⟩ :=
                collectFieldAssignments_eq_some_of_perm
                  observable resultVariables permutation.symm hright
              rw [hleft] at leftSuccess
              contradiction
      | some leftChunks =>
          obtain ⟨rightChunks, hright, chunks_perm⟩ :=
            collectFieldAssignments_eq_some_of_perm
              observable resultVariables permutation hleft
          have canonical_eq :=
            canonicalAssignments_perm resultVariables chunks_perm
          simp [projectPaired, hvars, hleft, hright, canonical_eq]

/--
Project child evidence through a fresh, normalized constructor signature.

The field and evidence lists are parallel and must have equal length.  The
result tree is built from the result signature, not from field order.
`project` is the low-level executable function; `ProjectionSignature` below
records its resolved-root/fresh-parameter preconditions explicitly.
-/
def project
    (observable : Observability)
    (fieldTypes : List Ty)
    (resultType : Ty)
    (childEvidence : List Evidence) : Option Evidence := do
  let resultVariables ←
    relevantVars observable (targetVars resultType) resultType
  let assignments ←
    collectAssignmentsList observable resultVariables
      fieldTypes childEvidence
  buildResultRoot observable resultVariables assignments resultType

/-- A constructor signature has a resolved, mask-checked result root. -/
inductive ResolvedResultRoot
    (observable : Observability) : Ty → Prop where
  | data {name arguments mask} :
      observable name = some mask →
      mask.length = arguments.length →
      ResolvedResultRoot observable (.data name arguments)
  | product {components} :
      ResolvedResultRoot observable (.prod components)

/--
Certified input boundary for signature-directed projection.

Canonical former names, fresh instantiation, and zonking are supplied by the
preceding elaboration phase.  This record captures the property used directly
here: a resolved result root with the frozen mask.  A fresh signature parameter
may occur more than once in the result; those occurrences intentionally share
one evidence assignment.
-/
structure ProjectionSignature (observable : Observability) where
  fieldTypes : List Ty
  resultType : Ty
  resultRoot : ResolvedResultRoot observable resultType

/-- Replace only the ordered field list of a certified result signature. -/
def ProjectionSignature.replaceFields
    {observable : Observability}
    (signature : ProjectionSignature observable)
    (fieldTypes : List Ty) :
    ProjectionSignature observable where
  fieldTypes := fieldTypes
  resultType := signature.resultType
  resultRoot := signature.resultRoot

/--
Project through an explicitly certified normalized signature.

Unlike low-level `project`, this public path pairs fields with child evidence
first and uses the canonical order-independent aggregation layer.
-/
def projectSignature
    {observable : Observability}
    (signature : ProjectionSignature observable)
    (childEvidence : List Evidence) : Option Evidence := do
  let fields ← pairFields signature.fieldTypes childEvidence
  projectPaired observable signature.resultType fields

/--
The certified projection path is invariant when field types and their
corresponding child evidence are permuted together.
-/
theorem projectSignature_simultaneous_perm
    {observable : Observability}
    (signature : ProjectionSignature observable)
    {left right : List FieldEvidence}
    (hfields : signature.fieldTypes = left.map Prod.fst)
    (permutation : left.Perm right) :
    projectSignature signature (left.map Prod.snd) =
      projectSignature
        (signature.replaceFields (right.map Prod.fst))
        (right.map Prod.snd) := by
  simpa [projectSignature, ProjectionSignature.replaceFields, hfields] using
    projectPaired_perm observable signature.resultType permutation

/--
A proof-relevant staged derivation of certified projection.

The relation exposes every possible failure boundary: parallel-list pairing,
observable result-variable discovery, per-field structural validation,
order-independent exact aggregation, and rebuilding in result-signature order.
-/
inductive ProjectionDerivation
    (observable : Observability)
    (fieldTypes : List Ty) (resultType : Ty)
    (childEvidence : List Evidence) :
    Evidence → Prop where
  | run
      {fields resultVariables chunks assignments result} :
      pairFields fieldTypes childEvidence = some fields →
      relevantVars observable (targetVars resultType) resultType =
        some resultVariables →
      collectFieldAssignments observable resultVariables fields =
        some chunks →
      canonicalAssignments resultVariables chunks = some assignments →
      buildResultRoot observable resultVariables assignments resultType =
        some result →
      ProjectionDerivation observable fieldTypes resultType
        childEvidence result

/--
The executable certified path succeeds exactly when all five projection
stages have a derivation.
-/
theorem projectSignature_eq_some_iff
    {observable : Observability}
    (signature : ProjectionSignature observable)
    {childEvidence : List Evidence} {result : Evidence} :
    projectSignature signature childEvidence = some result ↔
      ProjectionDerivation observable signature.fieldTypes
        signature.resultType childEvidence result := by
  constructor
  · intro hproject
    cases hfields :
        pairFields signature.fieldTypes childEvidence with
    | none =>
        simp [projectSignature, hfields] at hproject
    | some fields =>
        cases hvars :
            relevantVars observable
              (targetVars signature.resultType)
              signature.resultType with
        | none =>
            simp [projectSignature, projectPaired, hfields, hvars] at hproject
        | some resultVariables =>
            cases hchunks :
                collectFieldAssignments observable resultVariables fields with
            | none =>
                simp [projectSignature, projectPaired, hfields, hvars,
                  hchunks] at hproject
            | some chunks =>
                cases hassignments :
                    canonicalAssignments resultVariables chunks with
                | none =>
                    simp [projectSignature, projectPaired, hfields, hvars,
                      hchunks, hassignments] at hproject
                | some assignments =>
                    have hresult :
                        buildResultRoot observable resultVariables assignments
                            signature.resultType =
                          some result := by
                      simpa [projectSignature, projectPaired, hfields, hvars,
                        hchunks, hassignments] using hproject
                    exact ProjectionDerivation.run
                      hfields hvars hchunks hassignments hresult
  · intro derivation
    cases derivation with
    | run hfields hvars hchunks hassignments hresult =>
        simp [projectSignature, projectPaired, hfields, hvars,
          hchunks, hassignments, hresult]

/-- Declarative agreement between a result type's root and projected evidence. -/
inductive ResultEvidenceRoot : Ty → Evidence → Prop where
  | data {name arguments children} :
      ResultEvidenceRoot (.data name arguments) (.con name children)
  | product {components evidence} :
      ResultEvidenceRoot (.prod components) (.prod evidence)

/-- Rebuilding a result can never change its constructor/product root. -/
theorem buildResultRoot_sound
    {observable : Observability}
    {resultVariables : List TypePM.TyVar}
    {assignments : Assignments}
    {resultType : Ty} {result : Evidence}
    (hbuild :
      buildResultRoot observable resultVariables assignments resultType =
        some result) :
    ResultEvidenceRoot resultType result := by
  cases resultType with
  | data name arguments =>
      cases hmask : observable name with
      | none =>
          simp [buildResultRoot, hmask] at hbuild
      | some mask =>
          cases hchildren :
              buildResultSlotsMasked observable resultVariables assignments
                mask arguments with
          | none =>
              simp [buildResultRoot, hmask, hchildren] at hbuild
          | some children =>
              have result_eq : result = .con name children := by
                simpa [buildResultRoot, hmask, hchildren] using hbuild.symm
              subst result
              exact ResultEvidenceRoot.data
  | prod components =>
      cases hevidence :
          buildResultSlots observable resultVariables assignments components with
      | none =>
          simp [buildResultRoot, hevidence] at hbuild
      | some evidence =>
          have result_eq : result = .prod evidence := by
            simpa [buildResultRoot, hevidence] using hbuild.symm
          subst result
          exact ResultEvidenceRoot.product
  | var varId =>
      simp [buildResultRoot] at hbuild
  | skolem skolemId =>
      simp [buildResultRoot] at hbuild
  | unit =>
      simp [buildResultRoot] at hbuild
  | int =>
      simp [buildResultRoot] at hbuild
  | bool =>
      simp [buildResultRoot] at hbuild
  | fn domain codomain =>
      simp [buildResultRoot] at hbuild
  | matcher cap target =>
      simp [buildResultRoot] at hbuild
  | slot cap target =>
      simp [buildResultRoot] at hbuild

/-- A staged projection derivation always has the declared result root. -/
theorem ProjectionDerivation.resultRoot
    {observable : Observability}
    {fieldTypes : List Ty} {resultType : Ty}
    {childEvidence : List Evidence} {result : Evidence}
    (derivation :
      ProjectionDerivation observable fieldTypes resultType
        childEvidence result) :
    ResultEvidenceRoot resultType result := by
  cases derivation with
  | run _ _ _ _ hresult =>
      exact buildResultRoot_sound hresult

/--
Certified projection soundness: success supplies the complete staged
derivation and a result whose root is fixed by the normalized signature.
-/
theorem projectSignature_sound
    {observable : Observability}
    (signature : ProjectionSignature observable)
    {childEvidence : List Evidence} {result : Evidence}
    (hproject : projectSignature signature childEvidence = some result) :
    ProjectionDerivation observable signature.fieldTypes
        signature.resultType childEvidence result ∧
      ResultEvidenceRoot signature.resultType result := by
  have derivation :=
    (projectSignature_eq_some_iff signature).mp hproject
  exact ⟨derivation, derivation.resultRoot⟩

/-- Executable projection has at most one result. -/
theorem project_deterministic
    {observable : Observability}
    {fieldTypes : List Ty}
    {resultType : Ty}
    {childEvidence : List Evidence}
    {left right : Evidence}
    (hleft : project observable fieldTypes resultType childEvidence = some left)
    (hright : project observable fieldTypes resultType childEvidence = some right) :
    left = right := by
  rw [hleft] at hright
  exact Option.some.inj hright

/-- Unseen child evidence contributes no assignment for any field type. -/
@[simp] theorem collectAssignments_unseen
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (fieldType : Ty) :
    collectAssignments observable resultVariables fieldType .unseen = some [] := by
  cases fieldType <;> rfl

/--
An ordinary target substitution cannot seed evidence when the corresponding
child evidence is unseen, even if substitution reveals new type structure.
-/
theorem target_substitution_does_not_seed
    (observable : Observability)
    (resultVariables : List TypePM.TyVar)
    (targetSubst : TySubst)
    (fieldType : Ty) :
    collectAssignments observable resultVariables
      (fieldType.applyTarget targetSubst) .unseen = some [] :=
  collectAssignments_unseen observable resultVariables _

/--
With an unseen child, substituting its ordinary field type cannot change the
projected result.
-/
theorem project_single_unseen_applyTarget
    (observable : Observability)
    (targetSubst : TySubst)
    (fieldType resultType : Ty) :
    project observable [fieldType.applyTarget targetSubst]
        resultType [.unseen] =
      project observable [fieldType] resultType [.unseen] := by
  simp [project, collectAssignmentsList]

/-! ## Executable examples -/

private def swapObservability : Observability :=
  fun name => if name = "Swap" then some [true, true] else none

private def swapSignature : ProjectionSignature swapObservability where
  fieldTypes := [.var 0, .var 1]
  resultType := .data "Swap" [.var 1, .var 0]
  resultRoot := ResolvedResultRoot.data (mask := [true, true]) (by
    simp [swapObservability]) rfl

private def repeatedObservability : Observability :=
  fun name => if name = "Repeated" then some [true, true] else none

private def repeatedSignature :
    ProjectionSignature repeatedObservability where
  fieldTypes := [.var 0]
  resultType := .data "Repeated" [.var 0, .var 0]
  resultRoot := ResolvedResultRoot.data (mask := [true, true]) (by
    simp [repeatedObservability]) rfl

private def wrapObservability : Observability :=
  fun name =>
    if name = "Wrap" then some [true]
    else if name = "List" then some [true]
    else none

example :
    project swapObservability
      [.var 0, .var 1]
      (.data "Swap" [.var 1, .var 0])
      [.known (.var 10), .known (.var 11)] =
    some (.con "Swap" [.known (.var 11), .known (.var 10)]) := by
  rfl

example :
    projectSignature swapSignature
      [.known (.var 10), .known (.var 11)] =
    projectSignature
      (swapSignature.replaceFields [.var 1, .var 0])
      [.known (.var 11), .known (.var 10)] := by
  apply projectSignature_simultaneous_perm
    (signature := swapSignature)
    (left :=
      [(.var 0, .known (.var 10)),
        (.var 1, .known (.var 11))])
    (right :=
      [(.var 1, .known (.var 11)),
        (.var 0, .known (.var 10))])
  · rfl
  · exact List.Perm.swap _ _ []

example :
    projectSignature repeatedSignature [.known (.var 10)] =
      some
        (.con "Repeated"
          [.known (.var 10), .known (.var 10)]) := by
  simp [projectSignature, repeatedSignature, projectPaired,
    pairFields, relevantVars, relevantVarsMasked,
    targetVars, targetVarsList,
    collectAssignments,
    collectFieldAssignments, canonicalAssignments,
    evidenceContributions, Shape.mergeAll,
    buildResultRoot, buildResultSlot,
    buildResultSlotsMasked, buildResultTemplate,
    hasAssignment, lookupAssignment, repeatedObservability]

example :
    project wrapObservability
      [.data "List" [.var 0]]
      (.data "Wrap" [.var 0])
      [.con "List" [.known (.var 10)]] =
    some (.con "Wrap" [.known (.var 10)]) := by
  rfl

example :
    project wrapObservability
      [.data "List" [.var 0]]
      (.data "Wrap" [.var 0])
      [.known .none] =
    none := by
  rfl

example :
    project wrapObservability
      [.data "List" [.var 0]]
      (.data "Wrap" [.var 0])
      [.unseen] =
    some (.con "Wrap" [.unseen]) := by
  rfl

example :
    project wrapObservability
      [.var 0, .var 0]
      (.data "Wrap" [.var 0])
      [.known (.var 10), .known (.var 10)] =
    some (.con "Wrap" [.known (.var 10)]) := by
  rfl

example :
    project wrapObservability
      [.var 0, .var 0]
      (.data "Wrap" [.var 0])
      [.known (.var 10), .known (.var 11)] =
    none := by
  rfl

example :
    project wrapObservability
      [.var 0]
      (.data "Wrap" [.prod [.var 0, .prod [.int]]])
      [.known (.var 10)] =
    some
      (.con "Wrap"
        [.prod [.known (.var 10), .known .none]]) := by
  rfl

end Projection
end TypePM.P2
