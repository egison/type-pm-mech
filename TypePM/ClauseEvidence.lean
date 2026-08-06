import TypePM.Term
import TypePM.Shape
import TypePM.Projection

/-!
# Concrete matcher-clause evidence and coverage

This module is the type-independent concrete boundary between matcher clauses
and ShapeCap inference.  A frozen matcher signature supplies only immutable
observability, certified pattern-constructor projections, and the finite list
of general pattern constructors belonging to each canonical former.

Clause evidence is computed solely from a primitive-pattern pattern and the
capabilities of its holes.  In particular, no matcher target, expected type,
consumer demand, or annotation is an input to the checker.
-/

namespace TypePM

/-! ## Frozen matcher signatures -/

/-- A pattern-constructor name paired with its general-clause arity. -/
abbrev GeneralCtor := String × Nat

/--
The frozen, non-CAS matcher-signature fragment used by clause evidence and
coverage.  Every pattern-constructor entry contains a certified, normalized
projection signature.  `constructorsByFormer` is the finite conservative
coverage index; its rows are not defined as a recomputation of that table.
-/
structure FrozenMatcherSig where
  observability : Shape.Observability
  patternConstructors :
    List (String × Projection.ProjectionSignature observability)
  constructorsByFormer : List (String × List GeneralCtor)

/-- Deterministic lookup of a certified pattern-constructor signature. -/
def FrozenMatcherSig.findPatternConstructor?
    (signature : FrozenMatcherSig) (name : String) :
    Option (Projection.ProjectionSignature signature.observability) :=
  (List.find? (fun entry => entry.1 == name)
    signature.patternConstructors).map (·.2)

/-- Deterministic lookup of the general constructors of a canonical former. -/
def FrozenMatcherSig.constructorsFor?
    (signature : FrozenMatcherSig) (former : String) :
    Option (List GeneralCtor) :=
  (List.find? (fun entry => entry.1 == former)
    signature.constructorsByFormer).map (·.2)

/-! ## Hole counting -/

mutual

/-- Number of matcher holes in a primitive-pattern pattern. -/
def PPat.holeCount : PPat → Nat
  | .hole => 1
  | .wild => 0
  | .pval _ => 0
  | .ctor _ patterns => PPat.holeCountList patterns
  | .tuple patterns => PPat.holeCountList patterns

/-- Number of matcher holes in a list of primitive-pattern patterns. -/
def PPat.holeCountList : List PPat → Nat
  | [] => 0
  | pattern :: patterns =>
      pattern.holeCount + PPat.holeCountList patterns

end

/-! ## Concrete clause evidence -/

mutual

/--
Consume hole capabilities from left to right while constructing evidence.

`atRoot` distinguishes the root bare hole, whose evidence is `unseen`, from
a hole below a constructor or tuple, whose capability is embedded with
`Shape.ofCap`.  The unconsumed suffix is returned explicitly.
-/
def clauseEvidenceGo
    (signature : FrozenMatcherSig) (atRoot : Bool) :
    PPat → List Cap → Option (Shape.Evidence × List Cap)
  | .hole, [] =>
      none
  | .hole, capability :: capabilities =>
      some
        (if atRoot then .unseen else Shape.ofCap capability,
          capabilities)
  | .wild, capabilities =>
      some (.unseen, capabilities)
  | .pval _, capabilities =>
      some (.unseen, capabilities)
  | .ctor name patterns, capabilities => do
      let constructor ← signature.findPatternConstructor? name
      let (children, remaining) ←
        clauseEvidenceListGo signature patterns capabilities
      let evidence ←
        Projection.projectClauseSignature constructor children
      pure (evidence, remaining)
  | .tuple patterns, capabilities => do
      let (children, remaining) ←
        clauseEvidenceListGo signature patterns capabilities
      pure (.prod children, remaining)

/-- List traversal for `clauseEvidenceGo`. -/
def clauseEvidenceListGo
    (signature : FrozenMatcherSig) :
    List PPat → List Cap → Option (List Shape.Evidence × List Cap)
  | [], capabilities =>
      some ([], capabilities)
  | pattern :: patterns, capabilities => do
      let (head, afterHead) ←
        clauseEvidenceGo signature false pattern capabilities
      let (tail, remaining) ←
        clauseEvidenceListGo signature patterns afterHead
      pure (head :: tail, remaining)

end


/-- Accept only a successful evidence run that consumed every capability. -/
def finishClauseEvidence :
    Option (Shape.Evidence × List Cap) → Option Shape.Evidence
  | some (evidence, []) => some evidence
  | _ => none

/--
Concrete evidence for one primitive-pattern pattern.

The explicit hole-count check is redundant with a successful complete worker
run, but makes the exact clause/slot arity boundary manifest and yields a
stable theorem for the source checker.
-/
def clauseEvidence
    (signature : FrozenMatcherSig) (pattern : PPat)
    (holeCapabilities : List Cap) : Option Shape.Evidence :=
  if pattern.coreOrderCheck then
    if holeCapabilities.length = pattern.holeCount then
      finishClauseEvidence
        (clauseEvidenceGo signature true pattern holeCapabilities)
    else
      none
  else
    none

/-- Successful clause evidence certifies the formal core's PP order boundary. -/
theorem clauseEvidence_coreOrder
    {signature : FrozenMatcherSig} {pattern : PPat}
    {holeCapabilities : List Cap} {evidence : Shape.Evidence}
    (hcheck :
      clauseEvidence signature pattern holeCapabilities = some evidence) :
    PPatCoreOrder pattern := by
  unfold clauseEvidence at hcheck
  split at hcheck
  · exact PPat.coreOrderCheck_sound (by assumption)
  · contradiction

/-- A successful deterministic checker cannot return two evidence trees. -/
theorem clauseEvidence_deterministic
    {signature : FrozenMatcherSig} {pattern : PPat}
    {holeCapabilities : List Cap} {left right : Shape.Evidence}
    (hleft : clauseEvidence signature pattern holeCapabilities = some left)
    (hright : clauseEvidence signature pattern holeCapabilities = some right) :
    left = right :=
  Option.some.inj (hleft.symm.trans hright)

/-- Successful evidence extraction has exactly one capability per hole. -/
theorem clauseEvidence_holeCount
    {signature : FrozenMatcherSig} {pattern : PPat}
    {holeCapabilities : List Cap} {evidence : Shape.Evidence}
    (hcheck :
      clauseEvidence signature pattern holeCapabilities = some evidence) :
    holeCapabilities.length = pattern.holeCount := by
  unfold clauseEvidence at hcheck
  split at hcheck
  · split at hcheck
    · assumption
    · contradiction
  · contradiction

/-- Inversion for the all-capabilities-consumed boundary. -/
theorem finishClauseEvidence_eq_some
    {run : Option (Shape.Evidence × List Cap)}
    {evidence : Shape.Evidence}
    (hfinish : finishClauseEvidence run = some evidence) :
    run = some (evidence, []) := by
  cases run with
  | none => simp [finishClauseEvidence] at hfinish
  | some result =>
      cases result with
      | mk found remaining =>
          cases remaining with
          | nil =>
              simp [finishClauseEvidence] at hfinish
              subst found
              rfl
          | cons capability capabilities =>
              simp [finishClauseEvidence] at hfinish

/-- A successful public check is a worker run with an empty remainder. -/
theorem clauseEvidence_consumesAll
    {signature : FrozenMatcherSig} {pattern : PPat}
    {holeCapabilities : List Cap} {evidence : Shape.Evidence}
    (hcheck :
      clauseEvidence signature pattern holeCapabilities = some evidence) :
    clauseEvidenceGo signature true pattern holeCapabilities =
      some (evidence, []) := by
  unfold clauseEvidence at hcheck
  split at hcheck
  · split at hcheck
    · exact finishClauseEvidence_eq_some hcheck
    · contradiction
  · contradiction

/-- A checker parameterized by a target is non-seeding when targets are inert. -/
def TargetNonseeding
    (checker : Ty → Option Shape.Evidence) : Prop :=
  ∀ leftTarget rightTarget, checker leftTarget = checker rightTarget

/--
Clause evidence is target-nonseeding: varying an external target cannot alter
the result because the target is not an input to `clauseEvidence`.
-/
theorem clauseEvidence_targetNonseeding
    (signature : FrozenMatcherSig) (pattern : PPat)
    (holeCapabilities : List Cap) :
    TargetNonseeding
      (fun _target => clauseEvidence signature pattern holeCapabilities) := by
  intro _ _
  rfl

/-! ## Concrete coverage and matcher well-formedness -/

/-- The general constructor pattern `c $ ... $`. -/
def generalPP (name : String) (arity : Nat) : PPat :=
  .ctor name (List.replicate arity .hole)

/-- The general tuple pattern `($, ..., $)`. -/
def generalTuplePP (arity : Nat) : PPat :=
  .tuple (List.replicate arity .hole)

/-- An actual clause with exactly the requested primitive-pattern pattern. -/
def HasClausePP (clauses : List Clause) (pattern : PPat) : Prop :=
  ∃ clause ∈ clauses, clause.pp = pattern

/--
Concrete root coverage from the frozen pattern signature.

Coverage is deliberately shallow.  Constructor refinements do not count as
general clauses, and coverage does not recurse into child capabilities.
-/
def CoverageOK
    (signature : FrozenMatcherSig) (clauses : List Clause) : Cap → Prop
  | .any =>
      True
  | .con former _ =>
      ∃ constructors,
        signature.constructorsFor? former = some constructors ∧
        ∀ constructor ∈ constructors,
          HasClausePP clauses (generalPP constructor.1 constructor.2)
  | .prod components =>
      HasClausePP clauses (generalTuplePP components.length)
  | .var _ =>
      False
  | .skolem _ =>
      False

/--
The unique bare-hole catch-all is the final clause and has one variable arm,
as required by the TeX `CatchAllLast` predicate.
-/
def CatchAllLast (clauses : List Clause) : Prop :=
  ∃ before next name body,
    clauses =
      before ++ [.mk .hole next [.mk (.var name) body]] ∧
    ∀ clause ∈ before, clause.pp ≠ .hole

/-- Primitive-pattern binders are pairwise distinct in every actual clause. -/
def PPBindNodup (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, clause.pp.bindVars.Nodup

/--
Every arm's data-pattern binders are pairwise distinct and disjoint from the
primitive-pattern binders of their actual clause.
-/
def ArmBindNodup (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, ∀ arm ∈ clause.arms,
    arm.pat.bindVars.Nodup ∧
      ∀ name ∈ arm.pat.bindVars, name ∉ clause.pp.bindVars

/-! ## Dispatch before the catch-all -/

/-- A requested general clause occurs strictly before the final catch-all. -/
def GeneralBeforeCatchAll
    (clauses : List Clause) (pattern : PPat) : Prop :=
  ∃ before next name body,
    clauses =
      before ++ [.mk .hole next [.mk (.var name) body]] ∧
    HasClausePP before pattern

/--
Every general clause required by a capability can be reached before the final
bare-hole catch-all.
-/
def DispatchOK
    (signature : FrozenMatcherSig) (clauses : List Clause) : Cap → Prop
  | .any =>
      True
  | .con former _ =>
      ∃ constructors,
        signature.constructorsFor? former = some constructors ∧
        ∀ constructor ∈ constructors,
          GeneralBeforeCatchAll clauses
            (generalPP constructor.1 constructor.2)
  | .prod components =>
      GeneralBeforeCatchAll clauses (generalTuplePP components.length)
  | .var _ =>
      False
  | .skolem _ =>
      False

@[simp] theorem generalPP_ne_hole (name : String) (arity : Nat) :
    generalPP name arity ≠ .hole := by
  intro equality
  cases equality

@[simp] theorem generalTuplePP_ne_hole (arity : Nat) :
    generalTuplePP arity ≠ .hole := by
  intro equality
  cases equality

/-- Any non-hole covered clause lies in the prefix selected by `CatchAllLast`. -/
theorem hasClausePP_before_catchAll
    {clauses : List Clause} {pattern : PPat}
    (hcatch : CatchAllLast clauses)
    (hne : pattern ≠ .hole)
    (hclause : HasClausePP clauses pattern) :
    GeneralBeforeCatchAll clauses pattern := by
  rcases hcatch with ⟨before, next, name, body, hclauses, _⟩
  rcases hclause with ⟨clause, hmem, hpp⟩
  refine ⟨before, next, name, body, hclauses, ?_⟩
  rw [hclauses] at hmem
  have location :
      clause ∈ before ∨
        clause = Clause.mk .hole next [.mk (.var name) body] := by
    simpa using hmem
  cases location with
  | inl hbefore =>
      exact ⟨clause, hbefore, hpp⟩
  | inr hfinal =>
      subst clause
      exact (hne hpp.symm).elim

/-- Coverage plus final catch-all ordering yields concrete dispatchability. -/
theorem coverageOK_catchAllLast_dispatchOK
    (signature : FrozenMatcherSig) (clauses : List Clause) (capability : Cap)
    (hcoverage : CoverageOK signature clauses capability)
    (hcatch : CatchAllLast clauses) :
    DispatchOK signature clauses capability := by
  cases capability with
  | any =>
      trivial
  | var capVar =>
      contradiction
  | skolem name =>
      contradiction
  | con former children =>
      rcases hcoverage with ⟨constructors, hlookup, hconstructors⟩
      refine ⟨constructors, hlookup, ?_⟩
      intro constructor hmem
      exact hasClausePP_before_catchAll hcatch
        (generalPP_ne_hole constructor.1 constructor.2)
        (hconstructors constructor hmem)
  | prod components =>
      exact hasClausePP_before_catchAll hcatch
        (generalTuplePP_ne_hole components.length) hcoverage

end TypePM
