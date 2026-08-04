import TypePM.P2.Shape

/-!
# P2 direct-self recursion evidence fold

This module is a standalone evidence fold for the intended singleton
direct-self fragment.  A local recursive matcher may receive genuine known
evidence, and may refer directly to its own name.  References to any other name
are rejected rather than interpreted as alias, mutual-recursion, transform, or
higher-order producer flow.  The source bridge that proves which expressions
may create a `known` input, and that connects Egison's direct-self
classification to this fold, is not part of this module.

Consumer demand, expected result types, and annotations are deliberately absent
from `LocalEquation`.  They are deferred checks, not sources of ShapeCap
evidence.
-/

namespace TypePM.P2
namespace Recursion

open Shape

/--
An evidence source visible while checking one SCC-local recursive binding.

`known` is evidence that the caller has already justified independently of the
current recursive assumption.  This module does not itself prove provenance.
`reference` records a name-level producer reference.  The fold accepts it only
when it names the binding currently being solved.
-/
inductive Source where
  | known     : Evidence → Source
  | reference : String → Source
deriving Repr

/--
The local equation for one direct-self binding.

There are intentionally no fields for consumer demand, result annotations, or
general producer paths.
-/
structure LocalEquation where
  binder  : String
  sources : List Source
deriving Repr

/--
Fold direct-self sources into an evidence accumulator.

Known evidence is combined by exact merge.  A direct self-reference leaves
the current least approximation unchanged.  Every other reference fails
closed.  Recursion is structural on the finite source list, so termination is
checked by Lean's definition elaborator.
-/
def solveSources (binder : String) :
    Evidence → List Source → Option Evidence
  | accumulated, [] => some accumulated
  | accumulated, .known evidence :: rest =>
      match Shape.merge accumulated evidence with
      | some merged => solveSources binder merged rest
      | none => none
  | accumulated, .reference name :: rest =>
      if name = binder then
        solveSources binder accumulated rest
      else
        none

/--
Solve a direct-self local equation from the distinguished bottom marker
`unseen`.

The result remains partial evidence; observability-aware finalization is a
separate operation.  This executable fold is deterministic.  A general
producer-flow solver and its evidence order are outside the singleton
direct-self core formalized here.
-/
def solve (equation : LocalEquation) : Option Evidence :=
  solveSources equation.binder .unseen equation.sources

/-- Relational view of the deterministic solver. -/
def Solves (equation : LocalEquation) (evidence : Evidence) : Prop :=
  solve equation = some evidence

/--
The relational view is deterministic because it is defined by the terminating
solver function.
-/
theorem solves_deterministic {equation : LocalEquation}
    {left right : Evidence}
    (hleft : Solves equation left) (hright : Solves equation right) :
    left = right := by
  have hsome : some left = some right := hleft.symm.trans hright
  exact Option.some.inj hsome

/-- A finite sequence containing only direct references to one binder. -/
def selfSources (binder : String) : Nat → List Source
  | 0 => []
  | n + 1 => .reference binder :: selfSources binder n

/-- Direct-self references preserve every current evidence approximation. -/
@[simp] theorem solveSources_selfSources
    (binder : String) (accumulated : Evidence) :
    ∀ count,
      solveSources binder accumulated (selfSources binder count) =
        some accumulated
  | 0 => rfl
  | count + 1 => by
      simp [selfSources, solveSources,
        solveSources_selfSources binder accumulated count]

/--
A prefix consisting only of direct-self references has no effect on later
genuine evidence.
-/
theorem solveSources_selfPrefix
    (binder : String) (accumulated : Evidence) :
    ∀ count rest,
      solveSources binder accumulated
          (selfSources binder count ++ rest) =
        solveSources binder accumulated rest
  | 0, rest => rfl
  | count + 1, rest => by
      simp [selfSources, solveSources,
        solveSources_selfPrefix binder accumulated count rest]

/-- A nonempty, seedless direct-self cycle. -/
def seedlessCycle (binder : String) (extraReferences : Nat) :
    LocalEquation :=
  ⟨binder, selfSources binder (extraReferences + 1)⟩

/--
The direct-self fold leaves a seedless pure self cycle at `unseen`;
self-reference does not manufacture a capability.
-/
@[simp] theorem solve_seedlessCycle
    (binder : String) (extraReferences : Nat) :
    solve (seedlessCycle binder extraReferences) = some .unseen := by
  simp [solve, seedlessCycle]

/--
A local direct-self equation with one genuine external seed, surrounded by any
number of self references.
-/
def seededCycle (binder : String) (before after : Nat)
    (seed : Evidence) : LocalEquation :=
  ⟨binder,
    selfSources binder before ++
      .known seed :: selfSources binder after⟩

/--
Genuine external evidence propagates through a direct-self knot unchanged.
-/
@[simp] theorem solve_seededCycle
    (binder : String) (before after : Nat) (seed : Evidence) :
    solve (seededCycle binder before after seed) = some seed := by
  simp [solve, seededCycle, solveSources_selfPrefix, solveSources,
    Shape.merge_unseen_left]

/--
An unresolved reference to another name is rejected.  This is the explicit
fail-closed boundary for aliases, mutual recursion, and general producer flow.
-/
theorem solveSources_nonSelf_reference
    {binder other : String} (h : other ≠ binder)
    (accumulated : Evidence) (rest : List Source) :
    solveSources binder accumulated (.reference other :: rest) = none := by
  simp [solveSources, h]

/-- Equation-level form of `solveSources_nonSelf_reference`. -/
theorem solve_nonSelf_reference
    {binder other : String} (h : other ≠ binder) :
    solve ⟨binder, [.reference other]⟩ = none := by
  simp [solve, solveSources, h]

/--
Two genuine evidence sources separated by a self-reference are combined by
exact merge and by nothing else.
-/
theorem solve_two_known_with_self
    (binder : String) (left right : Evidence) :
    solve
        ⟨binder,
          [.known left, .reference binder, .known right]⟩ =
      Shape.merge left right := by
  cases hmerge : Shape.merge left right <;>
    simp [solve, solveSources, Shape.merge_unseen_left, hmerge]

/-- Any exact-merge incompatibility rejects the recursive equation. -/
theorem solve_known_mismatch
    {binder : String} {left right : Evidence}
    (hmismatch : Shape.merge left right = none) :
    solve
        ⟨binder,
          [.known left, .reference binder, .known right]⟩ =
      none := by
  rw [solve_two_known_with_self, hmismatch]

/-- Distinct known capability variables cannot be reconciled by recursion. -/
theorem solve_known_variable_mismatch
    {binder : String} {left right : CapVar} (h : left ≠ right) :
    solve
        ⟨binder,
          [.known (.known (.var left)),
            .reference binder,
            .known (.known (.var right))]⟩ =
      none := by
  apply solve_known_mismatch
  exact Shape.merge_known_vars_ne h

/-- Distinct known constructor heads cannot be reconciled by recursion. -/
theorem solve_known_constructor_mismatch
    {binder leftName rightName : String}
    {leftChildren rightChildren : List Evidence}
    (h : leftName ≠ rightName) :
    solve
        ⟨binder,
          [.known (.con leftName leftChildren),
            .reference binder,
            .known (.con rightName rightChildren)]⟩ =
      none := by
  apply solve_known_mismatch
  exact Shape.merge_constructor_names_ne h

/--
The fold result is wholly determined by its binder and evidence sources.

This theorem exposes the interface boundary: no expected capability, target
type, annotation, or consumer demand is consulted.  It is an interface fact,
not a provenance theorem for `.known` inputs.
-/
theorem solve_from_sources_only (equation : LocalEquation) :
    solve equation =
      solveSources equation.binder .unseen equation.sources :=
  rfl

end Recursion
end TypePM.P2
