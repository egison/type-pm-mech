import TypePM.Syntax

/-!
# Normalized-input canonicalization boundary

This module models the small, syntactic canonicalization allowlist used by the
non-CAS two-sorted core.  Its input is an already validated and frozen table of
fully-expanded nullary transparent aliases.  Normalization:

* expands a registered alias only at a nullary type head;
* recursively normalizes ordinary type arguments;
* never rewrites an existing matcher or slot capability; and
* contains no semantic equality, CAS conversion, coercion, reshape, or Tensor
  flattening rule.

Raw alias-graph validation, cycle detection, arity checking, name collision
checking, and construction of a `FrozenAliases` certificate are deliberately
outside this module.  They must happen before type inference and signature
registration.
-/

namespace TypePM
namespace Canonical

/-- One validated nullary transparent alias and its fully-expanded range. -/
structure AliasEntry where
  name  : String
  range : Ty
deriving Repr

/-- A frozen list of nullary transparent aliases. -/
abbrev AliasEnv := List AliasEntry

/-- Lookup uses the frozen order; `FrozenAliases` separately requires names to be unique. -/
def AliasEnv.lookup? : AliasEnv → String → Option Ty
  | [], _ => none
  | entry :: rest, name =>
      if entry.name = name then some entry.range
      else AliasEnv.lookup? rest name

/-- No two entries in an alias table have the same name. -/
def AliasEnv.NamesUnique : AliasEnv → Prop
  | [] => True
  | entry :: rest =>
      (∀ other ∈ rest, entry.name ≠ other.name) ∧
      AliasEnv.NamesUnique rest

mutual

/-- A capability is closed when it contains no inference variables or skolems. -/
def Cap.Closed : Cap → Prop
  | .none       => True
  | .var _      => False
  | .skolem _   => False
  | .con _ caps => Cap.ClosedList caps
  | .prod caps  => Cap.ClosedList caps

/-- List form of `Cap.Closed`. -/
def Cap.ClosedList : List Cap → Prop
  | []          => True
  | cap :: caps => Cap.Closed cap ∧ Cap.ClosedList caps

end

mutual

/-- A type is closed in both its ordinary and embedded capability variables. -/
def Ty.Closed : Ty → Prop
  | .var _        => False
  | .skolem _     => False
  | .unit         => True
  | .int          => True
  | .bool         => True
  | .data _ tys   => Ty.ClosedList tys
  | .prod tys     => Ty.ClosedList tys
  | .fn dom cod   => Ty.Closed dom ∧ Ty.Closed cod
  | .matcher c τ  => Cap.Closed c ∧ Ty.Closed τ
  | .slot c τ     => Cap.Closed c ∧ Ty.Closed τ

/-- List form of `Ty.Closed`. -/
def Ty.ClosedList : List Ty → Prop
  | []        => True
  | τ :: tys  => Ty.Closed τ ∧ Ty.ClosedList tys

end

mutual

/--
A capability is canonical relative to an alias table when no alias name occurs
as a capability former.

Capabilities are never normalized by `reprNF`; this predicate is therefore a
required property of frozen alias ranges and other normalized inputs.
-/
def Cap.AliasFree (aliases : AliasEnv) : Cap → Prop
  | .none       => True
  | .var _      => True
  | .skolem _   => True
  | .con name caps =>
      aliases.lookup? name = none ∧ Cap.AliasFreeList aliases caps
  | .prod caps  => Cap.AliasFreeList aliases caps

/-- List form of `Cap.AliasFree`. -/
def Cap.AliasFreeList (aliases : AliasEnv) : List Cap → Prop
  | []          => True
  | cap :: caps =>
      Cap.AliasFree aliases cap ∧ Cap.AliasFreeList aliases caps

end

mutual

/--
A type is canonical relative to an alias table when no registered alias remains
at any type or capability head.

The condition excludes malformed non-nullary uses of nullary aliases as well as
unexpanded nullary heads.
-/
def Ty.AliasFree (aliases : AliasEnv) : Ty → Prop
  | .var _        => True
  | .skolem _     => True
  | .unit         => True
  | .int          => True
  | .bool         => True
  | .data name tys =>
      aliases.lookup? name = none ∧ Ty.AliasFreeList aliases tys
  | .prod tys     => Ty.AliasFreeList aliases tys
  | .fn dom cod   =>
      Ty.AliasFree aliases dom ∧ Ty.AliasFree aliases cod
  | .matcher c τ  =>
      Cap.AliasFree aliases c ∧ Ty.AliasFree aliases τ
  | .slot c τ     =>
      Cap.AliasFree aliases c ∧ Ty.AliasFree aliases τ

/-- List form of `Ty.AliasFree`. -/
def Ty.AliasFreeList (aliases : AliasEnv) : List Ty → Prop
  | []        => True
  | τ :: tys  =>
      Ty.AliasFree aliases τ ∧ Ty.AliasFreeList aliases tys

end

mutual

/--
Normalize a type structurally.

The nullary alias case returns its already canonical range without recursively
normalizing that range.  This makes termination structural in the input type;
the `FrozenAliases` certificate supplies the missing canonical-range fact.
-/
def reprNF (aliases : AliasEnv) : Ty → Ty
  | .var a        => .var a
  | .skolem a     => .skolem a
  | .unit         => .unit
  | .int          => .int
  | .bool         => .bool
  | .data name [] =>
      match aliases.lookup? name with
      | some range => range
      | none       => .data name []
  | .data name (argument :: arguments) =>
      .data name
        (reprNF aliases argument :: reprNFList aliases arguments)
  | .prod tys     => .prod (reprNFList aliases tys)
  | .fn dom cod   => .fn (reprNF aliases dom) (reprNF aliases cod)
  | .matcher c τ  => .matcher c (reprNF aliases τ)
  | .slot c τ     => .slot c (reprNF aliases τ)

/-- List form of `reprNF`. -/
def reprNFList (aliases : AliasEnv) : List Ty → List Ty
  | []        => []
  | τ :: tys  => reprNF aliases τ :: reprNFList aliases tys

end

/--
Certificate expected at the normalized-input boundary.

The table constructor/validator is outside this module.  In particular, these
fields are not an algorithm for accepting a raw graph: callers must first
reject cycles, unknown heads, malformed applications, and name collisions, then
provide closed, fully-expanded ranges.
-/
structure FrozenAliases (aliases : AliasEnv) : Prop where
  uniqueNames : aliases.NamesUnique
  rangeClosed :
    ∀ name range, aliases.lookup? name = some range → Ty.Closed range
  rangeCanonical :
    ∀ name range, aliases.lookup? name = some range →
      Ty.AliasFree aliases range

mutual

/-- Canonical types are fixed points of structural normalization. -/
theorem reprNF_eq_of_aliasFree (aliases : AliasEnv) :
    ∀ τ : Ty, Ty.AliasFree aliases τ → reprNF aliases τ = τ
  | .var _, _ => rfl
  | .skolem _, _ => rfl
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .data name [], hfree => by
      simp [Ty.AliasFree] at hfree
      simp [reprNF, hfree]
  | .data name (argument :: arguments), hfree => by
      simp only [Ty.AliasFree] at hfree
      simp [reprNF,
        reprNF_eq_of_aliasFree aliases argument hfree.2.1,
        reprNFList_eq_of_aliasFree aliases arguments hfree.2.2]
  | .prod tys, hfree => by
      simp only [Ty.AliasFree] at hfree
      simp [reprNF, reprNFList_eq_of_aliasFree aliases tys hfree]
  | .fn dom cod, hfree => by
      simp only [Ty.AliasFree] at hfree
      simp [reprNF,
        reprNF_eq_of_aliasFree aliases dom hfree.1,
        reprNF_eq_of_aliasFree aliases cod hfree.2]
  | .matcher cap target, hfree => by
      simp only [Ty.AliasFree] at hfree
      simp [reprNF, reprNF_eq_of_aliasFree aliases target hfree.2]
  | .slot cap target, hfree => by
      simp only [Ty.AliasFree] at hfree
      simp [reprNF, reprNF_eq_of_aliasFree aliases target hfree.2]

/-- List form of `reprNF_eq_of_aliasFree`. -/
theorem reprNFList_eq_of_aliasFree (aliases : AliasEnv) :
    ∀ tys : List Ty,
      Ty.AliasFreeList aliases tys → reprNFList aliases tys = tys
  | [], _ => rfl
  | τ :: tys, hfree => by
      simp only [Ty.AliasFreeList] at hfree
      simp [reprNFList,
        reprNF_eq_of_aliasFree aliases τ hfree.1,
        reprNFList_eq_of_aliasFree aliases tys hfree.2]

end

mutual

/-- Normalization is idempotent for a validated frozen alias table. -/
theorem reprNF_idempotent {aliases : AliasEnv}
    (frozen : FrozenAliases aliases) :
    ∀ τ : Ty, reprNF aliases (reprNF aliases τ) = reprNF aliases τ
  | .var _ => rfl
  | .skolem _ => rfl
  | .unit => rfl
  | .int => rfl
  | .bool => rfl
  | .data name [] => by
      cases hlookup : aliases.lookup? name with
      | none =>
          simp [reprNF, hlookup]
      | some range =>
          have hcanonical : Ty.AliasFree aliases range :=
            frozen.rangeCanonical name range hlookup
          simp [reprNF, hlookup,
            reprNF_eq_of_aliasFree aliases range hcanonical]
  | .data name (argument :: arguments) => by
      simp [reprNF,
        reprNF_idempotent frozen argument,
        reprNFList_idempotent frozen arguments]
  | .prod tys => by
      simp [reprNF, reprNFList_idempotent frozen tys]
  | .fn dom cod => by
      simp [reprNF,
        reprNF_idempotent frozen dom,
        reprNF_idempotent frozen cod]
  | .matcher cap target => by
      simp [reprNF, reprNF_idempotent frozen target]
  | .slot cap target => by
      simp [reprNF, reprNF_idempotent frozen target]

/-- List form of `reprNF_idempotent`. -/
theorem reprNFList_idempotent {aliases : AliasEnv}
    (frozen : FrozenAliases aliases) :
    ∀ tys : List Ty,
      reprNFList aliases (reprNFList aliases tys) =
        reprNFList aliases tys
  | [] => rfl
  | τ :: tys => by
      simp [reprNFList,
        reprNF_idempotent frozen τ,
        reprNFList_idempotent frozen tys]

end

/--
A registered nullary alias expands to its certified closed, canonical range.
-/
theorem FrozenAliases.alias_expansion
    {aliases : AliasEnv} (frozen : FrozenAliases aliases)
    {name : String} {range : Ty}
    (hlookup : aliases.lookup? name = some range) :
    reprNF aliases (.data name []) = range ∧
      Ty.Closed range ∧ Ty.AliasFree aliases range := by
  exact ⟨by simp [reprNF, hlookup],
    frozen.rangeClosed name range hlookup,
    frozen.rangeCanonical name range hlookup⟩

/--
A non-nullary application is never expanded as a nullary alias.  Its arguments
are still normalized structurally so that a later arity checker can reject the
unchanged alias head.
-/
theorem reprNF_nonNullary_alias_application
    (aliases : AliasEnv) (name : String)
    (argument : Ty) (arguments : List Ty) :
    reprNF aliases (.data name (argument :: arguments)) =
      .data name
        (reprNF aliases argument :: reprNFList aliases arguments) :=
  rfl

/-- Structural normalization never changes an existing matcher capability. -/
theorem reprNF_matcher_capability
    (aliases : AliasEnv) (cap : Cap) (target : Ty) :
    reprNF aliases (.matcher cap target) =
      .matcher cap (reprNF aliases target) :=
  rfl

/-- Structural normalization never changes an existing slot capability. -/
theorem reprNF_slot_capability
    (aliases : AliasEnv) (cap : Cap) (target : Ty) :
    reprNF aliases (.slot cap target) =
      .slot cap (reprNF aliases target) :=
  rfl

/--
Regression: semantic Tensor flattening is not a `reprNF` rule.

Both Tensor applications are non-nullary, so the nested structure is retained.
-/
theorem reprNF_does_not_flatten_tensor (aliases : AliasEnv) :
    reprNF aliases
        (.data "Tensor" [.data "Tensor" [.int]]) =
      .data "Tensor" [.data "Tensor" [.int]] :=
  rfl

/--
Regression: no CAS ground equivalence is built into canonicalization.

With no explicitly frozen transparent alias, distinct nominal CAS heads remain
distinct.
-/
theorem reprNF_has_no_cas_ground_equivalence :
    reprNF [] (.data "Factor" []) ≠
      reprNF [] (.data "Term" []) := by
  decide

end Canonical
end TypePM
