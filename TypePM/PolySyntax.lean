import TypePM.Substitution

/-!
# Capture-free polymorphic payloads

`PolyCap` and `PolyTy` are the scheme-only boundary between source
polymorphism and the ordinary solver syntax.  Bound occurrences are `Fin`
indices, while free occurrences retain the existing unification metavariable
types.  Opening is the only operation that removes bound occurrences and
returns an ordinary `Cap`/`Ty`; ambient substitution only rewrites `meta`
nodes and therefore cannot capture a bound occurrence.

Because `Fin` indices are canonical de Bruijn names, every payload is already
alpha-normalized.  Applying a substitution never chooses fresh binder names
and hence preserves syntactic equality rather than weakening the algebra to
alpha-equivalence.
-/

namespace TypePM

namespace PolyCap

/-- Embed an ordinary solver capability as a bound-free polymorphic payload. -/
def lift {capArity : Nat} : Cap → PolyCap capArity
  | .any => .any
  | .var varId => .mvar varId
  | .skolem name => .skolem name
  | .con name children => .con name (children.map lift)
  | .prod components => .prod (components.map lift)

/-- Abstract selected capability metavariables into finite bound indices. -/
def abstract {capArity : Nat} (closing : CapVar → Option (Fin capArity)) :
    Cap → PolyCap capArity
  | .any => .any
  | .var varId =>
      match closing varId with
      | some index => .bound index
      | none => .mvar varId
  | .skolem name => .skolem name
  | .con name children => .con name (children.map (abstract closing))
  | .prod components => .prod (components.map (abstract closing))

/-- Open every bound capability with a caller-supplied ordinary capability. -/
def instantiate {capArity : Nat} (opening : Fin capArity → Cap) :
    PolyCap capArity → Cap
  | .any => .any
  | .mvar varId => .var varId
  | .bound index => opening index
  | .skolem name => .skolem name
  | .con name children => .con name (children.map (instantiate opening))
  | .prod components => .prod (components.map (instantiate opening))

/-- Apply an ambient capability substitution only to free metavariables. -/
def applyMeta {capArity : Nat} (substitution : CapSubst) :
    PolyCap capArity → PolyCap capArity
  | .any => .any
  | .mvar varId => lift (substitution varId)
  | .bound index => .bound index
  | .skolem name => .skolem name
  | .con name children =>
      .con name (children.map (applyMeta substitution))
  | .prod components => .prod (components.map (applyMeta substitution))

end PolyCap

namespace PolyTy

/-- Embed an ordinary solver type as a bound-free polymorphic payload. -/
def lift {capArity tyArity : Nat} : Ty → PolyTy capArity tyArity
  | .var varId => .mvar varId
  | .skolem name => .skolem name
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .data name children => .data name (children.map lift)
  | .prod components => .prod (components.map lift)
  | .fn domain codomain => .fn (lift domain) (lift codomain)
  | .matcher capability target =>
      .matcher (PolyCap.lift capability) (lift target)
  | .slot capability target => .slot (PolyCap.lift capability) (lift target)

/-- Abstract selected metavariables into the two finite binder spaces. -/
def abstract {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) :
    Ty → PolyTy capArity tyArity
  | .var varId =>
      match closeTy varId with
      | some index => .bound index
      | none => .mvar varId
  | .skolem name => .skolem name
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .data name children =>
      .data name (children.map (abstract closeCap closeTy))
  | .prod components =>
      .prod (components.map (abstract closeCap closeTy))
  | .fn domain codomain =>
      .fn (abstract closeCap closeTy domain)
        (abstract closeCap closeTy codomain)
  | .matcher capability target =>
      .matcher (PolyCap.abstract closeCap capability)
        (abstract closeCap closeTy target)
  | .slot capability target =>
      .slot (PolyCap.abstract closeCap capability)
        (abstract closeCap closeTy target)

/-- Open a polymorphic payload into the ordinary solver syntax. -/
def instantiate {capArity tyArity : Nat}
    (openCap : Fin capArity → Cap) (openTy : Fin tyArity → Ty) :
    PolyTy capArity tyArity → Ty
  | .mvar varId => .var varId
  | .bound index => openTy index
  | .skolem name => .skolem name
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .data name children =>
      .data name (children.map (instantiate openCap openTy))
  | .prod components =>
      .prod (components.map (instantiate openCap openTy))
  | .fn domain codomain =>
      .fn (instantiate openCap openTy domain)
        (instantiate openCap openTy codomain)
  | .matcher capability target =>
      .matcher (PolyCap.instantiate openCap capability)
        (instantiate openCap openTy target)
  | .slot capability target =>
      .slot (PolyCap.instantiate openCap capability)
        (instantiate openCap openTy target)

/-- Apply a paired ambient substitution only to free metavariable nodes. -/
def applyMeta {capArity tyArity : Nat} (substitution : Subst) :
    PolyTy capArity tyArity → PolyTy capArity tyArity
  | .mvar varId => lift (substitution.target varId)
  | .bound index => .bound index
  | .skolem name => .skolem name
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .data name children =>
      .data name (children.map (applyMeta substitution))
  | .prod components => .prod (components.map (applyMeta substitution))
  | .fn domain codomain =>
      .fn (applyMeta substitution domain) (applyMeta substitution codomain)
  | .matcher capability target =>
      .matcher (PolyCap.applyMeta substitution.cap capability)
        (applyMeta substitution target)
  | .slot capability target =>
      .slot (PolyCap.applyMeta substitution.cap capability)
        (applyMeta substitution target)

end PolyTy

/-! ## Structural boundary checks -/

/- The following regression distinguishes a bound index from a solver
metavariable even when their underlying natural-number payloads coincide. -/

namespace PolySyntaxRegression

/-- The former collision shape, now with a genuinely bound first capability
and a free metavariable in the second component. -/
def collisionBody : PolyTy 1 0 :=
  .prod [.matcher (.bound 0) .int, .matcher (.mvar 1) .int]

def captureAttempt : Subst :=
  { cap := fun varId => if varId = 1 then .var 0 else .var varId
    target := TySubst.id }

def laterRename : Subst :=
  { cap := fun varId => if varId = 0 then .var 1 else .var varId
    target := TySubst.id }

/-- A substitution image with the same numeric identifier as the binder
remains a free `meta`; it cannot become the distinct `bound 0` node. -/
theorem captureAttempt_keeps_namespaces_separate :
    PolyTy.applyMeta captureAttempt collisionBody =
      .prod [.matcher (.bound 0) .int, .matcher (.mvar 0) .int] := by
  simp [captureAttempt, collisionBody, PolyTy.applyMeta,
    PolyCap.applyMeta, PolyCap.lift]

/-- Later substitution rewrites only the free meta and leaves the bound node
fixed, so the old masking/capture discrepancy cannot occur. -/
theorem laterRename_preserves_bound :
    PolyTy.applyMeta laterRename
        (PolyTy.applyMeta captureAttempt collisionBody) =
      .prod [.matcher (.bound 0) .int, .matcher (.mvar 1) .int] := by
  simp [captureAttempt, laterRename, collisionBody, PolyTy.applyMeta,
    PolyCap.applyMeta, PolyCap.lift]

end PolySyntaxRegression

end TypePM
