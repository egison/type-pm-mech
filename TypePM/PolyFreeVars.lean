import TypePM.PolyScheme

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

namespace PolyScheme

/-- Free capability solver metavariables of a scheme.

No binder filtering is required: bound occurrences are already distinct
`PolyCap.bound` nodes. -/
def fcv (scheme : PolyScheme) : List CapVar :=
  scheme.body.fcv

/-- Free ordinary-type solver metavariables of a scheme. -/
def ftv (scheme : PolyScheme) : List TypePM.TyVar :=
  scheme.body.ftv

end PolyScheme

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
       body := collisionBody } : PolyScheme).fcv = [0] := by
  rfl

end PolyFreeVarsRegression

end TypePM
