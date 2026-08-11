import TypePM.PolySyntax

/-!
# Capture-free two-sorted schemes

`Scheme` packages the scheme-only payload syntax from `PolySyntax` with
its two binder arities.  Closing is the sole named-binder boundary: after it,
bound variables are finite local indices and cannot be passed to the ordinary
solver.  Ambient substitution preserves those indices, and instantiation is
the sole boundary back to ordinary `Cap` and `Ty`.
-/

namespace TypePM

/-- A closed two-sorted scheme in canonical local-index form. -/
structure Scheme where
  capArity : Nat
  tyArity : Nat
  body : PolyTy capArity tyArity
deriving Repr

namespace Scheme

/-- A monomorphic scheme contains no bound variables. -/
def mono (target : Ty) : Scheme :=
  { capArity := 0
    tyArity := 0
    body := PolyTy.lift target }

/-- Close named solver metavariables into finite scheme-local indices.

The binder lists are an input convention only; their identifiers are not
stored in the resulting scheme.  Generalization supplies duplicate-free
lists.  Explicit declaration checking should impose the same condition so
that every binder position has a unique meaning. -/
def close (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (target : Ty) : Scheme :=
  { capArity := capBinders.length
    tyArity := tyBinders.length
    body := PolyTy.abstract
      (fun varId => capBinders.finIdxOf? varId)
      (fun varId => tyBinders.finIdxOf? varId)
      target }

/-- Apply a paired ambient solver substitution to free metavariables only.
The binder arities and all bound indices remain definitionally unchanged. -/
def applyMeta (substitution : Subst) (scheme : Scheme) : Scheme :=
  { scheme with body := scheme.body.applyMeta substitution }

/-- Instantiate both binder sorts with assignments chosen by the caller.

Fresh inference instantiation, declarative variable-only instantiation, and
rigid skolemization use the same opening boundary with different assignments.
The assignments return ordinary solver syntax, so no bound node can escape. -/
def instantiate (scheme : Scheme)
    (openCap : Fin scheme.capArity → Cap)
    (openTy : Fin scheme.tyArity → Ty) : Ty :=
  scheme.body.instantiate openCap openTy

/-! ## Small boundary regressions -/

/-- Opening a representative monomorphic scheme returns its ordinary type. -/
theorem instantiate_mono_int
    (openCap : Fin (mono .int).capArity → Cap)
    (openTy : Fin (mono .int).tyArity → Ty) :
    (mono .int).instantiate openCap openTy = .int := by
  simp [mono, instantiate, PolyTy.lift, PolyTy.instantiate]

/-- Ambient substitution preserves both binder arities definitionally. -/
@[simp] theorem applyMeta_capArity (substitution : Subst)
    (scheme : Scheme) :
    (scheme.applyMeta substitution).capArity = scheme.capArity := by
  rfl

@[simp] theorem applyMeta_tyArity (substitution : Subst)
    (scheme : Scheme) :
    (scheme.applyMeta substitution).tyArity = scheme.tyArity := by
  rfl

end Scheme
end TypePM
