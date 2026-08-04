import TypePM.P2.Term

/-!
# Singleton direct-self classification

The formal core admits monomorphic recursion through one binder at a time.
This module implements the fail-closed, shadowing-aware syntactic boundary
used for matcher-producing recursion.  An occurrence of the recursive name is
accepted only when it is the head of an application.  Passing the name as an
argument, storing it under an alias, or returning it as a value is rejected.

This is intentionally not a general producer-flow analysis.  In particular,
the checker does not attempt to recover origins through aliases or higher-order
arguments.
-/

namespace TypePM.P2
namespace DirectSelf

mutual

/--
Check an expression in ordinary (non-head) position.  A bare occurrence of
`binder` is rejected; application nodes delegate their function spine to
`checkHead`.
-/
def check (binder : String) : Expr → Bool
  | .var name => name != binder
  | .lam name body =>
      if name == binder then true else check binder body
  | .fix self argument body =>
      if self == binder || argument == binder then true else check binder body
  | .app function argument =>
      checkHead binder function && check binder argument
  | .lit _ => true
  | .tuple expressions => checkList binder expressions
  | .ctor _ arguments => checkList binder arguments
  | .prim _ arguments => checkList binder arguments
  | .letE name value body =>
      check binder value &&
        (if name == binder then true else check binder body)
  | .something => true
  | .matcher clauses => checkClauses binder clauses
  | .matchAll target matcher pattern body =>
      check binder target && check binder matcher &&
        checkPattern binder pattern &&
        (if pattern.patVars.contains binder then true else check binder body)

/--
Check the function spine of an application.  The recursive binder is accepted
at the head; arguments in a curried spine remain ordinary expression
positions and are checked by `check`.
-/
def checkHead (binder : String) : Expr → Bool
  | .var _ => true
  | .app function argument =>
      checkHead binder function && check binder argument
  | expression => check binder expression

/-- Pointwise expression checker. -/
def checkList (binder : String) : List Expr → Bool
  | [] => true
  | expression :: expressions =>
      check binder expression && checkList binder expressions

/--
Check value-pattern expressions embedded in a pattern.  Pattern variables do
not bind inside the pattern itself; they are handled at the enclosing
`matchAll` body.
-/
def checkPattern (binder : String) : Pattern → Bool
  | .pvar _ => true
  | .wild => true
  | .pval expression => check binder expression
  | .embed _ => true
  | .pctor _ patterns => checkPatterns binder patterns
  | .pand left right => checkPattern binder left && checkPattern binder right
  | .por left right => checkPattern binder left && checkPattern binder right
  | .papp _ patterns => checkPatterns binder patterns
  | .ptuple patterns => checkPatterns binder patterns

/-- Pointwise pattern checker. -/
def checkPatterns (binder : String) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      checkPattern binder pattern && checkPatterns binder patterns

/--
Check a matcher arm.  Variables bound by the primitive pattern-pattern and the
arm's data pattern shadow an outer recursive binder in the arm body.
-/
def checkArm (binder : String) (ppBinds : List String) : Arm → Bool
  | .mk dataPattern body =>
      if ppBinds.contains binder || dataPattern.bindVars.contains binder then
        true
      else
        check binder body

/-- Pointwise arm checker. -/
def checkArms
    (binder : String) (ppBinds : List String) : List Arm → Bool
  | [] => true
  | arm :: arms =>
      checkArm binder ppBinds arm && checkArms binder ppBinds arms

/--
Check a matcher clause.  The next-matcher expression is evaluated in the
outer context and therefore never receives the clause's PP/DP binders.
-/
def checkClause (binder : String) : Clause → Bool
  | .mk pp next arms =>
      check binder next && checkArms binder pp.bindVars arms

/-- Pointwise matcher-clause checker. -/
def checkClauses (binder : String) : List Clause → Bool
  | [] => true
  | clause :: clauses =>
      checkClause binder clause && checkClauses binder clauses

end

/-- The proof-relevant direct-self judgment used by source recursion. -/
def Holds (binder : String) (body : Expr) : Prop :=
  check binder body = true

instance (binder : String) (body : Expr) : Decidable (Holds binder body) :=
  inferInstanceAs (Decidable (check binder body = true))

@[simp] theorem bare_self_rejected (binder : String) :
    ¬ Holds binder (.var binder) := by
  simp [Holds, check]

@[simp] theorem direct_application_accepted
    (binder argument : String) (hne : argument ≠ binder) :
    Holds binder (.app (.var binder) (.var argument)) := by
  simp [Holds, check, checkHead, hne]

@[simp] theorem returned_self_rejected
    (binder argument : String) (hne : argument ≠ binder) :
    ¬ Holds binder (.lam argument (.var binder)) := by
  simp [Holds, check, hne]

@[simp] theorem alias_rejected
    (binder alias argument : String) :
    ¬ Holds binder
      (.letE alias (.var binder)
        (.app (.var alias) (.var argument))) := by
  simp [Holds, check]

@[simp] theorem lambda_shadowing_accepted
    (binder : String) (body : Expr) :
    Holds binder (.lam binder body) := by
  simp [Holds, check]

@[simp] theorem fix_shadowing_accepted
    (binder argument : String) (body : Expr) :
    Holds binder (.fix binder argument body) := by
  simp [Holds, check]

/-- `list m`-shaped recursive next-matcher calls lie in the accepted fragment. -/
example :
    Holds "list"
      (.matcher
        [.mk (.ctor "cons" [.hole, .hole])
          (.tuple
            [.var "m", .app (.var "list") (.var "m")])
          []]) := by
  native_decide

/-- Passing the recursive producer through an alias is deliberately rejected. -/
example :
    ¬ Holds "list"
      (.letE "again" (.var "list")
        (.app (.var "again") (.var "m"))) := by
  native_decide

end DirectSelf
end TypePM.P2
