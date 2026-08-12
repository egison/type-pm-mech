import TypePM.Inference

/-!
# Structural fuel for inference completeness

The completeness recursion is indexed by a DD derivation, whereas the
executable traversal is guarded by a natural-number fuel.  The executable
structural measures deliberately sum children and siblings, so strict
adequacy at a parent implies strict adequacy for every recursive call after
one unit is consumed.  These small predicates keep arithmetic out of the
proof-relevant traversal packages.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessFuel

open Inference

abbrev ExprAdequate (fuel : Nat) (expression : Expr) : Prop :=
  exprTraversalFuel expression < fuel

abbrev ExprListAdequate (fuel : Nat) (expressions : List Expr) : Prop :=
  exprListTraversalFuel expressions < fuel

abbrev PatternAdequate (fuel : Nat) (pattern : Pattern) : Prop :=
  patternTraversalFuel pattern < fuel

abbrev PatternListAdequate (fuel : Nat) (patterns : List Pattern) : Prop :=
  patternListTraversalFuel patterns < fuel

abbrev PPatAdequate (fuel : Nat) (pattern : PPat) : Prop :=
  ppatTraversalFuel pattern < fuel

abbrev PPatListAdequate (fuel : Nat) (patterns : List PPat) : Prop :=
  ppatListTraversalFuel patterns < fuel

abbrev DPatAdequate (fuel : Nat) (pattern : DPat) : Prop :=
  dpatTraversalFuel pattern < fuel

abbrev DPatListAdequate (fuel : Nat) (patterns : List DPat) : Prop :=
  dpatListTraversalFuel patterns < fuel

abbrev ArmListAdequate (fuel : Nat) (arms : List Arm) : Prop :=
  armListTraversalFuel arms < fuel

abbrev ClauseAdequate (fuel : Nat) (clause : Clause) : Prop :=
  clauseTraversalFuel clause < fuel

abbrev ClauseListAdequate (fuel : Nat) (clauses : List Clause) : Prop :=
  clauseListTraversalFuel clauses < fuel

/-- The public fuel chosen by `inferRaw` strictly dominates its root syntax
measure. -/
theorem inferenceFuel_adequate (expression : Expr) :
    ExprAdequate (inferenceFuel expression) expression := by
  unfold ExprAdequate inferenceFuel
  omega

/-- Every adequate fuel is positive, permitting one equation unfolding of
the executable traversal. -/
theorem positive_of_lt {measure fuel : Nat} (adequate : measure < fuel) :
    ∃ predecessor, fuel = predecessor + 1 := by
  cases fuel with
  | zero => omega
  | succ predecessor => exact ⟨predecessor, rfl⟩

/-- An expression-list cell gives adequate predecessor fuel to its head and
tail. -/
theorem exprList_cons {fuel : Nat} {expression : Expr}
    {expressions : List Expr}
    (adequate : ExprListAdequate (fuel + 1) (expression :: expressions)) :
    ExprAdequate fuel expression ∧ ExprListAdequate fuel expressions := by
  simp only [ExprListAdequate, ExprAdequate, exprListTraversalFuel] at adequate ⊢
  omega

/-- A pattern-list cell gives adequate predecessor fuel to its head and
tail. -/
theorem patternList_cons {fuel : Nat} {pattern : Pattern}
    {patterns : List Pattern}
    (adequate : PatternListAdequate (fuel + 1) (pattern :: patterns)) :
    PatternAdequate fuel pattern ∧ PatternListAdequate fuel patterns := by
  simp only [PatternListAdequate, PatternAdequate,
    patternListTraversalFuel] at adequate ⊢
  omega

/-- Primitive-pattern list counterpart. -/
theorem ppatList_cons {fuel : Nat} {pattern : PPat} {patterns : List PPat}
    (adequate : PPatListAdequate (fuel + 1) (pattern :: patterns)) :
    PPatAdequate fuel pattern ∧ PPatListAdequate fuel patterns := by
  simp only [PPatListAdequate, PPatAdequate, ppatListTraversalFuel]
    at adequate ⊢
  omega

/-- Primitive data-pattern list counterpart. -/
theorem dpatList_cons {fuel : Nat} {pattern : DPat} {patterns : List DPat}
    (adequate : DPatListAdequate (fuel + 1) (pattern :: patterns)) :
    DPatAdequate fuel pattern ∧ DPatListAdequate fuel patterns := by
  simp only [DPatListAdequate, DPatAdequate, dpatListTraversalFuel]
    at adequate ⊢
  omega

/-- A clause-list cell gives adequate predecessor fuel to its head and tail. -/
theorem clauseList_cons {fuel : Nat} {clause : Clause}
    {clauses : List Clause}
    (adequate : ClauseListAdequate (fuel + 1) (clause :: clauses)) :
    ClauseAdequate fuel clause ∧ ClauseListAdequate fuel clauses := by
  simp only [ClauseListAdequate, ClauseAdequate,
    clauseListTraversalFuel] at adequate ⊢
  omega

end DemandTypingInferenceCompletenessFuel
end TypePM
