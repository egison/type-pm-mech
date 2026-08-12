import TypePM.Inference

/-!
# Structural fuel for inference completeness

The completeness recursion is indexed by a demand-directed derivation, whereas the
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

/-- Every immediate expression child receives adequate predecessor fuel. -/
theorem expr_lam {fuel : Nat} {name : String} {body : Expr}
    (adequate : ExprAdequate (fuel + 1) (.lam name body)) :
    ExprAdequate fuel body := by
  simp only [ExprAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_fix {fuel : Nat} {self argument : String} {body : Expr}
    (adequate : ExprAdequate (fuel + 1) (.fix self argument body)) :
    ExprAdequate fuel body := by
  simp only [ExprAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_app {fuel : Nat} {function argument : Expr}
    (adequate : ExprAdequate (fuel + 1) (.app function argument)) :
    ExprAdequate fuel function ∧ ExprAdequate fuel argument := by
  simp only [ExprAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_children {fuel : Nat} {constructor : String}
    {expressions : List Expr}
    (adequate : ExprAdequate (fuel + 1) (.ctor constructor expressions)) :
    ExprListAdequate fuel expressions := by
  simp only [ExprAdequate, ExprListAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_primitive {fuel : Nat} {op : PrimOp}
    {expressions : List Expr}
    (adequate : ExprAdequate (fuel + 1) (.prim op expressions)) :
    ExprListAdequate fuel expressions := by
  simp only [ExprAdequate, ExprListAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_tuple {fuel : Nat} {expressions : List Expr}
    (adequate : ExprAdequate (fuel + 1) (.tuple expressions)) :
    ExprListAdequate fuel expressions := by
  simp only [ExprAdequate, ExprListAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_let {fuel : Nat} {name : String} {value body : Expr}
    (adequate : ExprAdequate (fuel + 1) (.letE name value body)) :
    ExprAdequate fuel value ∧ ExprAdequate fuel body := by
  simp only [ExprAdequate, exprTraversalFuel] at adequate ⊢
  omega

theorem expr_matcher {fuel : Nat} {clauses : List Clause}
    (adequate : ExprAdequate (fuel + 1) (.matcher clauses)) :
    ClauseListAdequate fuel clauses := by
  simp only [ExprAdequate, ClauseListAdequate, exprTraversalFuel]
    at adequate ⊢
  omega

theorem expr_matchAll {fuel : Nat} {target matcher : Expr}
    {pattern : Pattern} {body : Expr}
    (adequate : ExprAdequate (fuel + 1)
      (.matchAll target matcher pattern body)) :
    ExprAdequate fuel target ∧ ExprAdequate fuel matcher ∧
      PatternAdequate fuel pattern ∧ ExprAdequate fuel body := by
  simp only [ExprAdequate, PatternAdequate, exprTraversalFuel]
    at adequate ⊢
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

theorem pattern_value {fuel : Nat} {expression : Expr}
    (adequate : PatternAdequate (fuel + 1) (.pval expression)) :
    ExprAdequate fuel expression := by
  simp only [PatternAdequate, ExprAdequate, patternTraversalFuel]
    at adequate ⊢
  omega

theorem pattern_ctor {fuel : Nat} {name : String} {patterns : List Pattern}
    (adequate : PatternAdequate (fuel + 1) (.pctor name patterns)) :
    PatternListAdequate fuel patterns := by
  simp only [PatternAdequate, PatternListAdequate, patternTraversalFuel]
    at adequate ⊢
  omega

theorem pattern_tuple {fuel : Nat} {patterns : List Pattern}
    (adequate : PatternAdequate (fuel + 1) (.ptuple patterns)) :
    PatternListAdequate fuel patterns := by
  simp only [PatternAdequate, PatternListAdequate, patternTraversalFuel]
    at adequate ⊢
  omega

theorem pattern_app {fuel : Nat} {name : String} {patterns : List Pattern}
    (adequate : PatternAdequate (fuel + 1) (.papp name patterns)) :
    PatternListAdequate fuel patterns := by
  simp only [PatternAdequate, PatternListAdequate, patternTraversalFuel]
    at adequate ⊢
  omega

theorem pattern_and {fuel : Nat} {left right : Pattern}
    (adequate : PatternAdequate (fuel + 1) (.pand left right)) :
    PatternAdequate fuel left ∧ PatternAdequate fuel right := by
  simp only [PatternAdequate, patternTraversalFuel] at adequate ⊢
  omega

theorem pattern_or {fuel : Nat} {left right : Pattern}
    (adequate : PatternAdequate (fuel + 1) (.por left right)) :
    PatternAdequate fuel left ∧ PatternAdequate fuel right := by
  simp only [PatternAdequate, patternTraversalFuel] at adequate ⊢
  omega

/-- Primitive-pattern list counterpart. -/
theorem ppatList_cons {fuel : Nat} {pattern : PPat} {patterns : List PPat}
    (adequate : PPatListAdequate (fuel + 1) (pattern :: patterns)) :
    PPatAdequate fuel pattern ∧ PPatListAdequate fuel patterns := by
  simp only [PPatListAdequate, PPatAdequate, ppatListTraversalFuel]
    at adequate ⊢
  omega

theorem ppat_ctor {fuel : Nat} {name : String} {patterns : List PPat}
    (adequate : PPatAdequate (fuel + 1) (.ctor name patterns)) :
    PPatListAdequate fuel patterns := by
  simp only [PPatAdequate, PPatListAdequate, ppatTraversalFuel]
    at adequate ⊢
  omega

theorem ppat_tuple {fuel : Nat} {patterns : List PPat}
    (adequate : PPatAdequate (fuel + 1) (.tuple patterns)) :
    PPatListAdequate fuel patterns := by
  simp only [PPatAdequate, PPatListAdequate, ppatTraversalFuel]
    at adequate ⊢
  omega

/-- Primitive data-pattern list counterpart. -/
theorem dpatList_cons {fuel : Nat} {pattern : DPat} {patterns : List DPat}
    (adequate : DPatListAdequate (fuel + 1) (pattern :: patterns)) :
    DPatAdequate fuel pattern ∧ DPatListAdequate fuel patterns := by
  simp only [DPatListAdequate, DPatAdequate, dpatListTraversalFuel]
    at adequate ⊢
  omega

theorem dpat_ctor {fuel : Nat} {name : String} {patterns : List DPat}
    (adequate : DPatAdequate (fuel + 1) (.ctor name patterns)) :
    DPatListAdequate fuel patterns := by
  simp only [DPatAdequate, DPatListAdequate, dpatTraversalFuel]
    at adequate ⊢
  omega

theorem dpat_tuple {fuel : Nat} {patterns : List DPat}
    (adequate : DPatAdequate (fuel + 1) (.tuple patterns)) :
    DPatListAdequate fuel patterns := by
  simp only [DPatAdequate, DPatListAdequate, dpatTraversalFuel]
    at adequate ⊢
  omega

theorem armList_cons {fuel : Nat} {dataPattern : DPat} {body : Expr}
    {arms : List Arm}
    (adequate : ArmListAdequate (fuel + 1)
      (.mk dataPattern body :: arms)) :
    DPatAdequate fuel dataPattern ∧ ExprAdequate fuel body ∧
      ArmListAdequate fuel arms := by
  simp only [ArmListAdequate, DPatAdequate, ExprAdequate,
    armListTraversalFuel, armTraversalFuel] at adequate ⊢
  omega

theorem clause_children {fuel : Nat} {primitivePattern : PPat}
    {next : Expr} {arms : List Arm}
    (adequate : ClauseAdequate (fuel + 1)
      (.mk primitivePattern next arms)) :
    PPatAdequate fuel primitivePattern ∧ ExprAdequate fuel next ∧
      ArmListAdequate fuel arms := by
  simp only [ClauseAdequate, PPatAdequate, ExprAdequate, ArmListAdequate,
    clauseTraversalFuel] at adequate ⊢
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
