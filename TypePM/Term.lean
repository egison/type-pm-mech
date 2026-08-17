import TypePM.Syntax

/-!
# Source and runtime terms

This module is the term-language foundation of the two-sorted Egison core.
All source forms and type-erased runtime values live directly in `TypePM`.

`match` is a surface elaboration into `matchAll` and `head` in the TeX model,
so it is deliberately not a core `Expr` constructor.
-/

namespace TypePM

/-- Primitive-pattern patterns `pp`. `pval x` represents `#$x`. -/
inductive PPat where
  | hole
  | wild
  | pval  : String → PPat
  | ctor  : String → List PPat → PPat
  | tuple : List PPat → PPat
deriving Repr

/-! ## Core ordering of primitive-pattern patterns -/

mutual

/--
Left-to-right, depth-first order for one primitive-pattern pattern.  The
Boolean indices record whether a pattern hole has already been visited.
`pval` is available only while that state is still `false`.
-/
inductive PPatOrder : Bool → PPat → Bool → Prop where
  | hole {seen} : PPatOrder seen .hole true
  | wild {seen} : PPatOrder seen .wild seen
  | pval {name} : PPatOrder false (.pval name) false
  | ctor {seen name patterns finished} :
      PPatsOrder seen patterns finished →
      PPatOrder seen (.ctor name patterns) finished
  | tuple {seen patterns finished} :
      PPatsOrder seen patterns finished →
      PPatOrder seen (.tuple patterns) finished

/-- List form of `PPatOrder`, threading the hole-seen state in source order. -/
inductive PPatsOrder : Bool → List PPat → Bool → Prop where
  | nil {seen} : PPatsOrder seen [] seen
  | cons {seen pattern middle patterns finished} :
      PPatOrder seen pattern middle →
      PPatsOrder middle patterns finished →
      PPatsOrder seen (pattern :: patterns) finished

end

/-- Formal-core boundary: no `#$x` occurs after a PP hole in DFS order. -/
def PPatCoreOrder (pattern : PPat) : Prop :=
  ∃ finished, PPatOrder false pattern finished

mutual

/-- Executable state-threading check corresponding to `PPatOrder`. -/
def PPat.orderState (seen : Bool) : PPat → Option Bool
  | .hole => some true
  | .wild => some seen
  | .pval _ => if seen then none else some false
  | .ctor _ patterns => PPat.orderStates seen patterns
  | .tuple patterns => PPat.orderStates seen patterns

/-- Executable list form of `PPat.orderState`. -/
def PPat.orderStates (seen : Bool) : List PPat → Option Bool
  | [] => some seen
  | pattern :: patterns => do
      let middle ← pattern.orderState seen
      PPat.orderStates middle patterns

end


/-- Executable formal-core order check used by Algorithm W. -/
def PPat.coreOrderCheck (pattern : PPat) : Bool :=
  (pattern.orderState false).isSome

mutual

/-- A successful executable order scan reconstructs its declarative proof. -/
theorem PPat.orderState_sound
    {seen finished : Bool} {pattern : PPat}
    (checked : pattern.orderState seen = some finished) :
    PPatOrder seen pattern finished := by
  cases pattern with
  | hole => simp [PPat.orderState] at checked; subst finished; exact .hole
  | wild => simp [PPat.orderState] at checked; subst finished; exact .wild
  | pval name =>
      cases seen <;> simp [PPat.orderState] at checked
      subst finished
      exact .pval
  | ctor name patterns =>
      exact .ctor (PPat.orderStates_sound checked)
  | tuple patterns =>
      exact .tuple (PPat.orderStates_sound checked)

/-- List form of `PPat.orderState_sound`. -/
theorem PPat.orderStates_sound
    {seen finished : Bool} {patterns : List PPat}
    (checked : PPat.orderStates seen patterns = some finished) :
    PPatsOrder seen patterns finished := by
  cases patterns with
  | nil =>
      simp [PPat.orderStates] at checked
      subst finished
      exact .nil
  | cons pattern patterns =>
      simp only [PPat.orderStates] at checked
      cases middleEq : pattern.orderState seen with
      | none => simp [middleEq] at checked
      | some middle =>
          simp only [middleEq] at checked
          exact .cons (PPat.orderState_sound middleEq)
            (PPat.orderStates_sound checked)

end


/-- Boolean success is sufficient for the declarative core order boundary. -/
theorem PPat.coreOrderCheck_sound {pattern : PPat}
    (checked : pattern.coreOrderCheck = true) : PPatCoreOrder pattern := by
  unfold PPat.coreOrderCheck at checked
  cases stateEq : pattern.orderState false with
  | none => simp [stateEq] at checked
  | some finished =>
      exact ⟨finished, PPat.orderState_sound stateEq⟩

/-- Primitive data patterns `dp`. -/
inductive DPat where
  | var   : String → DPat
  | wild
  | ctor  : String → List DPat → DPat
  | tuple : List DPat → DPat
deriving Repr

/-- Primitive operations used by matcher decomposition expressions. -/
inductive PrimOp where
  | append
  | splits
  | submultisetSplits
deriving Repr, DecidableEq

instance : BEq PrimOp where
  beq left right := decide (left = right)

instance : LawfulBEq PrimOp where
  eq_of_beq checked := of_decide_eq_true checked
  rfl := by simp

mutual

/-- Core source expressions `e`. -/
inductive Expr where
  | var       : String → Expr
  | lam       : String → Expr → Expr
  | fix       : String → String → Expr → Expr
  | app       : Expr → Expr → Expr
  | lit       : Int → Expr
  | tuple     : List Expr → Expr
  | ctor      : String → List Expr → Expr
  | prim      : PrimOp → List Expr → Expr
  | letE      : String → Expr → Expr → Expr
  | something : Expr
  | matcher   : List Clause → Expr
  | matchAll  : Expr → Expr → Pattern → Expr → Expr

/-- User patterns `p`. -/
inductive Pattern where
  | pvar   : String → Pattern
  | wild
  | pval   : Expr → Pattern
  | embed  : String → Pattern
  | pctor  : String → List Pattern → Pattern
  | pand   : Pattern → Pattern → Pattern
  | por    : Pattern → Pattern → Pattern
  | papp   : String → List Pattern → Pattern
  | ptuple : List Pattern → Pattern

/-- One data-pattern arm `[dp → N]` of a matcher clause. -/
inductive Arm where
  | mk : DPat → Expr → Arm

/-- A matcher clause `pp as M with [dp_j → N_j]_j`. -/
inductive Clause where
  | mk : PPat → Expr → List Arm → Clause

end


deriving instance Repr for Expr
deriving instance Repr for Pattern
deriving instance Repr for Arm
deriving instance Repr for Clause

/-! ## Clause and arm selectors -/

/-- The data pattern of an arm. -/
def Arm.pat : Arm → DPat
  | .mk pat _ => pat

/-- The body expression of an arm. -/
def Arm.body : Arm → Expr
  | .mk _ body => body

/-- The primitive-pattern pattern of a clause. -/
def Clause.pp : Clause → PPat
  | .mk pp _ _ => pp

/-- The next-matcher expression `M` of a clause. -/
def Clause.next : Clause → Expr
  | .mk _ next _ => next

/-- The ordered data-pattern arms of a clause. -/
def Clause.arms : Clause → List Arm
  | .mk _ _ arms => arms

/-- The arm data patterns of a clause, in source order. -/
def Clause.armPatterns (clause : Clause) : List DPat :=
  clause.arms.map Arm.pat

/-! ## Type-erased runtime values and environments -/

/-- Type-erased runtime values. -/
inductive Value where
  | lit       : Int → Value
  | ctor      : String → List Value → Value
  | tuple     : List Value → Value
  | closure   : Option String → List (String × Value) →
      String → Expr → Value
  | matcherV  : List (String × Value) →
      List Clause → List Clause → Value
  | something : Value
deriving Repr

/-- Runtime environments, with the newest binding first. -/
abbrev Env := List (String × Value)

/-- Runtime-environment lookup. -/
def Env.find? (ρ : Env) (name : String) : Option Value :=
  (List.find? (fun entry => entry.1 == name) ρ).map (·.2)

/-! ## Syntax helpers -/

mutual

/--
Expressions captured at the `#$x` positions where `pp` and `p` agree in
shape, from left to right.
-/
def capturedExprs : PPat → Pattern → List Expr
  | .pval _, .pval expr => [expr]
  | .ctor _ pps, .pctor _ pats => capturedExprsList pps pats
  | .tuple pps, .ptuple pats => capturedExprsList pps pats
  | _, _ => []

/-- List form of `capturedExprs`. -/
def capturedExprsList : List PPat → List Pattern → List Expr
  | pp :: pps, pat :: pats =>
      capturedExprs pp pat ++ capturedExprsList pps pats
  | _, _ => []

end


mutual

/-- Variables introduced by `#$x` in a primitive-pattern pattern. -/
def PPat.bindVars : PPat → List String
  | .hole => []
  | .wild => []
  | .pval name => [name]
  | .ctor _ pps => PPat.bindVarsList pps
  | .tuple pps => PPat.bindVarsList pps

/-- List form of `PPat.bindVars`. -/
def PPat.bindVarsList : List PPat → List String
  | [] => []
  | pp :: pps => pp.bindVars ++ PPat.bindVarsList pps

end


mutual

/-- Variables introduced by `$x` in a primitive data pattern. -/
def DPat.bindVars : DPat → List String
  | .var name => [name]
  | .wild => []
  | .ctor _ pats => DPat.bindVarsList pats
  | .tuple pats => DPat.bindVarsList pats

/-- List form of `DPat.bindVars`. -/
def DPat.bindVarsList : List DPat → List String
  | [] => []
  | pat :: pats => pat.bindVars ++ DPat.bindVarsList pats

end


mutual

/-- Embedded pattern variables `~x`, from left to right. -/
def Pattern.embedVars : Pattern → List String
  | .pvar _ => []
  | .wild => []
  | .pval _ => []
  | .embed name => [name]
  | .pctor _ pats => Pattern.embedVarsList pats
  | .pand left right => left.embedVars ++ right.embedVars
  | .por left right => left.embedVars ++ right.embedVars
  | .papp _ pats => Pattern.embedVarsList pats
  | .ptuple pats => Pattern.embedVarsList pats

/-- List form of `Pattern.embedVars`. -/
def Pattern.embedVarsList : List Pattern → List String
  | [] => []
  | pat :: pats => pat.embedVars ++ Pattern.embedVarsList pats

end


mutual

/-- Pattern variables `$x`, from left to right. -/
def Pattern.patVars : Pattern → List String
  | .pvar name => [name]
  | .wild => []
  | .pval _ => []
  | .embed _ => []
  | .pctor _ pats => Pattern.patVarsList pats
  | .pand left right => left.patVars ++ right.patVars
  | .por left _ => left.patVars
  | .papp _ pats => Pattern.patVarsList pats
  | .ptuple pats => Pattern.patVarsList pats

/-- List form of `Pattern.patVars`. -/
def Pattern.patVarsList : List Pattern → List String
  | [] => []
  | pat :: pats => pat.patVars ++ Pattern.patVarsList pats

end


/-- Encode a Lean list as the core `nil`/`cons` data value. -/
def mkListV : List Value → Value
  | [] => .ctor "nil" []
  | value :: values => .ctor "cons" [value, mkListV values]

/-- Decode a core `nil`/`cons` data value as a Lean list. -/
def listOfV : Value → Option (List Value)
  | .ctor "nil" [] => some []
  | .ctor "cons" [value, values] =>
      (listOfV values).map (value :: ·)
  | _ => none

/--
Decode a value as a `k`-component tuple. Following the operational model, a
one-component tuple is represented by the component itself.
-/
def decodeTuple (k : Nat) (value : Value) : Option (List Value) :=
  if k == 1 then
    some [value]
  else
    match value with
    | .tuple values =>
        if values.length == k then some values else none
    | _ => none

end TypePM
