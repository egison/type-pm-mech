import TypePM.Term

/-!
# Type-erased operational semantics

This module is the concrete operational semantics of the two-sorted Egison
core.  The dynamic semantics is deliberately type-erased: it depends only on
`TypePM.Term`; source typing and runtime invariants are connected later by
the preservation proof.

The mutually recursive judgments are:

* `Eval` for expression evaluation;
* `PPM` for primitive-pattern-pattern matching;
* `MAtom` for reducing one matching atom;
* `Step` for one matching-state step;
* `Search` for exhaustive matching-state search.

Pattern-function declarations need only their parameter names and body at
runtime, so `PatFunRuntimeSig` records exactly those fields.
-/

namespace TypePM

/-! ## Runtime matching states and pattern-function signatures -/

/-- Bindings accumulated while matching, newest segment first. -/
abbrev MatchSubst := List (String × Value)

/-- One matching atom `p ~_m v`. -/
structure Atom where
  p : Pattern
  m : Value
  v : Value
deriving Repr

/-- Runtime environment for embedded pattern parameters `~x`. -/
abbrev PiEnv := List (String × Pattern)

/-- A matching tree is either an atom or an isolated pattern-function node. -/
inductive Tree where
  | atom  : Atom → Tree
  | mnode : List Tree → Env → MatchSubst → PiEnv → Tree
deriving Repr

/-- A matching state `(S, rho, theta)`. -/
structure MState where
  S : List Tree
  ρ : Env
  θ : MatchSubst
deriving Repr

/-- The part of a pattern-function signature needed by the evaluator. -/
structure PatFunRuntimeSig where
  params : List String
  body   : Pattern
deriving Repr

/-- Runtime pattern-function signature environment. -/
abbrev RuntimeSigF := List (String × PatFunRuntimeSig)

/-! ## Built-in structural equality -/

mutual

/--
Structural equality on first-order values.  Closures, matcher closures, and
`something` are deliberately unequal to every value, including themselves.
-/
def Value.structEq : Value → Value → Bool
  | .lit n,       .lit n'        => n == n'
  | .ctor c vs,   .ctor c' vs'   => c == c' && structEqList vs vs'
  | .tuple vs,    .tuple vs'     => structEqList vs vs'
  | _,            _              => false

/-- Componentwise structural equality on value lists. -/
def structEqList : List Value → List Value → Bool
  | [],       []         => true
  | v :: vs,  v' :: vs'  => v.structEq v' && structEqList vs vs'
  | _,        _          => false

end

/-! ## Primitive delta rules -/

/--
Evaluation of runtime primitives.  `append` concatenates encoded lists;
`splits` enumerates every consecutive prefix/suffix split.
-/
def primEval : PrimOp → List Value → Option Value
  | .append, [v₁, v₂] => do
      let l₁ ← listOfV v₁
      let l₂ ← listOfV v₂
      pure (mkListV (l₁ ++ l₂))
  | .splits, [v] => do
      let l ← listOfV v
      pure (mkListV ((List.range (l.length + 1)).map fun i =>
        .tuple [mkListV (l.take i), mkListV (l.drop i)]))
  | _, _ => none

/-! ## Primitive data-pattern matching -/

mutual

/-- Deterministic primitive data-pattern matching. -/
def pdMatch : DPat → Value → Option Env
  | .var name, value => some [(name, value)]
  | .wild, _ => some []
  | .ctor name pats, value =>
      match value with
      | .ctor name' values =>
          if name == name' then pdMatchList pats values else none
      | _ => none
  | .tuple pats, value =>
      match value with
      | .tuple values => pdMatchList pats values
      | _ => none

/-- Componentwise primitive data-pattern matching. -/
def pdMatchList : List DPat → List Value → Option Env
  | [], values =>
      match values with
      | [] => some []
      | _ => none
  | pat :: pats, values =>
      match values with
      | value :: values' => do
          let ρ₁ ← pdMatch pat value
          let ρ₂ ← pdMatchList pats values'
          pure (ρ₁ ++ ρ₂)
      | _ => none

end

/-! ## Primitive-pattern shape checks -/

mutual

/-- Syntactic success guard for primitive-pattern-pattern matching. -/
def ppShapeOK : PPat → Pattern → Bool
  | .hole,          _              => true
  | .wild,          .wild          => true
  | .pval _,        .pval _        => true
  | .ctor name pps, .pctor name' ps =>
      name == name' && ppShapeOKList pps ps
  | .tuple pps,     .ptuple ps     => ppShapeOKList pps ps
  | _,              _              => false

/-- Componentwise primitive-pattern shape check. -/
def ppShapeOKList : List PPat → List Pattern → Bool
  | [],        []       => true
  | pp :: pps, p :: ps  => ppShapeOK pp p && ppShapeOKList pps ps
  | _,         _        => false

end


/-- Variable, wildcard, or value-pattern form used by `MS-PROD-SOME`. -/
def Pattern.isPrimForm : Pattern → Bool
  | .pvar _ => true
  | .wild   => true
  | .pval _ => true
  | _       => false

/--
Patterns eligible for ordered matcher-clause dispatch.  Conjunction,
disjunction, pattern-function application, and embedded parameters have their
own syntax-directed rules and must not be captured by a catch-all clause.
-/
def Pattern.isMatcherDispatchable : Pattern → Bool
  | .pvar _    => true
  | .wild      => true
  | .pval _    => true
  | .pctor _ _ => true
  | .ptuple _  => true
  | _          => false

/-! ## Recursive closures -/

/-- Reconstruct the self closure captured by a recursive function. -/
def selfClosure (name : String) (ρ : Env) (param : String)
    (body : Expr) : Value :=
  .closure (some name) ρ param body

/--
Extend a closure environment with its argument and, for a recursive closure,
with the same self closure.
-/
def pushArg (self : Option String) (ρ : Env) (param : String)
    (body : Expr) (arg : Value) : Env :=
  match self with
  | none => (param, arg) :: ρ
  | some name =>
      (param, arg) :: (name, selfClosure name ρ param body) :: ρ

/-! ## Mutually recursive operational judgments -/

mutual

/-- Big-step expression evaluation. -/
inductive Eval (SF : RuntimeSigF) : Env → Expr → Value → Prop where
  | var {ρ name value} :
      ρ.find? name = some value →
      Eval SF ρ (.var name) value
  | lam {ρ param body} :
      Eval SF ρ (.lam param body) (.closure none ρ param body)
  | fix {ρ name param body} :
      Eval SF ρ (.fix name param body)
        (selfClosure name ρ param body)
  | app {ρ fn arg self ρ' param body argValue value} :
      Eval SF ρ fn (.closure self ρ' param body) →
      Eval SF ρ arg argValue →
      Eval SF (pushArg self ρ' param body argValue) body value →
      Eval SF ρ (.app fn arg) value
  | lit {ρ n} :
      Eval SF ρ (.lit n) (.lit n)
  | tuple {ρ exprs values} :
      exprs.length = values.length →
      (∀ pair ∈ exprs.zip values, Eval SF ρ pair.1 pair.2) →
      Eval SF ρ (.tuple exprs) (.tuple values)
  | ctor {ρ name exprs values} :
      exprs.length = values.length →
      (∀ pair ∈ exprs.zip values, Eval SF ρ pair.1 pair.2) →
      Eval SF ρ (.ctor name exprs) (.ctor name values)
  | prim {ρ op exprs values value} :
      exprs.length = values.length →
      (∀ pair ∈ exprs.zip values, Eval SF ρ pair.1 pair.2) →
      primEval op values = some value →
      Eval SF ρ (.prim op exprs) value
  | letE {ρ name bound body boundValue value} :
      Eval SF ρ bound boundValue →
      Eval SF ((name, boundValue) :: ρ) body value →
      Eval SF ρ (.letE name bound body) value
  | something {ρ} :
      Eval SF ρ .something .something
  | matcher {ρ clauses} :
      Eval SF ρ (.matcher clauses) (.matcherV ρ clauses clauses)
  | matchAll {ρ target matcher pattern body targetValue matcherValue
      substitutions values} :
      Eval SF ρ target targetValue →
      Eval SF ρ matcher matcherValue →
      Search SF
        ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], ρ, []⟩
        substitutions →
      substitutions.length = values.length →
      (∀ pair ∈ substitutions.zip values,
        Eval SF (pair.1 ++ ρ) body pair.2) →
      Eval SF ρ (.matchAll target matcher pattern body) (mkListV values)

/-- Primitive-pattern-pattern matching.  `none` is explicit failure. -/
inductive PPM (SF : RuntimeSigF) :
    Env → PPat → Pattern → Option (List Pattern × Env) → Prop where
  | hole {ρ pattern} :
      PPM SF ρ .hole pattern (some ([pattern], []))
  | wild {ρ} :
      PPM SF ρ .wild .wild (some ([], []))
  | pval {ρ name expr value} :
      Eval SF ρ expr value →
      PPM SF ρ (.pval name) (.pval expr) (some ([], [(name, value)]))
  | ctor {ρ name pps patterns results} :
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF ρ entry.1.1 entry.1.2 (some entry.2)) →
      PPM SF ρ (.ctor name pps) (.pctor name patterns)
        (some ((results.map (·.1)).flatten,
          (results.map (·.2)).flatten))
  | tuple {ρ pps patterns results} :
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF ρ entry.1.1 entry.1.2 (some entry.2)) →
      PPM SF ρ (.tuple pps) (.ptuple patterns)
        (some ((results.map (·.1)).flatten,
          (results.map (·.2)).flatten))
  | fail {ρ pp pattern} :
      ppShapeOK pp pattern = false →
      PPM SF ρ pp pattern none

/-- Reduction of a single matching atom. -/
inductive MAtom (SF : RuntimeSigF) :
    Env → Pattern → Value → Value →
    List (List Atom) → MatchSubst → Prop where
  | someWC {ρ value} :
      MAtom SF ρ .wild .something value [[]] []
  | someVar {ρ name value} :
      MAtom SF ρ (.pvar name) .something value [[]] [(name, value)]
  | someValEq {ρ expr value expected} :
      Eval SF ρ expr expected →
      expected.structEq value = true →
      MAtom SF ρ (.pval expr) .something value [[]] []
  | someValNeq {ρ expr value expected} :
      Eval SF ρ expr expected →
      expected.structEq value = false →
      MAtom SF ρ (.pval expr) .something value [] []
  | and {ρ left right matcher value} :
      MAtom SF ρ (.pand left right) matcher value
        [[⟨left, matcher, value⟩, ⟨right, matcher, value⟩]] []
  | or {ρ left right matcher value} :
      MAtom SF ρ (.por left right) matcher value
        [[⟨left, matcher, value⟩], [⟨right, matcher, value⟩]] []
  | tuple {ρ patterns matchers values} :
      patterns.length = matchers.length →
      matchers.length = values.length →
      MAtom SF ρ (.ptuple patterns) (.tuple matchers) (.tuple values)
        [(patterns.zip (matchers.zip values)).map fun entry =>
          ⟨entry.1, entry.2.1, entry.2.2⟩] []
  | prodSome {ρ pattern matchers value} :
      pattern.isPrimForm = true →
      MAtom SF ρ pattern (.tuple matchers) value
        [[⟨pattern, .something, value⟩]] []
  | matcherPPFail {ρ ρm original pattern value pp next arms clauses
      continuations substitution} :
      pattern.isMatcherDispatchable = true →
      PPM SF ρ pp pattern none →
      MAtom SF ρ pattern (.matcherV ρm original clauses) value
        continuations substitution →
      MAtom SF ρ pattern
        (.matcherV ρm original (.mk pp next arms :: clauses)) value
        continuations substitution
  | matcherDPFail {ρ ρm original pattern value pp next dp body arms clauses
      holes ρp continuations substitution} :
      pattern.isMatcherDispatchable = true →
      PPM SF ρ pp pattern (some (holes, ρp)) →
      pdMatch dp value = none →
      MAtom SF ρ pattern
        (.matcherV ρm original (.mk pp next arms :: clauses)) value
        continuations substitution →
      MAtom SF ρ pattern
        (.matcherV ρm original
          (.mk pp next (.mk dp body :: arms) :: clauses)) value
        continuations substitution
  | matcher {ρ ρm original pattern value pp next dp body arms clauses holes ρp ρd
      decomposition tuples valueLists matcherValue matchers} :
      pattern.isMatcherDispatchable = true →
      PPM SF ρ pp pattern (some (holes, ρp)) →
      pdMatch dp value = some ρd →
      Eval SF (ρd ++ ρp ++ ρm) body decomposition →
      listOfV decomposition = some tuples →
      tuples.mapM (decodeTuple holes.length) = some valueLists →
      Eval SF ρm next matcherValue →
      decodeTuple holes.length matcherValue = some matchers →
      MAtom SF ρ pattern
        (.matcherV ρm original
          (.mk pp next (.mk dp body :: arms) :: clauses)) value
        (valueLists.map fun values =>
          (holes.zip (matchers.zip values)).map fun entry =>
            ⟨entry.1, entry.2.1, entry.2.2⟩) []

/-- One matching-state reduction. -/
inductive Step (SF : RuntimeSigF) : MState → List MState → Prop where
  | reduce {stack ρ substitution pattern matcher value continuations new} :
      MAtom SF (substitution ++ ρ) pattern matcher value
        continuations new →
      Step SF
        ⟨.atom ⟨pattern, matcher, value⟩ :: stack, ρ, substitution⟩
        (continuations.map fun atoms =>
          ⟨atoms.map .atom ++ stack, ρ, new ++ substitution⟩)
  | patfunEnter {stack ρ substitution name args matcher value signature} :
      (List.find? (fun entry => entry.1 == name) SF) =
        some (name, signature) →
      signature.params.length = args.length →
      Step SF
        ⟨.atom ⟨.papp name args, matcher, value⟩ :: stack, ρ, substitution⟩
        [⟨.mnode [.atom ⟨signature.body, matcher, value⟩]
            ρ [] (signature.params.zip args) :: stack,
          ρ, substitution⟩]
  | mnodeStep {stack ρ substitution tree innerStack ρf θf piE states} :
      (∀ name matcher value,
        tree = .atom ⟨.embed name, matcher, value⟩ →
        (List.find? (fun entry => entry.1 == name) piE) = none) →
      Step SF ⟨tree :: innerStack, ρf, θf⟩ states →
      Step SF
        ⟨.mnode (tree :: innerStack) ρf θf piE :: stack,
          ρ, substitution⟩
        (states.map fun state =>
          ⟨.mnode state.S ρf state.θ piE :: stack, ρ, substitution⟩)
  | mnodeVarpat {stack ρ substitution name pattern matcher value innerStack
      ρf θf piE} :
      (List.find? (fun entry => entry.1 == name) piE) =
        some (name, pattern) →
      Step SF
        ⟨.mnode (.atom ⟨.embed name, matcher, value⟩ :: innerStack)
            ρf θf piE :: stack,
          ρ, substitution⟩
        [⟨.atom ⟨pattern, matcher, value⟩ ::
            .mnode innerStack ρf θf piE :: stack,
          ρ, substitution⟩]
  | mnodeDone {stack ρ substitution ρf θf piE} :
      Step SF
        ⟨.mnode [] ρf θf piE :: stack, ρ, substitution⟩
        [⟨stack, ρ, substitution⟩]

/-- Exhaustive search from a matching state. -/
inductive Search (SF : RuntimeSigF) : MState → List MatchSubst → Prop where
  | done {ρ substitution} :
      Search SF ⟨[], ρ, substitution⟩ [substitution]
  | step {state states substitutions} :
      Step SF state states →
      states.length = substitutions.length →
      (∀ pair ∈ states.zip substitutions,
        Search SF pair.1 pair.2) →
      Search SF state substitutions.flatten

end

end TypePM
