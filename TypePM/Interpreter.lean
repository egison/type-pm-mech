import TypePM.Semantics

/-!
# Fuel-indexed reference interpreter

This module is an executable, fuel-indexed presentation of the type-erased
operational semantics in `TypePM.Semantics`.  Its purpose is to make the
notion of a runtime type error expressible: the big-step relations conflate
a stuck configuration with divergence (both simply have no derivation),
while here they are separated as `RunResult.stuck` and `RunResult.timeout`.

The interpreter mirrors the relational judgments constructor by
constructor — `evalFuel`/`Eval`, `ppmFuel`/`PPM`, `matomFuel`/`MAtom`,
`stepFuel`/`Step`, `searchFuel`/`Search` — so that adequacy (a successful
run reconstructs the corresponding derivation) is a structural induction.
Every recursive call consumes one unit of fuel; `timeout` therefore covers
both expression divergence and unbounded `matchAll` search.

`stuck` marks exactly the configurations with no applicable rule: an
unbound variable, applying a non-closure, a failing primitive delta, a
matching atom no `MAtom` rule accepts, an exhausted clause or arm list, a
failing decomposition decode, and an unknown or wrong-arity runtime
pattern function.  Match failure is *not* stuck: an atom may legitimately
reduce to no successor states, and a search over no states returns no
substitutions.
-/

namespace TypePM

/-- Outcome of one fuel-bounded run: success, fuel exhaustion, or a
configuration with no applicable rule (a runtime type error). -/
inductive RunResult (α : Type) : Type where
  | ok      : α → RunResult α
  | timeout : RunResult α
  | stuck   : RunResult α
deriving Repr

namespace RunResult

/-- Sequence two fuel-bounded computations. -/
def bind : RunResult α → (α → RunResult β) → RunResult β
  | .ok value, continuation => continuation value
  | .timeout, _ => .timeout
  | .stuck, _ => .stuck

instance : Monad RunResult where
  pure := .ok
  bind := RunResult.bind

@[simp] theorem bind_ok (value : α) (continuation : α → RunResult β) :
    bind (.ok value) continuation = continuation value := rfl

@[simp] theorem bind_timeout (continuation : α → RunResult β) :
    bind (.timeout : RunResult α) continuation = .timeout := rfl

@[simp] theorem bind_stuck (continuation : α → RunResult β) :
    bind (.stuck : RunResult α) continuation = .stuck := rfl

@[simp] theorem pure_eq_ok (value : α) :
    (pure value : RunResult α) = .ok value := rfl

@[simp] theorem monad_bind_eq_bind (run : RunResult α)
    (continuation : α → RunResult β) :
    run >>= continuation = bind run continuation := rfl

end RunResult

mutual

/-- Fuel-indexed expression evaluation mirroring `Eval`. -/
def evalFuel (SF : RuntimeSigF) : Nat → Env → Expr → RunResult Value
  | 0, _, _ => .timeout
  | fuel + 1, ρ, expression =>
    match expression with
    | .var name =>
        match Env.find? ρ name with
        | some value => .ok value
        | none => .stuck
    | .lam param body => .ok (.closure none ρ param body)
    | .fix name param body => .ok (selfClosure name ρ param body)
    | .app fn arg => do
        let fnValue ← evalFuel SF fuel ρ fn
        match fnValue with
        | .closure self closureEnv param body => do
            let argValue ← evalFuel SF fuel ρ arg
            evalFuel SF fuel (pushArg self closureEnv param body argValue)
              body
        | _ => .stuck
    | .lit n => .ok (.lit n)
    | .tuple exprs => do
        let values ← evalListFuel SF fuel ρ exprs
        pure (.tuple values)
    | .ctor name exprs => do
        let values ← evalListFuel SF fuel ρ exprs
        pure (.ctor name values)
    | .prim op exprs => do
        let values ← evalListFuel SF fuel ρ exprs
        match primEval op values with
        | some value => .ok value
        | none => .stuck
    | .letE name bound body => do
        let boundValue ← evalFuel SF fuel ρ bound
        evalFuel SF fuel ((name, boundValue) :: ρ) body
    | .something => .ok .something
    | .matcher clauses => .ok (.matcherV ρ clauses clauses)
    | .matchAll target matcher pattern body => do
        let targetValue ← evalFuel SF fuel ρ target
        let matcherValue ← evalFuel SF fuel ρ matcher
        let substitutions ← searchFuel SF fuel
          ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], ρ, []⟩
        let values ← evalSubstsFuel SF fuel ρ body substitutions
        pure (mkListV values)

/-- Pointwise evaluation of an expression list. -/
def evalListFuel (SF : RuntimeSigF) :
    Nat → Env → List Expr → RunResult (List Value)
  | 0, _, _ => .timeout
  | _ + 1, _, [] => .ok []
  | fuel + 1, ρ, expression :: exprs => do
      let value ← evalFuel SF fuel ρ expression
      let values ← evalListFuel SF fuel ρ exprs
      pure (value :: values)

/-- Evaluation of one body under each matching substitution. -/
def evalSubstsFuel (SF : RuntimeSigF) :
    Nat → Env → Expr → List MatchSubst → RunResult (List Value)
  | 0, _, _, _ => .timeout
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, ρ, body, substitution :: substitutions => do
      let value ← evalFuel SF fuel (substitution ++ ρ) body
      let values ← evalSubstsFuel SF fuel ρ body substitutions
      pure (value :: values)

/-- Fuel-indexed primitive-pattern-pattern matching mirroring `PPM`.
The shape check runs first: a shape-failing pair is an immediate explicit
failure with no embedded evaluation, and under a passing shape check the
structural walk cannot fail. -/
def ppmFuel (SF : RuntimeSigF) :
    Nat → Env → PPat → Pattern → RunResult (Option (List Pattern × Env))
  | 0, _, _, _ => .timeout
  | fuel + 1, ρ, pp, pattern =>
    if ppShapeOK pp pattern then
      match pp, pattern with
      | .hole, pattern => .ok (some ([pattern], []))
      | .wild, .wild => .ok (some ([], []))
      | .pval name, .pval expression => do
          let value ← evalFuel SF fuel ρ expression
          pure (some ([], [(name, value)]))
      | .ctor _ pps, .pctor _ patterns => do
          let results ← ppmListFuel SF fuel ρ pps patterns
          pure (some ((results.map (·.1)).flatten,
            (results.map (·.2)).flatten))
      | .tuple pps, .ptuple patterns => do
          let results ← ppmListFuel SF fuel ρ pps patterns
          pure (some ((results.map (·.1)).flatten,
            (results.map (·.2)).flatten))
      | _, _ => .stuck
    else .ok none

/-- Componentwise primitive-pattern matching under a passing parent shape
check; the impossible branches are stuck. -/
def ppmListFuel (SF : RuntimeSigF) :
    Nat → Env → List PPat → List Pattern →
    RunResult (List (List Pattern × Env))
  | 0, _, _, _ => .timeout
  | _ + 1, _, [], [] => .ok []
  | fuel + 1, ρ, pp :: pps, pattern :: patterns => do
      let outcome ← ppmFuel SF fuel ρ pp pattern
      match outcome with
      | some result => do
          let results ← ppmListFuel SF fuel ρ pps patterns
          pure (result :: results)
      | none => .stuck
  | _ + 1, _, _, _ => .stuck

/-- Fuel-indexed reduction of one matching atom mirroring `MAtom`. -/
def matomFuel (SF : RuntimeSigF) :
    Nat → Env → Pattern → Value → Value →
    RunResult (List (List Atom) × MatchSubst)
  | 0, _, _, _, _ => .timeout
  | fuel + 1, ρ, pattern, matcher, value =>
    match pattern, matcher with
    | .pand left right, matcher =>
        .ok ([[⟨left, matcher, value⟩, ⟨right, matcher, value⟩]], [])
    | .por left right, matcher =>
        .ok ([[⟨left, matcher, value⟩], [⟨right, matcher, value⟩]], [])
    | .wild, .something => .ok ([[]], [])
    | .pvar name, .something => .ok ([[]], [(name, value)])
    | .pval expression, .something => do
        let expected ← evalFuel SF fuel ρ expression
        if expected.structEq value then pure ([[]], [])
        else pure ([], [])
    | .ptuple patterns, .tuple matchers =>
        match value with
        | .tuple values =>
            if patterns.length = matchers.length ∧
                matchers.length = values.length then
              .ok ([(patterns.zip (matchers.zip values)).map fun entry =>
                ⟨entry.1, entry.2.1, entry.2.2⟩], [])
            else .stuck
        | _ => .stuck
    | pattern, .tuple _ =>
        if pattern.isPrimForm then
          .ok ([[⟨pattern, .something, value⟩]], [])
        else .stuck
    | pattern, .matcherV matcherEnv _original clauses =>
        if pattern.isMatcherDispatchable then
          dispatchFuel SF fuel ρ matcherEnv pattern value clauses
        else .stuck
    | _, _ => .stuck

/-- Ordered clause dispatch: skip shape-failing headers, commit to the
first shape-compatible clause. -/
def dispatchFuel (SF : RuntimeSigF) :
    Nat → Env → Env → Pattern → Value → List Clause →
    RunResult (List (List Atom) × MatchSubst)
  | 0, _, _, _, _, _ => .timeout
  | _ + 1, _, _, _, _, [] => .stuck
  | fuel + 1, ρ, matcherEnv, pattern, value, .mk pp next arms :: clauses => do
      let outcome ← ppmFuel SF fuel ρ pp pattern
      match outcome with
      | none => dispatchFuel SF fuel ρ matcherEnv pattern value clauses
      | some (holes, ppEnv) =>
          armsFuel SF fuel ρ matcherEnv value next holes ppEnv arms

/-- Ordered arm dispatch inside the committed clause. -/
def armsFuel (SF : RuntimeSigF) :
    Nat → Env → Env → Value → Expr → List Pattern → Env → List Arm →
    RunResult (List (List Atom) × MatchSubst)
  | 0, _, _, _, _, _, _, _ => .timeout
  | _ + 1, _, _, _, _, _, _, [] => .stuck
  | fuel + 1, ρ, matcherEnv, value, next, holes, ppEnv,
      .mk dp body :: arms =>
    match pdMatch dp value with
    | none => armsFuel SF fuel ρ matcherEnv value next holes ppEnv arms
    | some dataEnv => do
        let decomposition ←
          evalFuel SF fuel (dataEnv ++ ppEnv ++ matcherEnv) body
        match listOfV decomposition with
        | none => .stuck
        | some tuples =>
            match tuples.mapM (decodeTuple holes.length) with
            | none => .stuck
            | some valueLists => do
                let matcherValue ← evalFuel SF fuel matcherEnv next
                match decodeTuple holes.length matcherValue with
                | none => .stuck
                | some matchers =>
                    pure (valueLists.map fun values =>
                      (holes.zip (matchers.zip values)).map fun entry =>
                        ⟨entry.1, entry.2.1, entry.2.2⟩, [])

/-- Fuel-indexed matching-state step mirroring `Step`. -/
def stepFuel (SF : RuntimeSigF) : Nat → MState → RunResult (List MState)
  | 0, _ => .timeout
  | _ + 1, ⟨[], _, _⟩ => .stuck
  | _ + 1, ⟨.atom ⟨.papp name arguments, matcher, value⟩ :: stack,
      ρ, substitution⟩ =>
    match List.find? (fun entry => entry.1 == name) SF with
    | some entry =>
        if entry.2.params.length = arguments.length then
          .ok [⟨.mnode [.atom ⟨entry.2.body, matcher, value⟩] ρ []
              (entry.2.params.zip arguments) :: stack,
            ρ, substitution⟩]
        else .stuck
    | none => .stuck
  | fuel + 1, ⟨.atom ⟨pattern, matcher, value⟩ :: stack, ρ, substitution⟩ =>
      do
        let (continuations, new) ←
          matomFuel SF fuel (substitution ++ ρ) pattern matcher value
        pure (continuations.map fun atoms =>
          ⟨atoms.map .atom ++ stack, ρ, new ++ substitution⟩)
  | _ + 1, ⟨.mnode [] _ _ _ :: stack, ρ, substitution⟩ =>
      .ok [⟨stack, ρ, substitution⟩]
  | fuel + 1, ⟨.mnode (.atom ⟨.embed name, matcher, value⟩ :: innerStack)
      innerEnv innerSubst piE :: stack, ρ, substitution⟩ =>
    match List.find? (fun entry => entry.1 == name) piE with
    | some entry =>
        .ok [⟨.atom ⟨entry.2, matcher, value⟩ ::
            .mnode innerStack innerEnv innerSubst piE :: stack,
          ρ, substitution⟩]
    | none => do
        let states ← stepFuel SF fuel
          ⟨.atom ⟨.embed name, matcher, value⟩ :: innerStack,
            innerEnv, innerSubst⟩
        pure (states.map fun state =>
          ⟨.mnode state.S innerEnv state.θ piE :: stack, ρ, substitution⟩)
  | fuel + 1, ⟨.mnode (tree :: innerStack) innerEnv innerSubst piE :: stack,
      ρ, substitution⟩ => do
      let states ← stepFuel SF fuel
        ⟨tree :: innerStack, innerEnv, innerSubst⟩
      pure (states.map fun state =>
        ⟨.mnode state.S innerEnv state.θ piE :: stack, ρ, substitution⟩)

/-- Fuel-indexed exhaustive search mirroring `Search`. -/
def searchFuel (SF : RuntimeSigF) : Nat → MState → RunResult (List MatchSubst)
  | 0, _ => .timeout
  | _ + 1, ⟨[], _, substitution⟩ => .ok [substitution]
  | fuel + 1, state => do
      let states ← stepFuel SF fuel state
      let results ← searchListFuel SF fuel states
      pure results.flatten

/-- Pointwise search over successor states. -/
def searchListFuel (SF : RuntimeSigF) :
    Nat → List MState → RunResult (List (List MatchSubst))
  | 0, _ => .timeout
  | _ + 1, [] => .ok []
  | fuel + 1, state :: states => do
      let results ← searchFuel SF fuel state
      let rest ← searchListFuel SF fuel states
      pure (results :: rest)

end

/-! ## Executable smoke tests -/

/-- Identity application. -/
example :
    evalFuel [] 5 [] (.app (.lam "x" (.var "x")) (.lit 1)) = .ok (.lit 1) :=
  rfl

/-- Unbound variables are stuck, not timed out. -/
example : evalFuel [] 5 [] (.var "missing") = .stuck := rfl

/-- Applying a non-closure is stuck. -/
example : evalFuel [] 5 [] (.app (.lit 1) (.lit 2)) = .stuck := rfl

/-- Divergence is a timeout at every fuel (spot-checked at 7). -/
example :
    evalFuel [] 7 [] (.app (.fix "f" "x" (.app (.var "f") (.var "x")))
      (.lit 0)) = .timeout := rfl

end TypePM
