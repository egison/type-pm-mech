import TypePM.RecursiveExamples
import TypePM.RuntimeAgreementBridge
import TypePM.Safety

/-!
# Dynamic ordered-dispatch regression

This file drives one concrete `cons $x $rest` match through both private
matcher cursors before the successful arm.  The leading `nil` clause fails in
primitive-pattern dispatch, the first `nil` data arm of the `cons` clause
fails against the concrete `cons` target, and the following `cons` data arm
produces one two-component decomposition.  Thus one kernel derivation contains

`MAtom.matcherPPFail -> MAtom.matcherDPFail -> MAtom.matcher`,

with a genuine two-child `PPM.ctor` at the latter two nodes.  The resulting
atoms bind `x` and `rest`; the same run is closed under `Step`, `Search`,
`Reaches`, and `Eval`.
-/

namespace TypePM
namespace DynamicDispatchRegression

abbrev signature : FrozenSig := RecursiveExamples.listSignature

def runtimeSignature : RuntimeSigF := []

/-! ## Concrete source fixture -/

def nilValue : Value :=
  .ctor "nil" []

def targetExpression : Expr :=
  .ctor "cons" [.lit 1, .ctor "nil" []]

def targetValue : Value :=
  .ctor "cons" [.lit 1, nilValue]

def userPattern : Pattern :=
  .pctor "cons" [.pvar "x", .pvar "rest"]

def nilArm : Arm :=
  .mk .wild (.ctor "nil" [])

def nilClause : Clause :=
  .mk (generalPP "nil" 0) (.tuple []) [nilArm]

def failingDataArm : Arm :=
  .mk (.ctor "nil" []) (.ctor "nil" [])

def decompositionExpression : Expr :=
  .ctor "cons"
    [.tuple [.var "head", .var "tail"], .ctor "nil" []]

def decompositionValue : Value :=
  .ctor "cons" [.tuple [.lit 1, nilValue], nilValue]

def successfulDataArm : Arm :=
  .mk (.ctor "cons" [.var "head", .var "tail"])
    decompositionExpression

/-- This arm is unreachable in the concrete run.  It is retained so the
conservative source exhaustiveness checker sees an irrefutable arm. -/
def exhaustiveDataArm : Arm :=
  .mk .wild (.ctor "nil" [])

def nextMatchersExpression : Expr :=
  .tuple [.something, .something]

def liveConsClause : Clause :=
  .mk (generalPP "cons" 2) nextMatchersExpression
    [failingDataArm, successfulDataArm, exhaustiveDataArm]

/-- The mandatory bare-hole clause remains last. -/
def catchAllClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole")
      (.ctor "cons" [.var "whole", .ctor "nil" []])]

def clauses : List Clause :=
  [nilClause, liveConsClause, catchAllClause]

def matcherExpression : Expr :=
  .matcher clauses

def matcherValue : Value :=
  .matcherV [] clauses clauses

def program : Expr :=
  .matchAll targetExpression matcherExpression userPattern
    (.tuple [.var "x", .var "rest"])

def programValue : Value :=
  decompositionValue

/-! ## Primitive-pattern dispatch and data-arm cursor movement -/

theorem nil_primitive_pattern_failure :
    PPM runtimeSignature [] (generalPP "nil" 0) userPattern none := by
  exact .fail rfl

def primitiveResults : List (List Pattern × Env) :=
  [([.pvar "x"], []), ([.pvar "rest"], [])]

/-- The `cons` header traverses both child holes and returns the two user
subpatterns in source order. -/
theorem cons_primitive_pattern_success :
    PPM runtimeSignature [] (generalPP "cons" 2) userPattern
      (some ([.pvar "x", .pvar "rest"], [])) := by
  simpa [generalPP, userPattern, primitiveResults] using
    (PPM.ctor (SF := runtimeSignature) (ρ := []) (name := "cons")
      (pps := [.hole, .hole])
      (patterns := [.pvar "x", .pvar "rest"])
      (results := primitiveResults) rfl rfl (by
        intro entry member
        simp [primitiveResults] at member
        rcases member with rfl | rfl <;> exact .hole))

theorem first_data_arm_failure :
    pdMatch (.ctor "nil" []) targetValue = none := by
  rfl

def dataEnvironment : Env :=
  [("head", .lit 1), ("tail", nilValue)]

theorem second_data_arm_success :
    pdMatch (.ctor "cons" [.var "head", .var "tail"]) targetValue =
      some dataEnvironment := by
  rfl

theorem decomposition_evaluation :
    Eval runtimeSignature dataEnvironment decompositionExpression
      decompositionValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · refine Eval.tuple rfl ?_
    intro pair member
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact .var (by rfl)
    · rcases member with rfl | member
      · exact .var (by rfl)
      · simp at member
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

theorem next_matchers_evaluation :
    Eval runtimeSignature [] nextMatchersExpression
      (.tuple [.something, .something]) := by
  refine Eval.tuple rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .something
  · rcases member with rfl | member
    · exact .something
    · simp at member

def xAtom : Atom :=
  ⟨.pvar "x", .something, .lit 1⟩

def restAtom : Atom :=
  ⟨.pvar "rest", .something, nilValue⟩

def successfulContinuation : List Atom :=
  [xAtom, restAtom]

/-! ## One nested `MAtom` dispatch spine -/

/-- Successful reduction after the failed data arm has been removed from the
private clause cursor. -/
theorem successful_cons_reduction :
    MAtom runtimeSignature [] userPattern
      (.matcherV [] clauses
        [.mk (generalPP "cons" 2) nextMatchersExpression
          [successfulDataArm, exhaustiveDataArm], catchAllClause])
      targetValue [successfulContinuation] [] := by
  simpa [runtimeSignature, clauses, successfulDataArm, exhaustiveDataArm,
    decompositionExpression, decompositionValue, targetValue, nilValue,
    dataEnvironment, primitiveResults, nextMatchersExpression,
    successfulContinuation, xAtom, restAtom, listOfV, decodeTuple] using
    (MAtom.matcher (SF := runtimeSignature)
      (ρ := []) (ρm := []) (original := clauses)
      (pattern := userPattern) (value := targetValue)
      (pp := generalPP "cons" 2) (next := nextMatchersExpression)
      (dp := DPat.ctor "cons" [.var "head", .var "tail"])
      (body := decompositionExpression)
      (arms := [exhaustiveDataArm]) (clauses := [catchAllClause])
      (holes := [.pvar "x", .pvar "rest"]) (ρp := [])
      (ρd := dataEnvironment) (decomposition := decompositionValue)
      (tuples := [.tuple [.lit 1, nilValue]])
      (valueLists := [[.lit 1, nilValue]])
      (matcherValue := .tuple [.something, .something])
      (matchers := [.something, .something]) rfl
      cons_primitive_pattern_success second_data_arm_success
      decomposition_evaluation rfl rfl next_matchers_evaluation rfl)

/-- The first data arm fails, and dispatch continues to the successful arm of
the same `cons` clause. -/
theorem after_nil_clause_reduction :
    MAtom runtimeSignature [] userPattern
      (.matcherV [] clauses [liveConsClause, catchAllClause])
      targetValue [successfulContinuation] [] := by
  simpa [liveConsClause, failingDataArm] using
    (MAtom.matcherDPFail (SF := runtimeSignature) rfl
      cons_primitive_pattern_success first_data_arm_failure
      successful_cons_reduction)

/-- The complete atom reduction first skips the mismatching `nil` header,
then skips the mismatching `nil` data arm, and finally uses the `cons` arm. -/
theorem ordered_matcher_reduction :
    MAtom runtimeSignature [] userPattern matcherValue targetValue
      [successfulContinuation] [] := by
  simpa [matcherValue, clauses, nilClause] using
    (MAtom.matcherPPFail (SF := runtimeSignature) rfl
      nil_primitive_pattern_failure after_nil_clause_reduction)

/-! ## Concrete semantic dispatch history -/

theorem dispatch_trace_start :
    DispatchTrace runtimeSignature [] userPattern targetValue clauses clauses :=
  .refl

theorem dispatch_trace_after_nil :
    DispatchTrace runtimeSignature [] userPattern targetValue clauses
      [liveConsClause, catchAllClause] := by
  simpa [clauses, nilClause] using
    (DispatchTrace.nextClause dispatch_trace_start
      nil_primitive_pattern_failure)

theorem dispatch_trace_after_first_arm :
    DispatchTrace runtimeSignature [] userPattern targetValue clauses
      [.mk (generalPP "cons" 2) nextMatchersExpression
        [successfulDataArm, exhaustiveDataArm], catchAllClause] := by
  simpa [liveConsClause, failingDataArm] using
    (DispatchTrace.nextArm dispatch_trace_after_nil
      cons_primitive_pattern_success first_data_arm_failure)

/-! ## State execution, search, reachability, and evaluation -/

def initialState : MState :=
  ⟨[.atom ⟨userPattern, matcherValue, targetValue⟩], [], []⟩

def continuationState : MState :=
  ⟨[.atom xAtom, .atom restAtom], [], []⟩

def xSubstitution : MatchSubst :=
  [("x", .lit 1)]

def restState : MState :=
  ⟨[.atom restAtom], [], xSubstitution⟩

def finalSubstitution : MatchSubst :=
  [("rest", nilValue), ("x", .lit 1)]

def terminalState : MState :=
  ⟨[], [], finalSubstitution⟩

theorem dispatch_step :
    Step runtimeSignature initialState [continuationState] := by
  simpa [initialState, continuationState, successfulContinuation, xAtom,
    restAtom, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := []) ordered_matcher_reduction)

theorem x_reduction :
    MAtom runtimeSignature [] (.pvar "x") .something (.lit 1)
      [[]] xSubstitution := by
  simpa [xSubstitution] using
    (MAtom.someVar (SF := runtimeSignature) (ρ := [])
      (name := "x") (value := Value.lit 1))

theorem x_step :
    Step runtimeSignature continuationState [restState] := by
  simpa [continuationState, restState, xAtom, restAtom, xSubstitution,
    runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := [.atom restAtom])
      (ρ := []) (substitution := []) x_reduction)

theorem rest_reduction :
    MAtom runtimeSignature xSubstitution (.pvar "rest") .something nilValue
      [[]] [("rest", nilValue)] := by
  exact .someVar

theorem rest_step :
    Step runtimeSignature restState [terminalState] := by
  simpa [restState, terminalState, restAtom, xSubstitution,
    finalSubstitution, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := xSubstitution) rest_reduction)

theorem terminal_search :
    Search runtimeSignature terminalState [finalSubstitution] := by
  simpa [terminalState] using
    (Search.done (SF := runtimeSignature) (ρ := [])
      (substitution := finalSubstitution))

theorem rest_search :
    Search runtimeSignature restState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) rest_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact terminal_search
  · simp at member

theorem continuation_search :
    Search runtimeSignature continuationState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) x_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact rest_search
  · simp at member

theorem program_search :
    Search runtimeSignature initialState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) dispatch_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact continuation_search
  · simp at member

theorem program_reaches_terminal :
    Reaches runtimeSignature initialState terminalState :=
  .step dispatch_step (by simp)
    (.step x_step (by simp)
      (.step rest_step (by simp) .refl))

theorem target_evaluation :
    Eval runtimeSignature [] targetExpression targetValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .lit
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

theorem matcher_evaluation :
    Eval runtimeSignature [] matcherExpression matcherValue := by
  exact .matcher

theorem result_evaluation :
    Eval runtimeSignature finalSubstitution
      (.tuple [.var "x", .var "rest"])
      (.tuple [.lit 1, nilValue]) := by
  refine Eval.tuple rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .var (by rfl)
  · rcases member with rfl | member
    · exact .var (by rfl)
    · simp at member

theorem program_evaluation :
    Eval runtimeSignature [] program programValue := by
  simpa [program, programValue, decompositionValue, nilValue, mkListV] using
    (Eval.matchAll (SF := runtimeSignature) (ρ := [])
      (target := targetExpression) (matcher := matcherExpression)
      (pattern := userPattern) (body := .tuple [.var "x", .var "rest"])
      (targetValue := targetValue) (matcherValue := matcherValue)
      (substitutions := [finalSubstitution])
      (values := [.tuple [.lit 1, nilValue]]) target_evaluation
      matcher_evaluation program_search rfl (by
        intro pair member
        simp only [List.zip_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact result_evaluation
        · simp at member))

/-! ## Publicly typed ordered-dispatch fixture

The compact List trace above uses two catch-all consumers and is intentionally
operational.  This companion fixture gives the same private cursor spine a
fully checked source boundary.  Its non-recursive `Pair α` family has two
constructors, so both children of `pair $x $rest` can soundly use `something`.
The run still performs

`MAtom.matcherPPFail -> MAtom.matcherDPFail -> MAtom.matcher`,

binds both variables, reaches a nonempty terminal substitution, and is then
fed through public inference, evaluation preservation, step preservation,
reachability, search-substitution typing, and matcher consistency.
-/

namespace TypedFixture

def observability : Shape.Observability :=
  fun former =>
    if former = "List" then some [true]
    else if former = "Pair" then some [true]
    else none

def pairElement : Ty := .var 0
def pairTy : Ty := .data "Pair" [pairElement]

def emptyPairScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := []
  result := pairTy

def pairScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [pairElement, pairElement]
  result := pairTy

def emptyPairProjection : Projection.ProjectionSignature observability where
  fieldTypes := emptyPairScheme.args
  resultType := emptyPairScheme.result
  resultRoot := .data (mask := [true]) (by simp [observability]) (by simp)

def pairProjection : Projection.ProjectionSignature observability where
  fieldTypes := pairScheme.args
  resultType := pairScheme.result
  resultRoot := .data (mask := [true]) (by simp [observability]) (by simp)

def emptyPairPatternCtor : PatternCtorScheme observability where
  scheme := emptyPairScheme
  projection := emptyPairProjection
  projectionFields := rfl
  projectionResult := rfl

def pairPatternCtor : PatternCtorScheme observability where
  scheme := pairScheme
  projection := pairProjection
  projectionFields := rfl
  projectionResult := rfl

def signature : FrozenSig where
  observability := observability
  dataCtors :=
    [("nil", RecursiveExamples.nilScheme),
      ("cons", RecursiveExamples.consScheme),
      ("emptyPair", emptyPairScheme), ("pair", pairScheme)]
  patternCtors :=
    [("emptyPair", emptyPairPatternCtor), ("pair", pairPatternCtor)]
  patternFuns := []
  primitives := []
  constructorsByFormer :=
    [("Pair", [("emptyPair", 0), ("pair", 2)])]
  armExhaustive := basicArmExhaustive

def runtimeSignature : RuntimeSigF := []

def nilValue : Value := .ctor "nil" []
def targetExpression : Expr := .ctor "pair" [.lit 1, .lit 2]
def targetValue : Value := .ctor "pair" [.lit 1, .lit 2]
def userPattern : Pattern := .pctor "pair" [.pvar "x", .pvar "rest"]

def emptyArm : Arm := .mk .wild (.ctor "nil" [])
def emptyClause : Clause :=
  .mk (generalPP "emptyPair" 0) (.tuple []) [emptyArm]

def failingDataArm : Arm :=
  .mk (.ctor "emptyPair" []) (.ctor "nil" [])

def decompositionExpression : Expr :=
  .ctor "cons"
    [.tuple [.var "head", .var "tail"], .ctor "nil" []]

def decompositionValue : Value :=
  .ctor "cons" [.tuple [.lit 1, .lit 2], nilValue]

def successfulDataArm : Arm :=
  .mk (.ctor "pair" [.var "head", .var "tail"])
    decompositionExpression

def exhaustiveDataArm : Arm := .mk .wild (.ctor "nil" [])

def nextMatchersExpression : Expr := .tuple [.something, .something]

def livePairClause : Clause :=
  .mk (generalPP "pair" 2) nextMatchersExpression
    [failingDataArm, successfulDataArm, exhaustiveDataArm]

def catchAllClause : Clause :=
  .mk .hole .something
    [.mk (.var "whole")
      (.ctor "cons" [.var "whole", .ctor "nil" []])]

def clauses : List Clause := [emptyClause, livePairClause, catchAllClause]
def matcherExpression : Expr := .matcher clauses
def matcherValue : Value := .matcherV [] clauses clauses

def program : Expr :=
  .matchAll targetExpression matcherExpression userPattern
    (.tuple [.var "x", .var "rest"])

theorem signature_wf : FrozenSigWF signature :=
  frozenSigWFCheck_sound (by decide) rfl

theorem empty_primitive_pattern_failure :
    PPM runtimeSignature [] (generalPP "emptyPair" 0) userPattern none := by
  exact .fail rfl

def primitiveResults : List (List Pattern × Env) :=
  [([.pvar "x"], []), ([.pvar "rest"], [])]

theorem pair_primitive_pattern_success :
    PPM runtimeSignature [] (generalPP "pair" 2) userPattern
      (some ([.pvar "x", .pvar "rest"], [])) := by
  simpa [generalPP, userPattern, primitiveResults] using
    (PPM.ctor (SF := runtimeSignature) (ρ := []) (name := "pair")
      (pps := [.hole, .hole])
      (patterns := [.pvar "x", .pvar "rest"])
      (results := primitiveResults) rfl rfl (by
        intro entry member
        simp [primitiveResults] at member
        rcases member with rfl | rfl <;> exact .hole))

theorem first_data_arm_failure :
    pdMatch (.ctor "emptyPair" []) targetValue = none := by
  rfl

def dataEnvironment : Env :=
  [("head", .lit 1), ("tail", .lit 2)]

theorem second_data_arm_success :
    pdMatch (.ctor "pair" [.var "head", .var "tail"]) targetValue =
      some dataEnvironment := by
  rfl

theorem decomposition_evaluation :
    Eval runtimeSignature dataEnvironment decompositionExpression
      decompositionValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · refine Eval.tuple rfl ?_
    intro pair member
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact .var (by rfl)
    · rcases member with rfl | member
      · exact .var (by rfl)
      · simp at member
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

theorem next_matchers_evaluation :
    Eval runtimeSignature [] nextMatchersExpression
      (.tuple [.something, .something]) := by
  refine Eval.tuple rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .something
  · rcases member with rfl | member
    · exact .something
    · simp at member

def xAtom : Atom :=
  ⟨.pvar "x", .something, .lit 1⟩

def restAtom : Atom :=
  ⟨.pvar "rest", .something, .lit 2⟩

def successfulContinuation : List Atom :=
  [xAtom, restAtom]

theorem successful_pair_reduction :
    MAtom runtimeSignature [] userPattern
      (.matcherV [] clauses
        [.mk (generalPP "pair" 2) nextMatchersExpression
          [successfulDataArm, exhaustiveDataArm], catchAllClause])
      targetValue [successfulContinuation] [] := by
  simpa [runtimeSignature, clauses, successfulDataArm, exhaustiveDataArm,
    decompositionExpression, decompositionValue, targetValue, nilValue,
    dataEnvironment, primitiveResults, nextMatchersExpression,
    successfulContinuation, xAtom, restAtom, listOfV, decodeTuple] using
    (MAtom.matcher (SF := runtimeSignature)
      (ρ := []) (ρm := []) (original := clauses)
      (pattern := userPattern) (value := targetValue)
      (pp := generalPP "pair" 2) (next := nextMatchersExpression)
      (dp := DPat.ctor "pair" [.var "head", .var "tail"])
      (body := decompositionExpression)
      (arms := [exhaustiveDataArm]) (clauses := [catchAllClause])
      (holes := [.pvar "x", .pvar "rest"]) (ρp := [])
      (ρd := dataEnvironment) (decomposition := decompositionValue)
      (tuples := [.tuple [.lit 1, .lit 2]])
      (valueLists := [[.lit 1, .lit 2]])
      (matcherValue := .tuple [.something, .something])
      (matchers := [.something, .something]) rfl
      pair_primitive_pattern_success second_data_arm_success
      decomposition_evaluation rfl rfl next_matchers_evaluation rfl)

theorem after_empty_clause_reduction :
    MAtom runtimeSignature [] userPattern
      (.matcherV [] clauses [livePairClause, catchAllClause])
      targetValue [successfulContinuation] [] := by
  simpa [livePairClause, failingDataArm] using
    (MAtom.matcherDPFail (SF := runtimeSignature) rfl
      pair_primitive_pattern_success first_data_arm_failure
      successful_pair_reduction)

theorem ordered_matcher_reduction :
    MAtom runtimeSignature [] userPattern matcherValue targetValue
      [successfulContinuation] [] := by
  simpa [matcherValue, clauses, emptyClause] using
    (MAtom.matcherPPFail (SF := runtimeSignature) rfl
      empty_primitive_pattern_failure after_empty_clause_reduction)

def initialState : MState :=
  ⟨[.atom ⟨userPattern, matcherValue, targetValue⟩], [], []⟩

def continuationState : MState :=
  ⟨[.atom xAtom, .atom restAtom], [], []⟩

def xSubstitution : MatchSubst :=
  [("x", .lit 1)]

def restState : MState :=
  ⟨[.atom restAtom], [], xSubstitution⟩

def finalSubstitution : MatchSubst :=
  [("rest", .lit 2), ("x", .lit 1)]

def terminalState : MState :=
  ⟨[], [], finalSubstitution⟩

theorem dispatch_step :
    Step runtimeSignature initialState [continuationState] := by
  simpa [initialState, continuationState, successfulContinuation, xAtom,
    restAtom, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := []) ordered_matcher_reduction)

theorem x_reduction :
    MAtom runtimeSignature [] (.pvar "x") .something (.lit 1)
      [[]] xSubstitution := by
  simpa [xSubstitution] using
    (MAtom.someVar (SF := runtimeSignature) (ρ := [])
      (name := "x") (value := Value.lit 1))

theorem x_step :
    Step runtimeSignature continuationState [restState] := by
  simpa [continuationState, restState, xAtom, restAtom, xSubstitution,
    runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := [.atom restAtom])
      (ρ := []) (substitution := []) x_reduction)

theorem rest_reduction :
    MAtom runtimeSignature xSubstitution (.pvar "rest") .something (.lit 2)
      [[]] [("rest", .lit 2)] := by
  exact .someVar

theorem rest_step :
    Step runtimeSignature restState [terminalState] := by
  simpa [restState, terminalState, restAtom, xSubstitution,
    finalSubstitution, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := xSubstitution) rest_reduction)

theorem terminal_search :
    Search runtimeSignature terminalState [finalSubstitution] := by
  simpa [terminalState] using
    (Search.done (SF := runtimeSignature) (ρ := [])
      (substitution := finalSubstitution))

theorem rest_search :
    Search runtimeSignature restState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) rest_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact terminal_search
  · simp at member

theorem continuation_search :
    Search runtimeSignature continuationState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) x_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact rest_search
  · simp at member

theorem program_search :
    Search runtimeSignature initialState [finalSubstitution] := by
  refine Search.step (substitutions := [[finalSubstitution]]) dispatch_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact continuation_search
  · simp at member

theorem program_reaches_terminal :
    Reaches runtimeSignature initialState terminalState :=
  .step dispatch_step (by simp)
    (.step x_step (by simp)
      (.step rest_step (by simp) .refl))

theorem target_evaluation :
    Eval runtimeSignature [] targetExpression targetValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .lit
  · rcases member with rfl | member
    · exact .lit
    · simp at member

theorem matcher_evaluation :
    Eval runtimeSignature [] matcherExpression matcherValue := by
  exact .matcher

theorem result_evaluation :
    Eval runtimeSignature finalSubstitution
      (.tuple [.var "x", .var "rest"])
      (.tuple [.lit 1, .lit 2]) := by
  refine Eval.tuple rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .var (by rfl)
  · rcases member with rfl | member
    · exact .var (by rfl)
    · simp at member

theorem program_evaluation :
    Eval runtimeSignature [] program decompositionValue := by
  simpa [program, decompositionValue, nilValue, mkListV] using
    (Eval.matchAll (SF := runtimeSignature) (ρ := [])
      (target := targetExpression) (matcher := matcherExpression)
      (pattern := userPattern) (body := .tuple [.var "x", .var "rest"])
      (targetValue := targetValue) (matcherValue := matcherValue)
      (substitutions := [finalSubstitution])
      (values := [.tuple [.lit 1, .lit 2]]) target_evaluation
      matcher_evaluation program_search rfl (by
        intro pair member
        simp only [List.zip_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact result_evaluation
        · simp at member))

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] program).get (by native_decide)

/-- This accepted program needs the capability leaf produced by the `pair`
pattern constructor to remain structurally flexible until the enclosing
matcher-to-slot demand.  Freezing every child/result leaf at the local pattern
constructor cut would reject the later, valid `kappa -> Any` solve. -/
def pairPatternLeafStructuralizedAfterLocalCut : Bool :=
  inferenceResult.state.trace.events.any fun event =>
    match event with
    | .patternCtorCompatibility _ "pair" _ (.con "Pair" [.var leaf]) =>
        inferenceResult.state.prevailing.cap leaf == .any
    | _ => false

theorem pair_pattern_leaf_structuralized_after_local_cut :
    pairPatternLeafStructuralizedAfterLocalCut = true := by
  native_decide

theorem inference_success :
    Inference.infer signature [] program = some inferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

def programResult : Ty :=
  Ty.listT (.prod [.int, .int])

theorem inference_result_type :
    inferenceResult.resolvedTarget = programResult := by
  native_decide

theorem program_typed :
    RuntimeTyping signature [] program programResult := by
  have typing := Inference.infer_success_runtimeTyping inference_success
  rw [inference_result_type] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

theorem runtime_agrees (context : Context) :
    RuntimeSigAgrees signature context runtimeSignature where
  runtimeTyped := by
    intro entry member
    simp [runtimeSignature] at member
  sourceLookup := by
    intro name scheme found
    simp [signature, FrozenSig.findPatternFun] at found

theorem global_runtime_agreement :
    ∀ context, RuntimeSigAgrees signature context runtimeSignature :=
  runtime_agrees

def safetyPackage : CoreSafety signature runtimeSignature :=
  core_safety signature_wf

private theorem empty_environment_typed : EnvTyped signature [] [] := by
  intro name value found
  simp [Env.find?] at found

theorem target_evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature target_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement target_evaluation

theorem matcher_evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature matcher_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement matcher_evaluation

theorem program_evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature program_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement program_evaluation

theorem ordered_reduction_mirror :
    MAtomRuntimeSigAgrees signature runtimeSignature
      ordered_matcher_reduction :=
  MAtomRuntimeSigAgrees.of_global global_runtime_agreement
    ordered_matcher_reduction

theorem dispatch_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature dispatch_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement dispatch_step

theorem search_mirror :
    SearchRuntimeSigAgrees signature runtimeSignature program_search :=
  SearchRuntimeSigAgrees.of_global global_runtime_agreement program_search

theorem reachability_mirror :
    ReachesRuntimeSigAgrees signature runtimeSignature
      program_reaches_terminal :=
  ReachesRuntimeSigAgrees.of_global global_runtime_agreement
    program_reaches_terminal

theorem matcher_value_pristine : ValuePristine matcherValue := by
  exact .matcherLiteral .nil

theorem target_value_pristine : ValuePristine targetValue := by
  exact .ctor (.cons .lit (.cons .lit .nil))

theorem initial_atom_typed :
    ∃ goal, AtomTy signature [] [] []
      ⟨userPattern, matcherValue, targetValue⟩ goal := by
  cases program_typed with
  | matchAll targetTyping patternTyping matcherTyping bodyTyping =>
      have targetValueTyping := safetyPackage.evalPreservation
        target_evaluation_mirror EnvPristine.nil
        empty_environment_typed targetTyping
      have matcherValueTyping := safetyPackage.evalPreservation
        matcher_evaluation_mirror EnvPristine.nil
        empty_environment_typed matcherTyping
      exact ⟨_, .mk patternTyping
        (matcherValueTyping.toMatcherUsable signature_wf)
        targetValueTyping⟩

theorem program_value_typed :
    ValueTy signature decompositionValue programResult :=
  safetyPackage.evalPreservation program_evaluation_mirror
    EnvPristine.nil empty_environment_typed program_typed

theorem final_substitution_nonempty : finalSubstitution ≠ [] := by
  simp [finalSubstitution]

structure SharedGoalSafety (goal : MonoCtx) : Prop where
  initial : MStateTyAt signature [] [] initialState goal
  continuation : MStateTyAt signature [] [] continuationState goal
  terminal : MStateTyAt signature [] [] terminalState goal
  searched : MatchSubstTyped signature goal finalSubstitution
  consistent : MatchSubstTyped signature goal finalSubstitution

theorem shared_goal_safety : ∃ goal, SharedGoalSafety goal := by
  obtain ⟨goal, atomTyping⟩ := initial_atom_typed
  have initialTyping : MStateTyAt signature [] [] initialState goal := by
    simpa [initialState] using
      atomTyping.initialState_typed EnvPristine.nil matcher_value_pristine
        target_value_pristine empty_environment_typed
  have continuationTyping := safetyPackage.stepPreservation
    dispatch_step_mirror (runtime_agrees []) initialTyping
    continuationState (by simp)
  have terminalTyping := safetyPackage.reachesTyped
    reachability_mirror (runtime_agrees []) initialTyping
  have searchedTyping := safetyPackage.searchSubstitutionsTyped
    search_mirror (runtime_agrees []) initialTyping
    finalSubstitution (by simp)
  have consistentTyping := safetyPackage.matcherConsistency
    search_mirror (runtime_agrees []) EnvPristine.nil matcher_value_pristine
    target_value_pristine empty_environment_typed atomTyping
    finalSubstitution (by simp)
  exact ⟨goal, ⟨initialTyping, continuationTyping, terminalTyping,
    searchedTyping, consistentTyping⟩⟩

theorem initial_state_typed :
    ∃ goal, MStateTyAt signature [] [] initialState goal := by
  obtain ⟨goal, safety⟩ := shared_goal_safety
  exact ⟨goal, safety.initial⟩

theorem continuation_state_preserved :
    ∃ goal, MStateTyAt signature [] [] continuationState goal := by
  obtain ⟨goal, safety⟩ := shared_goal_safety
  exact ⟨goal, safety.continuation⟩

theorem terminal_state_preserved :
    ∃ goal, MStateTyAt signature [] [] terminalState goal := by
  obtain ⟨goal, safety⟩ := shared_goal_safety
  exact ⟨goal, safety.terminal⟩

theorem searched_substitution_typed :
    ∃ goal, MatchSubstTyped signature goal finalSubstitution := by
  obtain ⟨goal, safety⟩ := shared_goal_safety
  exact ⟨goal, safety.searched⟩

theorem matcher_consistent :
    ∃ goal, MatchSubstTyped signature goal finalSubstitution := by
  obtain ⟨goal, safety⟩ := shared_goal_safety
  exact ⟨goal, safety.consistent⟩

structure SafetyWitness : Prop where
  publicInference :
    Inference.infer signature [] program = some inferenceResult
  sourceTyping : RuntimeTyping signature [] program programResult
  orderedReduction :
    MAtom runtimeSignature [] userPattern matcherValue targetValue
      [successfulContinuation] []
  outerStep : Step runtimeSignature initialState [continuationState]
  reachesTerminal : Reaches runtimeSignature initialState terminalState
  finalSubstitutionNonempty : finalSubstitution ≠ []
  evaluationPreserved : ValueTy signature decompositionValue programResult
  sharedGoalSafety : ∃ goal, SharedGoalSafety goal

theorem dispatch_safety : SafetyWitness where
  publicInference := inference_success
  sourceTyping := program_typed
  orderedReduction := ordered_matcher_reduction
  outerStep := dispatch_step
  reachesTerminal := program_reaches_terminal
  finalSubstitutionNonempty := final_substitution_nonempty
  evaluationPreserved := program_value_typed
  sharedGoalSafety := shared_goal_safety

end TypedFixture
end DynamicDispatchRegression
end TypePM
