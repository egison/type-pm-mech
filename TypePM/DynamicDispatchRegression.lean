import TypePM.RecursiveExamples
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

end DynamicDispatchRegression
end TypePM
