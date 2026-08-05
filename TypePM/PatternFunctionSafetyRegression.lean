import TypePM.DynamicSafetyRegression

/-!
# Nonempty pattern-function safety regression

This file exercises the dynamic package with an actual runtime pattern-function
entry.  The closed, nullary `unit` definition expands to `ptuple []`, so source
and runtime signatures agree in every expression context without an ambient
freshness premise.  Its concrete run enters a pattern-function node, reduces
the empty tuple match inside that node, removes the completed node, and reaches
a terminal matching state.

Unlike the smaller empty-signature regression, this fixture applies every
field of `CoreSafety` to a concrete derivation.  In particular the terminal
search substitution is passed to both `searchSubstitutionsTyped` and
`matcherConsistency` through its actual list-membership proof.
-/

namespace TypePM
namespace PatternFunctionSafetyRegression

/-! ## Closed source and runtime pattern-function signatures -/

def unitResult : Dual :=
  ⟨.prod [], .prod []⟩

def unitScheme : DualScheme where
  capBinders := []
  tyBinders := []
  args := []
  result := unitResult

def unitDefinition : PatternDef where
  name := "unit"
  parameters := []
  body := .ptuple []

/-- Extend the concrete list signature with one closed pattern function. -/
def signature : FrozenSig :=
  { DynamicSafetyRegression.signature with
    patternFuns := [("unit", unitScheme)] }

@[simp] theorem find_unit :
    signature.findPatternFun "unit" = some unitScheme := by
  rfl

/-- The nullary definition is checked independently of the ambient context. -/
theorem unit_definition_typed (context : Context) :
    PatternDefTy signature context unitDefinition unitScheme := by
  refine @PatternDefTy.mk signature context unitDefinition [] unitResult []
    unitScheme find_unit ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · rfl
  · simp [PatternDef.parameterNames, unitDefinition]
  · intro capability member
    simp at member
  · simp
  · exact PatternTy.tuple PatternTys.nil
  · rfl
  · rfl

private theorem find_data_ctor_eq (name : String) :
    signature.findDataCtor name =
      DynamicSafetyRegression.signature.findDataCtor name := by
  rfl

/-- Adding a pattern-function table leaves the concrete data/primitive
obligations unchanged and gives a singleton, unshadowed function namespace. -/
theorem signature_wf : FrozenSigWF signature where
  listSigWF := by
    rcases DynamicSafetyRegression.signature_wf.listSigWF with
      ⟨⟨nilScheme, nilFound, nilInstances⟩,
        ⟨consScheme, consFound, consInstances⟩⟩
    exact
      ⟨⟨nilScheme, by simpa only [find_data_ctor_eq] using nilFound,
          nilInstances⟩,
        ⟨consScheme, by simpa only [find_data_ctor_eq] using consFound,
          consInstances⟩⟩
  patternFunNamesNodup := by
    simp [signature]
  dataResult := by
    intro name scheme targets result found instantiated
    apply DynamicSafetyRegression.signature_wf.dataResult
      (name := name) (scheme := scheme) (targets := targets)
      (result := result)
      (by simpa only [find_data_ctor_eq] using found) instantiated
  dataInstArgsUnique := by
    intro name scheme leftTargets rightTargets result found left right
    apply DynamicSafetyRegression.signature_wf.dataInstArgsUnique
      (name := name) (scheme := scheme) (result := result)
      (by simpa only [find_data_ctor_eq] using found) left right
  patternInstArgsUnique := by
    intro name entry leftTargets rightTargets result found
    simp [signature, DynamicSafetyRegression.signature,
      FrozenSig.findPatternCtor] at found
  patternCapArgsUnique := by
    intro name entry leftCaps rightCaps result found
    simp [signature, DynamicSafetyRegression.signature,
      FrozenSig.findPatternCtor] at found
  patternCtorIndexed := by
    intro name entry childCaps capability found
    simp [signature, DynamicSafetyRegression.signature,
      FrozenSig.findPatternCtor] at found
  primEvalTyped := by
    intro operation scheme values targets result value found
    simp [signature, DynamicSafetyRegression.signature,
      FrozenSig.findPrimitive] at found
  armExhaustiveBasic := rfl

def runtimeSignature : RuntimeSigF :=
  [("unit", unitDefinition.runtime)]

/-- The runtime table contains exactly the erasure of the checked source
definition, and source lookup returns that same runtime entry. -/
theorem runtime_agrees (context : Context) :
    RuntimeSigAgrees signature context runtimeSignature where
  runtimeTyped := by
    intro entry member
    simp only [runtimeSignature, List.mem_singleton] at member
    subst entry
    exact ⟨unitDefinition, unitScheme, rfl, unit_definition_typed context⟩
  sourceLookup := by
    intro name scheme found
    by_cases unitName : name = "unit"
    · subst name
      have schemeEquality : scheme = unitScheme :=
        (Option.some.inj (find_unit.symm.trans found)).symm
      subst scheme
      exact ⟨unitDefinition, rfl, rfl, unit_definition_typed context⟩
    · have reverseName : "unit" ≠ name :=
        fun equality => unitName equality.symm
      simp [signature, FrozenSig.findPatternFun, reverseName] at found

theorem global_runtime_agreement :
    ∀ context, RuntimeSigAgrees signature context runtimeSignature :=
  runtime_agrees

/-! ## Concrete execution through a pattern-function node -/

def program : Expr :=
  .matchAll (.tuple []) (.var "tupleMatcher") (.papp "unit" []) (.lit 1)

def tupleMatcherType : Ty :=
  .slot (.prod []) (.prod [])

def programContext : Context :=
  [("tupleMatcher", Scheme.mono tupleMatcherType)]

def programEnvironment : Env :=
  [("tupleMatcher", .tuple [])]

def programValue : Value :=
  mkListV [.lit 1]

def initialAtom : Atom :=
  ⟨.papp "unit" [], .tuple [], .tuple []⟩

def innerAtom : Atom :=
  ⟨.ptuple [], .tuple [], .tuple []⟩

def initialState : MState :=
  ⟨[.atom initialAtom], programEnvironment, []⟩

def nodeState : MState :=
  ⟨[.mnode [.atom innerAtom] programEnvironment [] []],
    programEnvironment, []⟩

def emptyNodeState : MState :=
  ⟨[.mnode [] programEnvironment [] []], programEnvironment, []⟩

def terminalState : MState :=
  ⟨[], programEnvironment, []⟩

theorem pattern_function_step :
    Step runtimeSignature initialState [nodeState] := by
  simpa [runtimeSignature, unitDefinition, PatternDef.runtime, initialState,
    initialAtom, nodeState, innerAtom, programEnvironment] using
    (Step.patfunEnter (SF := runtimeSignature) (stack := [])
      (ρ := programEnvironment)
      (substitution := []) (name := "unit") (args := [])
      (matcher := Value.tuple []) (value := Value.tuple [])
      (signature := unitDefinition.runtime) rfl rfl)

theorem inner_atom_reduction :
    MAtom runtimeSignature programEnvironment (.ptuple []) (.tuple [])
      (.tuple []) [[]] [] :=
  .tuple rfl rfl

theorem inner_step :
    Step runtimeSignature
      ⟨[.atom innerAtom], programEnvironment, []⟩ [terminalState] := by
  simpa [innerAtom, terminalState, programEnvironment] using
    (Step.reduce (SF := runtimeSignature) (stack := [])
      (ρ := programEnvironment)
      (substitution := []) inner_atom_reduction)

theorem node_reduction_step :
    Step runtimeSignature nodeState [emptyNodeState] := by
  simpa [nodeState, emptyNodeState, innerAtom, terminalState] using
    (Step.mnodeStep (SF := runtimeSignature) (stack := [])
      (ρ := programEnvironment)
      (substitution := []) (tree := Tree.atom innerAtom) (innerStack := [])
      (ρf := programEnvironment) (θf := []) (piE := [])
      (by
        intro name matcher value equality
        simp [innerAtom] at equality)
      inner_step)

theorem node_done_step :
    Step runtimeSignature emptyNodeState [terminalState] := by
  simpa [emptyNodeState, terminalState] using
    (Step.mnodeDone (SF := runtimeSignature) (stack := [])
      (ρ := programEnvironment) (substitution := [])
      (ρf := programEnvironment) (θf := []) (piE := []))

theorem terminal_search :
    Search runtimeSignature terminalState [[]] := by
  simpa [terminalState] using
    (Search.done (SF := runtimeSignature) (ρ := programEnvironment)
      (substitution := []))

theorem empty_node_search :
    Search runtimeSignature emptyNodeState [[]] := by
  refine Search.step (substitutions := [[[]]]) node_done_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact terminal_search
  · simp at member

theorem node_search :
    Search runtimeSignature nodeState [[]] := by
  refine Search.step (substitutions := [[[]]]) node_reduction_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact empty_node_search
  · simp at member

theorem program_search :
    Search runtimeSignature initialState [[]] := by
  refine Search.step (substitutions := [[[]]]) pattern_function_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact node_search
  · simp at member

theorem program_reaches_terminal :
    Reaches runtimeSignature initialState terminalState := by
  exact .step pattern_function_step (by simp)
    (.step node_reduction_step (by simp)
      (.step node_done_step (by simp) .refl))

theorem target_evaluation :
    Eval runtimeSignature programEnvironment (.tuple []) (.tuple []) :=
  .tuple rfl (by simp)

theorem matcher_evaluation :
    Eval runtimeSignature programEnvironment (.var "tupleMatcher")
      (.tuple []) := by
  exact .var (by rfl)

theorem program_evaluation :
    Eval runtimeSignature programEnvironment program programValue := by
  refine Eval.matchAll target_evaluation matcher_evaluation program_search rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact Eval.lit
  · simp at member

/-! ## Public inference and concrete state typing -/

private theorem option_eq_some_get_of_isSome {alpha : Type}
    (value : Option alpha) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => simp at present
  | some result => rfl

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature programContext program).get (by native_decide)

theorem inference_success :
    Inference.infer signature programContext program = some inferenceResult := by
  exact option_eq_some_get_of_isSome _ (by native_decide)

/-- Pin the public W result rather than leaving the preservation conclusion at
an opaque inferred target. -/
theorem inference_result_type :
    inferenceResult.resolvedTarget = Ty.listT .int := by
  native_decide

theorem inference_resolved_context :
    Inference.ResolvedContext inferenceResult.state.prevailing
      programContext = programContext := by
  native_decide

theorem program_typed :
    HasTy signature programContext program inferenceResult.resolvedTarget := by
  rw [← inference_resolved_context]
  exact Inference.infer_success_sound inference_success

theorem unit_value_flow_instance :
    unitScheme.ValueFlowInst [] unitResult := by
  refine ⟨CapSubst.id, TySubst.id, ?_⟩
  refine
    { capSupport := CapSubst.id_supportWithin []
      tySupport := TySubst.id_supportWithin []
      capBinderVariable := ?_
      argsResult := ?_
      resultResult := ?_ }
  · intro varId member
    exact (List.not_mem_nil member).elim
  · rfl
  · simp [unitScheme, unitResult, Dual.apply]

theorem initial_pattern_typed :
    ResolvedPatternTy signature Subst.id programContext [] []
      (.papp "unit" [])
      (.prod []) (.prod []) [] := by
  exact .ofTerminal
    (.app find_unit TerminalPatternResolutions.nil unit_value_flow_instance)

theorem matcher_value_typed :
    ValueTy signature (.tuple []) (.matcher (.prod []) (.prod [])) :=
  .matcherProduct (duals := []) .nil

theorem target_value_typed :
    ValueTy signature (.tuple []) (.prod []) :=
  .tuple .nil

theorem initial_atom_typed :
    AtomTy signature programContext [] [] initialAtom [] := by
  exact .mk initial_pattern_typed (.inl matcher_value_typed)
    target_value_typed

theorem empty_environment_typed : EnvTyped signature [] [] := by
  intro name value found
  simp [Env.find?] at found

theorem program_environment_pristine : EnvPristine programEnvironment := by
  exact .cons (.tuple .nil) .nil

theorem program_environment_typed :
    EnvTyped signature programContext programEnvironment := by
  simpa [programContext, programEnvironment, tupleMatcherType] using
    (EnvTyped.cons (signature := signature)
      (context := []) (environment := [])
      (name := "tupleMatcher") (value := Value.tuple [])
      (target := tupleMatcherType)
      (ValueTy.slotProduct (signature := signature) (duals := []) ValueTys.nil)
      empty_environment_typed)

theorem initial_state_typed :
    MStateTyAt signature programContext [] initialState [] := by
  refine ⟨?_, ?_, program_environment_typed, [],
    matchSubstTyped_nil signature, ?_⟩
  · exact ⟨
      .cons (.atom ⟨.tuple .nil, .tuple .nil⟩) .nil,
      program_environment_pristine, .nil⟩
  · rfl
  · exact .cons (.atom initial_atom_typed) .nil

/-! ## All six `CoreSafety` consequences -/

def safetyPackage : CoreSafety signature runtimeSignature :=
  core_safety signature_wf

theorem evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature program_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement program_evaluation

theorem first_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature pattern_function_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement
    pattern_function_step

theorem inner_atom_mirror :
    MAtomRuntimeSigAgrees signature runtimeSignature inner_atom_reduction :=
  MAtomRuntimeSigAgrees.of_global global_runtime_agreement
    inner_atom_reduction

theorem node_reduction_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature node_reduction_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement
    node_reduction_step

theorem node_done_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature node_done_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement node_done_step

theorem program_search_mirror :
    SearchRuntimeSigAgrees signature runtimeSignature program_search :=
  SearchRuntimeSigAgrees.of_global global_runtime_agreement program_search

theorem terminal_reachability_mirror :
    ReachesRuntimeSigAgrees signature runtimeSignature
      program_reaches_terminal :=
  ReachesRuntimeSigAgrees.of_global global_runtime_agreement
    program_reaches_terminal

/-- `CoreSafety.evalPreservation`, specialized to the pinned public result. -/
theorem program_value_typed :
    ValueTy signature programValue (Ty.listT .int) := by
  rw [← inference_result_type]
  exact safetyPackage.evalPreservation evaluation_mirror
    program_environment_pristine program_environment_typed program_typed

/-- `CoreSafety.stepPreservation` on the actual pattern-function entry step. -/
theorem node_state_typed :
    MStateTyAt signature programContext [] nodeState [] :=
  safetyPackage.stepPreservation first_step_mirror
    (runtime_agrees programContext)
    initial_state_typed nodeState (by simp)

/-- `CoreSafety.localProgress` consumes only syntax-directed readiness and the
checked initial state; it produces a pattern-function step. -/
theorem initial_state_progress :
    ∃ states, Step runtimeSignature initialState states :=
  safetyPackage.localProgress (runtime_agrees programContext)
    StepReady.patfun initial_state_typed

/-- `CoreSafety.reachesTyped` transports the same goal through all three
operational steps. -/
theorem terminal_state_typed :
    MStateTyAt signature programContext [] terminalState [] :=
  safetyPackage.reachesTyped terminal_reachability_mirror
    (runtime_agrees programContext) initial_state_typed

/-- `CoreSafety.searchSubstitutionsTyped` is applied to the substitution that
actually occurs in the concrete search result. -/
theorem searched_substitution_typed :
    MatchSubstTyped signature [] [] :=
  safetyPackage.searchSubstitutionsTyped program_search_mirror
    (runtime_agrees programContext) initial_state_typed [] (by simp)

/-- `CoreSafety.matcherConsistency` independently types that same concrete
search member from the initial atom boundary. -/
theorem consistent_substitution_typed :
    MatchSubstTyped signature [] [] :=
  safetyPackage.matcherConsistency program_search_mirror
    (runtime_agrees programContext) program_environment_pristine
    (.tuple .nil) (.tuple .nil) program_environment_typed
    initial_atom_typed [] (by simp)

/-- A single witness records that the nonempty source/runtime lookup and all
six public safety consequences are simultaneously instantiated. -/
structure AllSafetyFieldsWitness : Prop where
  signatureWF : FrozenSigWF signature
  sourceRuntimeAgreement : ∀ context,
    RuntimeSigAgrees signature context runtimeSignature
  nonemptyRuntime : runtimeSignature ≠ []
  inferredTarget : inferenceResult.resolvedTarget = Ty.listT .int
  evaluation : Eval runtimeSignature programEnvironment program programValue
  entersPatternFunction : Step runtimeSignature initialState [nodeState]
  reducesInsideNode : Step runtimeSignature nodeState [emptyNodeState]
  removesCompletedNode : Step runtimeSignature emptyNodeState [terminalState]
  reachesTerminal : Reaches runtimeSignature initialState terminalState
  enterAgreement :
    StepRuntimeSigAgrees signature runtimeSignature pattern_function_step
  innerAtomAgreement :
    MAtomRuntimeSigAgrees signature runtimeSignature inner_atom_reduction
  nestedStepAgreement :
    StepRuntimeSigAgrees signature runtimeSignature node_reduction_step
  doneStepAgreement :
    StepRuntimeSigAgrees signature runtimeSignature node_done_step
  evalPreserved : ValueTy signature programValue (Ty.listT .int)
  stepPreserved : MStateTyAt signature programContext [] nodeState []
  progress : ∃ states, Step runtimeSignature initialState states
  reachesPreserved : MStateTyAt signature programContext [] terminalState []
  searchedSubstitution : MatchSubstTyped signature [] []
  consistentSubstitution : MatchSubstTyped signature [] []

theorem all_safety_fields : AllSafetyFieldsWitness where
  signatureWF := signature_wf
  sourceRuntimeAgreement := global_runtime_agreement
  nonemptyRuntime := by simp [runtimeSignature]
  inferredTarget := inference_result_type
  evaluation := program_evaluation
  entersPatternFunction := pattern_function_step
  reducesInsideNode := node_reduction_step
  removesCompletedNode := node_done_step
  reachesTerminal := program_reaches_terminal
  enterAgreement := first_step_mirror
  innerAtomAgreement := inner_atom_mirror
  nestedStepAgreement := node_reduction_step_mirror
  doneStepAgreement := node_done_step_mirror
  evalPreserved := program_value_typed
  stepPreserved := node_state_typed
  progress := initial_state_progress
  reachesPreserved := terminal_state_typed
  searchedSubstitution := searched_substitution_typed
  consistentSubstitution := consistent_substitution_typed

end PatternFunctionSafetyRegression
end TypePM
