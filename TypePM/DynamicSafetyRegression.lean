import TypePM.RuntimeAgreementBridge
import TypePM.CertifiedInference

/-!
# End-to-end dynamic-safety regression

This file instantiates the dynamic package once, from a concrete frozen
signature through an actual `matchAll` run.  The runtime pattern-function
signature is empty; the matcher literal itself nevertheless exercises
primitive-pattern matching, matcher-atom reduction, two state steps,
exhaustive search, and reachability to a terminal state.
-/

namespace TypePM
namespace DynamicSafetyRegression

/-! ## A concrete frozen list signature -/

def nilScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := []
  result := .data "List" [.var 0]

def consScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [.var 0, .data "List" [.var 0]]
  result := .data "List" [.var 0]

def signature : FrozenSig where
  observability := fun _ => none
  dataCtors := [("nil", nilScheme), ("cons", consScheme)]
  patternCtors := []
  patternFuns := []
  primitives := []
  constructorsByFormer := []
  armExhaustive := basicArmExhaustive

private theorem nil_inst (target : Ty) :
    nilScheme.Inst [] (Ty.listT target) := by
  refine ⟨CapSubst.id, Unification.TySubst.single 0 target,
    CapSubst.id_supportWithin [],
    Unification.TySubst.single_supportWithin 0 target, ?_, ?_⟩
  · rfl
  · simp [nilScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
      Unification.TySubst.single]

private theorem cons_inst (target : Ty) :
    consScheme.Inst [target, Ty.listT target] (Ty.listT target) := by
  refine ⟨CapSubst.id, Unification.TySubst.single 0 target,
    CapSubst.id_supportWithin [],
    Unification.TySubst.single_supportWithin 0 target, ?_, ?_⟩
  · simp [consScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
      Unification.TySubst.single]
  · simp [consScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList,
      Unification.TySubst.single]

@[simp] theorem find_nil :
    signature.findDataCtor "nil" = some nilScheme := by
  rfl

@[simp] theorem find_cons :
    signature.findDataCtor "cons" = some consScheme := by
  rfl

private theorem find_data_cases
    {name : String} {scheme : CtorScheme}
    (found : signature.findDataCtor name = some scheme) :
    (name = "nil" ∧ scheme = nilScheme) ∨
      (name = "cons" ∧ scheme = consScheme) := by
  by_cases nilName : name = "nil"
  · subst name
    have equality : nilScheme = scheme := by
      simpa using found
    exact .inl ⟨rfl, equality.symm⟩
  by_cases consName : name = "cons"
  · subst name
    have equality : consScheme = scheme := by
      simpa using found
    exact .inr ⟨rfl, equality.symm⟩
  · have notNil : "nil" ≠ name := fun equality => nilName equality.symm
    have notCons : "cons" ≠ name := fun equality => consName equality.symm
    simp [signature, FrozenSig.findDataCtor, notNil, notCons] at found

private theorem nil_inst_result
    {targets : List Ty} {result : Ty}
    (instanceTyping : nilScheme.Inst targets result) :
    ∃ target, targets = [] ∧ result = Ty.listT target := by
  rcases instanceTyping with
    ⟨capSubst, targetSubst, capSupport, targetSupport, argsEquality,
      resultEquality⟩
  refine ⟨targetSubst 0, ?_, ?_⟩
  · simpa [nilScheme] using argsEquality.symm
  · simpa [nilScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEquality.symm

private theorem cons_inst_result
    {targets : List Ty} {result : Ty}
    (instanceTyping : consScheme.Inst targets result) :
    ∃ target,
      targets = [target, Ty.listT target] ∧ result = Ty.listT target := by
  rcases instanceTyping with
    ⟨capSubst, targetSubst, capSupport, targetSupport, argsEquality,
      resultEquality⟩
  refine ⟨targetSubst 0, ?_, ?_⟩
  · simpa [consScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      argsEquality.symm
  · simpa [consScheme, Ty.listT, Subst.apply, Ty.applyCapability,
      Ty.applyCapabilityList, Ty.applyTarget, Ty.applyTargetList] using
      resultEquality.symm

/-- All dynamic frozen-signature obligations are inhabited by this concrete
`nil`/`cons` table. -/
theorem signature_wf : FrozenSigWF signature where
  listSigWF :=
    { nilDeclared := ⟨nilScheme, find_nil, nil_inst⟩
      consDeclared := ⟨consScheme, find_cons, cons_inst⟩ }
  patternFunNamesNodup := by simp [signature]
  dataResult := by
    intro name scheme targets result found instanceTyping
    rcases find_data_cases found with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨target, targetsEquality, resultEquality⟩ :=
        nil_inst_result instanceTyping
      exact ⟨"List", [target], resultEquality⟩
    · obtain ⟨target, targetsEquality, resultEquality⟩ :=
        cons_inst_result instanceTyping
      exact ⟨"List", [target], resultEquality⟩
  dataInstArgsUnique := by
    intro name scheme leftTargets rightTargets result found left right
    rcases find_data_cases found with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨leftTarget, leftTargetsEquality, leftResult⟩ :=
        nil_inst_result left
      obtain ⟨rightTarget, rightTargetsEquality, rightResult⟩ :=
        nil_inst_result right
      exact leftTargetsEquality.trans rightTargetsEquality.symm
    · obtain ⟨leftTarget, leftTargetsEquality, leftResult⟩ :=
        cons_inst_result left
      obtain ⟨rightTarget, rightTargetsEquality, rightResult⟩ :=
        cons_inst_result right
      have targetEquality : leftTarget = rightTarget := by
        simpa [Ty.listT] using leftResult.symm.trans rightResult
      subst rightTarget
      exact leftTargetsEquality.trans rightTargetsEquality.symm
  patternInstArgsUnique := by
    intro name entry leftTargets rightTargets result found
    simp [signature, FrozenSig.findPatternCtor] at found
  patternCapArgsUnique := by
    intro name entry leftCaps rightCaps result found
    simp [signature, FrozenSig.findPatternCtor] at found
  patternCtorIndexed := by
    intro name entry childCaps capability found
    simp [signature, FrozenSig.findPatternCtor] at found
  primEvalTyped := by
    intro operation scheme values targets result value found
    simp [signature, FrozenSig.findPrimitive] at found
  armExhaustiveBasic := rfl

/-! ## One concrete matcher run -/

/-- There are no runtime pattern functions in this regression. -/
def runtimeSignature : RuntimeSigF := []

/-- Empty source and runtime pattern-function tables agree in every context. -/
theorem runtime_agrees (context : Context) :
    RuntimeSigAgrees signature context runtimeSignature where
  runtimeTyped := by
    intro entry member
    simp [runtimeSignature] at member
  sourceLookup := by
    intro name scheme found
    simp [signature, FrozenSig.findPatternFun] at found

/-- The context-parametric premise consumed by the mirror bridge is concrete,
not an oracle attached separately to each operational derivation. -/
theorem global_runtime_agreement :
    ∀ context, RuntimeSigAgrees signature context runtimeSignature :=
  runtime_agrees

def decompositionExpression : Expr :=
  .ctor "cons" [.lit 0, .ctor "nil" []]

def decompositionValue : Value :=
  .ctor "cons" [.lit 0, .ctor "nil" []]

def clause : Clause :=
  .mk .hole .something [.mk (.var "whole") decompositionExpression]

def program : Expr :=
  .matchAll (.lit 7) (.matcher [clause]) .wild (.lit 1)

def matcherValue : Value :=
  .matcherV [] [clause] [clause]

def branchAtom : Atom :=
  ⟨.wild, .something, .lit 0⟩

def initialState : MState :=
  ⟨[.atom ⟨.wild, matcherValue, .lit 7⟩], [], []⟩

def branchState : MState :=
  ⟨[.atom branchAtom], [], []⟩

def terminalState : MState :=
  ⟨[], [], []⟩

def programValue : Value :=
  mkListV [.lit 1]

theorem decomposition_evaluation :
    Eval runtimeSignature [("whole", .lit 7)] decompositionExpression
      decompositionValue := by
  refine Eval.ctor rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .lit
  · rcases member with rfl | member
    · exact .ctor rfl (by simp)
    · simp at member

theorem primitive_pattern_matching :
    PPM runtimeSignature [] .hole .wild (some ([.wild], [])) :=
  .hole

theorem matcher_reduction :
    MAtom runtimeSignature [] .wild matcherValue (.lit 7)
      [[branchAtom]] [] := by
  simpa [runtimeSignature, matcherValue, clause, branchAtom,
    decompositionExpression, decompositionValue, listOfV, decodeTuple] using
    (MAtom.matcher (SF := runtimeSignature)
      (ρ := []) (ρm := []) (original := [clause])
      (pattern := Pattern.wild) (value := Value.lit 7)
      (pp := PPat.hole) (next := Expr.something) (dp := DPat.var "whole")
      (body := decompositionExpression) (arms := []) (clauses := [])
      (holes := [Pattern.wild]) (ρp := [])
      (ρd := [("whole", Value.lit 7)])
      (decomposition := decompositionValue) (tuples := [Value.lit 0])
      (valueLists := [[Value.lit 0]]) (matcherValue := Value.something)
      (matchers := [Value.something]) rfl primitive_pattern_matching rfl
      decomposition_evaluation rfl rfl Eval.something rfl)

theorem first_step :
    Step runtimeSignature initialState [branchState] := by
  simpa [initialState, branchState, matcherValue, branchAtom,
    runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := []) matcher_reduction)

theorem branch_reduction :
    MAtom runtimeSignature [] .wild .something (.lit 0) [[]] [] :=
  .someWC

theorem second_step :
    Step runtimeSignature branchState [terminalState] := by
  simpa [branchState, terminalState, branchAtom, runtimeSignature] using
    (Step.reduce (SF := runtimeSignature) (stack := []) (ρ := [])
      (substitution := []) branch_reduction)

theorem branch_search :
    Search runtimeSignature branchState [[]] := by
  refine Search.step (substitutions := [[[]]]) second_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .done
  · simp at member

theorem program_search :
    Search runtimeSignature initialState [[]] := by
  refine Search.step (substitutions := [[[]]]) first_step rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact branch_search
  · simp at member

theorem program_reaches_terminal :
    Reaches runtimeSignature initialState terminalState := by
  exact .step first_step (by simp)
    (.step second_step (by simp) .refl)

theorem program_evaluation :
    Eval runtimeSignature [] program programValue := by
  refine Eval.matchAll Eval.lit Eval.matcher program_search rfl ?_
  intro pair member
  simp only [List.zip_cons_cons, List.mem_cons] at member
  rcases member with rfl | member
  · exact .lit
  · simp at member

/-! ## Bridge construction and application of `CoreSafety` -/

def inferenceResult : Inference.ExprResult :=
  (Inference.infer signature [] program).get (by native_decide)

theorem inference_success :
    Inference.infer signature [] program = some inferenceResult := by
  exact Inference.option_eq_some_get_of_isSome _ (by native_decide)

/-- Pin the concrete result independently of the derivation reconstructed from
public inference, so a future change in W cannot silently widen this fixture. -/
theorem inferenceResult_target :
    inferenceResult.resolvedTarget = Ty.listT .int := by
  native_decide

theorem program_typed :
    HasTy signature [] program (Ty.listT .int) := by
  have typing := Inference.infer_success_sound inference_success
  rw [inferenceResult_target] at typing
  simpa [Inference.ResolvedContext, Context.applySubst] using typing

theorem evaluation_mirror :
    EvalRuntimeSigAgrees signature runtimeSignature program_evaluation :=
  EvalRuntimeSigAgrees.of_global global_runtime_agreement program_evaluation

theorem primitive_pattern_mirror :
    PPMRuntimeSigAgrees signature runtimeSignature
      primitive_pattern_matching :=
  PPMRuntimeSigAgrees.of_global global_runtime_agreement
    primitive_pattern_matching

theorem matcher_reduction_mirror :
    MAtomRuntimeSigAgrees signature runtimeSignature matcher_reduction :=
  MAtomRuntimeSigAgrees.of_global global_runtime_agreement matcher_reduction

theorem first_step_mirror :
    StepRuntimeSigAgrees signature runtimeSignature first_step :=
  StepRuntimeSigAgrees.of_global global_runtime_agreement first_step

theorem program_search_mirror :
    SearchRuntimeSigAgrees signature runtimeSignature program_search :=
  SearchRuntimeSigAgrees.of_global global_runtime_agreement program_search

theorem terminal_reachability_mirror :
    ReachesRuntimeSigAgrees signature runtimeSignature
      program_reaches_terminal :=
  ReachesRuntimeSigAgrees.of_global global_runtime_agreement
    program_reaches_terminal

def safetyPackage : CoreSafety signature runtimeSignature :=
  core_safety signature_wf

private theorem empty_environment_typed : EnvTyped signature [] [] := by
  intro name value found
  simp [Env.find?] at found

/-- The general `CoreSafety` package fires on the concrete evaluation and
returns a kernel-checked typing derivation for its actual runtime value. -/
theorem program_value_typed :
    ValueTy signature programValue (Ty.listT .int) :=
  safetyPackage.evalPreservation evaluation_mirror EnvPristine.nil
    empty_environment_typed program_typed

/-- One bundled witness makes the signature, global agreement, all concrete
operational layers, their automatically constructed mirrors, and the applied
safety conclusion simultaneously available. -/
structure EndToEndWitness : Prop where
  signatureWF : FrozenSigWF signature
  agreement : ∀ context,
    RuntimeSigAgrees signature context runtimeSignature
  evaluation : Eval runtimeSignature [] program programValue
  primitiveMatching :
    PPM runtimeSignature [] .hole .wild (some ([.wild], []))
  atomReduction :
    MAtom runtimeSignature [] .wild matcherValue (.lit 7) [[branchAtom]] []
  stateStep : Step runtimeSignature initialState [branchState]
  search : Search runtimeSignature initialState [[]]
  reaches : Reaches runtimeSignature initialState terminalState
  evaluationAgreement :
    EvalRuntimeSigAgrees signature runtimeSignature program_evaluation
  primitiveAgreement :
    PPMRuntimeSigAgrees signature runtimeSignature primitive_pattern_matching
  atomAgreement :
    MAtomRuntimeSigAgrees signature runtimeSignature matcher_reduction
  stepAgreement :
    StepRuntimeSigAgrees signature runtimeSignature first_step
  searchAgreement :
    SearchRuntimeSigAgrees signature runtimeSignature program_search
  reachesAgreement :
    ReachesRuntimeSigAgrees signature runtimeSignature
      program_reaches_terminal
  core : CoreSafety signature runtimeSignature
  resultTyped :
    ValueTy signature programValue (Ty.listT .int)

theorem end_to_end : EndToEndWitness where
  signatureWF := signature_wf
  agreement := global_runtime_agreement
  evaluation := program_evaluation
  primitiveMatching := primitive_pattern_matching
  atomReduction := matcher_reduction
  stateStep := first_step
  search := program_search
  reaches := program_reaches_terminal
  evaluationAgreement := evaluation_mirror
  primitiveAgreement := primitive_pattern_mirror
  atomAgreement := matcher_reduction_mirror
  stepAgreement := first_step_mirror
  searchAgreement := program_search_mirror
  reachesAgreement := terminal_reachability_mirror
  core := safetyPackage
  resultTyped := program_value_typed

end DynamicSafetyRegression
end TypePM
