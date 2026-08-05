import TypePM.Safety

/-!
# Runtime-signature mirror construction

The derivation-local runtime-signature judgments in `Safety` deliberately
mirror the five mutually recursive operational judgments.  This module
closes their construction boundary: one source/runtime agreement valid for
every source context determines the mirror of every concrete operational
derivation.  No evaluation result, matching successor, or termination fact
is supplied by the agreement hypothesis.
-/

namespace TypePM

mutual

/-- Global source/runtime agreement constructs the exact mirror of a concrete
evaluation derivation. -/
theorem EvalRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {environment : Env} {expression : Expr} {value : Value}
    (evaluation : Eval SF environment expression value) :
    EvalRuntimeSigAgrees signature SF evaluation :=
  match evaluation with
  | .var found => .evar (found := found)
  | .lam => .elam
  | .fix => .efix
  | .app functionEvaluation argumentEvaluation bodyEvaluation =>
      .eapp (EvalRuntimeSigAgrees.of_global global functionEvaluation)
        (EvalRuntimeSigAgrees.of_global global argumentEvaluation)
        (EvalRuntimeSigAgrees.of_global global bodyEvaluation)
  | .lit => .elit
  | .tuple lengths evaluations =>
      .etuple (lengths := lengths)
        (fun pair member =>
          EvalRuntimeSigAgrees.of_global global (evaluations pair member))
  | @Eval.ctor _ _ name _ _ lengths evaluations =>
      .ector (name := name) (lengths := lengths)
        (fun pair member =>
          EvalRuntimeSigAgrees.of_global global (evaluations pair member))
  | @Eval.prim _ _ operation _ _ _ lengths evaluations primitive =>
      .eprim (operation := operation) (lengths := lengths)
        (primitive := primitive)
        (fun pair member =>
          EvalRuntimeSigAgrees.of_global global (evaluations pair member))
  | .letE boundEvaluation bodyEvaluation =>
      .elet (EvalRuntimeSigAgrees.of_global global boundEvaluation)
        (EvalRuntimeSigAgrees.of_global global bodyEvaluation)
  | .something => .esomething
  | .matcher => .ematcher
  | .matchAll targetEvaluation matcherEvaluation search lengths evaluations =>
      .ematchAll (lengths := lengths)
        (fun {context} {_result} _ _ => global context)
        (EvalRuntimeSigAgrees.of_global global targetEvaluation)
        (EvalRuntimeSigAgrees.of_global global matcherEvaluation)
        (SearchRuntimeSigAgrees.of_global global search)
        (fun pair member =>
          EvalRuntimeSigAgrees.of_global global (evaluations pair member))

/-- Global source/runtime agreement constructs the exact mirror of a concrete
primitive-pattern-pattern derivation. -/
theorem PPMRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {environment : Env} {pp : PPat} {pattern : Pattern}
    {result : Option (List Pattern × Env)}
    (matching : PPM SF environment pp pattern result) :
    PPMRuntimeSigAgrees signature SF matching :=
  match matching with
  | .hole => .phole
  | .wild => .pwild
  | .pval evaluation =>
      .ppval (EvalRuntimeSigAgrees.of_global global evaluation)
  | @PPM.ctor _ _ name _ _ _ lengthPP lengthResults matchings =>
      .pctor (name := name) (lengthPP := lengthPP)
        (lengthResults := lengthResults)
        (fun entry member =>
          PPMRuntimeSigAgrees.of_global global (matchings entry member))
  | .tuple lengthPP lengthResults matchings =>
      .ptuple (lengthPP := lengthPP) (lengthResults := lengthResults)
        (fun entry member =>
          PPMRuntimeSigAgrees.of_global global (matchings entry member))
  | .fail failed => .pfail (failed := failed)

/-- Global source/runtime agreement constructs the exact mirror of a concrete
matching-atom reduction. -/
theorem MAtomRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {environment : Env} {pattern : Pattern} {matcher value : Value}
    {continuations : List (List Atom)} {substitution : MatchSubst}
    (reduction : MAtom SF environment pattern matcher value continuations
      substitution) :
    MAtomRuntimeSigAgrees signature SF reduction :=
  match reduction with
  | .someWC => .msomeWC
  | .someVar => .msomeVar
  | .someValEq evaluation equal =>
      .msomeValEq (equal := equal)
        (EvalRuntimeSigAgrees.of_global global evaluation)
  | .someValNeq evaluation unequal =>
      .msomeValNeq (unequal := unequal)
        (EvalRuntimeSigAgrees.of_global global evaluation)
  | .and => .mand
  | .or => .mor
  | @MAtom.tuple _ runtimeEnvironment patterns matchers values patternLength
      valueLength =>
      .mtuple (environment := runtimeEnvironment) (patterns := patterns)
        (matchers := matchers) (values := values)
        (patternLength := patternLength) (valueLength := valueLength)
  | @MAtom.prodSome _ runtimeEnvironment userPattern matchers runtimeValue
      primitive =>
      .mprodSome (environment := runtimeEnvironment) (pattern := userPattern)
        (matchers := matchers) (value := runtimeValue) (primitive := primitive)
  | @MAtom.matcherPPFail _ environment matcherEnvironment original pattern
      value pp next arms clauses continuations substitution dispatch failure
      recursive =>
      .mppfail (environment := environment)
        (matcherEnvironment := matcherEnvironment) (original := original)
        (pattern := pattern) (value := value) (pp := pp) (next := next)
        (arms := arms) (clauses := clauses)
        (continuations := continuations) (substitution := substitution)
        (dispatch := dispatch)
        (PPMRuntimeSigAgrees.of_global global failure)
        (MAtomRuntimeSigAgrees.of_global global recursive)
  | @MAtom.matcherDPFail _ environment matcherEnvironment original pattern
      value pp next dp body arms clauses captures ppEnvironment continuations
      substitution dispatch ppSuccess dataFailure recursive =>
      .mdpfail (environment := environment)
        (matcherEnvironment := matcherEnvironment) (original := original)
        (pattern := pattern) (value := value) (pp := pp) (next := next)
        (dp := dp) (body := body) (arms := arms) (clauses := clauses)
        (captures := captures) (ppEnvironment := ppEnvironment)
        (continuations := continuations) (substitution := substitution)
        (dispatch := dispatch) (dataFailure := dataFailure)
        (PPMRuntimeSigAgrees.of_global global ppSuccess)
        (MAtomRuntimeSigAgrees.of_global global recursive)
  | @MAtom.matcher _ environment matcherEnvironment original pattern value pp
      next dp body arms clauses captures ppEnvironment dataEnvironment
      decomposition tuples valueLists matcherValue matchers dispatch ppSuccess
      dataSuccess bodyEvaluation listDecode tupleDecodes nextEvaluation
      matcherDecode =>
      .mmatcher (environment := environment)
        (matcherEnvironment := matcherEnvironment) (original := original)
        (pattern := pattern) (value := value) (pp := pp) (next := next)
        (dp := dp) (body := body) (arms := arms) (clauses := clauses)
        (captures := captures) (ppEnvironment := ppEnvironment)
        (dataEnvironment := dataEnvironment) (decomposition := decomposition)
        (tuples := tuples) (valueLists := valueLists)
        (matcherValue := matcherValue) (matchers := matchers)
        (dispatch := dispatch) (dataSuccess := dataSuccess)
        (listDecode := listDecode) (tupleDecodes := tupleDecodes)
        (matcherDecode := matcherDecode)
        (PPMRuntimeSigAgrees.of_global global ppSuccess)
        (EvalRuntimeSigAgrees.of_global global bodyEvaluation)
        (EvalRuntimeSigAgrees.of_global global nextEvaluation)

/-- Global source/runtime agreement constructs the exact mirror of a concrete
matching-state step. -/
theorem StepRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {state : MState} {states : List MState}
    (reduction : Step SF state states) :
    StepRuntimeSigAgrees signature SF reduction :=
  match reduction with
  | @Step.reduce _ stack environment substitution pattern matcher value
      continuations new atomReduction =>
      .sreduce (stack := stack) (environment := environment)
        (substitution := substitution) (pattern := pattern)
        (matcher := matcher) (value := value) (continuations := continuations)
        (new := new)
        (MAtomRuntimeSigAgrees.of_global global atomReduction)
  | @Step.patfunEnter _ stack environment substitution name arguments matcher
      value runtime found length =>
      .spatfunEnter (stack := stack) (environment := environment)
        (substitution := substitution) (name := name) (arguments := arguments)
        (matcher := matcher) (value := value) (runtime := runtime)
        (found := found) (length := length)
  | @Step.mnodeStep _ stack environment substitution tree innerStack
      innerEnvironment innerSubstitution parameters states guard inner =>
      .smnodeStep (stack := stack) (environment := environment)
        (substitution := substitution) (tree := tree) (innerStack := innerStack)
        (innerEnvironment := innerEnvironment)
        (innerSubstitution := innerSubstitution) (parameters := parameters)
        (states := states) (guard := guard)
        (StepRuntimeSigAgrees.of_global global inner)
  | @Step.mnodeVarpat _ stack environment substitution name pattern matcher
      value innerStack innerEnvironment innerSubstitution parameters found =>
      .smnodeVarpat (stack := stack) (environment := environment)
        (substitution := substitution) (name := name) (pattern := pattern)
        (matcher := matcher) (value := value) (innerStack := innerStack)
        (innerEnvironment := innerEnvironment)
        (innerSubstitution := innerSubstitution) (parameters := parameters)
        (found := found)
  | @Step.mnodeDone _ stack environment substitution innerEnvironment
      innerSubstitution parameters =>
      .smnodeDone (stack := stack) (environment := environment)
        (substitution := substitution) (innerEnvironment := innerEnvironment)
        (innerSubstitution := innerSubstitution) (parameters := parameters)

/-- Global source/runtime agreement constructs the exact mirror of a concrete
exhaustive-search derivation. -/
theorem SearchRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {state : MState} {substitutions : List MatchSubst}
    (search : Search SF state substitutions) :
    SearchRuntimeSigAgrees signature SF search :=
  match search with
  | .done => .sdone
  | .step reduction lengths searches =>
      .sstep (lengths := lengths)
        (StepRuntimeSigAgrees.of_global global reduction)
        (fun pair member =>
          SearchRuntimeSigAgrees.of_global global (searches pair member))

end

/-- Global source/runtime agreement also constructs the mirror of every
chosen concrete reachability branch. -/
theorem ReachesRuntimeSigAgrees.of_global
    {signature : FrozenSig} {SF : RuntimeSigF}
    (global : ∀ context, RuntimeSigAgrees signature context SF)
    {start finish : MState} (reachable : Reaches SF start finish) :
    ReachesRuntimeSigAgrees signature SF reachable := by
  induction reachable with
  | refl => exact .refl
  | step reduction member tail induction =>
      exact .step (member := member)
        (StepRuntimeSigAgrees.of_global global reduction) induction

end TypePM
