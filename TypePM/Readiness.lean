import TypePM.Safety

/-!
# Readiness from typing and embedded convergence

`StepReady`/`MAtomReady` bundle three kinds of facts: convergence of the
expression evaluations embedded in one dispatch step, success of the
decompression decodes, and reachability of a successful clause and arm.
This module discharges the latter two from the typing evidence, so local
progress needs only the honest semantic residue: the embedded evaluations
converge (with their derivation-local runtime-signature agreement).

Dispatch reachability needs no coverage: the mandatory final bare-hole
catch-all shape-matches every dispatchable pattern, and the frozen data-arm
exhaustiveness checker guarantees an irrefutable arm.  Coverage remains a
preservation-side concern.  Decode success follows from evaluation
preservation together with the canonical-form totality lemmas
(`listOfV_isSome`, `decodeTuple_isSome`) enabled by
`FrozenSigWF.listCtorsExclusive`.

The public corollary is `MStateTy.progress_of_evals`: a typed nonterminal
top-level matching state whose embedded evaluations converge takes one
concrete step.
-/

namespace TypePM

/-! ## Agreed embedded evaluations -/

/-- One convergent embedded evaluation together with its derivation-local
runtime-signature agreement. -/
def AgreedEval (signature : FrozenSig) (SF : RuntimeSigF)
    (environment : Env) (expression : Expr) : Prop :=
  ∃ value, ∃ evaluation : Eval SF environment expression value,
    EvalRuntimeSigAgrees signature SF evaluation

/-! ## Dispatch-site convergence -/

/--
Convergence of exactly the expression evaluations embedded in one
matcher-dispatch site: the captured value-pattern expressions of each
shape-compatible clause, and the decomposition body and next-matcher
expression of each arm able to receive the matched value.
-/
structure MatcherDispatchEvals (signature : FrozenSig) (SF : RuntimeSigF)
    (environment matcherEnvironment : Env) (pattern : Pattern)
    (value : Value) (clauses : List Clause) : Prop where
  captures :
    ∀ clause ∈ clauses, ppShapeOK clause.pp pattern = true →
      ∀ expression ∈ capturedExprs clause.pp pattern,
        AgreedEval signature SF environment expression
  bodies :
    ∀ clause ∈ clauses, ppShapeOK clause.pp pattern = true →
      ∀ {captures : List Pattern} {ppEnvironment : Env},
        PPM SF environment clause.pp pattern
          (some (captures, ppEnvironment)) →
        ∀ arm ∈ clause.arms, ∀ {dataEnvironment : Env},
          pdMatch arm.pat value = some dataEnvironment →
          AgreedEval signature SF
            (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
            arm.body
  nexts :
    ∀ clause ∈ clauses, ppShapeOK clause.pp pattern = true →
      AgreedEval signature SF matcherEnvironment clause.next

/-- Convergence of the expression evaluations embedded in one atom's
single-step dispatch: the value-pattern expression against `something`, and
the matcher-clause dispatch evaluations against a matcher literal.  All other
atom reductions embed no evaluation. -/
structure AtomEvals (signature : FrozenSig) (SF : RuntimeSigF)
    (environment : Env) (atom : Atom) : Prop where
  pval :
    ∀ expression, atom.p = .pval expression → atom.m = .something →
      AgreedEval signature SF environment expression
  dispatch :
    ∀ matcherEnvironment original current,
      atom.m = .matcherV matcherEnvironment original current →
      MatcherDispatchEvals signature SF environment matcherEnvironment
        atom.p atom.v current

/-- Embedded-evaluation convergence for the head position of one matching
state.  An embedded-parameter head needs no evaluation: its step is provided
by the enclosing node. -/
inductive TreeEvals (signature : FrozenSig) (SF : RuntimeSigF) :
    Env → Tree → Prop where
  | atom {environment : Env} {atom : Atom} :
      AtomEvals signature SF environment atom →
      TreeEvals signature SF environment (.atom atom)
  | embed {environment : Env} {name : String} {matcher value : Value} :
      TreeEvals signature SF environment
        (.atom ⟨.embed name, matcher, value⟩)
  | mnodeNil {environment innerEnvironment : Env}
      {innerSubstitution : MatchSubst} {piE : PiEnv} :
      TreeEvals signature SF environment
        (.mnode [] innerEnvironment innerSubstitution piE)
  | mnodeCons {environment : Env} {tree : Tree} {innerStack : List Tree}
      {innerEnvironment : Env} {innerSubstitution : MatchSubst}
      {piE : PiEnv} :
      TreeEvals signature SF
        (innerSubstitution ++ innerEnvironment) tree →
      TreeEvals signature SF environment
        (.mnode (tree :: innerStack) innerEnvironment innerSubstitution piE)

/-- Embedded-evaluation convergence at the head of one matching state. -/
def StateEvals (signature : FrozenSig) (SF : RuntimeSigF)
    (state : MState) : Prop :=
  ∀ tree rest, state.S = tree :: rest →
    TreeEvals signature SF (state.θ ++ state.ρ) tree

/-! ## PPM construction from capture admissibility -/

/--
Build a successful primitive-pattern match from capture admissibility and
convergence of the captured expressions, returning the typed and pristine
capture environment at the admissible binding context.
-/
theorem ppm_of_captureAdm
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {input : MonoCtx}
    {environment : Env}
    (environmentPristine : EnvPristine environment)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    {pp : PPat} {pattern : Pattern} {target : Ty} {bindings : MonoCtx}
    (admissible :
      CaptureAdm signature context input pp pattern target bindings)
    (evals : ∀ expression ∈ capturedExprs pp pattern,
      AgreedEval signature SF environment expression) :
    ∃ captures ppEnvironment,
      PPM SF environment pp pattern (some (captures, ppEnvironment)) ∧
      MonoEnvTys signature bindings ppEnvironment ∧
      EnvPristine ppEnvironment := by
  refine CaptureAdm.rec
    (motive_1 := fun pp pattern target bindings _ =>
      (∀ expression ∈ capturedExprs pp pattern,
        AgreedEval signature SF environment expression) →
      ∃ captures ppEnvironment,
        PPM SF environment pp pattern (some (captures, ppEnvironment)) ∧
        MonoEnvTys signature bindings ppEnvironment ∧
        EnvPristine ppEnvironment)
    (motive_2 := fun pps patterns targets bindings _ =>
      (∀ expression ∈ capturedExprsList pps patterns,
        AgreedEval signature SF environment expression) →
      ∃ results : List (List Pattern × Env),
        pps.length = patterns.length ∧
        (pps.zip patterns).length = results.length ∧
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) ∧
        MonoEnvTys signature bindings ((results.map Prod.snd).flatten) ∧
        EnvPristine ((results.map Prod.snd).flatten))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ admissible evals
  · intro pattern target _
    exact ⟨[pattern], [], .hole, .nil, .nil⟩
  · intro target _
    exact ⟨[], [], .wild, .nil, .nil⟩
  · intro name expression target expressionTyping evals
    obtain ⟨value, evaluation, agreement⟩ :=
      evals expression (by simp [capturedExprs])
    refine ⟨[], [(name, value)], .pval evaluation, ?_, ?_⟩
    · exact .cons (EvalRuntimeSigAgrees.preservation signatureWF agreement
        environmentPristine environmentTyping expressionTyping) .nil
    · exact .cons (EvalRuntimeSigAgrees.pristine signatureWF agreement
        environmentPristine) .nil
  · intro name entry pps patterns targets result bindings find children
      instantiation childrenIH evals
    obtain ⟨results, lengthPP, lengthResults, pointwise, bindingsTyped,
        bindingsPristine⟩ :=
      childrenIH (fun expression membership =>
        evals expression (by simpa [capturedExprs] using membership))
    exact ⟨(results.map (·.1)).flatten, (results.map (·.2)).flatten,
      .ctor lengthPP lengthResults pointwise, bindingsTyped, bindingsPristine⟩
  · intro pps patterns targets bindings children childrenIH evals
    obtain ⟨results, lengthPP, lengthResults, pointwise, bindingsTyped,
        bindingsPristine⟩ :=
      childrenIH (fun expression membership =>
        evals expression (by simpa [capturedExprs] using membership))
    exact ⟨(results.map (·.1)).flatten, (results.map (·.2)).flatten,
      .tuple lengthPP lengthResults pointwise, bindingsTyped, bindingsPristine⟩
  · intro _
    refine ⟨[], rfl, rfl, ?_, MonoEnvTys.nil, EnvPristine.nil⟩
    intro entry membership
    exact absurd membership (by simp)
  · intro pp pattern target bindings pps patterns targets restBindings head
      tail headIH tailIH evals
    obtain ⟨captures, ppEnvironment, headPPM, headTyped, headPristine⟩ :=
      headIH (fun expression membership =>
        evals expression (by
          simp only [capturedExprsList, List.mem_append]
          exact .inl membership))
    obtain ⟨results, lengthPP, lengthResults, pointwise, tailTyped,
        tailPristine⟩ :=
      tailIH (fun expression membership =>
        evals expression (by
          simp only [capturedExprsList, List.mem_append]
          exact .inr membership))
    refine ⟨(captures, ppEnvironment) :: results, by simp [lengthPP],
      by simp [List.zip_cons_cons, lengthResults], ?_, ?_, ?_⟩
    · intro entry membership
      rw [List.zip_cons_cons, List.zip_cons_cons] at membership
      rcases List.mem_cons.mp membership with rfl | membership
      · exact headPPM
      · exact pointwise entry membership
    · simpa [List.flatten_cons] using headTyped.append tailTyped
    · simpa [List.flatten_cons] using headPristine.append tailPristine

/-! ## Arm reachability -/

/-- The first data arm able to receive the value, with its failing prefix. -/
theorem arms_first_success {value : Value} :
    ∀ {arms : List Arm},
      (∃ arm ∈ arms, ∃ environment,
        pdMatch arm.pat value = some environment) →
      ∃ failed matched environment rest,
        arms = failed ++ matched :: rest ∧
        (∀ arm ∈ failed, pdMatch arm.pat value = none) ∧
        pdMatch matched.pat value = some environment
  | [], witness => by
      rcases witness with ⟨arm, membership, _⟩
      cases membership
  | arm :: arms, witness => by
      cases headMatch : pdMatch arm.pat value with
      | some environment =>
          refine ⟨[], arm, environment, arms, rfl, ?_, headMatch⟩
          intro candidate membership
          exact absurd membership (by simp)
      | none =>
          have tailWitness : ∃ candidate ∈ arms, ∃ environment,
              pdMatch candidate.pat value = some environment := by
            rcases witness with ⟨candidate, membership, environment, matched⟩
            rcases List.mem_cons.mp membership with rfl | membership
            · rw [headMatch] at matched
              cases matched
            · exact ⟨candidate, membership, environment, matched⟩
          obtain ⟨failed, matched, environment, rest, armsEq, failedAll,
              matchedSome⟩ := arms_first_success tailWitness
          refine ⟨arm :: failed, matched, environment, rest,
            by simp [armsEq], ?_, matchedSome⟩
          intro candidate membership
          rcases List.mem_cons.mp membership with rfl | membership
          · exact headMatch
          · exact failedAll candidate membership

/-- Chain data-arm failures below a ready successful arm of one clause. -/
theorem matcherDPFail_chain
    {SF : RuntimeSigF} {environment matcherEnvironment : Env}
    {pattern : Pattern} {value : Value} {original rest : List Clause}
    {pp : PPat} {next : Expr}
    (dispatchable : pattern.isMatcherDispatchable = true)
    {captures : List Pattern} {ppEnvironment : Env}
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment))) :
    ∀ {failed arms : List Arm},
      (∀ arm ∈ failed, pdMatch arm.pat value = none) →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original (.mk pp next arms :: rest))
        value →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original
          (.mk pp next (failed ++ arms) :: rest)) value
  | [], _, _, base => base
  | arm :: failed, arms, failedAll, base => by
      obtain ⟨dp, body⟩ := arm
      exact .matcherDPFail dispatchable matching
        (failedAll (.mk dp body) List.mem_cons_self)
        (matcherDPFail_chain dispatchable matching
          (fun candidate membership =>
            failedAll candidate (List.mem_cons_of_mem _ membership)) base)

/-! ## Capability shapes of structural patterns -/

/-- A typed constructor pattern resolves at a constructor capability. -/
theorem TerminalPatternResolution.pctor_capability
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {name : String} {patterns : List Pattern}
    {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input (.pctor name patterns) capability target output) :
    ∃ former arguments, capability = .con former arguments := by
  cases resolution with
  | ctor found children compatible instantiated =>
      obtain ⟨former, arguments, _constructors, capabilityEq, _, _⟩ :=
        signatureWF.patternCtorIndexed found compatible
      exact ⟨former, arguments, capabilityEq⟩

/-- A typed tuple pattern resolves at a product capability. -/
theorem TerminalPatternResolution.ptuple_capability
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {patterns : List Pattern} {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input (.ptuple patterns) capability target output) :
    ∃ components, capability = .prod components := by
  cases resolution with
  | tuple children => exact ⟨_, rfl⟩

/-- The catch-all producer serves only the catch-all consumer demand. -/
theorem CapabilityDemand.any_producer_consumer
    {consumer : Cap} (demand : CapabilityDemand .any consumer) :
    consumer = .any := by
  cases demand <;> rfl

/-- Primitive pattern forms are matcher-dispatchable. -/
theorem Pattern.isMatcherDispatchable_of_isPrimForm
    {pattern : Pattern} (primitive : pattern.isPrimForm = true) :
    pattern.isMatcherDispatchable = true := by
  cases pattern <;>
    simp_all [Pattern.isPrimForm, Pattern.isMatcherDispatchable]

/-! ## The matcher-dispatch walk -/

/--
Walk the clause list of one typed matcher-dispatch atom to readiness.
Reachability needs only the mandatory final catch-all (a shape-compatible
clause exists in every suffix still containing one) and frozen data-arm
exhaustiveness (the committed clause has a receiving arm); decode success is
discharged by preservation and canonical-form totality.  The `ppmBuilder`
callback supplies the typed primitive-pattern match of the committed clause
and is instantiated by the ordered and the primitive capture-admissibility
routes.
-/
theorem matcherReady_of_dispatch
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {matcherContext : Context}
    {environment matcherEnvironment : Env}
    {pattern : Pattern} {value : Value} {original : List Clause}
    {producerCapability : Cap} {target : Ty}
    {evidence : List Shape.Evidence}
    (dispatchable : pattern.isMatcherDispatchable = true)
    (clausesTyped : ResolvedClausesTy signature matcherContext original
      producerCapability target evidence)
    (armsExhaustive : ArmExhaustive signature original target)
    (matcherEnvironmentPristine : EnvPristine matcherEnvironment)
    (matcherEnvironmentTyped :
      EnvTyped signature matcherContext matcherEnvironment)
    (valueTyping : ValueTy signature value target)
    (valuePristine : ValuePristine value)
    (evals : MatcherDispatchEvals signature SF environment matcherEnvironment
      pattern value original)
    (ppmBuilder :
      ∀ {clause : Clause}, clause ∈ original →
        ppShapeOK clause.pp pattern = true →
        ∀ {prevailing : Subst} {holes : List Dual} {ppBindings : MonoCtx},
          ResolvedPPatTy signature prevailing clause.pp target holes
            ppBindings →
          PPatCapsAt signature true clause.pp (holes.map Dual.cap)
            producerCapability →
          PPatCoreOrder clause.pp →
          ∃ captures ppEnvironment,
            PPM SF environment clause.pp pattern
              (some (captures, ppEnvironment)) ∧
            MonoEnvTys signature ppBindings ppEnvironment ∧
            EnvPristine ppEnvironment)
    {remaining : List Clause}
    (memberOriginal : ∀ clause ∈ remaining, clause ∈ original)
    (witness : ∃ clause ∈ remaining, ppShapeOK clause.pp pattern = true) :
    MAtomReady SF environment pattern
      (.matcherV matcherEnvironment original remaining) value := by
  induction remaining with
  | nil =>
      rcases witness with ⟨clause, membership, _⟩
      cases membership
  | cons clause remaining induction =>
      obtain ⟨pp, next, arms⟩ := clause
      cases shapeOK : ppShapeOK pp pattern with
      | false =>
          have tailWitness : ∃ candidate ∈ remaining,
              ppShapeOK candidate.pp pattern = true := by
            rcases witness with ⟨candidate, membership, candidateShape⟩
            rcases List.mem_cons.mp membership with rfl | membership
            · rw [show (Clause.mk pp next arms).pp = pp from rfl,
                shapeOK] at candidateShape
              cases candidateShape
            · exact ⟨candidate, membership, candidateShape⟩
          exact .matcherPPFail dispatchable (.fail shapeOK)
            (induction
              (fun candidate membership =>
                memberOriginal candidate (List.mem_cons_of_mem _ membership))
              tailWitness)
      | true =>
          have headMember : Clause.mk pp next arms ∈ original :=
            memberOriginal _ List.mem_cons_self
          obtain ⟨prevailing, clauseEvidence, _evidenceMember,
              clauseTyping⟩ := clausesTyped.member headMember
          obtain ⟨holes, pp', next', arms', ppBindings, nextMatchers,
              clauseEq, ppTyping, ppCaps, decompose, nextTyping, armsTyping,
              _evidenceCheck⟩ := clauseTyping.checked
          injection clauseEq with ppEq nextEq armsEq
          subst ppEq
          subst nextEq
          subst armsEq
          have ppOrder : PPatCoreOrder pp := clauseTyping.coreOrder
          obtain ⟨dpFound, dpMember, dataEnvironment₀, dpMatched⟩ :=
            signatureWF.armExhaustiveSuccess
              (value := value) (armsExhaustive _ headMember)
          obtain ⟨armFound, armMember, patEq⟩ := List.mem_map.mp dpMember
          have armWitness : ∃ arm ∈ arms, ∃ environment,
              pdMatch arm.pat value = some environment :=
            ⟨armFound, armMember, dataEnvironment₀, by
              rw [patEq]; exact dpMatched⟩
          obtain ⟨failedArms, matchedArm, dataEnvironment, afterArms, armsEq,
              failedAll, matchedSome⟩ := arms_first_success armWitness
          obtain ⟨dp, body⟩ := matchedArm
          have matchedMember : Arm.mk dp body ∈ arms := by
            rw [armsEq]
            exact List.mem_append_right _ List.mem_cons_self
          obtain ⟨dpat, body', armBindings, armEq, dpatTyping, bodyTyping⟩ :=
            armsTyping.member matchedMember
          injection armEq with dpEq bodyEq
          subst dpEq
          subst bodyEq
          obtain ⟨captures, ppEnvironment, ppm, ppTyped, ppPristine⟩ :=
            ppmBuilder headMember shapeOK ppTyping ppCaps ppOrder
          have dataTyped :=
            pdMatch_typed signatureWF dpatTyping valueTyping matchedSome
          have dataPristine := pdMatch_pristine valuePristine matchedSome
          obtain ⟨decomposition, bodyEval, bodyAgree⟩ :=
            evals.bodies _ headMember shapeOK ppm (.mk dp body)
              matchedMember matchedSome
          have bodyEnvTyped : EnvTyped signature
              (armBindings.toContext ++ ppBindings.toContext ++
                matcherContext)
              (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) := by
            simpa [List.append_assoc] using
              dataTyped.envTyped_append
                (ppTyped.envTyped_append matcherEnvironmentTyped)
          have bodyEnvPristine : EnvPristine
              (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) := by
            simpa [List.append_assoc] using
              dataPristine.append
                (ppPristine.append matcherEnvironmentPristine)
          have decompositionTyping :=
            EvalRuntimeSigAgrees.preservation signatureWF bodyAgree
              bodyEnvPristine bodyEnvTyped bodyTyping
          obtain ⟨tuples, listDecode⟩ :=
            listOfV_isSome signatureWF decompositionTyping
          have tuplesTyped :=
            (listOfV_typed signatureWF decompositionTyping
              listDecode).replicate_mem
          obtain ⟨valueLists, tupleDecodes⟩ :=
            mapM_decodeTuple_isSome signatureWF
              (targets := holes.map Dual.target) tuplesTyped
          obtain ⟨matcherValue, nextEval, nextAgree⟩ :=
            evals.nexts _ headMember shapeOK
          have nextTypingInv :=
            decomposeME_typed
              (targets := holes.map fun hole => .slot hole.cap hole.target)
              (by simpa [List.length_map] using decompose) nextTyping
          have matcherValueTyping :=
            EvalRuntimeSigAgrees.preservation signatureWF nextAgree
              matcherEnvironmentPristine matcherEnvironmentTyped
              nextTypingInv
          obtain ⟨matchers, matcherDecode⟩ :=
            decodeTuple_isSome signatureWF matcherValueTyping
          have captureLength : captures.length = holes.length :=
            (ppm_captures_length pp ppm).trans ppTyping.holes_length.symm
          have tupleDecodes' :
              tuples.mapM (decodeTuple captures.length) = some valueLists := by
            rw [captureLength]
            simpa [List.length_map] using tupleDecodes
          have matcherDecode' :
              decodeTuple captures.length matcherValue = some matchers := by
            rw [captureLength]
            simpa [List.length_map] using matcherDecode
          have base : MAtomReady SF environment pattern
              (.matcherV matcherEnvironment original
                (.mk pp next (.mk dp body :: afterArms) :: remaining))
              value :=
            .matcher dispatchable ppm matchedSome bodyEval listDecode
              tupleDecodes' nextEval matcherDecode'
          have chained :=
            matcherDPFail_chain dispatchable ppm failedAll base
          rw [armsEq]
          exact chained

/-! ## The two capture-admissibility routes -/

/-- Primitive-route PPM construction: a shape-compatible clause head against
a primitive-form pattern embeds at most the pattern's own value expression. -/
theorem ppm_of_primitive
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {environment : Env}
    {prevailing patternPrevailing : Subst}
    {pp : PPat} {pattern : Pattern} {patternCapability : Cap} {target : Ty}
    {holes : List Dual} {ppBindings : MonoCtx}
    (environmentPristine : EnvPristine environment)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    (patternTyping : ResolvedPatternTy signature patternPrevailing context
      parameters input pattern patternCapability target output)
    (primitive : pattern.isPrimForm = true)
    (ppTyping : ResolvedPPatTy signature prevailing pp target holes
      ppBindings)
    (shapeOK : ppShapeOK pp pattern = true)
    (evals : ∀ expression ∈ capturedExprs pp pattern,
      AgreedEval signature SF environment expression) :
    ∃ captures ppEnvironment,
      PPM SF environment pp pattern (some (captures, ppEnvironment)) ∧
      MonoEnvTys signature ppBindings ppEnvironment ∧
      EnvPristine ppEnvironment := by
  have ppm₀ : ∃ captures ppEnvironment,
      PPM SF environment pp pattern (some (captures, ppEnvironment)) := by
    cases pp with
    | hole => exact ⟨[pattern], [], .hole⟩
    | wild =>
        cases pattern <;>
          first
          | exact ⟨[], [], .wild⟩
          | simp [ppShapeOK] at shapeOK
    | pval name =>
        cases pattern with
        | pval expression =>
            obtain ⟨value, evaluation, _⟩ :=
              evals expression (by simp [capturedExprs])
            exact ⟨[], [(name, value)], .pval evaluation⟩
        | pvar name' => simp [ppShapeOK] at shapeOK
        | wild => simp [ppShapeOK] at shapeOK
        | embed name' => simp [ppShapeOK] at shapeOK
        | pctor name' patterns => simp [ppShapeOK] at shapeOK
        | pand left right => simp [ppShapeOK] at shapeOK
        | por left right => simp [ppShapeOK] at shapeOK
        | papp name' patterns => simp [ppShapeOK] at shapeOK
        | ptuple patterns => simp [ppShapeOK] at shapeOK
    | ctor name pps =>
        cases pattern <;>
          simp_all [ppShapeOK, Pattern.isPrimForm]
    | tuple pps =>
        cases pattern <;>
          simp_all [ppShapeOK, Pattern.isPrimForm]
  obtain ⟨captures, ppEnvironment, ppm₀⟩ := ppm₀
  have admissible :=
    captureAdm_of_primitive_success patternTyping primitive ppTyping ppm₀
  exact ppm_of_captureAdm signatureWF environmentPristine environmentTyping
    admissible evals

/-! ## Atom readiness from typing -/

/--
A typed atom whose embedded evaluations converge is ready to reduce.
Pattern-function and embedded-parameter atoms are excluded: their steps are
provided by `Step.patfunEnter` and the enclosing node respectively.
-/
theorem MAtomReady.of_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {environment : Env}
    {pattern : Pattern} {matcher value : Value}
    (typing : AtomTy signature context parameters input
      ⟨pattern, matcher, value⟩ output)
    (matcherPristine : ValuePristine matcher)
    (valuePristine : ValuePristine value)
    (environmentPristine : EnvPristine environment)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    (notPatfun : ∀ name arguments, pattern ≠ .papp name arguments)
    (notEmbed : ∀ name, pattern ≠ .embed name)
    (evals : AtomEvals signature SF environment ⟨pattern, matcher, value⟩) :
    MAtomReady SF environment pattern matcher value := by
  cases typing with
  | mk patternTyping matcherTyping valueTyping =>
      obtain ⟨producerCapability, mTyping, demand⟩ := matcherTyping
      cases matcher with
      | lit n => cases mTyping
      | closure self closureEnvironment parameter body => cases mTyping
      | ctor name values =>
          cases mTyping with
          | ctor found instanceTyping fieldsTyped =>
              obtain ⟨former, arguments, resultEq⟩ :=
                signatureWF.dataResult found instanceTyping
              exact nomatch resultEq
      | something =>
          have capEq : producerCapability = .any :=
            mTyping.something_capability_unique
          subst capEq
          cases pattern with
          | pvar name => exact .someVar
          | wild => exact .someWC
          | pval expression =>
              obtain ⟨expected, evaluation, _⟩ :=
                evals.pval expression rfl rfl
              exact .someVal evaluation
          | pand left right => exact .and
          | por left right => exact .or
          | papp name arguments => exact absurd rfl (notPatfun name arguments)
          | embed name => exact absurd rfl (notEmbed name)
          | pctor name patterns =>
              have capEq := demand.any_producer_consumer
              obtain ⟨former, arguments, conEq⟩ :=
                patternTyping.terminal.pctor_capability signatureWF
              exact nomatch capEq.symm.trans conEq
          | ptuple patterns =>
              have capEq := demand.any_producer_consumer
              obtain ⟨components, prodEq⟩ :=
                patternTyping.terminal.ptuple_capability
              exact nomatch capEq.symm.trans prodEq
      | tuple matchers =>
          cases mTyping with
          | matcherProduct fieldsTyped =>
              cases pattern with
              | pvar name => exact .prodSome rfl
              | wild => exact .prodSome rfl
              | pval expression => exact .prodSome rfl
              | pand left right => exact .and
              | por left right => exact .or
              | papp name arguments =>
                  exact absurd rfl (notPatfun name arguments)
              | embed name => exact absurd rfl (notEmbed name)
              | pctor name patterns =>
                  obtain ⟨former, arguments, conEq⟩ :=
                    patternTyping.terminal.pctor_capability signatureWF
                  rw [conEq] at demand
                  exact nomatch demand
              | ptuple patterns =>
                  obtain ⟨values, valueEq, _⟩ :=
                    ValueTy.product_inversion signatureWF valueTyping
                  subst valueEq
                  exact .tuple
      | matcherV matcherEnvironment originalClauses currentClauses =>
          have currentEq : currentClauses = originalClauses := by
            cases matcherPristine
            rfl
          subst currentEq
          have matcherEnvironmentPristine :
              EnvPristine matcherEnvironment := by
            cases matcherPristine
            assumption
          obtain ⟨matcherContext, matcherEnvironmentTyped, _cursor,
              sourceTyping⟩ := mTyping.matcherLiteral_inversion
          obtain ⟨evidence, clausesTyped, _shape, catchAll,
              armsExhaustive, _ppNodup, _armNodup, _coverage⟩ :=
            sourceTyping.matcher_inversion
          have dispatchEvals := evals.dispatch _ _ _ rfl
          have go :
              pattern.isMatcherDispatchable = true →
              MAtomReady SF environment pattern
                (.matcherV matcherEnvironment currentClauses currentClauses)
                value := by
            intro dispatchable
            rcases catchAll with ⟨before, catchNext, catchName,
              catchBody, originalEq, _⟩
            refine matcherReady_of_dispatch signatureWF dispatchable
              clausesTyped armsExhaustive matcherEnvironmentPristine
              matcherEnvironmentTyped valueTyping
              valuePristine dispatchEvals
              (fun {clause} member shapeOK {prevailing'} {holes}
                  {ppBindings} ppTyping ppCaps ppOrder => by
                obtain ⟨finished, ordered⟩ := ppOrder
                have admissible := (captureAdm_of_order_at signatureWF
                  ppTyping.terminal ordered (fun _ => rfl) ppCaps
                  patternTyping.terminal demand shapeOK).1
                exact ppm_of_captureAdm signatureWF environmentPristine
                  environmentTyping admissible
                  (fun expression membership =>
                    dispatchEvals.captures clause member shapeOK
                      expression membership))
              (fun clause membership => membership) ?_
            refine ⟨.mk .hole catchNext [.mk (.var catchName) catchBody],
              ?_, rfl⟩
            rw [originalEq]
            exact List.mem_append_right _ List.mem_cons_self
          cases pattern with
          | pvar name => exact go rfl
          | wild => exact go rfl
          | pval expression => exact go rfl
          | pctor name patterns => exact go rfl
          | ptuple patterns => exact go rfl
          | pand left right => exact .and
          | por left right => exact .or
          | papp name arguments =>
              exact absurd rfl (notPatfun name arguments)
          | embed name => exact absurd rfl (notEmbed name)
  | primitive patternTyping primitive matcherAt valueTyping =>
      obtain ⟨consumerCapability, producerCapability, mTyping, demand⟩ :=
        matcherAt
      cases matcher with
      | lit n => cases mTyping
      | closure self closureEnvironment parameter body => cases mTyping
      | ctor name values =>
          cases mTyping with
          | ctor found instanceTyping fieldsTyped =>
              obtain ⟨former, arguments, resultEq⟩ :=
                signatureWF.dataResult found instanceTyping
              exact nomatch resultEq
      | something =>
          cases pattern with
          | pvar name => exact .someVar
          | wild => exact .someWC
          | pval expression =>
              obtain ⟨expected, evaluation, _⟩ :=
                evals.pval expression rfl rfl
              exact .someVal evaluation
          | pand left right => simp [Pattern.isPrimForm] at primitive
          | por left right => simp [Pattern.isPrimForm] at primitive
          | papp name arguments => simp [Pattern.isPrimForm] at primitive
          | embed name => simp [Pattern.isPrimForm] at primitive
          | pctor name patterns => simp [Pattern.isPrimForm] at primitive
          | ptuple patterns => simp [Pattern.isPrimForm] at primitive
      | tuple matchers =>
          exact .prodSome primitive
      | matcherV matcherEnvironment originalClauses currentClauses =>
          have currentEq : currentClauses = originalClauses := by
            cases matcherPristine
            rfl
          subst currentEq
          have matcherEnvironmentPristine :
              EnvPristine matcherEnvironment := by
            cases matcherPristine
            assumption
          obtain ⟨matcherContext, matcherEnvironmentTyped, _cursor,
              sourceTyping⟩ := mTyping.matcherLiteral_inversion
          obtain ⟨evidence, clausesTyped, _shape, catchAll,
              armsExhaustive, _ppNodup, _armNodup, _coverage⟩ :=
            sourceTyping.matcher_inversion
          have dispatchEvals := evals.dispatch _ _ _ rfl
          rcases catchAll with ⟨before, catchNext, catchName, catchBody,
            originalEq, _⟩
          refine matcherReady_of_dispatch signatureWF
            (Pattern.isMatcherDispatchable_of_isPrimForm primitive)
            clausesTyped armsExhaustive matcherEnvironmentPristine
            matcherEnvironmentTyped valueTyping
            valuePristine dispatchEvals
            (fun {clause} member shapeOK {prevailing'} {holes}
                {ppBindings} ppTyping ppCaps ppOrder =>
              ppm_of_primitive signatureWF environmentPristine
                environmentTyping patternTyping primitive ppTyping
                shapeOK
                (fun expression membership =>
                  dispatchEvals.captures clause member shapeOK
                    expression membership))
            (fun clause membership => membership) ?_
          refine ⟨.mk .hole catchNext [.mk (.var catchName) catchBody],
            ?_, rfl⟩
          rw [originalEq]
          exact List.mem_append_right _ List.mem_cons_self

/-! ## State readiness from typing -/

/--
Head-tree readiness from typing and convergence.  An embedded-parameter atom
head is excluded here; the top-level wrapper refutes it from typing, and the
enclosing node provides its step inside a pattern-function node.
-/
theorem StepReady.of_typed_tree
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} :
    ∀ (tree : Tree) {stack : List Tree} {environment : Env}
      {substitution : MatchSubst} {context : Context}
      {parameters : PatternCtx} {goal : MonoCtx},
      MStateTyAt signature context parameters
        ⟨tree :: stack, environment, substitution⟩ goal →
      (∀ name matcher value,
        tree = .atom ⟨.embed name, matcher, value⟩ → False) →
      TreeEvals signature SF (substitution ++ environment) tree →
      StepReady SF ⟨tree :: stack, environment, substitution⟩
  | .atom ⟨pattern, matcher, value⟩, stack, environment, substitution,
      context, parameters, goal => by
      intro typing notEmbedAtom evals
      rcases typing with ⟨⟨stackPristine, environmentPristine,
        substitutionPristine⟩, _noEmbed, environmentTyping, input,
        substitutionTyping, stackTyping⟩
      cases stackPristine with
      | cons headPristine _tailPristine =>
          cases headPristine with
          | atom atomPristine =>
              obtain ⟨matcherPristine, valuePristine⟩ := atomPristine
              cases stackTyping with
              | cons treeTyping _tailTyping =>
                  cases treeTyping with
                  | atom atomTyping =>
                      have combinedPristine :=
                        substitutionPristine.append environmentPristine
                      have combinedTyping :=
                        substitutionTyping.envTyped_append environmentTyping
                      have ready :
                          (∀ name arguments,
                            pattern ≠ .papp name arguments) →
                          (∀ name, pattern ≠ .embed name) →
                          AtomEvals signature SF
                            (substitution ++ environment)
                            ⟨pattern, matcher, value⟩ →
                          StepReady SF
                            ⟨.atom ⟨pattern, matcher, value⟩ :: stack,
                              environment, substitution⟩ :=
                        fun notPatfun notEmbed atomEvals =>
                          .atom (MAtomReady.of_typed signatureWF atomTyping
                            matcherPristine valuePristine combinedPristine
                            combinedTyping notPatfun notEmbed atomEvals)
                      cases pattern with
                      | papp name arguments => exact .patfun
                      | embed name =>
                          exact (notEmbedAtom name matcher value rfl).elim
                      | pvar name =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | wild =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | pval expression =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | pctor name patterns =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | ptuple patterns =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | pand left right =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
                      | por left right =>
                          exact ready (fun _ _ h => nomatch h)
                            (fun _ h => nomatch h)
                            (match evals with | .atom ae => ae)
  | .mnode [] innerEnvironment innerSubstitution piE, stack, environment,
      substitution, context, parameters, goal => by
      intro _typing _notEmbedAtom _evals
      exact .mnodeDone
  | .mnode (innerTree :: innerStack) innerEnvironment innerSubstitution piE,
      stack, environment, substitution, context, parameters, goal => by
      intro typing _notEmbedAtom evals
      rcases typing with ⟨⟨stackPristine, _environmentPristine,
        _substitutionPristine⟩, _noEmbed, _environmentTyping, input,
        _substitutionTyping, stackTyping⟩
      cases stackPristine with
      | cons nodePristine _tailPristine =>
          cases nodePristine with
          | mnode innerStackPristine innerEnvironmentPristine
              innerSubstitutionPristine =>
              cases stackTyping with
              | cons treeTyping _tailTyping =>
                  obtain ⟨innerParameters, innerBindings, innerOutput, rem,
                      duals, suffix, namesNodup, innerNoEmbed,
                      _argumentsNoEmbed, occurrences, _actuals,
                      _inParameters, capturedEnvironmentTyping,
                      innerSubstitutionTyping, innerStackTyping⟩ :=
                    treeTyping.mnode_inversion
                  by_cases embedHead : ∃ name m v,
                      innerTree = .atom ⟨.embed name, m, v⟩
                  · obtain ⟨name, m, v, rfl⟩ := embedHead
                    have nameLeading : name :: stackEmbedOccs innerStack =
                        rem.map Prod.fst := by
                      simpa [stackEmbedOccs, treeEmbedOccs,
                        Pattern.embedVars] using occurrences
                    cases remShape : rem with
                    | nil =>
                        rw [remShape] at nameLeading
                        cases nameLeading
                    | cons entry remRest =>
                        obtain ⟨entryName, entryPattern⟩ := entry
                        rw [remShape] at nameLeading
                        have nameEq : entryName = name := by
                          simpa using (List.cons.inj nameLeading.symm).1
                        subst nameEq
                        have entryMember : (entryName, entryPattern) ∈ piE := by
                          obtain ⟨index, dropEq⟩ := suffix
                          rw [dropEq] at remShape
                          exact List.mem_of_mem_drop
                            (remShape ▸ List.mem_cons_self)
                        have found :=
                          PiEnv.find?_eq_some_of_mem namesNodup entryMember
                        exact .mnodeVarpat found
                  · have innerNotEmbed :
                        ∀ name m v,
                          innerTree = .atom ⟨.embed name, m, v⟩ → False :=
                      fun name m v h => embedHead ⟨name, m, v, h⟩
                    have innerTyping : MStateTyAt signature context
                        innerParameters
                        ⟨innerTree :: innerStack, innerEnvironment,
                          innerSubstitution⟩ innerOutput :=
                      ⟨⟨innerStackPristine, innerEnvironmentPristine,
                          innerSubstitutionPristine⟩,
                        innerNoEmbed, capturedEnvironmentTyping,
                        innerBindings, innerSubstitutionTyping,
                        innerStackTyping⟩
                    have innerEvals :
                        TreeEvals signature SF
                          (innerSubstitution ++ innerEnvironment)
                          innerTree :=
                      match evals with | .mnodeCons inner => inner
                    exact .mnodeStep
                      (fun name m v h => (innerNotEmbed name m v h).elim)
                      (StepReady.of_typed_tree signatureWF innerTree
                        innerTyping innerNotEmbed innerEvals)

/-- A typed nonterminal top-level state whose embedded evaluations converge
is locally ready: decode success and dispatch reachability come from the
typing evidence, so only convergence remains as an assumption. -/
theorem StepReady.of_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {state : MState} {goal : MonoCtx}
    (typing : MStateTy signature context state goal)
    (nonterminal : state.S ≠ [])
    (evals : StateEvals signature SF state) :
    StepReady SF state := by
  obtain ⟨stack, environment, substitution⟩ := state
  cases stack with
  | nil => exact absurd rfl nonterminal
  | cons tree stack =>
      refine StepReady.of_typed_tree signatureWF tree typing ?_
        (evals tree stack rfl)
      intro name matcher value treeEq
      subst treeEq
      rcases typing with ⟨_, _, _, input, _, stackTyping⟩
      cases stackTyping with
      | cons treeTyping _ =>
          cases treeTyping with
          | atom atomTyping =>
              cases atomTyping with
              | mk patternTyping _ _ =>
                  have found := patternTyping.embed_inversion.1
                  cases found
              | primitive _ primitive _ _ =>
                  simp [Pattern.isPrimForm] at primitive

/-! ## Public corollary -/

/--
Local progress from typing and embedded convergence alone: a typed
nonterminal top-level matching state whose embedded evaluations converge
takes one concrete step.  Relative to `StepReady.progress`, the decode and
dispatch content of the readiness premise is discharged here from the
typing evidence; the residual assumption is exactly that the embedded
evaluations converge.
-/
theorem MStateTy.progress_of_evals
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {state : MState} {goal : MonoCtx}
    (agreement : RuntimeSigAgrees signature context SF)
    (typing : MStateTy signature context state goal)
    (nonterminal : state.S ≠ [])
    (evals : StateEvals signature SF state) :
    ∃ states, Step SF state states :=
  (StepReady.of_typed signatureWF typing nonterminal evals).progress
    signatureWF agreement typing

end TypePM
