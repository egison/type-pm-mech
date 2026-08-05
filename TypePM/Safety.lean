import TypePM.DynamicMetatheory
import TypePM.SourceGeneralization
import TypePM.Reachability

/-!
# Type safety of the concrete two-sorted Egison core

This module closes the dynamic proof for the concrete source and operational
judgments.  Supporting canonical and inversion lemmas live in
`DynamicMetatheory`; this file contains the run invariants, preservation,
progress, reachability, and terminal matcher-consistency theorem.
-/

namespace TypePM

/-! ## Pristine-state closure of the concrete semantics -/

/--
The semantic history of an ordered matcher-clause cursor.  Unlike the purely
syntactic `MatcherCursor`, every move records the concrete failure that made
the move legal.  Public matcher values start with `refl`; the two recursive
matcher rules extend this trace only inside their `MAtom` derivation.
-/
inductive DispatchTrace
    (SF : RuntimeSigF) (environment : Env)
    (pattern : Pattern) (value : Value) :
    List Clause → List Clause → Prop where
  | refl {clauses} :
      DispatchTrace SF environment pattern value clauses clauses
  | nextClause {pp next arms clauses original} :
      DispatchTrace SF environment pattern value original
        (.mk pp next arms :: clauses) →
      PPM SF environment pp pattern none →
      DispatchTrace SF environment pattern value original clauses
  | nextArm {pp next dp body arms clauses original holes ppEnvironment} :
      DispatchTrace SF environment pattern value original
        (.mk pp next (.mk dp body :: arms) :: clauses) →
      PPM SF environment pp pattern (some (holes, ppEnvironment)) →
      pdMatch dp value = none →
      DispatchTrace SF environment pattern value original
        (.mk pp next arms :: clauses)

/-- Forgetting recorded failures yields the ordinary source cursor relation. -/
theorem DispatchTrace.matcherCursor
    {SF : RuntimeSigF} {environment : Env}
    {pattern : Pattern} {value : Value} {original current : List Clause}
    (trace : DispatchTrace SF environment pattern value original current) :
    MatcherCursor current original := by
  induction trace with
  | refl => exact .refl
  | nextClause prior failure induction => exact .nextClause induction
  | nextArm prior ppSuccess dataFailure induction => exact .nextArm induction

/--
The PP headers dropped by a dispatch trace form an exact prefix of the
original header stream, and each carries its recorded PPM failure.
-/
theorem DispatchTrace.failedPrefix
    {SF : RuntimeSigF} {environment : Env}
    {pattern : Pattern} {value : Value} {original current : List Clause}
    (trace : DispatchTrace SF environment pattern value original current) :
    ∃ failed : List PPat,
      original.map Clause.pp = failed ++ current.map Clause.pp ∧
      ∀ pp ∈ failed, PPM SF environment pp pattern none := by
  induction trace with
  | refl =>
      exact ⟨[], by simp, fun pp member => by contradiction⟩
  | @nextClause pp next arms clauses original prior failure induction =>
      obtain ⟨failed, headers, failures⟩ := induction
      refine ⟨failed ++ [pp], ?_, ?_⟩
      · rw [headers]
        simp [Clause.pp, List.append_assoc]
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact failures candidate member
        · exact failure
  | nextArm prior ppSuccess dataFailure induction =>
      simpa [Clause.pp] using induction

/-- Once a suffix starts at the unique final hole, no clause can follow it. -/
theorem ppat_tail_after_final_hole_nil
    {before failed tail : List PPat}
    (beforeNonHole : ∀ pp ∈ before, pp ≠ .hole)
    (headers : before ++ [.hole] = failed ++ .hole :: tail) :
    tail = [] := by
  induction before generalizing failed with
  | nil =>
      cases failed with
      | nil => simpa using List.cons.inj headers |>.2
      | cons head failed =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at headers
          obtain ⟨headEquality, impossible⟩ := headers
          subst head
          simp at impossible
  | cons head before induction =>
      cases failed with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            List.cons.injEq] at headers
          exact (beforeNonHole head (by simp) headers.1).elim
      | cons failedHead failed =>
          simp only [List.cons_append, List.cons.injEq] at headers
          exact induction
            (fun pp member => beforeNonHole pp (by simp [member])) headers.2

/-- A hole clause occurring in a `CatchAllLast` matcher is the unique final
singleton variable arm. -/
theorem CatchAllLast.hole_member
    {clauses : List Clause} {clause : Clause}
    (catchAll : CatchAllLast clauses)
    (membership : clause ∈ clauses)
    (hole : clause.pp = .hole) :
    ∃ next name body,
      clause = .mk .hole next [.mk (.var name) body] := by
  rcases catchAll with ⟨before, next, name, body, rfl, beforeNonHole⟩
  simp only [List.mem_append, List.mem_singleton] at membership
  rcases membership with beforeMember | rfl
  · exact (beforeNonHole clause beforeMember hole).elim
  · exact ⟨next, name, body, rfl⟩

/-- Arm consumption makes the current arm list a suffix of the source arm
list. -/
theorem ClauseArmCursor.arms_suffix
    {current original : Clause}
    (cursor : ClauseArmCursor current original) :
    ∃ dropped, original.arms = dropped ++ current.arms := by
  induction cursor with
  | refl => exact ⟨[], rfl⟩
  | @nextArm pp next arm arms original previous induction =>
      obtain ⟨dropped, equality⟩ := induction
      refine ⟨dropped ++ [arm], ?_⟩
      rw [equality, List.append_assoc]
      rfl

/-- A nonempty cursor of a singleton source arm is still that singleton. -/
theorem ClauseArmCursor.singleton_inversion
    {current original : Clause} {arm sourceArm : Arm} {arms : List Arm}
    (cursor : ClauseArmCursor current original)
    (currentArms : current.arms = arm :: arms)
    (sourceArms : original.arms = [sourceArm]) :
    arm = sourceArm ∧ arms = [] := by
  obtain ⟨dropped, suffix⟩ := cursor.arms_suffix
  rw [sourceArms, currentArms] at suffix
  cases dropped with
  | nil =>
      simpa only [List.nil_append, List.cons.injEq] using suffix.symm
  | cons dropped droppedTail =>
      simp only [List.cons_append, List.cons.injEq] at suffix
      simp at suffix

/-- A dispatch trace whose current head is the bare hole is positioned at the
unique final clause and at its sole variable arm. -/
theorem DispatchTrace.hole_current_final
    {SF : RuntimeSigF} {environment : Env} {pattern : Pattern} {value : Value}
    {original clauses : List Clause} {next : Expr} {arm : Arm}
    {arms : List Arm}
    (trace : DispatchTrace SF environment pattern value original
      (.mk .hole next (arm :: arms) :: clauses))
    (catchAll : CatchAllLast original) :
    ∃ name body,
      clauses = [] ∧ arms = [] ∧ arm = .mk (.var name) body := by
  rcases catchAll with
    ⟨before, catchNext, catchName, catchBody, originalEquality,
      beforeNonHole⟩
  obtain ⟨failed, headers, failures⟩ := trace.failedPrefix
  rw [originalEquality] at headers
  simp only [List.map_append, List.map_cons,
    Clause.pp] at headers
  have tailHeaders : clauses.map Clause.pp = [] :=
    ppat_tail_after_final_hole_nil
      (fun pp member => by
        obtain ⟨clause, clauseMember, rfl⟩ := List.mem_map.mp member
        exact beforeNonHole clause clauseMember)
      headers
  have clausesEmpty : clauses = [] := by
    simpa using tailHeaders
  have cursor := trace.matcherCursor
  obtain ⟨sourceClause, sourceMember, armCursor⟩ :=
    cursor.member_origin
      (show Clause.mk .hole next (arm :: arms) ∈
        Clause.mk .hole next (arm :: arms) :: clauses from List.mem_cons_self)
  have sourceHole : sourceClause.pp = .hole := by
    exact armCursor.headers.1.symm
  obtain ⟨sourceNext, name, body, sourceEquality⟩ :=
    CatchAllLast.hole_member
      ⟨before, catchNext, catchName, catchBody, originalEquality,
        beforeNonHole⟩ sourceMember sourceHole
  have sourceArms : sourceClause.arms = [.mk (.var name) body] := by
    rw [sourceEquality]
    rfl
  obtain ⟨armEquality, armsEmpty⟩ :=
    armCursor.singleton_inversion rfl sourceArms
  exact ⟨name, body, clausesEmpty, armsEmpty, armEquality⟩

/-- A required general clause passed before the final catch-all has failed. -/
theorem DispatchTrace.failed_of_generalBeforeCatchAll
    {SF : RuntimeSigF} {environment : Env}
    {pattern : Pattern} {value : Value} {original : List Clause}
    {requested : PPat} {next : Expr} {name : String} {body : Expr}
    (trace : DispatchTrace SF environment pattern value original
      [.mk .hole next [.mk (.var name) body]])
    (before : GeneralBeforeCatchAll original requested) :
    PPM SF environment requested pattern none := by
  rcases before with
    ⟨beforeClauses, catchNext, catchName, catchBody, originalEquality,
      clause, clauseMember, clausePP⟩
  rw [originalEquality] at trace
  obtain ⟨failed, headers, failures⟩ := trace.failedPrefix
  simp only [List.map_append, List.map_singleton, Clause.pp] at headers
  have lengths := congrArg List.length headers
  simp only [List.length_append, List.length_singleton,
    Nat.add_right_cancel_iff] at lengths
  have failedEquality : beforeClauses.map Clause.pp = failed :=
    List.append_inj_left headers (by simpa using lengths)
  have requestedMember : requested ∈ beforeClauses.map Clause.pp :=
    List.mem_map.mpr ⟨clause, clauseMember, clausePP⟩
  exact failures requested (failedEquality ▸ requestedMember)

/-- A list of PP holes shape-checks every pattern list of the same arity. -/
@[simp] theorem ppShapeOKList_replicate_hole (patterns : List Pattern) :
    ppShapeOKList (List.replicate patterns.length PPat.hole) patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns induction =>
      change ppShapeOKList
        (List.replicate (patterns.length + 1) PPat.hole)
        (pattern :: patterns) = true
      rw [List.replicate_succ]
      simpa [ppShapeOKList, ppShapeOK] using induction

/-- General constructor clauses cannot fail on their matching constructor. -/
theorem ppm_generalPP_not_failure
    {SF : RuntimeSigF} {environment : Env} {name : String}
    {patterns : List Pattern}
    (failure : PPM SF environment (generalPP name patterns.length)
      (.pctor name patterns) none) : False := by
  cases failure with
  | fail rejected =>
      simp [generalPP, ppShapeOK, ppShapeOKList_replicate_hole] at rejected

/-- General tuple clauses cannot fail on a tuple of the same arity. -/
theorem ppm_generalTuplePP_not_failure
    {SF : RuntimeSigF} {environment : Env} {patterns : List Pattern}
    (failure : PPM SF environment (generalTuplePP patterns.length)
      (.ptuple patterns) none) : False := by
  cases failure with
  | fail rejected =>
      simp [generalTuplePP, ppShapeOK, ppShapeOKList_replicate_hole] at rejected

/-- A typed constructor pattern cannot first dispatch at the final catch-all. -/
theorem DispatchTrace.pctor_not_finalCatchAll
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {SF : RuntimeSigF} {environment : Env}
    {value : Value} {original : List Clause} {next : Expr}
    {catchName : String} {catchBody : Expr} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {name : String} {patterns : List Pattern} {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input (.pctor name patterns) capability target output)
    (dispatch : DispatchOK signature.toMatcherSig original capability)
    (trace : DispatchTrace SF environment (.pctor name patterns) value original
      [.mk .hole next [.mk (.var catchName) catchBody]]) : False := by
  cases resolution with
  | @ctor _ _ _ _ _ entry _ duals _ result found children compatible
      instantiated =>
      obtain ⟨former, arguments, capabilityEquality, indexed⟩ :=
        signatureWF.patternCtorIndexed found compatible
      rw [capabilityEquality] at dispatch
      obtain ⟨constructors, constructorsFound, required⟩ := dispatch
      have childLength : patterns.length = (duals.map Dual.cap).length := by
        simpa using children.length
      have before := required (name, (duals.map Dual.cap).length)
        (indexed constructorsFound)
      have failure := trace.failed_of_generalBeforeCatchAll before
      apply ppm_generalPP_not_failure
      rw [childLength]
      exact failure

/-- A typed tuple pattern cannot first dispatch at the final catch-all. -/
theorem DispatchTrace.ptuple_not_finalCatchAll
    {signature : FrozenSig} {prevailing : Subst}
    {SF : RuntimeSigF} {environment : Env} {value : Value}
    {original : List Clause} {next : Expr} {catchName : String}
    {catchBody : Expr} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patterns : List Pattern}
    {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input (.ptuple patterns) capability target output)
    (dispatch : DispatchOK signature.toMatcherSig original capability)
    (trace : DispatchTrace SF environment (.ptuple patterns) value original
      [.mk .hole next [.mk (.var catchName) catchBody]]) : False := by
  cases resolution with
  | @tuple _ _ _ _ _ duals _ children =>
    have childLength : patterns.length = (duals.map Dual.cap).length := by
      simpa using children.length
    have before : GeneralBeforeCatchAll original
        (generalTuplePP patterns.length) := by
      simpa [DispatchOK, childLength] using dispatch
    exact ppm_generalTuplePP_not_failure
      (trace.failed_of_generalBeforeCatchAll before)

/-- At a successful dispatch site, the clause is non-catch-all unless the
user pattern is one of the three primitive forms. -/
theorem DispatchTrace.nonCatchAll_or_primitive
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {SF : RuntimeSigF} {environment : Env}
    {value : Value} {original clauses : List Clause} {next body : Expr}
    {dp : DPat} {arms : List Arm} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {pattern : Pattern} {capability : Cap} {target : Ty}
    {pp : PPat}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input pattern capability target output)
    (dispatchable : pattern.isMatcherDispatchable = true)
    (dispatch : DispatchOK signature.toMatcherSig original capability)
    (catchAll : CatchAllLast original)
    (trace : DispatchTrace SF environment pattern value original
      (.mk pp next (.mk dp body :: arms) :: clauses)) :
    pp ≠ .hole ∨ pattern.isPrimForm = true := by
  by_cases nonCatchAll : pp ≠ .hole
  · exact .inl nonCatchAll
  · have ppEquality : pp = .hole := Classical.not_not.mp nonCatchAll
    subst pp
    obtain ⟨name, catchBody, clausesEmpty, armsEmpty, armEquality⟩ :=
      trace.hole_current_final catchAll
    subst clauses
    subst arms
    injection armEquality with dpEquality bodyEquality
    subst dp
    subst body
    cases pattern with
    | pvar name => exact .inr rfl
    | wild => exact .inr rfl
    | pval expression => exact .inr rfl
    | pctor name patterns =>
        exact (trace.pctor_not_finalCatchAll signatureWF resolution dispatch).elim
    | ptuple patterns =>
        exact (trace.ptuple_not_finalCatchAll resolution dispatch).elim
    | pand left right => simp [Pattern.isMatcherDispatchable] at dispatchable
    | por left right => simp [Pattern.isMatcherDispatchable] at dispatchable
    | papp name patterns => simp [Pattern.isMatcherDispatchable] at dispatchable
    | embed name => simp [Pattern.isMatcherDispatchable] at dispatchable
/-- The only runtime values visible during an internal matcher cursor walk. -/
def MAtomInputPristine (pattern : Pattern) (matcher : Value) : Prop :=
  ValuePristine matcher ∨
    ∃ matcherEnvironment original current,
      matcher = .matcherV matcherEnvironment original current ∧
      EnvPristine matcherEnvironment ∧
      pattern.isMatcherDispatchable = true

/-- Primitive-pattern matching stores only pristine evaluated value bindings. -/
def PPMOutputPristine : Option (List Pattern × Env) → Prop
  | none => True
  | some (_, environment) => EnvPristine environment

/-- One atom reduction returns pristine substitutions and atom payloads. -/
def MAtomOutputPristine
    (continuations : List (List Atom)) (substitution : MatchSubst) : Prop :=
  EnvPristine substitution ∧
    ∀ atoms ∈ continuations, StackPristine (atoms.map Tree.atom)

/-- Every successful branch returned by search is pristine. -/
def SearchOutputPristine (substitutions : List MatchSubst) : Prop :=
  ∀ substitution ∈ substitutions, EnvPristine substitution

/-- Internal matcher cursors retain their captured pristine environment. -/
theorem MAtomInputPristine.matcherEnvironment
    {pattern : Pattern} {environment : Env}
    {original current : List Clause}
    (pristine : MAtomInputPristine pattern
      (.matcherV environment original current)) :
    EnvPristine environment := by
  rcases pristine with pristine | ⟨found, foundOriginal, foundCurrent,
      equality, foundPristine, _⟩
  · cases pristine with
    | matcherLiteral environmentPristine => exact environmentPristine
  · injection equality with environmentEquality
    subst found
    exact foundPristine

/-- The left projection of a member of a zip occurs in its left input. -/
theorem List.fst_mem_of_mem_zip
    {lefts : List α} {rights : List β} {pair : α × β}
    (member : pair ∈ lefts.zip rights) :
    pair.1 ∈ lefts := by
  induction lefts generalizing rights with
  | nil => simp at member
  | cons left lefts induction =>
      cases rights with
      | nil => simp at member
      | cons right rights =>
          simp only [List.zip_cons_cons, List.mem_cons] at member ⊢
          rcases member with rfl | member
          · exact .inl rfl
          · exact .inr (induction member)

/-- Equal zip arity pairs every right member with a left input. -/
theorem List.exists_fst_mem_zip_of_snd_mem
    {lefts : List α} {rights : List β}
    (lengths : lefts.length = rights.length) {right : β}
    (member : right ∈ rights) :
    ∃ left, (left, right) ∈ lefts.zip rights := by
  induction lefts generalizing rights with
  | nil =>
      cases rights <;> simp at lengths member
  | cons left lefts induction =>
      cases rights with
      | nil => simp at lengths
      | cons head rights =>
          simp only [List.length_cons, Nat.succ.injEq] at lengths
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨left, by simp⟩
          · obtain ⟨found, foundMember⟩ := induction lengths member
            exact ⟨found, by simp [foundMember]⟩

/-- Pointwise facts over the right side of a zip survive flattening. -/
theorem List.forall_mem_flatten_of_zip
    {lefts : List α} {rights : List (List β)} {P : β → Prop}
    (lengths : lefts.length = rights.length)
    (pointwise : ∀ pair ∈ lefts.zip rights,
      ∀ value ∈ pair.2, P value) :
    ∀ value ∈ rights.flatten, P value := by
  induction lefts generalizing rights with
  | nil =>
      cases rights <;> simp at lengths ⊢
  | cons left lefts induction =>
      cases rights with
      | nil => simp at lengths
      | cons right rights =>
          simp only [List.length_cons, Nat.succ.injEq] at lengths
          intro value member
          simp only [List.flatten_cons, List.mem_append] at member
          rcases member with member | member
          · exact pointwise (left, right) (by simp) value member
          · exact induction lengths
              (fun pair pairMember => pointwise pair (by simp [pairMember]))
              value member

/-- Flattening a list of pristine environments remains pristine. -/
theorem EnvPristine.flatten_map_snd
    {results : List (α × Env)}
    (pointwise : ∀ result ∈ results, EnvPristine result.2) :
    EnvPristine ((results.map Prod.snd).flatten) := by
  induction results with
  | nil => exact .nil
  | cons result results induction =>
      simpa using (pointwise result (by simp)).append
        (induction (fun other member => pointwise other (by simp [member])))

/-- Extending a pristine closure environment with an argument is pristine. -/
theorem pushArg_pristine
    {self : Option String} {environment : Env} {parameter : String}
    {body : Expr} {argument : Value}
    (environmentPristine : EnvPristine environment)
    (argumentPristine : ValuePristine argument) :
    EnvPristine (pushArg self environment parameter body argument) := by
  cases self with
  | none => exact .cons argumentPristine environmentPristine
  | some name =>
      exact .cons argumentPristine
        (.cons (.closure environmentPristine) environmentPristine)

/-!
The five operational judgments are mutually recursive.  `Step.rec` supplies
all five induction hypotheses while returning the state-boundary result; the
auxiliary motives make the fact proved for each nested judgment explicit.
-/

/-- One concrete state step preserves the pristine public-state boundary. -/
theorem Step.pristine
    {SF : RuntimeSigF} {state : MState} {states : List MState}
    (reduction : Step SF state states)
    (statePristine : MStatePristine state) :
    ∀ next ∈ states, MStatePristine next := by
  refine Step.rec (SF := SF)
    (motive_1 := fun environment _ value _ =>
      EnvPristine environment → ValuePristine value)
    (motive_2 := fun environment _ _ result _ =>
      EnvPristine environment → PPMOutputPristine result)
    (motive_3 := fun environment pattern matcher value continuations
        substitution _ =>
      EnvPristine environment →
      ValuePristine value →
      MAtomInputPristine pattern matcher →
      MAtomOutputPristine continuations substitution)
    (motive_4 := fun state states _ =>
      MStatePristine state →
      ∀ next ∈ states, MStatePristine next)
    (motive_5 := fun state substitutions _ =>
      MStatePristine state → SearchOutputPristine substitutions)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep
    reduction statePristine
  case evar =>
    intro environment name value found environmentPristine
    exact environmentPristine.lookup found
  case elam =>
    intro environment parameter body environmentPristine
    exact .closure environmentPristine
  case efix =>
    intro environment name parameter body environmentPristine
    exact .closure environmentPristine
  case eapp =>
    intro environment function argument self closureEnvironment parameter body
      argumentValue value functionEvaluation argumentEvaluation bodyEvaluation
      functionIH argumentIH bodyIH environmentPristine
    have functionPristine := functionIH environmentPristine
    have argumentPristine := argumentIH environmentPristine
    cases functionPristine with
    | closure capturedPristine =>
        exact bodyIH (pushArg_pristine capturedPristine argumentPristine)
  case elit =>
    intro environment literal environmentPristine
    exact .lit
  case etuple =>
    intro environment expressions values lengths evaluations evaluationsIH
      environmentPristine
    exact .tuple (valuesPristine_of_zip lengths (fun pair member =>
      evaluationsIH pair member environmentPristine))
  case ector =>
    intro environment name expressions values lengths evaluations evaluationsIH
      environmentPristine
    exact .ctor (valuesPristine_of_zip lengths (fun pair member =>
      evaluationsIH pair member environmentPristine))
  case eprim =>
    intro environment operation expressions values value lengths evaluations
      primitive evaluationsIH environmentPristine
    exact primEval_pristine
      (valuesPristine_of_zip lengths (fun pair member =>
        evaluationsIH pair member environmentPristine)) primitive
  case elet =>
    intro environment name bound body boundValue value boundEvaluation
      bodyEvaluation boundIH bodyIH environmentPristine
    exact bodyIH (.cons (boundIH environmentPristine) environmentPristine)
  case esomething =>
    intro environment environmentPristine
    exact .something
  case ematcher =>
    intro environment clauses environmentPristine
    exact .matcherLiteral environmentPristine
  case ematchAll =>
    intro environment target matcher pattern body targetValue matcherValue
      substitutions values targetEvaluation matcherEvaluation search lengths
      evaluations targetIH matcherIH searchIH evaluationsIH
      environmentPristine
    have targetPristine := targetIH environmentPristine
    have matcherPristine := matcherIH environmentPristine
    have initialPristine : MStatePristine
        ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩ :=
      ⟨.cons (.atom ⟨matcherPristine, targetPristine⟩) .nil,
        environmentPristine, .nil⟩
    have substitutionsPristine := searchIH initialPristine
    apply mkListV_pristine
    exact valuesPristine_of_zip lengths (fun pair member =>
      evaluationsIH pair member
        ((substitutionsPristine pair.1
            (List.fst_mem_of_mem_zip member)).append environmentPristine))
  case phole =>
    intro environment pattern environmentPristine
    exact .nil
  case pwild =>
    intro environment environmentPristine
    exact .nil
  case ppval =>
    intro environment name expression value evaluation evaluationIH
      environmentPristine
    exact .cons (evaluationIH environmentPristine) .nil
  case pctor =>
    intro environment name pps patterns results lengths resultLengths matchings
      matchingsIH environmentPristine
    apply EnvPristine.flatten_map_snd
    intro result resultMember
    obtain ⟨input, inputMember⟩ :=
      List.exists_fst_mem_zip_of_snd_mem resultLengths resultMember
    exact matchingsIH (input, result) inputMember environmentPristine
  case ptuple =>
    intro environment pps patterns results lengths resultLengths matchings
      matchingsIH environmentPristine
    apply EnvPristine.flatten_map_snd
    intro result resultMember
    obtain ⟨input, inputMember⟩ :=
      List.exists_fst_mem_zip_of_snd_mem resultLengths resultMember
    exact matchingsIH (input, result) inputMember environmentPristine
  case pfail =>
    intros
    trivial
  case msomeWC =>
    intro environment value environmentPristine valuePristine matcherPristine
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp at member
    subst atoms
    exact .nil
  case msomeVar =>
    intro environment name value environmentPristine valuePristine
      matcherPristine
    refine ⟨.cons valuePristine .nil, ?_⟩
    intro atoms member
    simp at member
    subst atoms
    exact .nil
  case msomeValEq =>
    intro environment expression value expected evaluation equality evaluationIH
      environmentPristine valuePristine matcherPristine
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp at member
    subst atoms
    exact .nil
  case msomeValNeq =>
    intro environment expression value expected evaluation equality evaluationIH
      environmentPristine valuePristine matcherPristine
    exact ⟨.nil, fun atoms member => by contradiction⟩
  case mand =>
    intro environment left right matcher value environmentPristine
      valuePristine matcherPristine
    have actualMatcherPristine : ValuePristine matcher := by
      rcases matcherPristine with matcherPristine |
        ⟨found, original, current, matcherEquality, foundPristine,
          dispatchable⟩
      · exact matcherPristine
      · simp [Pattern.isMatcherDispatchable] at dispatchable
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp at member
    subst atoms
    exact .cons (.atom ⟨actualMatcherPristine, valuePristine⟩)
      (.cons (.atom ⟨actualMatcherPristine, valuePristine⟩) .nil)
  case mor =>
    intro environment left right matcher value environmentPristine
      valuePristine matcherPristine
    have actualMatcherPristine : ValuePristine matcher := by
      rcases matcherPristine with matcherPristine |
        ⟨found, original, current, matcherEquality, foundPristine,
          dispatchable⟩
      · exact matcherPristine
      · simp [Pattern.isMatcherDispatchable] at dispatchable
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp at member
    rcases member with rfl | rfl
    · exact .cons (.atom ⟨actualMatcherPristine, valuePristine⟩) .nil
    · exact .cons (.atom ⟨actualMatcherPristine, valuePristine⟩) .nil
  case mtuple =>
    intro environment patterns matchers values patternLength valueLength
      environmentPristine valuePristine matcherPristine
    have matchersPristine : ValuesPristine matchers := by
      rcases matcherPristine with matcherPristine |
        ⟨found, original, current, matcherEquality, foundPristine,
          dispatchable⟩
      · cases matcherPristine with
        | tuple result => exact result
      · cases matcherEquality
    have valuesPristine : ValuesPristine values := by
      cases valuePristine with
      | tuple result => exact result
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simpa [List.map_map, Function.comp_def] using
      stackPristine_atoms_zip patternLength valueLength
        matchersPristine valuesPristine
  case mprodSome =>
    intro environment pattern matchers value primitive environmentPristine
      valuePristine matcherPristine
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    exact .cons (.atom ⟨.something, valuePristine⟩) .nil
  case mppfail =>
    intro environment matcherEnvironment original pattern value pp next arms
      clauses continuations substitution dispatch ppFailure recursive ppIH
      recursiveIH environmentPristine valuePristine matcherPristine
    have capturedPristine := matcherPristine.matcherEnvironment
    exact recursiveIH environmentPristine valuePristine
      (.inr ⟨matcherEnvironment, original, clauses, rfl,
        capturedPristine, dispatch⟩)
  case mdpfail =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment continuations substitution dispatch
      ppSuccess dataFailure recursive ppIH recursiveIH environmentPristine
      valuePristine matcherPristine
    have capturedPristine := matcherPristine.matcherEnvironment
    exact recursiveIH environmentPristine valuePristine
      (.inr ⟨matcherEnvironment, original, .mk pp next arms :: clauses,
        rfl, capturedPristine, dispatch⟩)
  case mmatcher =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment dataEnvironment decomposition tuples
      valueLists matcherValue matchers dispatch ppSuccess dataSuccess
      bodyEvaluation listDecode tupleDecodes nextEvaluation matcherDecode ppIH
      bodyIH nextIH environmentPristine valuePristine matcherPristine
    have capturedPristine := matcherPristine.matcherEnvironment
    have ppEnvironmentPristine := ppIH environmentPristine
    have dataEnvironmentPristine :=
      pdMatch_pristine valuePristine dataSuccess
    have decompositionPristine := bodyIH
      ((dataEnvironmentPristine.append ppEnvironmentPristine).append
        capturedPristine)
    have tuplesPristine :=
      listOfV_pristine decompositionPristine listDecode
    have valueListsPristine :=
      decodeTuple_mapM_pristine tuplesPristine tupleDecodes
    have matcherValuePristine := nextIH capturedPristine
    have matchersPristine :=
      decodeTuple_pristine matcherValuePristine matcherDecode
    refine ⟨.nil, ?_⟩
    intro atoms member
    simp only [List.mem_map] at member
    obtain ⟨values, valuesMember, rfl⟩ := member
    simpa [List.map_map, Function.comp_def] using
      (stackPristine_atoms_zip
        (decodeTuple_length matcherDecode).symm
        ((decodeTuple_length matcherDecode).trans
          (decodeTuple_mapM_member tupleDecodes values valuesMember).symm)
        matchersPristine (valueListsPristine values valuesMember))
  case sreduce =>
    intro stack environment substitution pattern matcher value continuations
      new atomReduction atomIH statePristine
    rcases statePristine with ⟨stackPristine, environmentPristine,
      substitutionPristine⟩
    cases stackPristine with
    | cons treePristine tailPristine =>
        cases treePristine with
        | atom atomPristine =>
            rcases atomIH (substitutionPristine.append environmentPristine)
                atomPristine.2 (.inl atomPristine.1) with
              ⟨newPristine, continuationsPristine⟩
            intro next member
            simp only [List.mem_map] at member
            obtain ⟨atoms, atomsMember, rfl⟩ := member
            exact ⟨(continuationsPristine atoms atomsMember).append
                tailPristine,
              environmentPristine, newPristine.append substitutionPristine⟩
  case spatfunEnter =>
    intro stack environment substitution name arguments matcher value runtime
      found length statePristine
    rcases statePristine with ⟨stackPristine, environmentPristine,
      substitutionPristine⟩
    cases stackPristine with
    | cons treePristine tailPristine =>
        cases treePristine with
        | atom atomPristine =>
            intro next member
            simp only [List.mem_singleton] at member
            subst next
            exact ⟨.cons
                (.mnode (.cons (.atom atomPristine) .nil)
                  environmentPristine .nil)
                tailPristine,
              environmentPristine, substitutionPristine⟩
  case smnodeStep =>
    intro stack environment substitution tree innerStack capturedEnvironment
      innerSubstitution piE states bypass nested nestedIH statePristine
    rcases statePristine with ⟨stackPristine, environmentPristine,
      substitutionPristine⟩
    cases stackPristine with
    | cons treePristine tailPristine =>
        cases treePristine with
        | mnode innerStackPristine capturedPristine innerSubstPristine =>
            have nestedStatesPristine := nestedIH
              ⟨innerStackPristine, capturedPristine, innerSubstPristine⟩
            intro next member
            simp only [List.mem_map] at member
            obtain ⟨innerState, innerMember, rfl⟩ := member
            rcases nestedStatesPristine innerState innerMember with
              ⟨newInnerStackPristine, _, newInnerSubstPristine⟩
            exact ⟨.cons
                (.mnode newInnerStackPristine capturedPristine
                  newInnerSubstPristine)
                tailPristine,
              environmentPristine, substitutionPristine⟩
  case smnodeVarpat =>
    intro stack environment substitution name pattern matcher value innerStack
      capturedEnvironment innerSubstitution piE found statePristine
    rcases statePristine with ⟨stackPristine, environmentPristine,
      substitutionPristine⟩
    cases stackPristine with
    | cons treePristine tailPristine =>
        cases treePristine with
        | mnode innerStackPristine capturedPristine innerSubstPristine =>
            cases innerStackPristine with
            | cons innerTreePristine innerTailPristine =>
                cases innerTreePristine with
                | atom atomPristine =>
                    intro next member
                    simp only [List.mem_singleton] at member
                    subst next
                    exact ⟨.cons (.atom atomPristine)
                        (.cons
                          (.mnode innerTailPristine capturedPristine
                            innerSubstPristine)
                          tailPristine),
                      environmentPristine, substitutionPristine⟩
  case smnodeDone =>
    intro stack environment substitution capturedEnvironment innerSubstitution
      piE statePristine
    rcases statePristine with ⟨stackPristine, environmentPristine,
      substitutionPristine⟩
    cases stackPristine with
    | cons treePristine tailPristine =>
        intro next member
        simp only [List.mem_singleton] at member
        subst next
        exact ⟨tailPristine, environmentPristine, substitutionPristine⟩
  case sdone =>
    intro environment substitution statePristine result member
    simp only [List.mem_singleton] at member
    subst result
    exact statePristine.2.2
  case sstep =>
    intro state states substitutions reduction lengths searches stepIH searchesIH
      statePristine
    have statesPristine := stepIH statePristine
    exact List.forall_mem_flatten_of_zip lengths
      (fun pair pairMember substitution substitutionMember =>
        searchesIH pair pairMember
          (statesPristine pair.1 (List.fst_mem_of_mem_zip pairMember))
          substitution substitutionMember)

/-! ## Narrow value-pattern capture admissibility -/

mutual

/--
Every `#$x` site that PPM evaluates is typable in the atom's *input* binding
context.  In particular, it cannot depend on variables merely captured by an
earlier PP hole in the same compound pattern.
-/
inductive CaptureAdm (signature : FrozenSig)
    (context : Context) (input : MonoCtx) :
    PPat → Pattern → Ty → MonoCtx → Prop where
  | hole {pattern target} :
      CaptureAdm signature context input .hole pattern target []
  | wild {target} :
      CaptureAdm signature context input .wild .wild target []
  | pval {name expression target} :
      HasTy signature (input.toContext ++ context) expression target →
      CaptureAdm signature context input (.pval name) (.pval expression) target
        [(name, target)]
  | ctor {name entry pps patterns targets result bindings} :
      signature.findPatternCtor name = some entry →
      CaptureAdms signature context input pps patterns targets bindings →
      entry.Inst targets result →
      CaptureAdm signature context input (.ctor name pps)
        (.pctor name patterns) result bindings
  | tuple {pps patterns targets bindings} :
      CaptureAdms signature context input pps patterns targets bindings →
      CaptureAdm signature context input (.tuple pps) (.ptuple patterns)
        (.prod targets) bindings

/-- Pointwise capture admissibility at one fixed atom-input context. -/
inductive CaptureAdms (signature : FrozenSig)
    (context : Context) (input : MonoCtx) :
    List PPat → List Pattern → List Ty → MonoCtx → Prop where
  | nil : CaptureAdms signature context input [] [] [] []
  | cons {pp pattern target bindings pps patterns targets restBindings} :
      CaptureAdm signature context input pp pattern target bindings →
      CaptureAdms signature context input pps patterns targets restBindings →
      CaptureAdms signature context input
        (pp :: pps) (pattern :: patterns) (target :: targets)
        (bindings ++ restBindings)

end

/-- Terminal value patterns retain their expression typing and input. -/
theorem TerminalPatternResolution.pval_parts
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx} {capability : Cap}
    {target : Ty} {expression : Expr}
    (typing : TerminalPatternResolution signature prevailing context parameters
      input (.pval expression) capability target output) :
    output = input ∧
      HasTy signature (input.toContext ++ context) expression target := by
  cases typing with
  | pval fresh separate expressionTyping => exact ⟨rfl, expressionTyping⟩

/-- Inversion of a terminal constructor pattern at its actual indices. -/
theorem TerminalPatternResolution.ctor_parts
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx} {capability : Cap}
    {target : Ty} {name : String} {patterns : List Pattern}
    (typing : TerminalPatternResolution signature prevailing context parameters
      input (.pctor name patterns) capability target output) :
    ∃ entry duals,
      signature.findPatternCtor name = some entry ∧
      TerminalPatternResolutions signature prevailing context parameters input
        patterns duals output ∧
      entry.CapCompatible (duals.map Dual.cap) capability ∧
      entry.Inst (duals.map Dual.target) target := by
  cases typing with
  | ctor find children caps inst => exact ⟨_, _, find, children, caps, inst⟩

/-- Inversion of a terminal tuple pattern at its actual indices. -/
theorem TerminalPatternResolution.tuple_parts
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx} {capability : Cap}
    {target : Ty} {patterns : List Pattern}
    (typing : TerminalPatternResolution signature prevailing context parameters
      input (.ptuple patterns) capability target output) :
    ∃ duals,
      TerminalPatternResolutions signature prevailing context parameters input
        patterns duals output ∧
      capability = .prod (duals.map Dual.cap) ∧
      target = .prod (duals.map Dual.target) := by
  cases typing with
  | tuple children => exact ⟨_, children, rfl, rfl⟩

/-- Empty terminal pattern lists expose their exact endpoint indices. -/
theorem TerminalPatternResolutions.nil_parts
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx} {duals : List Dual}
    (typing : TerminalPatternResolutions signature prevailing context parameters
      input [] duals output) : duals = [] ∧ output = input := by
  cases typing
  exact ⟨rfl, rfl⟩

/-- Nonempty terminal pattern lists expose their threaded head and tail. -/
theorem TerminalPatternResolutions.cons_parts
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {pattern : Pattern} {patterns : List Pattern} {duals : List Dual}
    (typing : TerminalPatternResolutions signature prevailing context parameters
      input (pattern :: patterns) duals output) :
    ∃ capability target rest middle,
      duals = ⟨capability, target⟩ :: rest ∧
      TerminalPatternResolution signature prevailing context parameters input
        pattern capability target middle ∧
      TerminalPatternResolutions signature prevailing context parameters middle
        patterns rest output := by
  cases typing with
  | cons head tail => exact ⟨_, _, _, _, rfl, head, tail⟩

private theorem ppShapeOKList_of_ppm_children
    {pps : List PPat} {patterns : List Pattern}
    {results : List (List Pattern × Env)}
    (lengthPP : pps.length = patterns.length)
    (lengthResults : (pps.zip patterns).length = results.length)
    (all : ∀ entry ∈ (pps.zip patterns).zip results,
      ppShapeOK entry.1.1 entry.1.2 = true) :
    ppShapeOKList pps patterns = true := by
  cases pps with
  | nil =>
      cases patterns with
      | cons pattern patterns => simp at lengthPP
      | nil => rfl
  | cons pp pps =>
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
        cases results with
        | nil => simp [List.zip_cons_cons] at lengthResults
        | cons result results =>
          have headShape : ppShapeOK pp pattern = true :=
            all ((pp, pattern), result) (by simp [List.zip_cons_cons])
          have tailShapes :
              ∀ entry ∈ (pps.zip patterns).zip results,
                ppShapeOK entry.1.1 entry.1.2 = true := by
            intro entry member
            exact all entry (by
              simp [List.zip_cons_cons]
              exact .inr member)
          simp only [ppShapeOKList, Bool.and_eq_true]
          exact ⟨headShape,
            ppShapeOKList_of_ppm_children (by simpa using lengthPP)
              (by simpa [List.zip_cons_cons] using lengthResults)
              tailShapes⟩

private theorem PPM.success_shape_result
    {SF : RuntimeSigF} {environment : Env} {pp : PPat} {pattern : Pattern}
    {result : Option (List Pattern × Env)}
    (matching : PPM SF environment pp pattern result) :
    match result with
    | some _ => ppShapeOK pp pattern = true
    | none => True := by
  refine PPM.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ pp pattern result _ =>
      match result with
      | some _ => ppShapeOK pp pattern = true
      | none => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep matching
  case phole => intros; rfl
  case pwild => intros; rfl
  case ppval => intros; rfl
  case pctor =>
    intro runtimeEnvironment name pps patterns results lengthPP lengthResults
      all childrenIH
    simp [ppShapeOK, ppShapeOKList_of_ppm_children lengthPP lengthResults
      childrenIH]
  case ptuple =>
    intro runtimeEnvironment pps patterns results lengthPP lengthResults all
      childrenIH
    exact ppShapeOKList_of_ppm_children lengthPP lengthResults childrenIH
  case pfail => intros; trivial
  all_goals intros; trivial

/-- Every successful primitive-pattern match has the corresponding shape. -/
theorem PPM.success_shape
    {SF : RuntimeSigF} {environment : Env} {pp : PPat} {pattern : Pattern}
    {captures : List Pattern} {ppEnvironment : Env}
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment))) : ppShapeOK pp pattern = true :=
  matching.success_shape_result

/--
The core PP order makes value-pattern capture admissibility derivable from the
actual clause and user-pattern typings.  The auxiliary Boolean indices thread
whether a hole has already occurred; while they remain `false`, user-pattern
typing cannot have extended the atom's input bindings.
-/
theorem captureAdm_of_order_at
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {pp : PPat} {target : Ty}
    {holes : List Dual} {ppBindings : MonoCtx}
    (ppTyping : TerminalPPatResolution signature prevailing pp target holes
      ppBindings) :
    ∀ {atRoot : Bool} {holeCapabilities : List Cap}
      {patternPrevailing : Subst} {context : Context}
      {parameters : PatternCtx} {rootInput current output : MonoCtx}
      {pattern : Pattern} {patternCapability : Cap}
      {seen finished : Bool},
      PPatOrder seen pp finished →
      (seen = false → current = rootInput) →
      PPatCapsAt signature atRoot pp holeCapabilities patternCapability →
      TerminalPatternResolution signature patternPrevailing context parameters
        current pattern patternCapability target output →
      ppShapeOK pp pattern = true →
      CaptureAdm signature context rootInput pp pattern target ppBindings ∧
        (finished = false → output = rootInput) := by
  refine TerminalPPatResolution.rec
    (motive_1 := fun pp target holes ppBindings _ =>
      ∀ {atRoot : Bool} {holeCapabilities : List Cap}
        {patternPrevailing : Subst} {context : Context}
        {parameters : PatternCtx} {rootInput current output : MonoCtx}
        {pattern : Pattern} {patternCapability : Cap}
        {seen finished : Bool},
        PPatOrder seen pp finished →
        (seen = false → current = rootInput) →
        PPatCapsAt signature atRoot pp holeCapabilities patternCapability →
        TerminalPatternResolution signature patternPrevailing context
          parameters current pattern patternCapability target output →
        ppShapeOK pp pattern = true →
        CaptureAdm signature context rootInput pp pattern target ppBindings ∧
          (finished = false → output = rootInput))
    (motive_2 := fun pps targets holes ppBindings _ =>
      ∀ {holeCapabilities childCapabilities : List Cap}
        {patternPrevailing : Subst} {context : Context}
        {parameters : PatternCtx} {rootInput current output : MonoCtx}
        {patterns : List Pattern} {patternDuals : List Dual}
        {seen finished : Bool},
        PPatsOrder seen pps finished →
        (seen = false → current = rootInput) →
        PPatCapsList signature pps holeCapabilities childCapabilities →
        TerminalPatternResolutions signature patternPrevailing context
          parameters current patterns patternDuals output →
        patternDuals.map Dual.cap = childCapabilities →
        patternDuals.map Dual.target = targets →
        ppShapeOKList pps patterns = true →
        CaptureAdms signature context rootInput pps patterns targets ppBindings ∧
          (finished = false → output = rootInput))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ppTyping
  · intro rawTarget varId fresh atRoot holeCapabilities patternPrevailing
      context parameters rootInput current output pattern patternCapability
      seen finished order beforeHole capTyping patternTyping shape
    cases order
    exact ⟨CaptureAdm.hole, fun impossible => by contradiction⟩
  · intro rawTarget atRoot holeCapabilities patternPrevailing context
      parameters rootInput current output pattern patternCapability seen
      finished order beforeHole capTyping patternTyping shape
    cases order
    cases pattern <;> simp [ppShapeOK] at shape
    have outputEquality := patternTyping.wild_output
    subst output
    exact ⟨CaptureAdm.wild, fun notSeen => beforeHole notSeen⟩
  · intro name rawTarget atRoot holeCapabilities patternPrevailing context
      parameters rootInput current output pattern patternCapability seen
      finished order beforeHole capTyping patternTyping shape
    cases order
    cases pattern <;> simp [ppShapeOK] at shape
    obtain ⟨outputEquality, expressionTyping⟩ := patternTyping.pval_parts
    subst output
    have currentEq := beforeHole rfl
    subst current
    constructor
    · simpa [MonoCtx.applySubst] using
        (CaptureAdm.pval expressionTyping)
    · intro _
      rfl
  · intro name entry pps targets result holes bindings ppFind ppsTyping
      ppInstance childrenIH atRoot holeCapabilities patternPrevailing context
      parameters rootInput current output pattern patternCapability seen
      finished order beforeHole capTyping patternTyping shape
    cases order with
    | ctor childrenOrder =>
      cases capTyping with
      | @ctor _ _ capEntry _ _ childCapabilities _ capFind capsList
          capCompatible =>
        cases pattern <;> simp [ppShapeOK] at shape
        rename_i patternName patterns
        rcases shape with ⟨nameEquality, childrenShape⟩
        have patternNameEquality : patternName = name := by
          simpa using nameEquality.symm
        subst patternName
        obtain ⟨patternEntry, patternDuals, patternFind, patternsTyping,
            patternCompatible, patternInstance⟩ := patternTyping.ctor_parts
        have capEntryEquality : capEntry = entry :=
          Option.some.inj (capFind.symm.trans ppFind)
        subst capEntry
        have patternEntryEquality : patternEntry = entry :=
          Option.some.inj (patternFind.symm.trans ppFind)
        subst patternEntry
        have capsEquality :
            patternDuals.map Dual.cap = childCapabilities :=
          signatureWF.patternCapArgsUnique ppFind patternCompatible
            capCompatible
        have targetsEquality : patternDuals.map Dual.target = targets :=
          signatureWF.patternInstArgsUnique ppFind patternInstance ppInstance
        obtain ⟨childrenAdm, finishedBindings⟩ :=
          childrenIH childrenOrder beforeHole capsList patternsTyping
            capsEquality targetsEquality childrenShape
        exact ⟨CaptureAdm.ctor ppFind childrenAdm ppInstance,
          finishedBindings⟩
  · intro pps targets holes bindings ppsTyping childrenIH atRoot
      holeCapabilities patternPrevailing context parameters rootInput current
      output pattern patternCapability seen finished order beforeHole capTyping
      patternTyping shape
    cases order with
    | tuple childrenOrder =>
      cases capTyping with
      | tuple capsList =>
        cases pattern <;> simp [ppShapeOK] at shape
        rename_i patterns
        obtain ⟨patternDuals, patternsTyping, capEquality, targetEquality⟩ :=
          patternTyping.tuple_parts
        have capsEquality : patternDuals.map Dual.cap = _ :=
          (Cap.prod.inj capEquality).symm
        have targetsEquality : patternDuals.map Dual.target = targets :=
          (Ty.prod.inj targetEquality).symm
        obtain ⟨childrenAdm, finishedBindings⟩ :=
          childrenIH childrenOrder beforeHole capsList patternsTyping
            capsEquality targetsEquality shape
        exact ⟨CaptureAdm.tuple childrenAdm, finishedBindings⟩
  · intro holeCapabilities childCapabilities patternPrevailing context
      parameters rootInput current output patterns patternDuals seen finished
      order beforeHole capsTyping patternsTyping capsEquality targetsEquality
      shape
    cases order
    cases capsTyping
    cases patterns <;> simp [ppShapeOKList] at shape
    obtain ⟨rfl, rfl⟩ := patternsTyping.nil_parts
    exact ⟨CaptureAdms.nil, fun notSeen => beforeHole notSeen⟩
  · intro pp target headHoles headBindings pps targets tailHoles
      tailBindings headTyping tailTyping distinct headIH tailIH holeCapabilities
      childCapabilities
      patternPrevailing context parameters rootInput current output patterns
      patternDuals seen finished order beforeHole capsTyping patternsTyping
      capsEquality targetsEquality shape
    cases order with
    | cons headOrder tailOrder =>
      cases capsTyping with
      | @cons _ _ headCapHoles tailCapHoles headCapability tailCapabilities
          headCaps tailCaps =>
        cases patterns with
        | nil => simp [ppShapeOKList] at shape
        | cons pattern patterns =>
          obtain ⟨patternCap, patternTarget, patternDualsTail, middle, rfl,
              patternHead, patternTail⟩ := patternsTyping.cons_parts
          simp only [List.map_cons, List.cons.injEq] at capsEquality
          simp only [List.map_cons, List.cons.injEq] at targetsEquality
          obtain ⟨headCapEquality, tailCapsEquality⟩ := capsEquality
          obtain ⟨headTargetEquality, tailTargetsEquality⟩ :=
            targetsEquality
          rw [headCapEquality, headTargetEquality] at patternHead
          simp only [ppShapeOKList, Bool.and_eq_true] at shape
          obtain ⟨headAdm, middleBeforeHole⟩ :=
            headIH headOrder beforeHole headCaps patternHead shape.1
          obtain ⟨tailAdm, finishedBindings⟩ :=
            tailIH tailOrder middleBeforeHole tailCaps patternTail
              tailCapsEquality tailTargetsEquality shape.2
          exact ⟨CaptureAdms.cons headAdm tailAdm, finishedBindings⟩

/-- Core-ordered successful PPM sites have no external capture premise. -/
theorem captureAdm_of_coreOrder
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env}
    {ppPrevailing patternPrevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {pp : PPat} {pattern : Pattern} {capability : Cap} {target : Ty}
    {holes : List Dual} {ppBindings : MonoCtx}
    {captures : List Pattern} {ppEnvironment : Env}
    (order : PPatCoreOrder pp)
    (ppTyping : ResolvedPPatTy signature ppPrevailing pp target holes
      ppBindings)
    (capTyping : PPatCapsAt signature true pp (holes.map Dual.cap) capability)
    (patternTyping : ResolvedPatternTy signature patternPrevailing context
      parameters input pattern capability target output)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment))) :
    CaptureAdm signature context input pp pattern target ppBindings := by
  obtain ⟨finished, ordered⟩ := order
  have shape := matching.success_shape
  exact (captureAdm_of_order_at signatureWF ppTyping.terminal ordered
    (fun _ => rfl) capTyping patternTyping.terminal shape).1

/--
PPM's value environment is typed when its narrow `#$x` evaluations preserve
the types supplied by `CaptureAdm`.  The function premise is discharged by
the corresponding `Eval` induction hypotheses in the final combined proof;
it is not exposed by the public safety theorem.
-/
theorem ppm_environment_typed
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {input : MonoCtx} {environment : Env}
    (evalPreserve :
      ∀ {expression value target},
        Eval SF environment expression value →
        HasTy signature (input.toContext ++ context) expression target →
        ValueTy signature value target)
    {pp : PPat} {pattern : Pattern} {target : Ty} {bindings : MonoCtx}
    {captures : List Pattern} {ppEnvironment : Env}
    (admissible : CaptureAdm signature context input pp pattern target bindings)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment))) :
    MonoEnvTys signature bindings ppEnvironment := by
  refine CaptureAdm.rec
    (motive_1 := fun pp pattern target bindings _ =>
      ∀ {captures : List Pattern} {ppEnvironment : Env},
        PPM SF environment pp pattern (some (captures, ppEnvironment)) →
        MonoEnvTys signature bindings ppEnvironment)
    (motive_2 := fun pps patterns targets bindings _ =>
      ∀ {results : List (List Pattern × Env)},
        pps.length = patterns.length →
        (pps.zip patterns).length = results.length →
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
        MonoEnvTys signature bindings ((results.map Prod.snd).flatten))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ admissible matching
  · intro pattern target captures ppEnvironment matching
    cases matching
    exact .nil
  · intro target captures ppEnvironment matching
    cases matching
    exact .nil
  · intro name expression target expressionTyping captures ppEnvironment
      matching
    cases matching with
    | pval evaluation =>
        exact .cons (evalPreserve evaluation expressionTyping) .nil
  · intro name entry pps patterns targets result bindings find children
      instantiation childrenIH captures ppEnvironment matching
    cases matching with
    | ctor lengthPP lengthResults all =>
        exact childrenIH lengthPP lengthResults all
  · intro pps patterns targets bindings children childrenIH captures
      ppEnvironment matching
    cases matching with
    | tuple lengthPP lengthResults all =>
        exact childrenIH lengthPP lengthResults all
  · intro results lengthPP lengthResults all
    cases results with
    | nil => exact .nil
    | cons result results => simp at lengthResults
  · intro pp pattern target bindings pps patterns targets restBindings head
      tail headIH tailIH results lengthPP lengthResults all
    cases results with
    | nil => simp [List.zip_cons_cons] at lengthResults
    | cons result results =>
        obtain ⟨captures, headEnvironment⟩ := result
        have headMatching :
            PPM SF environment pp pattern
              (some (captures, headEnvironment)) :=
          all ((pp, pattern), (captures, headEnvironment))
            (by simp [List.zip_cons_cons])
        have tailMatching :
            ∀ entry ∈ (pps.zip patterns).zip results,
              PPM SF environment entry.1.1 entry.1.2 (some entry.2) := by
          intro entry member
          exact all entry (by simp [List.zip_cons_cons]; exact .inr member)
        simpa [List.flatten_cons] using
          (headIH headMatching).append
            (tailIH (by simpa using lengthPP)
              (by simpa [List.zip_cons_cons] using lengthResults) tailMatching)

/-! ## Embedded-parameter occurrence discipline -/

/-- A pointwise no-embedding fact implies the Boolean list check. -/
theorem Pattern.noEmbedInOrList_eq_true_of_mem
    {patterns : List Pattern}
    (all : ∀ pattern ∈ patterns, pattern.noEmbedInOr = true) :
    Pattern.noEmbedInOrList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns induction =>
      simp only [Pattern.noEmbedInOrList, Bool.and_eq_true]
      exact ⟨all pattern (by simp), induction (fun entry member =>
        all entry (by simp [member]))⟩

/-- Every member of a list passing the Boolean check passes it individually. -/
theorem Pattern.noEmbedInOr_of_mem
    {patterns : List Pattern}
    (checked : Pattern.noEmbedInOrList patterns = true)
    {pattern : Pattern} (member : pattern ∈ patterns) :
    pattern.noEmbedInOr = true := by
  induction patterns with
  | nil => contradiction
  | cons head tail induction =>
      simp only [Pattern.noEmbedInOrList, Bool.and_eq_true] at checked
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact checked.1
      · exact induction checked.2 member

/- A pattern with no embedded occurrence satisfies the branch-local
no-embedding discipline. -/
mutual

theorem Pattern.noEmbedInOr_of_embedVars_nil :
    ∀ pattern : Pattern,
      pattern.embedVars = [] → pattern.noEmbedInOr = true
  | .pvar _, _ => rfl
  | .wild, _ => rfl
  | .pval _, _ => rfl
  | .embed _, equality => by simp [Pattern.embedVars] at equality
  | .pctor _ patterns, equality => by
      exact Pattern.noEmbedInOrList_of_embedVarsList_nil patterns equality
  | .pand left right, equality => by
      have parts : left.embedVars = [] ∧ right.embedVars = [] := by
        exact List.append_eq_nil_iff.mp
          (by simpa [Pattern.embedVars] using equality)
      simp only [Pattern.noEmbedInOr, Bool.and_eq_true]
      exact ⟨Pattern.noEmbedInOr_of_embedVars_nil left parts.1,
        Pattern.noEmbedInOr_of_embedVars_nil right parts.2⟩
  | .por left right, equality => by
      have parts : left.embedVars = [] ∧ right.embedVars = [] := by
        exact List.append_eq_nil_iff.mp
          (by simpa [Pattern.embedVars] using equality)
      simp [Pattern.noEmbedInOr, parts,
        Pattern.noEmbedInOr_of_embedVars_nil left parts.1,
        Pattern.noEmbedInOr_of_embedVars_nil right parts.2]
  | .papp _ patterns, equality => by
      exact Pattern.noEmbedInOrList_of_embedVarsList_nil patterns equality
  | .ptuple patterns, equality => by
      exact Pattern.noEmbedInOrList_of_embedVarsList_nil patterns equality

theorem Pattern.noEmbedInOrList_of_embedVarsList_nil :
    ∀ patterns : List Pattern,
      Pattern.embedVarsList patterns = [] →
      Pattern.noEmbedInOrList patterns = true
  | [], _ => rfl
  | pattern :: patterns, equality => by
      have parts : pattern.embedVars = [] ∧
          Pattern.embedVarsList patterns = [] := by
        exact List.append_eq_nil_iff.mp
          (by simpa [Pattern.embedVarsList] using equality)
      simp only [Pattern.noEmbedInOrList, Bool.and_eq_true]
      exact ⟨Pattern.noEmbedInOr_of_embedVars_nil pattern parts.1,
        Pattern.noEmbedInOrList_of_embedVarsList_nil patterns parts.2⟩

end

/- Actual resolution binds every embedded occurrence in the fixed parameter
context. -/
section

variable {signature : FrozenSig}

mutual

theorem TerminalPatternResolution.embedVars_bound
    : ∀ {prevailing : Subst} {context : Context}
        {parameters : PatternCtx} {bindings : MonoCtx} {pattern : Pattern}
        {capability : Cap} {target : Ty} {output : MonoCtx},
      TerminalPatternResolution signature prevailing context parameters
          bindings pattern capability target output →
        ∀ name ∈ pattern.embedVars,
          ∃ dual, parameters.find? name = some dual := by
  intro prevailing context parameters bindings pattern capability target output typing
  cases typing with
  | pvar => intros; contradiction
  | wild => intros; contradiction
  | pval => intros; contradiction
  | embed sourceFound actualFound =>
      intro sought member
      simp only [Pattern.embedVars, List.mem_singleton] at member
      subst sought
      exact ⟨_, actualFound⟩
  | tuple children =>
      exact @TerminalPatternResolutions.embedVarsList_bound
        (prevailing, context, parameters) _ _ _ _ children
  | ctor found children capCompatible instantiation =>
      exact @TerminalPatternResolutions.embedVarsList_bound
        (prevailing, context, parameters) _ _ _ _ children
  | and left right =>
      intro name member
      simp only [Pattern.embedVars, List.mem_append] at member
      rcases member with member | member
      · exact @TerminalPatternResolution.embedVars_bound prevailing
          context parameters _ _ _ _ _ left name member
      · exact @TerminalPatternResolution.embedVars_bound prevailing
          context parameters _ _ _ _ _ right name member
  | or left right =>
      intro name member
      simp only [Pattern.embedVars, List.mem_append] at member
      rcases member with member | member
      · exact @TerminalPatternResolution.embedVars_bound prevailing
          context parameters _ _ _ _ _ left name member
      · exact @TerminalPatternResolution.embedVars_bound prevailing
          context parameters _ _ _ _ _ right name member
  | app found children instantiation =>
      exact @TerminalPatternResolutions.embedVarsList_bound
        (prevailing, context, parameters) _ _ _ _ children
termination_by prevailing context parameters bindings pattern capability target
  output _typing => sizeOf pattern

theorem TerminalPatternResolutions.embedVarsList_bound
    (scope : Subst × Context × PatternCtx) : ∀ {bindings : MonoCtx}
        {patterns : List Pattern} {duals : List Dual} {output : MonoCtx},
      TerminalPatternResolutions signature scope.1 scope.2.1 scope.2.2
          bindings patterns duals output →
        ∀ name ∈ Pattern.embedVarsList patterns,
          ∃ dual, scope.2.2.find? name = some dual := by
  intro bindings patterns duals output typing
  cases typing with
  | nil => intros; contradiction
  | cons head tail =>
      intro name member
      simp only [Pattern.embedVarsList, List.mem_append] at member
      rcases member with member | member
      · exact @TerminalPatternResolution.embedVars_bound scope.1
          scope.2.1 scope.2.2 _ _ _ _ _ head name member
      · exact @TerminalPatternResolutions.embedVarsList_bound scope
          _ _ _ _ tail name member
termination_by bindings patterns duals output _typing => sizeOf patterns

end

end

/-- With no fixed pattern parameters, actual resolution rules out every
embedded occurrence. -/
theorem TerminalPatternResolution.embedVars_nil_of_parameters_nil
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {target : Ty} {output : MonoCtx}
    (typing : TerminalPatternResolution signature prevailing context []
      bindings pattern capability target output) :
    pattern.embedVars = [] := by
  cases occurrence : pattern.embedVars with
  | nil => rfl
  | cons name names =>
      obtain ⟨dual, found⟩ := typing.embedVars_bound name (by
        rw [occurrence]
        exact List.mem_cons_self)
      simp [PatternCtx.find?] at found

/-- A top-level resolved pattern satisfies the state no-embedding invariant. -/
theorem ResolvedPatternTy.noEmbedInOr_of_parameters_nil
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {target : Ty} {output : MonoCtx}
    (typing : ResolvedPatternTy signature prevailing context [] bindings
      pattern capability target output) :
    pattern.noEmbedInOr = true :=
  Pattern.noEmbedInOr_of_embedVars_nil pattern
    typing.terminal.embedVars_nil_of_parameters_nil

/-! ## Consequences of checked pattern-function linearity -/

mutual

/-- A successful linear traversal computes the ordinary embed traversal. -/
theorem Pattern.embedVars_eq_of_linearEmbeds :
    ∀ (pattern : Pattern) {names : List String},
      pattern.linearEmbeds = some names → pattern.embedVars = names
  | .pvar _, _, equality => by
      simpa [Pattern.linearEmbeds, Pattern.embedVars] using
        congrArg Option.get! equality
  | .wild, _, equality => by
      simpa [Pattern.linearEmbeds, Pattern.embedVars] using
        congrArg Option.get! equality
  | .pval _, _, equality => by
      simpa [Pattern.linearEmbeds, Pattern.embedVars] using
        congrArg Option.get! equality
  | .embed name, _, equality => by
      simpa [Pattern.linearEmbeds, Pattern.embedVars] using
        congrArg Option.get! equality
  | .pctor name patterns, names, equality => by
      exact Pattern.embedVarsList_eq_of_linearEmbedsList patterns equality
  | .pand left right, names, equality => by
      cases leftResult : left.linearEmbeds with
      | none => simp [Pattern.linearEmbeds, leftResult] at equality
      | some leftNames =>
          cases rightResult : right.linearEmbeds with
          | none =>
              simp [Pattern.linearEmbeds, leftResult, rightResult] at equality
          | some rightNames =>
              have namesEquality : leftNames ++ rightNames = names := by
                simpa [Pattern.linearEmbeds, leftResult, rightResult] using
                  equality
              rw [← namesEquality]
              simp only [Pattern.embedVars]
              rw [Pattern.embedVars_eq_of_linearEmbeds left leftResult,
                Pattern.embedVars_eq_of_linearEmbeds right rightResult]
  | .por left right, names, equality => by
      simp [Pattern.linearEmbeds] at equality
  | .papp name patterns, names, equality => by
      exact Pattern.embedVarsList_eq_of_linearEmbedsList patterns equality
  | .ptuple patterns, names, equality => by
      exact Pattern.embedVarsList_eq_of_linearEmbedsList patterns equality

/-- List form of `Pattern.embedVars_eq_of_linearEmbeds`. -/
theorem Pattern.embedVarsList_eq_of_linearEmbedsList :
    ∀ (patterns : List Pattern) {names : List String},
      Pattern.linearEmbedsList patterns = some names →
      Pattern.embedVarsList patterns = names
  | [], _, equality => by
      simpa [Pattern.linearEmbedsList, Pattern.embedVarsList] using
        congrArg Option.get! equality
  | pattern :: patterns, names, equality => by
      cases headResult : pattern.linearEmbeds with
      | none =>
          simp [Pattern.linearEmbedsList, headResult] at equality
      | some headNames =>
          cases tailResult : Pattern.linearEmbedsList patterns with
          | none =>
              simp [Pattern.linearEmbedsList, headResult, tailResult] at equality
          | some tailNames =>
              have namesEquality : headNames ++ tailNames = names := by
                simpa [Pattern.linearEmbedsList, headResult, tailResult] using
                  equality
              rw [← namesEquality]
              simp only [Pattern.embedVarsList]
              rw [Pattern.embedVars_eq_of_linearEmbeds pattern headResult,
                Pattern.embedVarsList_eq_of_linearEmbedsList patterns tailResult]

end

mutual

/-- Successful linear traversal entails the no-embedding-under-or check. -/
theorem Pattern.noEmbedInOr_of_linearEmbeds :
    ∀ (pattern : Pattern) {names : List String},
      pattern.linearEmbeds = some names → pattern.noEmbedInOr = true
  | .pvar _, _, _ => rfl
  | .wild, _, _ => rfl
  | .pval _, _, _ => rfl
  | .embed _, _, _ => rfl
  | .pctor name patterns, names, equality =>
      Pattern.noEmbedInOrList_of_linearEmbedsList patterns equality
  | .pand left right, names, equality => by
      cases leftResult : left.linearEmbeds with
      | none => simp [Pattern.linearEmbeds, leftResult] at equality
      | some leftNames =>
          cases rightResult : right.linearEmbeds with
          | none =>
              simp [Pattern.linearEmbeds, leftResult, rightResult] at equality
          | some rightNames =>
              simp only [Pattern.noEmbedInOr, Bool.and_eq_true]
              exact ⟨Pattern.noEmbedInOr_of_linearEmbeds left leftResult,
                Pattern.noEmbedInOr_of_linearEmbeds right rightResult⟩
  | .por left right, names, equality => by
      simp [Pattern.linearEmbeds] at equality
  | .papp name patterns, names, equality =>
      Pattern.noEmbedInOrList_of_linearEmbedsList patterns equality
  | .ptuple patterns, names, equality =>
      Pattern.noEmbedInOrList_of_linearEmbedsList patterns equality

/-- List form of `Pattern.noEmbedInOr_of_linearEmbeds`. -/
theorem Pattern.noEmbedInOrList_of_linearEmbedsList :
    ∀ (patterns : List Pattern) {names : List String},
      Pattern.linearEmbedsList patterns = some names →
      Pattern.noEmbedInOrList patterns = true
  | [], _, _ => rfl
  | pattern :: patterns, names, equality => by
      cases headResult : pattern.linearEmbeds with
      | none =>
          simp [Pattern.linearEmbedsList, headResult] at equality
      | some headNames =>
          cases tailResult : Pattern.linearEmbedsList patterns with
          | none =>
              simp [Pattern.linearEmbedsList, headResult, tailResult] at equality
          | some tailNames =>
              simp only [Pattern.noEmbedInOrList, Bool.and_eq_true]
              exact ⟨Pattern.noEmbedInOr_of_linearEmbeds pattern headResult,
                Pattern.noEmbedInOrList_of_linearEmbedsList patterns tailResult⟩

end

/-- The stack check distributes over concatenation. -/
theorem stackNoEmbedInOr_append (left right : List Tree) :
    stackNoEmbedInOr (left ++ right) =
      (stackNoEmbedInOr left && stackNoEmbedInOr right) := by
  induction left with
  | nil => rfl
  | cons tree trees induction =>
      simp only [List.cons_append, stackNoEmbedInOr, induction]
      cases treeNoEmbedInOr tree <;>
        cases stackNoEmbedInOr trees <;> rfl

/-- Atom-only stacks have exactly the source pattern-list check. -/
theorem stackNoEmbedInOr_atoms (atoms : List Atom) :
    stackNoEmbedInOr (atoms.map Tree.atom) =
      Pattern.noEmbedInOrList (atoms.map Atom.p) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp only [List.map_cons, stackNoEmbedInOr, treeNoEmbedInOr,
        Pattern.noEmbedInOrList, induction]

/-! ## Runtime pattern-function shape -/

/-- The exact erased shape needed by pattern-function entry steps. -/
def RuntimePatternLinear (SF : RuntimeSigF) : Prop :=
  ∀ {name : String} {runtime : PatFunRuntimeSig},
    List.find? (fun entry => entry.1 == name) SF = some (name, runtime) →
    runtime.body.linearEmbeds = some runtime.params ∧ runtime.params.Nodup

/-- Bidirectional source/runtime agreement supplies the erased linear shape. -/
theorem RuntimeSigAgrees.runtimePatternLinear
    {signature : FrozenSig} {context : Context} {SF : RuntimeSigF}
    (agreement : RuntimeSigAgrees signature context SF) :
    RuntimePatternLinear SF := by
  intro name runtime found
  have member : (name, runtime) ∈ SF :=
    List.mem_of_find?_eq_some found
  rcases agreement.runtimeTyped (name, runtime) member with
    ⟨definition, scheme, entryEquality, definitionTyping⟩
  have nameEquality : name = definition.name :=
    congrArg Prod.fst entryEquality
  have runtimeEquality : runtime = definition.runtime :=
    congrArg Prod.snd entryEquality
  subst name
  subst runtime
  cases definitionTyping with
  | mk sourceLookup nonrecursive length parameterNamesNodup fresh
      capabilitiesNodup bodyTyping bodyLinear schemeEquality =>
      exact ⟨bodyLinear, parameterNamesNodup⟩

/-- Mapping the right projection of an arity-correct zip recovers the right list. -/
theorem map_snd_zip_eq_right :
    ∀ {left : List α} {right : List β},
      left.length = right.length →
      (left.zip right).map Prod.snd = right
  | [], [], _ => rfl
  | [], _ :: _, equality => by simp at equality
  | _ :: _, [], equality => by simp at equality
  | _ :: left, _ :: right, equality => by
      simp only [List.length_cons, Nat.succ.injEq] at equality
      simp only [List.zip_cons_cons, List.map_cons]
      rw [map_snd_zip_eq_right equality]

/-- Resolve a list of formal embedded occurrences through a runtime `PiEnv`. -/
def resolveEmbedOccs (piE : PiEnv) (names : List String) : List String :=
  names.flatMap fun name =>
    match List.find? (fun entry => entry.1 == name) piE with
    | some (_, pattern) => pattern.embedVars
    | none => [name]

/-- Pointwise equality on members is sufficient for `flatMap` equality. -/
theorem List.flatMap_congr_of_mem
    {items : List α} {left right : α → List β}
    (equal : ∀ item ∈ items, left item = right item) :
    items.flatMap left = items.flatMap right := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.flatMap_cons]
      rw [equal item (by simp), induction (fun entry member =>
        equal entry (by simp [member]))]

/--
Distinct, arity-correct formals resolve through their zipped actual arguments
to exactly the actual arguments' embedded occurrences.
-/
theorem resolveEmbedOccs_zip :
    ∀ {parameters : List String} {arguments : List Pattern},
      parameters.Nodup →
      parameters.length = arguments.length →
      resolveEmbedOccs (parameters.zip arguments) parameters =
        Pattern.embedVarsList arguments
  | [], [], _, _ => rfl
  | [], _ :: _, _, length => by simp at length
  | _ :: _, [], _, length => by simp at length
  | parameter :: parameters, argument :: arguments, nodup, length => by
      simp only [List.nodup_cons] at nodup
      simp only [List.length_cons, Nat.succ.injEq] at length
      simp only [resolveEmbedOccs, List.flatMap_cons, List.zip_cons_cons,
        List.find?_cons, beq_self_eq_true, Pattern.embedVarsList]
      congr 1
      calc
        _ = parameters.flatMap (fun name =>
              match List.find? (fun entry => entry.1 == name)
                (parameters.zip arguments) with
              | some (_, pattern) => pattern.embedVars
              | none => [name]) := by
            apply List.flatMap_congr_of_mem
            intro name membership
            have unequal : parameter ≠ name := fun equality =>
              nodup.1 (equality ▸ membership)
            rw [beq_false_of_ne unequal]
        _ = Pattern.embedVarsList arguments :=
          resolveEmbedOccs_zip nodup.2 length

/-- Embedded occurrences distribute over pattern-list concatenation. -/
theorem Pattern.embedVarsList_append (left right : List Pattern) :
    Pattern.embedVarsList (left ++ right) =
      Pattern.embedVarsList left ++ Pattern.embedVarsList right := by
  induction left with
  | nil => rfl
  | cons pattern patterns induction =>
      simp only [List.cons_append, Pattern.embedVarsList, induction,
        List.append_assoc]

/-- Zipping matcher/value payloads does not change the pattern projection. -/
theorem atomPatterns_zip3 :
    ∀ {patterns : List Pattern} {matchers values : List Value},
      patterns.length = matchers.length →
      matchers.length = values.length →
      (((patterns.zip (matchers.zip values)).map fun entry =>
        ⟨entry.1, entry.2.1, entry.2.2⟩ : List Atom).map Atom.p) =
        patterns := by
  intro patterns matchers values patternLength valueLength
  induction patterns generalizing matchers values with
  | nil =>
      cases matchers <;> simp at patternLength
      cases values <;> simp at valueLength ⊢
  | cons pattern patterns induction =>
      cases matchers with
      | nil => simp at patternLength
      | cons matcher matchers =>
          cases values with
          | nil => simp at valueLength
          | cons value values =>
              simp only [List.length_cons, Nat.succ.injEq] at patternLength
              simp only [List.length_cons, Nat.succ.injEq] at valueLength
              simp only [List.zip_cons_cons, List.map_cons]
              rw [induction patternLength valueLength]

/-- Atom-tree embedding exposes exactly the atoms' pattern occurrences. -/
theorem stackEmbedOccs_atoms (atoms : List Atom) :
    stackEmbedOccs (atoms.map Tree.atom) =
      Pattern.embedVarsList (atoms.map Atom.p) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp only [List.map_cons, stackEmbedOccs, treeEmbedOccs,
        Pattern.embedVarsList, induction]

/-- Ordered embed occurrences distribute over stack concatenation. -/
theorem stackEmbedOccs_append (left right : List Tree) :
    stackEmbedOccs (left ++ right) =
      stackEmbedOccs left ++ stackEmbedOccs right := by
  induction left with
  | nil => rfl
  | cons tree trees induction =>
      simp only [List.cons_append, stackEmbedOccs, induction,
        List.append_assoc]

mutual

/-- Successful PPM preserves the left-to-right embedded-parameter sequence. -/
theorem ppm_embedVars :
    ∀ (pp : PPat) {SF : RuntimeSigF} {environment : Env}
      {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env},
      PPM SF environment pp pattern (some (captures, ppEnvironment)) →
      Pattern.embedVarsList captures = pattern.embedVars
  | .hole, _, _, _, _, _, matching => by
      cases matching
      simp [Pattern.embedVarsList]
  | .wild, _, _, _, _, _, matching => by cases matching; rfl
  | .pval name, _, _, _, _, _, matching => by cases matching; rfl
  | .ctor name pps, _, _, _, _, _, matching => by
      cases matching with
      | ctor lengthPP lengthResults all =>
          exact ppm_embedVars_list pps lengthPP lengthResults all
  | .tuple pps, _, _, _, _, _, matching => by
      cases matching with
      | tuple lengthPP lengthResults all =>
          exact ppm_embedVars_list pps lengthPP lengthResults all

/-- List form of `ppm_embedVars`. -/
theorem ppm_embedVars_list :
    ∀ (pps : List PPat) {SF : RuntimeSigF} {environment : Env}
      {patterns : List Pattern} {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
      Pattern.embedVarsList ((results.map Prod.fst).flatten) =
        Pattern.embedVarsList patterns
  | [], _, _, patterns, results, lengthPP, lengthResults, all => by
      cases patterns with
      | cons pattern patterns => simp at lengthPP
      | nil =>
          cases results with
          | cons result results => simp at lengthResults
          | nil => rfl
  | pp :: pps, SF, environment, patterns, results, lengthPP, lengthResults,
      all => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnvironment⟩ := result
              have headMatching :
                  PPM SF environment pp pattern
                    (some (captures, ppEnvironment)) :=
                all ((pp, pattern), (captures, ppEnvironment))
                  (by simp [List.zip_cons_cons])
              have tailMatching :
                  ∀ entry ∈ (pps.zip patterns).zip results,
                    PPM SF environment entry.1.1 entry.1.2 (some entry.2) := by
                intro entry member
                exact all entry
                  (by simp [List.zip_cons_cons]; exact .inr member)
              simp only [List.map_cons, List.flatten_cons,
                Pattern.embedVarsList]
              rw [Pattern.embedVarsList_append, ppm_embedVars pp headMatching,
                ppm_embedVars_list pps (by simpa using lengthPP)
                  (by simpa [List.zip_cons_cons] using lengthResults)
                  tailMatching]

end

mutual

/-- Successful PPM returns exactly one captured pattern per syntactic hole. -/
theorem ppm_captures_length :
    ∀ (pp : PPat) {SF : RuntimeSigF} {environment : Env}
      {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env},
      PPM SF environment pp pattern (some (captures, ppEnvironment)) →
      captures.length = pp.holeCount
  | .hole, _, _, _, _, _, matching => by cases matching; rfl
  | .wild, _, _, _, _, _, matching => by cases matching; rfl
  | .pval name, _, _, _, _, _, matching => by cases matching; rfl
  | .ctor name pps, _, _, _, _, _, matching => by
      cases matching with
      | ctor lengthPP lengthResults all =>
          exact ppm_captures_length_list pps lengthPP lengthResults all
  | .tuple pps, _, _, _, _, _, matching => by
      cases matching with
      | tuple lengthPP lengthResults all =>
          exact ppm_captures_length_list pps lengthPP lengthResults all

/-- List form of `ppm_captures_length`. -/
theorem ppm_captures_length_list :
    ∀ (pps : List PPat) {SF : RuntimeSigF} {environment : Env}
      {patterns : List Pattern} {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
      ((results.map Prod.fst).flatten).length = PPat.holeCountList pps
  | [], _, _, patterns, results, lengthPP, lengthResults, all => by
      cases patterns with
      | cons pattern patterns => simp at lengthPP
      | nil =>
          cases results with
          | cons result results => simp at lengthResults
          | nil => rfl
  | pp :: pps, SF, environment, patterns, results, lengthPP, lengthResults,
      all => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnvironment⟩ := result
              have headMatching :
                  PPM SF environment pp pattern
                    (some (captures, ppEnvironment)) :=
                all ((pp, pattern), (captures, ppEnvironment))
                  (by simp [List.zip_cons_cons])
              have tailMatching :
                  ∀ entry ∈ (pps.zip patterns).zip results,
                    PPM SF environment entry.1.1 entry.1.2 (some entry.2) := by
                intro entry member
                exact all entry
                  (by simp [List.zip_cons_cons]; exact .inr member)
              simp only [List.map_cons, List.flatten_cons,
                List.length_append, PPat.holeCountList]
              rw [ppm_captures_length pp headMatching,
                ppm_captures_length_list pps (by simpa using lengthPP)
                  (by simpa [List.zip_cons_cons] using lengthResults)
                  tailMatching]

end

/-- Resolution changes dual contents but not the number of PP holes. -/
theorem ResolvedPPatTy.holes_length
    {signature : FrozenSig} {prevailing : Subst} {pattern : PPat}
    {target : Ty} {holes : List Dual} {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing pattern target holes
      bindings) :
    holes.length = pattern.holeCount := by
  exact typing.terminal.holes_length

/-- A resolved PP hole contributes one dual at the resolved clause target. -/
theorem ResolvedPPatTy.hole_inversion
    {signature : FrozenSig} {prevailing : Subst} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing .hole target holes
      bindings) :
    ∃ capability, holes = [⟨capability, target⟩] ∧ bindings = [] := by
  cases typing.terminal with
  | @hole rawTarget varId fresh =>
      exact ⟨(Cap.var varId).apply prevailing.cap,
        by simp [Dual.applySubst, Dual.apply], rfl⟩

/-- A resolved PP wildcard has no holes or bindings. -/
theorem ResolvedPPatTy.wild_inversion
    {signature : FrozenSig} {prevailing : Subst} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing .wild target holes
      bindings) : holes = [] ∧ bindings = [] := by
  cases typing.terminal
  exact ⟨rfl, rfl⟩

/-- A resolved PP value pattern has no holes. -/
theorem ResolvedPPatTy.pval_holes
    {signature : FrozenSig} {prevailing : Subst} {name : String}
    {target : Ty} {holes : List Dual} {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing (.pval name) target holes
      bindings) : holes = [] := by
  cases typing.terminal
  rfl

mutual

/-- PPM captures cannot introduce an embedded parameter below `or`. -/
theorem ppm_noEmbedInOr :
    ∀ (pp : PPat) {SF : RuntimeSigF} {environment : Env}
      {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env},
      PPM SF environment pp pattern (some (captures, ppEnvironment)) →
      pattern.noEmbedInOr = true →
      ∀ capture ∈ captures, capture.noEmbedInOr = true
  | .hole, _, _, _, _, _, matching, noOr, capture, member => by
      cases matching
      simp only [List.mem_singleton] at member
      subst capture
      exact noOr
  | .wild, _, _, _, _, _, matching, noOr, capture, member => by
      cases matching
      contradiction
  | .pval name, _, _, _, _, _, matching, noOr, capture, member => by
      cases matching
      contradiction
  | .ctor name pps, _, _, _, _, _, matching, noOr, capture, member => by
      cases matching with
      | ctor lengthPP lengthResults all =>
          exact ppm_noEmbedInOr_list pps lengthPP lengthResults all noOr
            capture member
  | .tuple pps, _, _, _, _, _, matching, noOr, capture, member => by
      cases matching with
      | tuple lengthPP lengthResults all =>
          exact ppm_noEmbedInOr_list pps lengthPP lengthResults all noOr
            capture member

/-- List form of `ppm_noEmbedInOr`. -/
theorem ppm_noEmbedInOr_list :
    ∀ (pps : List PPat) {SF : RuntimeSigF} {environment : Env}
      {patterns : List Pattern} {results : List (List Pattern × Env)},
      pps.length = patterns.length →
      (pps.zip patterns).length = results.length →
      (∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
      Pattern.noEmbedInOrList patterns = true →
      ∀ capture ∈ (results.map Prod.fst).flatten,
        capture.noEmbedInOr = true
  | [], _, _, patterns, results, lengthPP, lengthResults, all, noOr,
      capture, member => by
      cases patterns with
      | cons pattern patterns => simp at lengthPP
      | nil =>
          cases results with
          | cons result results => simp at lengthResults
          | nil => contradiction
  | pp :: pps, SF, environment, patterns, results, lengthPP, lengthResults,
      all, noOr, capture, member => by
      cases patterns with
      | nil => simp at lengthPP
      | cons pattern patterns =>
          cases results with
          | nil => simp [List.zip_cons_cons] at lengthResults
          | cons result results =>
              obtain ⟨captures, ppEnvironment⟩ := result
              simp only [Pattern.noEmbedInOrList, Bool.and_eq_true] at noOr
              obtain ⟨headNoOr, tailNoOr⟩ := noOr
              simp only [List.map_cons, List.flatten_cons,
                List.mem_append] at member
              rcases member with headMember | tailMember
              · exact ppm_noEmbedInOr pp
                  (all ((pp, pattern), (captures, ppEnvironment))
                    (by simp [List.zip_cons_cons]))
                  headNoOr capture headMember
              · exact ppm_noEmbedInOr_list pps
                  (by simpa using lengthPP)
                  (by simpa [List.zip_cons_cons] using lengthResults)
                  (fun entry entryMember => all entry
                    (by simp [List.zip_cons_cons]; exact .inr entryMember))
                  tailNoOr capture tailMember

end

/-! ## Matching-atom occurrence preservation -/

/--
Every continuation produced by one atom reduction carries the same ordered
embedded-parameter occurrences.  `or` requires the explicit source
restriction that neither branch may contain an embedded parameter.
-/
theorem MAtom.embedVars
    {SF : RuntimeSigF} {environment : Env} {pattern : Pattern}
    {matcher value : Value} {continuations : List (List Atom)}
    {substitution : MatchSubst}
    (reduction : MAtom SF environment pattern matcher value
      continuations substitution) :
    pattern.noEmbedInOr = true →
    ∀ atoms ∈ continuations,
      Pattern.embedVarsList (atoms.map Atom.p) = pattern.embedVars := by
  refine MAtom.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ pattern _ _ continuations _ _ =>
      pattern.noEmbedInOr = true →
      ∀ atoms ∈ continuations,
        Pattern.embedVarsList (atoms.map Atom.p) = pattern.embedVars)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    reduction
  case msomeWC =>
    intro environment value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simp [Pattern.embedVarsList, Pattern.embedVars]
  case msomeVar =>
    intro environment name value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rfl
  case msomeValEq =>
    intro environment expression value expected evaluation equality evalIH noOr
      atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rfl
  case msomeValNeq =>
    intro environment expression value expected evaluation equality evalIH noOr
      atoms member
    contradiction
  case mand =>
    intro environment left right matcher value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simp [Pattern.embedVarsList, Pattern.embedVars]
  case mor =>
    intro environment left right matcher value noOr atoms member
    simp only [Pattern.noEmbedInOr, Bool.and_eq_true] at noOr
    rcases noOr with ⟨⟨⟨leftEmpty, rightEmpty⟩, _⟩, _⟩
    have leftNone : left.embedVars = [] := by simpa using leftEmpty
    have rightNone : right.embedVars = [] := by simpa using rightEmpty
    have branch :
        atoms = [⟨left, matcher, value⟩] ∨
        atoms = [⟨right, matcher, value⟩] := by
      simpa using member
    rcases branch with rfl | rfl <;>
      simp [Pattern.embedVarsList, Pattern.embedVars, leftNone, rightNone]
  case mtuple =>
    intro environment patterns matchers values patternLength valueLength noOr
      atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rw [atomPatterns_zip3 patternLength valueLength]
    simp [Pattern.embedVars]
  case mprodSome =>
    intro environment pattern matchers value primitive noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simp [Pattern.embedVarsList]
  case mppfail =>
    intro environment matcherEnvironment original pattern value pp next arms
      clauses continuations substitution dispatch ppFailure recursive ppIH
      recursiveIH noOr atoms member
    exact recursiveIH noOr atoms member
  case mdpfail =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment continuations substitution dispatch
      ppSuccess dpFailure recursive ppIH recursiveIH noOr atoms member
    exact recursiveIH noOr atoms member
  case mmatcher =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment dataEnvironment decomposition tuples
      valueLists matcherValue matchers dispatch ppSuccess dataSuccess bodyEval
      listDecode valuesDecode nextEval matchersDecode ppIH bodyIH nextIH noOr
      atoms member
    rcases List.mem_map.mp member with ⟨components, componentsMember, rfl⟩
    have matcherLength : matchers.length = holes.length :=
      decodeTuple_length matchersDecode
    have componentLength : components.length = holes.length :=
      decodeTuple_mapM_member valuesDecode components componentsMember
    rw [atomPatterns_zip3 matcherLength.symm
      (matcherLength.trans componentLength.symm)]
    exact ppm_embedVars pp ppSuccess
  all_goals intros; trivial

/--
Atom reduction also preserves the prohibition on embedded parameters below
`or`.  In the matcher-dispatch case this follows from the corresponding PPM
capture property, rather than from a semantic assumption on the generated
continuation.
-/
theorem MAtom.noEmbedInOr
    {SF : RuntimeSigF} {environment : Env} {pattern : Pattern}
    {matcher value : Value} {continuations : List (List Atom)}
    {substitution : MatchSubst}
    (reduction : MAtom SF environment pattern matcher value
      continuations substitution) :
    pattern.noEmbedInOr = true →
    ∀ atoms ∈ continuations,
      Pattern.noEmbedInOrList (atoms.map Atom.p) = true := by
  refine MAtom.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ pattern _ _ continuations _ _ =>
      pattern.noEmbedInOr = true →
      ∀ atoms ∈ continuations,
        Pattern.noEmbedInOrList (atoms.map Atom.p) = true)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    reduction
  case msomeWC =>
    intro environment value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rfl
  case msomeVar =>
    intro environment name value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rfl
  case msomeValEq =>
    intro environment expression value expected evaluation equality evalIH noOr
      atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rfl
  case msomeValNeq =>
    intro environment expression value expected evaluation equality evalIH noOr
      atoms member
    contradiction
  case mand =>
    intro environment left right matcher value noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simpa [Pattern.noEmbedInOr, Pattern.noEmbedInOrList] using noOr
  case mor =>
    intro environment left right matcher value noOr atoms member
    have branch :
        atoms = [⟨left, matcher, value⟩] ∨
        atoms = [⟨right, matcher, value⟩] := by
      simpa using member
    simp only [Pattern.noEmbedInOr, Bool.and_eq_true] at noOr
    rcases branch with rfl | rfl
    · simpa [Pattern.noEmbedInOrList] using noOr.1.2
    · simpa [Pattern.noEmbedInOrList] using noOr.2
  case mtuple =>
    intro environment patterns matchers values patternLength valueLength noOr
      atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    rw [atomPatterns_zip3 patternLength valueLength]
    exact noOr
  case mprodSome =>
    intro environment pattern matchers value primitive noOr atoms member
    simp only [List.mem_singleton] at member
    subst atoms
    simpa [Pattern.noEmbedInOrList] using noOr
  case mppfail =>
    intro environment matcherEnvironment original pattern value pp next arms
      clauses continuations substitution dispatch ppFailure recursive ppIH
      recursiveIH noOr atoms member
    exact recursiveIH noOr atoms member
  case mdpfail =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment continuations substitution dispatch
      ppSuccess dpFailure recursive ppIH recursiveIH noOr atoms member
    exact recursiveIH noOr atoms member
  case mmatcher =>
    intro environment matcherEnvironment original pattern value pp next dp body
      arms clauses holes ppEnvironment dataEnvironment decomposition tuples
      valueLists matcherValue matchers dispatch ppSuccess dataSuccess bodyEval
      listDecode valuesDecode nextEval matchersDecode ppIH bodyIH nextIH noOr
      atoms member
    rcases List.mem_map.mp member with ⟨components, componentsMember, rfl⟩
    have matcherLength : matchers.length = holes.length :=
      decodeTuple_length matchersDecode
    have componentLength : components.length = holes.length :=
      decodeTuple_mapM_member valuesDecode components componentsMember
    rw [atomPatterns_zip3 matcherLength.symm
      (matcherLength.trans componentLength.symm)]
    exact Pattern.noEmbedInOrList_eq_true_of_mem
      (ppm_noEmbedInOr pp ppSuccess noOr)
  all_goals intros; trivial

/-! ## Syntactic step preservation -/

/-- One state step preserves the tree-level no-embedding discipline. -/
theorem Step.noEmbedInOr
    {SF : RuntimeSigF} (linear : RuntimePatternLinear SF)
    {state : MState} {states : List MState}
    (reduction : Step SF state states) :
    stackNoEmbedInOr state.S = true →
    ∀ next ∈ states, stackNoEmbedInOr next.S = true := by
  refine Step.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun state states _ =>
      stackNoEmbedInOr state.S = true →
      ∀ next ∈ states, stackNoEmbedInOr next.S = true)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?_ ?_
    reduction
  case sreduce =>
    intro stack environment substitution pattern matcher value continuations
      new atomReduction atomIH checked next member
    rcases List.mem_map.mp member with ⟨atoms, atomsMember, rfl⟩
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Bool.and_eq_true] at checked
    rw [stackNoEmbedInOr_append, stackNoEmbedInOr_atoms]
    simp only [Bool.and_eq_true]
    exact ⟨MAtom.noEmbedInOr atomReduction checked.1 atoms atomsMember,
      checked.2⟩
  case spatfunEnter =>
    intro stack environment substitution name arguments matcher value runtime
      found length checked next member
    simp only [List.mem_singleton] at member
    subst next
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Pattern.noEmbedInOr, Bool.and_eq_true] at checked ⊢
    obtain ⟨bodyLinear, parametersNodup⟩ := linear found
    have bodyNoOr :=
      Pattern.noEmbedInOr_of_linearEmbeds runtime.body bodyLinear
    have actualProjection :
        (runtime.params.zip arguments).map Prod.snd = arguments :=
      map_snd_zip_eq_right length
    exact ⟨⟨⟨bodyNoOr, trivial⟩,
      by simpa [actualProjection] using checked.1⟩, checked.2⟩
  case smnodeStep =>
    intro stack environment substitution tree innerStack innerEnvironment
      innerSubstitution piE states bypass nested nestedIH checked next member
    rcases List.mem_map.mp member with ⟨inner, innerMember, rfl⟩
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Bool.and_eq_true] at checked ⊢
    have innerChecked :
        stackNoEmbedInOr (tree :: innerStack) = true := by
      simp only [stackNoEmbedInOr, Bool.and_eq_true]
      exact checked.1.1
    exact ⟨⟨nestedIH innerChecked inner innerMember, checked.1.2⟩,
      checked.2⟩
  case smnodeVarpat =>
    intro stack environment substitution name pattern matcher value innerStack
      innerEnvironment innerSubstitution piE found checked next member
    simp only [List.mem_singleton] at member
    subst next
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Pattern.noEmbedInOr, Bool.and_eq_true] at checked ⊢
    have pairMember : (name, pattern) ∈ piE :=
      List.mem_of_find?_eq_some found
    have patternMember : pattern ∈ piE.map Prod.snd :=
      List.mem_map.mpr ⟨(name, pattern), pairMember, rfl⟩
    have patternNoOr :=
      Pattern.noEmbedInOr_of_mem checked.1.2 patternMember
    exact ⟨patternNoOr, ⟨⟨checked.1.1.2, checked.1.2⟩, checked.2⟩⟩
  case smnodeDone =>
    intro stack environment substitution innerEnvironment innerSubstitution
      piE checked next member
    simp only [List.mem_singleton] at member
    subst next
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Bool.and_eq_true] at checked
    exact checked.2
  all_goals intros; trivial

/-- One state step preserves the ordered unresolved embed occurrence stream. -/
theorem Step.embedOccs
    {SF : RuntimeSigF} (linear : RuntimePatternLinear SF)
    {state : MState} {states : List MState}
    (reduction : Step SF state states) :
    stackNoEmbedInOr state.S = true →
    ∀ next ∈ states,
      stackEmbedOccs next.S = stackEmbedOccs state.S := by
  refine Step.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun state states _ =>
      stackNoEmbedInOr state.S = true →
      ∀ next ∈ states,
        stackEmbedOccs next.S = stackEmbedOccs state.S)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?_ ?_
    reduction
  case sreduce =>
    intro stack environment substitution pattern matcher value continuations
      new atomReduction atomIH checked next member
    rcases List.mem_map.mp member with ⟨atoms, atomsMember, rfl⟩
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Bool.and_eq_true] at checked
    rw [stackEmbedOccs_append, stackEmbedOccs_atoms]
    simp only [stackEmbedOccs, treeEmbedOccs]
    rw [MAtom.embedVars atomReduction checked.1 atoms atomsMember]
  case spatfunEnter =>
    intro stack environment substitution name arguments matcher value runtime
      found length checked next member
    simp only [List.mem_singleton] at member
    subst next
    obtain ⟨bodyLinear, parametersNodup⟩ := linear found
    have bodyOccurrences : runtime.body.embedVars = runtime.params :=
      Pattern.embedVars_eq_of_linearEmbeds runtime.body bodyLinear
    simp only [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars]
    simp only [List.append_nil]
    change resolveEmbedOccs (runtime.params.zip arguments)
        runtime.body.embedVars ++ stackEmbedOccs stack =
      Pattern.embedVarsList arguments ++ stackEmbedOccs stack
    rw [bodyOccurrences,
      resolveEmbedOccs_zip parametersNodup length]
  case smnodeStep =>
    intro stack environment substitution tree innerStack innerEnvironment
      innerSubstitution piE states bypass nested nestedIH checked next member
    rcases List.mem_map.mp member with ⟨inner, innerMember, rfl⟩
    simp only [stackNoEmbedInOr, treeNoEmbedInOr,
      Bool.and_eq_true] at checked
    have innerChecked :
        stackNoEmbedInOr (tree :: innerStack) = true := by
      simp only [stackNoEmbedInOr, Bool.and_eq_true]
      exact checked.1.1
    simp only [stackEmbedOccs, treeEmbedOccs]
    rw [nestedIH innerChecked inner innerMember]
    rfl
  case smnodeVarpat =>
    intro stack environment substitution name pattern matcher value innerStack
      innerEnvironment innerSubstitution piE found checked next member
    simp only [List.mem_singleton] at member
    subst next
    simp only [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars]
    rw [List.flatMap_append]
    simp [found]
  case smnodeDone =>
    intro stack environment substitution innerEnvironment innerSubstitution
      piE checked next member
    simp only [List.mem_singleton] at member
    subst next
    rfl
  all_goals intros; trivial

/-! ## Resolved-pattern inversion used by state preservation -/

@[simp] theorem MonoCtx.names_applySubst_local
    (substitution : Subst) (bindings : MonoCtx) :
    (bindings.applySubst substitution).names = bindings.names := by
  simp [MonoCtx.applySubst, MonoCtx.names, List.map_map,
    Function.comp_def]

/-- A resolved variable pattern appends exactly its actual target binding. -/
theorem ResolvedPatternTy.pvar_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {name : String} {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      (.pvar name) capability target output) :
    name ∉ input.names ∧ output = input ++ [(name, target)] := by
  cases typing.terminal with
  | pvar missing freshCap freshTy =>
      constructor
      · simpa only [MonoCtx.names_applySubst_local] using missing
      · simp [MonoCtx.applySubst]

/-- A resolved wildcard leaves the binding context unchanged. -/
theorem ResolvedPatternTy.wild_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      .wild capability target output) : output = input := by
  cases typing.terminal
  rfl

/-- A resolved value pattern preserves bindings and retains the actual
expression typing used by `MS-SOME-VAL`. -/
theorem ResolvedPatternTy.pval_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {expression : Expr} {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      (.pval expression) capability target output) :
    output = input ∧
      HasTy signature (input.toContext ++ context) expression target := by
  cases typing.terminal with
  | pval fresh separate actualTyping =>
      exact ⟨rfl, actualTyping⟩

/-- Conjunction resolution exposes its two source-threaded actual children. -/
theorem ResolvedPatternTy.and_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {left right : Pattern} {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      (.pand left right) capability target output) :
    ∃ middle,
      ResolvedPatternTy signature prevailing context parameters input left
        capability target middle ∧
      ResolvedPatternTy signature prevailing context parameters middle right
        capability target output := by
  cases typing.terminal with
  | and leftResolution rightResolution =>
      exact ⟨_, .ofTerminal leftResolution, .ofTerminal rightResolution⟩

/-- Disjunction resolution exposes both alternatives at the same indices. -/
theorem ResolvedPatternTy.or_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {left right : Pattern} {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      (.por left right) capability target output) :
    ResolvedPatternTy signature prevailing context parameters input left
        capability target output ∧
      ResolvedPatternTy signature prevailing context parameters input right
        capability target output := by
  cases typing.terminal with
  | or leftResolution rightResolution =>
      exact ⟨.ofTerminal leftResolution, .ofTerminal rightResolution⟩

/-- An actual embedded parameter exposes the exact dual stored in the fixed
parameter context and does not add a source binding. -/
theorem ResolvedPatternTy.embed_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {name : String} {capability : Cap} {target : Ty}
    (typing : ResolvedPatternTy signature prevailing context parameters input
      (.embed name) capability target output) :
    parameters.find? name = some ⟨capability, target⟩ ∧ output = input := by
  cases typing.terminal with
  | embed sourceFound actualFound =>
      exact ⟨actualFound, rfl⟩

/-- Inversion of the leading actual argument retained by a pattern-function
node. -/
theorem PiEnvTyped.cons_inversion
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {name : String} {pattern : Pattern}
    {rest : PiEnv} {dual : Dual} {duals : List Dual}
    (typing : PiEnvTyped signature context parameters input
      ((name, pattern) :: rest) (dual :: duals) output) :
    ∃ middle prevailing,
      ResolvedPatternTy signature prevailing context parameters input pattern
        dual.cap dual.target middle ∧
      PiEnvTyped signature context parameters middle rest duals output := by
  cases typing with
  | cons head tail => exact ⟨_, _, head, tail⟩

/-- A lookup in a name-unique pattern environment returns its unique member. -/
theorem PiEnv.find?_eq_some_of_mem
    {α : Type} {parameters : List (String × α)}
    {name : String} {payload : α}
    (namesNodup : (parameters.map Prod.fst).Nodup)
    (member : (name, payload) ∈ parameters) :
    List.find? (fun entry => entry.1 == name) parameters =
      some (name, payload) := by
  induction parameters with
  | nil => contradiction
  | cons head tail induction =>
      obtain ⟨headName, headPayload⟩ := head
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · cases equality
        simp [List.find?]
      · have unequal : headName ≠ name := by
          intro equality
          apply headFresh
          rw [equality]
          exact List.mem_map_of_mem member
        simp only [List.find?]
        rw [show (headName == name) = false by simp [unequal]]
        exact induction tailNodup member

/-- Pair actual terminal resolutions with any same-length formal-name list. -/
theorem TerminalPatternResolutions.piEnvTyped
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {patterns : List Pattern} {duals : List Dual}
    (typing : TerminalPatternResolutions signature prevailing context
      parameters input patterns duals output)
    {names : List String} (length : names.length = patterns.length) :
    PiEnvTyped signature context parameters input (names.zip patterns) duals
      output := by
  induction patterns generalizing input output names duals with
  | nil =>
      cases typing
      cases names with
      | nil => exact .nil
      | cons name names => simp at length
  | cons pattern patterns induction =>
      cases typing with
      | cons head tail =>
          cases names with
          | nil => simp at length
          | cons name names =>
              simp only [List.length_cons, Nat.succ.injEq] at length
              exact .cons (.ofTerminal head) (induction tail length)

/-- A pointwise fixed-context lookup types an aligned remaining parameter
stream. -/
theorem RemInParameters.of_aligned_lookups
    {fixed : PatternCtx} :
    ∀ {names : List String} {patterns : List Pattern} {duals : List Dual},
      names.length = patterns.length →
      names.length = duals.length →
      (∀ entry ∈ names.zip duals,
        fixed.find? entry.1 = some entry.2) →
      RemInParameters fixed (names.zip patterns) duals
  | [], [], [], _, _, _ => trivial
  | [], [], _ :: _, _, length, _ => by simp at length
  | [], _ :: _, _, length, _, _ => by simp at length
  | _ :: _, [], _, length, _, _ => by simp at length
  | _ :: _, _, [], _, length, _ => by simp at length
  | name :: names, pattern :: patterns, dual :: duals,
      patternLength, dualLength, lookups => by
      simp only [List.length_cons, Nat.succ.injEq] at patternLength dualLength
      exact ⟨lookups (name, dual) (by simp),
        RemInParameters.of_aligned_lookups patternLength dualLength
          (fun entry member => lookups entry (by simp [member]))⟩

/-- Zipping one name-unique formal list with actual patterns and actual duals
produces the fixed-parameter relation used by an isolated node. -/
theorem RemInParameters.aligned_zip
    {names : List String} {patterns : List Pattern} {duals : List Dual}
    (namesNodup : names.Nodup)
    (patternLength : names.length = patterns.length)
    (dualLength : names.length = duals.length) :
    RemInParameters (names.zip duals) (names.zip patterns) duals := by
  apply RemInParameters.of_aligned_lookups patternLength dualLength
  intro entry member
  have found := PiEnv.find?_eq_some_of_mem
    (by simpa [List.map_fst_zip (Nat.le_of_eq dualLength)] using namesNodup)
    member
  unfold PatternCtx.find?
  rw [found]
  rfl

/-! ## Typed outputs of one atom reduction -/

/-- The type-level payload needed by `Step.reduce`: the returned runtime
prefix types a new source input, and every continuation consumes that input
to the original atom output. -/
def MAtomTypedOutput
    (signature : FrozenSig) (context : Context) (parameters : PatternCtx)
    (input output : MonoCtx) (continuations : List (List Atom))
    (newSubstitution : MatchSubst) : Prop :=
  ∀ {substitution : MatchSubst},
    MatchSubstTyped signature input substitution →
    ∃ nextInput,
      MatchSubstTyped signature nextInput
        (newSubstitution ++ substitution) ∧
      ∀ atoms ∈ continuations,
        StackTy signature context parameters nextInput
          (atoms.map Tree.atom) output

/-- `something` is usable at every target through its fixed `none`
capability. -/
theorem MatcherAtTarget.something
    {signature : FrozenSig} {target : Ty} :
    MatcherAtTarget signature .something target :=
  ⟨.none, .inl ValueTy.something⟩

/-- A resolved tuple atom decomposes into the exactly typed component stack. -/
theorem ResolvedPatternTy.tuple_atomStack
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patterns : List Pattern}
    {capability : Cap} {target : Ty} {matchers values : List Value}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.ptuple patterns) capability target output)
    (matcherTyping : MatcherUsable signature (.tuple matchers)
      capability target)
    (valueTyping : ValueTy signature (.tuple values) target) :
    StackTy signature context parameters input
      ((patterns.zip (matchers.zip values)).map fun entry =>
        Tree.atom ⟨entry.1, entry.2.1, entry.2.2⟩) output := by
  cases resolution.terminal with
  | tuple children =>
      have matchersTyped := ValueTy.tupleMatcherUsables matcherTyping
      obtain ⟨actualValues, valueEquality, valuesTyped⟩ :=
        ValueTy.product_inversion signatureWF valueTyping
      cases valueEquality
      exact children.atomStack matchersTyped valuesTyped

/-- `MS-SOME-WC` preserves the source input and has one empty continuation. -/
theorem matom_someWC_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {value : Value}
    {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input .wild capability target output)
    (_valueTyping : ValueTy signature value target) :
    MAtomTypedOutput signature context parameters input output [[]] [] := by
  have outputEquality := resolution.wild_inversion
  subst output
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp at member
  subst atoms
  exact .nil

/-- `MS-SOME-VAR` extends the reversed runtime substitution by one exactly
typed source binding. -/
theorem matom_someVar_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {name : String}
    {value : Value} {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.pvar name) capability target output)
    (valueTyping : ValueTy signature value target) :
    MAtomTypedOutput signature context parameters input output [[]]
      [(name, value)] := by
  obtain ⟨fresh, outputEquality⟩ := resolution.pvar_inversion
  subst output
  intro substitution substitutionTyping
  refine ⟨input ++ [(name, target)],
    by simpa using substitutionTyping.snoc_cons fresh valueTyping, ?_⟩
  intro atoms member
  simp at member
  subst atoms
  exact .nil

/-- A successful `something` value comparison consumes no bindings. -/
theorem matom_someValEq_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {expression : Expr}
    {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.pval expression) capability target output) :
    MAtomTypedOutput signature context parameters input output [[]] [] := by
  have outputEquality := resolution.pval_inversion |>.1
  subst output
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp at member
  subst atoms
  exact .nil

/-- A failed value comparison has no continuation, hence is type safe
vacuously. -/
theorem matom_someValNeq_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {expression : Expr}
    {capability : Cap} {target : Ty}
    (_resolution : ResolvedPatternTy signature prevailing context parameters
      input (.pval expression) capability target output) :
    MAtomTypedOutput signature context parameters input output [] [] := by
  intro substitution substitutionTyping
  exact ⟨input, by simpa using substitutionTyping, fun atoms member => by
    contradiction⟩

/-- `MS-AND` exposes the two threaded child atoms. -/
theorem matom_and_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {left right : Pattern}
    {matcher value : Value} {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.pand left right) capability target output)
    (matcherTyping : MatcherUsable signature matcher capability target)
    (valueTyping : ValueTy signature value target) :
    MAtomTypedOutput signature context parameters input output
      [[⟨left, matcher, value⟩, ⟨right, matcher, value⟩]] [] := by
  obtain ⟨middle, leftTyping, rightTyping⟩ := resolution.and_inversion
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_singleton] at member
  subst atoms
  exact .cons (.atom (.mk leftTyping matcherTyping valueTyping))
    (.cons (.atom (.mk rightTyping matcherTyping valueTyping)) .nil)

/-- `MS-OR` gives two independently typed alternatives. -/
theorem matom_or_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {left right : Pattern}
    {matcher value : Value} {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.por left right) capability target output)
    (matcherTyping : MatcherUsable signature matcher capability target)
    (valueTyping : ValueTy signature value target) :
    MAtomTypedOutput signature context parameters input output
      [[⟨left, matcher, value⟩], [⟨right, matcher, value⟩]] [] := by
  obtain ⟨leftTyping, rightTyping⟩ := resolution.or_inversion
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .cons (.atom (.mk leftTyping matcherTyping valueTyping)) .nil
  · exact .cons (.atom (.mk rightTyping matcherTyping valueTyping)) .nil

/-- `MS-TUPLE` is the component-stack theorem packaged as an atom output. -/
theorem matom_tuple_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {prevailing : Subst} {patterns : List Pattern}
    {matchers values : List Value} {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input (.ptuple patterns) capability target output)
    (matcherTyping : MatcherUsable signature (.tuple matchers)
      capability target)
    (valueTyping : ValueTy signature (.tuple values) target) :
    MAtomTypedOutput signature context parameters input output
      [(patterns.zip (matchers.zip values)).map fun entry =>
        ⟨entry.1, entry.2.1, entry.2.2⟩] [] := by
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_singleton] at member
  subst atoms
  simpa [List.map_map, Function.comp_def] using
    resolution.tuple_atomStack signatureWF matcherTyping valueTyping

/-- `MS-PROD-SOME` reuses the same resolved primitive pattern with the
target-polymorphic `something` matcher. -/
theorem matom_prodSome_typed
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {prevailing : Subst} {pattern : Pattern}
    {value : Value} {capability : Cap} {target : Ty}
    (resolution : ResolvedPatternTy signature prevailing context parameters
      input pattern capability target output)
    (primitive : pattern.isPrimForm = true)
    (valueTyping : ValueTy signature value target) :
    MAtomTypedOutput signature context parameters input output
      [[⟨pattern, .something, value⟩]] [] := by
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_singleton] at member
  subst atoms
  exact .cons (.atom (.primitive resolution primitive
    MatcherAtTarget.something valueTyping)) .nil

/-! ## Typed successful matcher dispatch -/

/--
The continuation core of `MS-MATCHER`.  Evaluation and decoding are handled
outside this lemma; its inputs are the exact typed slot/value lists they
produce.  A non-catch-all clause uses the two-substitution capture theorem.
The catch-all exception is permitted only for a primitive user pattern and is
typed with `AtomTy.primitive` at the captured slot's target.
-/
theorem matcher_success_continuations_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env}
    {patternPrevailing ppPrevailing : Subst}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {pattern : Pattern}
    {patternCapability : Cap} {target : Ty}
    {pp : PPat} {holes : List Dual} {ppBindings : MonoCtx}
    {captures : List Pattern}
    {ppEnvironment : Env} {matchers : List Value}
    {valueLists : List (List Value)}
    (patternResolution : TerminalPatternResolution signature patternPrevailing
      context parameters input pattern patternCapability target output)
    (ppResolution : TerminalPPatResolution signature ppPrevailing pp target
      holes ppBindings)
    (capTyping : PPatCapsAt signature true pp
      (holes.map Dual.cap) patternCapability)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (dispatchKind : pp ≠ .hole ∨ pattern.isPrimForm = true)
    (matcherTyping : ValueTys signature matchers
      (holes.map fun hole => .slot hole.cap hole.target))
    (valueListsTyping : ∀ values ∈ valueLists,
      ValueTys signature values (holes.map Dual.target)) :
    ∀ values ∈ valueLists,
      StackTy signature context parameters input
        ((captures.zip (matchers.zip values)).map fun entry =>
          Tree.atom ⟨entry.1, entry.2.1, entry.2.2⟩)
        output := by
  by_cases ppIsHole : pp = .hole
  · subst pp
    have primitive : pattern.isPrimForm = true := by
      rcases dispatchKind with nonCatchAll | primitive
      · exact (nonCatchAll rfl).elim
      · exact primitive
    cases matching
    obtain ⟨holeCapability, holesEquality, bindingsEquality⟩ :=
      (ResolvedPPatTy.ofTerminal ppResolution).hole_inversion
    subst holes
    intro values valuesMember
    have valuesTyping := valueListsTyping values valuesMember
    cases matcherTyping with
    | cons matcherHead matcherTail =>
        cases matcherTail
        cases valuesTyping with
        | cons valueHead valueTail =>
            cases valueTail
            exact .cons
              (.atom (.primitive (.ofTerminal patternResolution) primitive
                ⟨_, .inr matcherHead⟩ valueHead))
              .nil
  · obtain ⟨capturedDuals, capturedResolution, capEquality,
        targetEquality⟩ :=
      ppm_captures_terminal_parts signatureWF ppResolution capTyping
        patternResolution matching ppIsHole
    have actualEquality : capturedDuals = holes :=
      Dual.list_eq_of_maps_eq capEquality targetEquality
    have actualMatcherTyping := matcherTyping
    rw [← actualEquality] at actualMatcherTyping
    have matcherUsable := actualMatcherTyping.slotUsables
    intro values valuesMember
    have valuesTyping := valueListsTyping values valuesMember
    rw [← actualEquality] at valuesTyping
    exact capturedResolution.atomStack matcherUsable valuesTyping

/-- A primitive source pattern may be checked by a matcher whose capability
is unrelated to the pattern's producer capability.  In that target-only
case, a PP hole returns the primitive atom itself and every non-hole PP
returns the empty continuation. -/
theorem matcher_success_primitive_continuations_typed
    {signature : FrozenSig} {SF : RuntimeSigF} {environment : Env}
    {prevailing clausePrevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx} {pattern : Pattern}
    {patternCapability : Cap} {target : Ty} {pp : PPat}
    {holes : List Dual} {ppBindings : MonoCtx} {captures : List Pattern}
    {ppEnvironment : Env} {matchers : List Value}
    {valueLists : List (List Value)}
    (patternTyping : ResolvedPatternTy signature prevailing context parameters
      input pattern patternCapability target output)
    (primitive : pattern.isPrimForm = true)
    (ppTyping : ResolvedPPatTy signature clausePrevailing pp target holes
      ppBindings)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (matcherTyping : ValueTys signature matchers
      (holes.map fun hole => Ty.slot hole.cap hole.target))
    (valueListsTyping : ∀ values ∈ valueLists,
      ValueTys signature values (holes.map Dual.target)) :
    ∀ values ∈ valueLists,
      StackTy signature context parameters input
        ((captures.zip (matchers.zip values)).map fun entry =>
          Tree.atom ⟨entry.1, entry.2.1, entry.2.2⟩) output := by
  cases matching with
  | hole =>
      obtain ⟨holeCapability, holesEquality, bindingsEquality⟩ :=
        ppTyping.hole_inversion
      subst holes
      intro values valuesMember
      have valuesTyping := valueListsTyping values valuesMember
      cases matcherTyping with
      | cons matcherHead matcherTail =>
          cases matcherTail
          cases valuesTyping with
          | cons valueHead valueTail =>
              cases valueTail
              exact .cons
                (.atom (.primitive patternTyping primitive
                  ⟨holeCapability, .inr matcherHead⟩ valueHead)) .nil
  | wild =>
      obtain ⟨holesEquality, bindingsEquality⟩ := ppTyping.wild_inversion
      subst holes
      have outputEquality := patternTyping.wild_inversion
      subst output
      intro values valuesMember
      exact .nil
  | pval evaluation =>
      have holesEquality := ppTyping.pval_holes
      subst holes
      have outputEquality := patternTyping.pval_inversion |>.1
      subst output
      intro values valuesMember
      exact .nil
  | ctor lengthPP lengthResults all =>
      simp [Pattern.isPrimForm] at primitive
  | tuple lengthPP lengthResults all =>
      simp [Pattern.isPrimForm] at primitive

/-- Primitive source patterns need no capability alignment to recover the
narrow capture fact: a successful PPM can only be a hole, wildcard, or value
pattern at these indices. -/
theorem captureAdm_of_primitive_success
    {signature : FrozenSig} {SF : RuntimeSigF} {environment : Env}
    {ppPrevailing patternPrevailing : Subst} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {pp : PPat} {pattern : Pattern} {patternCapability : Cap} {target : Ty}
    {holes : List Dual} {ppBindings : MonoCtx}
    {captures : List Pattern} {ppEnvironment : Env}
    (patternTyping : ResolvedPatternTy signature patternPrevailing context
      parameters input pattern patternCapability target output)
    (primitive : pattern.isPrimForm = true)
    (ppTyping : ResolvedPPatTy signature ppPrevailing pp target holes
      ppBindings)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment))) :
    CaptureAdm signature context input pp pattern target ppBindings := by
  cases matching with
  | hole =>
      obtain ⟨_, _, bindingsEquality⟩ := ppTyping.hole_inversion
      subst ppBindings
      exact .hole
  | wild =>
      obtain ⟨_, bindingsEquality⟩ := ppTyping.wild_inversion
      subst ppBindings
      exact .wild
  | pval evaluation =>
      cases ppTyping.terminal
      have expressionTyping := patternTyping.pval_inversion.2
      simpa [MonoCtx.applySubst] using (CaptureAdm.pval expressionTyping)
  | ctor => simp [Pattern.isPrimForm] at primitive
  | tuple => simp [Pattern.isPrimForm] at primitive

/-- Full typed-output rule for the successful matcher arm.  Its three
recursive premises are tied to the concrete PPM/body/next derivations of this
very `MAtom.matcher` constructor. -/
theorem matom_matcher_success_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment matcherEnvironment : Env}
    {original clauses : List Clause} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {prevailing : Subst} {pattern : Pattern} {capability : Cap}
    {target : Ty} {value : Value} {pp : PPat} {next : Expr}
    {dp : DPat} {body : Expr} {arms : List Arm}
    {captures : List Pattern} {ppEnvironment dataEnvironment : Env}
    {decomposition : Value} {tuples : List Value}
    {valueLists : List (List Value)} {matcherValue : Value}
    {matchers : List Value}
    (patternTyping : ResolvedPatternTy signature prevailing context parameters
      input pattern capability target output)
    (matcherTyping : MatcherUsable signature
      (.matcherV matcherEnvironment original
        (.mk pp next (.mk dp body :: arms) :: clauses)) capability target)
    (valueTyping : ValueTy signature value target)
    (trace : DispatchTrace SF environment pattern value original
      (.mk pp next (.mk dp body :: arms) :: clauses))
    (dispatchable : pattern.isMatcherDispatchable = true)
    (ppSuccess : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (dataSuccess : pdMatch dp value = some dataEnvironment)
    (bodyEvaluation : Eval SF
      (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
      body decomposition)
    (listDecode : listOfV decomposition = some tuples)
    (tupleDecodes : tuples.mapM (decodeTuple captures.length) =
      some valueLists)
    (nextEvaluation : Eval SF matcherEnvironment next matcherValue)
    (matcherDecode : decodeTuple captures.length matcherValue = some matchers)
    (ppPreserve :
      ∀ {clauseTarget : Ty} {clauseBindings : MonoCtx},
        CaptureAdm signature context input pp pattern clauseTarget
          clauseBindings →
        MonoEnvTys signature clauseBindings ppEnvironment)
    (bodyPreserve :
      ∀ {bodyContext : Context} {bodyTarget : Ty},
        Eval SF (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
          body decomposition →
        EnvTyped signature bodyContext
          (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) →
        HasTy signature bodyContext body bodyTarget →
        ValueTy signature decomposition bodyTarget)
    (nextPreserve :
      ∀ {nextContext : Context} {nextTarget : Ty},
        Eval SF matcherEnvironment next matcherValue →
        EnvTyped signature nextContext matcherEnvironment →
        HasTy signature nextContext next nextTarget →
        ValueTy signature matcherValue nextTarget) :
    MAtomTypedOutput signature context parameters input output
      (valueLists.map fun values =>
        (captures.zip (matchers.zip values)).map fun entry =>
          ⟨entry.1, entry.2.1, entry.2.2⟩) [] := by
  obtain ⟨matcherContext, evidence, matcherEnvironmentTyped, cursor,
      sourceTyping, clausesTyped, shape, catchAll, armsExhaustive, ppNodup,
      armNodup, coverage⟩ :=
    ValueTy.coveredMatcherUsable_inversion matcherTyping
  obtain ⟨originalClause, clausePrevailing, clauseEvidence, typedPP,
      clauseHoles, ppBindings, nextMatchers, result, typedDP, typedBody,
      armBindings, sourceMember, clauseCursor, clauseTyping,
      originalPP, ppTyping, ppCaps, nextDecomposition, nextExpressionsTyping,
      resultEquality, armEquality, dataPatternTyping, bodyTyping⟩ :=
    cursor.arm_typed clausesTyped
      (show Clause.mk pp next (Arm.mk dp body :: arms) ∈
        Clause.mk pp next (Arm.mk dp body :: arms) :: clauses from
          List.mem_cons_self)
      (show Arm.mk dp body ∈ Arm.mk dp body :: arms from List.mem_cons_self)
  have headerPP : pp = originalClause.pp := by
    simpa [Clause.pp] using clauseCursor.headers.1
  have ppEquality : pp = typedPP := headerPP.trans originalPP
  subst typedPP
  have nextEquality : next = originalClause.next := by
    simpa [Clause.next] using clauseCursor.headers.2
  rw [← nextEquality] at nextDecomposition
  rw [← headerPP] at ppTyping ppCaps
  injection armEquality with dpEquality bodyEquality
  subst typedDP
  subst typedBody
  subst result
  have ppOrder : PPatCoreOrder pp := by
    rw [headerPP]
    exact clauseTyping.coreOrder
  have ppAdmissible := captureAdm_of_coreOrder signatureWF
    ppOrder ppTyping ppCaps patternTyping ppSuccess
  have ppEnvironmentTyping := ppPreserve ppAdmissible
  have dataEnvironmentTyping :=
    pdMatch_typed signatureWF dataPatternTyping valueTyping dataSuccess
  have bodyEnvironmentTyping :
      EnvTyped signature
        (armBindings.toContext ++ ppBindings.toContext ++ matcherContext)
        (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) := by
    simpa [List.append_assoc] using
      dataEnvironmentTyping.envTyped_append
        (ppEnvironmentTyping.envTyped_append matcherEnvironmentTyped)
  have decompositionTyping :=
    bodyPreserve bodyEvaluation bodyEnvironmentTyping bodyTyping
  have tuplesTyping :=
    listOfV_typed signatureWF decompositionTyping listDecode
  have captureLength : captures.length = clauseHoles.length :=
    (ppm_captures_length pp ppSuccess).trans ppTyping.holes_length.symm
  have tupleDecodes' :
      tuples.mapM (decodeTuple clauseHoles.length) = some valueLists := by
    simpa [captureLength] using tupleDecodes
  have matcherDecode' :
      decodeTuple clauseHoles.length matcherValue = some matchers := by
    simpa [captureLength] using matcherDecode
  have nextDecomposition' :
      decomposeME next
        (clauseHoles.map fun hole => Ty.slot hole.cap hole.target).length =
          some nextMatchers := by
    simpa using nextDecomposition
  have nextSourceTyping :=
    decomposeME_typed nextDecomposition' nextExpressionsTyping
  have matcherValueTyping :=
    nextPreserve nextEvaluation matcherEnvironmentTyped nextSourceTyping
  have matchersTyping :=
    decodeTuple_typed signatureWF matcherValueTyping (by
      simpa only [List.length_map] using matcherDecode')
  have valueListsTyping :=
    decodeTuple_mapM_typed signatureWF tuplesTyping (by
      simpa only [List.length_map] using tupleDecodes')
  have dispatch : DispatchOK signature.toMatcherSig original capability :=
    coverageOK_catchAllLast_dispatchOK signature.toMatcherSig original
      capability coverage catchAll
  have patternResolution := patternTyping.terminal
  have ppResolution := ppTyping.terminal
  have dispatchKind := trace.nonCatchAll_or_primitive signatureWF
    patternResolution dispatchable dispatch catchAll
  have continuationsTyped :=
    matcher_success_continuations_typed signatureWF patternResolution
      ppResolution ppCaps ppSuccess dispatchKind matchersTyping
      valueListsTyping
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_map] at member
  obtain ⟨values, valuesMember, rfl⟩ := member
  simpa only [List.map_map, Function.comp_def] using
      continuationsTyped values valuesMember

/-- Successful matcher dispatch for the target-only primitive branch of
`AtomTy`.  Clause typing still comes from the literal's own certified
capability, while the produced primitive atoms retain the source pattern's
independent capability. -/
theorem matom_matcher_success_primitive_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment matcherEnvironment : Env}
    {original clauses : List Clause} {context : Context}
    {parameters : PatternCtx} {input output : MonoCtx}
    {prevailing : Subst} {pattern : Pattern} {patternCapability : Cap}
    {target : Ty} {value : Value} {pp : PPat} {next : Expr}
    {dp : DPat} {body : Expr} {arms : List Arm}
    {captures : List Pattern} {ppEnvironment dataEnvironment : Env}
    {decomposition : Value} {tuples : List Value}
    {valueLists : List (List Value)} {matcherValue : Value}
    {matchers : List Value}
    (patternTyping : ResolvedPatternTy signature prevailing context parameters
      input pattern patternCapability target output)
    (primitive : pattern.isPrimForm = true)
    (matcherTyping : MatcherAtTarget signature
      (.matcherV matcherEnvironment original
        (.mk pp next (.mk dp body :: arms) :: clauses)) target)
    (valueTyping : ValueTy signature value target)
    (ppSuccess : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (dataSuccess : pdMatch dp value = some dataEnvironment)
    (bodyEvaluation : Eval SF
      (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
      body decomposition)
    (listDecode : listOfV decomposition = some tuples)
    (tupleDecodes : tuples.mapM (decodeTuple captures.length) =
      some valueLists)
    (nextEvaluation : Eval SF matcherEnvironment next matcherValue)
    (matcherDecode : decodeTuple captures.length matcherValue = some matchers)
    (ppPreserve :
      ∀ {clauseTarget : Ty} {clauseBindings : MonoCtx},
        CaptureAdm signature context input pp pattern clauseTarget
          clauseBindings →
        MonoEnvTys signature clauseBindings ppEnvironment)
    (bodyPreserve :
      ∀ {bodyContext : Context} {bodyTarget : Ty},
        Eval SF (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
          body decomposition →
        EnvTyped signature bodyContext
          (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) →
        HasTy signature bodyContext body bodyTarget →
        ValueTy signature decomposition bodyTarget)
    (nextPreserve :
      ∀ {nextContext : Context} {nextTarget : Ty},
        Eval SF matcherEnvironment next matcherValue →
        EnvTyped signature nextContext matcherEnvironment →
        HasTy signature nextContext next nextTarget →
        ValueTy signature matcherValue nextTarget) :
    MAtomTypedOutput signature context parameters input output
      (valueLists.map fun values =>
        (captures.zip (matchers.zip values)).map fun entry =>
          ⟨entry.1, entry.2.1, entry.2.2⟩) [] := by
  obtain ⟨matcherCapability, matcherUsable⟩ := matcherTyping
  obtain ⟨matcherContext, evidence, matcherEnvironmentTyped, cursor,
      sourceTyping, clausesTyped, shape, catchAll, armsExhaustive, ppNodup,
      armNodup, coverage⟩ :=
    ValueTy.coveredMatcherUsable_inversion matcherUsable
  obtain ⟨originalClause, clausePrevailing, clauseEvidence, typedPP,
      clauseHoles, ppBindings, nextMatchers, result, typedDP, typedBody,
      armBindings, sourceMember, clauseCursor, clauseTyping,
      originalPP, ppTyping, ppCaps, nextDecomposition, nextExpressionsTyping,
      resultEquality, armEquality, dataPatternTyping, bodyTyping⟩ :=
    cursor.arm_typed clausesTyped
      (show Clause.mk pp next (Arm.mk dp body :: arms) ∈
          Clause.mk pp next (Arm.mk dp body :: arms) :: clauses by simp)
      (show Arm.mk dp body ∈ Arm.mk dp body :: arms by simp)
  have headerPP : pp = originalClause.pp := by
    simpa [Clause.pp] using clauseCursor.headers.1
  have ppEquality : pp = typedPP := headerPP.trans originalPP
  subst typedPP
  have nextEquality : next = originalClause.next := by
    simpa [Clause.next] using clauseCursor.headers.2
  rw [← nextEquality] at nextDecomposition
  rw [← headerPP] at ppTyping
  injection armEquality with dataPatternEquality bodyEquality
  subst typedDP
  subst typedBody
  subst result
  have ppAdmissible := captureAdm_of_primitive_success patternTyping
    primitive ppTyping ppSuccess
  have ppEnvironmentTyping := ppPreserve ppAdmissible
  have dataEnvironmentTyping :=
    pdMatch_typed signatureWF dataPatternTyping valueTyping dataSuccess
  have bodyEnvironmentTyping :
      EnvTyped signature
        (armBindings.toContext ++ ppBindings.toContext ++ matcherContext)
        (dataEnvironment ++ ppEnvironment ++ matcherEnvironment) := by
    simpa [List.append_assoc] using
      dataEnvironmentTyping.envTyped_append
        (ppEnvironmentTyping.envTyped_append matcherEnvironmentTyped)
  have decompositionTyping :=
    bodyPreserve bodyEvaluation bodyEnvironmentTyping bodyTyping
  have tuplesTyping :=
    listOfV_typed signatureWF decompositionTyping listDecode
  have captureLength : captures.length = clauseHoles.length :=
    (ppm_captures_length pp ppSuccess).trans ppTyping.holes_length.symm
  have tupleDecodes' :
      tuples.mapM (decodeTuple clauseHoles.length) = some valueLists := by
    simpa [captureLength] using tupleDecodes
  have matcherDecode' :
      decodeTuple clauseHoles.length matcherValue = some matchers := by
    simpa [captureLength] using matcherDecode
  have nextDecomposition' :
      decomposeME next
        (clauseHoles.map fun hole => Ty.slot hole.cap hole.target).length =
          some nextMatchers := by
    simpa using nextDecomposition
  have nextSourceTyping :=
    decomposeME_typed nextDecomposition' nextExpressionsTyping
  have matcherValueTyping :=
    nextPreserve nextEvaluation matcherEnvironmentTyped nextSourceTyping
  have matchersTyping :=
    decodeTuple_typed signatureWF matcherValueTyping (by
      simpa only [List.length_map] using matcherDecode')
  have valueListsTyping :=
    decodeTuple_mapM_typed signatureWF tuplesTyping (by
      simpa only [List.length_map] using tupleDecodes')
  have continuationsTyped :=
    matcher_success_primitive_continuations_typed patternTyping primitive
      ppTyping ppSuccess matchersTyping valueListsTyping
  intro substitution substitutionTyping
  refine ⟨input, by simpa using substitutionTyping, ?_⟩
  intro atoms member
  simp only [List.mem_map] at member
  obtain ⟨values, valuesMember, rfl⟩ := member
  simpa only [List.map_map, Function.comp_def] using
    continuationsTyped values valuesMember

/-! ## Internal matcher-cursor transport for the combined proof -/

/-- Advancing past a failed clause preserves exact matcher usability. -/
theorem MatcherUsable.matcher_nextClause
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arms : List Arm} {clauses : List Clause}
    {capability : Cap} {target : Ty}
    (typing : MatcherUsable signature
      (.matcherV environment original (.mk pp next arms :: clauses))
      capability target) :
    MatcherUsable signature (.matcherV environment original clauses)
      capability target := by
  obtain ⟨context, environmentTyping, cursor, sourceTyping⟩ :=
    (ValueTy.matcherUsable_asMatcher typing).matcherLiteral_inversion
  exact .inl (.matcherLiteral context
    (fun name value found => environmentTyping.domain found)
    (fun name value scheme actual found sourceFound instantiation =>
      environmentTyping.lookup found sourceFound instantiation)
    sourceTyping (.nextClause cursor))

/-- Advancing past a failed data arm preserves exact matcher usability. -/
theorem MatcherUsable.matcher_nextArm
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arm : Arm} {arms : List Arm}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing : MatcherUsable signature
      (.matcherV environment original (.mk pp next (arm :: arms) :: clauses))
      capability target) :
    MatcherUsable signature
      (.matcherV environment original (.mk pp next arms :: clauses))
      capability target := by
  obtain ⟨context, environmentTyping, cursor, sourceTyping⟩ :=
    (ValueTy.matcherUsable_asMatcher typing).matcherLiteral_inversion
  exact .inl (.matcherLiteral context
    (fun name value found => environmentTyping.domain found)
    (fun name value scheme actual found sourceFound instantiation =>
      environmentTyping.lookup found sourceFound instantiation)
    sourceTyping (.nextArm cursor))

/-- Target-only matcher evidence is stable under a failed clause. -/
theorem MatcherAtTarget.matcher_nextClause
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arms : List Arm} {clauses : List Clause}
    {target : Ty}
    (typing : MatcherAtTarget signature
      (.matcherV environment original (.mk pp next arms :: clauses)) target) :
    MatcherAtTarget signature (.matcherV environment original clauses)
      target := by
  obtain ⟨capability, usable⟩ := typing
  exact ⟨capability, usable.matcher_nextClause⟩

/-- Target-only matcher evidence is stable under a failed data arm. -/
theorem MatcherAtTarget.matcher_nextArm
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arm : Arm} {arms : List Arm}
    {clauses : List Clause} {target : Ty}
    (typing : MatcherAtTarget signature
      (.matcherV environment original (.mk pp next (arm :: arms) :: clauses))
      target) :
    MatcherAtTarget signature
      (.matcherV environment original (.mk pp next arms :: clauses))
      target := by
  obtain ⟨capability, usable⟩ := typing
  exact ⟨capability, usable.matcher_nextArm⟩

/-- Atom typing follows the private suffix cursor after one PP failure. -/
theorem AtomTy.matcher_nextClause
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {pattern : Pattern} {environment : Env}
    {original : List Clause} {pp : PPat} {next : Expr} {arms : List Arm}
    {clauses : List Clause} {value : Value}
    (typing : AtomTy signature context parameters input
      ⟨pattern, .matcherV environment original (.mk pp next arms :: clauses),
        value⟩ output) :
    AtomTy signature context parameters input
      ⟨pattern, .matcherV environment original clauses, value⟩ output := by
  cases typing with
  | mk patternTyping matcherTyping valueTyping =>
      exact .mk patternTyping matcherTyping.matcher_nextClause valueTyping
  | primitive patternTyping primitive matcherTyping valueTyping =>
      exact .primitive patternTyping primitive
        matcherTyping.matcher_nextClause valueTyping

/-- Atom typing follows the private suffix cursor after one data-arm failure. -/
theorem AtomTy.matcher_nextArm
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {pattern : Pattern} {environment : Env}
    {original : List Clause} {pp : PPat} {next : Expr} {dp : DPat}
    {body : Expr} {arms : List Arm} {clauses : List Clause} {value : Value}
    (typing : AtomTy signature context parameters input
      ⟨pattern,
        .matcherV environment original
          (.mk pp next (.mk dp body :: arms) :: clauses), value⟩ output) :
    AtomTy signature context parameters input
      ⟨pattern, .matcherV environment original (.mk pp next arms :: clauses),
        value⟩ output := by
  cases typing with
  | mk patternTyping matcherTyping valueTyping =>
      exact .mk patternTyping matcherTyping.matcher_nextArm valueTyping
  | primitive patternTyping primitive matcherTyping valueTyping =>
      exact .primitive patternTyping primitive
        matcherTyping.matcher_nextArm valueTyping

/-- Concrete failure history required only while one `MAtom` dispatch walks a
matcher literal.  Non-literal matchers satisfy it vacuously. -/
def MAtomDispatchTrace
    (SF : RuntimeSigF) (environment : Env) (pattern : Pattern)
    (value matcher : Value) : Prop :=
  ∀ {matcherEnvironment : Env} {original current : List Clause},
    matcher = .matcherV matcherEnvironment original current →
    DispatchTrace SF environment pattern value original current

/-! ## Derivation-local runtime-signature agreement -/

/-
Runtime pattern-function agreement is needed only when evaluation reaches an
actual `matchAll` and its matching search later enters a pattern function.
The five operational judgments are mutual, so this proof-relevant package
mirrors their concrete derivations and records agreement only at those exact
evaluation sites.  It contains no typing result, `MAtom` result, successor,
or termination oracle.
-/
mutual

inductive EvalRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {environment : Env} → {expression : Expr} → {value : Value} →
      Eval SF environment expression value → Prop where
  | evar {environment : Env} {name : String} {value : Value}
      {found : Env.find? environment name = some value} :
      EvalRuntimeSigAgrees signature SF (.var found)
  | elam {environment parameter body} :
      EvalRuntimeSigAgrees signature SF
        (@Eval.lam SF environment parameter body)
  | efix {environment name parameter body} :
      EvalRuntimeSigAgrees signature SF
        (@Eval.fix SF environment name parameter body)
  | eapp
      {environment function argument self closureEnvironment parameter body
       argumentValue value}
      {functionEvaluation : Eval SF environment function
        (.closure self closureEnvironment parameter body)}
      {argumentEvaluation : Eval SF environment argument argumentValue}
      {bodyEvaluation : Eval SF
        (pushArg self closureEnvironment parameter body argumentValue)
        body value} :
      EvalRuntimeSigAgrees signature SF functionEvaluation →
      EvalRuntimeSigAgrees signature SF argumentEvaluation →
      EvalRuntimeSigAgrees signature SF bodyEvaluation →
      EvalRuntimeSigAgrees signature SF
        (.app functionEvaluation argumentEvaluation bodyEvaluation)
  | elit {environment value} :
      EvalRuntimeSigAgrees signature SF (@Eval.lit SF environment value)
  | etuple
      {environment : Env} {expressions : List Expr} {values : List Value}
      {lengths : expressions.length = values.length}
      {evaluations : ∀ pair ∈ expressions.zip values,
        Eval SF environment pair.1 pair.2} :
      (∀ pair (member : pair ∈ expressions.zip values),
        EvalRuntimeSigAgrees signature SF (evaluations pair member)) →
      EvalRuntimeSigAgrees signature SF (.tuple lengths evaluations)
  | ector
      {environment : Env} {name : String} {expressions : List Expr}
      {values : List Value}
      {lengths : expressions.length = values.length}
      {evaluations : ∀ pair ∈ expressions.zip values,
        Eval SF environment pair.1 pair.2} :
      (∀ pair (member : pair ∈ expressions.zip values),
        EvalRuntimeSigAgrees signature SF (evaluations pair member)) →
      EvalRuntimeSigAgrees signature SF (.ctor lengths evaluations)
  | eprim
      {environment : Env} {operation : PrimOp} {expressions : List Expr}
      {values : List Value} {value : Value}
      {lengths : expressions.length = values.length}
      {evaluations : ∀ pair ∈ expressions.zip values,
        Eval SF environment pair.1 pair.2}
      {primitive : primEval operation values = some value} :
      (∀ pair (member : pair ∈ expressions.zip values),
        EvalRuntimeSigAgrees signature SF (evaluations pair member)) →
      EvalRuntimeSigAgrees signature SF
        (.prim lengths evaluations primitive)
  | elet
      {environment name bound body boundValue value}
      {boundEvaluation : Eval SF environment bound boundValue}
      {bodyEvaluation : Eval SF ((name, boundValue) :: environment) body value} :
      EvalRuntimeSigAgrees signature SF boundEvaluation →
      EvalRuntimeSigAgrees signature SF bodyEvaluation →
      EvalRuntimeSigAgrees signature SF
        (.letE boundEvaluation bodyEvaluation)
  | esomething {environment} :
      EvalRuntimeSigAgrees signature SF (@Eval.something SF environment)
  | ematcher {environment clauses} :
      EvalRuntimeSigAgrees signature SF (@Eval.matcher SF environment clauses)
  | ematchAll
      {environment : Env} {target matcher body : Expr} {pattern : Pattern}
      {targetValue matcherValue : Value}
      {substitutions : List MatchSubst} {values : List Value}
      {targetEvaluation : Eval SF environment target targetValue}
      {matcherEvaluation : Eval SF environment matcher matcherValue}
      {search : Search SF
        ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩
        substitutions}
      {lengths : substitutions.length = values.length}
      {evaluations : ∀ pair ∈ substitutions.zip values,
        Eval SF (pair.1 ++ environment) body pair.2} :
      (∀ {context : Context} {result : Ty},
        EnvTyped signature context environment →
        HasTy signature context (.matchAll target matcher pattern body) result →
        RuntimeSigAgrees signature context SF) →
      EvalRuntimeSigAgrees signature SF targetEvaluation →
      EvalRuntimeSigAgrees signature SF matcherEvaluation →
      SearchRuntimeSigAgrees signature SF search →
      (∀ pair (member : pair ∈ substitutions.zip values),
        EvalRuntimeSigAgrees signature SF (evaluations pair member)) →
      EvalRuntimeSigAgrees signature SF
        (.matchAll targetEvaluation matcherEvaluation search lengths evaluations)

inductive PPMRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {environment : Env} → {pp : PPat} → {pattern : Pattern} →
      {result : Option (List Pattern × Env)} →
      PPM SF environment pp pattern result → Prop where
  | phole {environment pattern} :
      PPMRuntimeSigAgrees signature SF (@PPM.hole SF environment pattern)
  | pwild {environment} :
      PPMRuntimeSigAgrees signature SF (@PPM.wild SF environment)
  | ppval
      {environment name expression value}
      {evaluation : Eval SF environment expression value} :
      EvalRuntimeSigAgrees signature SF evaluation →
      PPMRuntimeSigAgrees signature SF (@PPM.pval SF environment name
        expression value evaluation)
  | pctor
      {environment : Env} {name : String} {pps : List PPat}
      {patterns : List Pattern} {results : List (List Pattern × Env)}
      {lengthPP : pps.length = patterns.length}
      {lengthResults : (pps.zip patterns).length = results.length}
      {matchings : ∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF environment entry.1.1 entry.1.2 (some entry.2)} :
      (∀ entry (member : entry ∈ (pps.zip patterns).zip results),
        PPMRuntimeSigAgrees signature SF (matchings entry member)) →
      PPMRuntimeSigAgrees signature SF
        (.ctor lengthPP lengthResults matchings)
  | ptuple
      {environment : Env} {pps : List PPat} {patterns : List Pattern}
      {results : List (List Pattern × Env)}
      {lengthPP : pps.length = patterns.length}
      {lengthResults : (pps.zip patterns).length = results.length}
      {matchings : ∀ entry ∈ (pps.zip patterns).zip results,
        PPM SF environment entry.1.1 entry.1.2 (some entry.2)} :
      (∀ entry (member : entry ∈ (pps.zip patterns).zip results),
        PPMRuntimeSigAgrees signature SF (matchings entry member)) →
      PPMRuntimeSigAgrees signature SF
        (.tuple lengthPP lengthResults matchings)
  | pfail {environment pp pattern}
      {failed : ppShapeOK pp pattern = false} :
      PPMRuntimeSigAgrees signature SF (@PPM.fail SF environment pp pattern
        failed)

inductive MAtomRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {environment : Env} → {pattern : Pattern} → {matcher value : Value} →
      {continuations : List (List Atom)} → {substitution : MatchSubst} →
      MAtom SF environment pattern matcher value continuations substitution →
      Prop where
  | msomeWC {environment value} :
      MAtomRuntimeSigAgrees signature SF (@MAtom.someWC SF environment value)
  | msomeVar {environment name value} :
      MAtomRuntimeSigAgrees signature SF (@MAtom.someVar SF environment name value)
  | msomeValEq
      {environment expression value expected}
      {evaluation : Eval SF environment expression expected}
      {equal : expected.structEq value = true} :
      EvalRuntimeSigAgrees signature SF evaluation →
      MAtomRuntimeSigAgrees signature SF (.someValEq evaluation equal)
  | msomeValNeq
      {environment expression value expected}
      {evaluation : Eval SF environment expression expected}
      {unequal : expected.structEq value = false} :
      EvalRuntimeSigAgrees signature SF evaluation →
      MAtomRuntimeSigAgrees signature SF (.someValNeq evaluation unequal)
  | mand {environment left right matcher value} :
      MAtomRuntimeSigAgrees signature SF
        (@MAtom.and SF environment left right matcher value)
  | mor {environment left right matcher value} :
      MAtomRuntimeSigAgrees signature SF
        (@MAtom.or SF environment left right matcher value)
  | mtuple
      {environment : Env} {patterns : List Pattern} {matchers values : List Value}
      {patternLength : patterns.length = matchers.length}
      {valueLength : matchers.length = values.length} :
      MAtomRuntimeSigAgrees signature SF
        (.tuple patternLength valueLength)
  | mprodSome
      {environment : Env} {pattern : Pattern} {matchers : List Value}
      {value : Value}
      {primitive : pattern.isPrimForm = true} :
      MAtomRuntimeSigAgrees signature SF (.prodSome primitive)
  | mppfail
      {environment matcherEnvironment : Env} {original : List Clause}
      {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
      {arms : List Arm} {clauses : List Clause}
      {continuations : List (List Atom)} {substitution : MatchSubst}
      {dispatch : pattern.isMatcherDispatchable = true}
      {failure : PPM SF environment pp pattern none}
      {recursive : MAtom SF environment pattern
        (.matcherV matcherEnvironment original clauses) value
        continuations substitution} :
      PPMRuntimeSigAgrees signature SF failure →
      MAtomRuntimeSigAgrees signature SF recursive →
      MAtomRuntimeSigAgrees signature SF
        (.matcherPPFail dispatch failure recursive)
  | mdpfail
      {environment matcherEnvironment : Env} {original : List Clause}
      {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
      {dp : DPat} {body : Expr} {arms : List Arm} {clauses : List Clause}
      {captures : List Pattern} {ppEnvironment : Env}
      {continuations : List (List Atom)} {substitution : MatchSubst}
      {dispatch : pattern.isMatcherDispatchable = true}
      {ppSuccess : PPM SF environment pp pattern
        (some (captures, ppEnvironment))}
      {dataFailure : pdMatch dp value = none}
      {recursive : MAtom SF environment pattern
        (.matcherV matcherEnvironment original (.mk pp next arms :: clauses))
        value continuations substitution} :
      PPMRuntimeSigAgrees signature SF ppSuccess →
      MAtomRuntimeSigAgrees signature SF recursive →
      MAtomRuntimeSigAgrees signature SF
        (.matcherDPFail dispatch ppSuccess dataFailure recursive)
  | mmatcher
      {environment matcherEnvironment : Env} {original : List Clause}
      {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
      {dp : DPat} {body : Expr} {arms : List Arm} {clauses : List Clause}
      {captures : List Pattern} {ppEnvironment dataEnvironment : Env}
      {decomposition : Value} {tuples : List Value}
      {valueLists : List (List Value)} {matcherValue : Value}
      {matchers : List Value}
      {dispatch : pattern.isMatcherDispatchable = true}
      {ppSuccess : PPM SF environment pp pattern
        (some (captures, ppEnvironment))}
      {dataSuccess : pdMatch dp value = some dataEnvironment}
      {bodyEvaluation : Eval SF
        (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
        body decomposition}
      {listDecode : listOfV decomposition = some tuples}
      {tupleDecodes : tuples.mapM (decodeTuple captures.length) =
        some valueLists}
      {nextEvaluation : Eval SF matcherEnvironment next matcherValue}
      {matcherDecode : decodeTuple captures.length matcherValue = some matchers} :
      PPMRuntimeSigAgrees signature SF ppSuccess →
      EvalRuntimeSigAgrees signature SF bodyEvaluation →
      EvalRuntimeSigAgrees signature SF nextEvaluation →
      MAtomRuntimeSigAgrees signature SF
        (.matcher dispatch ppSuccess dataSuccess bodyEvaluation listDecode
          tupleDecodes nextEvaluation matcherDecode)

inductive StepRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {state : MState} → {states : List MState} →
      Step SF state states → Prop where
  | sreduce
      {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {pattern : Pattern} {matcher value : Value}
      {continuations : List (List Atom)} {new : MatchSubst}
      {atomReduction : MAtom SF (substitution ++ environment) pattern matcher
        value continuations new} :
      MAtomRuntimeSigAgrees signature SF atomReduction →
      StepRuntimeSigAgrees signature SF (.reduce atomReduction)
  | spatfunEnter
      {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {name : String} {arguments : List Pattern} {matcher value : Value}
      {runtime : PatFunRuntimeSig}
      {found : List.find? (fun entry => entry.1 == name) SF =
        some (name, runtime)}
      {length : runtime.params.length = arguments.length} :
      StepRuntimeSigAgrees signature SF (.patfunEnter found length)
  | smnodeStep
      {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {tree : Tree} {innerStack : List Tree} {innerEnvironment : Env}
      {innerSubstitution : MatchSubst} {parameters : PiEnv}
      {states : List MState}
      {guard : ∀ name matcher value,
        tree = .atom ⟨.embed name, matcher, value⟩ →
        List.find? (fun entry => entry.1 == name) parameters = none}
      {inner : Step SF
        ⟨tree :: innerStack, innerEnvironment, innerSubstitution⟩ states} :
      StepRuntimeSigAgrees signature SF inner →
      StepRuntimeSigAgrees signature SF (.mnodeStep guard inner)
  | smnodeVarpat
      {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {name : String} {pattern : Pattern} {matcher value : Value}
      {innerStack : List Tree} {innerEnvironment : Env}
      {innerSubstitution : MatchSubst} {parameters : PiEnv}
      {found : List.find? (fun entry => entry.1 == name) parameters =
        some (name, pattern)} :
      StepRuntimeSigAgrees signature SF (.mnodeVarpat found)
  | smnodeDone
      {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {innerEnvironment : Env} {innerSubstitution : MatchSubst}
      {parameters : PiEnv} :
      StepRuntimeSigAgrees signature SF
        (@Step.mnodeDone SF stack environment substitution innerEnvironment
          innerSubstitution parameters)

inductive SearchRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {state : MState} → {substitutions : List MatchSubst} →
      Search SF state substitutions → Prop where
  | sdone {environment substitution} :
      SearchRuntimeSigAgrees signature SF (@Search.done SF environment substitution)
  | sstep
      {state : MState} {states : List MState}
      {substitutions : List (List MatchSubst)}
      {reduction : Step SF state states}
      {lengths : states.length = substitutions.length}
      {searches : ∀ pair ∈ states.zip substitutions,
        Search SF pair.1 pair.2} :
      StepRuntimeSigAgrees signature SF reduction →
      (∀ pair (member : pair ∈ states.zip substitutions),
        SearchRuntimeSigAgrees signature SF (searches pair member)) →
      SearchRuntimeSigAgrees signature SF
        (.step reduction lengths searches)

end

/-- A public matcher atom starts its private cursor history at reflexivity. -/
theorem MAtomDispatchTrace.pristine
    {SF : RuntimeSigF} {environment : Env} {pattern : Pattern}
    {value matcher : Value} (matcherPristine : ValuePristine matcher) :
    MAtomDispatchTrace SF environment pattern value matcher := by
  intro matcherEnvironment original current equality
  cases matcherPristine with
  | matcherLiteral environmentPristine =>
      cases equality
      exact .refl
  | _ => cases equality

/-- The PP-failure rule advances both the certified matcher type and the
concrete failure trace before invoking its exact recursive `MAtom` IH. -/
theorem matom_matcherPPFail_typed
    {signature : FrozenSig} {SF : RuntimeSigF} {environment : Env}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {matcherEnvironment : Env} {original : List Clause}
    {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
    {arms : List Arm} {clauses : List Clause}
    {continuations : List (List Atom)} {substitution : MatchSubst}
    (failure : PPM SF environment pp pattern none)
    (typing : AtomTy signature context parameters input
      ⟨pattern,
        .matcherV matcherEnvironment original (.mk pp next arms :: clauses),
        value⟩ output)
    (trace : MAtomDispatchTrace SF environment pattern value
      (.matcherV matcherEnvironment original (.mk pp next arms :: clauses)))
    (recursive :
      AtomTy signature context parameters input
        ⟨pattern, .matcherV matcherEnvironment original clauses, value⟩
        output →
      MAtomDispatchTrace SF environment pattern value
        (.matcherV matcherEnvironment original clauses) →
      MAtomTypedOutput signature context parameters input output
        continuations substitution) :
    MAtomTypedOutput signature context parameters input output
      continuations substitution := by
  apply recursive typing.matcher_nextClause
  intro foundEnvironment foundOriginal foundCurrent equality
  cases equality
  exact .nextClause (trace rfl) failure

/-- The data-pattern-failure rule advances to the next arm in both the
certified matcher type and the concrete failure trace. -/
theorem matom_matcherDPFail_typed
    {signature : FrozenSig} {SF : RuntimeSigF} {environment : Env}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {matcherEnvironment : Env} {original : List Clause}
    {pattern : Pattern} {value : Value} {pp : PPat} {next : Expr}
    {dp : DPat} {body : Expr} {arms : List Arm} {clauses : List Clause}
    {captures : List Pattern} {ppEnvironment : Env}
    {continuations : List (List Atom)} {substitution : MatchSubst}
    (ppSuccess : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (dataFailure : pdMatch dp value = none)
    (typing : AtomTy signature context parameters input
      ⟨pattern,
        .matcherV matcherEnvironment original
          (.mk pp next (.mk dp body :: arms) :: clauses), value⟩ output)
    (trace : MAtomDispatchTrace SF environment pattern value
      (.matcherV matcherEnvironment original
        (.mk pp next (.mk dp body :: arms) :: clauses)))
    (recursive :
      AtomTy signature context parameters input
        ⟨pattern,
          .matcherV matcherEnvironment original (.mk pp next arms :: clauses),
          value⟩ output →
      MAtomDispatchTrace SF environment pattern value
        (.matcherV matcherEnvironment original (.mk pp next arms :: clauses)) →
      MAtomTypedOutput signature context parameters input output
        continuations substitution) :
    MAtomTypedOutput signature context parameters input output
      continuations substitution := by
  apply recursive typing.matcher_nextArm
  intro foundEnvironment foundOriginal foundCurrent equality
  cases equality
  exact .nextArm (trace rfl) ppSuccess dataFailure

/-! ## Combined preservation kernels -/

/-- Internal motive shared by concrete evaluation-preservation calls. -/
private abbrev EvalPreservationKernel
    (signature : FrozenSig) (SF : RuntimeSigF) : Prop :=
  ∀ {environment : Env} {expression : Expr} {value : Value}
      {evaluation : Eval SF environment expression value},
    EvalRuntimeSigAgrees signature SF evaluation →
    ∀ {context : Context} {target : Ty},
      EnvPristine environment →
      EnvTyped signature context environment →
      HasTy signature context expression target →
      ValueTy signature value target

/-- Internal pristine-result motive for concrete evaluation. -/
private abbrev EvalPristineKernel
    (signature : FrozenSig) (SF : RuntimeSigF) : Prop :=
  ∀ {environment : Env} {expression : Expr} {value : Value}
      {evaluation : Eval SF environment expression value},
    EvalRuntimeSigAgrees signature SF evaluation →
    EnvPristine environment →
    ValuePristine value

/-- Internal motive for a successful concrete primitive-pattern match. -/
private abbrev PPMPreservationKernel
    (signature : FrozenSig) (SF : RuntimeSigF) : Prop :=
  ∀ {environment : Env} {pp : PPat} {pattern : Pattern}
      {captures : List Pattern} {ppEnvironment : Env}
      {matching : PPM SF environment pp pattern
        (some (captures, ppEnvironment))},
    PPMRuntimeSigAgrees signature SF matching →
    ∀ {context : Context} {input : MonoCtx} {target : Ty}
      {bindings : MonoCtx},
      EnvPristine environment →
      EnvTyped signature (input.toContext ++ context) environment →
      CaptureAdm signature context input pp pattern target bindings →
      MonoEnvTys signature bindings ppEnvironment

/-- Internal pristine-output motive for primitive-pattern matching. -/
private abbrev PPMPristineKernel
    (signature : FrozenSig) (SF : RuntimeSigF) : Prop :=
  ∀ {environment : Env} {pp : PPat} {pattern : Pattern}
      {result : Option (List Pattern × Env)}
      {matching : PPM SF environment pp pattern result},
    PPMRuntimeSigAgrees signature SF matching →
    EnvPristine environment →
    PPMOutputPristine result

/-- Primitive-pattern matching preserves the pristine boundary once nested
evaluations do. -/
private theorem PPMRuntimeSigAgrees.pristine_with
    {signature : FrozenSig} {SF : RuntimeSigF}
    (evalPristine : EvalPristineKernel signature SF)
    {environment : Env} {pp : PPat} {pattern : Pattern}
    {result : Option (List Pattern × Env)}
    {matching : PPM SF environment pp pattern result}
    (agreement : PPMRuntimeSigAgrees signature SF matching)
    (environmentPristine : EnvPristine environment) :
    PPMOutputPristine result := by
  refine PPMRuntimeSigAgrees.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {runtimeEnvironment} {_} {_} {runtimeResult} _ _ =>
      EnvPristine runtimeEnvironment → PPMOutputPristine runtimeResult)
    (motive_3 := fun _ _ => True)
    (motive_4 := fun _ _ => True)
    (motive_5 := fun _ _ => True)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep agreement environmentPristine
  case phole => exact fun _ => .nil
  case pwild => exact fun _ => .nil
  case ppval =>
    intro runtimeEnvironment name expression value evaluation
      evaluationAgreement evaluationIH runtimePristine
    exact .cons (evalPristine evaluationAgreement runtimePristine) .nil
  case pctor =>
    intro ignored runtimeEnvironment name pps patterns results patternLength
      resultLength matchings childrenAgreements childrenIH runtimePristine
    apply EnvPristine.flatten_map_snd
    intro child childMember
    obtain ⟨input, inputMember⟩ :=
      List.exists_fst_mem_zip_of_snd_mem resultLength childMember
    exact childrenIH (input, child) inputMember runtimePristine
  case ptuple =>
    intro runtimeEnvironment pps patterns results patternLength resultLength
      matchings childrenAgreements childrenIH runtimePristine
    apply EnvPristine.flatten_map_snd
    intro child childMember
    obtain ⟨input, inputMember⟩ :=
      List.exists_fst_mem_zip_of_snd_mem resultLength childMember
    exact childrenIH (input, child) inputMember runtimePristine
  case pfail => intros; trivial
  all_goals intros; trivial

/-- Fold exact child PPM preservation across a source-aligned compound
capture derivation. -/
private theorem CaptureAdms.ppm_environments_typed
    {signature : FrozenSig} {_SF : RuntimeSigF}
    {context : Context} {input : MonoCtx}
    {pps : List PPat} {patterns : List Pattern} {targets : List Ty}
    {bindings : MonoCtx}
    (admissible : CaptureAdms signature context input pps patterns targets
      bindings)
    {_environment : Env} {results : List (List Pattern × Env)}
    (patternLength : pps.length = patterns.length)
    (resultLength : (pps.zip patterns).length = results.length)
    (preserve :
      ∀ entry ∈ (pps.zip patterns).zip results,
        ∀ {target : Ty} {entryBindings : MonoCtx},
          CaptureAdm signature context input entry.1.1 entry.1.2 target
            entryBindings →
          MonoEnvTys signature entryBindings entry.2.2) :
    MonoEnvTys signature bindings ((results.map Prod.snd).flatten) := by
  induction pps generalizing patterns targets bindings results with
  | nil =>
      cases admissible
      cases results with
      | nil => exact .nil
      | cons result results => simp at resultLength
  | cons pp pps induction =>
      cases admissible with
      | cons head tail =>
          cases results with
          | nil => simp [List.zip_cons_cons] at resultLength
          | cons result results =>
              obtain ⟨captures, headEnvironment⟩ := result
              have headTyping := preserve
                ((_, _), (captures, headEnvironment))
                (by simp [List.zip_cons_cons]) head
              simpa [List.flatten_cons] using
                headTyping.append
                  (induction tail
                    (by simpa using patternLength)
                    (by simpa [List.zip_cons_cons] using resultLength)
                    (fun entry member {target} {entryBindings}
                        entryAdmissible =>
                      preserve entry (by
                        simp only [List.zip_cons_cons, List.mem_cons]
                        exact .inr member) entryAdmissible))

/-- Successful PPM preserves its exact monomorphic capture environment. -/
private theorem PPMRuntimeSigAgrees.preserve_with
    {signature : FrozenSig} {SF : RuntimeSigF}
    (evalPreserve : EvalPreservationKernel signature SF)
    {environment : Env} {pp : PPat} {pattern : Pattern}
    {result : Option (List Pattern × Env)}
    {matching : PPM SF environment pp pattern result}
    (agreement : PPMRuntimeSigAgrees signature SF matching)
    {captures : List Pattern} {ppEnvironment : Env}
    (resultEquality : result = some (captures, ppEnvironment))
    {context : Context} {input : MonoCtx} {target : Ty}
    {bindings : MonoCtx}
    (environmentPristine : EnvPristine environment)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    (admissible :
      CaptureAdm signature context input pp pattern target bindings) :
    MonoEnvTys signature bindings ppEnvironment := by
  refine PPMRuntimeSigAgrees.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun {runtimeEnvironment} {primitivePattern} {userPattern}
        {runtimeResult} _ _ =>
      ∀ {actualCaptures : List Pattern} {actualEnvironment : Env},
        runtimeResult = some (actualCaptures, actualEnvironment) →
        ∀ {sourceContext : Context} {sourceInput : MonoCtx}
          {sourceTarget : Ty} {sourceBindings : MonoCtx},
          EnvPristine runtimeEnvironment →
          EnvTyped signature (sourceInput.toContext ++ sourceContext)
            runtimeEnvironment →
          CaptureAdm signature sourceContext sourceInput primitivePattern
            userPattern sourceTarget sourceBindings →
          MonoEnvTys signature sourceBindings actualEnvironment)
    (motive_3 := fun _ _ => True)
    (motive_4 := fun _ _ => True)
    (motive_5 := fun _ _ => True)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep
    agreement resultEquality environmentPristine environmentTyping admissible
  case phole =>
    intro runtimeEnvironment userPattern actualCaptures actualEnvironment
      equality sourceContext sourceInput sourceTarget sourceBindings
      runtimePristine runtimeTyping captureTyping
    cases equality
    cases captureTyping
    exact .nil
  case pwild =>
    intro runtimeEnvironment actualCaptures actualEnvironment equality
      sourceContext sourceInput sourceTarget sourceBindings runtimePristine
      runtimeTyping captureTyping
    cases equality
    cases captureTyping
    exact .nil
  case ppval =>
    intro runtimeEnvironment name expression evaluated evaluation
      evaluationAgreement evaluationIH actualCaptures actualEnvironment equality
      sourceContext sourceInput sourceTarget sourceBindings runtimePristine
      runtimeTyping captureTyping
    cases equality
    cases captureTyping with
    | pval expressionTyping =>
        exact .cons
          (evalPreserve evaluationAgreement runtimePristine runtimeTyping
            expressionTyping)
          .nil
  case pctor =>
    intro ignoredName runtimeEnvironment name pps patterns results patternLength
      resultLength matchings childrenAgreements childrenIH actualCaptures
      actualEnvironment equality sourceContext sourceInput sourceTarget
      sourceBindings runtimePristine runtimeTyping captureTyping
    cases equality
    cases captureTyping with
    | ctor find children instantiation =>
        exact children.ppm_environments_typed (_SF := SF)
          (_environment := runtimeEnvironment) patternLength resultLength
          (fun entry member {target} {entryBindings} entryAdmissible =>
            childrenIH entry member rfl runtimePristine runtimeTyping
              entryAdmissible)
  case ptuple =>
    intro runtimeEnvironment pps patterns results patternLength resultLength
      matchings childrenAgreements childrenIH actualCaptures actualEnvironment
      equality sourceContext sourceInput sourceTarget sourceBindings
      runtimePristine runtimeTyping captureTyping
    cases equality
    cases captureTyping with
    | tuple children =>
        exact children.ppm_environments_typed (_SF := SF)
          (_environment := runtimeEnvironment) patternLength resultLength
          (fun entry member {target} {entryBindings} entryAdmissible =>
            childrenIH entry member rfl runtimePristine runtimeTyping
              entryAdmissible)
  all_goals intros; trivial

/-- All syntax-directed atom rules preserve their concrete threaded binding
indices.  The two callback arguments are the exact mutually recursive Eval
and PPM motives; neither supplies an operational result or successor. -/
private theorem MAtomRuntimeSigAgrees.preserve_with
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    (evalPristine : EvalPristineKernel signature SF)
    (evalPreserve : EvalPreservationKernel signature SF)
    (ppmPristine : PPMPristineKernel signature SF)
    (ppmPreserve : PPMPreservationKernel signature SF)
    {environment : Env} {pattern : Pattern} {matcher value : Value}
    {continuations : List (List Atom)} {new : MatchSubst}
    {reduction : MAtom SF environment pattern matcher value continuations new}
    (agreement : MAtomRuntimeSigAgrees signature SF reduction)
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx}
    (environmentPristine : EnvPristine environment)
    (valuePristine : ValuePristine value)
    (matcherPristine : MAtomInputPristine pattern matcher)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    (typing : AtomTy signature context parameters input
      ⟨pattern, matcher, value⟩ output)
    (trace : MAtomDispatchTrace SF environment pattern value matcher) :
    MAtomTypedOutput signature context parameters input output
      continuations new := by
  cases agreement with
  | msomeWC =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_someWC_typed patternTyping valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          exact matom_someWC_typed patternTyping valueTyping
  | msomeVar =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_someVar_typed patternTyping valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          exact matom_someVar_typed patternTyping valueTyping
  | msomeValEq evaluationAgreement =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_someValEq_typed patternTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          exact matom_someValEq_typed patternTyping
  | msomeValNeq evaluationAgreement =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_someValNeq_typed patternTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          exact matom_someValNeq_typed patternTyping
  | mand =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_and_typed patternTyping matcherTyping valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          simp [Pattern.isPrimForm] at primitive
  | mor =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_or_typed patternTyping matcherTyping valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          simp [Pattern.isPrimForm] at primitive
  | mtuple =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_tuple_typed signatureWF patternTyping matcherTyping
            valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          simp [Pattern.isPrimForm] at primitive
  | mprodSome =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          exact matom_prodSome_typed patternTyping (by assumption) valueTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          exact matom_prodSome_typed patternTyping primitive valueTyping
  | mppfail ppAgreement recursiveAgreement =>
      exact matom_matcherPPFail_typed (by assumption) typing trace
        (fun recursiveTyping recursiveTrace =>
          MAtomRuntimeSigAgrees.preserve_with signatureWF evalPristine
            evalPreserve ppmPristine ppmPreserve recursiveAgreement
            environmentPristine valuePristine
            (.inr ⟨_, _, _, rfl, matcherPristine.matcherEnvironment,
              by assumption⟩)
            environmentTyping recursiveTyping recursiveTrace)
  | mdpfail ppAgreement recursiveAgreement =>
      exact matom_matcherDPFail_typed (by assumption) (by assumption) typing
        trace (fun recursiveTyping recursiveTrace =>
          MAtomRuntimeSigAgrees.preserve_with signatureWF evalPristine
            evalPreserve ppmPristine ppmPreserve recursiveAgreement
            environmentPristine valuePristine
            (.inr ⟨_, _, _, rfl, matcherPristine.matcherEnvironment,
              by assumption⟩)
            environmentTyping recursiveTyping recursiveTrace)
  | mmatcher ppAgreement bodyAgreement nextAgreement =>
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          have ppEnvironmentPristine :=
            ppmPristine ppAgreement environmentPristine
          have dataEnvironmentPristine :=
            pdMatch_pristine valuePristine (by assumption)
          have matcherEnvironmentPristine :=
            matcherPristine.matcherEnvironment
          have bodyEnvironmentPristine : EnvPristine _ :=
            (dataEnvironmentPristine.append ppEnvironmentPristine).append
              matcherEnvironmentPristine
          intro substitution substitutionTyping
          exact (matom_matcher_success_typed signatureWF patternTyping
            matcherTyping valueTyping (trace rfl) (by assumption)
            (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) (by assumption) (by assumption)
            (fun admissible =>
              ppmPreserve ppAgreement environmentPristine environmentTyping
                admissible)
            (fun _ bodyEnvironment bodyTyping =>
              evalPreserve bodyAgreement bodyEnvironmentPristine
                bodyEnvironment bodyTyping)
            (fun _ nextEnvironment nextTyping =>
              evalPreserve nextAgreement matcherEnvironmentPristine
                nextEnvironment nextTyping)) substitutionTyping
      | primitive patternTyping primitive matcherTyping valueTyping =>
          have ppEnvironmentPristine :=
            ppmPristine ppAgreement environmentPristine
          have dataEnvironmentPristine :=
            pdMatch_pristine valuePristine (by assumption)
          have matcherEnvironmentPristine :=
            matcherPristine.matcherEnvironment
          have bodyEnvironmentPristine : EnvPristine _ :=
            (dataEnvironmentPristine.append ppEnvironmentPristine).append
              matcherEnvironmentPristine
          intro substitution substitutionTyping
          exact (matom_matcher_success_primitive_typed signatureWF
            patternTyping primitive matcherTyping valueTyping
            (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption) (by assumption) (by assumption)
            (fun admissible =>
              ppmPreserve ppAgreement environmentPristine environmentTyping
                admissible)
            (fun _ bodyEnvironment bodyTyping =>
              evalPreserve bodyAgreement bodyEnvironmentPristine
                bodyEnvironment bodyTyping)
            (fun _ nextEnvironment nextTyping =>
              evalPreserve nextAgreement matcherEnvironmentPristine
                nextEnvironment nextTyping)) substitutionTyping

/-! ## Local readiness for matching-state progress -/

/-
`MAtomReady` is deliberately not a repackaging of `MAtom`: it records no
continuation list and no output substitution.  Its only proof-relevant
runtime data are the local evaluations and matching/decode results needed by
the rule that will be constructed by progress.  In particular, failure
readiness advances to the next private matcher cursor without guessing the
eventual atom result.
-/
inductive MAtomReady (SF : RuntimeSigF) :
    Env → Pattern → Value → Value → Prop where
  | someWC {environment value} :
      MAtomReady SF environment .wild .something value
  | someVar {environment name value} :
      MAtomReady SF environment (.pvar name) .something value
  | someVal {environment expression expected value} :
      Eval SF environment expression expected →
      MAtomReady SF environment (.pval expression) .something value
  | and {environment left right matcher value} :
      MAtomReady SF environment (.pand left right) matcher value
  | or {environment left right matcher value} :
      MAtomReady SF environment (.por left right) matcher value
  | tuple {environment patterns matchers values} :
      MAtomReady SF environment (.ptuple patterns)
        (.tuple matchers) (.tuple values)
  | prodSome {environment pattern matchers value} :
      pattern.isPrimForm = true →
      MAtomReady SF environment pattern (.tuple matchers) value
  | matcherPPFail
      {environment matcherEnvironment original pattern value pp next arms
       clauses} :
      pattern.isMatcherDispatchable = true →
      PPM SF environment pp pattern none →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original clauses) value →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original
          (.mk pp next arms :: clauses)) value
  | matcherDPFail
      {environment matcherEnvironment original pattern value pp next dp body
       arms clauses captures ppEnvironment} :
      pattern.isMatcherDispatchable = true →
      PPM SF environment pp pattern
        (some (captures, ppEnvironment)) →
      pdMatch dp value = none →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original
          (.mk pp next arms :: clauses)) value →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original
          (.mk pp next (.mk dp body :: arms) :: clauses)) value
  | matcher
      {environment matcherEnvironment original pattern value pp next dp body
       arms clauses captures ppEnvironment dataEnvironment decomposition
       tuples valueLists matcherValue matchers} :
      pattern.isMatcherDispatchable = true →
      PPM SF environment pp pattern
        (some (captures, ppEnvironment)) →
      pdMatch dp value = some dataEnvironment →
      Eval SF (dataEnvironment ++ ppEnvironment ++ matcherEnvironment)
        body decomposition →
      listOfV decomposition = some tuples →
      tuples.mapM (decodeTuple captures.length) = some valueLists →
      Eval SF matcherEnvironment next matcherValue →
      decodeTuple captures.length matcherValue = some matchers →
      MAtomReady SF environment pattern
        (.matcherV matcherEnvironment original
          (.mk pp next (.mk dp body :: arms) :: clauses)) value

/-- Local atom readiness constructs an actual atom reduction. -/
theorem MAtomReady.progress
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env} {pattern : Pattern}
    {matcher value : Value}
    (ready : MAtomReady SF environment pattern matcher value) :
    ∀ {context : Context} {parameters : PatternCtx}
      {input output : MonoCtx},
      AtomTy signature context parameters input ⟨pattern, matcher, value⟩
        output →
      ∃ continuations substitution,
        MAtom SF environment pattern matcher value continuations substitution := by
  induction ready with
  | someWC =>
      intro context parameters input output typing
      exact ⟨[[]], [], .someWC⟩
  | someVar =>
      intro context parameters input output typing
      exact ⟨[[]], [(_, _)], .someVar⟩
  | @someVal expression expected value evaluation =>
      intro context parameters input output typing
      cases equality : expected.structEq value with
      | false => exact ⟨[], [], .someValNeq evaluation equality⟩
      | true => exact ⟨[[]], [], .someValEq evaluation equality⟩
  | and =>
      intro context parameters input output typing
      exact ⟨[[⟨_, _, _⟩, ⟨_, _, _⟩]], [], .and⟩
  | or =>
      intro context parameters input output typing
      exact ⟨[[⟨_, _, _⟩], [⟨_, _, _⟩]], [], .or⟩
  | @tuple patterns matchers values =>
      intro context parameters input output typing
      cases typing with
      | mk patternTyping matcherTyping valueTyping =>
          cases patternTyping.terminal with
          | @tuple _ _ _ _ _ duals _ children =>
              have matcherComponents :=
                ValueTy.tupleMatcherUsables matcherTyping
              obtain ⟨actualValues, valueEquality, valueComponents⟩ :=
                ValueTy.product_inversion signatureWF valueTyping
              cases valueEquality
              have patternLength : patterns.length = matchers.length :=
                children.length.trans matcherComponents.length.symm
              have componentLength : values.length = duals.length := by
                simpa only [List.length_map] using valueComponents.length
              have valueLength : matchers.length = values.length :=
                matcherComponents.length.trans componentLength.symm
              exact ⟨[_], [], .tuple patternLength valueLength⟩
      | primitive patternTyping primitive matcherTyping valueTyping =>
          simp [Pattern.isPrimForm] at primitive
  | prodSome primitive =>
      intro context parameters input output typing
      exact ⟨[[⟨_, .something, _⟩]], [], .prodSome primitive⟩
  | matcherPPFail dispatch failure recursive induction =>
      intro context parameters input output typing
      obtain ⟨continuations, substitution, reduction⟩ :=
        induction typing.matcher_nextClause
      exact ⟨continuations, substitution,
        .matcherPPFail dispatch failure reduction⟩
  | matcherDPFail dispatch ppSuccess dataFailure recursive induction =>
      intro context parameters input output typing
      obtain ⟨continuations, substitution, reduction⟩ :=
        induction typing.matcher_nextArm
      exact ⟨continuations, substitution,
        .matcherDPFail dispatch ppSuccess dataFailure reduction⟩
  | matcher dispatch ppSuccess dataSuccess bodyEvaluation listDecode
      tupleDecodes nextEvaluation matcherDecode =>
      intro context parameters input output typing
      exact ⟨_, [], .matcher dispatch ppSuccess dataSuccess bodyEvaluation
        listDecode tupleDecodes nextEvaluation matcherDecode⟩

/-
State readiness contains no `MAtom`, `Step`, successor state, or externally
typed result.  Pattern-function lookup and arity are supplied later by
`RuntimeSigAgrees`; the readiness constructor for that syntax therefore has
no premise.  A nested node either resolves its leading embedded parameter or
recursively readies the exact inner state stepped by `Step.mnodeStep`.
-/
inductive StepReady (SF : RuntimeSigF) : MState → Prop where
  | atom
      {stack environment substitution pattern matcher value} :
      MAtomReady SF (substitution ++ environment) pattern matcher value →
      StepReady SF
        ⟨.atom ⟨pattern, matcher, value⟩ :: stack,
          environment, substitution⟩
  | patfun
      {stack environment substitution name arguments matcher value} :
      StepReady SF
        ⟨.atom ⟨.papp name arguments, matcher, value⟩ :: stack,
          environment, substitution⟩
  | mnodeStep
      {stack environment substitution tree innerStack innerEnvironment
       innerSubstitution parameters} :
      (∀ name matcher value,
        tree = .atom ⟨.embed name, matcher, value⟩ →
        List.find? (fun entry => entry.1 == name) parameters = none) →
      StepReady SF
        ⟨tree :: innerStack, innerEnvironment, innerSubstitution⟩ →
      StepReady SF
        ⟨.mnode (tree :: innerStack) innerEnvironment innerSubstitution
            parameters :: stack,
          environment, substitution⟩
  | mnodeVarpat
      {stack environment substitution name pattern matcher value innerStack
       innerEnvironment innerSubstitution parameters} :
      List.find? (fun entry => entry.1 == name) parameters =
        some (name, pattern) →
      StepReady SF
        ⟨.mnode
            (.atom ⟨.embed name, matcher, value⟩ :: innerStack)
            innerEnvironment innerSubstitution parameters :: stack,
          environment, substitution⟩
  | mnodeDone
      {stack environment substitution innerEnvironment innerSubstitution
       parameters} :
      StepReady SF
        ⟨.mnode [] innerEnvironment innerSubstitution parameters :: stack,
          environment, substitution⟩

/-- The isolated inner state retained by a typed pattern-function node. -/
theorem TreeTy.mnode_inner
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {trees : List Tree} {environment : Env}
    {substitution : MatchSubst} {piE : PiEnv}
    (typing : TreeTy signature context parameters input
      (.mnode trees environment substitution piE) output) :
    ∃ innerParameters innerBindings innerOutput,
      stackNoEmbedInOr trees = true ∧
      EnvTyped signature context environment ∧
      MatchSubstTyped signature innerBindings substitution ∧
      StackTy signature context innerParameters innerBindings trees
        innerOutput := by
  cases typing with
  | mnode suffix namesNodup noEmbed argumentsNoEmbed occurrences actuals
      inParameters environmentTyping substitutionTyping stackTyping =>
      exact ⟨_, _, _, noEmbed, environmentTyping, substitutionTyping,
        stackTyping⟩

/-- Full inversion data for rebuilding an isolated node after one inner
transition. -/
theorem TreeTy.mnode_inversion
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {trees : List Tree} {environment : Env}
    {substitution : MatchSubst} {piE : PiEnv}
    (typing : TreeTy signature context parameters input
      (.mnode trees environment substitution piE) output) :
    ∃ innerParameters innerBindings innerOutput rem duals,
      (∃ index, rem = piE.drop index) ∧
      (piE.map Prod.fst).Nodup ∧
      stackNoEmbedInOr trees = true ∧
      Pattern.noEmbedInOrList (piE.map Prod.snd) = true ∧
      stackEmbedOccs trees = rem.map Prod.fst ∧
      PiEnvTyped signature context parameters input rem duals output ∧
      RemInParameters innerParameters rem duals ∧
      EnvTyped signature context environment ∧
      MatchSubstTyped signature innerBindings substitution ∧
      StackTy signature context innerParameters innerBindings trees
        innerOutput := by
  cases typing with
  | mnode suffix namesNodup noEmbed argumentsNoEmbed occurrences actuals
      inParameters environmentTyping substitutionTyping stackTyping =>
      exact ⟨_, _, _, _, _, suffix, namesNodup, noEmbed,
        argumentsNoEmbed, occurrences, actuals, inParameters,
        environmentTyping, substitutionTyping, stackTyping⟩

/-- The leading unresolved occurrence identifies the exact leading suffix
entry, not merely another equal-named entry in the full parameter list. -/
theorem PiEnv.leading_suffix
    {parameters rem : PiEnv} {name : String} {pattern : Pattern}
    {names : List String}
    (suffix : ∃ index, rem = parameters.drop index)
    (namesNodup : (parameters.map Prod.fst).Nodup)
    (occurrences : name :: names = rem.map Prod.fst)
    (found : List.find? (fun entry => entry.1 == name) parameters =
      some (name, pattern)) :
    ∃ rest, rem = (name, pattern) :: rest ∧
      rest.map Prod.fst = names ∧
      ∃ index, rest = parameters.drop index := by
  obtain ⟨index, rfl⟩ := suffix
  cases dropped : parameters.drop index with
  | nil => simp [dropped] at occurrences
  | cons head rest =>
      obtain ⟨headName, headPattern⟩ := head
      rw [dropped] at occurrences
      have occurrenceParts :
          headName = name ∧ rest.map Prod.fst = names := by
        exact List.cons.inj occurrences.symm
      rcases occurrenceParts with ⟨headNameEquality, restNames⟩
      subst headName
      have headMember : (name, headPattern) ∈ parameters :=
        List.mem_of_mem_drop (by rw [dropped]; exact List.mem_cons_self)
      have headFound := PiEnv.find?_eq_some_of_mem namesNodup headMember
      have patternEquality : headPattern = pattern := by
        have pairEquality : (name, headPattern) = (name, pattern) :=
          Option.some.inj (headFound.symm.trans found)
        exact congrArg Prod.snd pairEquality
      subst headPattern
      refine ⟨rest, rfl, restNames, index + 1, ?_⟩
      have tailDrop :
          List.drop 1 (List.drop index parameters) = rest := by
        rw [dropped]
        rfl
      simpa only [List.drop_drop, Nat.add_comm] using tailDrop.symm

/-! ## Typed reconstruction of the syntax-directed state steps -/

/-- Rebuild the public stack after one typed atom reduction. -/
theorem Step.reduce_preservation
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    {stack : List Tree} {environment : Env} {substitution : MatchSubst}
    {pattern : Pattern} {matcher value : Value}
    {continuations : List (List Atom)} {new : MatchSubst}
    (linear : RuntimePatternLinear SF)
    (reduction : MAtom SF (substitution ++ environment) pattern matcher value
      continuations new)
    (typedOutput :
      ∀ {input output},
        EnvTyped signature (input.toContext ++ context)
          (substitution ++ environment) →
        AtomTy signature context parameters input ⟨pattern, matcher, value⟩
          output →
        MAtomTypedOutput signature context parameters input output
          continuations new)
    (typing : MStateTyAt signature context parameters
      ⟨.atom ⟨pattern, matcher, value⟩ :: stack,
        environment, substitution⟩ goal) :
    ∀ next ∈ continuations.map (fun atoms =>
        ⟨atoms.map Tree.atom ++ stack, environment,
          new ++ substitution⟩),
      MStateTyAt signature context parameters next goal := by
  intro next member
  rcases List.mem_map.mp member with ⟨atoms, atomsMember, rfl⟩
  rcases typing with
    ⟨statePristine, noEmbed, environmentTyping, input,
      substitutionTyping, stackTyping⟩
  cases stackTyping with
  | cons treeTyping tailTyping =>
      cases treeTyping with
      | atom atomTyping =>
          obtain ⟨nextInput, nextSubstitutionTyping, atomsTyping⟩ :=
            typedOutput
              (substitutionTyping.envTyped_append environmentTyping)
              atomTyping substitutionTyping
          refine
            ⟨Step.pristine (.reduce reduction) statePristine _ member,
              Step.noEmbedInOr linear (.reduce reduction) noEmbed _ member,
              environmentTyping, nextInput, nextSubstitutionTyping, ?_⟩
          exact (atomsTyping atoms atomsMember).append tailTyping

/-- Rebuild an isolated node around every typed successor of its exact inner
state. -/
theorem Step.mnodeStep_preservation
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    {stack : List Tree} {environment : Env} {substitution : MatchSubst}
    {tree : Tree} {innerStack : List Tree} {innerEnvironment : Env}
    {innerSubstitution : MatchSubst} {piE : PiEnv}
    {states : List MState}
    (linear : RuntimePatternLinear SF)
    (guard : ∀ name matcher value,
      tree = .atom ⟨.embed name, matcher, value⟩ →
      List.find? (fun entry => entry.1 == name) piE = none)
    (innerReduction : Step SF
      ⟨tree :: innerStack, innerEnvironment, innerSubstitution⟩ states)
    (innerPreservation :
      ∀ {innerParameters : PatternCtx} {innerGoal : MonoCtx},
        MStateTyAt signature context innerParameters
          ⟨tree :: innerStack, innerEnvironment, innerSubstitution⟩
          innerGoal →
        ∀ next ∈ states,
          MStateTyAt signature context innerParameters next innerGoal)
    (typing : MStateTyAt signature context parameters
      ⟨.mnode (tree :: innerStack) innerEnvironment innerSubstitution piE ::
          stack,
        environment, substitution⟩ goal) :
    ∀ next ∈ states.map (fun state =>
        ⟨.mnode state.S innerEnvironment state.θ piE :: stack,
          environment, substitution⟩),
      MStateTyAt signature context parameters next goal := by
  intro next member
  rcases List.mem_map.mp member with ⟨inner, innerMember, rfl⟩
  rcases typing with
    ⟨statePristine, noEmbed, environmentTyping, input,
      substitutionTyping, stackTyping⟩
  rcases statePristine with
    ⟨stackPristine, outerEnvironmentPristine,
      outerSubstitutionPristine⟩
  cases stackPristine with
  | cons nodePristine tailPristine =>
      cases nodePristine with
      | mnode innerStackPristine innerEnvironmentPristine
          innerSubstitutionPristine =>
          cases stackTyping with
          | cons nodeTyping tailTyping =>
              obtain ⟨fixedParameters, innerBindings, innerOutput, rem,
                  duals, suffix, namesNodup, innerNoEmbed,
                  argumentsNoEmbed, occurrences, actuals, inParameters,
                  capturedEnvironmentTyping, innerSubstitutionTyping,
                  innerStackTyping⟩ :=
                nodeTyping.mnode_inversion
              have originalInnerTyping : MStateTyAt signature context
                  fixedParameters
                  ⟨tree :: innerStack, innerEnvironment,
                    innerSubstitution⟩ innerOutput :=
                ⟨⟨innerStackPristine, innerEnvironmentPristine,
                    innerSubstitutionPristine⟩,
                  innerNoEmbed, capturedEnvironmentTyping, innerBindings,
                  innerSubstitutionTyping, innerStackTyping⟩
              obtain ⟨innerPristine, nextInnerNoEmbed,
                  nextInnerEnvironmentTyping, nextInnerInput,
                  nextInnerSubstitutionTyping, nextInnerStackTyping⟩ :=
                innerPreservation originalInnerTyping inner innerMember
              have nextOccurrences :
                  stackEmbedOccs inner.S = rem.map Prod.fst :=
                (Step.embedOccs linear innerReduction innerNoEmbed inner
                  innerMember).trans occurrences
              have nextNodeTyping :=
                TreeTy.mnode suffix namesNodup nextInnerNoEmbed argumentsNoEmbed
                  nextOccurrences actuals inParameters
                  capturedEnvironmentTyping nextInnerSubstitutionTyping
                  nextInnerStackTyping
              refine
                ⟨Step.pristine (.mnodeStep guard innerReduction)
                    ⟨StackPristine.cons
                        (TreePristine.mnode innerStackPristine
                          innerEnvironmentPristine
                          innerSubstitutionPristine)
                        tailPristine,
                      outerEnvironmentPristine,
                      outerSubstitutionPristine⟩ _ member,
                  Step.noEmbedInOr linear (.mnodeStep guard innerReduction)
                    noEmbed _ member,
                  environmentTyping, input, substitutionTyping, ?_⟩
              exact .cons nextNodeTyping tailTyping

/-- Resolving the leading embedded parameter exposes the correspondingly
typed actual pattern and advances the retained actual-argument suffix. -/
theorem Step.mnodeVarpat_preservation
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {outerParameters : PatternCtx} {goal : MonoCtx}
    {stack : List Tree} {environment : Env} {substitution : MatchSubst}
    {name : String} {pattern : Pattern} {matcher value : Value}
    {innerStack : List Tree} {innerEnvironment : Env}
    {innerSubstitution : MatchSubst} {piE : PiEnv}
    (linear : RuntimePatternLinear SF)
    (found : List.find? (fun entry => entry.1 == name) piE =
      some (name, pattern))
    (typing : MStateTyAt signature context outerParameters
      ⟨.mnode (.atom ⟨.embed name, matcher, value⟩ :: innerStack)
          innerEnvironment innerSubstitution piE :: stack,
        environment, substitution⟩ goal) :
    MStateTyAt signature context outerParameters
      ⟨.atom ⟨pattern, matcher, value⟩ ::
          .mnode innerStack innerEnvironment innerSubstitution piE :: stack,
        environment, substitution⟩ goal := by
  rcases typing with
    ⟨statePristine, noEmbed, environmentTyping, input,
      substitutionTyping, stackTyping⟩
  cases stackTyping with
  | cons nodeTyping tailTyping =>
      obtain ⟨fixedParameters, innerBindings, innerOutput, rem, duals,
          suffix, namesNodup, innerNoEmbed, argumentsNoEmbed, occurrences,
          actuals, inParameters, capturedEnvironmentTyping,
          innerSubstitutionTyping, innerStackTyping⟩ :=
        nodeTyping.mnode_inversion
      have leadingOccurrences :
          name :: stackEmbedOccs innerStack = rem.map Prod.fst := by
        simpa only [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars,
          List.singleton_append] using occurrences
      obtain ⟨rest, remEquality, restNames, restSuffix⟩ :=
        PiEnv.leading_suffix suffix namesNodup leadingOccurrences found
      subst rem
      cases duals with
      | nil => simp [RemInParameters] at inParameters
      | cons dual restDuals =>
          change fixedParameters.find? name = some dual ∧
            RemInParameters fixedParameters rest restDuals at inParameters
          rcases inParameters with ⟨fixedFound, restInParameters⟩
          obtain ⟨middle, prevailing, actualHead, actualTail⟩ :=
            actuals.cons_inversion
          cases innerStackTyping with
          | cons embeddedTreeTyping remainingInnerTyping =>
              cases embeddedTreeTyping with
              | atom embeddedAtomTyping =>
                  cases embeddedAtomTyping with
                  | mk embeddedResolution matcherTyping valueTyping =>
                      obtain ⟨embeddedFound, embeddedOutput⟩ :=
                        embeddedResolution.embed_inversion
                      have dualEquality :=
                        Option.some.inj (fixedFound.symm.trans embeddedFound)
                      cases dualEquality
                      have remainingInnerTyping' :
                          StackTy signature context fixedParameters
                            innerBindings innerStack innerOutput := by
                        simpa only [embeddedOutput] using remainingInnerTyping
                      have restNoEmbed :
                          stackNoEmbedInOr innerStack = true := by
                        simpa only [stackNoEmbedInOr, treeNoEmbedInOr,
                          Pattern.noEmbedInOr, Bool.true_and] using innerNoEmbed
                      have residualNodeTyping :=
                        TreeTy.mnode restSuffix namesNodup restNoEmbed
                          argumentsNoEmbed restNames.symm actualTail
                          restInParameters capturedEnvironmentTyping
                          innerSubstitutionTyping remainingInnerTyping'
                      have outputStackTyping :
                          StackTy signature context outerParameters input
                            (.atom ⟨pattern, matcher, value⟩ ::
                              .mnode innerStack innerEnvironment
                                innerSubstitution piE :: stack) goal :=
                        .cons (.atom (.mk actualHead matcherTyping valueTyping))
                          (.cons residualNodeTyping tailTyping)
                      refine
                        ⟨Step.pristine (SF := SF) (.mnodeVarpat found)
                            statePristine _
                            (by simp),
                          Step.noEmbedInOr linear (.mnodeVarpat found) noEmbed _
                            (by simp),
                          environmentTyping, input, substitutionTyping,
                          outputStackTyping⟩
                  | primitive embeddedResolution primitive matcherTyping
                      valueTyping =>
                      simp [Pattern.isPrimForm] at primitive

/-- An exhausted isolated node consumes no remaining actual arguments, so
its outer binding cursor is already the input cursor of the tail stack. -/
theorem Step.mnodeDone_preservation
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    {stack : List Tree} {environment : Env} {substitution : MatchSubst}
    {innerEnvironment : Env} {innerSubstitution : MatchSubst}
    {piE : PiEnv}
    (linear : RuntimePatternLinear SF)
    (typing : MStateTyAt signature context parameters
      ⟨.mnode [] innerEnvironment innerSubstitution piE :: stack,
        environment, substitution⟩ goal) :
    MStateTyAt signature context parameters
      ⟨stack, environment, substitution⟩ goal := by
  rcases typing with
    ⟨statePristine, noEmbed, environmentTyping, input,
      substitutionTyping, stackTyping⟩
  cases stackTyping with
  | cons nodeTyping tailTyping =>
      obtain ⟨fixedParameters, innerBindings, innerOutput, rem, duals,
          suffix, namesNodup, innerNoEmbed, argumentsNoEmbed, occurrences,
          actuals, inParameters, capturedEnvironmentTyping,
          innerSubstitutionTyping, innerStackTyping⟩ :=
        nodeTyping.mnode_inversion
      have mappedNil : rem.map Prod.fst = [] := by
        simpa only [stackEmbedOccs] using occurrences.symm
      have remNil : rem = [] := List.map_eq_nil_iff.mp mappedNil
      subst rem
      cases actuals with
      | nil =>
          refine
            ⟨Step.pristine (SF := SF) (.mnodeDone) statePristine _ (by simp),
              Step.noEmbedInOr linear (.mnodeDone) noEmbed _ (by simp),
              environmentTyping, input, substitutionTyping, tailTyping⟩

/-! ## Combined preservation -/

/-- Equal-arity pointwise typing builds the replicated target list used by
the concrete list encoding. -/
private theorem ValueTys.replicate_of_zip
    {signature : FrozenSig} {target : Ty} :
    ∀ {inputs : List α} {values : List Value},
      inputs.length = values.length →
      (∀ pair ∈ inputs.zip values, ValueTy signature pair.2 target) →
      ValueTys signature values (List.replicate values.length target)
  | [], [], _, _ => .nil
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | input :: inputs, value :: values, lengths, pointwise => by
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simpa [List.replicate_succ] using
        ValueTys.cons
          (pointwise (input, value) (by simp))
          (ValueTys.replicate_of_zip lengths
            (fun pair member => pointwise pair (by simp [member])))

/-- The one reconstruction callback whose source proof crosses the
pattern-function definition boundary.  The concrete callback below is
discharged by `PatternDefTy.instantiatedBody`; it is kept private so no
operational oracle reaches the public theorem. -/
private def PatfunPreservationKernel
    (signature : FrozenSig) (SF : RuntimeSigF) : Prop :=
  ∀ {stack : List Tree} {environment : Env} {substitution : MatchSubst}
      {name : String} {arguments : List Pattern} {matcher value : Value}
      {runtime : PatFunRuntimeSig}
      {_found : List.find? (fun entry => entry.1 == name) SF =
        some (name, runtime)}
      {_length : runtime.params.length = arguments.length}
      {context : Context} {parameters : PatternCtx} {goal : MonoCtx},
    RuntimeSigAgrees signature context SF →
    MStateTyAt signature context parameters
      ⟨.atom ⟨.papp name arguments, matcher, value⟩ :: stack,
        environment, substitution⟩ goal →
    MStateTyAt signature context parameters
      ⟨.mnode [.atom ⟨runtime.body, matcher, value⟩]
          environment [] (runtime.params.zip arguments) :: stack,
        environment, substitution⟩ goal

/-- Reconstruct the isolated node introduced by `Step.patfunEnter` from the
checked source definition and its concrete value-flow instance. -/
private theorem PatfunPreservationKernel.of_instantiatedBody
    {signature : FrozenSig} {SF : RuntimeSigF}
    (instantiate :
      ∀ {context : Context} {definition : PatternDef} {scheme : DualScheme}
        (typing : PatternDefTy signature context definition scheme),
        typing.InstantiatedBody) :
    PatfunPreservationKernel signature SF := by
  intro stack environment substitution name arguments matcher value runtime
    found length context parameters goal agreement stateTyping
  rcases stateTyping with
    ⟨statePristine, noEmbed, environmentTyping, input,
      substitutionTyping, stackTyping⟩
  rcases statePristine with
    ⟨stackPristine, environmentPristine, substitutionPristine⟩
  cases stackPristine with
  | cons headPristine tailPristine =>
      cases headPristine with
      | atom atomPristine =>
          cases stackTyping with
          | cons headTyping tailTyping =>
              cases headTyping with
              | atom atomTyping =>
                  cases atomTyping with
                  | mk patternTyping matcherTyping valueTyping =>
                      cases patternTyping.terminal with
                      | @app _ _ _ _ _ scheme _ duals _ result sourceLookup
                          children instanceTyping =>
                          obtain ⟨definition, nameEquality, runtimeFound,
                              definitionTyping⟩ :=
                            agreement.sourceLookup sourceLookup
                          have runtimeEquality : runtime = definition.runtime :=
                            congrArg Prod.snd
                              (Option.some.inj (found.symm.trans runtimeFound))
                          subst runtime
                          obtain ⟨bodyPrevailing, bodyOutput, bodyTyping⟩ :=
                            instantiate definitionTyping instanceTyping
                          obtain ⟨bodyLinear, namesNodup⟩ :=
                            agreement.runtimePatternLinear runtimeFound
                          have bodyLinear' :
                              definition.body.linearEmbeds =
                                some definition.parameterNames := by
                            simpa [PatternDef.runtime] using bodyLinear
                          have namesNodup' :
                              definition.parameterNames.Nodup := by
                            simpa [PatternDef.runtime] using namesNodup
                          have argumentLength :
                              definition.parameterNames.length =
                                arguments.length := by
                            simpa [PatternDef.runtime] using length
                          have dualLength :
                              definition.parameterNames.length = duals.length :=
                            definitionTyping.actual_arity instanceTyping
                          have actualsTyping :
                              PiEnvTyped signature context parameters input
                                (definition.parameterNames.zip arguments)
                                duals _ :=
                            children.piEnvTyped argumentLength
                          have remainingInParameters :
                              RemInParameters
                                (definition.parameterNames.zip duals)
                                (definition.parameterNames.zip arguments)
                                duals :=
                            RemInParameters.aligned_zip namesNodup'
                              argumentLength dualLength
                          have bodyNoEmbed :
                              Pattern.noEmbedInOr definition.body = true :=
                            Pattern.noEmbedInOr_of_linearEmbeds definition.body
                              bodyLinear'
                          have argumentsNoEmbed :
                              Pattern.noEmbedInOrList arguments = true := by
                            have parts :
                                treeNoEmbedInOr
                                    (.atom ⟨.papp name arguments, matcher,
                                      value⟩) = true ∧
                                  stackNoEmbedInOr stack = true := by
                              simpa only [stackNoEmbedInOr,
                                Bool.and_eq_true] using noEmbed
                            simpa only [treeNoEmbedInOr,
                              Pattern.noEmbedInOr] using parts.1
                          have tailNoEmbed :
                              stackNoEmbedInOr stack = true := by
                            have parts :
                                treeNoEmbedInOr
                                    (.atom ⟨.papp name arguments, matcher,
                                      value⟩) = true ∧
                                  stackNoEmbedInOr stack = true := by
                              simpa only [stackNoEmbedInOr,
                                Bool.and_eq_true] using noEmbed
                            exact parts.2
                          have bodyOccurrences :
                              stackEmbedOccs
                                  [.atom ⟨definition.body, matcher, value⟩] =
                                (definition.parameterNames.zip arguments).map
                                  Prod.fst := by
                            simp only [stackEmbedOccs, treeEmbedOccs]
                            rw [Pattern.embedVars_eq_of_linearEmbeds
                              definition.body bodyLinear']
                            simpa using
                              (List.map_fst_zip
                                (Nat.le_of_eq argumentLength)).symm
                          have piNamesNodup :
                              ((definition.parameterNames.zip arguments).map
                                Prod.fst).Nodup := by
                            rw [List.map_fst_zip
                              (Nat.le_of_eq argumentLength)]
                            exact namesNodup'
                          have piArgumentsNoEmbed :
                              Pattern.noEmbedInOrList
                                  ((definition.parameterNames.zip arguments).map
                                    Prod.snd) = true := by
                            rw [map_snd_zip_eq_right argumentLength]
                            exact argumentsNoEmbed
                          have innerStackTyping :
                              StackTy signature context
                                (definition.parameterNames.zip duals) []
                                [.atom ⟨definition.body, matcher, value⟩]
                                bodyOutput :=
                            .cons (.atom (.mk bodyTyping matcherTyping valueTyping))
                              .nil
                          have nodeTyping :
                              TreeTy signature context parameters input
                                (.mnode
                                  [.atom ⟨definition.body, matcher, value⟩]
                                  environment []
                                  (definition.parameterNames.zip arguments))
                                _ :=
                            .mnode ⟨0, by simp⟩ piNamesNodup
                              (by simpa [stackNoEmbedInOr, treeNoEmbedInOr]
                                using bodyNoEmbed)
                              piArgumentsNoEmbed bodyOccurrences actualsTyping
                              remainingInParameters environmentTyping
                              (matchSubstTyped_nil signature) innerStackTyping
                          have successorPristine : MStatePristine
                              ⟨.mnode
                                  [.atom ⟨definition.body, matcher, value⟩]
                                  environment []
                                  (definition.parameterNames.zip arguments) ::
                                    stack,
                                environment, substitution⟩ :=
                            ⟨StackPristine.cons
                                (.mnode
                                  (.cons (.atom atomPristine) .nil)
                                  environmentPristine .nil)
                                tailPristine,
                              environmentPristine, substitutionPristine⟩
                          have piPatterns :
                              (definition.parameterNames.zip arguments).map
                                  Prod.snd = arguments :=
                            map_snd_zip_eq_right argumentLength
                          have successorNoEmbed :
                              stackNoEmbedInOr
                                (.mnode
                                    [.atom
                                      ⟨definition.body, matcher, value⟩]
                                    environment []
                                    (definition.parameterNames.zip arguments) ::
                                  stack) = true := by
                            simp [stackNoEmbedInOr, treeNoEmbedInOr,
                              bodyNoEmbed, piPatterns, argumentsNoEmbed,
                              tailNoEmbed]
                          exact ⟨successorPristine, successorNoEmbed,
                            environmentTyping, input, substitutionTyping,
                            .cons nodeTyping tailTyping⟩
                  | primitive patternTyping primitive matcherTyping valueTyping =>
                      simp [Pattern.isPrimForm] at primitive

/-- The concrete source theorem packaged at the operational callback type. -/
private theorem PatfunPreservationKernel.of_source
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} :
    PatfunPreservationKernel signature SF := by
  intro stack environment substitution name arguments matcher value runtime
    found length context parameters goal runtimeAgreement stateTyping
  exact PatfunPreservationKernel.of_instantiatedBody
    (fun typing => typing.instantiatedBody
      signatureWF.armExhaustiveBasic signatureWF.patternFunNamesNodup)
    (_found := found) (_length := length) runtimeAgreement stateTyping

/-- The five derivation-local agreement judgments are eliminated together.
The result rooted at `Eval` carries both the pristine runtime fact needed by
nested `matchAll` and concrete type preservation. -/
private theorem EvalRuntimeSigAgrees.preserve_with
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    (generalizedValueFlow :
      ∀ {context : Context} {expression : Expr} {source : Ty}
        (typing : HasTy signature context expression source),
        typing.GeneralizedValueFlow)
    (patfunPreserve : PatfunPreservationKernel signature SF)
    {environment : Env} {expression : Expr} {value : Value}
    {evaluation : Eval SF environment expression value}
    (agreement : EvalRuntimeSigAgrees signature SF evaluation) :
    (EnvPristine environment → ValuePristine value) ∧
    (∀ {context : Context} {target : Ty},
      EnvPristine environment →
      EnvTyped signature context environment →
      HasTy signature context expression target →
      ValueTy signature value target) := by
  refine EvalRuntimeSigAgrees.rec
    (motive_1 := fun {runtimeEnvironment} {sourceExpression} {result} _ _ =>
      (EnvPristine runtimeEnvironment → ValuePristine result) ∧
      (∀ {sourceContext : Context} {sourceTarget : Ty},
        EnvPristine runtimeEnvironment →
        EnvTyped signature sourceContext runtimeEnvironment →
        HasTy signature sourceContext sourceExpression sourceTarget →
        ValueTy signature result sourceTarget))
    (motive_2 := fun {runtimeEnvironment} {primitivePattern} {userPattern}
        {runtimeResult} _ _ =>
      (EnvPristine runtimeEnvironment → PPMOutputPristine runtimeResult) ∧
      (∀ {actualCaptures : List Pattern} {actualEnvironment : Env},
        runtimeResult = some (actualCaptures, actualEnvironment) →
        ∀ {sourceContext : Context} {sourceInput : MonoCtx}
          {sourceTarget : Ty} {sourceBindings : MonoCtx},
          EnvPristine runtimeEnvironment →
          EnvTyped signature (sourceInput.toContext ++ sourceContext)
            runtimeEnvironment →
          CaptureAdm signature sourceContext sourceInput primitivePattern
            userPattern sourceTarget sourceBindings →
          MonoEnvTys signature sourceBindings actualEnvironment))
    (motive_3 := fun {runtimeEnvironment} {userPattern} {runtimeMatcher}
        {runtimeValue} {continuations} {newSubstitution} _ _ =>
      ∀ {sourceContext : Context} {sourceParameters : PatternCtx}
        {sourceInput sourceOutput : MonoCtx},
        EnvPristine runtimeEnvironment →
        ValuePristine runtimeValue →
        MAtomInputPristine userPattern runtimeMatcher →
        EnvTyped signature (sourceInput.toContext ++ sourceContext)
          runtimeEnvironment →
        AtomTy signature sourceContext sourceParameters sourceInput
          ⟨userPattern, runtimeMatcher, runtimeValue⟩ sourceOutput →
        MAtomDispatchTrace SF runtimeEnvironment userPattern runtimeValue
          runtimeMatcher →
        MAtomTypedOutput signature sourceContext sourceParameters sourceInput
          sourceOutput continuations newSubstitution)
    (motive_4 := fun {state} {states} _ _ =>
      ∀ {sourceContext : Context} {sourceParameters : PatternCtx}
        {goal : MonoCtx},
        RuntimeSigAgrees signature sourceContext SF →
        MStateTyAt signature sourceContext sourceParameters state goal →
        ∀ next ∈ states,
          MStateTyAt signature sourceContext sourceParameters next goal)
    (motive_5 := fun {state} {substitutions} _ _ =>
      (MStatePristine state → SearchOutputPristine substitutions) ∧
      (∀ {sourceContext : Context} {sourceParameters : PatternCtx}
          {goal : MonoCtx},
        RuntimeSigAgrees signature sourceContext SF →
        MStateTyAt signature sourceContext sourceParameters state goal →
        ∀ substitution ∈ substitutions,
          MatchSubstTyped signature goal substitution))
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep agreement
  case evar =>
    intro runtimeEnvironment name result found
    constructor
    · intro runtimePristine
      exact runtimePristine.lookup found
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | var sourceFound instantiation =>
              exact terminalEnvironment.lookup found sourceFound instantiation)
  case elam =>
    intro runtimeEnvironment parameter body
    constructor
    · exact fun runtimePristine => .closure runtimePristine
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | lam bodyTyping =>
              exact ValueTy.closure terminalContext
                (fun name value found => terminalEnvironment.domain found)
                (fun name value scheme actual found sourceFound instantiation =>
                  terminalEnvironment.lookup found sourceFound instantiation)
                (fun _ => bodyTyping)
                (fun _ equality => nomatch equality))
  case efix =>
    intro runtimeEnvironment self parameter body
    constructor
    · exact fun runtimePristine => .closure runtimePristine
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | fixE bodyTyping =>
              exact ValueTy.closure terminalContext
                (fun name value found => terminalEnvironment.domain found)
                (fun name value scheme actual found sourceFound instantiation =>
                  terminalEnvironment.lookup found sourceFound instantiation)
                (fun equality => nomatch equality)
                (fun requested equality => by cases equality; exact bodyTyping))
  case eapp =>
    intro runtimeEnvironment function argument self closureEnvironment parameter
      body argumentValue result functionEvaluation argumentEvaluation
      bodyEvaluation functionAgreement argumentAgreement bodyAgreement
      functionIH argumentIH bodyIH
    constructor
    · intro runtimePristine
      have functionPristine := functionIH.1 runtimePristine
      have argumentPristine := argumentIH.1 runtimePristine
      cases functionPristine with
      | closure capturedPristine =>
          exact bodyIH.1 (pushArg_pristine capturedPristine argumentPristine)
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | app functionTyping argumentTyping =>
              have functionValueTyping := functionIH.2 runtimePristine
                terminalEnvironment functionTyping
              have argumentValueTyping := argumentIH.2 runtimePristine
                terminalEnvironment argumentTyping
              obtain ⟨bodyContext, bodyEnvironmentTyping, bodyTyping⟩ :=
                pushArg_typed functionValueTyping argumentValueTyping
              have functionPristine := functionIH.1 runtimePristine
              have argumentPristine := argumentIH.1 runtimePristine
              cases functionPristine with
              | closure capturedPristine =>
                  exact bodyIH.2
                    (pushArg_pristine capturedPristine argumentPristine)
                    bodyEnvironmentTyping bodyTyping)
  case elit =>
    intro runtimeEnvironment literal
    constructor
    · exact fun _ => .lit
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun terminalTyping terminalEvidence _ => by
          cases terminalEvidence
          exact ValueTy.lit)
  case etuple =>
    intro runtimeEnvironment expressions values lengths evaluations
      childrenAgreements childrenIH
    constructor
    · intro runtimePristine
      exact .tuple (valuesPristine_of_zip lengths (fun pair member =>
        (childrenIH pair member).1 runtimePristine))
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | tuple expressionsTyping =>
              exact ValueTy.tuple
                (valueTys_of_evalZip expressionsTyping lengths
                  (fun pair member actual actualTyping =>
                    (childrenIH pair member).2 runtimePristine
                      terminalEnvironment actualTyping))
          | coerceTupleMatcher expressionsTyping =>
              exact ValueTy.matcherProduct
                (valueTys_of_evalZip expressionsTyping lengths
                  (fun pair member actual actualTyping =>
                    (childrenIH pair member).2 runtimePristine
                      terminalEnvironment actualTyping)))
  case ector =>
    intro ignoredName runtimeEnvironment name expressions values lengths evaluations
      childrenAgreements childrenIH
    constructor
    · intro runtimePristine
      exact .ctor (valuesPristine_of_zip lengths (fun pair member =>
        (childrenIH pair member).1 runtimePristine))
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | ctor sourceFound instantiation expressionsTyping =>
              exact ValueTy.ctor sourceFound instantiation
                (valueTys_of_evalZip expressionsTyping lengths
                  (fun pair member actual actualTyping =>
                    (childrenIH pair member).2 runtimePristine
                      terminalEnvironment actualTyping)))
  case eprim =>
    intro runtimeEnvironment operation expressions values result lengths
      evaluations primitive childrenAgreements childrenIH
    constructor
    · intro runtimePristine
      exact primEval_pristine
        (valuesPristine_of_zip lengths (fun pair member =>
          (childrenIH pair member).1 runtimePristine)) primitive
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | prim sourceFound instantiation expressionsTyping =>
              exact signatureWF.primEvalTyped sourceFound instantiation
                (valueTys_of_evalZip expressionsTyping lengths
                  (fun pair member actual actualTyping =>
                    (childrenIH pair member).2 runtimePristine
                      terminalEnvironment actualTyping)) primitive)
  case elet =>
    intro runtimeEnvironment name bound body boundValue result boundEvaluation
      bodyEvaluation boundAgreement bodyAgreement boundIH bodyIH
    constructor
    · intro runtimePristine
      exact bodyIH.1 (.cons (boundIH.1 runtimePristine) runtimePristine)
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | letE boundTyping bodyTyping =>
              have boundValueTyping := boundIH.2 runtimePristine
                terminalEnvironment boundTyping
              have extendedEnvironmentTyping :=
                EnvTyped.consScheme
                  (name := name) (value := boundValue)
                  (scheme := signature.generalize terminalContext _)
                  (fun actual instantiation =>
                    boundIH.2 runtimePristine terminalEnvironment
                      (generalizedValueFlow boundTyping instantiation))
                  terminalEnvironment
              exact bodyIH.2 (.cons (boundIH.1 runtimePristine) runtimePristine)
                extendedEnvironmentTyping bodyTyping)
  case esomething =>
    intro runtimeEnvironment
    constructor
    · exact fun _ => .something
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun terminalTyping terminalEvidence _ => by
          cases terminalEvidence
          exact ValueTy.something)
  case ematcher =>
    intro runtimeEnvironment clauses
    constructor
    · exact fun runtimePristine => .matcherLiteral runtimePristine
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext} {terminalTarget} terminalTyping terminalEvidence
            terminalEnvironment => by
          cases terminalEvidence with
          | matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
              coverage =>
              exact ValueTy.matcherLiteral terminalContext
                (fun name value found => terminalEnvironment.domain found)
                (fun name value scheme actual found sourceFound instantiation =>
                  terminalEnvironment.lookup found sourceFound instantiation)
                (HasTy.matcher clausesTyping shape catchAll exhaustive ppNodup
                  armNodup coverage) MatcherCursor.refl)
  case ematchAll =>
    intro runtimeEnvironment targetExpression matcherExpression body pattern
      targetValue matcherValue substitutions values targetEvaluation
      matcherEvaluation search lengths evaluations localAgreement
      targetAgreement matcherAgreement searchAgreement childrenAgreements
      targetIH matcherIH searchIH childrenIH
    constructor
    · intro runtimePristine
      have targetPristine := targetIH.1 runtimePristine
      have matcherPristine := matcherIH.1 runtimePristine
      have initialPristine : MStatePristine
          ⟨[.atom ⟨pattern, matcherValue, targetValue⟩], runtimeEnvironment,
            []⟩ :=
        ⟨.cons (.atom ⟨matcherPristine, targetPristine⟩) .nil,
          runtimePristine, .nil⟩
      have substitutionsPristine := searchIH.1 initialPristine
      exact mkListV_pristine
        (valuesPristine_of_zip lengths (fun pair member =>
          (childrenIH pair member).1
            ((substitutionsPristine pair.1
              (List.fst_mem_of_mem_zip member)).append runtimePristine)))
    · intro sourceContext sourceTarget runtimePristine runtimeTyping typing
      exact preserveSourceCoercions signatureWF typing runtimeTyping
        (fun {terminalContext : Context} {terminalTarget : Ty}
            (terminalTyping : HasTy signature terminalContext
              (.matchAll targetExpression matcherExpression pattern body)
              terminalTarget)
            (terminalEvidence : HasTy.Terminal terminalTyping)
            (terminalEnvironment :
              EnvTyped signature terminalContext runtimeEnvironment) => by
          cases terminalEvidence with
          | @matchAll _ terminalContext _ _ _ _ _ bodyTarget _ _
              targetTyping patternTyping matcherTyping bodyTyping =>
              have targetValueTyping := targetIH.2 runtimePristine
                terminalEnvironment targetTyping
              have matcherValueTyping := matcherIH.2 runtimePristine
                terminalEnvironment matcherTyping
              have targetPristine := targetIH.1 runtimePristine
              have matcherPristine := matcherIH.1 runtimePristine
              have initialPristine : MStatePristine
                  ⟨[.atom ⟨pattern, matcherValue, targetValue⟩],
                    runtimeEnvironment, []⟩ :=
                ⟨.cons (.atom ⟨matcherPristine, targetPristine⟩) .nil,
                  runtimePristine, .nil⟩
              have initialNoEmbed :
                  stackNoEmbedInOr
                    [.atom ⟨pattern, matcherValue, targetValue⟩] = true := by
                simpa [stackNoEmbedInOr, treeNoEmbedInOr] using
                  patternTyping.noEmbedInOr_of_parameters_nil
              have emptySubstitution : MatchSubstTyped signature [] [] :=
                ⟨List.nodup_nil, rfl, fun entry member => by contradiction⟩
              have initialTyping : MStateTyAt signature terminalContext []
                  ⟨[.atom ⟨pattern, matcherValue, targetValue⟩],
                    runtimeEnvironment, []⟩ _ :=
                ⟨initialPristine, initialNoEmbed, terminalEnvironment, [],
                  emptySubstitution,
                  .cons (.atom (.mk patternTyping (.inr matcherValueTyping)
                    targetValueTyping)) .nil⟩
              have runtimeAgreement :=
                localAgreement terminalEnvironment
                  (.matchAll targetTyping patternTyping matcherTyping bodyTyping)
              have substitutionsTyped := searchIH.2 runtimeAgreement
                initialTyping
              exact mkListV_typed signatureWF (target := bodyTarget)
                (ValueTys.replicate_of_zip lengths
                  (fun pair member =>
                    show ValueTy signature pair.2 bodyTarget from
                    (childrenIH pair member).2
                      ((searchIH.1 initialPristine pair.1
                        (List.fst_mem_of_mem_zip member)).append runtimePristine)
                      ((substitutionsTyped pair.1
                        (List.fst_mem_of_mem_zip member)).envTyped_append
                        terminalEnvironment)
                      bodyTyping)))
  case phole =>
    intro runtimeEnvironment userPattern
    constructor
    · exact fun _ => .nil
    · intro actualCaptures actualEnvironment equality sourceContext sourceInput
        sourceTarget sourceBindings runtimePristine runtimeTyping captureTyping
      cases equality
      cases captureTyping
      exact .nil
  case pwild =>
    intro runtimeEnvironment
    constructor
    · exact fun _ => .nil
    · intro actualCaptures actualEnvironment equality sourceContext sourceInput
        sourceTarget sourceBindings runtimePristine runtimeTyping captureTyping
      cases equality
      cases captureTyping
      exact .nil
  case ppval =>
    intro runtimeEnvironment name expression evaluated evaluation
      evaluationAgreement evaluationIH
    constructor
    · intro runtimePristine
      exact .cons (evaluationIH.1 runtimePristine) .nil
    · intro actualCaptures actualEnvironment equality sourceContext sourceInput
        sourceTarget sourceBindings runtimePristine runtimeTyping captureTyping
      cases equality
      cases captureTyping with
      | pval expressionTyping =>
          exact .cons
            (evaluationIH.2 runtimePristine runtimeTyping expressionTyping)
            .nil
  case pctor =>
    intro ignoredName runtimeEnvironment name pps patterns results patternLength
      resultLength matchings childrenAgreements childrenIH
    constructor
    · intro runtimePristine
      apply EnvPristine.flatten_map_snd
      intro result member
      obtain ⟨input, inputMember⟩ :=
        List.exists_fst_mem_zip_of_snd_mem resultLength member
      exact (childrenIH (input, result) inputMember).1 runtimePristine
    · intro actualCaptures actualEnvironment equality sourceContext sourceInput
        sourceTarget sourceBindings runtimePristine runtimeTyping captureTyping
      cases equality
      cases captureTyping with
      | ctor found children instantiation =>
          exact children.ppm_environments_typed (_SF := SF)
            (_environment := runtimeEnvironment) patternLength resultLength
            (fun entry member {target} {entryBindings} entryAdmissible =>
              (childrenIH entry member).2 rfl runtimePristine runtimeTyping
                entryAdmissible)
  case ptuple =>
    intro runtimeEnvironment pps patterns results patternLength resultLength
      matchings childrenAgreements childrenIH
    constructor
    · intro runtimePristine
      apply EnvPristine.flatten_map_snd
      intro result member
      obtain ⟨input, inputMember⟩ :=
        List.exists_fst_mem_zip_of_snd_mem resultLength member
      exact (childrenIH (input, result) inputMember).1 runtimePristine
    · intro actualCaptures actualEnvironment equality sourceContext sourceInput
        sourceTarget sourceBindings runtimePristine runtimeTyping captureTyping
      cases equality
      cases captureTyping with
      | tuple children =>
          exact children.ppm_environments_typed (_SF := SF)
            (_environment := runtimeEnvironment) patternLength resultLength
            (fun entry member {target} {entryBindings} entryAdmissible =>
              (childrenIH entry member).2 rfl runtimePristine runtimeTyping
                entryAdmissible)
  case pfail =>
    intro runtimeEnvironment pp userPattern failed
    constructor
    · intro runtimePristine
      trivial
    · intro actualCaptures actualEnvironment equality
      contradiction
  case msomeWC =>
    intro runtimeEnvironment runtimeValue sourceContext sourceParameters
      sourceInput sourceOutput runtimePristine valuePristine matcherPristine
      runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_someWC_typed patternTyping valueTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        exact matom_someWC_typed patternTyping valueTyping
  case msomeVar =>
    intro runtimeEnvironment name runtimeValue sourceContext sourceParameters
      sourceInput sourceOutput runtimePristine valuePristine matcherPristine
      runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_someVar_typed patternTyping valueTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        exact matom_someVar_typed patternTyping valueTyping
  case msomeValEq =>
    intro runtimeEnvironment compared value expected evaluation equal
      evaluationAgreement evaluationIH sourceContext sourceParameters
      sourceInput sourceOutput runtimePristine valuePristine matcherPristine
      runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_someValEq_typed patternTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        exact matom_someValEq_typed patternTyping
  case msomeValNeq =>
    intro runtimeEnvironment compared value expected evaluation unequal
      evaluationAgreement evaluationIH sourceContext sourceParameters
      sourceInput sourceOutput runtimePristine valuePristine matcherPristine
      runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_someValNeq_typed patternTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        exact matom_someValNeq_typed patternTyping
  case mand =>
    intro runtimeEnvironment left right runtimeMatcher runtimeValue sourceContext
      sourceParameters sourceInput sourceOutput runtimePristine valuePristine
      matcherPristine runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_and_typed patternTyping matcherTyping valueTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        simp [Pattern.isPrimForm] at primitive
  case mor =>
    intro runtimeEnvironment left right runtimeMatcher runtimeValue sourceContext
      sourceParameters sourceInput sourceOutput runtimePristine valuePristine
      matcherPristine runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_or_typed patternTyping matcherTyping valueTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        simp [Pattern.isPrimForm] at primitive
  case mtuple =>
    intro ignored runtimeEnvironment patterns matchers values patternLength valueLength
      sourceContext sourceParameters sourceInput sourceOutput runtimePristine
      valuePristine matcherPristine runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_tuple_typed signatureWF patternTyping matcherTyping
          valueTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        simp [Pattern.isPrimForm] at primitive
  case mprodSome =>
    intro ignored1 ignored2 ignored3 runtimeEnvironment userPattern matchers runtimeValue primitive
      sourceContext sourceParameters sourceInput sourceOutput runtimePristine
      valuePristine matcherPristine runtimeTyping atomTyping trace
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact matom_prodSome_typed patternTyping primitive valueTyping
    | primitive patternTyping primitive' matcherTyping valueTyping =>
        exact matom_prodSome_typed patternTyping primitive' valueTyping
  case mppfail =>
    intro ignored1 ignored2 runtimeEnvironment matcherEnvironment original userPattern runtimeValue
      pp next arms clauses continuations new dispatch failure recursive
      failureAgreement recursiveAgreement failureIH recursiveIH sourceContext
      sourceParameters sourceInput sourceOutput runtimePristine valuePristine
      matcherPristine runtimeTyping atomTyping trace
    exact matom_matcherPPFail_typed failure atomTyping trace
      (fun recursiveTyping recursiveTrace =>
        recursiveIH runtimePristine valuePristine
          (.inr ⟨_, _, _, rfl, matcherPristine.matcherEnvironment, dispatch⟩)
          runtimeTyping recursiveTyping recursiveTrace)
  case mdpfail =>
    intro ignored runtimeEnvironment matcherEnvironment original userPattern runtimeValue
      pp next dp body arms clauses captures ppEnvironment continuations new
      dispatch ppSuccess dataFailure recursive ppAgreement recursiveAgreement
      ppIH recursiveIH sourceContext sourceParameters sourceInput sourceOutput
      runtimePristine valuePristine matcherPristine runtimeTyping atomTyping
      trace
    exact matom_matcherDPFail_typed ppSuccess dataFailure atomTyping trace
      (fun recursiveTyping recursiveTrace =>
        recursiveIH runtimePristine valuePristine
          (.inr ⟨_, _, _, rfl, matcherPristine.matcherEnvironment, dispatch⟩)
          runtimeTyping recursiveTyping recursiveTrace)
  case mmatcher =>
    intro ignored1 ignored2 ignored3 runtimeEnvironment matcherEnvironment original userPattern runtimeValue
      pp next dp body arms clauses captures ppEnvironment dataEnvironment
      decomposition tuples valueLists matcherValue matchers dispatch ppSuccess
      dataSuccess bodyEvaluation listDecode tupleDecodes nextEvaluation
      matcherDecode ppAgreement bodyAgreement nextAgreement ppIH bodyIH nextIH
      sourceContext sourceParameters sourceInput sourceOutput runtimePristine
      valuePristine matcherPristine runtimeTyping atomTyping trace
    have ppEnvironmentPristine := ppIH.1 runtimePristine
    have dataEnvironmentPristine :=
      pdMatch_pristine valuePristine dataSuccess
    have matcherEnvironmentPristine := matcherPristine.matcherEnvironment
    have bodyEnvironmentPristine : EnvPristine _ :=
      (dataEnvironmentPristine.append ppEnvironmentPristine).append
        matcherEnvironmentPristine
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        intro substitution substitutionTyping
        exact (matom_matcher_success_typed signatureWF patternTyping
          matcherTyping valueTyping (trace rfl) dispatch ppSuccess dataSuccess
          bodyEvaluation listDecode tupleDecodes nextEvaluation matcherDecode
          (fun admissible =>
            ppIH.2 rfl runtimePristine runtimeTyping admissible)
          (fun _ bodyEnvironment bodyTyping =>
            bodyIH.2 bodyEnvironmentPristine bodyEnvironment bodyTyping)
          (fun _ nextEnvironment nextTyping =>
            nextIH.2 matcherEnvironmentPristine nextEnvironment nextTyping))
          substitutionTyping
    | primitive patternTyping primitive matcherTyping valueTyping =>
        intro substitution substitutionTyping
        exact (matom_matcher_success_primitive_typed signatureWF
          patternTyping primitive matcherTyping valueTyping ppSuccess
          dataSuccess bodyEvaluation listDecode tupleDecodes nextEvaluation
          matcherDecode
          (fun admissible =>
            ppIH.2 rfl runtimePristine runtimeTyping admissible)
          (fun _ bodyEnvironment bodyTyping =>
            bodyIH.2 bodyEnvironmentPristine bodyEnvironment bodyTyping)
          (fun _ nextEnvironment nextTyping =>
            nextIH.2 matcherEnvironmentPristine nextEnvironment nextTyping))
          substitutionTyping
  case sreduce =>
    intro ignored stack runtimeEnvironment substitution userPattern runtimeMatcher
      runtimeValue continuations new atomReduction atomAgreement atomIH
      sourceContext sourceParameters goal runtimeAgreement stateTyping next member
    rcases stateTyping.1 with
      ⟨stackPristine, environmentPristine, substitutionPristine⟩
    cases stackPristine with
    | cons headPristine tailPristine =>
        cases headPristine with
        | atom atomPristine =>
            have combinedPristine :=
              substitutionPristine.append environmentPristine
            rcases atomPristine with ⟨matcherPristine, valuePristine⟩
            have typedOutput :
                ∀ {input output},
                  EnvTyped signature (input.toContext ++ sourceContext)
                    (substitution ++ runtimeEnvironment) →
                  AtomTy signature sourceContext sourceParameters input
                    ⟨userPattern, runtimeMatcher, runtimeValue⟩ output →
                  MAtomTypedOutput signature sourceContext sourceParameters
                    input output continuations new := by
              intro input output combinedTyping atomTyping
              exact atomIH combinedPristine valuePristine
                (.inl matcherPristine) combinedTyping atomTyping
                (MAtomDispatchTrace.pristine matcherPristine)
            exact Step.reduce_preservation
              runtimeAgreement.runtimePatternLinear atomReduction typedOutput
              stateTyping next member
  case spatfunEnter =>
    intro ignored1 ignored2 ignored3 ignored4 ignored5 stack runtimeEnvironment substitution name arguments runtimeMatcher
      runtimeValue runtime found length sourceContext sourceParameters goal
      runtimeAgreement stateTyping next member
    simp only [List.mem_singleton] at member
    subst next
    exact patfunPreserve (_found := found) (_length := length)
      runtimeAgreement stateTyping
  case smnodeStep =>
    intro ignored1 ignored2 ignored3 stack runtimeEnvironment substitution tree innerStack
      innerEnvironment innerSubstitution parameters states guard innerReduction
      innerAgreement innerIH sourceContext sourceParameters goal runtimeAgreement
      stateTyping next member
    exact Step.mnodeStep_preservation runtimeAgreement.runtimePatternLinear guard
      innerReduction
      (fun {innerParameters} {innerGoal} innerTyping inner innerMember =>
        innerIH runtimeAgreement innerTyping inner innerMember)
      stateTyping next member
  case smnodeVarpat =>
    intro ignored1 ignored2 ignored3 ignored4 ignored5 ignored6 ignored7 ignored8 stack runtimeEnvironment substitution name pattern runtimeMatcher
      runtimeValue innerStack innerEnvironment innerSubstitution parameters found
      sourceContext sourceParameters goal runtimeAgreement stateTyping next member
    simp only [List.mem_singleton] at member
    subst next
    exact Step.mnodeVarpat_preservation
      runtimeAgreement.runtimePatternLinear found stateTyping
  case smnodeDone =>
    intro stack runtimeEnvironment substitution innerEnvironment
      innerSubstitution parameters sourceContext sourceParameters goal
      runtimeAgreement stateTyping next member
    simp only [List.mem_singleton] at member
    subst next
    exact Step.mnodeDone_preservation
      runtimeAgreement.runtimePatternLinear stateTyping
  case sdone =>
    intro runtimeEnvironment substitution
    constructor
    · intro statePristine actual member
      simp only [List.mem_singleton] at member
      subst actual
      exact statePristine.2.2
    · intro sourceContext sourceParameters goal runtimeAgreement stateTyping
        actual member
      simp only [List.mem_singleton] at member
      subst actual
      exact stateTyping.terminal_substitution
  case sstep =>
    intro state states resultLists reduction lengths searches stepAgreement
      searchesAgreement stepIH searchesIH
    constructor
    · intro statePristine
      have statesPristine := Step.pristine reduction statePristine
      exact List.forall_mem_flatten_of_zip lengths
        (fun pair pairMember actual actualMember =>
          (searchesIH pair pairMember).1
            (statesPristine pair.1 (List.fst_mem_of_mem_zip pairMember))
            actual actualMember)
    · intro sourceContext sourceParameters goal runtimeAgreement stateTyping
        actual member
      obtain ⟨resultList, resultListMember, actualMember⟩ :=
        List.mem_flatten.mp member
      obtain ⟨successor, paired⟩ :=
        List.exists_fst_mem_zip_of_snd_mem lengths resultListMember
      exact (searchesIH (successor, resultList) paired).2 runtimeAgreement
        (stepIH runtimeAgreement stateTyping successor
          (List.fst_mem_of_mem_zip paired))
        actual actualMember

/-! ## Public concrete preservation surface -/

/-- Evaluation preserves the pristine runtime-value boundary. -/
theorem EvalRuntimeSigAgrees.pristine
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {environment : Env} {expression : Expr} {value : Value}
    {evaluation : Eval SF environment expression value}
    (agreement : EvalRuntimeSigAgrees signature SF evaluation)
    (environmentPristine : EnvPristine environment) :
    ValuePristine value :=
  (EvalRuntimeSigAgrees.preserve_with signatureWF
    (fun typing => typing.generalizedValueFlow
      signatureWF.armExhaustiveBasic)
    (@PatfunPreservationKernel.of_source signature signatureWF SF) agreement).1
    environmentPristine

/-- Evaluation from a pristine typed environment preserves the exact source
target. -/
theorem EvalRuntimeSigAgrees.preservation
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {environment : Env} {expression : Expr} {value : Value}
    {evaluation : Eval SF environment expression value}
    (agreement : EvalRuntimeSigAgrees signature SF evaluation)
    {context : Context} {target : Ty}
    (environmentPristine : EnvPristine environment)
    (environmentTyping : EnvTyped signature context environment)
    (sourceTyping : HasTy signature context expression target) :
    ValueTy signature value target :=
  (EvalRuntimeSigAgrees.preserve_with signatureWF
    (fun typing => typing.generalizedValueFlow
      signatureWF.armExhaustiveBasic)
    (@PatfunPreservationKernel.of_source signature signatureWF SF) agreement).2
    environmentPristine environmentTyping sourceTyping

/-- The exact typed-output statement for one atom reduction, specialized to
the public evaluation theorem. -/
private theorem MAtomRuntimeSigAgrees.preservation
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {environment : Env} {pattern : Pattern} {matcher value : Value}
    {continuations : List (List Atom)} {new : MatchSubst}
    {reduction : MAtom SF environment pattern matcher value continuations new}
    (agreement : MAtomRuntimeSigAgrees signature SF reduction)
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    (environmentPristine : EnvPristine environment)
    (valuePristine : ValuePristine value)
    (matcherPristine : MAtomInputPristine pattern matcher)
    (environmentTyping :
      EnvTyped signature (input.toContext ++ context) environment)
    (typing : AtomTy signature context parameters input
      ⟨pattern, matcher, value⟩ output)
    (trace : MAtomDispatchTrace SF environment pattern value matcher) :
    MAtomTypedOutput signature context parameters input output
      continuations new := by
  let evalPristine : EvalPristineKernel signature SF :=
    fun {environment} {expression} {value} {evaluation}
        evaluationAgreement pristine =>
      EvalRuntimeSigAgrees.pristine signatureWF
        evaluationAgreement pristine
  let evalPreserve : EvalPreservationKernel signature SF :=
    fun {environment} {expression} {value} {evaluation}
        evaluationAgreement {context} {target} pristine environmentTyping
          sourceTyping =>
      EvalRuntimeSigAgrees.preservation signatureWF
        evaluationAgreement pristine environmentTyping sourceTyping
  let ppmPristine : PPMPristineKernel signature SF :=
    fun {environment} {pp} {pattern} {result} {matching}
        ppmAgreement pristine =>
      PPMRuntimeSigAgrees.pristine_with evalPristine ppmAgreement pristine
  let ppmPreserve : PPMPreservationKernel signature SF :=
    fun {environment} {pp} {pattern} {captures} {ppEnvironment} {matching}
        ppmAgreement {context} {input} {target} {bindings} pristine
          environmentTyping captureTyping =>
      PPMRuntimeSigAgrees.preserve_with evalPreserve ppmAgreement rfl pristine
        environmentTyping captureTyping
  intro runtimeSubstitution runtimeSubstitutionTyping
  exact (agreement.preserve_with signatureWF evalPristine evalPreserve
    ppmPristine ppmPreserve environmentPristine valuePristine matcherPristine
    environmentTyping typing trace) runtimeSubstitutionTyping

/-- Every successor of one derivation-locally agreed concrete step remains
typed at the same matching goal. -/
theorem StepRuntimeSigAgrees.preservation
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {state : MState} {states : List MState}
    {reduction : Step SF state states}
    (derivationAgreement : StepRuntimeSigAgrees signature SF reduction)
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    (runtimeAgreement : RuntimeSigAgrees signature context SF)
    (stateTyping : MStateTyAt signature context parameters state goal) :
    ∀ next ∈ states,
      MStateTyAt signature context parameters next goal := by
  refine StepRuntimeSigAgrees.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ _ => True)
    (motive_4 := fun {runtimeState} {runtimeStates} _ _ =>
      ∀ {sourceContext : Context} {sourceParameters : PatternCtx}
        {sourceGoal : MonoCtx},
        RuntimeSigAgrees signature sourceContext SF →
        MStateTyAt signature sourceContext sourceParameters runtimeState
          sourceGoal →
        ∀ next ∈ runtimeStates,
          MStateTyAt signature sourceContext sourceParameters next sourceGoal)
    (motive_5 := fun _ _ => True)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep derivationAgreement runtimeAgreement stateTyping
  case sreduce =>
      intro ignored stack environment substitution pattern matcher value
        continuations new atomReduction atomAgreement atomIH sourceContext
        sourceParameters sourceGoal runtimeAgreement stateTyping next member
      rcases stateTyping.1 with
        ⟨stackPristine, environmentPristine, substitutionPristine⟩
      cases stackPristine with
      | cons headPristine tailPristine =>
          cases headPristine with
          | atom atomPristine =>
              rcases atomPristine with ⟨matcherPristine, valuePristine⟩
              have combinedPristine :=
                substitutionPristine.append environmentPristine
              have typedOutput :
                  ∀ {input output},
                    EnvTyped signature (input.toContext ++ sourceContext)
                      (substitution ++ environment) →
                    AtomTy signature sourceContext sourceParameters input
                      ⟨pattern, matcher, value⟩ output →
                    MAtomTypedOutput signature sourceContext sourceParameters
                      input output continuations new := by
                intro input output combinedTyping atomTyping
                exact atomAgreement.preservation signatureWF
                  combinedPristine valuePristine (.inl matcherPristine)
                  combinedTyping atomTyping
                  (MAtomDispatchTrace.pristine matcherPristine)
              exact Step.reduce_preservation
                runtimeAgreement.runtimePatternLinear atomReduction typedOutput
                stateTyping next member
  case spatfunEnter =>
      intro ignored1 ignored2 ignored3 ignored4 ignored5 stack environment
        substitution name arguments matcher value runtime found length
        sourceContext sourceParameters sourceGoal runtimeAgreement stateTyping
        next member
      simp only [List.mem_singleton] at member
      subst next
      exact PatfunPreservationKernel.of_instantiatedBody
        (fun typing => typing.instantiatedBody
          signatureWF.armExhaustiveBasic
          signatureWF.patternFunNamesNodup) (_found := found)
        (_length := length) runtimeAgreement stateTyping
  case smnodeStep =>
      intro ignored1 ignored2 ignored3 stack environment substitution tree
        innerStack innerEnvironment innerSubstitution piE states guard inner
        innerAgreement innerIH sourceContext sourceParameters sourceGoal
        runtimeAgreement stateTyping next member
      exact Step.mnodeStep_preservation
        runtimeAgreement.runtimePatternLinear guard inner
        (fun {innerParameters} {innerGoal} innerTyping innerState
            innerMember =>
          innerIH runtimeAgreement innerTyping innerState innerMember)
        stateTyping next member
  case smnodeVarpat =>
      intro ignored1 ignored2 ignored3 ignored4 ignored5 ignored6 ignored7
        ignored8 stack environment substitution name pattern matcher value
        innerStack innerEnvironment innerSubstitution piE found sourceContext
        sourceParameters sourceGoal runtimeAgreement stateTyping next member
      simp only [List.mem_singleton] at member
      subst next
      exact Step.mnodeVarpat_preservation
        runtimeAgreement.runtimePatternLinear found stateTyping
  case smnodeDone =>
      intro stack environment substitution innerEnvironment innerSubstitution
        piE sourceContext sourceParameters sourceGoal runtimeAgreement
        stateTyping next member
      simp only [List.mem_singleton] at member
      subst next
      exact Step.mnodeDone_preservation
        runtimeAgreement.runtimePatternLinear stateTyping
  all_goals intros; trivial

/-! ## Reachability and successful search -/

/-- Derivation-local runtime agreement along one chosen reachability branch. -/
inductive ReachesRuntimeSigAgrees
    (signature : FrozenSig) (SF : RuntimeSigF) :
    {start finish : MState} → Reaches SF start finish → Prop where
  | refl {state} :
      ReachesRuntimeSigAgrees signature SF (@Reaches.refl SF state)
  | step
      {state successors next finish}
      {reduction : Step SF state successors}
      {member : next ∈ successors}
      {tail : Reaches SF next finish} :
      StepRuntimeSigAgrees signature SF reduction →
      ReachesRuntimeSigAgrees signature SF tail →
      ReachesRuntimeSigAgrees signature SF
        (.step reduction member tail)

/-- One-step preservation iterates along every agreed chosen branch. -/
theorem ReachesRuntimeSigAgrees.typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {start finish : MState} {reachable : Reaches SF start finish}
    (pathAgreement : ReachesRuntimeSigAgrees signature SF reachable)
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    (runtimeAgreement : RuntimeSigAgrees signature context SF)
    (initialTyping : MStateTyAt signature context parameters start goal) :
    MStateTyAt signature context parameters finish goal := by
  induction pathAgreement with
  | refl => exact initialTyping
  | step stepAgreement tailAgreement induction =>
      exact induction
        (stepAgreement.preservation signatureWF runtimeAgreement
          initialTyping _ (by assumption))

/-- Every substitution returned by an agreed exhaustive search is typed at
the source binding goal of its initial state. -/
theorem SearchRuntimeSigAgrees.substitutions_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {state : MState} {substitutions : List MatchSubst}
    {search : Search SF state substitutions}
    (searchAgreement : SearchRuntimeSigAgrees signature SF search)
    {context : Context} {parameters : PatternCtx} {goal : MonoCtx}
    (runtimeAgreement : RuntimeSigAgrees signature context SF)
    (initialTyping : MStateTyAt signature context parameters state goal) :
    ∀ substitution ∈ substitutions,
      MatchSubstTyped signature goal substitution := by
  refine SearchRuntimeSigAgrees.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ _ => True)
    (motive_4 := fun _ _ => True)
    (motive_5 := fun {runtimeState} {runtimeSubstitutions} _ _ =>
      ∀ {sourceContext : Context} {sourceParameters : PatternCtx}
        {sourceGoal : MonoCtx},
        RuntimeSigAgrees signature sourceContext SF →
        MStateTyAt signature sourceContext sourceParameters runtimeState
          sourceGoal →
        ∀ substitution ∈ runtimeSubstitutions,
          MatchSubstTyped signature sourceGoal substitution)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?elet
    ?esomething ?ematcher ?ematchAll
    ?phole ?pwild ?ppval ?pctor ?ptuple ?pfail
    ?msomeWC ?msomeVar ?msomeValEq ?msomeValNeq ?mand ?mor ?mtuple
    ?mprodSome ?mppfail ?mdpfail ?mmatcher
    ?sreduce ?spatfunEnter ?smnodeStep ?smnodeVarpat ?smnodeDone
    ?sdone ?sstep searchAgreement runtimeAgreement initialTyping
  case sdone =>
      intro runtimeEnvironment runtimeSubstitution sourceContext
        sourceParameters sourceGoal runtimeAgreement initialTyping
        substitution member
      simp only [List.mem_singleton] at member
      subst substitution
      exact initialTyping.terminal_substitution
  case sstep =>
      intro runtimeState runtimeStates resultLists reduction lengths searches
        stepAgreement childrenAgreements stepIH childrenIH sourceContext
        sourceParameters sourceGoal runtimeAgreement initialTyping substitution
        member
      obtain ⟨resultList, resultListMember, substitutionMember⟩ :=
        List.mem_flatten.mp member
      obtain ⟨successor, paired⟩ :=
        List.exists_fst_mem_zip_of_snd_mem (by assumption) resultListMember
      have successorTyping :=
        stepAgreement.preservation signatureWF runtimeAgreement
          initialTyping successor (List.fst_mem_of_mem_zip paired)
      exact childrenIH (successor, resultList) paired runtimeAgreement
        successorTyping substitution substitutionMember
  all_goals intros; trivial

/-- A top-level atom and the empty initial substitution form the concrete
typed state used by matcher consistency. -/
theorem AtomTy.initialState_typed
    {signature : FrozenSig} {context : Context} {goal : MonoCtx}
    {environment : Env}
    {pattern : Pattern} {matcher value : Value}
    (environmentPristine : EnvPristine environment)
    (matcherPristine : ValuePristine matcher)
    (valuePristine : ValuePristine value)
    (environmentTyping : EnvTyped signature context environment)
    (atomTyping : AtomTy signature context [] []
      ⟨pattern, matcher, value⟩ goal) :
    MStateTy signature context
      ⟨[.atom ⟨pattern, matcher, value⟩], environment, []⟩ goal := by
  have patternNoEmbed : Pattern.noEmbedInOr pattern = true := by
    cases atomTyping with
    | mk patternTyping matcherTyping valueTyping =>
        exact patternTyping.noEmbedInOr_of_parameters_nil
    | primitive patternTyping primitive matcherTyping valueTyping =>
        exact patternTyping.noEmbedInOr_of_parameters_nil
  exact
    ⟨⟨.cons (.atom ⟨matcherPristine, valuePristine⟩) .nil,
        environmentPristine, .nil⟩,
      by simpa [stackNoEmbedInOr, treeNoEmbedInOr] using patternNoEmbed,
      environmentTyping, [], matchSubstTyped_nil signature,
      .cons (.atom atomTyping) .nil⟩

/-- Matcher consistency: every successful substitution produced from one
well-typed pristine initial atom has exactly its source binding context. -/
theorem matcher_consistency
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF}
    {context : Context} {goal : MonoCtx} {environment : Env}
    {pattern : Pattern} {matcher value : Value}
    {substitutions : List MatchSubst}
    {search : Search SF
      ⟨[.atom ⟨pattern, matcher, value⟩], environment, []⟩
      substitutions}
    (searchAgreement : SearchRuntimeSigAgrees signature SF search)
    (runtimeAgreement : RuntimeSigAgrees signature context SF)
    (environmentPristine : EnvPristine environment)
    (matcherPristine : ValuePristine matcher)
    (valuePristine : ValuePristine value)
    (environmentTyping : EnvTyped signature context environment)
    (atomTyping : AtomTy signature context [] []
      ⟨pattern, matcher, value⟩ goal) :
    ∀ substitution ∈ substitutions,
      MatchSubstTyped signature goal substitution :=
  searchAgreement.substitutions_typed signatureWF runtimeAgreement
    (atomTyping.initialState_typed environmentPristine matcherPristine
      valuePristine environmentTyping)

/-- Local readiness is defined only for a nonterminal matching state. -/
theorem StepReady.stack_ne_nil
    {SF : RuntimeSigF} {state : MState} (ready : StepReady SF state) :
    state.S ≠ [] := by
  cases ready <;> simp

/-- Every locally ready, well-typed nonterminal state takes one concrete step. -/
theorem StepReady.progress
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {context : Context} {parameters : PatternCtx}
    {state : MState} {goal : MonoCtx}
    (agreement : RuntimeSigAgrees signature context SF)
    (ready : StepReady SF state)
    (typing : MStateTyAt signature context parameters state goal) :
    ∃ states, Step SF state states := by
  induction ready generalizing parameters goal with
  | atom atomReady =>
      rcases typing with
        ⟨statePristine, noEmbed, environmentTyping, input,
          substitutionTyping, stackTyping⟩
      cases stackTyping with
      | cons treeTyping tailTyping =>
          cases treeTyping with
          | atom atomTyping =>
              obtain ⟨continuations, new, reduction⟩ :=
                atomReady.progress signatureWF atomTyping
              exact ⟨_, .reduce reduction⟩
  | @patfun stack environment substitution name arguments matcher value =>
      rcases typing with
        ⟨statePristine, noEmbed, environmentTyping, input,
          substitutionTyping, stackTyping⟩
      cases stackTyping with
      | cons treeTyping tailTyping =>
          cases treeTyping with
          | atom atomTyping =>
              cases atomTyping with
              | mk patternTyping matcherTyping valueTyping =>
                  cases patternTyping.terminal with
                  | @app _ _ _ _ _ scheme _ duals _ result sourceLookup
                      children instanceTyping =>
                      obtain ⟨definition, nameEquality, runtimeFound,
                          definitionTyping⟩ :=
                        agreement.sourceLookup sourceLookup
                      have actualArity :=
                        definitionTyping.actual_arity instanceTyping
                      have runtimeArity :
                          definition.runtime.params.length = arguments.length := by
                        exact actualArity.trans children.length.symm
                      exact ⟨_, .patfunEnter runtimeFound runtimeArity⟩
              | primitive patternTyping primitive matcherTyping valueTyping =>
                  simp [Pattern.isPrimForm] at primitive
  | @mnodeStep stack environment substitution tree innerStack
      innerEnvironment innerSubstitution innerParameters guard innerReady
      induction =>
      rcases typing with
        ⟨statePristine, noEmbed, environmentTyping, input,
          substitutionTyping, stackTyping⟩
      rcases statePristine with
        ⟨stackPristine, outerEnvironmentPristine,
          outerSubstitutionPristine⟩
      cases stackPristine with
      | cons nodePristine tailPristine =>
          cases nodePristine with
          | mnode innerStackPristine innerEnvironmentPristine
              innerSubstitutionPristine =>
              cases stackTyping with
              | cons treeTyping tailTyping =>
                  obtain ⟨fixedParameters, innerBindings, innerOutput,
                      innerNoEmbed, capturedEnvironmentTyping,
                      innerSubstitutionTyping, innerStackTyping⟩ :=
                    treeTyping.mnode_inner
                  have innerTyping : MStateTyAt signature context
                      fixedParameters
                      ⟨tree :: innerStack, innerEnvironment,
                        innerSubstitution⟩ innerOutput :=
                    ⟨⟨innerStackPristine, innerEnvironmentPristine,
                        innerSubstitutionPristine⟩,
                      innerNoEmbed, capturedEnvironmentTyping,
                      innerBindings, innerSubstitutionTyping,
                      innerStackTyping⟩
                  obtain ⟨states, innerStep⟩ :=
                    induction innerTyping
                  exact ⟨_, .mnodeStep guard innerStep⟩
  | mnodeVarpat found =>
      exact ⟨_, .mnodeVarpat found⟩
  | mnodeDone =>
      exact ⟨_, .mnodeDone⟩

/-! ## Bundled public safety theorem -/

/-- The six concrete safety consequences exposed by the Egison core. -/
structure CoreSafety (signature : FrozenSig) (SF : RuntimeSigF) : Prop where
  evalPreservation :
    ∀ {environment expression value}
      {evaluation : Eval SF environment expression value}
      {context target},
      EvalRuntimeSigAgrees signature SF evaluation →
      EnvPristine environment →
      EnvTyped signature context environment →
      HasTy signature context expression target →
      ValueTy signature value target
  stepPreservation :
    ∀ {state states} {reduction : Step SF state states}
      {context parameters goal},
      StepRuntimeSigAgrees signature SF reduction →
      RuntimeSigAgrees signature context SF →
      MStateTyAt signature context parameters state goal →
      ∀ next ∈ states,
        MStateTyAt signature context parameters next goal
  localProgress :
    ∀ {context parameters state goal},
      RuntimeSigAgrees signature context SF →
      StepReady SF state →
      MStateTyAt signature context parameters state goal →
      ∃ states, Step SF state states
  reachesTyped :
    ∀ {start finish} {reachable : Reaches SF start finish}
      {context parameters goal},
      ReachesRuntimeSigAgrees signature SF reachable →
      RuntimeSigAgrees signature context SF →
      MStateTyAt signature context parameters start goal →
      MStateTyAt signature context parameters finish goal
  searchSubstitutionsTyped :
    ∀ {state substitutions} {search : Search SF state substitutions}
      {context parameters goal},
      SearchRuntimeSigAgrees signature SF search →
      RuntimeSigAgrees signature context SF →
      MStateTyAt signature context parameters state goal →
      ∀ substitution ∈ substitutions,
        MatchSubstTyped signature goal substitution
  matcherConsistency :
    ∀ {context goal environment pattern matcher value substitutions}
      {search : Search SF
        ⟨[.atom ⟨pattern, matcher, value⟩], environment, []⟩
        substitutions},
      SearchRuntimeSigAgrees signature SF search →
      RuntimeSigAgrees signature context SF →
      EnvPristine environment →
      ValuePristine matcher →
      ValuePristine value →
      EnvTyped signature context environment →
      AtomTy signature context [] [] ⟨pattern, matcher, value⟩ goal →
      ∀ substitution ∈ substitutions,
        MatchSubstTyped signature goal substitution

/-- Frozen-signature well-formedness discharges the complete public safety
package; value-pattern capture admissibility is derived from clause order. -/
theorem core_safety
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} :
    CoreSafety signature SF where
  evalPreservation := fun agreement environmentPristine environmentTyping
      sourceTyping =>
    agreement.preservation signatureWF environmentPristine
      environmentTyping sourceTyping
  stepPreservation := fun agreement runtimeAgreement stateTyping next member =>
    agreement.preservation signatureWF runtimeAgreement stateTyping
      next member
  localProgress := fun runtimeAgreement ready stateTyping =>
    ready.progress signatureWF runtimeAgreement stateTyping
  reachesTyped := fun pathAgreement runtimeAgreement initialTyping =>
    pathAgreement.typed signatureWF runtimeAgreement initialTyping
  searchSubstitutionsTyped :=
    fun searchAgreement runtimeAgreement initialTyping substitution member =>
      searchAgreement.substitutions_typed signatureWF
        runtimeAgreement initialTyping substitution member
  matcherConsistency :=
    fun searchAgreement runtimeAgreement environmentPristine matcherPristine
        valuePristine environmentTyping atomTyping substitution member =>
      matcher_consistency signatureWF searchAgreement
        runtimeAgreement environmentPristine matcherPristine valuePristine
        environmentTyping atomTyping substitution member

end TypePM
