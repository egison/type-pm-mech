import TypePM.Preservation
import TypePM.SourceMetatheory
import TypePM.PatternFunction

/-!
# Concrete dynamic metatheory for the two-sorted core

This module supplies the structural and canonical lemmas needed before the
`MAtom`/`Step`/`Search` preservation proof.  Every statement is about the
concrete source and runtime judgments; no runtime oracle or abstract runtime
specification is introduced.
-/

namespace TypePM

/-! ## Pristine-value structural facts -/

/-- Every member of a pristine value list is pristine. -/
theorem ValuesPristine.member
    {values : List Value} (pristine : ValuesPristine values) :
    ∀ {value}, value ∈ values → ValuePristine value := by
  intro value membership
  induction values with
  | nil => contradiction
  | cons head tail induction =>
      cases pristine with
      | cons headPristine tailPristine =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact headPristine
      · exact induction tailPristine membership

/-- Pointwise pristine value lists compose by append. -/
theorem ValuesPristine.append
    {left right : List Value}
    (leftPristine : ValuesPristine left)
    (rightPristine : ValuesPristine right) :
    ValuesPristine (left ++ right) := by
  induction left with
  | nil => exact rightPristine
  | cons head tail induction =>
      cases leftPristine with
      | cons headPristine tailPristine =>
          exact .cons headPristine (induction tailPristine)

/-- A successful lookup from a pristine environment is pristine. -/
theorem EnvPristine.lookup
    {environment : Env} (pristine : EnvPristine environment)
    {name : String} {value : Value}
    (found : Env.find? environment name = some value) :
    ValuePristine value := by
  induction environment with
  | nil => simp [Env.find?] at found
  | cons head tail induction =>
      obtain ⟨headName, headValue⟩ := head
      cases pristine with
      | cons headPristine tailPristine =>
      simp only [Env.find?, List.find?] at found
      cases equal : (headName == name) with
      | true =>
          rw [equal] at found
          simp only [Option.map, Option.some.injEq] at found
          subst value
          exact headPristine
      | false =>
          rw [equal] at found
          exact induction tailPristine found

/-- Pristine environments compose by append. -/
theorem EnvPristine.append
    {left right : Env}
    (leftPristine : EnvPristine left)
    (rightPristine : EnvPristine right) :
    EnvPristine (left ++ right) := by
  induction left with
  | nil => exact rightPristine
  | cons head tail induction =>
      cases leftPristine with
      | cons headPristine tailPristine =>
          exact .cons headPristine (induction tailPristine)

/-- Pristine stacks compose by append. -/
theorem StackPristine.append
    {left right : List Tree}
    (leftPristine : StackPristine left)
    (rightPristine : StackPristine right) :
    StackPristine (left ++ right) := by
  induction left with
  | nil => exact rightPristine
  | cons head tail induction =>
      cases leftPristine with
      | cons headPristine tailPristine =>
          exact .cons headPristine (induction tailPristine)

/-- Taking a prefix preserves pointwise pristineness. -/
theorem ValuesPristine.take
    {values : List Value} (pristine : ValuesPristine values) (count : Nat) :
    ValuesPristine (values.take count) := by
  induction count generalizing values with
  | zero => exact .nil
  | succ count induction =>
      cases values with
      | nil => exact .nil
      | cons value values =>
          cases pristine with
          | cons head tail => exact .cons head (induction tail)

/-- Dropping a prefix preserves pointwise pristineness. -/
theorem ValuesPristine.drop
    {values : List Value} (pristine : ValuesPristine values) (count : Nat) :
    ValuesPristine (values.drop count) := by
  induction count generalizing values with
  | zero => exact pristine
  | succ count induction =>
      cases values with
      | nil => exact .nil
      | cons value values =>
          cases pristine with
          | cons _ tail => exact induction tail

/-- Core list encoding preserves pristine elements. -/
theorem mkListV_pristine
    {values : List Value} (pristine : ValuesPristine values) :
    ValuePristine (mkListV values) := by
  induction values with
  | nil => exact .ctor .nil
  | cons value values induction =>
      cases pristine with
      | cons head tail =>
          exact .ctor (.cons head (.cons (induction tail) .nil))

/-- Core list decoding exposes only pristine elements. -/
theorem listOfV_pristine
    {value : Value} {values : List Value}
    (pristine : ValuePristine value)
    (decoded : listOfV value = some values) :
    ValuesPristine values := by
  let P : Value → Prop := fun candidate =>
    ∀ {outputs : List Value},
      ValuePristine candidate →
      listOfV candidate = some outputs →
      ValuesPristine outputs
  have all : ∀ candidate, P candidate := by
    refine Value.rec
      (motive_1 := P)
      (motive_2 := fun fields => ∀ field ∈ fields, P field)
      (motive_3 := fun _ => True)
      (motive_4 := fun _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro literal outputs _ decoding
      simp [listOfV] at decoding
    · intro name fields fieldsIH outputs candidatePristine decoding
      cases candidatePristine with
      | ctor fieldsPristine =>
          by_cases nilName : name = "nil"
          · subst name
            cases fields with
            | nil =>
                simp only [listOfV, Option.some.injEq] at decoding
                subst outputs
                exact .nil
            | cons head tail => simp [listOfV] at decoding
          · by_cases consName : name = "cons"
            · subst name
              cases fields with
              | nil => simp [listOfV] at decoding
              | cons head tail =>
                  cases tail with
                  | nil => simp [listOfV] at decoding
                  | cons rest more =>
                      cases more with
                      | cons extra extras => simp [listOfV] at decoding
                      | nil =>
                          cases fieldsPristine with
                          | cons headPristine tailPristine =>
                              cases tailPristine with
                              | cons restPristine tailPristine =>
                                  cases tailPristine
                                  cases restDecode : listOfV rest with
                                  | none =>
                                      simp [listOfV, restDecode] at decoding
                                  | some restValues =>
                                      simp [listOfV, restDecode] at decoding
                                      subst outputs
                                      exact .cons headPristine
                                        (fieldsIH rest (by simp) restPristine
                                          restDecode)
            · simp [listOfV, nilName, consName] at decoding
    · intro fields _ outputs _ decoding
      simp [listOfV] at decoding
    · intro self environment parameter body _ outputs _ decoding
      simp [listOfV] at decoding
    · intro environment original current _ outputs _ decoding
      simp [listOfV] at decoding
    · intro outputs _ decoding
      simp [listOfV] at decoding
    · intro field membership
      contradiction
    · intro head tail headIH tailIH field membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact headIH
      · exact tailIH field membership
    · trivial
    · intros
      trivial
    · intros
      trivial
  exact all value pristine decoded

/-- Tuple decoding exposes only pristine components. -/
theorem decodeTuple_pristine
    {count : Nat} {value : Value} {values : List Value}
    (pristine : ValuePristine value)
    (decoded : decodeTuple count value = some values) :
    ValuesPristine values := by
  unfold decodeTuple at decoded
  by_cases singleton : count == 1
  · simp [singleton] at decoded
    subst values
    exact .cons pristine .nil
  · cases value with
    | tuple components =>
        cases pristine with
        | tuple componentsPristine =>
            simp [singleton] at decoded
            rw [← decoded.2]
            exact componentsPristine
    | lit => simp [singleton] at decoded
    | ctor => simp [singleton] at decoded
    | closure => simp [singleton] at decoded
    | matcherV => simp [singleton] at decoded
    | something => simp [singleton] at decoded

/-- Every tuple produced by pointwise decoding of pristine inputs is pristine. -/
theorem decodeTuple_mapM_pristine :
    ∀ {inputs : List Value} {outputs : List (List Value)} {count : Nat},
      ValuesPristine inputs →
      inputs.mapM (decodeTuple count) = some outputs →
      ∀ output ∈ outputs, ValuesPristine output := by
  intro inputs outputs count inputsPristine decoding
  induction inputs generalizing outputs with
  | nil =>
      simp at decoding
      subst outputs
      intro output membership
      contradiction
  | cons input inputs induction =>
      cases inputsPristine with
      | cons inputPristine inputsPristine =>
          simp only [List.mapM_cons] at decoding
          cases headDecode : decodeTuple count input with
          | none => simp [headDecode] at decoding
          | some headOutput =>
              cases tailDecode : List.mapM (decodeTuple count) inputs with
              | none => simp [headDecode, tailDecode] at decoding
              | some tailOutputs =>
                  simp [headDecode, tailDecode] at decoding
                  subst outputs
                  intro output membership
                  simp only [List.mem_cons] at membership
                  rcases membership with rfl | membership
                  · exact decodeTuple_pristine inputPristine headDecode
                  · exact induction inputsPristine tailDecode output membership

/-- Mapping pristine outputs over any finite list is pointwise pristine. -/
theorem valuesPristine_map_of_mem
    {items : List α} {output : α → Value}
    (all : ∀ item ∈ items, ValuePristine (output item)) :
    ValuesPristine (items.map output) := by
  induction items with
  | nil => exact .nil
  | cons item items induction =>
      exact .cons (all item (by simp))
        (induction (fun other member => all other (by simp [member])))

/-- Pointwise output facts over an arity-correct zip form a pristine list. -/
theorem valuesPristine_of_zip
    {inputs : List α} {values : List Value}
    (length : inputs.length = values.length)
    (pointwise : ∀ pair ∈ inputs.zip values, ValuePristine pair.2) :
    ValuesPristine values := by
  induction inputs generalizing values with
  | nil =>
      cases values <;> simp at length ⊢
      exact .nil
  | cons input inputs induction =>
      cases values with
      | nil => simp at length
      | cons value values =>
          exact .cons
            (pointwise (input, value) (by simp))
            (induction (by simpa using length) (fun pair member =>
              pointwise pair (by simp [member])))

/-- Zip-built atom continuations preserve pristine matcher/value payloads. -/
theorem stackPristine_atoms_zip
    {patterns : List Pattern} {matchers values : List Value}
    (patternLength : patterns.length = matchers.length)
    (valueLength : matchers.length = values.length)
    (matchersPristine : ValuesPristine matchers)
    (valuesPristine : ValuesPristine values) :
    StackPristine
      (((patterns.zip (matchers.zip values)).map fun entry =>
        Tree.atom ⟨entry.1, entry.2.1, entry.2.2⟩)) := by
  induction patterns generalizing matchers values with
  | nil =>
      cases matchers <;> simp at patternLength
      cases values <;> simp at valueLength ⊢
      exact .nil
  | cons pattern patterns induction =>
      cases matchers with
      | nil => simp at patternLength
      | cons matcher matchers =>
          cases values with
          | nil => simp at valueLength
          | cons value values =>
              cases matchersPristine with
              | cons matcherPristine matchersPristine =>
                  cases valuesPristine with
                  | cons valuePristine valuesPristine =>
                      exact .cons (.atom ⟨matcherPristine, valuePristine⟩)
                        (induction (by simpa using patternLength)
                          (by simpa using valueLength) matchersPristine
                          valuesPristine)

/-- The two concrete primitive operations preserve pristine values. -/
theorem primEval_pristine
    {op : PrimOp} {values : List Value} {result : Value}
    (pristine : ValuesPristine values)
    (evaluation : primEval op values = some result) :
    ValuePristine result := by
  cases op with
  | append =>
      cases values with
      | nil => simp [primEval] at evaluation
      | cons left tail =>
          cases tail with
          | nil => simp [primEval] at evaluation
          | cons right rest =>
              cases rest with
              | cons extra extras => simp [primEval] at evaluation
              | nil =>
                  cases pristine with
                  | cons leftPristine tailPristine =>
                      cases tailPristine with
                      | cons rightPristine tailPristine =>
                          cases tailPristine
                          cases leftDecode : listOfV left with
                          | none => simp [primEval, leftDecode] at evaluation
                          | some leftValues =>
                              cases rightDecode : listOfV right with
                              | none =>
                                  simp [primEval, leftDecode, rightDecode]
                                    at evaluation
                              | some rightValues =>
                                  simp [primEval, leftDecode, rightDecode]
                                    at evaluation
                                  subst result
                                  exact mkListV_pristine
                                    ((listOfV_pristine leftPristine leftDecode).append
                                      (listOfV_pristine rightPristine
                                        rightDecode))
  | splits =>
      cases values with
      | nil => simp [primEval] at evaluation
      | cons input rest =>
          cases rest with
          | cons extra extras => simp [primEval] at evaluation
          | nil =>
              cases pristine with
              | cons inputPristine tailPristine =>
                  cases tailPristine
                  cases decoding : listOfV input with
                  | none => simp [primEval, decoding] at evaluation
                  | some elements =>
                      simp [primEval, decoding] at evaluation
                      subst result
                      apply mkListV_pristine
                      apply valuesPristine_map_of_mem
                      intro index membership
                      exact .tuple
                        (.cons
                          (mkListV_pristine
                            ((listOfV_pristine inputPristine decoding).take
                              index))
                          (.cons
                            (mkListV_pristine
                              ((listOfV_pristine inputPristine decoding).drop
                                index))
                            .nil))

/-! ## Bidirectional source/runtime pattern-function agreement -/

/--
Runtime entries are source checked, and every frozen source lookup resolves to
the exact runtime parameter list and body of that checked definition.  The
second direction is essential for `Step.patfunEnter`; `RuntimeSigTyped` alone
only supplies runtime-to-source soundness.
-/
structure RuntimeSigAgrees
    (signature : FrozenSig) (context : Context)
    (runtime : RuntimeSigF) : Prop where
  runtimeTyped : RuntimeSigTyped signature context runtime
  sourceLookup :
    ∀ {name : String} {scheme : DualScheme},
      signature.findPatternFun name = some scheme →
      ∃ definition : PatternDef,
        definition.name = name ∧
        List.find? (fun entry => entry.1 == name) runtime =
          some (name, definition.runtime) ∧
        PatternDefTy signature context definition scheme

/-- Safe dual instantiation preserves the scheme's argument arity. -/
theorem DualScheme.ValueFlowInst.args_length
    {scheme : DualScheme} {args : List Dual} {result : Dual}
    (typing : scheme.ValueFlowInst args result) :
    scheme.args.length = args.length := by
  rcases typing with ⟨C, T, instanceTyping⟩
  simpa only [List.length_map] using
    congrArg List.length instanceTyping.argsResult

/-- A checked pattern-function definition and one safe use agree on arity. -/
theorem PatternDefTy.actual_arity
    {definitionSignature : FrozenSig} {context : Context}
    {definition : PatternDef} {scheme : DualScheme}
    (typing : PatternDefTy definitionSignature context definition scheme)
    {args : List Dual} {result : Dual}
    (instanceTyping : scheme.ValueFlowInst args result) :
    definition.parameterNames.length = args.length := by
  induction typing with
  | @mk capabilities rawResult resultBindings _ _ found nonrecursive
      parameterLength nodup fresh capsNodup bodyTyping linear schemeEquality =>
      have localInstance :=
        (schemeEquality.instances args result).mp instanceTyping
      have instantiatedLength := localInstance.args_length
      have normalizedLength :
          (definition.coreScheme definitionSignature context capabilities
            rawResult).args.length =
          (patternParameterDuals definition.parameters capabilities).length := by
        simp [PatternDef.coreScheme]
      have sourceLength :
          (patternParameterDuals definition.parameters capabilities).length =
            args.length := by
        exact normalizedLength.symm.trans instantiatedLength
      have dualLength :
          (patternParameterDuals definition.parameters capabilities).length =
            definition.parameters.length := by
        simp [patternParameterDuals, parameterLength]
      simpa [PatternDef.parameterNames] using dualLength.symm.trans sourceLength

/-! ## Membership inversion for clauses and arms -/

/-- Every member of a typed arm list has its concrete data-pattern/body typing. -/
theorem ArmsTy.member
    {signature : FrozenSig} {context : Context} {target ppResult : Ty}
    {ppBindings : MonoCtx} {arms : List Arm}
    (typing : ArmsTy signature context target ppBindings ppResult arms) :
    ∀ {arm : Arm}, arm ∈ arms →
      ∃ pattern body armBindings,
        arm = .mk pattern body ∧
        DPatTy signature pattern target armBindings ∧
        RuntimeTyping signature
          (armBindings.toContext ++ ppBindings.toContext ++ context)
          body ppResult := by
  intro arm membership
  induction arms with
  | nil => contradiction
  | cons head tail ih =>
      cases typing with
      | cons headTyping tailTyping =>
          simp only [List.mem_cons] at membership
          rcases membership with rfl | membership
          · cases headTyping with
            | mk patternTyping bodyTyping =>
                exact ⟨_, _, _, rfl, patternTyping, bodyTyping⟩
          · exact ih tailTyping membership

/-- Threaded pattern-list typing composes over concatenation. -/
theorem PatternTys.append
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input middle output : MonoCtx}
    {leftPatterns rightPatterns : List Pattern}
    {leftDuals rightDuals : List Dual}
    (left : PatternTys signature context parameters input
      leftPatterns leftDuals middle)
    (right : PatternTys signature context parameters middle
      rightPatterns rightDuals output) :
    PatternTys signature context parameters input
      (leftPatterns ++ rightPatterns) (leftDuals ++ rightDuals) output := by
  induction leftPatterns generalizing input leftDuals middle with
  | nil =>
      cases left
      exact right
  | cons pattern patterns induction =>
      cases left with
      | cons head tail => exact .cons head (induction tail right)

/-- Threaded resolved pattern-list typing composes over concatenation. -/
theorem PatternResolutions.append
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx}
    {input middle output : MonoCtx}
    {leftPatterns rightPatterns : List Pattern}
    {leftDuals rightDuals : List Dual}
    (left : PatternResolutions signature prevailing context parameters input
      leftPatterns leftDuals middle)
    (right : PatternResolutions signature prevailing context parameters middle
      rightPatterns rightDuals output) :
    PatternResolutions signature prevailing context parameters input
      (leftPatterns ++ rightPatterns) (leftDuals ++ rightDuals) output := by
  induction leftPatterns generalizing input leftDuals middle with
  | nil =>
      cases left with
      | identity equality typing =>
          subst prevailing
          cases typing
          exact right
      | nil => exact right
  | cons pattern patterns induction =>
      cases left with
      | identity equality typing =>
          subst prevailing
          exact .identity rfl (PatternTys.append typing right.raw)
      | cons head tail => exact .cons head (induction tail right)

/-- Terminal pattern lists retain one dual for each pattern. -/
theorem TerminalPatternResolutions.length
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {patterns : List Pattern} {duals : List Dual}
    (typing : TerminalPatternResolutions signature prevailing context
      parameters input patterns duals output) :
    patterns.length = duals.length := by
  induction patterns generalizing input duals with
  | nil =>
      cases typing
      rfl
  | cons pattern patterns induction =>
      cases typing with
      | cons head tail =>
          simp only [List.length_cons, induction tail]

/-- Terminal pattern-list resolution composes over source-order append. -/
theorem TerminalPatternResolutions.append
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx}
    {input middle output : MonoCtx}
    {leftPatterns rightPatterns : List Pattern}
    {leftDuals rightDuals : List Dual}
    (left : TerminalPatternResolutions signature prevailing context parameters
      input leftPatterns leftDuals middle)
    (right : TerminalPatternResolutions signature prevailing context parameters
      middle rightPatterns rightDuals output) :
    TerminalPatternResolutions signature prevailing context parameters input
      (leftPatterns ++ rightPatterns) (leftDuals ++ rightDuals) output := by
  induction leftPatterns generalizing input middle leftDuals with
  | nil =>
      cases left
      exact right
  | cons pattern patterns induction =>
      cases left with
      | cons head tail => exact .cons head (induction tail right)

/-- Every member of a typed clause list is paired with its actual evidence. -/
theorem ClausesTy.member
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    {evidence : List Shape.Evidence}
    (typing :
      ClausesTy signature prevailing context clauses capability target
        evidence) :
    ∀ {clause : Clause}, clause ∈ clauses →
      ∃ clauseEvidence,
        clauseEvidence ∈ evidence ∧
        ClauseTy signature prevailing context clause capability target
          clauseEvidence := by
  intro clause membership
  induction clauses generalizing evidence with
  | nil => contradiction
  | cons head tail ih =>
      cases typing with
      | cons headTyping tailTyping =>
          simp only [List.mem_cons] at membership
          rcases membership with rfl | membership
          · exact ⟨_, List.mem_cons_self, headTyping⟩
          · obtain ⟨foundEvidence, evidenceMember, foundTyping⟩ :=
              ih tailTyping membership
            exact ⟨foundEvidence, List.mem_cons_of_mem _ evidenceMember,
              foundTyping⟩

/--
Resolved clause membership retains the one prevailing substitution shared by
the whole matcher literal.
-/
theorem ResolvedClausesTy.member
    {signature : FrozenSig} {context : Context} {clauses : List Clause}
    {capability : Cap} {target : Ty} {evidence : List Shape.Evidence}
    (typing :
      ResolvedClausesTy signature context clauses capability target evidence)
    {clause : Clause} (membership : clause ∈ clauses) :
    ∃ prevailing clauseEvidence,
      clauseEvidence ∈ evidence ∧
      ClauseTy signature prevailing context clause capability target
        clauseEvidence := by
  cases typing with
  | ofShared sharedTyping =>
      obtain ⟨clauseEvidence, evidenceMember, clauseTyping⟩ :=
        sharedTyping.member membership
      exact ⟨_, clauseEvidence, evidenceMember, clauseTyping⟩

/-! ## Matcher cursor inversion -/

/-- A runtime clause differs from its source clause only by consumed arms. -/
inductive ClauseArmCursor : Clause → Clause → Prop where
  | refl {clause} : ClauseArmCursor clause clause
  | nextArm {pp next arm arms original} :
      ClauseArmCursor (.mk pp next (arm :: arms)) original →
      ClauseArmCursor (.mk pp next arms) original

/-- Consuming arms never changes a clause's primitive pattern or next term. -/
theorem ClauseArmCursor.headers
    {current original : Clause}
    (cursor : ClauseArmCursor current original) :
    current.pp = original.pp ∧ current.next = original.next := by
  induction cursor with
  | refl => exact ⟨rfl, rfl⟩
  | nextArm _ induction => exact induction

/-- Every remaining runtime arm was an arm of the original source clause. -/
theorem ClauseArmCursor.arm_mem
    {current original : Clause}
    (cursor : ClauseArmCursor current original)
    {arm : Arm} (membership : arm ∈ current.arms) :
    arm ∈ original.arms := by
  induction cursor with
  | refl => exact membership
  | @nextArm pp next head arms original previous induction =>
      exact induction (List.mem_cons_of_mem head membership)

/--
Every clause visible through a matcher cursor originates in a concrete source
clause; the only permitted intra-clause change is dropping an arm prefix.
-/
theorem MatcherCursor.member_origin
    {current original : List Clause}
    (cursor : MatcherCursor current original)
    {clause : Clause} (membership : clause ∈ current) :
    ∃ originalClause,
      originalClause ∈ original ∧ ClauseArmCursor clause originalClause := by
  induction cursor generalizing clause with
  | refl => exact ⟨clause, membership, ClauseArmCursor.refl⟩
  | @nextClause pp next arms clauses original previous induction =>
      exact induction (List.mem_cons_of_mem _ membership)
  | @nextArm pp next arm arms clauses original previous induction =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · obtain ⟨sourceClause, sourceMember, sourceCursor⟩ :=
          induction (show Clause.mk pp next (arm :: arms) ∈
            Clause.mk pp next (arm :: arms) :: clauses from List.mem_cons_self)
        exact ⟨sourceClause, sourceMember, ClauseArmCursor.nextArm sourceCursor⟩
      · exact induction (List.mem_cons_of_mem _ membership)

/-- Cursor membership recovers the original clause typing and evidence. -/
theorem MatcherCursor.member_typed
    {signature : FrozenSig} {context : Context}
    {current original : List Clause} {capability : Cap} {target : Ty}
    {evidence : List Shape.Evidence}
    (cursor : MatcherCursor current original)
    (typing : ResolvedClausesTy signature context original capability target
      evidence)
    {clause : Clause} (membership : clause ∈ current) :
    ∃ originalClause prevailing clauseEvidence,
      originalClause ∈ original ∧
      ClauseArmCursor clause originalClause ∧
      clauseEvidence ∈ evidence ∧
      ClauseTy signature prevailing context originalClause capability target
        clauseEvidence := by
  obtain ⟨originalClause, sourceMember, clauseCursor⟩ :=
    cursor.member_origin membership
  obtain ⟨prevailing, clauseEvidence, evidenceMember,
      clauseTyping⟩ := typing.member sourceMember
  exact ⟨originalClause, prevailing, clauseEvidence, sourceMember,
    clauseCursor, evidenceMember, clauseTyping⟩

/-- A current runtime arm retains its exact source data-pattern/body typing. -/
theorem MatcherCursor.arm_typed
    {signature : FrozenSig} {context : Context}
    {current original : List Clause} {capability : Cap} {target : Ty}
    {evidence : List Shape.Evidence}
    (cursor : MatcherCursor current original)
    (typing : ResolvedClausesTy signature context original capability target
      evidence)
    {clause : Clause} (clauseMember : clause ∈ current)
    {arm : Arm} (armMember : arm ∈ clause.arms) :
    ∃ originalClause prevailing clauseEvidence pp holes ppBindings
        nextMatchers result pattern body armBindings,
      originalClause ∈ original ∧
      ClauseArmCursor clause originalClause ∧
      ClauseTy signature prevailing context originalClause capability target
        clauseEvidence ∧
      originalClause.pp = pp ∧
      ResolvedPPatTy signature prevailing pp target holes ppBindings ∧
      PPatCapsAt signature true pp (holes.map Dual.cap) capability ∧
      decomposeME originalClause.next holes.length = some nextMatchers ∧
      ExprsTy signature context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) ∧
      result = Ty.listT (prodTy (holes.map Dual.target)) ∧
      arm = .mk pattern body ∧
      DPatTy signature pattern target armBindings ∧
      RuntimeTyping signature
        (armBindings.toContext ++ ppBindings.toContext ++ context)
        body result := by
  obtain ⟨originalClause, prevailing, clauseEvidence, sourceMember,
      clauseCursor, _evidenceMember, clauseTyping⟩ :=
    cursor.member_typed typing clauseMember
  obtain ⟨holes, pp, next, arms, ppBindings, nextMatchers, rfl,
      ppTyping, ppCaps, decompose, nextTyping, armsTyping, _evidenceCheck⟩ :=
    clauseTyping.checked
  have originalArmMember : arm ∈ arms := clauseCursor.arm_mem armMember
  obtain ⟨pattern, body, armBindings, armEquality, patternTyping,
      bodyTyping⟩ := armsTyping.member originalArmMember
  exact ⟨_, prevailing, clauseEvidence, pp, holes, ppBindings, nextMatchers,
    _, pattern, body, armBindings, sourceMember, clauseCursor, clauseTyping,
    rfl, ppTyping, ppCaps, decompose, nextTyping, rfl, armEquality, patternTyping,
    bodyTyping⟩

/-! ## Exact monomorphic environment typing -/

/-- A runtime environment aligned entry-for-entry with a monomorphic context. -/
inductive MonoEnvTys (signature : FrozenSig) : MonoCtx → Env → Prop where
  | nil : MonoEnvTys signature [] []
  | cons {name target value bindings environment} :
      ValueTy signature value target →
      MonoEnvTys signature bindings environment →
      MonoEnvTys signature
        ((name, target) :: bindings) ((name, value) :: environment)

/-- Entrywise monomorphic environment typing composes over concatenation. -/
theorem MonoEnvTys.append
    {signature : FrozenSig} {leftBindings rightBindings : MonoCtx}
    {leftEnvironment rightEnvironment : Env}
    (left : MonoEnvTys signature leftBindings leftEnvironment)
    (right : MonoEnvTys signature rightBindings rightEnvironment) :
    MonoEnvTys signature (leftBindings ++ rightBindings)
      (leftEnvironment ++ rightEnvironment) := by
  induction left with
  | nil => exact right
  | cons valueTyping _ induction =>
      exact MonoEnvTys.cons valueTyping induction

/-- Exact alignment preserves list lengths. -/
theorem MonoEnvTys.length
    {signature : FrozenSig} {bindings : MonoCtx} {environment : Env}
    (typing : MonoEnvTys signature bindings environment) :
    bindings.length = environment.length := by
  induction typing with
  | nil => rfl
  | cons _ _ induction => simp [induction]

/-- Exact alignment preserves the name sequence. -/
theorem MonoEnvTys.names
    {signature : FrozenSig} {bindings : MonoCtx} {environment : Env}
    (typing : MonoEnvTys signature bindings environment) :
    bindings.names = environment.map Prod.fst := by
  induction typing with
  | nil => rfl
  | cons _ _ induction =>
      simpa only [MonoCtx.names, List.map_cons] using
        congrArg (List.cons _) induction

/-- Exact monomorphic alignment induces ordinary runtime-environment typing. -/
theorem MonoEnvTys.toEnvTyped
    {signature : FrozenSig} {bindings : MonoCtx} {environment : Env}
    (typing : MonoEnvTys signature bindings environment) :
    EnvTyped signature bindings.toContext environment := by
  induction typing with
  | nil =>
      intro name value hfind
      simp [Env.find?] at hfind
  | cons valueTyping _ induction =>
      simpa only [MonoCtx.toContext, List.map_cons] using
        EnvTyped.cons valueTyping induction

/-- Prefix an exact monomorphic environment to an arbitrary typed runtime
environment. -/
theorem MonoEnvTys.envTyped_append
    {signature : FrozenSig} {bindings : MonoCtx} {values : Env}
    {context : Context} {environment : Env}
    (leading : MonoEnvTys signature bindings values)
    (suffix : EnvTyped signature context environment) :
    EnvTyped signature (bindings.toContext ++ context)
      (values ++ environment) := by
  induction leading with
  | nil => simpa [MonoCtx.toContext] using suffix
  | cons valueTyping tailTyping induction =>
      simpa only [MonoCtx.toContext, List.map_cons, List.cons_append] using
        EnvTyped.cons valueTyping induction

/-! ## Matching substitutions as runtime environments -/

/-- A unique monomorphic binding is found at its exact singleton scheme. -/
theorem MonoCtx.find_toContext_of_mem
    {bindings : MonoCtx} {name : String} {target : Ty}
    (nodup : bindings.names.Nodup)
    (membership : (name, target) ∈ bindings) :
    Context.find? bindings.toContext name = some (Scheme.mono target) := by
  induction bindings with
  | nil => contradiction
  | cons head tail induction =>
      obtain ⟨headName, headTarget⟩ := head
      simp only [MonoCtx.names, List.map_cons, List.nodup_cons] at nodup
      obtain ⟨headFresh, tailNodup⟩ := nodup
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · cases equality
        simp [Context.find?, MonoCtx.toContext]
      · have nameMember : name ∈ MonoCtx.names tail :=
          List.mem_map_of_mem membership
        have unequal : headName ≠ name := fun equality =>
          headFresh (equality ▸ nameMember)
        simp only [Context.find?, MonoCtx.toContext, List.map_cons, List.find?]
        rw [show (headName == name) = false by simp [unequal]]
        exact induction tailNodup membership

/-- A successful runtime-environment lookup returns an actual list entry. -/
theorem Env.mem_of_find?_eq_some :
    ∀ {environment : Env} {name : String} {value : Value},
      Env.find? environment name = some value →
      (name, value) ∈ environment := by
  intro environment name value found
  induction environment with
  | nil => simp [Env.find?] at found
  | cons head tail induction =>
      obtain ⟨headName, headValue⟩ := head
      simp only [Env.find?, List.find?] at found
      cases equality : (headName == name) with
      | true =>
          rw [equality] at found
          simp only [Option.map, Option.some.injEq] at found
          have nameEquality : headName = name := by simpa using equality
          subst headName
          subst headValue
          exact List.mem_cons_self
      | false =>
          rw [equality] at found
          exact List.mem_cons_of_mem _ (induction found)

/--
The reversed runtime substitution represents the same finite map as its
unique source binding context, so it is a typed expression environment.
-/
theorem MatchSubstTyped.toEnvTyped
    {signature : FrozenSig} {bindings : MonoCtx}
    {substitution : MatchSubst}
    (typing : MatchSubstTyped signature bindings substitution) :
    EnvTyped signature bindings.toContext substitution := by
  rcases typing with ⟨nodup, namesEquality, valuesTyped⟩
  intro name value found
  have runtimeMember : (name, value) ∈ substitution :=
    Env.mem_of_find?_eq_some found
  have runtimeNameMember : name ∈ substitution.map Prod.fst :=
    List.mem_map_of_mem runtimeMember
  have bindingNameMember : name ∈ bindings.names := by
    rw [namesEquality]
    simpa using runtimeNameMember
  obtain ⟨entry, entryMember, entryName⟩ :=
    List.exists_of_mem_map bindingNameMember
  obtain ⟨bindingName, target⟩ := entry
  simp only at entryName
  subst bindingName
  have contextFind := MonoCtx.find_toContext_of_mem nodup entryMember
  obtain ⟨typedValue, valueFind, valueTyping⟩ :=
    valuesTyped _ entryMember
  have valueEquality : typedValue = value :=
    Option.some.inj (valueFind.symm.trans found)
  subst typedValue
  refine ⟨Scheme.mono target, contextFind, ?_⟩
  intro actual hinstance
  have targetEquality := hinstance.mono_eq
  subst actual
  exact valueTyping

/--
Append one fresh source binding while prefixing its runtime substitution
entry.  This is the exact order reversal used by `MAtom.someVar`.
-/
theorem MatchSubstTyped.snoc_cons
    {signature : FrozenSig} {bindings : MonoCtx}
    {substitution : MatchSubst} {name : String} {target : Ty} {value : Value}
    (typing : MatchSubstTyped signature bindings substitution)
    (fresh : name ∉ bindings.names)
    (valueTyping : ValueTy signature value target) :
    MatchSubstTyped signature (bindings ++ [(name, target)])
      ((name, value) :: substitution) := by
  rcases typing with ⟨nodup, namesEquality, valuesTyped⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show (bindings ++ [(name, target)]).names =
        bindings.names ++ [name] by simp [MonoCtx.names]]
    exact List.nodup_append.mpr ⟨nodup, by simp, by
        intro old oldMember new newMember equality
        simp only [List.mem_singleton] at newMember
        exact fresh ((equality.trans newMember) ▸ oldMember)⟩
  · simpa [MonoCtx.names] using
      congrArg (fun names => names ++ [name]) namesEquality
  · intro entry member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with oldMember | rfl
    · obtain ⟨stored, storedFind, storedTyping⟩ :=
        valuesTyped entry oldMember
      have entryNameMember : entry.1 ∈ bindings.names :=
        List.mem_map_of_mem oldMember
      have unequal : name ≠ entry.1 := fun equality =>
        fresh (equality ▸ entryNameMember)
      refine ⟨stored, ?_, storedTyping⟩
      simp only [Env.find?, List.find?]
      rw [show (name == entry.1) = false by
        exact beq_false_of_ne unequal]
      exact storedFind
    · exact ⟨value, by simp [Env.find?], valueTyping⟩

/-! ## Typed stack composition -/

/-- Typed stacks compose along their threaded binding index. -/
theorem StackTy.append
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input middle output : MonoCtx} {left right : List Tree}
    (leftTyping : StackTy signature context parameters input left middle)
    (rightTyping : StackTy signature context parameters middle right output) :
    StackTy signature context parameters input (left ++ right) output := by
  induction left generalizing input middle with
  | nil =>
      cases leftTyping
      exact rightTyping
  | cons tree trees induction =>
      cases leftTyping with
      | cons treeTyping restTyping =>
          exact .cons treeTyping (induction restTyping rightTyping)

/-- A successful prefix lookup is unchanged by appending an environment. -/
theorem Env.find?_append_left
    {left right : Env} {name : String} {value : Value}
    (found : Env.find? left name = some value) :
    Env.find? (left ++ right) name = some value := by
  unfold Env.find? at found ⊢
  rw [List.find?_append]
  cases raw : List.find? (fun entry => entry.1 == name) left with
  | none => simp [raw] at found
  | some entry =>
      obtain ⟨entryName, entryValue⟩ := entry
      simp [raw] at found ⊢
      exact found

/-- If the prefix misses a name, append lookup is exactly suffix lookup. -/
theorem Env.find?_append_of_none
    {left right : Env} {name : String}
    (missing : Env.find? left name = none) :
    Env.find? (left ++ right) name = Env.find? right name := by
  unfold Env.find? at missing ⊢
  rw [List.find?_append]
  cases raw : List.find? (fun entry => entry.1 == name) left with
  | none => simp
  | some entry => simp [raw] at missing

/-- A successful prefix context lookup survives context concatenation. -/
theorem Context.find?_append_left
    {left right : Context} {name : String} {scheme : Scheme}
    (found : Context.find? left name = some scheme) :
    Context.find? (left ++ right) name = some scheme := by
  unfold Context.find? at found ⊢
  rw [List.find?_append]
  cases raw : List.find? (fun entry => entry.1 == name) left with
  | none => simp [raw] at found
  | some entry =>
      obtain ⟨entryName, entryScheme⟩ := entry
      simp [raw] at found ⊢
      exact found

/-- A missing prefix context delegates lookup to its suffix. -/
theorem Context.find?_append_right
    {left right : Context} {name : String} {scheme : Scheme}
    (missing : Context.find? left name = none)
    (found : Context.find? right name = some scheme) :
    Context.find? (left ++ right) name = some scheme := by
  unfold Context.find? at missing found ⊢
  rw [List.find?_append]
  cases raw : List.find? (fun entry => entry.1 == name) left with
  | none => simpa [raw] using found
  | some entry => simp [raw] at missing

/-- Absence from the concrete runtime domain implies lookup failure. -/
theorem Env.find?_eq_none_of_name_not_mem
    {environment : Env} {name : String}
    (missing : name ∉ environment.map Prod.fst) :
    Env.find? environment name = none := by
  unfold Env.find?
  have raw : List.find? (fun entry => entry.1 == name) environment = none :=
    List.find?_eq_none.mpr (by
      intro entry member equal
      have nameEqual : entry.1 = name := by simpa using equal
      exact missing (nameEqual ▸ List.mem_map_of_mem member))
  rw [raw]
  rfl

/-- Absence from mono bindings implies failure in their source context. -/
theorem MonoCtx.find?_toContext_eq_none
    {bindings : MonoCtx} {name : String}
    (missing : name ∉ bindings.names) :
    Context.find? bindings.toContext name = none := by
  unfold Context.find?
  have raw :
      List.find? (fun entry => entry.1 == name) bindings.toContext = none :=
    List.find?_eq_none.mpr (by
      intro entry member equal
      have nameEqual : entry.1 = name := by simpa using equal
      apply missing
      rw [← nameEqual]
      rcases List.mem_map.mp member with
        ⟨binding, bindingMember, bindingEquality⟩
      exact List.mem_map.mpr ⟨binding, bindingMember,
        congrArg Prod.fst bindingEquality⟩)
  rw [raw]
  rfl

/--
A typed matching substitution may prefix an ordinary typed environment.  The
source and runtime prefixes use opposite list order but denote the same unique
finite map; the prefix shadows the suffix on both sides.
-/
theorem MatchSubstTyped.envTyped_append
    {signature : FrozenSig} {bindings : MonoCtx}
    {substitution : MatchSubst} {context : Context} {environment : Env}
    (substitutionTyping : MatchSubstTyped signature bindings substitution)
    (environmentTyping : EnvTyped signature context environment) :
    EnvTyped signature (bindings.toContext ++ context)
      (substitution ++ environment) := by
  rcases substitutionTyping with ⟨nodup, namesEquality, valuesTyped⟩
  intro name value found
  by_cases inBindings : name ∈ bindings.names
  · obtain ⟨entry, entryMember, entryName⟩ :=
      List.exists_of_mem_map inBindings
    obtain ⟨bindingName, target⟩ := entry
    simp only at entryName
    subst bindingName
    obtain ⟨storedValue, storedFind, storedTyping⟩ :=
      valuesTyped _ entryMember
    have appendFind := Env.find?_append_left
      (right := environment) storedFind
    have valueEquality : storedValue = value :=
      Option.some.inj (appendFind.symm.trans found)
    subst storedValue
    have sourceFind := MonoCtx.find_toContext_of_mem nodup entryMember
    have contextFind := Context.find?_append_left
      (right := context) sourceFind
    refine ⟨Scheme.mono target, contextFind, ?_⟩
    intro actual hinstance
    have targetEquality := hinstance.mono_eq
    subst actual
    exact storedTyping
  · have runtimeNameMissing : name ∉ substitution.map Prod.fst := by
      intro member
      apply inBindings
      rw [namesEquality]
      simpa using member
    have substitutionMissing :=
      Env.find?_eq_none_of_name_not_mem runtimeNameMissing
    have environmentFind : Env.find? environment name = some value := by
      rw [← Env.find?_append_of_none
        (right := environment) substitutionMissing]
      exact found
    obtain ⟨scheme, sourceFind, instances⟩ :=
      environmentTyping name value environmentFind
    have bindingContextMissing := MonoCtx.find?_toContext_eq_none inBindings
    refine ⟨scheme,
      Context.find?_append_right bindingContextMissing sourceFind, ?_⟩
    intro actual hinstance
    apply instances actual
    exact hinstance

/-! ## Canonical constructor values -/

/-! ## Runtime slot-coercion provenance -/

/-!
Advancing the private cursor of a matcher literal does not change its outer
runtime type.  In particular, this transport must preserve a checked slot
derivation itself: after `any` becomes the one-way catch-all demand, the
slot's consumer capability need not be the literal's producer capability.
-/

/-- Dropping a failed head clause preserves the complete outer runtime type. -/
theorem ValueTy.matcher_nextClause
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arms : List Arm}
    {tail : List Clause} {target : Ty}
    (typing : ValueTy signature
      (.matcherV environment original (.mk pp next arms :: tail)) target) :
    ValueTy signature (.matcherV environment original tail) target := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      actualValue =
          .matcherV environment original (.mk pp next arms :: tail) →
        ValueTy signature (.matcherV environment original tail) actualTarget)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing rfl
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro actualEnvironment currentClauses originalClauses capability
      matcherTarget context domain instances source cursor instancesIH equality
    cases equality
    exact .matcherLiteral context domain instances source (.nextClause cursor)
  · intros
    contradiction
  · intros
    contradiction
  · intro value producerCap producerTarget consumerCap consumerTarget
      bindings C T post inner raw postVariable innerIH equality
    cases equality
    exact .matcherToSlot (innerIH rfl) raw postVariable
  · intro value sourceCap sourceTarget requestedCap requestedTarget C T post
      inner raw postVariable innerIH equality
    cases equality
    exact .slotToSlot (innerIH rfl) raw postVariable
  · intros
    contradiction
  · trivial
  · intros
    trivial

/-- Dropping a failed head arm preserves the complete outer runtime type. -/
theorem ValueTy.matcher_nextArm
    {signature : FrozenSig} {environment : Env} {original : List Clause}
    {pp : PPat} {next : Expr} {arm : Arm} {arms : List Arm}
    {clauses : List Clause} {target : Ty}
    (typing : ValueTy signature
      (.matcherV environment original
        (.mk pp next (arm :: arms) :: clauses)) target) :
    ValueTy signature
      (.matcherV environment original (.mk pp next arms :: clauses)) target := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      actualValue = .matcherV environment original
          (.mk pp next (arm :: arms) :: clauses) →
        ValueTy signature
          (.matcherV environment original (.mk pp next arms :: clauses))
          actualTarget)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing rfl
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro actualEnvironment currentClauses originalClauses capability
      matcherTarget context domain instances source cursor instancesIH equality
    cases equality
    exact .matcherLiteral context domain instances source (.nextArm cursor)
  · intros
    contradiction
  · intros
    contradiction
  · intro value producerCap producerTarget consumerCap consumerTarget
      bindings C T post inner raw postVariable innerIH equality
    cases equality
    exact .matcherToSlot (innerIH rfl) raw postVariable
  · intro value sourceCap sourceTarget requestedCap requestedTarget C T post
      inner raw postVariable innerIH equality
    cases equality
    exact .slotToSlot (innerIH rfl) raw postVariable
  · intros
    contradiction
  · trivial
  · intros
    trivial

/-- A successful producer-to-consumer check normalizes both targets identically. -/
theorem matcherToSlot_targets_eq
    {producerTarget consumerTarget : Ty}
    {C : CapSubst} {T : TySubst}
    (unified : Unification.mguTy
      (producerTarget.applyCapability C)
      (consumerTarget.applyCapability C) = some T) :
    (Subst.mk C T).apply producerTarget =
      (Subst.mk C T).apply consumerTarget := by
  simpa only [Subst.apply] using Unification.mguTy_sound unified

/-- A slot-to-slot check likewise gives equal normalized source/request indices. -/
theorem slotToSlot_indices_eq
    {sourceCap requestedCap : Cap}
    {sourceTarget requestedTarget : Ty}
    {C : CapSubst} {T : TySubst}
    (capUnified :
      Unification.mguCap sourceCap requestedCap = some C)
    (targetUnified : Unification.mguTy
      (sourceTarget.applyCapability C)
      (requestedTarget.applyCapability C) = some T) :
    sourceCap.apply C = requestedCap.apply C ∧
      (Subst.mk C T).apply sourceTarget =
        (Subst.mk C T).apply requestedTarget := by
  exact ⟨Unification.mguCap_sound capUnified,
    by simpa only [Subst.apply] using
      Unification.mguTy_sound targetUnified⟩

/-! ## Canonical matcher products -/

/--
Raw one-way matching induces runtime demand evidence against the substituted
consumer.  In particular, the variable case becomes `equal`: even when the
variable's image is `any`, it is not reinterpreted as a wildcard occurrence.
-/
theorem CapabilityDemand.ofDemandMatches (S : CapSubst) :
    ∀ (producer consumer : Cap),
      DemandMatches S producer consumer →
      CapabilityDemand producer (consumer.apply S) := by
  intro producer consumer matching
  exact Cap.rec
    (motive_1 := fun consumer => ∀ producer,
      DemandMatches S producer consumer →
      CapabilityDemand producer (consumer.apply S))
    (motive_2 := fun consumers => ∀ producers,
      DemandMatchesList S producers consumers →
      CapabilityDemands producers (Cap.applyList S consumers))
    (by
      intro _ _
      exact .any)
    (fun varId => by
      intro producer matching
      have equality : S varId = producer := by
        cases producer <;> simpa [DemandMatches] using matching
      rw [Cap.apply, equality]
      exact .equal)
    (fun consumerId => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producerId
      change producerId = consumerId at matching
      rw [matching]
      exact .equal)
    (fun consumerName consumers consumersIH => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producerName producers
      change producerName = consumerName ∧
        DemandMatchesList S producers consumers at matching
      rw [matching.1]
      exact .con (consumersIH producers matching.2))
    (fun consumers consumersIH => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producers
      change DemandMatchesList S producers consumers at matching
      exact .prod (consumersIH producers matching))
    (by
      intro producers matching
      cases producers with
      | nil => exact .nil
      | cons _ _ => contradiction)
    (fun _ _ consumerIH consumersIH => by
      intro producers matching
      cases producers with
      | nil => contradiction
      | cons producer producers =>
          simp only [DemandMatchesList] at matching
          exact .cons (consumerIH producer matching.1)
            (consumersIH producers matching.2))
    consumer producer matching

/-- A declarative one-way witness retains the normalized producer endpoint. -/
theorem CapabilityDemand.ofOneWayAt
    {S : CapSubst} {producer consumer : Cap}
    (matching : OneWayAt S producer consumer) :
    CapabilityDemand (producer.apply S) (consumer.apply S) := by
  rw [matching.2.1]
  exact CapabilityDemand.ofDemandMatches S producer consumer matching.2.2

mutual

/-- Variable renaming preserves runtime demand provenance. -/
theorem CapabilityDemand.applyRen
    {producer consumer : Cap} (ren : CapVar → CapVar)
    (demand : CapabilityDemand producer consumer) :
    CapabilityDemand (producer.applyRen ren)
      (consumer.applyRen ren) := by
  cases demand with
  | equal => exact .equal
  | any => exact .any
  | con children => exact .con (children.applyRen ren)
  | prod components => exact .prod (components.applyRen ren)

/-- List form of `CapabilityDemand.applyRen`. -/
theorem CapabilityDemands.applyRen
    {producers consumers : List Cap} (ren : CapVar → CapVar)
    (demands : CapabilityDemands producers consumers) :
    CapabilityDemands (Cap.applyRenList ren producers)
      (Cap.applyRenList ren consumers) := by
  cases demands with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.applyRen ren) (tail.applyRen ren)

end

/-- The runtime demand carried by a matcher-to-slot raw certificate. -/
theorem MatcherToSlotRawCert.capabilityDemand
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T) :
    CapabilityDemand (producerCap.apply C) (consumerCap.apply C) := by
  rw [raw.capSubstitution]
  exact CapabilityDemand.ofOneWayAt
    (CapMatch.matchCap_restricted_sound raw.matched)

/-- Variable-only solver posts preserve a raw matcher-to-slot demand. -/
theorem MatcherToSlotRawCert.postCapabilityDemand
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    {post : Subst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T)
    (postVariable : VariablePost post) :
    CapabilityDemand ((producerCap.apply C).apply post.cap)
      ((consumerCap.apply C).apply post.cap) := by
  have renamed := raw.capabilityDemand.applyRen postVariable.capRen
  rw [← postVariable.applyCap_eq_applyRen,
    ← postVariable.applyCap_eq_applyRen] at renamed
  exact renamed

/-- Pointwise demand streams compose by append. -/
theorem CapabilityDemands.append : ∀
    {leftProducers leftConsumers rightProducers rightConsumers : List Cap},
    CapabilityDemands leftProducers leftConsumers →
    CapabilityDemands rightProducers rightConsumers →
    CapabilityDemands (leftProducers ++ rightProducers)
      (leftConsumers ++ rightConsumers)
  | [], [], _, _, .nil, right => right
  | _ :: _, _ :: _, _, _, .cons head tail, right =>
      .cons head (CapabilityDemands.append tail right)

/-- A product consumer exposes pointwise producer demands. -/
theorem CapabilityDemand.prod_inversion
    {producer : Cap} {consumers : List Cap}
    (demand : CapabilityDemand producer (.prod consumers)) :
    ∃ producers,
      producer = .prod producers ∧ CapabilityDemands producers consumers := by
  cases demand with
  | equal => exact ⟨consumers, rfl, CapabilityDemand.equalList consumers⟩
  | prod children => exact ⟨_, rfl, children⟩

/-- A constructor consumer exposes pointwise producer demands at the same head. -/
theorem CapabilityDemand.con_inversion
    {producer : Cap} {name : String} {consumers : List Cap}
    (demand : CapabilityDemand producer (.con name consumers)) :
    ∃ producers,
      producer = .con name producers ∧ CapabilityDemands producers consumers := by
  cases demand with
  | equal => exact ⟨consumers, rfl, CapabilityDemand.equalList consumers⟩
  | con children => exact ⟨_, rfl, children⟩

mutual

/-- Runtime demand compatibility composes without erasing explicit `any` nodes. -/
theorem CapabilityDemand.trans
    {producer middle consumer : Cap}
    (first : CapabilityDemand producer middle)
    (second : CapabilityDemand middle consumer) :
    CapabilityDemand producer consumer := by
  cases second with
  | equal => exact first
  | any => exact .any
  | @con name middleChildren consumerChildren children =>
      obtain ⟨producerChildren, rfl, firstChildren⟩ := first.con_inversion
      exact .con (CapabilityDemands.trans firstChildren children)
  | @prod middleChildren consumerChildren children =>
      obtain ⟨producerChildren, rfl, firstChildren⟩ := first.prod_inversion
      exact .prod (CapabilityDemands.trans firstChildren children)

/-- Pointwise runtime demand compatibility composes. -/
theorem CapabilityDemands.trans
    {producers middle consumers : List Cap}
    (first : CapabilityDemands producers middle)
    (second : CapabilityDemands middle consumers) :
    CapabilityDemands producers consumers := by
  cases second with
  | nil =>
      cases first
      exact .nil
  | cons secondHead secondTail =>
      cases first with
      | cons firstHead firstTail =>
          exact .cons (CapabilityDemand.trans firstHead secondHead)
            (CapabilityDemands.trans firstTail secondTail)

end

/-- Pointwise exact usability of runtime matcher components. -/
inductive MatcherUsables (signature : FrozenSig) :
    List Value → List Dual → Prop where
  | nil : MatcherUsables signature [] []
  | cons {value values dual duals} :
      MatcherUsable signature value dual.cap dual.target →
      MatcherUsables signature values duals →
      MatcherUsables signature (value :: values) (dual :: duals)

/-- Pointwise matcher usability retains exact component arity. -/
theorem MatcherUsables.length
    {signature : FrozenSig} {values : List Value} {duals : List Dual}
    (typing : MatcherUsables signature values duals) :
    values.length = duals.length := by
  induction typing with
  | nil => rfl
  | cons head tail induction => simp only [List.length_cons, induction]

/--
Expose the producer capabilities hidden by a pointwise consumer view.  Target
indices are unchanged; only capabilities participate in one-way demand.
-/
theorem MatcherUsables.hiddenProducers
    {signature : FrozenSig} {values : List Value} {consumers : List Dual}
    (typing : MatcherUsables signature values consumers) :
    ∃ producers : List Dual,
      ValueTys signature values
        (producers.map fun dual => .matcher dual.cap dual.target) ∧
      CapabilityDemands
        (producers.map Dual.cap) (consumers.map Dual.cap) ∧
      producers.map Dual.target = consumers.map Dual.target := by
  induction typing with
  | nil => exact ⟨[], .nil, .nil, rfl⟩
  | @cons value values consumer consumers head tail induction =>
      obtain ⟨producerCapability, headTyping, headDemand⟩ := head
      obtain ⟨producers, producerTyping, demands, targets⟩ := induction
      let producer : Dual :=
        ⟨producerCapability, consumer.target⟩
      refine ⟨producer :: producers, ?_, ?_, ?_⟩
      · exact .cons headTyping producerTyping
      · exact .cons headDemand demands
      · simp only [List.map_cons, producer,
          List.cons.injEq, true_and]
        exact targets

/-- Exact producer matcher components are usable at their declared duals. -/
theorem ValueTys.matcherUsables
    {signature : FrozenSig} {values : List Value} {duals : List Dual}
    (typing : ValueTys signature values
      (duals.map fun dual => .matcher dual.cap dual.target)) :
    MatcherUsables signature values duals := by
  induction duals generalizing values with
  | nil =>
      cases typing
      exact .nil
  | cons dual duals induction =>
      cases typing with
      | cons head tail => exact .cons (.ofMatcher head) (induction tail)

/--
Recover matcher origins from a checked runtime slot.  Frozen-signature
well-formedness rules out an ill-formed data constructor whose declared result
is itself a slot; the three genuine slot constructors retain all provenance
needed for the remaining cases.
-/
theorem ValueTy.toMatcherUsable
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {value : Value} {capability : Cap} {target : Ty}
    (typing : ValueTy signature value (.slot capability target)) :
    MatcherUsable signature value capability target := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      ∀ requestedCapability requestedTarget,
        actualTarget = .slot requestedCapability requestedTarget →
        MatcherUsable signature actualValue requestedCapability
          requestedTarget)
    (motive_2 := fun actualValues actualTargets _ =>
      ∀ requestedDuals,
        actualTargets = requestedDuals.map
          (fun dual => .slot dual.cap dual.target) →
        MatcherUsables signature actualValues requestedDuals)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    typing capability target rfl
  · intros
    contradiction
  · intro name scheme values targets result found instantiation valuesTyping _
      requestedCapability requestedTarget equality
    obtain ⟨former, arguments, resultEquality⟩ :=
      signatureWF.dataResult found instantiation
    rw [resultEquality] at equality
    cases equality
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro value producerCap producerTarget consumerCap consumerTarget
      bindings C T post inner raw postVariable _ requestedCapability
      requestedTarget equality
    cases equality
    have producerTyping := inner
    have targetEquality := matcherToSlot_targets_eq raw.targetUnified
    rw [targetEquality] at producerTyping
    exact ⟨_, producerTyping, raw.postCapabilityDemand postVariable⟩
  · intro value sourceCap sourceTarget requestedCap requestedTarget C T post
      inner raw postVariable innerIH requestedCapability actualTarget equality
    cases equality
    have sourceUsable := innerIH _ _ rfl
    have indexEquality := slotToSlot_indices_eq raw.capabilityUnified
      raw.targetUnified
    have capabilityEquality := congrArg
      (fun current => current.apply post.cap) indexEquality.1
    have targetEquality := congrArg post.apply indexEquality.2
    rw [capabilityEquality, targetEquality] at sourceUsable
    exact sourceUsable
  · intro values duals componentTyping componentIH requestedCapability
      requestedTarget equality
    cases equality
    have components := componentIH duals rfl
    obtain ⟨producers, producerTyping, demands, targetEquality⟩ :=
      components.hiddenProducers
    refine ⟨.prod (producers.map Dual.cap), ?_, .prod demands⟩
    rw [← targetEquality]
    exact .matcherProduct producerTyping
  · intro requestedDuals equality
    cases requestedDuals with
    | nil => exact .nil
    | cons head tail => simp at equality
  · intro value actualTarget values actualTargets head tail headIH tailIH
      requestedDuals equality
    cases requestedDuals with
    | nil => simp at equality
    | cons requested rest =>
        simp only [List.map_cons, List.cons.injEq] at equality
        exact .cons (headIH _ _ equality.1) (tailIH rest equality.2)

/-- Exact slot components are usable at their declared duals. -/
theorem ValueTys.slotUsables
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {values : List Value} {duals : List Dual}
    (typing : ValueTys signature values
      (duals.map fun dual => .slot dual.cap dual.target)) :
    MatcherUsables signature values duals := by
  induction duals generalizing values with
  | nil =>
      cases typing
      exact .nil
  | cons dual duals induction =>
      cases typing with
      | cons head tail =>
          exact .cons (head.toMatcherUsable signatureWF) (induction tail)

/-- Capability and target projections jointly determine a dual list. -/
theorem Dual.list_eq_of_maps_eq :
    ∀ {left right : List Dual},
      left.map Dual.cap = right.map Dual.cap →
      left.map Dual.target = right.map Dual.target →
      left = right := by
  intro left
  induction left with
  | nil =>
      intro right capEquality targetEquality
      cases right with
      | nil => rfl
      | cons head tail => simp at capEquality
  | cons head tail induction =>
      intro right capEquality targetEquality
      cases right with
      | nil => simp at capEquality
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at capEquality targetEquality
          obtain ⟨capHead, capTail⟩ := capEquality
          obtain ⟨targetHead, targetTail⟩ := targetEquality
          cases head with
          | mk headCap headTarget =>
              cases other with
              | mk otherCap otherTarget =>
                  change headCap = otherCap at capHead
                  change headTarget = otherTarget at targetHead
                  subst otherCap
                  subst otherTarget
                  exact congrArg (Dual.mk headCap headTarget :: ·)
                    (induction capTail targetTail)

/-- Pointwise matcher origins compose with a later consumer-demand stream. -/
theorem MatcherUsables.weaken
    {signature : FrozenSig} {values : List Value}
    {producers consumers : List Dual}
    (typing : MatcherUsables signature values producers)
    (demands : CapabilityDemands
      (producers.map Dual.cap) (consumers.map Dual.cap))
    (targets : producers.map Dual.target = consumers.map Dual.target) :
    MatcherUsables signature values consumers := by
  induction consumers generalizing producers values with
  | nil =>
      cases producers with
      | nil =>
          cases typing
          exact .nil
      | cons producer producers =>
          cases demands
  | cons consumer consumers induction =>
      cases producers with
      | nil =>
          cases demands
      | cons producer producers =>
          cases typing with
          | cons head tail =>
              obtain ⟨hiddenCapability, hiddenTyping, hiddenDemand⟩ := head
              cases demands with
              | cons headDemand tailDemands =>
                  simp only [List.map_cons, List.cons.injEq] at targets
                  rcases targets with ⟨headTarget, tailTargets⟩
                  cases producer with
                  | mk producerCapability producerTarget =>
                      cases consumer with
                      | mk consumerCapability consumerTarget =>
                          dsimp only [Dual.target] at headTarget
                          subst consumerTarget
                          exact .cons
                            ⟨hiddenCapability, hiddenTyping,
                              hiddenDemand.trans headDemand⟩
                            (induction tail tailDemands tailTargets)

/-- A matcher-product typing of a runtime tuple exposes its exact component
duals without dependent elimination on the mapped capability/target indices. -/
theorem ValueTy.tupleMatcher_inversion
    {signature : FrozenSig} {values : List Value}
    {capabilities : List Cap} {targets : List Ty}
    (typing : ValueTy signature (.tuple values)
      (.matcher (.prod capabilities) (.prod targets))) :
    ∃ duals : List Dual,
      ValueTys signature values
        (duals.map fun dual => .matcher dual.cap dual.target) ∧
      duals.map Dual.cap = capabilities ∧
      duals.map Dual.target = targets := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      actualValue = .tuple values →
      actualTarget = .matcher (.prod capabilities) (.prod targets) →
      ∃ duals : List Dual,
        ValueTys signature values
          (duals.map fun dual => .matcher dual.cap dual.target) ∧
        duals.map Dual.cap = capabilities ∧
        duals.map Dual.target = targets)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing rfl rfl
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro actualValues actualDuals componentTyping _ valueEquality
      targetEquality
    cases valueEquality
    simp only [Ty.matcher.injEq, Cap.prod.injEq, Ty.prod.injEq] at targetEquality
    exact ⟨actualDuals, componentTyping, targetEquality.1,
      targetEquality.2⟩
  · intro value producerCap producerTarget consumerCap consumerTarget
      bindings C T post inner raw postVariable _ valueEquality targetEquality
    cases targetEquality
  · intro value sourceCap sourceTarget requestedCap requestedTarget C T post
      inner raw postVariable _ valueEquality targetEquality
    cases targetEquality
  · intro actualValues actualDuals componentTyping _ valueEquality
      targetEquality
    cases targetEquality
  · exact True.intro
  · intros
    exact True.intro

/-- A demanded product matcher exposes demand-compatible components. -/
theorem ValueTy.tupleMatcherUsables
    {signature : FrozenSig} {values : List Value} {duals : List Dual}
    (typing : MatcherUsable signature (.tuple values)
      (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))) :
    MatcherUsables signature values duals := by
  obtain ⟨producerCapability, producerTyping, demand⟩ := typing
  obtain ⟨producerCaps, producerShape, componentDemands⟩ :=
    demand.prod_inversion
  subst producerCapability
  obtain ⟨producerDuals, componentTyping, capEquality, targetEquality⟩ :=
    producerTyping.tupleMatcher_inversion
  rw [← capEquality] at componentDemands
  exact componentTyping.matcherUsables.weaken componentDemands targetEquality

/--
An actual terminal pattern-list resolution, usable matchers, and typed values
form the concrete continuation stack at exactly the terminal indices.
-/
theorem TerminalPatternResolutions.atomStack
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patterns : List Pattern}
    {duals : List Dual} {matchers values : List Value}
    (resolutions : TerminalPatternResolutions signature prevailing context
      parameters input patterns duals output)
    (matcherTyping : MatcherUsables signature matchers duals)
    (valueTyping : ValueTys signature values (duals.map Dual.target)) :
    StackTy signature context parameters input
      ((patterns.zip (matchers.zip values)).map fun entry =>
        Tree.atom ⟨entry.1, entry.2.1, entry.2.2⟩)
      output := by
  induction patterns generalizing input output duals matchers values with
  | nil =>
      cases resolutions with
      | nil =>
          cases matcherTyping
          cases valueTyping
          exact .nil
  | cons pattern patterns induction =>
      cases resolutions with
      | cons head tail =>
          cases matcherTyping with
          | cons matcherHead matcherTail =>
              cases valueTyping with
              | cons valueHead valueTail =>
                  exact .cons
                    (.atom (.mk (.ofTerminal head) matcherHead valueHead))
                    (induction tail matcherTail valueTail)

/-- Recover the hidden producer of a usable concrete matcher literal. -/
theorem ValueTy.matcherUsable_asMatcher
    {signature : FrozenSig} {environment : Env}
    {original current : List Clause} {capability : Cap} {target : Ty}
    (typing : MatcherUsable signature
      (.matcherV environment original current) capability target) :
    ∃ producerCapability,
      ValueTy signature (.matcherV environment original current)
        (.matcher producerCapability target) := by
  obtain ⟨producerCapability, producerTyping, _⟩ := typing
  exact ⟨producerCapability, producerTyping⟩

/-- Covered source evidence is indexed by the hidden producer, not the demand. -/
theorem ValueTy.coveredMatcherUsable_inversion
    {signature : FrozenSig} {environment : Env}
    {original current : List Clause} {capability : Cap} {target : Ty}
    (typing : MatcherUsable signature
      (.matcherV environment original current) capability target) :
    ∃ producerCapability,
      CoveredMatcherLiteralView signature environment original current
        producerCapability target ∧
      CapabilityDemand producerCapability capability := by
  obtain ⟨producerCapability, producerTyping, demand⟩ := typing
  exact ⟨producerCapability,
    producerTyping.coveredMatcherLiteral_inversion, demand⟩

/--
Invert a concrete constructor value at a declared constructor instance.  The
field-target uniqueness premise is the exact frozen-signature condition used
to align the runtime and source instantiations.
-/
theorem ValueTy.ctor_inversion
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {name : String} {scheme : CtorScheme} {values : List Value}
    {targets : List Ty} {result : Ty}
    (typing : ValueTy signature (.ctor name values) result)
    (hfind : signature.findDataCtor name = some scheme)
    (hinstance : scheme.Inst targets result) :
    ValueTys signature values targets := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      ∀ {requestedName : String} {requestedScheme : CtorScheme}
        {requestedValues : List Value} {requestedTargets : List Ty}
        {requestedResult : Ty},
        actualValue = .ctor requestedName requestedValues →
        actualTarget = requestedResult →
        signature.findDataCtor requestedName = some requestedScheme →
        requestedScheme.Inst requestedTargets requestedResult →
        ValueTys signature requestedValues requestedTargets)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    typing rfl rfl hfind hinstance
  · intros
    contradiction
  · intro actualName actualScheme actualValues actualTargets actualResult
      actualFind actualInstance actualValuesTyping _ requestedName
      requestedScheme requestedValues requestedTargets requestedResult
      valueEquality targetEquality requestedFind requestedInstance
    cases valueEquality
    cases targetEquality
    have schemeEquality : requestedScheme = actualScheme :=
      Option.some.inj (requestedFind.symm.trans actualFind)
    subst requestedScheme
    have targetsEquality : requestedTargets = actualTargets :=
      signatureWF.dataInstArgsUnique actualFind requestedInstance
        actualInstance
    subst requestedTargets
    exact actualValuesTyping
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro value producerCap producerTarget consumerCap consumerTarget
      bindings C T post inner raw postVariable _ requestedName
      requestedScheme requestedValues requestedTargets requestedResult
      valueEquality targetEquality requestedFind requestedInstance
    obtain ⟨former, arguments, dataEquality⟩ :=
      signatureWF.dataResult requestedFind requestedInstance
    rw [dataEquality] at targetEquality
    cases targetEquality
  · intro value sourceCap sourceTarget requestedCap requestedTarget C T
      post inner raw postVariable _
      requestedName requestedScheme requestedValues requestedTargets
      requestedResult valueEquality targetEquality requestedFind
      requestedInstance
    obtain ⟨former, arguments, dataEquality⟩ :=
      signatureWF.dataResult requestedFind requestedInstance
    rw [dataEquality] at targetEquality
    cases targetEquality
  · intros
    contradiction
  · trivial
  · intros
    trivial

/-! ## Canonical products, tuples, and lists -/

/-- The syntactic next-matcher decomposition reconstructs the corresponding
`prodTy` source judgment. -/
theorem decomposeME_typed
    {signature : FrozenSig} {context : Context}
    {next : Expr} {expressions : List Expr} {targets : List Ty}
    (decomposition : decomposeME next targets.length = some expressions)
    (typing : ExprsTy signature context expressions targets) :
    RuntimeTyping signature context next (prodTy targets) := by
  cases targets with
  | nil =>
      cases next <;> simp [decomposeME] at decomposition
      rename_i tupleExpressions
      cases tupleExpressions with
      | nil =>
          simp at decomposition
          subst expressions
          exact .tuple typing
      | cons expression expressions => simp at decomposition
  | cons target rest =>
      cases rest with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            decomposeME, Option.some.injEq] at decomposition
          subst expressions
          cases typing with
          | cons head tail =>
              cases tail
              exact head
      | cons second tail =>
          cases next <;> simp [decomposeME] at decomposition
          rename_i tupleExpressions
          rcases decomposition with ⟨length, rfl⟩
          exact .tuple typing

/-- No runtime value inhabits the zero-component product encoding `unit`. -/
theorem ValueTy.unit_impossible
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {value : Value} (typing : ValueTy signature value .unit) : False := by
  refine ValueTy.rec
    (motive_1 := fun _ target _ => target = .unit → False)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing rfl
  · intros
    contradiction
  · intro name scheme values targets result hfind hinst _ _ equality
    obtain ⟨former, arguments, resultEquality⟩ :=
      signatureWF.dataResult hfind hinst
    rw [resultEquality] at equality
    cases equality
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · trivial
  · intros
    trivial

/--
Successful tuple decoding at the source product arity returns exactly the
fields typed by that product.  The arity-one representation is the value
itself; arity zero is ruled out by `ValueTy.unit_impossible`.
-/
theorem decodeTuple_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {value : Value} {targets : List Ty} {values : List Value}
    (typing : ValueTy signature value (prodTy targets))
    (decoding : decodeTuple targets.length value = some values) :
    ValueTys signature values targets := by
  cases targets with
  | nil =>
      obtain ⟨tupleValues, valueEquality, valuesTyping⟩ :=
        ValueTy.product_inversion signatureWF typing
      subst value
      cases valuesTyping
      simp [decodeTuple] at decoding
      subst values
      exact ValueTys.nil
  | cons target rest =>
      cases rest with
      | nil =>
          simp only [decodeTuple, List.length_cons, List.length_nil,
            Nat.reduceAdd, beq_self_eq_true, if_true,
            Option.some.injEq] at decoding
          subst values
          exact .cons typing .nil
      | cons second tail =>
          simp only [prodTy] at typing
          obtain ⟨tupleValues, valueEquality, valuesTyping⟩ :=
            ValueTy.product_inversion signatureWF typing
          subst value
          simp [decodeTuple] at decoding
          rcases decoding with ⟨_, rfl⟩
          exact valuesTyping

/-- Successful tuple decoding returns exactly the requested arity. -/
theorem decodeTuple_length
    {k : Nat} {value : Value} {values : List Value}
    (decoding : decodeTuple k value = some values) :
    values.length = k := by
  unfold decodeTuple at decoding
  split at decoding
  · rename_i one
    simp only [beq_iff_eq] at one
    simp only [Option.some.injEq] at decoding
    subst values
    simpa using one.symm
  · cases value <;> simp_all
    rcases decoding with ⟨length, rfl⟩
    exact length

/-- Every component list returned by `mapM decodeTuple` has the same arity. -/
theorem decodeTuple_mapM_member :
    ∀ {inputs : List Value} {outputs : List (List Value)} {k : Nat},
      inputs.mapM (decodeTuple k) = some outputs →
      ∀ output ∈ outputs, output.length = k := by
  intro inputs outputs k decoding
  induction inputs generalizing outputs with
  | nil =>
      simp at decoding
      subst outputs
      intro output member
      contradiction
  | cons input inputs induction =>
      simp only [List.mapM_cons] at decoding
      cases headDecode : decodeTuple k input with
      | none => simp [headDecode] at decoding
      | some headOutput =>
          cases tailDecode : List.mapM (decodeTuple k) inputs with
          | none => simp [headDecode, tailDecode] at decoding
          | some tailOutputs =>
              simp [headDecode, tailDecode] at decoding
              subst outputs
              intro output member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact decodeTuple_length headDecode
              · exact induction tailDecode output member

/-- Pointwise tuple decoding preserves the exact component target stream. -/
theorem decodeTuple_mapM_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature) :
    ∀ {inputs : List Value} {outputs : List (List Value)}
      {targets : List Ty},
      ValueTys signature inputs
        (List.replicate inputs.length (prodTy targets)) →
      inputs.mapM (decodeTuple targets.length) = some outputs →
      ∀ output ∈ outputs, ValueTys signature output targets := by
  intro inputs outputs targets inputsTyping decoding
  induction inputs generalizing outputs with
  | nil =>
      simp at decoding
      subst outputs
      intro output membership
      contradiction
  | cons input inputs induction =>
      cases inputsTyping with
      | cons inputTyping inputsTyping =>
          simp only [List.mapM_cons] at decoding
          cases headDecode : decodeTuple targets.length input with
          | none => simp [headDecode] at decoding
          | some headOutput =>
              cases tailDecode : inputs.mapM (decodeTuple targets.length) with
              | none => simp [headDecode, tailDecode] at decoding
              | some tailOutputs =>
                  simp [headDecode, tailDecode] at decoding
                  subst outputs
                  intro output membership
                  simp only [List.mem_cons] at membership
                  rcases membership with rfl | membership
                  · exact decodeTuple_typed signatureWF inputTyping headDecode
                  · exact induction inputsTyping tailDecode output membership

/-- Decoding a typed core list returns pointwise typed elements. -/
theorem listOfV_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature) :
    ∀ {value : Value} {target : Ty} {values : List Value},
      ValueTy signature value (Ty.listT target) →
      listOfV value = some values →
      ValueTys signature values (List.replicate values.length target) := by
  obtain ⟨nilScheme, nilFind, nilInst⟩ :=
    signatureWF.listSigWF.nilDeclared
  obtain ⟨consScheme, consFind, consInst⟩ :=
    signatureWF.listSigWF.consDeclared
  let P : Value → Prop := fun value =>
    ∀ {target : Ty} {values : List Value},
      ValueTy signature value (Ty.listT target) →
      listOfV value = some values →
      ValueTys signature values (List.replicate values.length target)
  refine Value.rec
    (motive_1 := P)
    (motive_2 := fun fields => ∀ value ∈ fields, P value)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro literal target values typing decoding
    simp [listOfV] at decoding
  · intro name fields fieldsIH target values typing decoding
    by_cases nilName : name = "nil"
    · subst name
      cases fields with
      | nil =>
          simp only [listOfV, Option.some.injEq] at decoding
          subst values
          exact ValueTys.nil
      | cons head tail =>
          simp [listOfV] at decoding
    · by_cases consName : name = "cons"
      · subst name
        cases fields with
        | nil => simp [listOfV] at decoding
        | cons head tail =>
            cases tail with
            | nil => simp [listOfV] at decoding
            | cons rest tailTail =>
                cases tailTail with
                | cons third more => simp [listOfV] at decoding
                | nil =>
                    have fieldTyping := ValueTy.ctor_inversion signatureWF typing
                      consFind (consInst target)
                    cases fieldTyping with
                    | cons headTyping fieldTyping =>
                        cases fieldTyping with
                        | cons restTyping fieldTyping =>
                            cases fieldTyping
                            cases restDecode : listOfV rest with
                            | none => simp [listOfV, restDecode] at decoding
                            | some restValues =>
                                simp [listOfV, restDecode] at decoding
                                subst values
                                have restIH : P rest :=
                                  fieldsIH rest (by simp)
                                have typedRest := restIH restTyping restDecode
                                simpa [List.replicate_succ] using
                                  ValueTys.cons headTyping typedRest
      · simp [listOfV, nilName, consName] at decoding
  · intro fields _ target values typing decoding
    simp [listOfV] at decoding
  · intro self environment parameter body _ target values typing decoding
    simp [listOfV] at decoding
  · intro environment originalClauses currentClauses _ target values typing
      decoding
    simp [listOfV] at decoding
  · intro target values typing decoding
    simp [listOfV] at decoding
  · intro value membership
    contradiction
  · intro head tail headIH tailIH value membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact headIH
    · exact tailIH value membership
  · trivial
  · intros
    trivial
  · intros
    trivial

/-- Encoding pointwise typed elements produces a typed core list. -/
theorem mkListV_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {target : Ty} : ∀ {values : List Value},
      ValueTys signature values (List.replicate values.length target) →
      ValueTy signature (mkListV values) (Ty.listT target) := by
  obtain ⟨nilScheme, nilFind, nilInst⟩ :=
    signatureWF.listSigWF.nilDeclared
  obtain ⟨consScheme, consFind, consInst⟩ :=
    signatureWF.listSigWF.consDeclared
  intro values typing
  induction values with
  | nil =>
      exact ValueTy.ctor nilFind (nilInst target) ValueTys.nil
  | cons value values induction =>
      simp [List.replicate_succ] at typing
      cases typing with
      | cons valueTyping valuesTyping =>
          exact ValueTy.ctor consFind (consInst target)
            (.cons valueTyping (.cons (induction valuesTyping) .nil))

/-! ## Primitive data-pattern matching -/

/--
The conservative core exhaustiveness checker is sound for the concrete
matcher: a successful check identifies an arm pattern that succeeds on every
value (independently of its type).
-/
theorem basicArmExhaustive_sound
    {patterns : List DPat} {target : Ty} {value : Value}
    (checked : basicArmExhaustive patterns target = true) :
    ∃ pattern, pattern ∈ patterns ∧
      ∃ environment, pdMatch pattern value = some environment := by
  induction patterns with
  | nil => simp [basicArmExhaustive] at checked
  | cons pattern patterns induction =>
      cases pattern with
      | var name =>
          exact ⟨.var name, List.mem_cons_self, [(name, value)], rfl⟩
      | wild =>
          exact ⟨.wild, List.mem_cons_self, [], rfl⟩
      | ctor name fields =>
          simp only [basicArmExhaustive, List.any_cons, DPat.isIrrefutable,
            Bool.false_or] at checked
          obtain ⟨found, member, environment, matching⟩ := induction checked
          exact ⟨found, List.mem_cons_of_mem _ member, environment, matching⟩
      | tuple fields =>
          simp only [basicArmExhaustive, List.any_cons, DPat.isIrrefutable,
            Bool.false_or] at checked
          obtain ⟨found, member, environment, matching⟩ := induction checked
          exact ⟨found, List.mem_cons_of_mem _ member, environment, matching⟩

/-! ## Pristineness of primitive data matching -/

mutual

/-- Data matching stores only subvalues of its pristine input. -/
theorem pdMatch_pristine :
    ∀ {pattern : DPat} {value : Value} {environment : Env},
      ValuePristine value →
      pdMatch pattern value = some environment →
      EnvPristine environment
  | .var name, value, environment, valuePristine, matching => by
      simp only [pdMatch, Option.some.injEq] at matching
      subst environment
      exact .cons valuePristine .nil
  | .wild, value, environment, valuePristine, matching => by
      simp only [pdMatch, Option.some.injEq] at matching
      subst environment
      exact .nil
  | .ctor name patterns, value, environment, valuePristine, matching => by
      cases value with
      | ctor valueName values =>
          cases valuePristine with
          | ctor valuesPristine =>
              simp only [pdMatch] at matching
              split at matching
              · exact pdMatchList_pristine valuesPristine matching
              · contradiction
      | lit => simp [pdMatch] at matching
      | tuple => simp [pdMatch] at matching
      | closure => simp [pdMatch] at matching
      | matcherV => simp [pdMatch] at matching
      | something => simp [pdMatch] at matching
  | .tuple patterns, value, environment, valuePristine, matching => by
      cases value with
      | tuple values =>
          cases valuePristine with
          | tuple valuesPristine =>
              exact pdMatchList_pristine valuesPristine matching
      | lit => simp [pdMatch] at matching
      | ctor => simp [pdMatch] at matching
      | closure => simp [pdMatch] at matching
      | matcherV => simp [pdMatch] at matching
      | something => simp [pdMatch] at matching

/-- List data matching preserves pointwise pristineness. -/
theorem pdMatchList_pristine :
    ∀ {patterns : List DPat} {values : List Value} {environment : Env},
      ValuesPristine values →
      pdMatchList patterns values = some environment →
      EnvPristine environment
  | [], values, environment, valuesPristine, matching => by
      cases values with
      | nil =>
          simp only [pdMatchList, Option.some.injEq] at matching
          subst environment
          exact .nil
      | cons value values => simp [pdMatchList] at matching
  | pattern :: patterns, values, environment, valuesPristine, matching => by
      cases values with
      | nil => simp [pdMatchList] at matching
      | cons value values =>
          cases valuesPristine with
          | cons valuePristine valuesPristine =>
              simp only [pdMatchList] at matching
              cases headMatch : pdMatch pattern value with
              | none => simp [headMatch] at matching
              | some headEnvironment =>
                  cases tailMatch : pdMatchList patterns values with
                  | none => simp [headMatch, tailMatch] at matching
                  | some tailEnvironment =>
                      simp [headMatch, tailMatch] at matching
                      subst environment
                      exact (pdMatch_pristine valuePristine headMatch).append
                        (pdMatchList_pristine valuesPristine tailMatch)

end

/-! ## Primitive-pattern capture typing -/

/-!
PPM capture typing must retain both halves of every dual.  Target agreement
alone is insufficient: it would allow a continuation to consume a next
matcher at an unrelated capability.  The only exception is a bare *root*
hole, which is handled by the primitive/catch-all atom rule; nested holes are
exactly aligned below.
-/

/--
Every non-catch-all PP success captures patterns at the exact hole capability
and target streams.  The auxiliary list motive follows the independent PP
target and capability derivations in lockstep without identifying their raw
provenance lists.
-/
theorem PatternTy.ptuple_inv
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patterns : List Pattern}
    {capabilities : List Cap} {targets : List Ty}
    (typing : PatternTy signature context parameters input (.ptuple patterns)
      (.prod capabilities) (.prod targets) output) :
    ∃ duals,
      PatternTys signature context parameters input patterns duals output ∧
      duals.map Dual.cap = capabilities ∧
      duals.map Dual.target = targets := by
  cases typing with
  | tuple children =>
      exact ⟨_, children, Cap.prod.inj rfl, Ty.prod.inj rfl⟩

/-- Invert tuple capability alignment without dependent elimination on its
outer capability index. -/
theorem PPatCapsAt.tuple_inv
    {signature : FrozenSig} {atRoot : Bool} {patterns : List PPat}
    {holeCapabilities : List Cap} {outerCapability : Cap}
    (typing : PPatCapsAt signature atRoot (.tuple patterns) holeCapabilities
      outerCapability) :
    ∃ childCapabilities,
      PPatCapsList signature patterns holeCapabilities childCapabilities ∧
      outerCapability = .prod childCapabilities := by
  cases typing with
  | tuple children => exact ⟨_, children, rfl⟩

/-- Invert an aligned tuple pattern while retaining the identity-resolution
alternative explicitly. -/
theorem PatternResolution.ptuple_cases
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {patterns : List Pattern} {rawCapability : Cap} {rawTarget : Ty}
    (resolution : PatternResolution signature prevailing context parameters
      input (.ptuple patterns) rawCapability rawTarget output) :
    (prevailing = Subst.id ∧
      PatternTy signature context parameters input (.ptuple patterns)
        rawCapability rawTarget output) ∨
    ∃ rawDuals,
      PatternResolutions signature prevailing context parameters input
        patterns rawDuals output ∧
      rawCapability = .prod (rawDuals.map Dual.cap) ∧
      rawTarget = .prod (rawDuals.map Dual.target) := by
  cases resolution with
  | identity equality typing => exact .inl ⟨equality, typing⟩
  | tuple children => exact .inr ⟨_, children, rfl, rfl⟩

/-- Mapping the identity substitution over raw targets is pointwise identity. -/
@[simp] theorem Subst.map_apply_id (targets : List Ty) :
    targets.map Subst.id.apply = targets := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp [Subst.apply_id, induction]

/-- Capability substitution distributes through products as a pointwise map. -/
theorem Cap.applyList_eq_map_local (substitution : CapSubst) :
    ∀ capabilities,
      Cap.applyList substitution capabilities =
        capabilities.map fun capability => capability.apply substitution
  | [] => rfl
  | capability :: capabilities => by
      change capability.apply substitution ::
          Cap.applyList substitution capabilities =
        capability.apply substitution ::
          capabilities.map (fun child => child.apply substitution)
      rw [Cap.applyList_eq_map_local substitution capabilities]

theorem Cap.apply_prod_map (substitution : CapSubst)
    (capabilities : List Cap) :
    (Cap.prod capabilities).apply substitution =
      .prod (capabilities.map fun capability => capability.apply substitution) := by
  change Cap.prod (Cap.applyList substitution capabilities) = _
  rw [Cap.applyList_eq_map_local]

/-- Paired substitution distributes through products as a pointwise map. -/
theorem Subst.applyList_eq_map_local (substitution : Subst) :
    ∀ targets,
      Ty.applyTargetList substitution.target
          (Ty.applyCapabilityList substitution.cap targets) =
        targets.map substitution.apply
  | [] => rfl
  | target :: targets => by
      change substitution.apply target ::
          Ty.applyTargetList substitution.target
            (Ty.applyCapabilityList substitution.cap targets) =
        substitution.apply target :: targets.map substitution.apply
      rw [Subst.applyList_eq_map_local substitution targets]

theorem Subst.apply_prod_map_local (substitution : Subst)
    (targets : List Ty) :
    substitution.apply (.prod targets) =
      .prod (targets.map substitution.apply) := by
  change Ty.prod
      (Ty.applyTargetList substitution.target
        (Ty.applyCapabilityList substitution.cap targets)) = _
  rw [Subst.applyList_eq_map_local]

/-- Capture typing for an arbitrary primitive-pattern position. -/
theorem ppm_captures_typed_raw_at
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {pattern : Pattern} {captures : List Pattern}
    {ppEnvironment : Env} {target : Ty} {holes : List Dual}
    {holeCapabilities : List Cap} {ppBindings : MonoCtx}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patternCap : Cap} {atRoot : Bool}
    (ppTyping : PPatTy signature pp target holes ppBindings)
    (capTyping : PPatCapsAt signature atRoot pp holeCapabilities patternCap)
    (patternTyping : PatternTy signature context parameters input pattern
      patternCap target output)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : atRoot = true → pp ≠ .hole) :
    ∃ duals,
      PatternTys signature context parameters input captures duals output ∧
      duals.map Dual.cap = holeCapabilities ∧
      duals.map Dual.target = holes.map Dual.target := by
  refine PPatTy.rec
    (motive_1 := fun pp target holes ppBindings _ =>
      ∀ {atRoot : Bool} {holeCapabilities : List Cap}
        {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env}
        {context : Context} {parameters : PatternCtx}
        {input output : MonoCtx} {patternCap : Cap},
        PPatCapsAt signature atRoot pp holeCapabilities patternCap →
        (atRoot = true → pp ≠ .hole) →
        PatternTy signature context parameters input pattern patternCap target
          output →
        PPM SF environment pp pattern (some (captures, ppEnvironment)) →
        ∃ duals,
          PatternTys signature context parameters input captures duals output ∧
          duals.map Dual.cap = holeCapabilities ∧
          duals.map Dual.target = holes.map Dual.target)
    (motive_2 := fun pps targets holes ppBindings _ =>
      ∀ {holeCapabilities childCapabilities : List Cap}
        {patterns : List Pattern}
        {results : List (List Pattern × Env)}
        {context : Context} {parameters : PatternCtx}
        {input output : MonoCtx} {patternDuals : List Dual},
        PPatCapsList signature pps holeCapabilities childCapabilities →
        PatternTys signature context parameters input patterns patternDuals
          output →
        patternDuals.map Dual.cap = childCapabilities →
        patternDuals.map Dual.target = targets →
        pps.length = patterns.length →
        (pps.zip patterns).length = results.length →
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
        ∃ capturedDuals,
          PatternTys signature context parameters input
            ((results.map Prod.fst).flatten) capturedDuals output ∧
          capturedDuals.map Dual.cap = holeCapabilities ∧
          capturedDuals.map Dual.target = holes.map Dual.target)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ppTyping
    capTyping nonCatchAll patternTyping matching
  · intro target varId fresh atRoot holeCapabilities pattern captures
      ppEnvironment context parameters input output patternCap capTyping
      notRoot patternTyping matching
    cases capTyping with
    | rootHole =>
        exact (notRoot rfl rfl).elim
    | childHole =>
        cases matching
        exact ⟨[⟨patternCap, target⟩], .cons patternTyping .nil, rfl, rfl⟩
  · intro target atRoot holeCapabilities pattern captures ppEnvironment
      context parameters input output patternCap capTyping notRoot patternTyping
      matching
    cases capTyping
    cases matching
    cases patternTyping
    exact ⟨[], .nil, rfl, rfl⟩
  · intro name target atRoot holeCapabilities pattern captures ppEnvironment
      context parameters input output patternCap capTyping notRoot patternTyping
      matching
    cases capTyping
    cases matching
    cases patternTyping
    exact ⟨[], .nil, rfl, rfl⟩
  · intro name entry pps targets result holes bindings ppFind ppsTyping
      ppInstance listIH atRoot holeCapabilities pattern captures ppEnvironment
      context parameters input output patternCap capTyping notRoot patternTyping
      matching
    cases capTyping with
    | @ctor _ _ capEntry _ _ childCapabilities _ capFind capsList
        capCompatible =>
        have capEntryEquality : capEntry = entry :=
          Option.some.inj (capFind.symm.trans ppFind)
        subst capEntry
        cases matching with
        | ctor lengthPP lengthResults all =>
            cases patternTyping with
            | @ctor _ _ _ _ patternEntry patterns patternDuals resultBindings
                patternResult patternFind patternsTyping patternCompatible
                patternInstance =>
                have patternEntryEquality : patternEntry = entry :=
                  Option.some.inj (patternFind.symm.trans ppFind)
                subst patternEntry
                have capsEquality :
                    patternDuals.map Dual.cap = childCapabilities :=
                  signatureWF.patternCapArgsUnique ppFind patternCompatible
                    capCompatible
                have targetsEquality :
                    patternDuals.map Dual.target = targets :=
                  signatureWF.patternInstArgsUnique ppFind patternInstance
                    ppInstance
                exact listIH capsList patternsTyping capsEquality
                  targetsEquality lengthPP lengthResults all
  · intro pps targets holes bindings ppsTyping listIH atRoot
      holeCapabilities pattern captures ppEnvironment context parameters input
      output patternCap capTyping notRoot patternTyping matching
    cases capTyping with
    | tuple capsList =>
        cases matching with
        | tuple lengthPP lengthResults all =>
            obtain ⟨patternDuals, patternsTyping, capsEquality,
                targetsEquality⟩ := PatternTy.ptuple_inv patternTyping
            exact listIH capsList patternsTyping capsEquality
              targetsEquality lengthPP lengthResults all
  · intro holeCapabilities childCapabilities patterns results context
      parameters input output
      patternDuals capsTyping patternTyping capsEquality targetsEquality
      lengthPP lengthResults all
    cases capsTyping
    cases patterns with
    | cons pattern patterns => simp at lengthPP
    | nil =>
        cases patternTyping
        cases results with
        | cons result results => simp at lengthResults
        | nil => exact ⟨[], .nil, rfl, rfl⟩
  · intro pp target headHoles headBindings pps targets tailHoles tailBindings
      headTyping tailTyping disjoint headIH tailIH holeCapabilities
      childCapabilities patterns results context parameters input output
      patternDuals capsTyping patternTyping capsEquality targetsEquality
      lengthPP lengthResults all
    cases capsTyping with
    | @cons _ _ headCapHoles tailCapHoles headCapability tailCapabilities
        headCaps tailCaps =>
        cases patterns with
        | nil => simp at lengthPP
        | cons pattern patterns =>
            cases results with
            | nil => simp [List.zip_cons_cons] at lengthResults
            | cons result results =>
                cases patternTyping with
                | cons patternHead patternTail =>
                    rename_i patternCap patternTarget middle patternDualsTail
                    simp only [List.map_cons, List.cons.injEq] at capsEquality targetsEquality
                    obtain ⟨headCapEquality, tailCapsEquality⟩ :=
                      capsEquality
                    obtain ⟨headTargetEquality, tailTargetsEquality⟩ :=
                      targetsEquality
                    obtain ⟨captures, ppEnvironment⟩ := result
                    have headPPM :
                        PPM SF environment pp pattern
                          (some (captures, ppEnvironment)) :=
                      all ((pp, pattern), (captures, ppEnvironment))
                        (by simp [List.zip_cons_cons])
                    rw [headCapEquality, headTargetEquality] at patternHead
                    obtain ⟨headDuals, headCapturedTyping, headDualCaps,
                        headDualTargets⟩ :=
                      headIH headCaps (by simp) patternHead headPPM
                    obtain ⟨tailDuals, tailCapturedTyping, tailDualCaps,
                        tailDualTargets⟩ :=
                      tailIH tailCaps patternTail tailCapsEquality
                        tailTargetsEquality (by simpa using lengthPP)
                        (by simpa [List.zip_cons_cons] using lengthResults)
                        (fun entry member => all entry
                          (by simp [List.zip_cons_cons]; exact .inr member))
                    refine ⟨headDuals ++ tailDuals, ?_, ?_, ?_⟩
                    · simpa [List.flatten_cons] using
                        PatternTys.append headCapturedTyping tailCapturedTyping
                    · simp [headDualCaps, tailDualCaps]
                    · simp [headDualTargets, tailDualTargets]

/-- Exact raw dual stream captured by a non-catch-all root PP success. -/
theorem ppm_captures_typed_raw
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {pattern : Pattern} {captures : List Pattern}
    {ppEnvironment : Env} {target : Ty} {holes : List Dual}
    {holeCapabilities : List Cap} {ppBindings : MonoCtx}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patternCap : Cap}
    (ppTyping : PPatTy signature pp target holes ppBindings)
    (capTyping : PPatCapsAt signature true pp holeCapabilities patternCap)
    (patternTyping : PatternTy signature context parameters input pattern
      patternCap target output)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ duals,
      PatternTys signature context parameters input captures duals output ∧
      duals.map Dual.cap = holeCapabilities ∧
      duals.map Dual.target = holes.map Dual.target :=
  ppm_captures_typed_raw_at signatureWF ppTyping capTyping patternTyping
    matching (fun _ => nonCatchAll)

/-- List form of `ppm_captures_typed_raw`, obtained through tuple formation. -/
theorem ppm_captures_typed_raw_list
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {SF : RuntimeSigF} {environment : Env}
    {pps : List PPat} {patterns : List Pattern}
    {results : List (List Pattern × Env)} {targets : List Ty}
    {holes : List Dual} {holeCapabilities childCapabilities : List Cap}
    {ppBindings : MonoCtx} {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx} {patternDuals : List Dual}
    (ppTyping : PPatTys signature pps targets holes ppBindings)
    (capTyping :
      PPatCapsList signature pps holeCapabilities childCapabilities)
    (patternTyping : PatternTys signature context parameters input patterns
      patternDuals output)
    (capEquality : patternDuals.map Dual.cap = childCapabilities)
    (targetEquality : patternDuals.map Dual.target = targets)
    (lengthPP : pps.length = patterns.length)
    (lengthResults : (pps.zip patterns).length = results.length)
    (matching : ∀ entry ∈ (pps.zip patterns).zip results,
      PPM SF environment entry.1.1 entry.1.2 (some entry.2)) :
    ∃ capturedDuals,
      PatternTys signature context parameters input
        ((results.map Prod.fst).flatten) capturedDuals output ∧
      capturedDuals.map Dual.cap = holeCapabilities ∧
      capturedDuals.map Dual.target = holes.map Dual.target := by
  have tupleMatching :
      PPM SF environment (.tuple pps) (.ptuple patterns)
        (some ((results.map Prod.fst).flatten,
          (results.map Prod.snd).flatten)) :=
    .tuple lengthPP lengthResults matching
  have tuplePatternTyping := PatternTy.tuple patternTyping
  rw [capEquality, targetEquality] at tuplePatternTyping
  exact ppm_captures_typed_raw signatureWF (.tuple ppTyping)
    (.tuple capTyping) tuplePatternTyping tupleMatching (by simp)

/--
Resolved capture alignment, stated componentwise so independently threaded PP
target/capability provenance can be followed through list concatenation.
-/
theorem ppm_captures_resolved_parts
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {ppRawTarget : Ty} {rawHoles : List Dual}
    {rawPPBindings : MonoCtx} {holeCapabilities : List Cap}
    {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
    {rawPatternTarget : Ty}
    (ppResolution : PPatResolution signature prevailing pp ppRawTarget
      rawHoles rawPPBindings)
    (capTyping : PPatCapsAt signature true pp holeCapabilities
      (rawPatternCap.apply prevailing.cap))
    (patternResolution : PatternResolution signature prevailing rawContext
      rawParameters rawInput pattern rawPatternCap rawPatternTarget rawOutput)
    (targetEquality : prevailing.apply rawPatternTarget =
      prevailing.apply ppRawTarget)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ capturedRawDuals,
      PatternResolutions signature prevailing rawContext rawParameters rawInput
        captures capturedRawDuals rawOutput ∧
      ((capturedRawDuals.map (Dual.applySubst prevailing)).map Dual.cap) =
        holeCapabilities ∧
      ((capturedRawDuals.map (Dual.applySubst prevailing)).map Dual.target) =
        (rawHoles.map (Dual.applySubst prevailing)).map Dual.target := by
  refine PPatResolution.rec
    (motive_1 := fun pp ppRawTarget rawHoles rawPPBindings _ =>
      ∀ {atRoot : Bool} {holeCapabilities : List Cap}
        {pattern : Pattern} {captures : List Pattern} {ppEnvironment : Env}
        {rawContext : Context} {rawParameters : PatternCtx}
        {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
        {rawPatternTarget : Ty},
        PPatCapsAt signature atRoot pp holeCapabilities
          (rawPatternCap.apply prevailing.cap) →
        (atRoot = true → pp ≠ .hole) →
        PatternResolution signature prevailing rawContext rawParameters
          rawInput pattern rawPatternCap rawPatternTarget rawOutput →
        prevailing.apply rawPatternTarget = prevailing.apply ppRawTarget →
        PPM SF environment pp pattern (some (captures, ppEnvironment)) →
        ∃ capturedRawDuals,
          PatternResolutions signature prevailing rawContext rawParameters
            rawInput captures capturedRawDuals rawOutput ∧
          ((capturedRawDuals.map (Dual.applySubst prevailing)).map Dual.cap) =
            holeCapabilities ∧
          ((capturedRawDuals.map (Dual.applySubst prevailing)).map
              Dual.target) =
            (rawHoles.map (Dual.applySubst prevailing)).map Dual.target)
    (motive_2 := fun pps ppRawTargets rawHoles rawPPBindings _ =>
      ∀ {holeCapabilities childCapabilities : List Cap}
        {patterns : List Pattern} {results : List (List Pattern × Env)}
        {rawContext : Context} {rawParameters : PatternCtx}
        {rawInput rawOutput : MonoCtx} {rawPatternDuals : List Dual},
        PPatCapsList signature pps holeCapabilities childCapabilities →
        PatternResolutions signature prevailing rawContext rawParameters
          rawInput patterns rawPatternDuals rawOutput →
        ((rawPatternDuals.map (Dual.applySubst prevailing)).map Dual.cap) =
          childCapabilities →
        ((rawPatternDuals.map (Dual.applySubst prevailing)).map Dual.target) =
          ppRawTargets.map prevailing.apply →
        pps.length = patterns.length →
        (pps.zip patterns).length = results.length →
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
        ∃ capturedRawDuals,
          PatternResolutions signature prevailing rawContext rawParameters
            rawInput ((results.map Prod.fst).flatten) capturedRawDuals
            rawOutput ∧
          ((capturedRawDuals.map (Dual.applySubst prevailing)).map Dual.cap) =
            holeCapabilities ∧
          ((capturedRawDuals.map (Dual.applySubst prevailing)).map
              Dual.target) =
            (rawHoles.map (Dual.applySubst prevailing)).map Dual.target)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ppResolution
    capTyping (fun _ => nonCatchAll) patternResolution targetEquality matching
  · intro pp ppTarget ppHoles ppBindings prevailingIdentity ppTyping atRoot
      holeCapabilities pattern captures ppEnvironment rawContext rawParameters
      rawInput rawOutput rawPatternCap rawPatternTarget capTyping notRoot
      patternResolution targetEquality matching
    subst prevailing
    have rawTargetEquality : rawPatternTarget = ppTarget := by
      simpa [Subst.apply_id] using targetEquality
    subst rawPatternTarget
    obtain ⟨capturedDuals, capturedTyping, capturedCaps, capturedTargets⟩ :=
      ppm_captures_typed_raw_at signatureWF ppTyping
        (by simpa [Subst.apply_id] using capTyping)
        patternResolution.raw matching notRoot
    exact ⟨capturedDuals, .identity rfl capturedTyping,
      by simpa [Subst.apply_id] using capturedCaps,
      by simpa [Subst.apply_id] using capturedTargets⟩
  · intro ppTarget varId fresh atRoot holeCapabilities pattern captures
      ppEnvironment rawContext rawParameters rawInput rawOutput rawPatternCap
      rawPatternTarget capTyping notRoot patternResolution targetEquality
      matching
    cases capTyping with
    | rootHole => exact (notRoot rfl rfl).elim
    | childHole =>
        cases matching
        exact ⟨[⟨rawPatternCap, rawPatternTarget⟩],
          .cons patternResolution .nil, rfl,
          by simpa [Dual.applySubst, Dual.apply] using targetEquality⟩
  · intro ppTarget atRoot holeCapabilities pattern captures ppEnvironment
      rawContext rawParameters rawInput rawOutput rawPatternCap rawPatternTarget
      capTyping notRoot patternResolution targetEquality matching
    cases capTyping
    cases matching
    cases patternResolution with
    | identity equality typing =>
        cases typing
        exact ⟨[], .nil, rfl, rfl⟩
    | wild => exact ⟨[], .nil, rfl, rfl⟩
  · intro name ppTarget atRoot holeCapabilities pattern captures
      ppEnvironment rawContext rawParameters rawInput rawOutput rawPatternCap
      rawPatternTarget capTyping notRoot patternResolution targetEquality
      matching
    cases capTyping
    cases matching
    cases patternResolution with
    | identity equality typing =>
        cases typing
        exact ⟨[], .nil, rfl, rfl⟩
    | pval expressionTyping fresh disjoint actualTyping =>
        exact ⟨[], .nil, rfl, rfl⟩
  · intro name entry pps ppTargets ppResult rawHoles rawBindings ppFind
      ppChildren ppRawInstance ppActualInstance listIH atRoot holeCapabilities
      pattern captures ppEnvironment rawContext rawParameters rawInput rawOutput
      rawPatternCap rawPatternTarget capTyping notRoot patternResolution
      targetEquality matching
    cases capTyping with
    | @ctor _ _ capEntry _ _ childCapabilities _ capFind capChildren
        capCompatible =>
        have capEntryEquality : capEntry = entry :=
          Option.some.inj (capFind.symm.trans ppFind)
        subst capEntry
        cases matching with
        | ctor lengthPP lengthResults all =>
            cases patternResolution with
            | identity prevailingIdentity patternTyping =>
                subst prevailing
                have rawTargetEquality : rawPatternTarget = ppResult := by
                  simpa [Subst.apply_id] using targetEquality
                subst rawPatternTarget
                obtain ⟨capturedDuals, capturedTyping, capturedCaps,
                    capturedTargets⟩ :=
                  ppm_captures_typed_raw signatureWF
                    (.ctor ppFind ppChildren.raw ppRawInstance)
                    (by simpa [Subst.apply_id] using
                      (PPatCapsAt.ctor capFind capChildren capCompatible))
                    patternTyping (.ctor lengthPP lengthResults all)
                    (by simp)
                exact ⟨capturedDuals, .identity rfl capturedTyping,
                  by simpa [Subst.apply_id] using capturedCaps,
                  by simpa [Subst.apply_id] using capturedTargets⟩
            | @ctor _ _ _ _ _ patternEntry patternPatterns rawPatternDuals
                _ rawResult patternFind patternChildren rawCompatible
                rawInstance actualCompatible actualInstance =>
                have patternEntryEquality : patternEntry = entry :=
                  Option.some.inj (patternFind.symm.trans ppFind)
                subst patternEntry
                have capsEquality :
                    ((rawPatternDuals.map (Dual.applySubst prevailing)).map
                      Dual.cap) = childCapabilities :=
                  signatureWF.patternCapArgsUnique ppFind actualCompatible
                    capCompatible
                have targetsEquality :
                    ((rawPatternDuals.map (Dual.applySubst prevailing)).map
                      Dual.target) = ppTargets.map prevailing.apply :=
                  signatureWF.patternInstArgsUnique ppFind
                    (by
                      have rewritten := actualInstance
                      rw [show (rawResult.applySubst prevailing).target =
                          prevailing.apply ppResult by
                          simpa [Dual.applySubst, Dual.apply] using
                            targetEquality] at rewritten
                      exact rewritten)
                    ppActualInstance
                exact listIH capChildren patternChildren capsEquality
                  targetsEquality lengthPP lengthResults all
  · intro pps ppTargets rawHoles rawBindings ppChildren listIH atRoot
      holeCapabilities pattern captures ppEnvironment rawContext rawParameters
      rawInput rawOutput rawPatternCap rawPatternTarget capTyping notRoot
      patternResolution targetEquality matching
    obtain ⟨childCapabilities, capChildren, outerCapEquality⟩ :=
      PPatCapsAt.tuple_inv capTyping
    cases matching with
    | tuple lengthPP lengthResults all =>
        rcases PatternResolution.ptuple_cases patternResolution with
          ⟨prevailingIdentity, patternTyping⟩ |
          ⟨rawPatternDuals, patternChildren, rawCapShape, rawTargetShape⟩
        · subst prevailing
          have rawTargetEquality :
              rawPatternTarget = .prod ppTargets := by
            simpa [Subst.apply_id] using targetEquality
          subst rawPatternTarget
          obtain ⟨capturedDuals, capturedTyping, capturedCaps,
              capturedTargets⟩ :=
            ppm_captures_typed_raw_at signatureWF (.tuple ppChildren.raw)
              (by simpa [Subst.apply_id] using capTyping) patternTyping
              (.tuple lengthPP lengthResults all) (by simp)
          exact ⟨capturedDuals, .identity rfl capturedTyping,
            by simpa [Subst.apply_id] using capturedCaps,
            by simpa [Subst.apply_id] using capturedTargets⟩
        · subst rawPatternCap
          subst rawPatternTarget
          have capsEquality :
              ((rawPatternDuals.map (Dual.applySubst prevailing)).map
                Dual.cap) = childCapabilities := by
            simpa [Cap.applyList_eq_map_local, Cap.apply_prod_map,
              List.map_map, Dual.applySubst,
              Dual.apply, Function.comp_def] using
              Cap.prod.inj outerCapEquality
          have targetsEquality :
              ((rawPatternDuals.map (Dual.applySubst prevailing)).map
                Dual.target) = ppTargets.map prevailing.apply := by
            have productEquality :
                Ty.prod ((rawPatternDuals.map Dual.target).map
                    prevailing.apply) =
                  Ty.prod (ppTargets.map prevailing.apply) := by
              simpa only [Subst.apply_prod_map_local] using targetEquality
            simpa [List.map_map, Dual.applySubst, Dual.apply,
              Function.comp_def] using Ty.prod.inj productEquality
          exact listIH capChildren patternChildren capsEquality targetsEquality
            lengthPP lengthResults all
  · intro pps ppTargets rawHoles rawBindings prevailingIdentity ppTyping
      holeCapabilities childCapabilities patterns results rawContext
      rawParameters rawInput rawOutput rawPatternDuals capsListTyping
      capturedResolution capsEquality targetsEquality lengthPP lengthResults all
    subst prevailing
    obtain ⟨capturedDuals, capturedTyping, capturedCaps, capturedTargets⟩ :=
      ppm_captures_typed_raw_list signatureWF ppTyping capsListTyping
        capturedResolution.raw
        (by simpa [Subst.apply_id] using capsEquality)
        (by simpa [Subst.apply_id] using targetsEquality)
        lengthPP lengthResults all
    exact ⟨capturedDuals, .identity rfl capturedTyping,
      by simpa [Subst.apply_id] using capturedCaps,
      by simpa [Subst.apply_id] using capturedTargets⟩
  · intro holeCapabilities childCapabilities patterns results rawContext
      rawParameters rawInput rawOutput rawPatternDuals capTyping
      patternResolution capsEquality targetsEquality lengthPP lengthResults all
    cases capTyping
    cases patterns with
    | cons pattern patterns => simp at lengthPP
    | nil =>
        cases results with
        | cons result results => simp at lengthResults
        | nil =>
            cases patternResolution with
            | identity prevailingIdentity patternTyping =>
                cases patternTyping
                exact ⟨[], .nil, rfl, rfl⟩
            | nil => exact ⟨[], .nil, rfl, rfl⟩
  · intro pp ppTarget headHoles headBindings pps ppTargets tailHoles
      tailBindings headResolution tailResolution disjoint headIH tailIH
      holeCapabilities childCapabilities patterns results rawContext
      rawParameters rawInput rawOutput rawPatternDuals capsListTyping
      capturedResolution capsEquality targetsEquality lengthPP lengthResults all
    cases capsListTyping with
    | @cons _ _ headCapHoles tailCapHoles headCapability tailCapabilities
        headCaps tailCaps =>
        cases patterns with
        | nil => simp at lengthPP
        | cons pattern patterns =>
            cases results with
            | nil => simp [List.zip_cons_cons] at lengthResults
            | cons result results =>
                cases capturedResolution with
                | identity prevailingIdentity patternTyping =>
                    subst prevailing
                    obtain ⟨capturedDuals, capturedTyping, capturedCaps,
                        capturedTargets⟩ :=
                      ppm_captures_typed_raw_list signatureWF
                        (.cons headResolution.raw tailResolution.raw disjoint)
                        (PPatCapsList.cons headCaps tailCaps) patternTyping
                        (by simpa [Subst.apply_id] using capsEquality)
                        (by simpa [Subst.apply_id] using targetsEquality)
                        lengthPP lengthResults all
                    exact ⟨capturedDuals, .identity rfl capturedTyping,
                      by simpa [Subst.apply_id] using capturedCaps,
                      by simpa [Subst.apply_id] using capturedTargets⟩
                | cons patternHead patternTail =>
                    rename_i rawPatternCap rawPatternTarget middle
                      rawPatternDualsTail
                    simp only [List.map_cons, List.cons.injEq] at capsEquality targetsEquality
                    obtain ⟨headCapEquality, tailCapsEquality⟩ :=
                      capsEquality
                    obtain ⟨headTargetEquality, tailTargetsEquality⟩ :=
                      targetsEquality
                    obtain ⟨captures, ppEnvironment⟩ := result
                    have headPPM :
                        PPM SF environment pp pattern
                          (some (captures, ppEnvironment)) :=
                      all ((pp, pattern), (captures, ppEnvironment))
                        (by simp [List.zip_cons_cons])
                    obtain ⟨headDuals, headCaptured, headDualCaps,
                        headDualTargets⟩ :=
                      headIH (atRoot := false) (by
                        have headCapsActual := headCaps
                        rw [← headCapEquality] at headCapsActual
                        simpa [Dual.applySubst, Dual.apply] using headCapsActual)
                        (by simp) patternHead
                        headTargetEquality headPPM
                    obtain ⟨tailDuals, tailCaptured, tailDualCaps,
                        tailDualTargets⟩ :=
                      tailIH tailCaps patternTail tailCapsEquality
                        tailTargetsEquality (by simpa using lengthPP)
                        (by simpa [List.zip_cons_cons] using lengthResults)
                        (fun entry member => all entry
                          (by simp [List.zip_cons_cons]; exact .inr member))
                    refine ⟨headDuals ++ tailDuals,
                      PatternResolutions.append headCaptured tailCaptured,
                      ?_, ?_⟩
                    · simp [headDualCaps, tailDualCaps]
                    · simp [headDualTargets, tailDualTargets]

/-- Exact resolved dual stream captured by a non-catch-all PP success. -/
theorem ppm_captures_resolved
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {prevailing : Subst} {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {ppRawTarget : Ty} {rawHoles : List Dual}
    {rawPPBindings : MonoCtx} {pattern : Pattern}
    {captures : List Pattern} {ppEnvironment : Env}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
    {rawPatternTarget : Ty}
    (ppResolution : PPatResolution signature prevailing pp ppRawTarget
      rawHoles rawPPBindings)
    (capTyping : PPatCapsAt signature true pp
      ((rawHoles.map (Dual.applySubst prevailing)).map Dual.cap)
      (rawPatternCap.apply prevailing.cap))
    (patternResolution : PatternResolution signature prevailing rawContext
      rawParameters rawInput pattern rawPatternCap rawPatternTarget rawOutput)
    (targetEquality : prevailing.apply rawPatternTarget =
      prevailing.apply ppRawTarget)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ capturedRawDuals,
      PatternResolutions signature prevailing rawContext rawParameters rawInput
        captures capturedRawDuals rawOutput ∧
      capturedRawDuals.map (Dual.applySubst prevailing) =
        rawHoles.map (Dual.applySubst prevailing) := by
  obtain ⟨capturedRawDuals, capturedTyping, capEquality, targetEquality⟩ :=
    ppm_captures_resolved_parts signatureWF ppResolution capTyping
      patternResolution targetEquality matching nonCatchAll
  exact ⟨capturedRawDuals, capturedTyping,
    Dual.list_eq_of_maps_eq capEquality targetEquality⟩

/-! ## Two-substitution capture alignment -/

/-- Actual constructor children retained by any aligned user-pattern
resolution, including its identity shortcut. -/
theorem PatternResolution.pctor_actual_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {name : String} {patterns : List Pattern} {rawCapability : Cap}
    {rawTarget : Ty}
    (resolution : PatternResolution signature prevailing context parameters
      input (.pctor name patterns) rawCapability rawTarget output) :
    ∃ entry rawDuals,
      signature.findPatternCtor name = some entry ∧
      PatternResolutions signature prevailing context parameters input
        patterns rawDuals output ∧
      entry.CapCompatible
        ((rawDuals.map (Dual.applySubst prevailing)).map Dual.cap)
        (rawCapability.apply prevailing.cap) ∧
      entry.Inst
        ((rawDuals.map (Dual.applySubst prevailing)).map Dual.target)
        (prevailing.apply rawTarget) := by
  cases resolution with
  | identity equality typing =>
      subst prevailing
      cases typing with
      | ctor found children compatible instantiated =>
          exact ⟨_, _, found, .identity rfl children,
            by simpa [Subst.apply_id] using compatible,
            by simpa [Subst.apply_id] using instantiated⟩
  | ctor found children rawCompatible rawInstance actualCompatible
      actualInstance =>
      exact ⟨_, _, found, children,
        by simpa [Dual.applySubst, Dual.apply] using actualCompatible,
        by simpa [Dual.applySubst, Dual.apply] using actualInstance⟩

/-- Actual tuple children retained by any aligned user-pattern resolution. -/
theorem PatternResolution.ptuple_actual_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {patterns : List Pattern} {rawCapability : Cap} {rawTarget : Ty}
    (resolution : PatternResolution signature prevailing context parameters
      input (.ptuple patterns) rawCapability rawTarget output) :
    ∃ rawDuals,
      PatternResolutions signature prevailing context parameters input
        patterns rawDuals output ∧
      rawCapability.apply prevailing.cap =
        .prod ((rawDuals.map (Dual.applySubst prevailing)).map Dual.cap) ∧
      prevailing.apply rawTarget =
        .prod ((rawDuals.map (Dual.applySubst prevailing)).map
          Dual.target) := by
  rcases PatternResolution.ptuple_cases resolution with
    ⟨equality, typing⟩ | ⟨rawDuals, children, capShape, targetShape⟩
  · subst prevailing
    cases typing with
    | tuple children =>
        exact ⟨_, .identity rfl children,
          by simp,
          by simp [Subst.apply_id]⟩
  · subst rawCapability
    subst rawTarget
    exact ⟨rawDuals, children,
      by simp [List.map_map, Dual.applySubst,
        Dual.apply, Function.comp_def],
      by simp [List.map_map, Dual.applySubst,
        Dual.apply, Function.comp_def]⟩

/-- An aligned primitive constructor exposes its actual child target
instance even when the alignment uses the identity shortcut. -/
theorem PPatResolution.ctor_actual_children
    {signature : FrozenSig} {prevailing : Subst}
    {name : String} {entry : PatternCtorScheme signature.observability}
    {patterns : List PPat} {result : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (found : signature.findPatternCtor name = some entry)
    (resolution : PPatResolution signature prevailing (.ctor name patterns)
      result holes bindings) :
    ∃ alignedTargets,
      PPatResolutions signature prevailing patterns alignedTargets holes
        bindings ∧
      entry.Inst (alignedTargets.map prevailing.apply)
        (prevailing.apply result) := by
  cases resolution with
  | identity equality typing =>
      subst prevailing
      cases typing with
      | ctor alignedFound children rawInstance =>
          have entryEquality := Option.some.inj (alignedFound.symm.trans found)
          subst_vars
          exact ⟨_, PPatResolutions.identity rfl children,
            by simpa [Subst.apply_id] using rawInstance⟩
  | ctor alignedFound children alignedRawInstance alignedActualInstance =>
      have entryEquality := Option.some.inj (alignedFound.symm.trans found)
      subst_vars
      exact ⟨_, children, alignedActualInstance⟩

/-- Actual tuple children retained by any aligned primitive-pattern tuple. -/
theorem PPatResolution.tuple_actual_children
    {signature : FrozenSig} {prevailing : Subst}
    {patterns : List PPat} {result : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (resolution : PPatResolution signature prevailing (.tuple patterns)
      result holes bindings) :
    ∃ alignedTargets,
      PPatResolutions signature prevailing patterns alignedTargets holes
        bindings ∧
      prevailing.apply result =
        .prod (alignedTargets.map prevailing.apply) := by
  cases resolution with
  | identity equality typing =>
      subst prevailing
      cases typing with
      | tuple children =>
          exact ⟨_, .identity rfl children, by simp⟩
  | tuple children =>
      exact ⟨_, children, by simp⟩

/-- Split a nonempty aligned primitive-pattern list without assuming that its
raw target, hole, or binding streams coincide with another derivation. -/
theorem PPatResolutions.cons_actual_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {pattern : PPat} {patterns : List PPat} {targets : List Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (resolution : PPatResolutions signature prevailing (pattern :: patterns)
      targets holes bindings) :
    ∃ headTarget tailTargets headHoles tailHoles headBindings tailBindings,
      targets = headTarget :: tailTargets ∧
      holes = headHoles ++ tailHoles ∧
      bindings = headBindings ++ tailBindings ∧
      PPatResolution signature prevailing pattern headTarget headHoles
        headBindings ∧
      PPatResolutions signature prevailing patterns tailTargets tailHoles
        tailBindings := by
  cases resolution with
  | identity equality typing =>
      subst prevailing
      cases typing with
      | cons head tail distinct =>
          exact ⟨_, _, _, _, _, _, rfl, rfl, rfl,
            .identity rfl head, .identity rfl tail⟩
  | cons head tail distinct =>
      exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, head, tail⟩

/-- Split a nonempty aligned user-pattern list through its identity shortcut
or its explicit cons constructor. -/
theorem PatternResolutions.cons_actual_inversion
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {pattern : Pattern} {patterns : List Pattern} {duals : List Dual}
    (resolution : PatternResolutions signature prevailing context parameters
      input (pattern :: patterns) duals output) :
    ∃ headCapability headTarget middle tailDuals,
      duals = ⟨headCapability, headTarget⟩ :: tailDuals ∧
      PatternResolution signature prevailing context parameters input pattern
        headCapability headTarget middle ∧
      PatternResolutions signature prevailing context parameters middle patterns
        tailDuals output := by
  cases resolution with
  | identity equality typing =>
      subst prevailing
      cases typing with
      | cons head tail =>
          exact ⟨_, _, _, _, rfl, .identity rfl head, .identity rfl tail⟩
  | cons head tail =>
      exact ⟨_, _, _, _, rfl, head, tail⟩

/-- A hole capability judgment is either the forbidden root catch-all case or
the exact singleton capability used at a nested position. -/
theorem PPatCapsAt.hole_cases
    {signature : FrozenSig} {atRoot : Bool}
    {holeCapabilities : List Cap} {outerCapability : Cap}
    (typing : PPatCapsAt signature atRoot .hole holeCapabilities
      outerCapability) :
    atRoot = true ∨
    (atRoot = false ∧ holeCapabilities = [outerCapability]) := by
  cases typing with
  | rootHole => exact .inl rfl
  | childHole => exact .inr ⟨rfl, rfl⟩

/-- Every primitive-pattern typing stream contains one dual per syntactic
hole. -/
theorem PPatTy.holes_length
    {signature : FrozenSig} :
    ∀ {pattern target holes bindings},
      PPatTy signature pattern target holes bindings →
      holes.length = pattern.holeCount := by
  intro pattern target holes bindings typing
  refine PPatTy.rec
    (motive_1 := fun pattern _ holes _ _ =>
      holes.length = pattern.holeCount)
    (motive_2 := fun patterns _ holes _ _ =>
      holes.length = PPat.holeCountList patterns)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro target varId fresh
    rfl
  · intro target
    rfl
  · intro name target
    rfl
  · intro name entry patterns targets result holes bindings found children
      instantiated childrenIH
    exact childrenIH
  · intro patterns targets holes bindings children childrenIH
    exact childrenIH
  · rfl
  · intro pattern target headHoles headBindings patterns targets tailHoles
      tailBindings head tail distinct headIH tailIH
    simp [PPat.holeCountList, headIH, tailIH]

/-- Aligned primitive-pattern resolution preserves the syntactic hole count. -/
theorem PPatResolution.holes_length
    {signature : FrozenSig} {prevailing : Subst}
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (resolution : PPatResolution signature prevailing pattern target holes
      bindings) :
    holes.length = pattern.holeCount :=
  resolution.raw.holes_length

/-- Terminal primitive-pattern resolution contains one dual per syntactic
hole, independently of the raw substitution stream that produced it. -/
theorem TerminalPPatResolution.holes_length
    {signature : FrozenSig} {prevailing : Subst}
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (resolution : TerminalPPatResolution signature prevailing pattern target
      holes bindings) :
    holes.length = pattern.holeCount := by
  refine TerminalPPatResolution.rec
    (motive_1 := fun pattern _ holes _ _ =>
      holes.length = pattern.holeCount)
    (motive_2 := fun patterns _ holes _ _ =>
      holes.length = PPat.holeCountList patterns)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ resolution
  · intro rawTarget varId fresh
    rfl
  · intro rawTarget
    rfl
  · intro name rawTarget
    rfl
  · intro name entry patterns targets result holes bindings found children
      instantiated childrenIH
    exact childrenIH
  · intro patterns targets holes bindings children childrenIH
    exact childrenIH
  · rfl
  · intro pattern target headHoles headBindings patterns targets tailHoles
      tailBindings head tail distinct headIH tailIH
    simp [PPat.holeCountList, headIH, tailIH]

/-- Terminal wildcard resolution preserves its incoming binding context. -/
theorem TerminalPatternResolution.wild_output
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input .wild capability target output) :
    output = input := by
  cases resolution
  rfl

/-- Terminal value-pattern resolution also preserves incoming bindings. -/
theorem TerminalPatternResolution.pval_output
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {expression : Expr} {capability : Cap} {target : Ty}
    (resolution : TerminalPatternResolution signature prevailing context
      parameters input (.pval expression) capability target output) :
    output = input := by
  cases resolution
  rfl

/-- Capability alignment also contains one capability per syntactic hole. -/
theorem PPatCapsAt.holes_length
    {signature : FrozenSig} {atRoot : Bool} {pattern : PPat}
    {holeCapabilities : List Cap} {outerCapability : Cap}
    (typing : PPatCapsAt signature atRoot pattern holeCapabilities
      outerCapability) :
    holeCapabilities.length = pattern.holeCount := by
  refine PPatCapsAt.rec
    (motive_1 := fun _ pattern holes _ _ =>
      holes.length = pattern.holeCount)
    (motive_2 := fun patterns holes _ _ =>
      holes.length = PPat.holeCountList patterns)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro holeCapability outerCapability
    rfl
  · intro capability
    rfl
  · intro atRoot outerCapability
    rfl
  · intro atRoot name outerCapability
    rfl
  · intro atRoot name entry patterns holes children outer found typing
      compatible childrenIH
    exact childrenIH
  · intro atRoot patterns holes children typing childrenIH
    exact childrenIH
  · rfl
  · intro pattern patterns headHoles tailHoles headCapability
      tailCapabilities head tail headIH tailIH
    simp [PPat.holeCountList, headIH, tailIH]

/-- Nondependent inversion of a nonempty capability-alignment list. -/
theorem PPatCapsList.cons_inversion
    {signature : FrozenSig} {pattern : PPat} {patterns : List PPat}
    {holeCapabilities childCapabilities : List Cap}
    (typing : PPatCapsList signature (pattern :: patterns) holeCapabilities
      childCapabilities) :
    ∃ headHoles tailHoles headCapability tailCapabilities,
      holeCapabilities = headHoles ++ tailHoles ∧
      childCapabilities = headCapability :: tailCapabilities ∧
      PPatCapsAt signature false pattern headHoles headCapability ∧
      PPatCapsList signature patterns tailHoles tailCapabilities := by
  cases typing with
  | cons head tail =>
      exact ⟨_, _, _, _, rfl, rfl, head, tail⟩

/-
Terminal capture alignment is stated only at actual indices.  The matcher
clause and the match site may retain unrelated raw substitutions; targets
remain equal while producer and consumer capability streams are related by
the retained one-way demand witness.
-/
theorem ppm_captures_terminal_parts
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {ppPrevailing patternPrevailing : Subst}
    {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {target : Ty} {holes : List Dual}
    {ppBindings : MonoCtx} {pattern : Pattern}
    {captures : List Pattern} {ppEnvironment : Env}
    {context : Context} {parameters : PatternCtx}
    {input output : MonoCtx}
    {producerCapability consumerCapability : Cap}
    (ppResolution : TerminalPPatResolution signature ppPrevailing pp target
      holes ppBindings)
    (capTyping : PPatCapsAt signature true pp (holes.map Dual.cap)
      producerCapability)
    (patternResolution : TerminalPatternResolution signature
      patternPrevailing context parameters input pattern consumerCapability
      target output)
    (capabilityDemand :
      CapabilityDemand producerCapability consumerCapability)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ capturedDuals,
      TerminalPatternResolutions signature patternPrevailing context parameters
        input captures capturedDuals output ∧
      CapabilityDemands (holes.map Dual.cap)
        (capturedDuals.map Dual.cap) ∧
      capturedDuals.map Dual.target = holes.map Dual.target := by
  refine TerminalPPatResolution.rec
    (motive_1 := fun pp target holes _ _ =>
      ∀ {atRoot : Bool} {pattern : Pattern} {captures : List Pattern}
        {ppEnvironment : Env} {context : Context} {parameters : PatternCtx}
        {input output : MonoCtx}
        {producerCapability consumerCapability : Cap},
        PPatCapsAt signature atRoot pp (holes.map Dual.cap)
          producerCapability →
        (atRoot = true → pp ≠ .hole) →
        TerminalPatternResolution signature patternPrevailing context
          parameters input pattern consumerCapability target output →
        CapabilityDemand producerCapability consumerCapability →
        PPM SF environment pp pattern (some (captures, ppEnvironment)) →
        ∃ capturedDuals,
          TerminalPatternResolutions signature patternPrevailing context
            parameters input captures capturedDuals output ∧
          CapabilityDemands (holes.map Dual.cap)
            (capturedDuals.map Dual.cap) ∧
          capturedDuals.map Dual.target = holes.map Dual.target)
    (motive_2 := fun pps targets holes _ _ =>
      ∀ {patterns : List Pattern}
        {results : List (List Pattern × Env)}
        {context : Context} {parameters : PatternCtx}
        {input output : MonoCtx} {patternDuals : List Dual}
        {childCapabilities : List Cap},
        PPatCapsList signature pps (holes.map Dual.cap)
          childCapabilities →
        TerminalPatternResolutions signature patternPrevailing context
          parameters input patterns patternDuals output →
        CapabilityDemands childCapabilities
          (patternDuals.map Dual.cap) →
        patternDuals.map Dual.target = targets →
        pps.length = patterns.length →
        (pps.zip patterns).length = results.length →
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
        ∃ capturedDuals,
          TerminalPatternResolutions signature patternPrevailing context
            parameters input ((results.map Prod.fst).flatten) capturedDuals
            output ∧
          CapabilityDemands (holes.map Dual.cap)
            (capturedDuals.map Dual.cap) ∧
          capturedDuals.map Dual.target = holes.map Dual.target)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ppResolution
    capTyping (fun _ => nonCatchAll) patternResolution capabilityDemand matching
  · intro rawTarget varId fresh atRoot pattern captures ppEnvironment
      context parameters input output producerCapability consumerCapability
      caps notRoot patternTyping capabilityDemand matched
    cases caps with
    | rootHole => exact (notRoot rfl rfl).elim
    | childHole =>
        cases matched
        refine ⟨[⟨consumerCapability, ppPrevailing.apply rawTarget⟩],
          .cons patternTyping .nil, ?_, ?_⟩
        · simpa [Dual.applySubst, Dual.apply] using
            CapabilityDemands.cons capabilityDemand CapabilityDemands.nil
        · simp [Dual.applySubst, Dual.apply]
  · intro rawTarget atRoot pattern captures ppEnvironment context parameters
      input output producerCapability consumerCapability caps notRoot
      patternTyping capabilityDemand matched
    cases caps
    cases matched
    have outputEquality := patternTyping.wild_output
    subst output
    exact ⟨[], .nil, .nil, rfl⟩
  · intro name rawTarget atRoot pattern captures ppEnvironment context
      parameters input output producerCapability consumerCapability caps
      notRoot patternTyping capabilityDemand matched
    cases caps
    cases matched
    have outputEquality := patternTyping.pval_output
    subst output
    exact ⟨[], .nil, .nil, rfl⟩
  · intro name entry pps targets result holes bindings found children
      instantiated listIH atRoot pattern captures ppEnvironment context
      parameters input output producerCapability consumerCapability caps
      notRoot patternTyping capabilityDemand matched
    cases caps with
    | @ctor _ _ capEntry _ _ childCapabilities _ capFound capChildren
        capCompatible =>
        have entryEquality : capEntry = entry :=
          Option.some.inj (capFound.symm.trans found)
        subst capEntry
        cases matched with
        | ctor lengthPP lengthResults all =>
            cases patternTyping with
            | @ctor _ _ _ _ _ patternEntry patternPatterns patternDuals
                _ patternResult patternFound patternChildren
                patternCompatible patternInstantiated =>
                have patternEntryEquality : patternEntry = entry :=
                  Option.some.inj (patternFound.symm.trans found)
                subst patternEntry
                have childDemands : CapabilityDemands childCapabilities
                    (patternDuals.map Dual.cap) :=
                  signatureWF.patternCapDemands found capCompatible
                    patternCompatible capabilityDemand
                have targetsEquality :
                    patternDuals.map Dual.target = targets :=
                  signatureWF.patternInstArgsUnique found patternInstantiated
                    instantiated
                exact listIH capChildren patternChildren childDemands
                  targetsEquality lengthPP lengthResults all
  · intro pps targets holes bindings children listIH atRoot pattern captures
      ppEnvironment context parameters input output producerCapability
      consumerCapability caps notRoot patternTyping capabilityDemand matched
    obtain ⟨childCapabilities, capChildren, outerEquality⟩ :=
      PPatCapsAt.tuple_inv caps
    cases matched with
    | tuple lengthPP lengthResults all =>
        cases patternTyping with
        | @tuple _ _ _ _ _ patternDuals _ patternChildren =>
            rw [outerEquality] at capabilityDemand
            have childDemands : CapabilityDemands childCapabilities
                (patternDuals.map Dual.cap) :=
              capabilityDemand.prod_children
            exact listIH capChildren patternChildren childDemands
              rfl lengthPP lengthResults all
  · intro patterns results context parameters input output patternDuals
      childCapabilities caps patternTyping capDemands targetsEquality
      lengthPP lengthResults all
    cases caps
    cases patterns with
    | cons pattern patterns => simp at lengthPP
    | nil =>
        cases results with
        | cons result results => simp at lengthResults
        | nil =>
            cases patternTyping
            exact ⟨[], .nil, .nil, rfl⟩
  · intro pp target headHoles headBindings pps targets tailHoles
      tailBindings headResolution tailResolution distinct headIH tailIH
      patterns results context parameters input output patternDuals
      childCapabilities caps patternTyping capDemands targetsEquality
      lengthPP lengthResults all
    obtain ⟨headCapHoles, tailCapHoles, headCapability, tailCapabilities,
        capHolesShape, childCapsShape, headCaps, tailCaps⟩ :=
      PPatCapsList.cons_inversion caps
    have headHoleLength : (headHoles.map Dual.cap).length = pp.holeCount := by
      simpa only [List.length_map] using headResolution.holes_length
    have headCapLength : headCapHoles.length = pp.holeCount :=
      headCaps.holes_length
    obtain ⟨headHolesEquality, tailHolesEquality⟩ :=
      List.append_inj
        (by simpa only [List.map_append] using capHolesShape)
        (headHoleLength.trans headCapLength.symm)
    rw [← headHolesEquality] at headCaps
    rw [← tailHolesEquality] at tailCaps
    cases patterns with
    | nil => simp at lengthPP
    | cons pattern patterns =>
        cases patternTyping with
        | @cons _ _ _ _ _ patternCap patternTarget middle _ patternDualsTail
            _ patternHead patternTail =>
            simp only [List.map_cons] at capDemands
            simp only [List.map_cons, List.cons.injEq] at targetsEquality
            rw [childCapsShape] at capDemands
            cases capDemands with
            | cons headDemand tailDemands =>
                obtain ⟨headTargetEquality, tailTargetsEquality⟩ :=
                  targetsEquality
                rw [headTargetEquality] at patternHead
                cases results with
                | nil => simp [List.zip_cons_cons] at lengthResults
                | cons result results =>
                    obtain ⟨headCaptures, headEnvironment⟩ := result
                    have headMatching :
                        PPM SF environment pp pattern
                          (some (headCaptures, headEnvironment)) :=
                      all ((pp, pattern), (headCaptures, headEnvironment))
                        (by simp [List.zip_cons_cons])
                    obtain ⟨headDuals, headCaptured, headDualCaps,
                        headDualTargets⟩ :=
                      headIH (atRoot := false) headCaps (by simp)
                        patternHead headDemand headMatching
                    obtain ⟨tailDuals, tailCaptured, tailDualCaps,
                        tailDualTargets⟩ :=
                      tailIH tailCaps patternTail tailDemands
                        tailTargetsEquality (by simpa using lengthPP)
                        (by simpa [List.zip_cons_cons] using lengthResults)
                        (fun entry member => all entry
                          (by simp [List.zip_cons_cons]; exact .inr member))
                    refine ⟨headDuals ++ tailDuals,
                      headCaptured.append tailCaptured, ?_, ?_⟩
                    · simpa only [List.map_append] using
                        headDualCaps.append tailDualCaps
                    · simp [List.map_append, headDualTargets,
                        tailDualTargets]

/--
Capture alignment when the matcher clause and the match site were resolved by
independent prevailing substitutions.  Only the two *actual* dual streams are
identified; their raw provenance streams remain independent.
-/
theorem ppm_captures_resolved_two_parts
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {ppPrevailing patternPrevailing : Subst}
    {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {ppRawTarget : Ty} {ppRawHoles : List Dual}
    {ppRawBindings : MonoCtx} {pattern : Pattern}
    {captures : List Pattern} {ppEnvironment : Env}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
    {rawPatternTarget : Ty}
    (ppResolution : PPatResolution signature ppPrevailing pp ppRawTarget
      ppRawHoles ppRawBindings)
    (capTyping : PPatCapsAt signature true pp
      ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.cap)
      (rawPatternCap.apply patternPrevailing.cap))
    (patternResolution : PatternResolution signature patternPrevailing
      rawContext rawParameters rawInput pattern rawPatternCap rawPatternTarget
      rawOutput)
    (targetEquality : patternPrevailing.apply rawPatternTarget =
      ppPrevailing.apply ppRawTarget)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ capturedRawDuals,
      PatternResolutions signature patternPrevailing rawContext rawParameters
        rawInput captures capturedRawDuals rawOutput ∧
      ((capturedRawDuals.map (Dual.applySubst patternPrevailing)).map
          Dual.cap) =
        ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.cap) ∧
      ((capturedRawDuals.map (Dual.applySubst patternPrevailing)).map
          Dual.target) =
        ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.target) := by
  refine PPatTy.rec
    (motive_1 := fun pp _ _ _ _ =>
      ∀ {ppPrevailing : Subst} {ppRawTarget : Ty}
        {ppRawHoles : List Dual} {ppRawBindings : MonoCtx}
        {atRoot : Bool} {pattern : Pattern} {captures : List Pattern}
        {ppEnvironment : Env} {patternPrevailing : Subst}
        {rawContext : Context} {rawParameters : PatternCtx}
        {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
        {rawPatternTarget : Ty},
        PPatResolution signature ppPrevailing pp ppRawTarget ppRawHoles
          ppRawBindings →
        PPatCapsAt signature atRoot pp
          ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.cap)
          (rawPatternCap.apply patternPrevailing.cap) →
        (atRoot = true → pp ≠ .hole) →
        PatternResolution signature patternPrevailing rawContext rawParameters
          rawInput pattern rawPatternCap rawPatternTarget rawOutput →
        patternPrevailing.apply rawPatternTarget =
          ppPrevailing.apply ppRawTarget →
        PPM SF environment pp pattern (some (captures, ppEnvironment)) →
        ∃ capturedRawDuals,
          PatternResolutions signature patternPrevailing rawContext
            rawParameters rawInput captures capturedRawDuals rawOutput ∧
          ((capturedRawDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.cap) =
            ((ppRawHoles.map
              (Dual.applySubst ppPrevailing)).map Dual.cap) ∧
          ((capturedRawDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.target) =
            ((ppRawHoles.map
              (Dual.applySubst ppPrevailing)).map Dual.target))
    (motive_2 := fun pps _ _ _ _ =>
      ∀ {ppPrevailing : Subst} {ppRawTargets : List Ty}
        {ppRawHoles : List Dual} {ppRawBindings : MonoCtx}
        {patterns : List Pattern}
        {results : List (List Pattern × Env)}
        {patternPrevailing : Subst} {rawContext : Context}
        {rawParameters : PatternCtx} {rawInput rawOutput : MonoCtx}
        {rawPatternDuals : List Dual} {childCapabilities : List Cap},
        PPatResolutions signature ppPrevailing pps ppRawTargets ppRawHoles
          ppRawBindings →
        PPatCapsList signature pps
          ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.cap)
          childCapabilities →
        PatternResolutions signature patternPrevailing rawContext rawParameters
          rawInput patterns rawPatternDuals rawOutput →
        ((rawPatternDuals.map
            (Dual.applySubst patternPrevailing)).map Dual.cap) =
          childCapabilities →
        ((rawPatternDuals.map
            (Dual.applySubst patternPrevailing)).map Dual.target) =
          ppRawTargets.map ppPrevailing.apply →
        pps.length = patterns.length →
        (pps.zip patterns).length = results.length →
        (∀ entry ∈ (pps.zip patterns).zip results,
          PPM SF environment entry.1.1 entry.1.2 (some entry.2)) →
        ∃ capturedRawDuals,
          PatternResolutions signature patternPrevailing rawContext
            rawParameters rawInput ((results.map Prod.fst).flatten)
            capturedRawDuals rawOutput ∧
          ((capturedRawDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.cap) =
            ((ppRawHoles.map
              (Dual.applySubst ppPrevailing)).map Dual.cap) ∧
          ((capturedRawDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.target) =
            ((ppRawHoles.map
              (Dual.applySubst ppPrevailing)).map Dual.target))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ppResolution.raw
    ppResolution capTyping (fun _ => nonCatchAll) patternResolution
      targetEquality matching
  · intro rawTarget varId fresh ppPrevailing ppRawTarget ppRawHoles
      ppRawBindings atRoot pattern captures ppEnvironment patternPrevailing
      rawContext rawParameters rawInput rawOutput rawPatternCap
      rawPatternTarget ppResolution capTyping notRoot patternResolution
      targetEquality matching
    cases ppResolution with
    | identity equality typing =>
        subst ppPrevailing
        cases typing with
        | hole alignedFresh =>
            rcases PPatCapsAt.hole_cases capTyping with
              root | ⟨child, singleton⟩
            · exact (notRoot root rfl).elim
            ·
                cases matching
                exact ⟨[⟨rawPatternCap, rawPatternTarget⟩],
                  .cons patternResolution .nil,
                  by simpa [Dual.applySubst, Dual.apply] using singleton.symm,
                  by simpa [Dual.applySubst, Dual.apply] using targetEquality⟩
    | hole alignedFresh =>
        rcases PPatCapsAt.hole_cases capTyping with
          root | ⟨child, singleton⟩
        · exact (notRoot root rfl).elim
        ·
            cases matching
            exact ⟨[⟨rawPatternCap, rawPatternTarget⟩],
              .cons patternResolution .nil,
              by simpa [Dual.applySubst, Dual.apply] using singleton.symm,
              by simpa [Dual.applySubst, Dual.apply] using targetEquality⟩
  · intro rawTarget ppPrevailing ppRawTarget ppRawHoles ppRawBindings
      atRoot pattern captures ppEnvironment patternPrevailing rawContext
      rawParameters rawInput rawOutput rawPatternCap rawPatternTarget
      ppResolution capTyping notRoot patternResolution targetEquality matching
    cases ppResolution with
    | identity equality typing =>
        subst ppPrevailing
        cases typing
        cases capTyping
        cases matching
        cases patternResolution with
        | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
        | wild => exact ⟨[], .nil, rfl, rfl⟩
    | wild =>
        cases capTyping
        cases matching
        cases patternResolution with
        | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
        | wild => exact ⟨[], .nil, rfl, rfl⟩
  · intro name rawTarget ppPrevailing ppRawTarget ppRawHoles ppRawBindings
      atRoot pattern captures ppEnvironment patternPrevailing rawContext
      rawParameters rawInput rawOutput rawPatternCap rawPatternTarget
      ppResolution capTyping notRoot patternResolution targetEquality matching
    cases ppResolution with
    | identity equality typing =>
        subst ppPrevailing
        cases typing
        cases capTyping
        cases matching
        cases patternResolution with
        | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
        | pval rawTyping fresh separate actualTyping =>
            exact ⟨[], .nil, rfl, rfl⟩
    | pval =>
        cases capTyping
        cases matching
        cases patternResolution with
        | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
        | pval rawTyping fresh separate actualTyping =>
            exact ⟨[], .nil, rfl, rfl⟩
  · intro name entry pps rawTargets rawResult rawHoles rawBindings found
      rawChildren rawInstance listIH ppPrevailing ppRawTarget ppRawHoles
      ppRawBindings atRoot pattern captures ppEnvironment patternPrevailing
      rawContext rawParameters rawInput rawOutput rawPatternCap
      rawPatternTarget ppResolution capTyping notRoot patternResolution
      targetEquality matching
    obtain ⟨alignedTargets, alignedChildren, alignedActualInstance⟩ :=
      PPatResolution.ctor_actual_children found ppResolution
    cases capTyping with
    | @ctor _ _ capEntry _ _ childCapabilities _ capFind capChildren
        capCompatible =>
        have capEntryEquality : capEntry = entry :=
          Option.some.inj (capFind.symm.trans found)
        subst capEntry
        cases matching with
        | ctor lengthPP lengthResults all =>
            obtain ⟨patternEntry, rawPatternDuals, patternFind,
                patternChildren, actualCompatible, actualInstance⟩ :=
              PatternResolution.pctor_actual_inversion patternResolution
            have patternEntryEquality : patternEntry = entry :=
              Option.some.inj (patternFind.symm.trans found)
            subst patternEntry
            have capsEquality :
                ((rawPatternDuals.map
                  (Dual.applySubst patternPrevailing)).map Dual.cap) =
                  childCapabilities :=
              signatureWF.patternCapArgsUnique found actualCompatible
                capCompatible
            have targetsEquality :
                ((rawPatternDuals.map
                  (Dual.applySubst patternPrevailing)).map Dual.target) =
                  alignedTargets.map ppPrevailing.apply := by
              apply signatureWF.patternInstArgsUnique found
              · have rewritten := actualInstance
                rw [show patternPrevailing.apply rawPatternTarget =
                    ppPrevailing.apply ppRawTarget from targetEquality] at rewritten
                exact rewritten
              · exact alignedActualInstance
            exact listIH alignedChildren capChildren patternChildren
              capsEquality targetsEquality lengthPP lengthResults all
  · intro pps rawTargets rawHoles rawBindings rawChildren listIH
      ppPrevailing ppRawTarget ppRawHoles ppRawBindings atRoot pattern captures
      ppEnvironment patternPrevailing rawContext rawParameters rawInput
      rawOutput rawPatternCap rawPatternTarget ppResolution capTyping notRoot
      patternResolution targetEquality matching
    obtain ⟨alignedTargets, alignedChildren, ppTargetShape⟩ :=
      PPatResolution.tuple_actual_children ppResolution
    obtain ⟨childCapabilities, capChildren, outerCapEquality⟩ :=
      PPatCapsAt.tuple_inv capTyping
    cases matching with
    | tuple lengthPP lengthResults all =>
        obtain ⟨rawPatternDuals, patternChildren, patternCapShape,
            patternTargetShape⟩ :=
          PatternResolution.ptuple_actual_inversion patternResolution
        have capsEquality :
            ((rawPatternDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.cap) =
              childCapabilities := by
          apply Cap.prod.inj
          exact patternCapShape.symm.trans outerCapEquality
        have targetsEquality :
            ((rawPatternDuals.map
              (Dual.applySubst patternPrevailing)).map Dual.target) =
              alignedTargets.map ppPrevailing.apply := by
          apply Ty.prod.inj
          exact patternTargetShape.symm.trans
            (targetEquality.trans ppTargetShape)
        exact listIH alignedChildren capChildren patternChildren capsEquality
          targetsEquality lengthPP lengthResults all
  · intro ppPrevailing ppRawTargets ppRawHoles ppRawBindings patterns
      results patternPrevailing rawContext rawParameters rawInput rawOutput
      rawPatternDuals childCapabilities ppResolution capTyping
      patternResolution capsEquality targetsEquality lengthPP lengthResults all
    cases ppResolution with
    | identity equality typing =>
        subst ppPrevailing
        cases typing
        cases capTyping
        cases patterns with
        | cons pattern patterns => simp at lengthPP
        | nil =>
            cases results with
            | cons result results => simp at lengthResults
            | nil =>
                cases patternResolution with
                | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
                | nil => exact ⟨[], .nil, rfl, rfl⟩
    | nil =>
        cases capTyping
        cases patterns with
        | cons pattern patterns => simp at lengthPP
        | nil =>
            cases results with
            | cons result results => simp at lengthResults
            | nil =>
                cases patternResolution with
                | identity equality typing => cases typing; exact ⟨[], .nil, rfl, rfl⟩
                | nil => exact ⟨[], .nil, rfl, rfl⟩
  · intro pp rawTarget rawHeadHoles rawHeadBindings pps rawTargets
      rawTailHoles rawTailBindings rawHead rawTail distinct headIH tailIH
      ppPrevailing ppRawTargets ppRawHoles ppRawBindings patterns results
      patternPrevailing rawContext rawParameters rawInput rawOutput
      rawPatternDuals childCapabilities ppResolution capTyping
      patternResolution capsEquality targetsEquality lengthPP lengthResults all
    obtain ⟨alignedHeadTarget, alignedTailTargets, alignedHeadHoles,
        alignedTailHoles, alignedHeadBindings, alignedTailBindings,
        targetsShape, holesShape, bindingsShape, alignedHead,
        alignedTail⟩ :=
      PPatResolutions.cons_actual_inversion ppResolution
    subst ppRawTargets
    subst ppRawHoles
    subst ppRawBindings
    cases patterns with
    | nil => simp at lengthPP
    | cons pattern patterns =>
        obtain ⟨rawPatternCap, rawPatternTarget, middle,
            rawPatternDualsTail, dualsShape, patternHead, patternTail⟩ :=
          PatternResolutions.cons_actual_inversion patternResolution
        subst rawPatternDuals
        obtain ⟨headCapHoles, tailCapHoles, headCapability,
            tailCapabilities, capHolesShape, childCapsShape, headCaps,
            tailCaps⟩ :=
          PPatCapsList.cons_inversion capTyping
        have alignedHeadLength :
            ((alignedHeadHoles.map
              (Dual.applySubst ppPrevailing)).map Dual.cap).length =
              pp.holeCount := by
          simpa only [List.length_map] using alignedHead.holes_length
        have capHeadLength : headCapHoles.length = pp.holeCount :=
          headCaps.holes_length
        obtain ⟨headHolesEquality, tailHolesEquality⟩ :=
          List.append_inj
            (by simpa only [List.map_append] using capHolesShape)
            (alignedHeadLength.trans capHeadLength.symm)
        rw [← headHolesEquality] at headCaps
        rw [← tailHolesEquality] at tailCaps
        have actualCapsShape := capsEquality.trans childCapsShape
        simp only [List.map_cons, List.cons.injEq] at actualCapsShape
        simp only [List.map_cons, List.cons.injEq] at targetsEquality
        obtain ⟨headCapEquality, tailCapsEquality⟩ := actualCapsShape
        obtain ⟨headTargetEquality, tailTargetsEquality⟩ :=
          targetsEquality
        cases results with
        | nil => simp [List.zip_cons_cons] at lengthResults
        | cons result results =>
            obtain ⟨captures, ppEnvironment⟩ := result
            have headPPM :
                PPM SF environment pp pattern
                  (some (captures, ppEnvironment)) :=
              all ((pp, pattern), (captures, ppEnvironment))
                (by simp [List.zip_cons_cons])
            obtain ⟨headDuals, headCaptured, headDualCaps,
                headDualTargets⟩ :=
              headIH alignedHead (by
                have rewritten := headCaps
                rw [← headCapEquality] at rewritten
                simpa [Dual.applySubst, Dual.apply] using rewritten)
                (by simp) patternHead headTargetEquality headPPM
            obtain ⟨tailDuals, tailCaptured, tailDualCaps,
                tailDualTargets⟩ :=
              tailIH alignedTail tailCaps patternTail tailCapsEquality
                tailTargetsEquality (by simpa using lengthPP)
                (by simpa [List.zip_cons_cons] using lengthResults)
                (fun entry member => all entry
                  (by simp [List.zip_cons_cons]; exact .inr member))
            refine ⟨headDuals ++ tailDuals,
              PatternResolutions.append headCaptured tailCaptured,
              ?_, ?_⟩
            · simp [List.map_append, headDualCaps, tailDualCaps]
            · simp [List.map_append, headDualTargets, tailDualTargets]

/-- Exact actual dual-stream equality for independently resolved matcher and
match-site derivations. -/
theorem ppm_captures_resolved_two
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {ppPrevailing patternPrevailing : Subst}
    {SF : RuntimeSigF} {environment : Env}
    {pp : PPat} {ppRawTarget : Ty} {ppRawHoles : List Dual}
    {ppRawBindings : MonoCtx} {pattern : Pattern}
    {captures : List Pattern} {ppEnvironment : Env}
    {rawContext : Context} {rawParameters : PatternCtx}
    {rawInput rawOutput : MonoCtx} {rawPatternCap : Cap}
    {rawPatternTarget : Ty}
    (ppResolution : PPatResolution signature ppPrevailing pp ppRawTarget
      ppRawHoles ppRawBindings)
    (capTyping : PPatCapsAt signature true pp
      ((ppRawHoles.map (Dual.applySubst ppPrevailing)).map Dual.cap)
      (rawPatternCap.apply patternPrevailing.cap))
    (patternResolution : PatternResolution signature patternPrevailing
      rawContext rawParameters rawInput pattern rawPatternCap rawPatternTarget
      rawOutput)
    (targetEquality : patternPrevailing.apply rawPatternTarget =
      ppPrevailing.apply ppRawTarget)
    (matching : PPM SF environment pp pattern
      (some (captures, ppEnvironment)))
    (nonCatchAll : pp ≠ .hole) :
    ∃ capturedRawDuals,
      PatternResolutions signature patternPrevailing rawContext rawParameters
        rawInput captures capturedRawDuals rawOutput ∧
      capturedRawDuals.map (Dual.applySubst patternPrevailing) =
        ppRawHoles.map (Dual.applySubst ppPrevailing) := by
  obtain ⟨capturedRawDuals, capturedTyping, capEquality, targetEquality⟩ :=
    ppm_captures_resolved_two_parts signatureWF ppResolution capTyping
      patternResolution targetEquality matching nonCatchAll
  exact ⟨capturedRawDuals, capturedTyping,
    Dual.list_eq_of_maps_eq capEquality targetEquality⟩

/-- Successful primitive data-pattern matching returns exact typed bindings. -/
theorem pdMatch_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature) :
    ∀ {pattern : DPat} {value : Value} {target : Ty}
      {bindings : MonoCtx} {environment : Env},
      DPatTy signature pattern target bindings →
      ValueTy signature value target →
      pdMatch pattern value = some environment →
      MonoEnvTys signature bindings environment
  := by
  intro pattern value target bindings environment patternTyping valueTyping
    matching
  refine DPatTy.rec
    (motive_1 := fun pattern target bindings _ =>
      ∀ {value environment},
        ValueTy signature value target →
        pdMatch pattern value = some environment →
        MonoEnvTys signature bindings environment)
    (motive_2 := fun patterns targets bindings _ =>
      ∀ {values environment},
        ValueTys signature values targets →
        pdMatchList patterns values = some environment →
        MonoEnvTys signature bindings environment)
    ?_ ?_ ?_ ?_ ?_ ?_ patternTyping valueTyping matching
  · intro name target value environment valueTyping matching
    simp only [pdMatch, Option.some.injEq] at matching
    subst environment
    exact MonoEnvTys.cons valueTyping MonoEnvTys.nil
  · intro target value environment _ matching
    simp only [pdMatch, Option.some.injEq] at matching
    subst environment
    exact MonoEnvTys.nil
  · intro name scheme patterns targets result bindings hfind patternsTyping
      hinstance listIH value environment valueTyping matching
    cases value with
    | ctor valueName values =>
        simp only [pdMatch] at matching
        split at matching
        · rename_i namesEqual
          simp only [beq_iff_eq] at namesEqual
          subst valueName
          have valuesTyping :=
            ValueTy.ctor_inversion signatureWF valueTyping hfind hinstance
          exact listIH valuesTyping matching
        · contradiction
    | lit => simp [pdMatch] at matching
    | tuple => simp [pdMatch] at matching
    | closure => simp [pdMatch] at matching
    | matcherV => simp [pdMatch] at matching
    | something => simp [pdMatch] at matching
  · intro patterns targets bindings patternsTyping listIH value environment
      valueTyping matching
    cases value with
    | tuple values =>
        simp only [pdMatch] at matching
        obtain ⟨canonicalValues, valueEquality, valuesTyping⟩ :=
          ValueTy.product_inversion signatureWF valueTyping
        injection valueEquality with valuesEquality
        subst canonicalValues
        exact listIH valuesTyping matching
    | lit => simp [pdMatch] at matching
    | ctor => simp [pdMatch] at matching
    | closure => simp [pdMatch] at matching
    | matcherV => simp [pdMatch] at matching
    | something => simp [pdMatch] at matching
  · intro values environment valuesTyping matching
    cases valuesTyping
    simp only [pdMatchList, Option.some.injEq] at matching
    subst environment
    exact MonoEnvTys.nil
  · intro pattern target headBindings patterns targets tailBindings
      patternTyping patternsTyping disjoint headIH tailIH values environment
      valuesTyping matching
    cases values with
    | nil => cases valuesTyping
    | cons headValue tailValues =>
        cases valuesTyping with
        | cons valueTyping valuesTyping =>
            simp only [pdMatchList] at matching
            cases headMatch : pdMatch pattern headValue with
            | none => simp [headMatch] at matching
            | some headEnvironment =>
                cases tailMatch : pdMatchList patterns tailValues with
                | none => simp [headMatch, tailMatch] at matching
                | some tailEnvironment =>
                    simp [headMatch, tailMatch] at matching
                    subst environment
                    exact (headIH valueTyping headMatch).append
                      (tailIH valuesTyping tailMatch)

/-- List form of `pdMatch_typed`. -/
theorem pdMatchList_typed
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature) :
    ∀ {patterns : List DPat} {values : List Value} {targets : List Ty}
      {bindings : MonoCtx} {environment : Env},
      DPatTys signature patterns targets bindings →
      ValueTys signature values targets →
      pdMatchList patterns values = some environment →
      MonoEnvTys signature bindings environment
  := by
  intro patterns values targets bindings environment patternsTyping valuesTyping
    matching
  exact pdMatch_typed signatureWF (DPatTy.tuple patternsTyping)
    (ValueTy.tuple valuesTyping) matching

/-- Data-pattern matching also yields ordinary `EnvTyped` once names are unique. -/
theorem pdMatch_monoEnvTys
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {pattern : DPat} {value : Value} {target : Ty}
    {bindings : MonoCtx} {environment : Env}
    (patternTyping : DPatTy signature pattern target bindings)
    (valueTyping : ValueTy signature value target)
    (matching : pdMatch pattern value = some environment) :
    MonoEnvTys signature bindings environment :=
  pdMatch_typed signatureWF patternTyping valueTyping matching

/-- Successful primitive data-pattern matching yields a typed mono context. -/
theorem pdMatch_envTyped
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {pattern : DPat} {value : Value} {target : Ty}
    {bindings : MonoCtx} {environment : Env}
    (patternTyping : DPatTy signature pattern target bindings)
    (valueTyping : ValueTy signature value target)
    (matching : pdMatch pattern value = some environment) :
    EnvTyped signature bindings.toContext environment :=
  (pdMatch_typed signatureWF patternTyping valueTyping matching).toEnvTyped

end TypePM
