import TypePM.InterpreterSafetyDefs
import TypePM.InterpreterAdequacy
import TypePM.Readiness
import TypePM.RuntimeAgreementBridge

/-!
# Dispatch-level safety of the fuel-indexed interpreter

`dispatchSafe` is the functional twin of `matcherReady_of_dispatch`: the
ordered clause walk of one typed matcher-dispatch site never sticks, and a
successful walk returns only the empty substitution together with
continuation branches whose atoms are scoped left-to-right against the
ambient names and whose captured patterns cover the dispatched pattern's
guaranteed binders.  `armsSafe` performs the arm walk inside the committed
clause.

Both walks receive their honest semantic residue as fuel-bounded kernels —
the expression-evaluation kernel and (for the clause walk) the
primitive-pattern-match kernel — bounded by the same fuel as the
conclusion, so the master strong induction on fuel can instantiate them.
Shape-failing clause heads are skipped by the shape-first design of
`ppmFuel`; the committed clause finds a receiving arm through the frozen
data-arm exhaustiveness checker; decode success follows from evaluation
preservation and the canonical-form totality lemmas.
-/

namespace TypePM

/-! ## Decode helpers

The arity of a successful tuple decode is `decodeTuple_length` from
`TypePM.DynamicMetatheory`, whose statement is exactly the one needed
here; only the membership inversion for the pointwise decode is new. -/

/-- Membership inversion for a pointwise tuple decode. -/
theorem mapM_decodeTuple_mem {k : Nat} :
    ∀ {tuples : List Value} {valueLists : List (List Value)},
      tuples.mapM (decodeTuple k) = some valueLists →
      ∀ values ∈ valueLists,
        ∃ tuple ∈ tuples, decodeTuple k tuple = some values
  | [], _, h, values, membership => by
      cases h
      cases membership
  | tuple :: tuples, valueLists, h, values, membership => by
      simp only [List.mapM_cons, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨head, headDecode, h⟩ := h
      obtain ⟨tail, tailDecode, h⟩ := h
      cases h
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨tuple, List.mem_cons_self, headDecode⟩
      · obtain ⟨found, foundMember, foundDecode⟩ :=
          mapM_decodeTuple_mem tailDecode values membership
        exact ⟨found, List.mem_cons_of_mem _ foundMember, foundDecode⟩

/-- Zipped continuation atoms project back to the captured patterns. -/
theorem zip_atoms_patterns :
    ∀ {captures : List Pattern} {matchers values : List Value},
      matchers.length = captures.length →
      values.length = captures.length →
      ((captures.zip (matchers.zip values)).map fun entry =>
        (⟨entry.1, entry.2.1, entry.2.2⟩ : Atom)).map Atom.p = captures
  | [], _, _, _, _ => rfl
  | capture :: captures, matcher :: matchers, value :: values, mlen,
      vlen => by
      simp only [List.zip_cons_cons, List.map_cons]
      exact congrArg (List.cons capture)
        (zip_atoms_patterns (by simpa using mlen) (by simpa using vlen))
  | _ :: _, [], _, mlen, _ => by simp at mlen
  | _ :: _, _ :: _, [], _, vlen => by simp at vlen

/-! ## Scoping of data-match environments -/

mutual

/-- A successful data match stores only subvalues of its scoped input. -/
theorem pdMatch_scoped :
    ∀ {dp : DPat} {value : Value} {environment : Env},
      ScopedValue value →
      pdMatch dp value = some environment →
      ScopedEnv environment
  | .var name, value, environment, wellScoped, h => by
      simp only [pdMatch, Option.some.injEq] at h
      subst h
      exact .cons wellScoped .nil
  | .wild, value, environment, _, h => by
      simp only [pdMatch, Option.some.injEq] at h
      subst h
      exact .nil
  | .ctor name pats, value, environment, wellScoped, h => by
      cases value with
      | ctor valueName values =>
          simp only [pdMatch] at h
          split at h
          · cases wellScoped with
            | ctor valuesScoped =>
                exact pdMatchList_scoped valuesScoped.mem h
          · cases h
      | lit n => simp [pdMatch] at h
      | tuple values => simp [pdMatch] at h
      | closure self ρ param body => simp [pdMatch] at h
      | matcherV ρ original current => simp [pdMatch] at h
      | something => simp [pdMatch] at h
  | .tuple pats, value, environment, wellScoped, h => by
      cases value with
      | tuple values =>
          simp only [pdMatch] at h
          cases wellScoped with
          | tuple valuesScoped =>
              exact pdMatchList_scoped valuesScoped.mem h
      | lit n => simp [pdMatch] at h
      | ctor valueName values => simp [pdMatch] at h
      | closure self ρ param body => simp [pdMatch] at h
      | matcherV ρ original current => simp [pdMatch] at h
      | something => simp [pdMatch] at h

/-- List form of `pdMatch_scoped`. -/
theorem pdMatchList_scoped :
    ∀ {pats : List DPat} {values : List Value} {environment : Env},
      (∀ value ∈ values, ScopedValue value) →
      pdMatchList pats values = some environment →
      ScopedEnv environment
  | [], values, environment, _, h => by
      cases values with
      | nil =>
          simp only [pdMatchList, Option.some.injEq] at h
          subst h
          exact .nil
      | cons value values => simp [pdMatchList] at h
  | pat :: pats, values, environment, wellScoped, h => by
      cases values with
      | nil => simp [pdMatchList] at h
      | cons value values =>
          simp only [pdMatchList, Option.bind_eq_bind,
            Option.bind_eq_some_iff] at h
          obtain ⟨headEnv, headMatch, h⟩ := h
          obtain ⟨tailEnv, tailMatch, h⟩ := h
          cases h
          exact ScopedEnv.append
            (pdMatch_scoped (wellScoped value List.mem_cons_self) headMatch)
            (pdMatchList_scoped
              (fun candidate membership =>
                wellScoped candidate (List.mem_cons_of_mem _ membership))
              tailMatch)

end

/-! ## The dispatch-branch contract -/

/-- One dispatch branch's outputs: continuation atoms scoped left-to-right
against the ambient names, and the pattern's guaranteed binders covered by
the continuation's binders. -/
def DispatchBranchProps (ambient : List String) (pattern : Pattern)
    (output : List (List Atom) × MatchSubst) : Prop :=
  output.2 = [] ∧
  ∀ atoms ∈ output.1,
    AtomsScoped ambient [] atoms ∧
    ∀ name ∈ pattern.scopeVars,
      name ∈ Pattern.scopeVarsList (atoms.map Atom.p)

/-! ## The arm walk of the committed clause -/

/--
The functional arm walk inside the committed clause is safe: with the
committed clause's typing pieces, its successful functional
primitive-pattern match, and a receiving arm guaranteed to exist, the walk
never sticks, and a successful walk satisfies `DispatchBranchProps`.  The
embedded body and next-matcher evaluations arrive through a fuel-bounded
evaluation kernel quantified at the same fuel as the walk.
-/
theorem armsSafe
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    {matcherContext : Context} {ρa matcherEnv : Env}
    {pattern : Pattern} {value : Value} {target : Ty}
    {pp : PPat} {next : Expr} {prevailing : Subst} {holes : List Dual}
    {ppBindings : MonoCtx} {nextMatchers : List Expr}
    {fuel₀ : Nat} {captures : List Pattern} {ppEnv : Env}
    (ppTyping : ResolvedPPatTy signature prevailing pp target holes
      ppBindings)
    (decompose : decomposeME next holes.length = some nextMatchers)
    (nextTyping : ExprsTy signature matcherContext nextMatchers
      (holes.map fun hole => .slot hole.cap hole.target))
    (ppmRun : ppmFuel [] fuel₀ ρa pp pattern =
      .ok (some (captures, ppEnv)))
    (ppTyped : MonoEnvTys signature ppBindings ppEnv)
    (ppPristine : EnvPristine ppEnv) (ppScoped : ScopedEnv ppEnv)
    (matcherEnvTyped : EnvTyped signature matcherContext matcherEnv)
    (matcherEnvPristine : EnvPristine matcherEnv)
    (matcherEnvScoped : ScopedEnv matcherEnv)
    (nextFv : ∀ name ∈ next.freeVars, name ∈ Env.names matcherEnv)
    (valueTyping : ValueTy signature value target)
    (valuePristine : ValuePristine value)
    (valueScoped : ScopedValue value)
    (ambientPattern : ∀ name ∈ Pattern.exprVarsUnder [] pattern,
      name ∈ Env.names ρa) :
    ∀ {fuel : Nat} {arms : List Arm},
      ArmsTy signature matcherContext target ppBindings
        (Ty.listT (prodTy (holes.map Dual.target))) arms →
      (∀ arm ∈ arms, ∀ name ∈ arm.body.freeVars.removeAll
        (arm.pat.bindVars ++ pp.bindVars),
        name ∈ Env.names matcherEnv) →
      (∃ arm ∈ arms, ∃ environment,
        pdMatch arm.pat value = some environment) →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {context' : Context} {ρ' : Env} {e : Expr} {τ : Ty},
          TypingInvariant signature context' e τ →
          EnvTyped signature context' ρ' → EnvPristine ρ' →
          ScopedEnv ρ' →
          (∀ name ∈ e.freeVars, name ∈ Env.names ρ') →
          evalFuel [] fuel' ρ' e ≠ .stuck ∧
          ∀ v, evalFuel [] fuel' ρ' e = .ok v → ScopedValue v) →
      Safe (DispatchBranchProps (Env.names ρa) pattern)
        (armsFuel [] fuel ρa matcherEnv value next captures ppEnv
          arms) := by
  intro fuel
  induction fuel with
  | zero =>
      intro arms _ _ _ _
      exact Safe.timeout
  | succ fuel ih =>
      intro arms armsTyping armFv witness evalKernel
      cases arms with
      | nil =>
          rcases witness with ⟨arm, membership, _⟩
          cases membership
      | cons arm arms =>
          obtain ⟨dp, body⟩ := arm
          cases armsTyping with
          | cons headTyping tailTyping =>
          cases headTyping with
          | mk dpatTyping bodyTyping =>
          rename_i armBindings
          simp only [armsFuel, RunResult.monad_bind_eq_bind]
          split
          · -- the head arm rejects the value: walk the tail
            rename_i hData
            have tailWitness : ∃ arm ∈ arms, ∃ environment,
                pdMatch arm.pat value = some environment := by
              rcases witness with ⟨candidate, membership, environment,
                matched⟩
              rcases List.mem_cons.mp membership with rfl | membership
              · rw [show (Arm.mk dp body).pat = dp from rfl, hData]
                  at matched
                cases matched
              · exact ⟨candidate, membership, environment, matched⟩
            refine ih tailTyping ?_ tailWitness ?_
            · intro arm membership name nameMembership
              exact armFv arm (List.mem_cons_of_mem _ membership) name
                nameMembership
            · intro fuel' lt
              exact evalKernel (Nat.lt_succ_of_lt lt)
          · -- the head arm receives the value
            rename_i dataEnv hData
            have relPpm := ppmFuel_ok ppmRun
            have dataTyped :=
              pdMatch_typed signatureWF dpatTyping valueTyping hData
            have dataPristine := pdMatch_pristine valuePristine hData
            have dataScoped := pdMatch_scoped valueScoped hData
            have bodyEnvTyped : EnvTyped signature
                (armBindings.toContext ++ ppBindings.toContext ++
                  matcherContext)
                (dataEnv ++ ppEnv ++ matcherEnv) := by
              simpa [List.append_assoc] using
                dataTyped.envTyped_append
                  (ppTyped.envTyped_append matcherEnvTyped)
            have bodyEnvPristine :
                EnvPristine (dataEnv ++ ppEnv ++ matcherEnv) := by
              simpa [List.append_assoc] using
                dataPristine.append
                  (ppPristine.append matcherEnvPristine)
            have bodyEnvScoped :
                ScopedEnv (dataEnv ++ ppEnv ++ matcherEnv) := by
              simpa [List.append_assoc] using
                dataScoped.append (ppScoped.append matcherEnvScoped)
            have bodyFv : ∀ name ∈ body.freeVars,
                name ∈ Env.names (dataEnv ++ ppEnv ++ matcherEnv) := by
              intro name membership
              by_cases hBound : name ∈ dp.bindVars ++ pp.bindVars
              · simp only [Env.names_append, pdMatch_names hData,
                  ppm_env_names pp relPpm]
                exact List.mem_append.mpr (.inl hBound)
              · simp only [Env.names_append]
                exact List.mem_append.mpr
                  (.inr (armFv (Arm.mk dp body) List.mem_cons_self name
                    (List.mem_removeAll_of_mem membership hBound)))
            cases hBody : evalFuel [] fuel
                (dataEnv ++ ppEnv ++ matcherEnv) body with
            | timeout => exact Safe.timeout
            | stuck =>
                exact absurd hBody
                  ((evalKernel (Nat.lt_succ_self fuel) bodyTyping
                    bodyEnvTyped bodyEnvPristine bodyEnvScoped
                    bodyFv).1)
            | ok decomposition =>
                simp only [RunResult.bind_ok]
                have decompositionScoped :=
                  (evalKernel (Nat.lt_succ_self fuel) bodyTyping
                    bodyEnvTyped bodyEnvPristine bodyEnvScoped
                    bodyFv).2 decomposition hBody
                have decompositionTyping :=
                  EvalRuntimeSigAgrees.preservation signatureWF
                    (EvalRuntimeSigAgrees.of_global agrees
                      (evalFuel_ok hBody))
                    bodyEnvPristine bodyEnvTyped bodyTyping
                have captureLength : captures.length = holes.length :=
                  (ppm_captures_length pp relPpm).trans
                    ppTyping.holes_length.symm
                split
                · -- the decomposition decodes as a list
                  rename_i hList
                  obtain ⟨tuples, listDecode⟩ :=
                    listOfV_isSome signatureWF decompositionTyping
                  rw [listDecode] at hList
                  cases hList
                · rename_i tuples hList
                  have tuplesTyped :=
                    (listOfV_typed signatureWF decompositionTyping
                      hList).replicate_mem
                  split
                  · -- every element decodes at the capture arity
                    rename_i hDecode
                    obtain ⟨valueLists, tupleDecodes⟩ :=
                      mapM_decodeTuple_isSome signatureWF
                        (targets := holes.map Dual.target) tuplesTyped
                    have tupleDecodes' :
                        tuples.mapM (decodeTuple captures.length) =
                          some valueLists := by
                      rw [captureLength]
                      simpa [List.length_map] using tupleDecodes
                    rw [tupleDecodes'] at hDecode
                    cases hDecode
                  · rename_i valueLists hDecode
                    have nextTypingInv :=
                      decomposeME_typed
                        (targets := holes.map fun hole =>
                          .slot hole.cap hole.target)
                        (by simpa [List.length_map] using decompose)
                        nextTyping
                    cases hNext : evalFuel [] fuel matcherEnv next with
                    | timeout => exact Safe.timeout
                    | stuck =>
                        exact absurd hNext
                          ((evalKernel (Nat.lt_succ_self fuel)
                            nextTypingInv matcherEnvTyped
                            matcherEnvPristine matcherEnvScoped
                            nextFv).1)
                    | ok matcherValue =>
                        simp only [RunResult.bind_ok]
                        have matcherValueScoped :=
                          (evalKernel (Nat.lt_succ_self fuel)
                            nextTypingInv matcherEnvTyped
                            matcherEnvPristine matcherEnvScoped
                            nextFv).2 matcherValue hNext
                        have matcherValueTyping :=
                          EvalRuntimeSigAgrees.preservation signatureWF
                            (EvalRuntimeSigAgrees.of_global agrees
                              (evalFuel_ok hNext))
                            matcherEnvPristine matcherEnvTyped
                            nextTypingInv
                        split
                        · -- the next matcher decodes at the capture arity
                          rename_i hMatchers
                          obtain ⟨matchers, matcherDecode⟩ :=
                            decodeTuple_isSome signatureWF
                              matcherValueTyping
                          have matcherDecode' :
                              decodeTuple captures.length matcherValue =
                                some matchers := by
                            rw [captureLength]
                            simpa [List.length_map] using matcherDecode
                          rw [matcherDecode'] at hMatchers
                          cases hMatchers
                        · rename_i matchers hMatchers
                          refine ⟨rfl, ?_⟩
                          intro atoms membership
                          obtain ⟨values, valuesMem, rfl⟩ :=
                            List.mem_map.mp membership
                          obtain ⟨tuple, tupleMem, tupleDecode⟩ :=
                            mapM_decodeTuple_mem hDecode values
                              valuesMem
                          refine ⟨?_, ?_⟩
                          · exact AtomsScoped.of_captured
                              (ppm_captured_scoped pp relPpm
                                ambientPattern)
                              (decodeTuple_scoped matcherValueScoped
                                hMatchers)
                              (decodeTuple_scoped
                                (listOfV_scoped decompositionScoped
                                  hList tuple tupleMem)
                                tupleDecode)
                          · intro name nameMembership
                            rw [zip_atoms_patterns
                              (decodeTuple_length hMatchers)
                              (decodeTuple_length tupleDecode)]
                            exact ppm_scopeVars_sub pp relPpm name
                              nameMembership

/-! ## The clause walk -/

/--
The functional clause dispatch of one typed matcher-dispatch site is safe:
the walk skips shape-failing headers, commits to the first
shape-compatible clause, never sticks, and a successful dispatch satisfies
`DispatchBranchProps`.  The committed clause's primitive-pattern match and
the embedded expression evaluations arrive through fuel-bounded kernels
quantified at the same fuel as the walk; the two clause-header scoping
facts consumed by the arm walk are derived locally from the single
`ScopedClauses` premise.
-/
theorem dispatchSafe
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    (agrees : ∀ context, RuntimeSigAgrees signature context
      ([] : RuntimeSigF))
    {matcherContext : Context} {ρa matcherEnv : Env}
    {pattern : Pattern} {value : Value} {target : Ty}
    {original : List Clause} {producerCapability : Cap}
    {evidence : List Shape.Evidence}
    (clausesTyped : ResolvedClausesTy signature matcherContext original
      producerCapability target evidence)
    (armsExhaustive : ArmExhaustive signature original target)
    (matcherEnvTyped : EnvTyped signature matcherContext matcherEnv)
    (matcherEnvPristine : EnvPristine matcherEnv)
    (matcherEnvScoped : ScopedEnv matcherEnv)
    (clausesScoped : ScopedClauses (Env.names matcherEnv) original)
    (valueTyping : ValueTy signature value target)
    (valuePristine : ValuePristine value)
    (valueScoped : ScopedValue value)
    (ambientPattern : ∀ name ∈ Pattern.exprVarsUnder [] pattern,
      name ∈ Env.names ρa) :
    ∀ {fuel : Nat} {remaining : List Clause},
      (∀ {clause : Clause}, clause ∈ original →
        ppShapeOK clause.pp pattern = true →
        ∀ {prevailing : Subst} {holes : List Dual}
          {ppBindings : MonoCtx},
          ResolvedPPatTy signature prevailing clause.pp target holes
            ppBindings →
          PPatCapsAt signature true clause.pp (holes.map Dual.cap)
            producerCapability →
          PPatCoreOrder clause.pp →
          ∀ {fuel' : Nat}, fuel' < fuel →
            ppmFuel [] fuel' ρa clause.pp pattern ≠ .stuck ∧
            ∀ captures ppEnv,
              ppmFuel [] fuel' ρa clause.pp pattern =
                .ok (some (captures, ppEnv)) →
              MonoEnvTys signature ppBindings ppEnv ∧
              EnvPristine ppEnv ∧ ScopedEnv ppEnv) →
      (∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {context' : Context} {ρ' : Env} {e : Expr} {τ : Ty},
          TypingInvariant signature context' e τ →
          EnvTyped signature context' ρ' → EnvPristine ρ' →
          ScopedEnv ρ' →
          (∀ name ∈ e.freeVars, name ∈ Env.names ρ') →
          evalFuel [] fuel' ρ' e ≠ .stuck ∧
          ∀ v, evalFuel [] fuel' ρ' e = .ok v → ScopedValue v) →
      (∀ clause ∈ remaining, clause ∈ original) →
      (∃ clause ∈ remaining, ppShapeOK clause.pp pattern = true) →
      Safe (DispatchBranchProps (Env.names ρa) pattern)
        (dispatchFuel [] fuel ρa matcherEnv pattern value
          remaining) := by
  intro fuel
  induction fuel with
  | zero =>
      intro remaining _ _ _ _
      exact Safe.timeout
  | succ fuel ih =>
      intro remaining ppmKernel evalKernel memberOriginal witness
      cases remaining with
      | nil =>
          rcases witness with ⟨clause, membership, _⟩
          cases membership
      | cons clause remaining =>
          obtain ⟨pp, next, arms⟩ := clause
          have headMember : Clause.mk pp next arms ∈ original :=
            memberOriginal _ List.mem_cons_self
          simp only [dispatchFuel, RunResult.monad_bind_eq_bind]
          cases hPpm : ppmFuel [] fuel ρa pp pattern with
          | timeout => exact Safe.timeout
          | stuck =>
              cases hShape : ppShapeOK pp pattern with
              | false =>
                  -- a shape-failing head cannot stick
                  cases fuel with
                  | zero => simp [ppmFuel] at hPpm
                  | succ f => simp [ppmFuel, hShape] at hPpm
              | true =>
                  obtain ⟨prevailing, clauseEvidence, _evidenceMember,
                      clauseTyping⟩ := clausesTyped.member headMember
                  obtain ⟨holes, pp', next', arms', ppBindings,
                      nextMatchers, clauseEq, ppTyping, ppCaps,
                      _decompose, _nextTyping, _armsTyping,
                      _evidenceCheck⟩ := clauseTyping.checked
                  injection clauseEq with ppEq nextEq armsEq
                  subst ppEq
                  subst nextEq
                  subst armsEq
                  exact absurd hPpm
                    ((ppmKernel headMember hShape ppTyping ppCaps
                      clauseTyping.coreOrder
                      (Nat.lt_succ_self fuel)).1)
          | ok outcome =>
              simp only [RunResult.bind_ok]
              cases outcome with
              | none =>
                  -- shape failure: walk the tail
                  have headShapeFalse :
                      ppShapeOK pp pattern = false := by
                    cases ppmFuel_ok hPpm with
                    | fail shapeFalse => exact shapeFalse
                  have tailWitness : ∃ candidate ∈ remaining,
                      ppShapeOK candidate.pp pattern = true := by
                    rcases witness with ⟨candidate, membership,
                      candidateShape⟩
                    rcases List.mem_cons.mp membership with
                      rfl | membership
                    · rw [show (Clause.mk pp next arms).pp = pp
                          from rfl, headShapeFalse] at candidateShape
                      cases candidateShape
                    · exact ⟨candidate, membership, candidateShape⟩
                  refine ih ?_ ?_ ?_ tailWitness
                  · intro clause' member shape prevailing holes
                      ppBindings ppTy caps order fuel' lt
                    exact ppmKernel member shape ppTy caps order
                      (Nat.lt_succ_of_lt lt)
                  · intro fuel' lt
                    exact evalKernel (Nat.lt_succ_of_lt lt)
                  · intro candidate member
                    exact memberOriginal candidate
                      (List.mem_cons_of_mem _ member)
              | some result =>
                  -- commit to the head clause
                  obtain ⟨captures, ppEnv⟩ := result
                  have hShape : ppShapeOK pp pattern = true := by
                    cases hS : ppShapeOK pp pattern with
                    | true => rfl
                    | false =>
                        cases fuel with
                        | zero => simp [ppmFuel] at hPpm
                        | succ f => simp [ppmFuel, hS] at hPpm
                  obtain ⟨prevailing, clauseEvidence, _evidenceMember,
                      clauseTyping⟩ := clausesTyped.member headMember
                  obtain ⟨holes, pp', next', arms', ppBindings,
                      nextMatchers, clauseEq, ppTyping, ppCaps,
                      decompose, nextTyping, armsTyping,
                      _evidenceCheck⟩ := clauseTyping.checked
                  injection clauseEq with ppEq nextEq armsEq
                  subst ppEq
                  subst nextEq
                  subst armsEq
                  obtain ⟨ppTyped, ppPristine, ppScoped⟩ :=
                    (ppmKernel headMember hShape ppTyping ppCaps
                      clauseTyping.coreOrder
                      (Nat.lt_succ_self fuel)).2 captures ppEnv hPpm
                  obtain ⟨dpFound, dpMember, dataEnvironment₀,
                      dpMatched⟩ :=
                    signatureWF.armExhaustiveSuccess (value := value)
                      (armsExhaustive _ headMember)
                  obtain ⟨armFound, armMember, patEq⟩ :=
                    List.mem_map.mp dpMember
                  have armWitness : ∃ arm ∈ arms, ∃ environment,
                      pdMatch arm.pat value = some environment :=
                    ⟨armFound, armMember, dataEnvironment₀, by
                      rw [patEq]; exact dpMatched⟩
                  have nextFv : ∀ name ∈ next.freeVars,
                      name ∈ Env.names matcherEnv := by
                    intro name membership
                    exact clausesScoped name
                      (Clause.freeVars_mem_of_mem headMember name
                        (List.mem_append.mpr (.inl membership)))
                  have armFv : ∀ arm ∈ arms,
                      ∀ name ∈ arm.body.freeVars.removeAll
                        (arm.pat.bindVars ++ pp.bindVars),
                      name ∈ Env.names matcherEnv := by
                    intro arm membership name nameMembership
                    obtain ⟨dp, body⟩ := arm
                    exact clausesScoped name
                      (Clause.freeVars_mem_of_mem headMember name
                        (List.mem_append.mpr (.inr
                          (Arm.freeVars_mem_of_mem membership name
                            nameMembership))))
                  exact armsSafe signatureWF agrees ppTyping decompose
                    nextTyping hPpm ppTyped ppPristine ppScoped
                    matcherEnvTyped matcherEnvPristine matcherEnvScoped
                    nextFv valueTyping valuePristine valueScoped
                    ambientPattern armsTyping armFv armWitness
                    (fun {fuel'} lt =>
                      evalKernel (Nat.lt_succ_of_lt lt))

end TypePM
