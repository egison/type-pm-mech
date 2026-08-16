import TypePM.InterpreterEvalSafe

/-!
# Primitive-route primitive-pattern-pattern safety

A primitive-form pattern meets a clause header in at most one shallow
node, so its functional match is analyzed directly: shape-failing pairs
return an explicit failure, `hole`/`wild` succeed with empty captures, and
the single `pval` capture runs one embedded evaluation whose safety the
expression kernel supplies.  The successful capture environment's typing
is recovered through the relational `CaptureAdm` extracted from the
mirrored derivation, exactly as in the relational `ppm_of_primitive`.
-/

namespace TypePM

/--
Primitive-route clause-header match safety: under a passing shape check
against a primitive-form pattern, `ppmFuel` cannot stick, and a
successful capture environment is typed at the header's binding context,
pristine, and scoped.
-/
theorem ppmSafe_primitive
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {parameters : PatternCtx} {input output : MonoCtx}
    {ρa : Env} {prevailing patternPrevailing : Subst}
    {pp : PPat} {pattern : Pattern} {patternCapability : Cap}
    {target : Ty} {holes : List Dual} {ppBindings : MonoCtx}
    (patternTyping : ResolvedPatternTy signature patternPrevailing context
      parameters input pattern patternCapability target output)
    (primitive : pattern.isPrimForm = true)
    (ppTyping : ResolvedPPatTy signature prevailing pp target holes
      ppBindings)
    (shapeOK : ppShapeOK pp pattern = true)
    (ambient : ∀ name ∈ Pattern.exprVarsUnder [] pattern,
      name ∈ Env.names ρa)
    {fuel : Nat}
    (evalKernel :
      ∀ {fuel' : Nat}, fuel' < fuel →
        ∀ {expression : Expr} {target' : Ty},
          TypingInvariant signature (input.toContext ++ context) expression
            target' →
          (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
          evalFuel SF fuel' ρa expression ≠ .stuck ∧
          ∀ v, evalFuel SF fuel' ρa expression = .ok v →
            ScopedValue v ∧ ValuePristine v ∧
            ValueTy signature v target') :
    ppmFuel SF fuel ρa pp pattern ≠ .stuck ∧
    ∀ captures ppEnv,
      ppmFuel SF fuel ρa pp pattern = .ok (some (captures, ppEnv)) →
      MonoEnvTys signature ppBindings ppEnv ∧
      EnvPristine ppEnv ∧ ScopedEnv ppEnv := by
  cases fuel with
  | zero => exact ⟨by simp [ppmFuel], fun _ _ h => by simp [ppmFuel] at h⟩
  | succ fuel =>
    cases pp with
    | hole =>
        have admissible := captureAdm_of_primitive_success
          (SF := SF) (environment := ρa) patternTyping
          primitive ppTyping .hole
        cases admissible with
        | hole =>
            refine ⟨by simp [ppmFuel, shapeOK], ?_⟩
            intro captures ppEnv h
            simp only [ppmFuel, shapeOK, if_true, RunResult.ok.injEq,
              Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            exact ⟨.nil, .nil, .nil⟩
    | wild =>
        cases pattern with
        | wild =>
            have admissible := captureAdm_of_primitive_success
              (SF := SF) (environment := ρa) patternTyping
              primitive ppTyping .wild
            cases admissible with
            | wild =>
                refine ⟨by simp [ppmFuel, shapeOK], ?_⟩
                intro captures ppEnv h
                simp only [ppmFuel, shapeOK, if_true, RunResult.ok.injEq,
                  Option.some.injEq, Prod.mk.injEq] at h
                rw [← h.2]
                exact ⟨.nil, .nil, .nil⟩
        | pvar name => simp [ppShapeOK] at shapeOK
        | pval expression => simp [ppShapeOK] at shapeOK
        | embed name => simp [Pattern.isPrimForm] at primitive
        | pctor name patterns => simp [Pattern.isPrimForm] at primitive
        | ptuple patterns => simp [Pattern.isPrimForm] at primitive
        | pand left right => simp [Pattern.isPrimForm] at primitive
        | por left right => simp [Pattern.isPrimForm] at primitive
        | papp name arguments => simp [Pattern.isPrimForm] at primitive
    | pval ppName =>
        cases pattern with
        | pval expression =>
            cases hTerminal : patternTyping.terminal with
            | pval capFresh capNotIn exprTyping =>
            have exprFv : ∀ n ∈ expression.freeVars, n ∈ Env.names ρa :=
              fun n h => ambient n (by
                simpa [Pattern.exprVarsUnder, List.removeAll_nil] using h)
            have kernelRun := evalKernel (Nat.lt_succ_self fuel) exprTyping
              exprFv
            cases hEval : evalFuel SF fuel ρa expression with
            | stuck => exact absurd hEval kernelRun.1
            | timeout =>
                constructor
                · intro h
                  simp [ppmFuel, shapeOK, hEval] at h
                · intro captures ppEnv h
                  simp [ppmFuel, shapeOK, hEval] at h
            | ok value =>
                obtain ⟨scopedV, pristineV, typedV⟩ :=
                  kernelRun.2 value hEval
                have admissible := captureAdm_of_primitive_success
                  (SF := SF) (environment := ρa)
                  patternTyping primitive ppTyping
                  (.pval (evalFuel_ok hEval))
                cases admissible with
                | pval _ =>
                    constructor
                    · intro h
                      simp [ppmFuel, shapeOK, hEval] at h
                    · intro captures ppEnv h
                      simp only [ppmFuel, shapeOK, if_true,
                        RunResult.monad_bind_eq_bind, hEval,
                        RunResult.bind_ok, RunResult.pure_eq_ok,
                        RunResult.ok.injEq, Option.some.injEq,
                        Prod.mk.injEq] at h
                      rw [← h.2]
                      exact ⟨.cons typedV .nil, .cons pristineV .nil,
                        .cons scopedV .nil⟩
        | pvar name => simp [ppShapeOK] at shapeOK
        | wild => simp [ppShapeOK] at shapeOK
        | embed name => simp [Pattern.isPrimForm] at primitive
        | pctor name patterns => simp [Pattern.isPrimForm] at primitive
        | ptuple patterns => simp [Pattern.isPrimForm] at primitive
        | pand left right => simp [Pattern.isPrimForm] at primitive
        | por left right => simp [Pattern.isPrimForm] at primitive
        | papp name arguments => simp [Pattern.isPrimForm] at primitive
    | ctor ppCtorName pps =>
        cases pattern <;> simp_all [ppShapeOK, Pattern.isPrimForm]
    | tuple pps =>
        cases pattern <;> simp_all [ppShapeOK, Pattern.isPrimForm]

end TypePM
