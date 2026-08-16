import TypePM.InterpreterSafetyDefs
import TypePM.InterpreterAdequacy
import TypePM.Safety

/-!
# Safety of the committed clause's primitive-pattern match

`ppmSafe`/`ppmListSafe` are the functional twins of `ppm_of_captureAdm`: a
capture-admissible primitive-pattern match in a well-ordered clause header
cannot stick, and a successful match returns a capture environment typed at
the admissible binding context, pristine, and scoped.  The embedded `#$x`
evaluations are received through a fuel-bounded evaluation kernel covering
exactly the strictly smaller fuels, so that the orchestrating strong
induction on fuel can instantiate it.

The order side condition threads the hole-seen state: below a hole-free
prefix the runtime binding discipline of `Pattern.exprVarsUnder` starts from
the empty bound list, and `CaptureAdm.scopeVars_nil_of_order` shows a
capture-admissible pattern below a hole-free header binds nothing, so the
threading stays trivial exactly where the kernel needs it.
-/

namespace TypePM

/-! ## Hole-seen monotonicity of the primitive-pattern order -/

/-- The hole-seen state never regresses: an order derivation entered at
`true` also finishes at `true`. -/
theorem PPatOrder.true_mono {pp : PPat} {finished : Bool}
    (order : PPatOrder true pp finished) : finished = true := by
  refine PPatOrder.rec
    (motive_1 := fun seen _ finished _ => seen = true → finished = true)
    (motive_2 := fun seen _ finished _ => seen = true → finished = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ order rfl
  · intro _ _
    rfl
  · intro _ h
    exact h
  · intro _ h
    exact h
  · intro _ _ _ _ _ ih h
    exact ih h
  · intro _ _ _ _ ih h
    exact ih h
  · intro _ h
    exact h
  · intro _ _ _ _ _ _ _ ihHead ihTail h
    exact ihTail (ihHead h)

/-- List form of `PPatOrder.true_mono`. -/
theorem PPatsOrder.true_mono {pps : List PPat} {finished : Bool}
    (orders : PPatsOrder true pps finished) : finished = true :=
  PPatOrder.true_mono (.tuple orders)

/-! ## Capture-admissible patterns below a hole-free header bind nothing -/

/-- A capture-admissible pattern below a hole-free header binds nothing. -/
theorem CaptureAdm.scopeVars_nil_of_order
    {signature : FrozenSig} {context : Context} {input : MonoCtx} :
    ∀ {pp : PPat} {pattern : Pattern} {target : Ty} {bindings : MonoCtx}
      {seen : Bool},
      CaptureAdm signature context input pp pattern target bindings →
      PPatOrder seen pp false →
      pattern.scopeVars = [] := by
  intro pp pattern target bindings seen admissible order
  refine CaptureAdm.rec
    (motive_1 := fun pp pattern _ _ _ =>
      ∀ {seen : Bool}, PPatOrder seen pp false → pattern.scopeVars = [])
    (motive_2 := fun pps patterns _ _ _ =>
      ∀ {seen : Bool}, PPatsOrder seen pps false →
        Pattern.scopeVarsList patterns = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ admissible order
  · intro _pattern _target _seen order
    cases order
  · intro _target _seen _order
    rfl
  · intro _name _expression _target _typing _seen _order
    rfl
  · intro _name _entry _pps _patterns _targets _result _bindings _find
      _children _inst ihList _seen order
    cases order with
    | ctor orders => exact ihList orders
  · intro _pps _patterns _targets _bindings _children ihList _seen order
    cases order with
    | tuple orders => exact ihList orders
  · intro _seen _orders
    rfl
  · intro _pp pattern _target _bindings pps patterns _targets _restBindings
      _head _tail ihHead ihTail _seen orders
    cases orders with
    | @cons _ _ middle _ _ headOrder tailOrders =>
        cases middle with
        | true => exact absurd (PPatsOrder.true_mono tailOrders) (by decide)
        | false =>
            have hHead := ihHead headOrder
            have hTail := ihTail tailOrders
            simp [Pattern.scopeVarsList, hHead, hTail]

/-- List form: capture-admissible components below a hole-free header bind
nothing. -/
theorem CaptureAdms.scopeVarsList_nil_of_order
    {signature : FrozenSig} {context : Context} {input : MonoCtx}
    {pps : List PPat} {patterns : List Pattern} {targets : List Ty}
    {bindings : MonoCtx} {seen : Bool}
    (admissible :
      CaptureAdms signature context input pps patterns targets bindings)
    (orders : PPatsOrder seen pps false) :
    Pattern.scopeVarsList patterns = [] :=
  CaptureAdm.scopeVars_nil_of_order (.tuple admissible) (.tuple orders)

/-! ## Removal of nothing, and the admissible shape alignment -/

/-- Removing nothing removes nothing. -/
theorem List.removeAll_nil_right (l : List String) : l.removeAll [] = l := by
  simp [List.removeAll]

/-- Capture admissibility aligns the clause header and the user pattern in
shape. -/
theorem CaptureAdm.shapeOK
    {signature : FrozenSig} {context : Context} {input : MonoCtx}
    {pp : PPat} {pattern : Pattern} {target : Ty} {bindings : MonoCtx}
    (admissible :
      CaptureAdm signature context input pp pattern target bindings) :
    ppShapeOK pp pattern = true := by
  refine CaptureAdm.rec
    (motive_1 := fun pp pattern _ _ _ => ppShapeOK pp pattern = true)
    (motive_2 := fun pps patterns _ _ _ => ppShapeOKList pps patterns = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ admissible
  · intro pattern _target
    cases pattern <;> rfl
  · intro _target
    rfl
  · intro _name _expression _target _typing
    rfl
  · intro _name _entry _pps _patterns _targets _result _bindings _find
      _children _inst ihList
    simp [ppShapeOK, ihList]
  · intro _pps _patterns _targets _bindings _children ihList
    simpa [ppShapeOK] using ihList
  · rfl
  · intro _pp _pattern _target _bindings _pps _patterns _targets
      _restBindings _head _tail ihHead ihTail
    simp [ppShapeOKList, ihHead, ihTail]

/-! ## The fuel-indexed master induction -/

/-- Fuel-indexed master induction behind `ppmSafe`/`ppmListSafe`: at every
fuel, the committed clause's primitive-pattern match and its component walk
are safe below an evaluation kernel covering the strictly smaller fuels. -/
private theorem ppmSafe_aux
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {input : MonoCtx}
    {ρa : Env} (fuel : Nat) :
    (∀ {pp : PPat} {pattern : Pattern} {target : Ty} {bindings : MonoCtx}
      {seen finished : Bool} {bound : List String},
      (evalKernel :
        ∀ {fuel' : Nat}, fuel' < fuel →
          ∀ {expression : Expr} {target' : Ty},
            TypingInvariant signature (input.toContext ++ context) expression
              target' →
            (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
            evalFuel SF fuel' ρa expression ≠ .stuck ∧
            ∀ value, evalFuel SF fuel' ρa expression = .ok value →
              ScopedValue value ∧ ValuePristine value ∧
              ValueTy signature value target') →
      CaptureAdm signature context input pp pattern target bindings →
      PPatOrder seen pp finished →
      (seen = false → bound = []) →
      (∀ name ∈ Pattern.exprVarsUnder bound pattern,
        name ∈ Env.names ρa) →
      Safe (fun outcome =>
        ∀ captures ppEnv, outcome = some (captures, ppEnv) →
          MonoEnvTys signature bindings ppEnv ∧
          EnvPristine ppEnv ∧ ScopedEnv ppEnv)
        (ppmFuel SF fuel ρa pp pattern)) ∧
    (∀ {pps : List PPat} {patterns : List Pattern} {targets : List Ty}
      {bindings : MonoCtx} {seen finished : Bool} {bound : List String},
      (evalKernel :
        ∀ {fuel' : Nat}, fuel' < fuel →
          ∀ {expression : Expr} {target' : Ty},
            TypingInvariant signature (input.toContext ++ context) expression
              target' →
            (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
            evalFuel SF fuel' ρa expression ≠ .stuck ∧
            ∀ value, evalFuel SF fuel' ρa expression = .ok value →
              ScopedValue value ∧ ValuePristine value ∧
              ValueTy signature value target') →
      CaptureAdms signature context input pps patterns targets bindings →
      PPatsOrder seen pps finished →
      (seen = false → bound = []) →
      (∀ name ∈ Pattern.exprVarsUnderList bound patterns,
        name ∈ Env.names ρa) →
      Safe (fun results =>
        MonoEnvTys signature bindings ((results.map Prod.snd).flatten) ∧
        EnvPristine ((results.map Prod.snd).flatten) ∧
        ScopedEnv ((results.map Prod.snd).flatten))
        (ppmListFuel SF fuel ρa pps patterns)) := by
  induction fuel with
  | zero =>
      constructor
      · intro _ _ _ _ _ _ _ _ _ _ _ _
        simp [ppmFuel]
      · intro _ _ _ _ _ _ _ _ _ _ _ _
        simp [ppmListFuel]
  | succ fuel ih =>
      obtain ⟨ihOne, ihList⟩ := ih
      constructor
      · -- One committed primitive-pattern pair at `fuel + 1`.
        intro pp pattern target bindings seen finished bound evalKernel
          admissible order boundEmpty ambient
        cases admissible with
        | hole =>
            simp only [ppmFuel]
            split
            · intro captures ppEnv h
              cases h
              exact ⟨.nil, .nil, .nil⟩
            · intro captures ppEnv h
              cases h
        | wild =>
            simp only [ppmFuel]
            split
            · intro captures ppEnv h
              cases h
              exact ⟨.nil, .nil, .nil⟩
            · intro captures ppEnv h
              cases h
        | @pval name expression _target typing =>
            cases order
            have hBound : bound = [] := boundEmpty rfl
            subst hBound
            have expressionFv :
                ∀ name' ∈ expression.freeVars, name' ∈ Env.names ρa := by
              intro name' membership
              refine ambient name' ?_
              simpa [Pattern.exprVarsUnder, List.removeAll_nil_right] using
                membership
            simp only [ppmFuel, RunResult.monad_bind_eq_bind]
            split
            · cases hEval : evalFuel SF fuel ρa expression with
              | ok value =>
                  simp only [RunResult.bind_ok, RunResult.pure_eq_ok]
                  intro captures ppEnv h
                  cases h
                  obtain ⟨valueScoped, valuePristine, valueTyped⟩ :=
                    (evalKernel (Nat.lt_succ_self fuel) typing
                      expressionFv).2 value hEval
                  exact ⟨.cons valueTyped .nil, .cons valuePristine .nil,
                    .cons valueScoped .nil⟩
              | timeout =>
                  simp only [RunResult.bind_timeout]
                  exact Safe.timeout
              | stuck =>
                  exact absurd hEval
                    ((evalKernel (Nat.lt_succ_self fuel) typing
                      expressionFv).1)
            · intro captures ppEnv h
              cases h
        | @ctor name _entry pps patterns _targets _result _bindings _find
            children _inst =>
            cases order with
            | ctor orders =>
                have listSafe := ihList
                  (fun {fuel'} h => evalKernel (Nat.lt_succ_of_lt h))
                  children orders boundEmpty
                  (by
                    intro name' membership
                    refine ambient name' ?_
                    simpa [Pattern.exprVarsUnder] using membership)
                simp only [ppmFuel, RunResult.monad_bind_eq_bind]
                split
                · cases hList : ppmListFuel SF fuel ρa pps patterns with
                  | ok results =>
                      simp only [RunResult.bind_ok, RunResult.pure_eq_ok]
                      intro captures ppEnv h
                      cases h
                      rw [hList] at listSafe
                      obtain ⟨bindingsTyped, bindingsPristine,
                        bindingsScoped⟩ := listSafe
                      exact ⟨bindingsTyped, bindingsPristine, bindingsScoped⟩
                  | timeout =>
                      simp only [RunResult.bind_timeout]
                      exact Safe.timeout
                  | stuck =>
                      exact absurd hList listSafe.not_stuck
                · intro captures ppEnv h
                  cases h
        | @tuple pps patterns _targets _bindings children =>
            cases order with
            | tuple orders =>
                have listSafe := ihList
                  (fun {fuel'} h => evalKernel (Nat.lt_succ_of_lt h))
                  children orders boundEmpty
                  (by
                    intro name' membership
                    refine ambient name' ?_
                    simpa [Pattern.exprVarsUnder] using membership)
                simp only [ppmFuel, RunResult.monad_bind_eq_bind]
                split
                · cases hList : ppmListFuel SF fuel ρa pps patterns with
                  | ok results =>
                      simp only [RunResult.bind_ok, RunResult.pure_eq_ok]
                      intro captures ppEnv h
                      cases h
                      rw [hList] at listSafe
                      obtain ⟨bindingsTyped, bindingsPristine,
                        bindingsScoped⟩ := listSafe
                      exact ⟨bindingsTyped, bindingsPristine, bindingsScoped⟩
                  | timeout =>
                      simp only [RunResult.bind_timeout]
                      exact Safe.timeout
                  | stuck =>
                      exact absurd hList listSafe.not_stuck
                · intro captures ppEnv h
                  cases h
      · -- Componentwise walk at `fuel + 1`.
        intro pps patterns targets bindings seen finished bound evalKernel
          admissible orders boundEmpty ambient
        cases admissible with
        | nil =>
            simp only [ppmListFuel]
            exact ⟨.nil, .nil, .nil⟩
        | @cons pp pattern _target headBindings pps patterns _targets
            restBindings head tail =>
            cases orders with
            | @cons _ _ middle _ _ headOrder tailOrders =>
                have headSafe := ihOne
                  (fun {fuel'} h => evalKernel (Nat.lt_succ_of_lt h))
                  head headOrder boundEmpty
                  (by
                    intro name' membership
                    refine ambient name' ?_
                    simp only [Pattern.exprVarsUnderList, List.mem_append]
                    exact .inl membership)
                have tailBoundEmpty :
                    middle = false → bound ++ pattern.scopeVars = [] := by
                  intro hMiddle
                  subst hMiddle
                  have hSeen : seen = false := by
                    cases seen with
                    | false => rfl
                    | true =>
                        exact absurd (PPatOrder.true_mono headOrder)
                          (by decide)
                  have hBound : bound = [] := boundEmpty hSeen
                  have hScope : pattern.scopeVars = [] :=
                    CaptureAdm.scopeVars_nil_of_order head headOrder
                  simp [hBound, hScope]
                have tailSafe := ihList
                  (fun {fuel'} h => evalKernel (Nat.lt_succ_of_lt h))
                  tail tailOrders tailBoundEmpty
                  (by
                    intro name' membership
                    refine ambient name' ?_
                    simp only [Pattern.exprVarsUnderList, List.mem_append]
                    exact .inr membership)
                simp only [ppmListFuel, RunResult.monad_bind_eq_bind]
                cases hHead : ppmFuel SF fuel ρa pp pattern with
                | ok outcome =>
                    simp only [RunResult.bind_ok]
                    rw [hHead] at headSafe
                    cases outcome with
                    | none =>
                        cases ppmFuel_ok hHead with
                        | fail hFalse =>
                            have hTrue := CaptureAdm.shapeOK head
                            rw [hFalse] at hTrue
                            exact absurd hTrue (by decide)
                    | some result =>
                        obtain ⟨captures, ppEnv⟩ := result
                        obtain ⟨headTyped, headPristine, headScoped⟩ :=
                          headSafe captures ppEnv rfl
                        cases hTail :
                            ppmListFuel SF fuel ρa pps patterns with
                        | ok results =>
                            simp only [RunResult.bind_ok,
                              RunResult.pure_eq_ok]
                            rw [hTail] at tailSafe
                            obtain ⟨tailTyped, tailPristine, tailScoped⟩ :=
                              tailSafe
                            refine ⟨?_, ?_, ?_⟩
                            · simpa [List.flatten_cons] using
                                headTyped.append tailTyped
                            · simpa [List.flatten_cons] using
                                headPristine.append tailPristine
                            · simpa [List.flatten_cons] using
                                headScoped.append tailScoped
                        | timeout =>
                            simp only [RunResult.bind_timeout]
                            exact Safe.timeout
                        | stuck =>
                            exact absurd hTail tailSafe.not_stuck
                | timeout =>
                    simp only [RunResult.bind_timeout]
                    exact Safe.timeout
                | stuck =>
                    exact absurd hHead headSafe.not_stuck

/-! ## The public statements -/

/-- The committed clause's primitive-pattern match is safe: it cannot
stick, and a successful match returns a capture environment typed at the
admissible binding context, pristine, and scoped.  The embedded `#$x`
evaluations are received through an evaluation kernel covering exactly the
strictly smaller fuels. -/
theorem ppmSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {input : MonoCtx}
    {ρa : Env} :
    ∀ {fuel : Nat} {pp : PPat} {pattern : Pattern} {target : Ty}
      {bindings : MonoCtx} {seen finished : Bool} {bound : List String},
      (evalKernel :
        ∀ {fuel' : Nat}, fuel' < fuel →
          ∀ {expression : Expr} {target' : Ty},
            TypingInvariant signature (input.toContext ++ context) expression
              target' →
            (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
            evalFuel SF fuel' ρa expression ≠ .stuck ∧
            ∀ value, evalFuel SF fuel' ρa expression = .ok value →
              ScopedValue value ∧ ValuePristine value ∧
              ValueTy signature value target') →
      CaptureAdm signature context input pp pattern target bindings →
      PPatOrder seen pp finished →
      (seen = false → bound = []) →
      (∀ name ∈ Pattern.exprVarsUnder bound pattern,
        name ∈ Env.names ρa) →
      Safe (fun outcome =>
        ∀ captures ppEnv, outcome = some (captures, ppEnv) →
          MonoEnvTys signature bindings ppEnv ∧
          EnvPristine ppEnv ∧ ScopedEnv ppEnv)
        (ppmFuel SF fuel ρa pp pattern) := by
  intro fuel pp pattern target bindings seen finished bound evalKernel
    admissible order boundEmpty ambient
  exact (ppmSafe_aux fuel).1 evalKernel admissible order boundEmpty ambient

/-- Componentwise form of `ppmSafe`: the walk over the committed clause's
components is safe, and its successful results flatten to a capture
environment typed at the concatenated admissible binding context, pristine,
and scoped. -/
theorem ppmListSafe
    {signature : FrozenSig} {SF : RuntimeSigF}
    {context : Context} {input : MonoCtx}
    {ρa : Env} :
    ∀ {fuel : Nat} {pps : List PPat} {patterns : List Pattern}
      {targets : List Ty} {bindings : MonoCtx} {seen finished : Bool}
      {bound : List String},
      (evalKernel :
        ∀ {fuel' : Nat}, fuel' < fuel →
          ∀ {expression : Expr} {target' : Ty},
            TypingInvariant signature (input.toContext ++ context) expression
              target' →
            (∀ name ∈ expression.freeVars, name ∈ Env.names ρa) →
            evalFuel SF fuel' ρa expression ≠ .stuck ∧
            ∀ value, evalFuel SF fuel' ρa expression = .ok value →
              ScopedValue value ∧ ValuePristine value ∧
              ValueTy signature value target') →
      CaptureAdms signature context input pps patterns targets bindings →
      PPatsOrder seen pps finished →
      (seen = false → bound = []) →
      (∀ name ∈ Pattern.exprVarsUnderList bound patterns,
        name ∈ Env.names ρa) →
      Safe (fun results =>
        MonoEnvTys signature bindings ((results.map Prod.snd).flatten) ∧
        EnvPristine ((results.map Prod.snd).flatten) ∧
        ScopedEnv ((results.map Prod.snd).flatten))
        (ppmListFuel SF fuel ρa pps patterns) := by
  intro fuel pps patterns targets bindings seen finished bound evalKernel
    admissible orders boundEmpty ambient
  exact (ppmSafe_aux fuel).2 evalKernel admissible orders boundEmpty ambient

end TypePM
