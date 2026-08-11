import TypePM.DemandTypingTerminalAuditTree
import TypePM.DemandTypingTerminalErasure
import TypePM.DemandTypingRuntimeErasureMatchAll
import TypePM.DemandTypingIdempotence

/-!
# Fixed-root erasure of terminal-audited demand typing

The recursive certificate is indexed by one root substitution.  Every
recursive call therefore receives the exact chronological factorization from
its local output cut to that root.  This is weaker, and more useful here, than
the old claim that a node is safe under every imaginable future suffix.
-/

namespace TypePM

open DemandTypingIdempotence

namespace DDErasure.StateFactorization

private theorem liftDual_eq
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : Dual}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.applySubst S = right.applySubst S) :
    left.applySubst S' = right.applySubst S' := by
  rcases factorization with ⟨post, rfl, _⟩
  simpa only [Dual.applySubst_seq] using
    congrArg (Dual.applySubst post) equality

private theorem liftDualList_eq
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : List Dual}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.map (Dual.applySubst S) =
      right.map (Dual.applySubst S)) :
    left.map (Dual.applySubst S') = right.map (Dual.applySubst S') := by
  rcases factorization with ⟨post, rfl, _⟩
  simpa only [Dual.map_applySubst_seq] using
    congrArg (List.map (Dual.applySubst post)) equality

private theorem liftTyList_eq
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : List Ty}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.map S.apply = right.map S.apply) :
    left.map S'.apply = right.map S'.apply := by
  rcases factorization with ⟨post, rfl, _⟩
  simpa only [Subst.map_apply_seq] using
    congrArg (List.map post.apply) equality

private theorem liftBindings_eq
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : MonoCtx}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : left.applySubst S = right.applySubst S) :
    left.applySubst S' = right.applySubst S' := by
  rcases factorization with ⟨post, rfl, _⟩
  simpa only [MonoCtx.applySubst_seq] using
    congrArg (MonoCtx.applySubst post) equality

end DDErasure.StateFactorization

private theorem freshPatternVariables_of_bounded
    {signature : FrozenSig} {q : InferenceBase.FreshSupply}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    (closed : signature.SchemesClosed)
    (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindings) :
    FreshCap signature context parameters bindings ⟨q.nextCap⟩ ∧
      FreshTy signature context parameters bindings q.nextTy := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [closed.signatureCaps]
      simp
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      exact Nat.lt_irrefl q.nextCap
        ((contextBounded entry entryMem).caps ⟨q.nextCap⟩ variableMem)
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      rcases List.mem_append.mp variableMem with capMem | targetMem
      · exact Nat.lt_irrefl q.nextCap
          ((parametersBounded entry entryMem).1 ⟨q.nextCap⟩ capMem)
      · exact Nat.lt_irrefl q.nextCap
          ((parametersBounded entry entryMem).2.caps ⟨q.nextCap⟩ targetMem)
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      exact Nat.lt_irrefl q.nextCap
        ((bindingsBounded entry entryMem).caps ⟨q.nextCap⟩ variableMem)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [closed.signatureTargets]
      simp
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      exact Nat.lt_irrefl q.nextTy
        ((contextBounded entry entryMem).targets q.nextTy variableMem)
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      exact Nat.lt_irrefl q.nextTy
        ((parametersBounded entry entryMem).2.targets q.nextTy variableMem)
    · intro membership
      obtain ⟨entry, entryMem, variableMem⟩ :=
        List.mem_flatMap.mp membership
      exact Nat.lt_irrefl q.nextTy
        ((bindingsBounded entry entryMem).targets q.nextTy variableMem)

private theorem closedPatternCtorInstanceAt
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String} {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (q : InferenceBase.FreshSupply) (terminal : Subst) :
    entry.Inst
      ((InferenceBase.instantiateCtorScheme q entry.scheme).value.1.map
        terminal.apply)
      (terminal.apply
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2) := by
  apply CtorScheme.Inst.transport
    (InferenceBase.instantiateCtorScheme_sound q entry.scheme)
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    rw [(closed.patternCtors lookup).1] at membership
    contradiction
  · intro varId membership
    rw [(closed.patternCtors lookup).2] at membership
    contradiction

private theorem closedDualSchemeInstanceAt
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    {q : InferenceBase.FreshSupply} {S : Subst} (Sb : S.BoundedBy q)
    {terminalSupply : InferenceBase.FreshSupply} {terminal : Subst}
    {ledger terminalLedger : CapabilityOriginLedger}
    (toTerminal : DDErasure.StateFactorization
      (InferenceBase.instantiateDualScheme q scheme).supply S
      (DDLedger.markDualInstance ledger q scheme)
      terminalSupply terminal terminalLedger) :
    scheme.ValueFlowInst
      ((InferenceBase.instantiateDualScheme q scheme).value.1.map
        (Dual.applySubst terminal))
      ((InferenceBase.instantiateDualScheme q scheme).value.2.applySubst
        terminal) := by
  rcases toTerminal with ⟨post, terminalEquation, admissible⟩
  apply (DualScheme.instantiateVariableInstAt q scheme).transportResult
  · intro varId membership
    rw [(closed.patternFuns lookup).1] at membership
    contradiction
  · intro varId membership
    rw [(closed.patternFuns lookup).2] at membership
    contradiction
  · intro binder binderMem image imageEquation
    have canonicalEquation :
        (InferenceBase.instantiateDualScheme q scheme).subst.cap binder =
          .var ⟨q.nextCap + binder.id⟩ := by
      simp [InferenceBase.instantiateDualScheme,
        InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
        binderMem]
    have imageEquality : image = ⟨q.nextCap + binder.id⟩ := by
      rw [canonicalEquation] at imageEquation
      exact Cap.var.inj imageEquation.symm
    subst image
    rcases admissible.dualInstanceImageVariable binderMem with
      ⟨finalImage, postEquation⟩
    refine ⟨finalImage, ?_⟩
    rw [terminalEquation]
    change (S.cap ⟨q.nextCap + binder.id⟩).apply post.cap =
      .var finalImage
    rw [Sb.capFixedAbove ⟨q.nextCap + binder.id⟩
      (Nat.le_add_right q.nextCap binder.id)]
    simpa only [Cap.apply] using postEquation

private theorem freezeExportFactor
    (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) (capImages : List CapVar)
    (exportedPayload : Ty) :
    DDErasure.StateFactorization q S ledger q S
      (DDLedger.freezeExport ledger S capImages exportedPayload) := by
  exact DDErasure.StateFactorization.ofTransition
    (SupplyExtends.refl q)
    (DDLedger.RefinesBelow.freezeExport q ledger S capImages exportedPayload)

private theorem closedDualSchemeInstanceAlignedAt
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme)
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} (Sb : S.BoundedBy q)
    {terminalSupply : InferenceBase.FreshSupply} {terminal : Subst}
    {terminalLedger : CapabilityOriginLedger} {duals : List Dual}
    (toTerminal : DDErasure.StateFactorization
      (InferenceBase.instantiateDualScheme q scheme).supply S
      (DDLedger.markDualInstance ledger q scheme)
      terminalSupply terminal terminalLedger)
    (dualsEquality : duals.map (Dual.applySubst terminal) =
      (InferenceBase.instantiateDualScheme q scheme).value.1.map
        (Dual.applySubst terminal)) :
    scheme.ValueFlowInst (duals.map (Dual.applySubst terminal))
      ((InferenceBase.instantiateDualScheme q scheme).value.2.applySubst
        terminal) := by
  have instanceAt := closedDualSchemeInstanceAt closed lookup Sb toTerminal
  rw [← dualsEquality] at instanceAt
  exact instanceAt

private theorem childDepth_le_fuel {child parent fuel : Nat}
    (parent_le : parent ≤ fuel + 1) (child_lt : child < parent) :
    child ≤ fuel := by
  omega

local macro "audit_child_bound" : term =>
  `(childDepth_le_fuel (by assumption) (by
      simp [DDSynthTerminalAudit.depth, DDSynthsTerminalAudit.depth,
        DDCheckTerminalAudit.depth, DDChecksTerminalAudit.depth,
        DDPatternTerminalAudit.depth, DDPatternsTerminalAudit.depth,
        DDArmsTerminalAudit.depth, DDClauseTerminalAudit.depth,
        DDClausesTerminalAudit.depth, Nat.lt_add_one_iff,
        Nat.le_max_left, Nat.le_max_right]))

set_option maxHeartbeats 4000000 in
mutual

private theorem DDSynthTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (audit : DDSynthTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeTyping signature (context.applySubst terminal) expression
      (terminal.apply target) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDSynthTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | var =>
      rename_i name scheme lookup
      rcases toTerminal with ⟨post, equation, admissible⟩
      exact DDSynthOrigin.runtimeErasureUnder_var lookup Sid Sb equation
        admissible
  | lam bodyAudit =>
      rename_i name body bodyTarget bodyRaw bodyOrigin
      have extension := SupplyExtends.bumpTy q 1
      have domainB : Ty.BoundedBy { q with nextTy := q.nextTy + 1 }
          (.var q.nextTy) := Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      have bodyTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := (name, Scheme.mono (.var q.nextTy)) :: context) bodyAudit
        fuel' audit_child_bound toTerminal closed
        Sid (Sb.mono extension)
        (Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainB)
          (contextBounded.mono extension))
      simp only [Context.applySubst, List.map_cons, Scheme.applyMeta_mono,
        Subst.apply_fn] at bodyTyping ⊢
      exact RuntimeTyping.lam bodyTyping
  | fix bodyAudit =>
      rename_i argument self body bodyTarget S1 distinct direct nonMatcher
        bodyRaw aligned bodyOrigin
      have extension := SupplyExtends.bumpTy q 2
      have domainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var q.nextTy) := Ty.BoundedBy.varOf (by
            exact Nat.lt_add_of_pos_right (by decide))
      have codomainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
          (.var (q.nextTy + 1)) := Ty.BoundedBy.varOf (by
            exact Nat.add_lt_add_left (by decide : 1 < 2) q.nextTy)
      have bodyContextB : Context.BoundedBy { q with nextTy := q.nextTy + 2 }
          ((argument, Scheme.mono (.var q.nextTy)) ::
            (self, Scheme.mono
              (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context) :=
        Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainB)
          (Context.BoundedBy.cons
            (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
            (contextBounded.mono extension))
      obtain ⟨S1b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
        (Sb.mono extension) bodyContextB
      have alignFactor := DDErasure.StateFactorization.ofAlignTypes aligned
        S1b bodyB (codomainB.mono bodyOrigin.erase.supplyExtends)
      have bodyTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := _) bodyAudit fuel' audit_child_bound
        (alignFactor.trans toTerminal) closed Sid (Sb.mono extension)
        bodyContextB
      rcases toTerminal with ⟨post, terminalEquation, _⟩
      have finalResultEquality : terminal.apply bodyTarget =
          terminal.apply (.var (q.nextTy + 1)) := by
        rw [terminalEquation, Subst.seq_apply, Subst.seq_apply]
        exact congrArg post.apply aligned.output_equal
      have bodyExpected : RuntimeTyping signature
          ((argument, Scheme.mono (terminal.apply (.var q.nextTy))) ::
            (self, Scheme.mono
              (.fn (terminal.apply (.var q.nextTy))
                (terminal.apply (.var (q.nextTy + 1))))) ::
            context.applySubst terminal) body
          (terminal.apply (.var (q.nextTy + 1))) := by
        rw [finalResultEquality] at bodyTyping
        simpa only [Context.applySubst, List.map_cons,
          Scheme.applyMeta_mono, Subst.apply_fn] using bodyTyping
      exact RuntimeTyping.fixE distinct direct bodyExpected
  | app functionAudit argumentAudit =>
      rename_i function functionTarget q1 S1 ledger1 S2 argument aligned
        functionRaw argumentRaw functionOrigin argumentOrigin
      obtain ⟨S1b, functionB⟩ := functionOrigin.erase.boundedBy closed Sb
        contextBounded
      have extension := SupplyExtends.bumpTy q1 2
      have domainB : Ty.BoundedBy
          { q1 with nextTy := q1.nextTy + 2 } (.var q1.nextTy) :=
        Ty.BoundedBy.varOf (by
          change q1.nextTy < q1.nextTy + 2
          omega)
      have codomainB : Ty.BoundedBy
          { q1 with nextTy := q1.nextTy + 2 } (.var (q1.nextTy + 1)) :=
        Ty.BoundedBy.varOf (by
          change q1.nextTy + 1 < q1.nextTy + 2
          omega)
      have shapeB := Ty.BoundedBy.fnOf domainB codomainB
      have S2b := aligned.erase.boundedBy (S1b.mono extension)
        (functionB.mono extension) shapeB
      have argumentFactor := DDCheckOrigin.factorize argumentOrigin closed S2b
        (contextBounded.mono
          (functionOrigin.erase.supplyExtends.trans extension)) domainB
      have allocation := DDErasure.StateFactorization.ofTransition
        (S := S1) (before := ledger1) (after := ledger1) extension
        (DDLedger.RefinesBelow.refl _ _)
      have alignment := DDErasure.StateFactorization.ofAlignTypes aligned
        (S1b.mono extension) (functionB.mono extension) shapeB
      have functionToTerminal :=
        ((allocation.trans alignment).trans argumentFactor).trans toTerminal
      have functionTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := context) functionAudit fuel' audit_child_bound functionToTerminal
        closed Sid Sb contextBounded
      have S2id := DemandTypingIdempotence.DDAlignTypes.idempotent
        aligned.erase (DemandTypingIdempotence.DDSynth.idempotent
          functionOrigin.erase Sid)
      have argumentTyping := DDCheckTerminalAudit.runtimeErasureFuel
        (context := context) argumentAudit fuel' audit_child_bound
        toTerminal closed S2id S2b
        (contextBounded.mono
          (functionOrigin.erase.supplyExtends.trans extension)) domainB
      rcases argumentFactor with ⟨argumentPost, argumentEquation, _⟩
      rcases toTerminal with ⟨terminalPost, terminalEquation, _⟩
      have finalShape : terminal.apply functionTarget = terminal.apply
          (.fn (.var q1.nextTy) (.var (q1.nextTy + 1))) := by
        rw [terminalEquation, argumentEquation, Subst.seq_apply,
          Subst.seq_apply, Subst.seq_apply, Subst.seq_apply]
        exact congrArg terminalPost.apply
          (congrArg argumentPost.apply aligned.output_equal)
      apply RuntimeTyping.app
        (domain := terminal.apply (.var q1.nextTy))
        (codomain := terminal.apply (.var (q1.nextTy + 1)))
      · rw [finalShape] at functionTyping
        simpa only [Subst.apply_fn] using functionTyping
      · exact argumentTyping
  | lit =>
      rename_i value
      rcases toTerminal with ⟨post, equation, admissible⟩
      exact DDSynthOrigin.runtimeErasureUnder_lit _ _ _ _ _ _
        equation admissible
  | tuple childrenAudit =>
      rename_i expressions targets childrenRaw childrenOrigin
      simpa only [Subst.apply_prod, Subst.applyList_eq_map] using
        RuntimeTyping.tuple
          (DDSynthsTerminalAudit.runtimeErasureFuel (context := context)
            childrenAudit fuel' audit_child_bound toTerminal closed Sid Sb
            contextBounded)
  | ctor childrenAudit =>
      rename_i scheme expressions ledger1 name lookup childrenRaw childrenOrigin
      have freezing := DDErasure.StateFactorization.ofTransition
        (S := S') (before := ledger1)
        (after := DDLedger.freezeExport ledger1 S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
        (SupplyExtends.refl q')
        (DDLedger.RefinesBelow.freezeExport q' ledger1 S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q scheme
      have childrenTyping := DDChecksTerminalAudit.runtimeErasureFuel
        (context := context) childrenAudit fuel' audit_child_bound
        (freezing.trans toTerminal) closed Sid (Sb.mono ext)
        (contextBounded.mono ext) instB.1
      have instanceAt : scheme.Inst
          ((InferenceBase.instantiateCtorScheme q scheme).value.1.map
            terminal.apply)
          (terminal.apply
            (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
        apply CtorScheme.Inst.transport
          (InferenceBase.instantiateCtorScheme_sound q scheme)
        apply CtorScheme.instCompositionAdm_of_free_fixed
        · intro varId membership
          rw [(closed.dataCtors lookup).1] at membership
          contradiction
        · intro varId membership
          rw [(closed.dataCtors lookup).2] at membership
          contradiction
      exact RuntimeTyping.ctor lookup instanceAt childrenTyping
  | prim childrenAudit =>
      rename_i scheme expressions ledger1 op lookup childrenRaw childrenOrigin
      have freezing := DDErasure.StateFactorization.ofTransition
        (S := S') (before := ledger1)
        (after := DDLedger.freezeExport ledger1 S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
        (SupplyExtends.refl q')
        (DDLedger.RefinesBelow.freezeExport q' ledger1 S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.primitives lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q scheme
      have childrenTyping := DDChecksTerminalAudit.runtimeErasureFuel
        (context := context) childrenAudit fuel' audit_child_bound
        (freezing.trans toTerminal) closed Sid (Sb.mono ext)
        (contextBounded.mono ext) instB.1
      have instanceAt : scheme.Inst
          ((InferenceBase.instantiateCtorScheme q scheme).value.1.map
            terminal.apply)
          (terminal.apply
            (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
        apply CtorScheme.Inst.transport
          (InferenceBase.instantiateCtorScheme_sound q scheme)
        apply CtorScheme.instCompositionAdm_of_free_fixed
        · intro varId membership
          rw [(closed.primitives lookup).1] at membership
          contradiction
        · intro varId membership
          rw [(closed.primitives lookup).2] at membership
          contradiction
      exact RuntimeTyping.prim lookup instanceAt childrenTyping
  | letE valueAudit bodyAudit facts =>
      rename_i name value body valueTarget q1 S1 ledger1 valueRaw
        bodyRaw valueOrigin bodyOrigin
      obtain ⟨S1b, valueB⟩ := valueOrigin.erase.boundedBy closed Sb
        contextBounded
      have bodyContextB : Context.BoundedBy _
          ((name, signature.generalize (context.applySubst S1)
            (S1.apply valueTarget)) :: context) :=
        Context.BoundedBy.cons
          (FrozenSig.generalize_boundedBy (S1b.apply valueB))
          (contextBounded.mono valueOrigin.erase.supplyExtends)
      have bodyFactor := DDSynthOrigin.factorize bodyOrigin closed S1b
        bodyContextB
      have valueTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := context) valueAudit fuel' audit_child_bound
        (bodyFactor.trans toTerminal) closed Sid Sb contextBounded
      have S1id := DemandTypingIdempotence.DDSynth.idempotent
        valueOrigin.erase Sid
      have bodyTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := _) bodyAudit fuel' audit_child_bound toTerminal closed S1id S1b
        bodyContextB
      change RuntimeTyping signature
        ((name, (signature.generalize (context.applySubst S1)
          (S1.apply valueTarget)).applyMeta terminal) ::
          context.applySubst terminal) body (terminal.apply target)
        at bodyTyping
      rw [facts.stable] at bodyTyping
      exact RuntimeTyping.letE valueTyping bodyTyping
  | something =>
      rcases toTerminal with ⟨post, equation, admissible⟩
      exact DDSynthOrigin.runtimeErasureUnder_something _ _ _ _ _
        equation admissible
  | matcher clausesAudit facts =>
      rename_i clauses rawHoleLists evidence capability ledger1 inferred
        catchAll binders coverage collected clauseCaps arms clausesRaw
        clausesOrigin
      rcases facts.valid with
        ⟨terminalEvidence, collected, inferred, clauseCaps, arms, coverage⟩
      have ext := SupplyExtends.bumpTy q 1
      have sharedB : Ty.BoundedBy { q with nextTy := q.nextTy + 1 }
          (.var q.nextTy) := Ty.BoundedBy.varOf (Nat.lt_succ_self _)
      have freezing := DDErasure.StateFactorization.ofTransition
        (S := S') (before := ledger1)
        (after := DDLedger.freezeMatcherProducer ledger1 capability)
        (SupplyExtends.refl q')
        (DDLedger.RefinesBelow.freezeMatcherProducer q' ledger1 capability)
      have clausesTyping := DDClausesTerminalAudit.runtimeErasureFuel
        (context := context) clausesAudit fuel' audit_child_bound
        (freezing.trans toTerminal) closed
        Sid (Sb.mono ext) (contextBounded.mono ext) sharedB
        (capability := capability.apply terminal.cap)
        (evidences := terminalEvidence)
        (Inference.clauseCapsListCheck_sound clauseCaps)
        (Inference.collectClauseEvidence_sound collected)
      have binderWitness := Inference.matcherBindersCheck_sound binders
      simpa only [Subst.apply_matcher] using
        RuntimeTyping.matcher (ResolvedClausesTy.ofShared clausesTyping)
          inferred (Inference.catchAllLastCheck_sound catchAll)
          (Inference.armExhaustiveCheck_sound arms)
          binderWitness.1 binderWitness.2
          (Inference.coverageCheck_sound coverage)
  | matchAll targetAudit patternAudit matcherAudit bodyAudit =>
      rename_i targetExpr targetTarget q1 S1 ledger1 pattern dual bindings q2
        S2 ledger2 S3 matcherExpr q3 S4 ledger3 body bodyTarget targetAligned
        patternRaw patternOrigin matcherRaw matcherOrigin targetRaw bodyRaw
        targetOrigin bodyOrigin
      obtain ⟨S1b, targetB⟩ := targetOrigin.erase.boundedBy closed Sb
        contextBounded
      have ext1 := targetOrigin.erase.supplyExtends
      obtain ⟨S2b, dualB, bindingsB⟩ := patternOrigin.erase.boundedBy
        closed S1b (contextBounded.mono ext1)
        (fun entry mem => nomatch mem) (fun entry mem => nomatch mem)
      have ext2 := patternOrigin.erase.supplyExtends
      have alignFactor := DDErasure.StateFactorization.ofAlignTypes
        targetAligned S2b dualB.2 (targetB.mono ext2)
      have S3b := targetAligned.erase.boundedBy S2b dualB.2
        (targetB.mono ext2)
      have matcherExpectedB := Ty.BoundedBy.slotOf dualB.1
        (targetB.mono ext2)
      have matcherFactor := DDCheckOrigin.factorize matcherOrigin closed S3b
        (contextBounded.mono (ext1.trans ext2)) matcherExpectedB
      have S4b := matcherOrigin.erase.boundedBy closed S3b
        (contextBounded.mono (ext1.trans ext2)) matcherExpectedB
      have ext3 := matcherOrigin.erase.supplyExtends
      have bodyContextB := Context.BoundedBy.append
        ((bindingsB.mono ext3).toContext)
        (contextBounded.mono ((ext1.trans ext2).trans ext3))
      have bodyFactor := DDSynthOrigin.factorize bodyOrigin closed S4b
        bodyContextB
      have patternFactor := DDPatternOrigin.factorize patternOrigin closed S1b
        (contextBounded.mono ext1) (fun entry mem => nomatch mem)
        (fun entry mem => nomatch mem)
      have targetAt := DDSynthTerminalAudit.runtimeErasureFuel
        (context := context) targetAudit fuel' audit_child_bound
        (patternFactor.trans
          ((alignFactor.trans matcherFactor).trans bodyFactor) |>.trans
            toTerminal) closed Sid Sb contextBounded
      have S1id := DemandTypingIdempotence.DDSynth.idempotent
        targetOrigin.erase Sid
      have patternAt := DDPatternTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := []) patternAudit fuel'
        (childDepth_le_fuel (by assumption) (by
          simp only [DDSynthTerminalAudit.depth, Nat.lt_add_one_iff]
          exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
        (((alignFactor.trans matcherFactor).trans bodyFactor).trans toTerminal)
        closed S1id S1b (contextBounded.mono ext1)
        (fun entry mem => nomatch mem) (fun entry mem => nomatch mem)
      have S2id := DemandTypingIdempotence.DDPattern.idempotent
        patternOrigin.erase S1id
      have S3id := DemandTypingIdempotence.DDAlignTypes.idempotent
        targetAligned.erase S2id
      have matcherAt := DDCheckTerminalAudit.runtimeErasureFuel
        (context := context) matcherAudit fuel'
        (childDepth_le_fuel (by assumption) (by
          simp only [DDSynthTerminalAudit.depth, Nat.lt_add_one_iff]
          exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)))
        ((bodyFactor.trans toTerminal)) closed S3id S3b
        (contextBounded.mono (ext1.trans ext2)) matcherExpectedB
      have S4id := DemandTypingIdempotence.DDCheck.idempotent
        matcherOrigin.erase S3id
      have bodyAt := DDSynthTerminalAudit.runtimeErasureFuel
        (context := _) bodyAudit fuel'
        (childDepth_le_fuel (by assumption) (by
          simp only [DDSynthTerminalAudit.depth, Nat.lt_add_one_iff]
          exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)))
        toTerminal closed S4id S4b
        bodyContextB
      have targetEq : terminal.apply dual.target =
          terminal.apply targetTarget := by
        exact ((matcherFactor.trans bodyFactor).trans toTerminal).liftTyEquality
          targetAligned.output_equal
      rw [targetEq] at patternAt
      have bodyAt' : RuntimeTyping signature
          ((bindings.applySubst terminal).toContext ++
            context.applySubst terminal) body (terminal.apply bodyTarget) := by
        simpa only [Context.applySubst_append,
          MonoCtx.toContext_applySubst] using bodyAt
      change RuntimeTyping signature (context.applySubst terminal)
        (.matchAll targetExpr matcherExpr pattern body)
        (Ty.listT (terminal.apply bodyTarget))
      exact RuntimeTyping.matchAll targetAt
        (ResolvedPatternTy.ofTerminal patternAt)
        (by simpa only [Subst.apply_slot] using matcherAt) bodyAt'
  | fixMatcher bodyAudit =>
      rename_i q0 argument domain self codomain clauses bodyTarget S1 distinct
        direct placeholder bodyRaw aligned bodyOrigin
      obtain ⟨domainB, codomainB⟩ :=
        fixMatcherPlaceholderSupply_boundedBy placeholder
      have ext := SupplyExtends.fixMatcherPlaceholder placeholder
      have bodyContextB : Context.BoundedBy _
          ((argument, Scheme.mono domain) ::
            (self, Scheme.mono (.fn domain codomain)) :: context) :=
        Context.BoundedBy.cons (Scheme.BoundedBy.ofMono domainB)
          (Context.BoundedBy.cons
            (Scheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
            (contextBounded.mono ext))
      obtain ⟨S1b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
        (Sb.mono ext) bodyContextB
      have alignFactor := DDErasure.StateFactorization.ofAlignTypes aligned
        S1b bodyB (codomainB.mono bodyOrigin.erase.supplyExtends)
      have bodyTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := _) bodyAudit fuel' audit_child_bound
        (alignFactor.trans toTerminal) closed Sid (Sb.mono ext) bodyContextB
      rcases toTerminal with ⟨post, terminalEquation, _⟩
      have finalResultEquality : terminal.apply bodyTarget =
          terminal.apply codomain := by
        rw [terminalEquation, Subst.seq_apply, Subst.seq_apply]
        exact congrArg post.apply aligned.output_equal
      have bodyExpected : RuntimeTyping signature
          ((argument, Scheme.mono (terminal.apply domain)) ::
            (self, Scheme.mono
              (.fn (terminal.apply domain) (terminal.apply codomain))) ::
            context.applySubst terminal) (.matcher clauses)
          (terminal.apply codomain) := by
        rw [finalResultEquality] at bodyTyping
        simpa only [Context.applySubst, List.map_cons,
          Scheme.applyMeta_mono, Subst.apply_fn] using bodyTyping
      exact RuntimeTyping.fixE distinct direct bodyExpected

termination_by fuel

private theorem DDSynthsTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (audit : DDSynthsTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    ExprsTy signature (context.applySubst terminal) expressions
      (targets.map terminal.apply) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDSynthsTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | nil => exact ExprsTy.nil
  | cons headAudit tailAudit =>
      rename_i expression target q1 S1 ledger1 expressions targets headRaw
        tailRaw headOrigin tailOrigin
      obtain ⟨S1b, _⟩ := headOrigin.erase.boundedBy closed Sb contextBounded
      have tailFactor := DDSynthsOrigin.factorize tailOrigin closed S1b
        (contextBounded.mono headOrigin.erase.supplyExtends)
      exact ExprsTy.cons
        (DDSynthTerminalAudit.runtimeErasureFuel (context := context) headAudit
          fuel' audit_child_bound (tailFactor.trans toTerminal) closed Sid Sb
          contextBounded)
        (DDSynthsTerminalAudit.runtimeErasureFuel (context := context) tailAudit
          fuel' audit_child_bound toTerminal closed
          (DemandTypingIdempotence.DDSynth.idempotent headOrigin.erase Sid) S1b
          (contextBounded.mono headOrigin.erase.supplyExtends))

termination_by fuel

private theorem DDCheckTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {expected : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDCheckOrigin signature raw ledger ledger'}
    (audit : DDCheckTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) :
    RuntimeTyping signature (context.applySubst terminal) expression
      (terminal.apply expected) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDCheckTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | mk synthAudit =>
      rename_i rawTarget S1 synthRaw aligned synthOrigin
      obtain ⟨S1b, synthB⟩ := synthOrigin.erase.boundedBy closed Sb
        contextBounded
      have alignFactor := aligned.factorPost S1b synthB
        (expectedBounded.mono synthOrigin.erase.supplyExtends)
      have synthTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := context) synthAudit fuel' audit_child_bound
        (DDErasure.StateFactorization.trans alignFactor toTerminal) closed Sid
        Sb contextBounded
      rcases toTerminal with ⟨post, equation, _⟩
      have certificate := aligned.runtimeCertificate.apply post
      have finalAlignment : RuntimeAlignment (terminal.apply rawTarget)
          (terminal.apply expected) := by
        simpa only [equation, Subst.seq_apply] using certificate
      exact finalAlignment.transport synthTyping

termination_by fuel

private theorem DDChecksTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedsBounded : ∀ expected ∈ expecteds, expected.BoundedBy q) :
    ExprsTy signature (context.applySubst terminal) expressions
      (expecteds.map terminal.apply) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDChecksTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | nil => exact ExprsTy.nil
  | cons headAudit tailAudit =>
      rename_i expression expected q1 S1 ledger1 expressions tailExpecteds
        headRaw tailRaw headOrigin tailOrigin
      have headB := expectedsBounded expected (by simp)
      have S1b := headOrigin.erase.boundedBy closed Sb contextBounded headB
      have tailBounds : ∀ item ∈ tailExpecteds,
          item.BoundedBy q1 := by
        intro item mem
        exact (expectedsBounded item (by simp [mem])).mono
          headOrigin.erase.supplyExtends
      have tailFactor := DDChecksOrigin.factorize tailOrigin closed S1b
        (contextBounded.mono headOrigin.erase.supplyExtends) tailBounds
      exact ExprsTy.cons
        (DDCheckTerminalAudit.runtimeErasureFuel (context := context) headAudit
          fuel' audit_child_bound (tailFactor.trans toTerminal) closed Sid Sb
          contextBounded headB)
        (DDChecksTerminalAudit.runtimeErasureFuel (context := context) tailAudit
          fuel' audit_child_bound toTerminal closed
          (DemandTypingIdempotence.DDCheck.idempotent headOrigin.erase Sid) S1b
          (contextBounded.mono headOrigin.erase.supplyExtends) tailBounds)

termination_by fuel

private theorem DDPatternTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {parameters : PatternCtx} {bindingsIn : MonoCtx} {pattern : Pattern}
    {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDPatternOrigin signature raw ledger ledger'}
    (audit : DDPatternTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    TerminalPatternResolution signature terminal
      (context.applySubst terminal) (parameters.applySubst terminal)
      (bindingsIn.applySubst terminal) pattern (dual.cap.apply terminal.cap)
      (terminal.apply dual.target) (bindingsOut.applySubst terminal) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDPatternTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | pvar =>
      rename_i name freshName
      obtain ⟨freshCap, freshTy⟩ := freshPatternVariables_of_bounded
        closed contextBounded parametersBounded bindingsBounded
      simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
        (TerminalPatternResolution.pvar (prevailing := terminal)
          (actualContext := context.applySubst terminal) freshName freshCap
          freshTy)
  | wild =>
      obtain ⟨freshCap, freshTy⟩ := freshPatternVariables_of_bounded
        closed contextBounded parametersBounded bindingsBounded
      simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
        (TerminalPatternResolution.wild (prevailing := terminal)
          (actualContext := context.applySubst terminal) freshCap freshTy)
  | pval expressionAudit =>
      rename_i _ expression target q1 ledger1 expressionRaw expressionOrigin
      obtain ⟨S1b, targetB⟩ := expressionOrigin.erase.boundedBy closed Sb
        (Context.BoundedBy.append bindingsBounded.toContext contextBounded)
      have allocation := DDErasure.StateFactorization.ofTransition
        (S := S')
        (SupplyExtends.bumpCap q1 1)
        (DDLedger.RefinesBelow.markFreshCap q1 ledger1)
      have expressionTyping := DDSynthTerminalAudit.runtimeErasureFuel
        (context := bindingsIn.toContext ++ context) expressionAudit fuel'
        audit_child_bound
        (allocation.trans toTerminal) closed Sid Sb
        (Context.BoundedBy.append bindingsBounded.toContext contextBounded)
      have expressionTyping' : RuntimeTyping signature
          ((bindingsIn.applySubst terminal).toContext ++
            context.applySubst terminal) expression (terminal.apply target) := by
        simpa only [Context.applySubst_append,
          MonoCtx.toContext_applySubst] using expressionTyping
      have ext := expressionOrigin.erase.supplyExtends
      obtain ⟨freshCap, _freshTy⟩ := freshPatternVariables_of_bounded closed
        (contextBounded.mono ext) (parametersBounded.mono ext)
        (bindingsBounded.mono ext)
      have separate : ⟨q1.nextCap⟩ ∉ target.fcv := by
        intro membership
        exact Nat.lt_irrefl q1.nextCap (targetB.caps ⟨q1.nextCap⟩ membership)
      simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
        (TerminalPatternResolution.pval (prevailing := terminal)
          (actualContext := context.applySubst terminal) freshCap separate
          expressionTyping')
  | embed =>
      rename_i _ _ _ _ name lookup
      apply TerminalPatternResolution.embed
        (rawContext := context) (rawParameters := parameters)
        (rawBindings := bindingsIn)
        (actualContext := context.applySubst terminal)
        (prevailing := terminal) lookup
      rw [PatternCtx.find?_applySubst, lookup]
      rfl
  | ptuple childrenAudit =>
      rename_i patterns duals childrenRaw childrenOrigin
      have childrenAt := DDPatternsTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) childrenAudit fuel'
        audit_child_bound
        toTerminal closed Sid Sb
        contextBounded parametersBounded bindingsBounded
      simpa only [Dual.map_cap_applySubst, Dual.map_target_applySubst,
        Cap.apply_prod, Cap.applyList_eq_map, Subst.apply_prod] using
        TerminalPatternResolution.tuple childrenAt
  | pctor childrenAudit facts =>
      rename_i name patterns entry duals q1 S1 S2 capability ledger1 ledger2
        lookup targetsAligned childrenRaw compatible capRaw capOrigin
        childrenOrigin
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      have instExt := SupplyExtends.instantiateCtorScheme q entry.scheme
      obtain ⟨S1b, dualsB, bindingsB⟩ :=
        childrenOrigin.erase.boundedBy closed (Sb.mono instExt)
          (contextBounded.mono instExt) (parametersBounded.mono instExt)
          (bindingsBounded.mono instExt)
      have childExt := childrenOrigin.erase.supplyExtends
      have expectedB : ∀ expected ∈
          (InferenceBase.instantiateCtorScheme q entry.scheme).value.1,
          expected.BoundedBy q1 := by
        intro expected mem
        exact (instB.1 expected mem).mono childExt
      have targetsFactor := targetsAligned.factorPost S1b dualsB expectedB
      have S2b := targetsAligned.erase.boundedBy S1b dualsB expectedB
      have capFactor := DDPatternCtorCapOrigin.factorize capOrigin S2b
        (fun child mem => by
          obtain ⟨item, itemMem, rfl⟩ := List.mem_map.mp mem
          exact (dualsB item itemMem).1)
      have freezing := freezeExportFactor q' S' ledger2
          (Inference.freshCapImages q entry.scheme.capBinders)
          (Inference.capabilityExportPayload [capability]
            ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
              bindingsOut.map fun binding => binding.2))
      have childrenAt := DDPatternsTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) childrenAudit fuel'
        audit_child_bound
        ((((targetsFactor.trans capFactor).trans freezing).trans toTerminal))
        closed Sid (Sb.mono instExt)
        (contextBounded.mono instExt) (parametersBounded.mono instExt)
        (bindingsBounded.mono instExt)
      have targetEquality :=
        DDErasure.StateFactorization.liftTyList_eq
          ((capFactor.trans freezing).trans toTerminal)
          targetsAligned.output_equal
      have instanceAt := closedPatternCtorInstanceAt closed lookup q terminal
      rw [← targetEquality] at instanceAt
      exact TerminalPatternResolution.ctor
        (result := ⟨capability.apply terminal.cap,
          terminal.apply
            (InferenceBase.instantiateCtorScheme q entry.scheme).value.2⟩)
        lookup childrenAt facts.compatible
        (by simpa only [Dual.map_target_applySubst] using instanceAt)
  | pand leftAudit rightAudit =>
      rename_i left leftBindings q1 S1 ledger1 right rightDual S2 leftRaw
        rightRaw leftOrigin rightOrigin aligned
      obtain ⟨S1b, leftDualB, leftBindingsB⟩ :=
        leftOrigin.erase.boundedBy closed Sb contextBounded parametersBounded
          bindingsBounded
      have ext1 := leftOrigin.erase.supplyExtends
      obtain ⟨S2b, rightDualB, _⟩ := rightOrigin.erase.boundedBy closed S1b
        (contextBounded.mono ext1) (parametersBounded.mono ext1) leftBindingsB
      have ext2 := rightOrigin.erase.supplyExtends
      have alignFactor := aligned.factorPost S2b
        (leftDualB.mono ext2) rightDualB
      have rightFactor := DDPatternOrigin.factorize rightOrigin closed S1b
        (contextBounded.mono ext1) (parametersBounded.mono ext1) leftBindingsB
      have leftAt := DDPatternTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) leftAudit fuel'
        audit_child_bound
        ((rightFactor.trans alignFactor).trans toTerminal) closed Sid Sb
        contextBounded parametersBounded bindingsBounded
      have rightAt := DDPatternTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) rightAudit fuel'
        audit_child_bound
        (alignFactor.trans toTerminal) closed
        (DemandTypingIdempotence.DDPattern.idempotent leftOrigin.erase Sid)
        S1b (contextBounded.mono ext1)
        (parametersBounded.mono ext1) leftBindingsB
      have dualEquality := toTerminal.liftDual_eq aligned.output_equal
      have capEquality := congrArg Dual.cap dualEquality
      have targetEquality := congrArg Dual.target dualEquality
      simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality
      rw [← capEquality, ← targetEquality] at rightAt
      exact TerminalPatternResolution.and leftAt rightAt
  | por leftAudit rightAudit =>
      rename_i left q1 S1 ledger1 right rightDual rightBindings S2 S3 leftRaw
        rightRaw leftOrigin dualsAligned rightOrigin bindingsAligned
      obtain ⟨S1b, leftDualB, leftBindingsB⟩ :=
        leftOrigin.erase.boundedBy closed Sb contextBounded parametersBounded
          bindingsBounded
      have ext1 := leftOrigin.erase.supplyExtends
      obtain ⟨S2b, rightDualB, rightBindingsB⟩ :=
        rightOrigin.erase.boundedBy closed S1b (contextBounded.mono ext1)
          (parametersBounded.mono ext1) (bindingsBounded.mono ext1)
      have ext2 := rightOrigin.erase.supplyExtends
      have dualFactor := dualsAligned.factorPost S2b
        (leftDualB.mono ext2) rightDualB
      have S3b := dualsAligned.erase.boundedBy S2b
        (leftDualB.mono ext2) rightDualB
      have bindingFactor := bindingsAligned.factorPost S3b
        (fun entry mem => (leftBindingsB.mono ext2) entry mem)
        (fun entry mem => rightBindingsB entry mem)
      have rightFactor := DDPatternOrigin.factorize rightOrigin closed S1b
        (contextBounded.mono ext1) (parametersBounded.mono ext1)
        (bindingsBounded.mono ext1)
      have leftAt := DDPatternTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) leftAudit fuel'
        audit_child_bound
        (((rightFactor.trans dualFactor).trans bindingFactor).trans toTerminal)
        closed Sid Sb contextBounded parametersBounded bindingsBounded
      have rightAt := DDPatternTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) rightAudit fuel'
        audit_child_bound
        ((dualFactor.trans bindingFactor).trans toTerminal) closed
        (DemandTypingIdempotence.DDPattern.idempotent leftOrigin.erase Sid)
        S1b (contextBounded.mono ext1)
        (parametersBounded.mono ext1) (bindingsBounded.mono ext1)
      have dualEquality :=
        (bindingFactor.trans toTerminal).liftDual_eq dualsAligned.output_equal
      have bindingsEquality := toTerminal.liftBindings_eq
        bindingsAligned.output_equal
      have capEquality := congrArg Dual.cap dualEquality
      have targetEquality := congrArg Dual.target dualEquality
      simp only [Dual.applySubst, Dual.apply] at capEquality targetEquality
      rw [← capEquality, ← targetEquality, ← bindingsEquality] at rightAt
      exact TerminalPatternResolution.or leftAt rightAt
  | papp childrenAudit =>
      rename_i scheme patterns duals S1 name lookup childrenRaw aligned
        childrenOrigin
      have instExt := SupplyExtends.instantiateDualScheme q scheme
      have instB := instantiateDualScheme_boundedBy (q := q)
        ((closed.patternFuns lookup).boundedBy)
      obtain ⟨S1b, dualsB, _⟩ := childrenOrigin.erase.boundedBy closed
        (Sb.mono instExt) (contextBounded.mono instExt)
        (parametersBounded.mono instExt) (bindingsBounded.mono instExt)
      have childExt := childrenOrigin.erase.supplyExtends
      have expectedB : ∀ item ∈
          (InferenceBase.instantiateDualScheme q scheme).value.1,
          item.BoundedBy q' := by
        intro item mem
        exact ⟨(instB.1 item mem).1.mono childExt,
          (instB.1 item mem).2.mono childExt⟩
      have alignFactor := aligned.factorPost S1b dualsB expectedB
      have childrenFactor := DDPatternsOrigin.factorize childrenOrigin closed
        (Sb.mono instExt) (contextBounded.mono instExt)
        (parametersBounded.mono instExt) (bindingsBounded.mono instExt)
      have childrenAt := DDPatternsTerminalAudit.runtimeErasureFuel
        (context := context) (parameters := parameters) childrenAudit fuel'
        audit_child_bound
        (alignFactor.trans toTerminal) closed Sid (Sb.mono instExt)
        (contextBounded.mono instExt) (parametersBounded.mono instExt)
        (bindingsBounded.mono instExt)
      have instanceAt := closedDualSchemeInstanceAlignedAt closed lookup Sb
        ((childrenFactor.trans alignFactor).trans toTerminal)
        (toTerminal.liftDualList_eq aligned.output_equal)
      exact TerminalPatternResolution.app lookup childrenAt instanceAt

termination_by fuel

private theorem DDPatternsTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {parameters : PatternCtx} {bindingsIn : MonoCtx} {patterns : List Pattern}
    {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDPatternsOrigin signature raw ledger ledger'}
    (audit : DDPatternsTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    TerminalPatternResolutions signature terminal
      (context.applySubst terminal) (parameters.applySubst terminal)
      (bindingsIn.applySubst terminal) patterns
      (duals.map (Dual.applySubst terminal))
      (bindingsOut.applySubst terminal) := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDPatternsTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | nil => exact TerminalPatternResolutions.nil
  | cons headAudit tailAudit =>
      rename_i pattern dual bindings1 q1 S1 ledger1 patterns duals headRaw
        tailRaw headOrigin tailOrigin
      obtain ⟨S1b, _dualB, bindings1B⟩ := headOrigin.erase.boundedBy closed
        Sb contextBounded parametersBounded bindingsBounded
      have ext := headOrigin.erase.supplyExtends
      have tailFactor := DDPatternsOrigin.factorize tailOrigin closed S1b
        (contextBounded.mono ext) (parametersBounded.mono ext) bindings1B
      simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
        TerminalPatternResolutions.cons
          (DDPatternTerminalAudit.runtimeErasureFuel (context := context)
            (parameters := parameters) headAudit fuel' audit_child_bound
            (tailFactor.trans toTerminal) closed Sid Sb
            contextBounded parametersBounded bindingsBounded)
          (DDPatternsTerminalAudit.runtimeErasureFuel (context := context)
            (parameters := parameters) tailAudit fuel' audit_child_bound
            toTerminal closed
            (DemandTypingIdempotence.DDPattern.idempotent headOrigin.erase Sid)
            S1b (contextBounded.mono ext)
            (parametersBounded.mono ext) bindings1B)

termination_by fuel

private theorem DDArmsTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {ppBindings : MonoCtx} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (bindingsBounded : MonoCtx.BoundedBy q ppBindings)
    (clauseBounded : clauseTarget.BoundedBy q)
    (bodyBounded : bodyTarget.BoundedBy q) :
    ArmsTy signature (context.applySubst terminal) (terminal.apply clauseTarget)
      (ppBindings.applySubst terminal) (terminal.apply bodyTarget) arms := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDArmsTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | nil => exact ArmsTy.nil
  | cons bodyAudit tailAudit =>
      rename_i q1 S1 armBindings body q2 S2 ledger1 ledger2 tailArms
        dataPattern disjoint patternRaw bodyRaw bodyOrigin tailRaw patternOrigin
        tailOrigin
      obtain ⟨S1b, armBindingsB⟩ := patternOrigin.erase.boundedBy closed
        Sb clauseBounded
      have ext1 := patternOrigin.erase.supplyExtends
      have bodyContextB := Context.BoundedBy.append
        (Context.BoundedBy.append armBindingsB.toContext
          ((bindingsBounded.mono ext1).toContext))
        (contextBounded.mono ext1)
      have S2b := bodyOrigin.erase.boundedBy closed S1b bodyContextB
        (bodyBounded.mono ext1)
      have ext2 := bodyOrigin.erase.supplyExtends
      have tailFactor := DDArmsOrigin.factorize tailOrigin closed S2b
        (contextBounded.mono (ext1.trans ext2))
        (bindingsBounded.mono (ext1.trans ext2))
        (clauseBounded.mono (ext1.trans ext2))
        (bodyBounded.mono (ext1.trans ext2))
      have bodyFactor := DDCheckOrigin.factorize bodyOrigin closed S1b
        bodyContextB (bodyBounded.mono ext1)
      have patternFactor := DDDPatOrigin.factorize patternOrigin closed Sb
        clauseBounded
      rcases (bodyFactor.trans tailFactor).trans toTerminal
        with ⟨patternPost, patternEquation, patternAdmissible⟩
      have patternAt :=
        (DDDPatOrigin.runtimeErasureUnder patternOrigin closed Sb clauseBounded)
          patternEquation patternAdmissible
      have bodyAt := DDCheckTerminalAudit.runtimeErasureFuel
        (context := armBindings.toContext ++ ppBindings.toContext ++ context)
        bodyAudit fuel' audit_child_bound (tailFactor.trans toTerminal) closed
        (DemandTypingIdempotence.DDDPat.idempotent patternOrigin.erase Sid) S1b
        bodyContextB (bodyBounded.mono ext1)
      have bodyAt' : RuntimeTyping signature
          ((armBindings.applySubst terminal).toContext ++
            (ppBindings.applySubst terminal).toContext ++
            context.applySubst terminal) body (terminal.apply bodyTarget) := by
        simpa only [Context.applySubst_append,
          MonoCtx.toContext_applySubst] using bodyAt
      have tailAt := DDArmsTerminalAudit.runtimeErasureFuel
        (context := context) tailAudit fuel' audit_child_bound toTerminal closed
        (DemandTypingIdempotence.DDCheck.idempotent bodyOrigin.erase
          (DemandTypingIdempotence.DDDPat.idempotent patternOrigin.erase Sid))
        S2b (contextBounded.mono (ext1.trans ext2))
        (bindingsBounded.mono (ext1.trans ext2))
        (clauseBounded.mono (ext1.trans ext2))
        (bodyBounded.mono (ext1.trans ext2))
      exact ArmsTy.cons (ArmTy.mk patternAt bodyAt') tailAt

termination_by fuel

private theorem DDClauseTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {clause : Clause} {sharedTarget : Ty} {holes : List Dual}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    (audit : DDClauseTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q)
    {capability : Cap} {evidence : Shape.Evidence}
    (capsAtTerminal : PPatCapsAt signature true clause.pp
      ((holes.map (Dual.applySubst terminal)).map Dual.cap) capability)
    (evidenceAtTerminal : clauseEvidence signature.toMatcherSig clause.pp
      ((holes.map (Dual.applySubst terminal)).map Dual.cap) = some evidence) :
    ClauseTy signature terminal (context.applySubst terminal) clause capability
      (terminal.apply sharedTarget) evidence := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDClauseTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | mk nextAudit armsAudit =>
      rename_i q1 S1 nextMatchers q2 S2 ledger1 ledger2 ppBindings arms pp next
        decomposed nextRaw nextOrigin ppRaw armsRaw ppOrigin armsOrigin
      obtain ⟨S1b, holesB, ppBindingsB⟩ := ppOrigin.erase.boundedBy closed
        Sb sharedBounded
      have ext1 := ppOrigin.erase.supplyExtends
      have nextExpectedB : ∀ expected ∈
          (holes.map fun hole => Ty.slot hole.cap hole.target),
          expected.BoundedBy q1 := by
        intro expected mem
        obtain ⟨hole, holeMem, rfl⟩ := List.mem_map.mp mem
        exact Ty.BoundedBy.slotOf (holesB hole holeMem).1
          (holesB hole holeMem).2
      have S2b := nextOrigin.erase.boundedBy closed S1b
        (contextBounded.mono ext1) nextExpectedB
      have ext2 := nextOrigin.erase.supplyExtends
      have armBodyB := listT_boundedBy (prodTy_boundedBy (fun target mem => by
        obtain ⟨hole, holeMem, rfl⟩ := List.mem_map.mp mem
        exact (holesB hole holeMem).2.mono ext2))
      have armsFactor := DDArmsOrigin.factorize armsOrigin closed S2b
        (contextBounded.mono (ext1.trans ext2)) (ppBindingsB.mono ext2)
        (sharedBounded.mono (ext1.trans ext2)) armBodyB
      have nextFactor := DDChecksOrigin.factorize nextOrigin closed S1b
        (contextBounded.mono ext1) nextExpectedB
      have ppFactor := DDPPatOrigin.factorize ppOrigin closed Sb sharedBounded
      rcases (nextFactor.trans armsFactor).trans toTerminal with
        ⟨ppPost, ppEquation, ppAdmissible⟩
      have ppAt := (DDPPatOrigin.runtimeErasureUnder ppOrigin closed Sb
        sharedBounded) ppEquation ppAdmissible
      have nextAt := DDChecksTerminalAudit.runtimeErasureFuel
        (context := context) nextAudit fuel' audit_child_bound
        (armsFactor.trans toTerminal) closed
        (DemandTypingIdempotence.DDPPat.idempotent ppOrigin.erase Sid) S1b
        (contextBounded.mono ext1) nextExpectedB
      have armsAt := DDArmsTerminalAudit.runtimeErasureFuel
        (context := context) armsAudit fuel' audit_child_bound toTerminal closed
        (DemandTypingIdempotence.DDChecks.idempotent nextOrigin.erase
          (DemandTypingIdempotence.DDPPat.idempotent ppOrigin.erase Sid))
        S2b (contextBounded.mono (ext1.trans ext2)) (ppBindingsB.mono ext2)
        (sharedBounded.mono (ext1.trans ext2)) armBodyB
      exact ClauseTy.mk (clauseEvidence_coreOrder evidenceAtTerminal)
        (.ofTerminal ppAt) capsAtTerminal (by simpa using decomposed)
        (by simpa [Subst.apply_slot, List.map_map, Function.comp_def,
          Dual.applySubst, Dual.apply] using nextAt)
        (by simpa only [Subst.apply_listT, Subst.apply_prodTy,
          Dual.map_target_applySubst] using armsAt)
        evidenceAtTerminal

termination_by fuel

private theorem DDClausesTerminalAudit.runtimeErasureFuel
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDClauses signature q S context clauses sharedTarget
      holeLists q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    (fuel : Nat) (fuelEnough : audit.depth ≤ fuel)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q)
    {capability : Cap} {evidences : List Shape.Evidence}
    (capsAtTerminal : Inference.ClauseCapsList signature clauses
      (terminalHoleCaps terminal holeLists) capability)
    (evidenceAtTerminal : Inference.ClauseEvidenceList signature.toMatcherSig
      clauses (terminalHoleCaps terminal holeLists) evidences) :
    ClausesTy signature terminal (context.applySubst terminal) clauses
      capability (terminal.apply sharedTarget) evidences := by
  have fuelPositive : 0 < fuel := by
    have depthPositive : 0 < audit.depth := by
      cases audit <;> simp [DDClausesTerminalAudit.depth]
    omega
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fuelPositive)
  cases audit with
  | nil =>
      cases capsAtTerminal
      cases evidenceAtTerminal
      exact ClausesTy.nil
  | cons headAudit tailAudit =>
      rename_i clause holes q1 S1 ledger1 tailClauses tailHoles headRaw
        tailRaw headOrigin tailOrigin
      cases capsAtTerminal with
      | cons headCaps tailCaps =>
        cases evidenceAtTerminal with
        | cons headEvidence tailEvidence =>
          obtain ⟨S1b, _holesB⟩ := headOrigin.erase.boundedBy closed Sb
            contextBounded sharedBounded
          have ext := headOrigin.erase.supplyExtends
          have tailFactor := DDClausesOrigin.factorize tailOrigin closed S1b
            (contextBounded.mono ext) (sharedBounded.mono ext)
          exact ClausesTy.cons
            (DDClauseTerminalAudit.runtimeErasureFuel (context := context)
              headAudit fuel' audit_child_bound (tailFactor.trans toTerminal)
              closed Sid Sb
              contextBounded sharedBounded headCaps headEvidence)
            (DDClausesTerminalAudit.runtimeErasureFuel (context := context)
              tailAudit fuel' audit_child_bound toTerminal closed
              (DemandTypingIdempotence.DDClause.idempotent headOrigin.erase Sid)
              S1b (contextBounded.mono ext) (sharedBounded.mono ext)
              tailCaps tailEvidence)

termination_by fuel
decreasing_by
  all_goals omega

end

/-! ## Public erasure interface

The implementation above consumes an explicit structural fuel.  These thin
wrappers instantiate it with the audit depth, keeping fuel and its bookkeeping
out of the public API.
-/

theorem DDSynthTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDSynthOrigin signature raw ledger ledger'}
    (audit : DDSynthTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeTyping signature (context.applySubst terminal) expression
      (terminal.apply target) :=
  DDSynthTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded

theorem DDSynthsTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDSynthsOrigin signature raw ledger ledger'}
    (audit : DDSynthsTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    ExprsTy signature (context.applySubst terminal) expressions
      (targets.map terminal.apply) :=
  DDSynthsTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded

theorem DDCheckTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {expected : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDCheckOrigin signature raw ledger ledger'}
    (audit : DDCheckTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) :
    RuntimeTyping signature (context.applySubst terminal) expression
      (terminal.apply expected) :=
  DDCheckTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded expectedBounded

theorem DDChecksTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDChecksOrigin signature raw ledger ledger'}
    (audit : DDChecksTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedsBounded : ∀ expected ∈ expecteds, expected.BoundedBy q) :
    ExprsTy signature (context.applySubst terminal) expressions
      (expecteds.map terminal.apply) :=
  DDChecksTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded expectedsBounded

theorem DDPatternTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {parameters : PatternCtx} {bindingsIn : MonoCtx} {pattern : Pattern}
    {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDPatternOrigin signature raw ledger ledger'}
    (audit : DDPatternTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    TerminalPatternResolution signature terminal
      (context.applySubst terminal) (parameters.applySubst terminal)
      (bindingsIn.applySubst terminal) pattern (dual.cap.apply terminal.cap)
      (terminal.apply dual.target) (bindingsOut.applySubst terminal) :=
  DDPatternTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded parametersBounded bindingsBounded

theorem DDPatternsTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {parameters : PatternCtx} {bindingsIn : MonoCtx} {patterns : List Pattern}
    {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDPatternsOrigin signature raw ledger ledger'}
    (audit : DDPatternsTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (parametersBounded : PatternCtx.BoundedBy q parameters)
    (bindingsBounded : MonoCtx.BoundedBy q bindingsIn) :
    TerminalPatternResolutions signature terminal
      (context.applySubst terminal) (parameters.applySubst terminal)
      (bindingsIn.applySubst terminal) patterns
      (duals.map (Dual.applySubst terminal))
      (bindingsOut.applySubst terminal) :=
  DDPatternsTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded parametersBounded bindingsBounded

theorem DDArmsTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {ppBindings : MonoCtx} {arms : List Arm} {clauseTarget bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget
      bodyTarget q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDArmsOrigin signature raw ledger ledger'}
    (audit : DDArmsTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (bindingsBounded : MonoCtx.BoundedBy q ppBindings)
    (clauseBounded : clauseTarget.BoundedBy q)
    (bodyBounded : bodyTarget.BoundedBy q) :
    ArmsTy signature (context.applySubst terminal) (terminal.apply clauseTarget)
      (ppBindings.applySubst terminal) (terminal.apply bodyTarget) arms :=
  DDArmsTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded bindingsBounded clauseBounded bodyBounded

theorem DDClauseTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {clause : Clause} {sharedTarget : Ty} {holes : List Dual}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDClauseOrigin signature raw ledger ledger'}
    (audit : DDClauseTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q)
    {capability : Cap} {evidence : Shape.Evidence}
    (capsAtTerminal : PPatCapsAt signature true clause.pp
      ((holes.map (Dual.applySubst terminal)).map Dual.cap) capability)
    (evidenceAtTerminal : clauseEvidence signature.toMatcherSig clause.pp
      ((holes.map (Dual.applySubst terminal)).map Dual.cap) = some evidence) :
    ClauseTy signature terminal (context.applySubst terminal) clause capability
      (terminal.apply sharedTarget) evidence :=
  DDClauseTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded sharedBounded capsAtTerminal evidenceAtTerminal

theorem DDClausesTerminalAudit.runtimeErasure
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {raw : DDClauses signature q S context clauses sharedTarget
      holeLists q' S'} {ledger ledger' terminalLedger : CapabilityOriginLedger}
    {origin : DDClausesOrigin signature raw ledger ledger'}
    (audit : DDClausesTerminalAudit terminal signature origin)
    {terminalSupply : InferenceBase.FreshSupply}
    (toTerminal : DDErasure.StateFactorization q' S' ledger'
      terminalSupply terminal terminalLedger)
    (closed : signature.SchemesClosed) (Sid : S.Idempotent)
    (Sb : S.BoundedBy q) (contextBounded : Context.BoundedBy q context)
    (sharedBounded : sharedTarget.BoundedBy q)
    {capability : Cap} {evidences : List Shape.Evidence}
    (capsAtTerminal : Inference.ClauseCapsList signature clauses
      (terminalHoleCaps terminal holeLists) capability)
    (evidenceAtTerminal : Inference.ClauseEvidenceList signature.toMatcherSig
      clauses (terminalHoleCaps terminal holeLists) evidences) :
    ClausesTy signature terminal (context.applySubst terminal) clauses
      capability (terminal.apply sharedTarget) evidences :=
  DDClausesTerminalAudit.runtimeErasureFuel audit audit.depth (Nat.le_refl _)
    toTerminal
    closed Sid Sb contextBounded sharedBounded capsAtTerminal evidenceAtTerminal

end TypePM
