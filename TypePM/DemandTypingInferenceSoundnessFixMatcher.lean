import TypePM.DemandTypingInferenceSoundness

/-!
# Recursive matcher inference soundness

This module reconstructs the demand-directed `fixMatcher` rule from the
state-threaded recursive matcher placeholder used by executable inference.
The three mutually recursive skeleton fresheners are related first to their
pure supply twins, including the exact capability-origin ledger cut.
-/

namespace TypePM
namespace Inference

private theorem setOrigins_append (ledger : CapabilityOriginLedger)
    (left right : List CapVar) (origin : CapabilityOrigin) :
    ledger.setOrigins (left ++ right) origin =
      (ledger.setOrigins right origin).setOrigins left origin := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, CapabilityOriginLedger.setOrigins]
      rw [ih]

private def markCapAlloc (ledger : CapabilityOriginLedger) (start : Nat) :
    Nat → CapabilityOriginLedger
  | 0 => ledger
  | count + 1 =>
      (markCapAlloc ledger start count).setOrigin ⟨start + count⟩
        .structuralFlexible

private theorem markCapAlloc_add (ledger : CapabilityOriginLedger)
    (start first second : Nat) :
    markCapAlloc (markCapAlloc ledger start first) (start + first) second =
      markCapAlloc ledger start (first + second) := by
  induction second with
  | zero => simp [markCapAlloc]
  | succ second ih =>
      simp only [markCapAlloc]
      rw [ih]
      congr 2
      simp [Nat.add_assoc]

private theorem markCapRange_eq_markCapAlloc
    (ledger : CapabilityOriginLedger) (start nextTy count : Nat) :
    DDLedger.markCapRange ledger ⟨start, nextTy⟩
        ⟨start + count, nextTy⟩ =
      markCapAlloc ledger start count := by
  unfold DDLedger.markCapRange
  have difference : start + count - start = count := by omega
  rw [difference]
  change ledger.setOrigins
      ((List.range count).map fun offset => ⟨start + offset⟩).reverse
        .structuralFlexible = markCapAlloc ledger start count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.reverse_append]
      simp only [List.map_singleton, List.reverse_singleton]
      rw [setOrigins_append]
      simp only [CapabilityOriginLedger.setOrigins]
      rw [ih (by omega)]
      rfl

/-- Exact state effect of a solve-free sequence of fresh capability
allocations. -/
private def FreshCapExtension (initial final : InferState) : Prop :=
  ∃ count : Nat,
    final.supply =
      { initial.supply with nextCap := initial.supply.nextCap + count } ∧
    final.prevailing = initial.prevailing ∧
    final.capabilityOrigins =
      markCapAlloc initial.capabilityOrigins initial.supply.nextCap count

private theorem FreshCapExtension.refl (state : InferState) :
    FreshCapExtension state state := by
  exact ⟨0, by simp, rfl, rfl⟩

private theorem FreshCapExtension.freshCap
    (state : InferState) (origin : ConstraintOrigin) :
    FreshCapExtension state (state.freshCap origin).2 := by
  refine ⟨1, ?_, rfl, ?_⟩
  · simp [InferState.freshCap, InferenceBase.freshCapMeta,
      InferState.recordEvent]
  · rfl

private theorem FreshCapExtension.trans {first middle last : InferState}
    (front : FreshCapExtension first middle)
    (back : FreshCapExtension middle last) :
    FreshCapExtension first last := by
  rcases front with
    ⟨frontCount, frontSupply, frontPrevailing, frontLedger⟩
  rcases back with ⟨backCount, backSupply, backPrevailing, backLedger⟩
  refine ⟨frontCount + backCount, ?_, ?_, ?_⟩
  · rw [backSupply, frontSupply]
    simp [Nat.add_assoc]
  · exact backPrevailing.trans frontPrevailing
  · rw [backLedger, frontSupply, frontLedger]
    exact markCapAlloc_add first.capabilityOrigins first.supply.nextCap
      frontCount backCount

private theorem FreshCapExtension.toRange {initial final : InferState}
    (extension : FreshCapExtension initial final) :
    final.capabilityOrigins =
      DDLedger.markCapRange initial.capabilityOrigins initial.supply
        final.supply := by
  rcases extension with ⟨count, supply, _, ledger⟩
  rw [supply, ledger]
  symm
  exact markCapRange_eq_markCapAlloc initial.capabilityOrigins
    initial.supply.nextCap initial.supply.nextTy count

private theorem FreshCapExtension.prevailing {initial final : InferState}
    (extension : FreshCapExtension initial final) :
    final.prevailing = initial.prevailing := by
  rcases extension with ⟨_, _, prevailing, _⟩
  exact prevailing

private def FreshSkeletonRun (observable : Shape.Observability)
    (evidence : Shape.Evidence) (initial : InferState) (capability : Cap)
    (final : InferState) : Prop :=
  freshenSkeletonSupply observable evidence initial.supply =
      some (capability, final.supply) ∧
    FreshCapExtension initial final

private def FreshSkeletonsRun (observable : Shape.Observability)
    (evidence : List Shape.Evidence) (initial : InferState)
    (capabilities : List Cap) (final : InferState) : Prop :=
  freshenSkeletonListSupply observable evidence initial.supply =
      some (capabilities, final.supply) ∧
    FreshCapExtension initial final

private def FreshSkeletonMaskedRun (observable : Shape.Observability)
    (mask : List Bool) (evidence : List Shape.Evidence)
    (initial : InferState) (capabilities : List Cap)
    (final : InferState) : Prop :=
  freshenSkeletonMaskedSupply observable mask evidence initial.supply =
      some (capabilities, final.supply) ∧
    FreshCapExtension initial final

private theorem DDSynthOrigin.transportRawLocal
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw raw' : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger') :
    DDSynthOrigin signature raw' ledger ledger' := by
  have equality : raw = raw' := Subsingleton.elim _ _
  subst raw'
  exact origin

private theorem DDSynthOrigin.transportInitial
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S T : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' terminal : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger terminal)
    (substEq : S = T) (ledgerEq : ledger = ledger') :
    ∃ raw' : DDSynth signature q T context expression target q' S',
      DDSynthOrigin signature raw' ledger' terminal := by
  subst T
  subst ledger'
  exact ⟨raw, origin⟩

/- The executable skeleton freshener and its three pure supply twins agree
on values and exact terminal state. -/
mutual

theorem freshenSkeleton_ddRun
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (evidence : Shape.Evidence) (initial : InferState)
      (capability : Cap) (final : InferState),
      freshenSkeleton observable origin evidence initial =
          some (capability, final) →
        FreshSkeletonRun observable evidence initial capability final
  | .unseen, initial, capability, final, success => by
      simp only [freshenSkeleton, Option.some.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, FreshCapExtension.freshCap initial origin⟩
  | .known leaf, initial, capability, final, success => by
      simp only [freshenSkeleton, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, FreshCapExtension.refl initial⟩
  | .con name children, initial, capability, final, success => by
      cases maskEq : observable name with
      | none => simp [freshenSkeleton, maskEq] at success
      | some mask =>
          cases childrenEq : freshenSkeletonMasked observable origin mask
              children initial with
          | none => simp [freshenSkeleton, maskEq, childrenEq] at success
          | some pair =>
              rcases pair with ⟨capabilities, childrenFinal⟩
              simp [freshenSkeleton, maskEq, childrenEq] at success
              rcases success with ⟨rfl, rfl⟩
              rcases freshenSkeletonMasked_ddRun observable origin mask
                  children initial capabilities childrenFinal childrenEq with
                ⟨pure, extension⟩
              exact ⟨by simp [freshenSkeletonSupply, maskEq, pure], extension⟩
  | .prod components, initial, capability, final, success => by
      cases childrenEq : freshenSkeletonList observable origin components
          initial with
      | none => simp [freshenSkeleton, childrenEq] at success
      | some pair =>
          rcases pair with ⟨capabilities, childrenFinal⟩
          simp [freshenSkeleton, childrenEq] at success
          rcases success with ⟨rfl, rfl⟩
          rcases freshenSkeletonList_ddRun observable origin components
              initial capabilities childrenFinal childrenEq with
            ⟨pure, extension⟩
          exact ⟨by simp [freshenSkeletonSupply, pure], extension⟩

theorem freshenSkeletonList_ddRun
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (evidence : List Shape.Evidence) (initial : InferState)
      (capabilities : List Cap) (final : InferState),
      freshenSkeletonList observable origin evidence initial =
          some (capabilities, final) →
        FreshSkeletonsRun observable evidence initial capabilities final
  | [], initial, capabilities, final, success => by
      simp only [freshenSkeletonList, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, FreshCapExtension.refl initial⟩
  | evidence :: rest, initial, capabilities, final, success => by
      cases headEq : freshenSkeleton observable origin evidence initial with
      | none => simp [freshenSkeletonList, headEq] at success
      | some headPair =>
          rcases headPair with ⟨head, middle⟩
          cases tailEq : freshenSkeletonList observable origin rest middle with
          | none => simp [freshenSkeletonList, headEq, tailEq] at success
          | some tailPair =>
              rcases tailPair with ⟨tail, tailFinal⟩
              simp [freshenSkeletonList, headEq, tailEq] at success
              rcases success with ⟨rfl, rfl⟩
              rcases freshenSkeleton_ddRun observable origin evidence initial
                  head middle headEq with ⟨headPure, headExtension⟩
              rcases freshenSkeletonList_ddRun observable origin rest middle
                  tail tailFinal tailEq with ⟨tailPure, tailExtension⟩
              exact ⟨by simp [freshenSkeletonListSupply, headPure, tailPure],
                headExtension.trans tailExtension⟩

theorem freshenSkeletonMasked_ddRun
    (observable : Shape.Observability) (origin : ConstraintOrigin) :
    ∀ (mask : List Bool) (evidence : List Shape.Evidence)
      (initial : InferState) (capabilities : List Cap) (final : InferState),
      freshenSkeletonMasked observable origin mask evidence initial =
          some (capabilities, final) →
        FreshSkeletonMaskedRun observable mask evidence initial capabilities
          final
  | [], [], initial, capabilities, final, success => by
      simp only [freshenSkeletonMasked, Option.some.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, FreshCapExtension.refl initial⟩
  | [], _ :: _, _, _, _, success => by
      simp [freshenSkeletonMasked] at success
  | _ :: _, [], _, _, _, success => by
      simp [freshenSkeletonMasked] at success
  | isObservable :: mask, evidence :: rest, initial, capabilities, final,
      success => by
      cases isObservable with
      | false =>
          cases tailEq : freshenSkeletonMasked observable origin mask rest
              initial with
          | none => simp [freshenSkeletonMasked, tailEq] at success
          | some tailPair =>
              rcases tailPair with ⟨tail, tailFinal⟩
              simp [freshenSkeletonMasked, tailEq] at success
              rcases success with ⟨rfl, rfl⟩
              rcases freshenSkeletonMasked_ddRun observable origin mask rest
                  initial tail tailFinal tailEq with ⟨tailPure, extension⟩
              exact ⟨by simp [freshenSkeletonMaskedSupply, tailPure],
                extension⟩
      | true =>
          cases headEq : freshenSkeleton observable origin evidence initial with
          | none => simp [freshenSkeletonMasked, headEq] at success
          | some headPair =>
              rcases headPair with ⟨head, middle⟩
              cases tailEq : freshenSkeletonMasked observable origin mask rest
                  middle with
              | none =>
                  simp [freshenSkeletonMasked, headEq, tailEq] at success
              | some tailPair =>
                  rcases tailPair with ⟨tail, tailFinal⟩
                  simp [freshenSkeletonMasked, headEq, tailEq] at success
                  rcases success with ⟨rfl, rfl⟩
                  rcases freshenSkeleton_ddRun observable origin evidence
                      initial head middle headEq with
                    ⟨headPure, headExtension⟩
                  rcases freshenSkeletonMasked_ddRun observable origin mask rest
                      middle tail tailFinal tailEq with
                    ⟨tailPure, tailExtension⟩
                  exact
                    ⟨by simp [freshenSkeletonMaskedSupply, headPure, tailPure],
                      headExtension.trans tailExtension⟩

end

/-- Public exact-state surface of skeleton freshening.  Downstream
soundness slices need only agreement with the pure supply twin and the two
state components consumed by DD origin certificates; the internal extension
representation remains private to this module. -/
theorem freshenSkeleton_supplyExact
    {observable : Shape.Observability} {origin : ConstraintOrigin}
    {evidence : Shape.Evidence} {initial final : InferState}
    {capability : Cap}
    (success : freshenSkeleton observable origin evidence initial =
      some (capability, final)) :
    freshenSkeletonSupply observable evidence initial.supply =
        some (capability, final.supply) ∧
      final.prevailing = initial.prevailing ∧
      final.capabilityOrigins =
        DDLedger.markCapRange initial.capabilityOrigins initial.supply
          final.supply := by
  rcases freshenSkeleton_ddRun observable origin evidence initial capability
      final success with ⟨pure, extension⟩
  exact ⟨pure, extension.prevailing, extension.toRange⟩

/-- Internal exact extension for the stateful shared-result assignment
allocator used by pattern constructors. -/
private theorem freshPatternCtorAssignments_extension
    (origin : ConstraintOrigin) :
    ∀ (variables : List TypePM.TyVar) (initial : InferState),
      let allocated := freshPatternCtorAssignments origin variables initial
      allocated.1 =
          (patternCtorAssignmentsSupply variables initial.supply).1 ∧
        allocated.2.supply =
          (patternCtorAssignmentsSupply variables initial.supply).2 ∧
        FreshCapExtension initial allocated.2
  | [], initial => by
      exact ⟨rfl, rfl, FreshCapExtension.refl initial⟩
  | varId :: variables, initial => by
      let middle := (initial.freshCap origin).2
      rcases freshPatternCtorAssignments_extension origin variables middle with
        ⟨assignments, supply, extension⟩
      have middleSupply : middle.supply =
          { initial.supply with
            nextCap := initial.supply.nextCap + 1 } := by
        simp [middle, InferState.freshCap, InferenceBase.freshCapMeta,
          InferState.recordEvent]
      simp only [freshPatternCtorAssignments,
        patternCtorAssignmentsSupply]
      rw [assignments, supply, middleSupply]
      exact ⟨rfl, rfl,
        (FreshCapExtension.freshCap initial origin).trans extension⟩

/-- Public exact-state surface of the pattern-constructor shared-result
assignment allocator. -/
theorem freshPatternCtorAssignments_supplyExact
    (origin : ConstraintOrigin) (variables : List TypePM.TyVar)
    (initial : InferState) :
    let allocated := freshPatternCtorAssignments origin variables initial
    allocated.1 =
        (patternCtorAssignmentsSupply variables initial.supply).1 ∧
      allocated.2.supply =
        (patternCtorAssignmentsSupply variables initial.supply).2 ∧
      allocated.2.prevailing = initial.prevailing ∧
      allocated.2.capabilityOrigins =
        DDLedger.markCapRange initial.capabilityOrigins initial.supply
          allocated.2.supply := by
  rcases freshPatternCtorAssignments_extension origin variables initial with
    ⟨assignments, supply, extension⟩
  exact ⟨assignments, supply, extension.prevailing, extension.toRange⟩

private def recursiveMatcherTemplateSupply (signature : FrozenSig)
    (clauses : List Clause) (q : InferenceBase.FreshSupply) :
    Option (Cap × InferenceBase.FreshSupply) := do
  let evidence <- matcherSkeletonEvidence signature.toMatcherSig clauses
  match evidence with
  | .unseen => pure (.any, q)
  | evidence => freshenSkeletonSupply signature.observability evidence q

private def finishFixMatcherPlaceholderSupply
    (capability : Cap) (q : InferenceBase.FreshSupply) :
    Ty × Ty × InferenceBase.FreshSupply :=
  match capability.fcv with
  | first :: _ =>
      (.slot (.var first) (.var q.nextTy),
        .matcher capability (.var (q.nextTy + 1)),
        { q with nextTy := q.nextTy + 2 })
  | [] =>
      (.slot (.var ⟨q.nextCap⟩) (.var q.nextTy),
        .matcher capability (.var (q.nextTy + 1)),
        { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 2 })

private theorem finishFixMatcherPlaceholderSupply_option
    (option : Option (Cap × InferenceBase.FreshSupply)) :
    (match option with
    | none => none
    | some (capability, q) =>
        match capability.fcv with
        | first :: _ =>
            some (.slot (.var first) (.var q.nextTy),
              .matcher capability (.var (q.nextTy + 1)),
              { q with nextTy := q.nextTy + 2 })
        | [] =>
            some (.slot (.var ⟨q.nextCap⟩) (.var q.nextTy),
              .matcher capability (.var (q.nextTy + 1)),
              { q with nextCap := q.nextCap + 1, nextTy := q.nextTy + 2 })) = (do
      let (capability, q) ← option
      pure (finishFixMatcherPlaceholderSupply capability q)) := by
  cases option with
  | none => rfl
  | some pair =>
      rcases pair with ⟨capability, q⟩
      generalize fcvEq : capability.fcv = vars
      cases vars <;>
        simp [finishFixMatcherPlaceholderSupply, fcvEq]

private theorem fixMatcherPlaceholderSupply_eq
    (signature : FrozenSig) (clauses : List Clause)
    (q : InferenceBase.FreshSupply) :
    fixMatcherPlaceholderSupply signature clauses q = (do
      let (capability, q) ←
        recursiveMatcherTemplateSupply signature clauses q
      pure (finishFixMatcherPlaceholderSupply capability q)) := by
  unfold fixMatcherPlaceholderSupply recursiveMatcherTemplateSupply
  cases evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses with
  | none => rfl
  | some evidence =>
      let option :=
        match evidence with
        | .unseen => some (Cap.any, q)
        | evidence =>
            freshenSkeletonSupply signature.observability evidence q
      exact finishFixMatcherPlaceholderSupply_option option

private theorem recursiveMatcherTemplate_ddRun
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {initial final : InferState} {capability : Cap}
    (success : recursiveMatcherTemplate signature path clauses initial =
      some (capability, final)) :
    recursiveMatcherTemplateSupply signature clauses initial.supply =
        some (capability, final.supply) ∧
      FreshCapExtension initial final := by
  cases evidenceEq : matcherSkeletonEvidence signature.toMatcherSig clauses with
  | none => simp [recursiveMatcherTemplate, evidenceEq] at success
  | some evidence =>
      cases evidence with
      | unseen =>
          simp only [recursiveMatcherTemplate, evidenceEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨by simp [recursiveMatcherTemplateSupply, evidenceEq],
            FreshCapExtension.refl initial⟩
      | known leaf =>
          rcases freshenSkeleton_ddRun signature.observability
              (freshOrigin .recursiveBinder path "fix-producer-shape")
              (.known leaf) initial capability final (by
                simpa [recursiveMatcherTemplate, evidenceEq] using success) with
            ⟨pure, extension⟩
          exact ⟨by simpa [recursiveMatcherTemplateSupply, evidenceEq] using pure,
            extension⟩
      | con name children =>
          rcases freshenSkeleton_ddRun signature.observability
              (freshOrigin .recursiveBinder path "fix-producer-shape")
              (.con name children) initial capability final (by
                simpa [recursiveMatcherTemplate, evidenceEq] using success) with
            ⟨pure, extension⟩
          exact ⟨by simpa [recursiveMatcherTemplateSupply, evidenceEq] using pure,
            extension⟩
      | prod components =>
          rcases freshenSkeleton_ddRun signature.observability
              (freshOrigin .recursiveBinder path "fix-producer-shape")
              (.prod components) initial capability final (by
                simpa [recursiveMatcherTemplate, evidenceEq] using success) with
            ⟨pure, extension⟩
          exact ⟨by simpa [recursiveMatcherTemplateSupply, evidenceEq] using pure,
            extension⟩

/-- Exact correspondence between the executable matcher placeholder and the
pure supply-indexed placeholder used by `DDSynth.fixMatcher`. -/
theorem buildFixPlaceholder_matcher_ddRun
    {signature : FrozenSig} {path : SyntaxPath} {clauses : List Clause}
    {initial final : InferState} {domain codomain : Ty}
    (success : buildFixPlaceholder signature path (.matcher clauses) initial =
      some (domain, codomain, final)) :
    fixMatcherPlaceholderSupply signature clauses initial.supply =
        some (domain, codomain, final.supply) ∧
      final.prevailing = initial.prevailing ∧
      final.capabilityOrigins =
        DDLedger.markCapRange initial.capabilityOrigins initial.supply
          final.supply := by
  cases recursiveEq : recursiveMatcherTemplate signature path clauses initial with
  | none => simp [buildFixPlaceholder, recursiveEq] at success
  | some pair =>
      rcases pair with ⟨capability, middle⟩
      rcases recursiveMatcherTemplate_ddRun recursiveEq with
        ⟨recursivePure, recursiveExtension⟩
      generalize fcvEq : capability.fcv = capabilityVars
      cases capabilityVars with
      | nil =>
          simp [buildFixPlaceholder, recursiveEq, fcvEq] at success
          rcases success with ⟨rfl, rfl, rfl⟩
          let capState :=
            (middle.freshCap
              (freshOrigin .recursiveBinder path
                "fix-argument-capability")).2
          let targetState :=
            (capState.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
          let producerState :=
            (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
          have allocated : FreshCapExtension initial capState :=
            recursiveExtension.trans (FreshCapExtension.freshCap middle _)
          refine ⟨?_, ?_, ?_⟩
          · rw [fixMatcherPlaceholderSupply_eq, recursivePure]
            simp [finishFixMatcherPlaceholderSupply, fcvEq,
              InferState.freshCap,
              InferenceBase.freshCapMeta, InferState.freshTy,
              InferenceBase.freshTyMeta, InferState.recordEvent]
          · simpa [fcvEq, capState, targetState, producerState] using
              allocated.prevailing
          · have range := allocated.toRange
            simpa [fcvEq, capState, targetState, producerState,
              DDLedger.markCapRange, InferState.freshTy,
              InferenceBase.freshTyMeta, InferState.recordEvent] using range
      | cons first rest =>
          simp [buildFixPlaceholder, recursiveEq, fcvEq] at success
          rcases success with ⟨rfl, rfl, rfl⟩
          let targetState :=
            (middle.freshTy
              (freshOrigin .recursiveBinder path "fix-argument-target")).2
          let producerState :=
            (targetState.freshTy
              (freshOrigin .recursiveBinder path "fix-producer-target")).2
          refine ⟨?_, ?_, ?_⟩
          · rw [fixMatcherPlaceholderSupply_eq, recursivePure]
            simp [finishFixMatcherPlaceholderSupply, fcvEq,
              InferState.freshTy,
              InferenceBase.freshTyMeta, InferState.recordEvent]
          · simpa [fcvEq, targetState, producerState] using
              recursiveExtension.prevailing
          · have range := recursiveExtension.toRange
            simpa [fcvEq, targetState, producerState,
              DDLedger.markCapRange, InferState.freshTy,
              InferenceBase.freshTyMeta, InferState.recordEvent] using range

/-- Reconstruct recursive matcher synthesis from its exact placeholder cut,
body run, and final codomain alignment. -/
theorem DDSynthRun.fixMatcher
    {signature : FrozenSig} {context : Context} {self argument : String}
    {clauses : List Clause} {initial bodyInitial : InferState}
    {path : SyntaxPath} {domain codomain : Ty}
    {bodyResult : ExprResult} {alignedState : InferState}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholder : fixMatcherPlaceholderSupply signature clauses
      initial.supply = some (domain, codomain, bodyInitial.supply))
    (bodyPrevailing : bodyInitial.prevailing = initial.prevailing)
    (bodyLedger : bodyInitial.capabilityOrigins =
      DDLedger.markCapRange initial.capabilityOrigins initial.supply
        bodyInitial.supply)
    (bodyRun : DDSynthRun signature
      ((argument, Scheme.mono domain) ::
        (self, Scheme.mono (.fn domain codomain)) :: context)
      (.matcher clauses) bodyInitial bodyResult)
    (alignRun : DDAlignTypesRun bodyResult.target codomain bodyResult.state
      alignedState) :
    DDSynthRun signature context (.fix self argument (.matcher clauses))
      initial
      (finishExpr (.fix self argument (.matcher clauses)) path
        (.fn domain codomain) alignedState) := by
  rcases bodyRun with ⟨bodyTarget, bodyDerived, bodyTargetEq, bodyOrigin⟩
  rcases alignRun with ⟨alignedSupplyEq, alignedLedgerEq, aligned⟩
  subst bodyTarget
  rcases DDSynthOrigin.transportInitial bodyOrigin bodyPrevailing bodyLedger with
    ⟨bodyDerived', bodyOrigin'⟩
  have baseRun : DDSynthRun signature context
      (.fix self argument (.matcher clauses)) initial
      ⟨.fn domain codomain, alignedState⟩ := by
    unfold DDSynthRun
    let rawDerived := DDSynth.fixMatcher distinct direct placeholder
      bodyDerived' aligned.erase
    let finalDerived : DDSynth signature initial.supply initial.prevailing
        context (.fix self argument (.matcher clauses)) (.fn domain codomain)
        alignedState.supply alignedState.prevailing :=
      alignedSupplyEq.symm ▸ rawDerived
    refine ⟨.fn domain codomain, finalDerived, rfl, ?_⟩
    simp only [alignedSupplyEq, alignedLedgerEq]
    exact DDSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin'
      aligned
  unfold DDSynthRun at baseRun ⊢
  simpa [finishExpr] using baseRun

/-- The matcher-bodied recursive branch can be called directly from the
global expression mutual induction: its only recursive premise is the body
soundness hypothesis at the exact executable entry state. -/
theorem inferExprFuel_fixMatcher_ddSynthRun
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {self argument : String}
    {clauses : List Clause} {initial : InferState} {result : ExprResult}
    (bodySound : ∀ (bodyContext : Context) (bodySelfEnv : SelfEnv)
        (bodyInitial : InferState) (bodyResult : ExprResult),
      inferExprFuel fuel signature bodyContext bodySelfEnv (0 :: path)
        (.matcher clauses) bodyInitial = some bodyResult →
      DDSynthRun signature bodyContext (.matcher clauses) bodyInitial
        bodyResult)
    (success : inferExprFuel (fuel + 1) signature context selfEnv path
      (.fix self argument (.matcher clauses)) initial = some result) :
    DDSynthRun signature context (.fix self argument (.matcher clauses))
      initial result := by
  cases gate : (self != argument &&
      DirectSelf.check self (.matcher clauses)) with
  | false => simp [inferExprFuel, gate] at success
  | true =>
      rcases (DirectSelf.fix_gate_eq_true self argument
        (.matcher clauses)).mp gate with ⟨distinct, direct⟩
      let visited := visit initial .exprFix path
      cases placeholderEq : buildFixPlaceholder signature path
          (.matcher clauses) visited with
      | none =>
          simp [inferExprFuel, gate, visited, placeholderEq] at success
      | some placeholderResult =>
          rcases placeholderResult with ⟨domain, codomain, placeholderState⟩
          let placeholder := Ty.fn domain codomain
          let bodyInitial :=
            (placeholderState.recordEvent
              (.fixPlaceholder self argument placeholder path)).recordEvent
              (.directSelfAccepted self placeholder path)
          let bodyContext :=
            (argument, Scheme.mono domain) ::
              (self, Scheme.mono placeholder) :: context
          let bodySelfEnv :=
            (self, placeholder) :: selfEnv.eraseMany [self, argument]
          cases bodyEq : inferExprFuel fuel signature bodyContext bodySelfEnv
              (0 :: path) (.matcher clauses) bodyInitial with
          | none =>
              have actualBodyEq := bodyEq
              simp only [bodyContext, bodySelfEnv, bodyInitial, placeholder]
                at actualBodyEq
              simp [inferExprFuel, gate, visited, placeholderEq,
                actualBodyEq] at success
          | some bodyResult =>
              have actualBodyEq := bodyEq
              simp only [bodyContext, bodySelfEnv, bodyInitial, placeholder]
                at actualBodyEq
              cases alignEq : alignTypes bodyResult.state
                  (freshOrigin .recursiveBinder path "fix-result")
                  bodyResult.target codomain with
              | none =>
                  simp [inferExprFuel, gate, visited, placeholderEq,
                    actualBodyEq, alignEq] at success
              | some alignedState =>
                  have resultEq : finishExpr
                      (.fix self argument (.matcher clauses)) path placeholder
                      alignedState = result := by
                    apply Option.some.inj
                    simpa [inferExprFuel, gate, visited, placeholderEq,
                      actualBodyEq, alignEq] using success
                  subst result
                  rcases buildFixPlaceholder_matcher_ddRun placeholderEq with
                    ⟨placeholderPure, placeholderPrevailing,
                      placeholderLedger⟩
                  apply DDSynthRun.fixMatcher distinct direct placeholderPure
                  · simpa [bodyInitial, visited, InferState.recordEvent] using
                      placeholderPrevailing
                  · simpa [bodyInitial, visited, InferState.recordEvent] using
                      placeholderLedger
                  · exact bodySound bodyContext bodySelfEnv bodyInitial
                      bodyResult bodyEq
                  · exact alignTypes_ddAlignTypesRun alignEq

end Inference
end TypePM
