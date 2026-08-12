import TypePM.DemandTypingOriginMetatheory
import TypePM.DemandTypingTerminalAuditBuilder
import TypePM.PolyCloseLaws
import TypePM.CertifiedInferenceRegression
import TypePM.AcceptanceGapRegression
import TypePM.RecursiveExamples

/-!
# Demand-directed judgment regressions

Concrete inhabitants and refutations for the `DDSynth`/`DDCheck` judgments:
a solve-free synthesis, an application whose domain alignment and argument
check each perform one paired solve, a positive slot-demand coercion of a
product of matchers at a slot-headed expectation, and the align-level
refutation showing that the same product admits no checking cut against a
matcher-headed expectation.  The positive/negative pair pins the slot-demand
boundary for the judgment itself, mirroring the selector-level regressions
of `CertifiedInferenceRegression`.

The pattern layer is exercised end to end by two flagship derivations: the
or-pattern program of `AcceptanceGapRegression` (a `matchAll` whose pattern
aligns two independently allocated binder metas by name), and a delegating
matcher literal (one catch-all clause whose hole slot is fed by `something`
one-way and whose arm body is an inner `matchAll`), which closes at
`Matcher Any Int` through the same executable finalization checks consumed
by the executable traversal.
-/

namespace TypePM
namespace DemandTypingRegression

open CertifiedInferenceRegression (emptySignature concretePairProductType
  concretePairMatcherType concretePairSlotType)

/-- Origin certificates are insensitive to the proof term used for the same
raw demand-typing proposition. -/
theorem DDSynthOrigin.transportRaw
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw raw' : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger') :
    DDSynthOrigin signature raw' ledger ledger' := by
  have proofEq : raw = raw' := Subsingleton.elim _ _
  cases proofEq
  exact origin

theorem DDSynthOrigin.transportRawTo
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDSynthOrigin signature raw ledger ledger')
    (raw' : DDSynth signature q S context expression target q' S') :
    DDSynthOrigin signature raw' ledger ledger' :=
  DDSynthOrigin.transportRaw origin

/-- Package the source proof term existentially so constructor-built origin
certificates elaborate independently of an opaque regression witness. -/
theorem DDSynthOrigin.transportSome
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw' : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (source : ∃ raw : DDSynth signature q S context expression target q' S',
      DDSynthOrigin signature raw ledger ledger') :
    DDSynthOrigin signature raw' ledger ledger' := by
  rcases source with ⟨raw, origin⟩
  exact DDSynthOrigin.transportRaw origin

/-- Exact paired solves whose capability component is identity are admissible
under every origin ledger. -/
def originSafePairedCapId (ledger : CapabilityOriginLedger)
    {left right : Ty} {targetSubst : TySubst}
    (exact : ExactPairedMGU left right ⟨CapSubst.id, targetSubst⟩) :
    OriginSafeExactPairedMGU ledger left right
      ⟨CapSubst.id, targetSubst⟩ :=
  ⟨exact, ⟨AdmissibleCapPost.id ledger⟩⟩

/-! ## Capability-range ledger order -/

/-- A two-variable batch has exactly the stack order produced by two
successive executable `freshCap` updates: the later allocation shadows at the
ledger head. -/
theorem markCapRange_two_exact (ledger : CapabilityOriginLedger)
    (nextCap nextTy : Nat) :
    let q : InferenceBase.FreshSupply := ⟨nextCap, nextTy⟩
    DDLedger.markCapRange ledger q
        { q with nextCap := q.nextCap + 2 } =
      (ledger.setOrigin ⟨nextCap⟩ .structuralFlexible).setOrigin
        ⟨nextCap + 1⟩ .structuralFlexible := by
  simp only [DDLedger.markCapRange]
  have rangeLength : nextCap + 2 - nextCap = 2 := by omega
  rw [rangeLength, show List.range 2 = [0, 1] by decide]
  rfl

/-- The same exact-order equation stated directly against two executable
allocations. -/
theorem markCapRange_two_matches_freshCap (state : Inference.InferState)
    (origin : Inference.ConstraintOrigin) :
    let first := (state.freshCap origin).2
    let second := (first.freshCap origin).2
    DDLedger.markCapRange state.capabilityOrigins state.supply second.supply =
      second.capabilityOrigins := by
  simpa [Inference.InferState.freshCap, InferenceBase.freshCapMeta,
    Inference.InferState.recordEvent] using
    (markCapRange_two_exact state.capabilityOrigins state.supply.nextCap
      state.supply.nextTy)

/-! ## Solve-free synthesis -/

/-- `λx. x` with a fresh metavariable domain. -/
def identityExpr : Expr := .lam "x" (.var "x")

/-- The identity function synthesizes its λ domain as a fresh metavariable
and consumes no solve. -/
def identity_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] identityExpr
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
  apply DDSynth.lam
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("x", Scheme.mono (.var 0))]) (name := "x")
      (scheme := Scheme.mono (.var 0)) (by
        simp [Context.applySubst, Context.find?]))

def identity_ddSynthOrigin :
    DDSynthOrigin emptySignature identity_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst Subst.id
      [("x", Scheme.mono (.var 0))]).find? "x" =
      some (Scheme.mono (.var 0)) := by
    simp [Context.applySubst, Context.find?]
  have bodyOrigin : DDSynthOrigin emptySignature
      (DDSynth.var (q := ⟨0, 1⟩) lookup) [] [] := by
    simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, Scheme.mono,
      Scheme.canonicalCapImages, CapabilityOriginLedger.setOrigins] using
      (DDSynthOrigin.var (signature := emptySignature) (q := ⟨0, 1⟩)
        (ledger := []) lookup)
  let raw₀ := DDSynth.lam (signature := emptySignature) (q := ⟨0, 0⟩)
    (DDSynth.var (q := ⟨0, 1⟩) lookup)
  have origin₀ : DDSynthOrigin emptySignature raw₀ [] [] :=
    DDSynthOrigin.lam (q := ⟨0, 0⟩) bodyOrigin
  have raw₀' : DDSynth emptySignature ⟨0, 0⟩ Subst.id [] identityExpr
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
    simpa only [raw₀, identityExpr,
      InferenceBase.instantiateScheme_mono_value,
      InferenceBase.instantiateScheme_mono_supply] using raw₀
  exact ⟨raw₀', by
    simpa only [raw₀, identityExpr,
      InferenceBase.instantiateScheme_mono_value,
      InferenceBase.instantiateScheme_mono_supply] using origin₀⟩

def identity_terminalAudit :
    ∀ terminal, DDSynthTerminalAudit terminal emptySignature
      identity_ddSynthOrigin := by
  intro terminal
  let lookup : (Context.applySubst Subst.id
      [("x", Scheme.mono (.var 0))]).find? "x" =
      some (Scheme.mono (.var 0)) := by
    simp [Context.applySubst, Context.find?]
  let bodyOrigin := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 1⟩) (ledger := []) lookup
  let bodyAudit : DDSynthTerminalAudit terminal emptySignature bodyOrigin :=
    DDSynthTerminalAudit.var (lookup := lookup)
  let origin₀ := DDSynthOrigin.lam (q := ⟨0, 0⟩) bodyOrigin
  let audit₀ : DDSynthTerminalAudit terminal emptySignature origin₀ :=
    DDSynthTerminalAudit.lam bodyAudit
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, bodyAudit, identityExpr,
    DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins,
    Scheme.canonicalCapImages, Scheme.FreshOpening.capImages,
    Scheme.mono] using source₀

/-- The closed wrapper publishes the identity type unchanged. -/
theorem identity_ddTyping :
    DDTyping emptySignature [] identityExpr (.fn (.var 0) (.var 0)) :=
  ⟨.fn (.var 0) (.var 0), ⟨0, 1⟩, Subst.id, identity_ddSynth, [],
    identity_ddSynthOrigin, identity_terminalAudit Subst.id,
    by simp [Subst.apply_id]⟩

/-! ## One application: domain alignment and argument solve -/

/-- The most general paired solution of the application-function alignment
`fn ?0 ?0 ≐ fn ?1 ?2`. -/
def applicationDelta : TySubst := fnDiagonalDelta 0 1 2

theorem applicationDelta_pairedMGU :
    ExactPairedMGU (.fn (.var 0) (.var 0)) (.fn (.var 1) (.var 2))
      ⟨CapSubst.id, applicationDelta⟩ :=
  ExactPairedMGU.fnDiagonal 0 1 2 (by decide) (by decide) (by decide)

/-- Prevailing substitution after application-function alignment. -/
def applicationFunctionSubst : Subst :=
  Subst.seq ⟨CapSubst.id, applicationDelta⟩ Subst.id

/-- Terminal substitution of `(λx. x) 1`: the function alignment followed by
the argument solve. -/
def applicationTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 1 .int⟩
    applicationFunctionSubst

theorem applicationArgument_ddCheck :
    DDCheck emptySignature ⟨0, 3⟩ applicationFunctionSubst [] (.lit 1)
      (.var 1) ⟨0, 3⟩ applicationTerminal := by
  exact .mk .lit (.ordinary rfl (.ordinary rfl
    (ExactPairedMGU.varRight .int 1 (by decide))))

def applicationArgument_ddCheckOrigin :
    DDCheckOrigin emptySignature applicationArgument_ddCheck [] [] := by
  refine .mk (synthesized := DDSynth.lit (signature := emptySignature)
    (q := ⟨0, 3⟩) (S := applicationFunctionSubst) (Γ := [])
    (value := 1)) .lit ?_
  exact .ordinary (S := applicationFunctionSubst) (raw := .int)
    (expected := .var 1) rfl
      (.ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.varRight .int 1 (by decide))))

theorem application_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      (.app identityExpr (.lit 1)) (.var 2) ⟨0, 3⟩
      applicationTerminal := by
  exact .app identity_ddSynth
    (.ordinary rfl applicationDelta_pairedMGU)
    applicationArgument_ddCheck

def application_ddSynthOrigin :
    DDSynthOrigin emptySignature application_ddSynth [] [] := by
  exact .app identity_ddSynthOrigin
    (.ordinary rfl (originSafePairedCapId [] applicationDelta_pairedMGU))
    applicationArgument_ddCheckOrigin

def application_terminalAudit :
    DDSynthTerminalAudit applicationTerminal emptySignature
      application_ddSynthOrigin := by
  let functionAudit := identity_terminalAudit applicationTerminal
  let argumentSynthOrigin := DDSynthOrigin.lit (signature := emptySignature)
    (q := ⟨0, 3⟩) (S := applicationFunctionSubst) (context := [])
    (value := 1) (ledger := [])
  let argumentSynthAudit : DDSynthTerminalAudit applicationTerminal
      emptySignature argumentSynthOrigin := DDSynthTerminalAudit.lit
  let argumentAligned : DDAlignWithLedger [] applicationFunctionSubst .int
      (.var 1) applicationTerminal :=
    .ordinary rfl (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight .int 1 (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    argumentSynthAudit
  let functionAligned : DDAlignTypesWithLedger [] Subst.id
      (.fn (.var 0) (.var 0)) (.fn (.var 1) (.var 2))
      applicationFunctionSubst :=
    .ordinary rfl (originSafePairedCapId [] applicationDelta_pairedMGU)
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        functionAudit argumentAudit))

/-- `(λx. x) 1` closes at `Int` through one domain alignment and one
demand-free ordinary argument alignment. -/
theorem application_ddTyping :
    DDTyping emptySignature [] (.app identityExpr (.lit 1)) .int := by
  exact ⟨.var 2, ⟨0, 3⟩, applicationTerminal, application_ddSynth, [],
    application_ddSynthOrigin, application_terminalAudit, rfl⟩

/-! ## Slot demand: positive coercion and matcher-headed refutation -/

/-- `(something, something)`: a raw product of matcher producers. -/
def somethingPair : Expr := .tuple [.something, .something]

/-- The raw synthesized type of `somethingPair` from the empty supply. -/
def somethingPairRaw : Ty :=
  .prod [.matcher .any (.var 0), .matcher .any (.var 1)]

theorem somethingPair_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] somethingPair
      somethingPairRaw ⟨0, 2⟩ Subst.id := by
  exact .tuple (.cons .something (.cons .something .nil))

/-- Restricted one-way capability component of the product-matcher lift: the
consumer prod-of-`Any` capability accepts the producer with no bindings. -/
def pairCapDelta : CapSubst :=
  CapMatch.Bindings.toSubstWithin (Cap.prod [.any, .any]).fcv []

/-- Most general target solution of the lifted producer-to-slot targets. -/
def pairTargetDelta : TySubst := fun candidate =>
  if candidate = 0 then .int
  else if candidate = 1 then .int
  else .var candidate

theorem pairTargetDelta_targetMGU :
    TargetMGU (.prod [.var 0, .var 1]) (.prod [.int, .int])
      pairTargetDelta := by
  constructor
  · rfl
  · intro U unifies
    have components :
        Ty.prod [U 0, U 1] = Ty.prod [Ty.int, Ty.int] := unifies
    have listEq : [U 0, U 1] = [Ty.int, Ty.int] := by
      injection components
    have headEq : U 0 = Ty.int := by
      injection listEq
    have tailEq : U 1 = Ty.int := by
      have tailListEq : [U 1] = [Ty.int] := by
        injection listEq with _ tailListEq
      injection tailListEq
    refine ⟨U, ?_⟩
    funext candidate
    by_cases hzero : candidate = 0
    · subst hzero
      exact headEq
    · by_cases hone : candidate = 1
      · subst hone
        simp only [TySubst.comp, pairTargetDelta, if_neg hzero]
        exact tailEq
      · simp only [TySubst.comp, pairTargetDelta, if_neg hzero, if_neg hone]
        rfl

/-- The lifted-target solution is exact: it is the identity outside the
two component targets. -/
theorem pairTargetDelta_exact :
    ExactTargetMGU (.prod [.var 0, .var 1]) (.prod [.int, .int])
      pairTargetDelta := by
  have deltaIdem : pairTargetDelta.Idempotent := by
    apply TySubst.idempotent_of_pointwise
    intro candidate
    by_cases hzero : candidate = 0
    · subst hzero
      rfl
    · by_cases hone : candidate = 1
      · subst hone
        rfl
      · rw [show pairTargetDelta candidate = .var candidate from by
          show (if candidate = 0 then Ty.int
            else if candidate = 1 then Ty.int
            else .var candidate) = .var candidate
          rw [if_neg hzero, if_neg hone]]
        show pairTargetDelta candidate = .var candidate
        show (if candidate = 0 then Ty.int
          else if candidate = 1 then Ty.int
          else .var candidate) = .var candidate
        rw [if_neg hzero, if_neg hone]
  refine ⟨pairTargetDelta_targetMGU, ?_, ?_, ?_, deltaIdem⟩
  · intro candidate outside
    have hzero : ¬ candidate = 0 := fun h => outside (by
      cases h
      simp [Ty.ftv, Ty.ftvList])
    have hone : ¬ candidate = 1 := fun h => outside (by
      cases h
      simp [Ty.ftv, Ty.ftvList])
    simp [pairTargetDelta, hzero, hone]
  · intro candidate mem image imageMem
    by_cases hzero : candidate = 0
    · subst hzero
      rw [show pairTargetDelta 0 = Ty.int from rfl] at imageMem
      nomatch imageMem
    · by_cases hone : candidate = 1
      · subst hone
        rw [show pairTargetDelta 1 = Ty.int from rfl] at imageMem
        nomatch imageMem
      · rw [show pairTargetDelta candidate = .var candidate from by
          show (if candidate = 0 then Ty.int
            else if candidate = 1 then Ty.int
            else .var candidate) = .var candidate
          rw [if_neg hzero, if_neg hone]] at imageMem
        have h : image = candidate := by simpa [Ty.ftv] using imageMem
        simpa [h] using mem
  · intro candidate mem image imageMem
    by_cases hzero : candidate = 0
    · subst hzero
      rw [show pairTargetDelta 0 = Ty.int from rfl] at imageMem
      nomatch imageMem
    · by_cases hone : candidate = 1
      · subst hone
        rw [show pairTargetDelta 1 = Ty.int from rfl] at imageMem
        nomatch imageMem
      · rw [show pairTargetDelta candidate = .var candidate from by
          show (if candidate = 0 then Ty.int
            else if candidate = 1 then Ty.int
            else .var candidate) = .var candidate
          rw [if_neg hzero, if_neg hone]] at imageMem
        have empty : (Ty.var candidate).fcv = ([] : List CapVar) := rfl
        rw [empty] at imageMem
        nomatch imageMem

/-- Terminal substitution of the positive slot-demand coercion. -/
def somethingPairTerminal : Subst :=
  Subst.seq ⟨pairCapDelta, pairTargetDelta⟩ Subst.id

/-- The product of matcher producers checks against the aggregate slot
expectation through the product-matcher lift, and the lift resolves both
`something` targets to `Int`. -/
theorem somethingPair_checks_at_slot :
    DDCheck emptySignature ⟨0, 0⟩ Subst.id [] somethingPair
        concretePairSlotType ⟨0, 2⟩ somethingPairTerminal ∧
      somethingPairTerminal.apply somethingPairRaw =
        concretePairProductType := by
  refine ⟨.mk somethingPair_ddSynth ?_, rfl⟩
  exact .productMatcherLift rfl
    (show Subst.id.apply concretePairSlotType =
      .slot (.prod [.any, .any]) (.prod [.int, .int]) from rfl)
    ⟨[], rfl, by rfl, pairTargetDelta_exact⟩

/-- A matcher-headed expectation is not a demand: no checking cut exists for
the raw product of matchers against the matcher-headed pair expectation, at
any output substitution.  Together with `somethingPair_checks_at_slot`, this
pins the slot-demand boundary at the level of the judgment. -/
theorem somethingPairRaw_no_matcher_expected_cut :
    ∀ S', ¬ DDAlign Subst.id somethingPairRaw concretePairMatcherType S' := by
  intro S' aligned
  have matcherView :
      Subst.id.apply concretePairMatcherType =
        .matcher (.prod [.any, .any]) (.prod [.int, .int]) := rfl
  have ordinary := aligned.matcherExpected matcherView
  cases ordinary with
  | matcherPair rawView _ _ _ => nomatch rawView
  | slotPair rawView _ _ _ => nomatch rawView
  | ordinary _ mgu => nomatch mgu.1.1

/-! ## Polymorphic `let`: generalization and quantified instantiation -/

/-- The Damas–Milner witness `let id = λx. x in (id id) 1`. -/
def dmLetProgram : Expr :=
  .letE "id" identityExpr (.app (.app (.var "id") (.var "id")) (.lit 1))

/-- The generalized scheme of `id` computed at the `let` cut. -/
def dmIdScheme : Scheme :=
  Scheme.close [] [0] (.fn (.var 0) (.var 0))

@[simp] theorem dmIdScheme_applyMeta (S : Subst) :
    dmIdScheme.applyMeta S = dmIdScheme := by
  unfold dmIdScheme
  apply Scheme.close_applyMeta_eq_self <;>
    simp [Ty.fcv, Ty.ftv]

@[simp] theorem dmIdScheme_instance_value
    (q : InferenceBase.FreshSupply) :
    (InferenceBase.instantiateScheme q dmIdScheme).value =
      .fn (.var q.nextTy) (.var q.nextTy) := by
  rw [InferenceBase.instantiateScheme_value]
  simp [dmIdScheme, Scheme.openValue_close, openingTySubst, Subst.apply,
    Ty.applyCapability, Ty.applyTarget,
    Scheme.canonicalFreshOpening, Scheme.FreshOpening.toValueOpening,
    List.finIdxOf?]

@[simp] theorem dmIdScheme_instance_supply
    (q : InferenceBase.FreshSupply) :
    (InferenceBase.instantiateScheme q dmIdScheme).supply =
      { q with nextTy := q.nextTy + 1 } := by
  cases q
  rfl

@[simp] theorem dmIdScheme_capImages
    (q : InferenceBase.FreshSupply) :
    Scheme.canonicalCapImages q dmIdScheme = [] := by
  apply Scheme.canonicalCapImages_eq_nil_of_capArity_zero
  rfl

/-- Prevailing substitution after the inner function alignment
`fn ?1 ?1 ≐ fn ?2 ?3`. -/
def dmAlign1 : Subst :=
  Subst.seq ⟨CapSubst.id, fnDiagonalDelta 1 2 3⟩ Subst.id

/-- Prevailing substitution after the inner argument solve fixes the inner
domain to the second instance `fn ?4 ?4`. -/
def dmInner : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 2 (.fn (.var 4) (.var 4))⟩ dmAlign1

/-- Prevailing substitution after the outer function alignment
`fn ?4 ?4 ≐ fn ?5 ?6`. -/
def dmAlign2 : Subst :=
  Subst.seq ⟨CapSubst.id, fnDiagonalDelta 4 5 6⟩ dmInner

/-- Terminal substitution of the witness: the literal-argument solve after
the three preceding cuts. -/
def dmLetTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 5 .int⟩ dmAlign2

/-- `id id` under the generalized scheme: both uses instantiate the
quantified scheme at distinct fresh images (`?1` and `?4`), and the argument
check resolves the inner domain by an ordinary demand-free alignment. -/
def dmInnerFunction_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("id", dmIdScheme)]
      (.var "id") (.fn (.var 1) (.var 1)) ⟨0, 2⟩ Subst.id := by
  simpa only [dmIdScheme_instance_value, dmIdScheme_instance_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("id", dmIdScheme)]) (name := "id")
      (scheme := dmIdScheme) (by
        simp [Context.applySubst, Context.find?]))

theorem dmInnerFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature dmInnerFunction_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst Subst.id [("id", dmIdScheme)]).find? "id" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  rw [← dmIdScheme_instance_value ⟨0, 1⟩,
    ← dmIdScheme_instance_supply ⟨0, 1⟩]
  refine ⟨DDSynth.var (signature := emptySignature) lookup, ?_⟩
  simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.var (ledger := []) lookup)

def dmInnerArgumentVar_ddSynth :
    DDSynth emptySignature ⟨0, 4⟩ dmAlign1 [("id", dmIdScheme)]
      (.var "id") (.fn (.var 4) (.var 4)) ⟨0, 5⟩ dmAlign1 := by
  simpa only [dmIdScheme_instance_value, dmIdScheme_instance_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 4⟩)
      (S := dmAlign1) (Γ := [("id", dmIdScheme)])
      (name := "id") (scheme := dmIdScheme) (by
        simp [Context.applySubst, Context.find?]))

theorem dmInnerArgumentVar_ddSynthOrigin :
    DDSynthOrigin emptySignature dmInnerArgumentVar_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst dmAlign1 [("id", dmIdScheme)]).find? "id" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  rw [← dmIdScheme_instance_value ⟨0, 4⟩,
    ← dmIdScheme_instance_supply ⟨0, 4⟩]
  refine ⟨DDSynth.var (signature := emptySignature) lookup, ?_⟩
  simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.var (ledger := []) lookup)

theorem dmInnerArgument_ddCheck :
    DDCheck emptySignature ⟨0, 4⟩ dmAlign1 [("id", dmIdScheme)]
      (.var "id") (.var 2) ⟨0, 5⟩ dmInner := by
  exact .mk dmInnerArgumentVar_ddSynth
    (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight (.fn (.var 4) (.var 4)) 2 (by decide))))

theorem dmInnerArgument_ddCheckOrigin :
    DDCheckOrigin emptySignature dmInnerArgument_ddCheck [] [] := by
  exact .mk dmInnerArgumentVar_ddSynthOrigin (.ordinary (S := dmAlign1)
    (raw := .fn (.var 4) (.var 4)) (expected := .var 2) rfl
      (.ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.varRight (.fn (.var 4) (.var 4)) 2
          (by decide)))))

theorem dmInnerApp_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("id", dmIdScheme)]
      (.app (.var "id") (.var "id")) (.var 3) ⟨0, 5⟩ dmInner := by
  exact DDSynth.app (q₁ := ⟨0, 2⟩) (S₁ := Subst.id) (S₂ := dmAlign1)
    (functionTarget := .fn (.var 1) (.var 1))
    dmInnerFunction_ddSynth
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    dmInnerArgument_ddCheck

theorem dmInnerApp_ddSynthOrigin :
    DDSynthOrigin emptySignature dmInnerApp_ddSynth [] [] := by
  exact .app dmInnerFunction_ddSynthOrigin
    (.ordinary (S := Subst.id)
    (left := .fn (.var 1) (.var 1))
    (right := .fn (.var 2) (.var 3)) rfl
      (originSafePairedCapId []
        (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide)
          (by decide)))) dmInnerArgument_ddCheckOrigin

theorem dmOuterApp_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("id", dmIdScheme)]
      (.app (.app (.var "id") (.var "id")) (.lit 1)) (.var 6)
      ⟨0, 7⟩ dmLetTerminal := by
  exact DDSynth.app (q₁ := ⟨0, 5⟩) (S₁ := dmInner) (S₂ := dmAlign2)
    (functionTarget := .var 3) dmInnerApp_ddSynth
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 4 5 6 (by decide) (by decide) (by decide)))
    (.mk .lit (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight .int 5 (by decide)))))

theorem dmOuterArgument_ddCheck :
    DDCheck emptySignature ⟨0, 7⟩ dmAlign2 [("id", dmIdScheme)]
      (.lit 1) (.var 5) ⟨0, 7⟩ dmLetTerminal := by
  exact .mk .lit (.ordinary rfl (.ordinary rfl
    (ExactPairedMGU.varRight .int 5 (by decide))))

theorem dmOuterArgument_ddCheckOrigin :
    DDCheckOrigin emptySignature dmOuterArgument_ddCheck [] [] := by
  refine .mk (synthesized := DDSynth.lit (signature := emptySignature)
    (q := ⟨0, 7⟩) (S := dmAlign2) (Γ := [("id", dmIdScheme)])
    (value := 1)) .lit ?_
  exact .ordinary (S := dmAlign2) (raw := .int) (expected := .var 5) rfl
    (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight .int 5 (by decide))))

theorem dmOuterApp_ddSynthOrigin :
    DDSynthOrigin emptySignature dmOuterApp_ddSynth [] [] := by
  refine .app dmInnerApp_ddSynthOrigin
    (.ordinary (S := dmInner) (left := .var 3)
      (right := .fn (.var 5) (.var 6)) rfl (originSafePairedCapId []
      (ExactPairedMGU.fnDiagonal 4 5 6 (by decide) (by decide) (by decide))))
    dmOuterArgument_ddCheckOrigin

theorem dmLet_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] dmLetProgram (.var 6)
      ⟨0, 7⟩ dmLetTerminal :=
  .letE identity_ddSynth dmOuterApp_ddSynth

theorem dmLet_ddSynthOrigin :
    DDSynthOrigin emptySignature dmLet_ddSynth [] [] := by
  exact .letE identity_ddSynthOrigin dmOuterApp_ddSynthOrigin

def dmInnerFunction_terminalAudit :
    DDSynthTerminalAudit dmLetTerminal emptySignature
      dmInnerFunction_ddSynthOrigin := by
  let lookup : (Context.applySubst Subst.id [("id", dmIdScheme)]).find? "id" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  let origin₀ := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 1⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit dmLetTerminal emptySignature origin₀ :=
    DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [dmIdScheme_instance_value, dmIdScheme_instance_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins] using source₀

def dmInnerArgumentVar_terminalAudit :
    DDSynthTerminalAudit dmLetTerminal emptySignature
      dmInnerArgumentVar_ddSynthOrigin := by
  let lookup : (Context.applySubst dmAlign1 [("id", dmIdScheme)]).find? "id" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  let origin₀ := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 4⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit dmLetTerminal emptySignature origin₀ :=
    DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [dmIdScheme_instance_value, dmIdScheme_instance_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins] using source₀

def dmInnerApp_terminalAudit :
    DDSynthTerminalAudit dmLetTerminal emptySignature
      dmInnerApp_ddSynthOrigin := by
  let argumentAligned : DDAlignWithLedger [] dmAlign1
      (.fn (.var 4) (.var 4)) (.var 2) dmInner :=
    .ordinary rfl (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight (.fn (.var 4) (.var 4)) 2 (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    dmInnerArgumentVar_terminalAudit
  let functionAligned : DDAlignTypesWithLedger [] Subst.id
      (.fn (.var 1) (.var 1)) (.fn (.var 2) (.var 3)) dmAlign1 :=
    .ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        dmInnerFunction_terminalAudit argumentAudit))

def dmOuterApp_terminalAudit :
    DDSynthTerminalAudit dmLetTerminal emptySignature
      dmOuterApp_ddSynthOrigin := by
  let argumentSynthOrigin := DDSynthOrigin.lit (signature := emptySignature)
    (q := ⟨0, 7⟩) (S := dmAlign2) (context := [("id", dmIdScheme)])
    (value := 1) (ledger := [])
  let argumentSynthAudit : DDSynthTerminalAudit dmLetTerminal emptySignature
      argumentSynthOrigin := DDSynthTerminalAudit.lit
  let argumentAligned : DDAlignWithLedger [] dmAlign2 .int (.var 5)
      dmLetTerminal := .ordinary rfl (.ordinary rfl
        (originSafePairedCapId []
          (ExactPairedMGU.varRight .int 5 (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    argumentSynthAudit
  let functionAligned : DDAlignTypesWithLedger [] dmInner (.var 3)
      (.fn (.var 5) (.var 6)) dmAlign2 :=
    .ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.fnDiagonal 4 5 6 (by decide) (by decide) (by decide)))
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        dmInnerApp_terminalAudit argumentAudit))

def dmLet_terminalAudit :
    DDSynthTerminalAudit dmLetTerminal emptySignature dmLet_ddSynthOrigin := by
  let stable :
      (emptySignature.generalize
        (Context.applySubst Subst.id ([] : Context))
        (Subst.id.apply (.fn (.var 0) (.var 0)))).applyMeta dmLetTerminal =
      emptySignature.generalize
        (Context.applySubst dmLetTerminal ([] : Context))
        (dmLetTerminal.apply (.fn (.var 0) (.var 0))) := by
    native_decide
  let facts : DDTerminalAudit.LetFacts dmLetTerminal emptySignature []
      (.fn (.var 0) (.var 0)) Subst.id := ⟨by simpa using stable⟩
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.letE
        (identity_terminalAudit dmLetTerminal) dmOuterApp_terminalAudit facts))

/-- The polymorphic-`let` witness closes at `Int` through the demand-directed
judgment: the `let` rule generalizes the value type in the substituted
context, and each use of `id` instantiates the quantified scheme at a fresh
supply-indexed image. -/
theorem dmLet_ddTyping :
    DDTyping emptySignature [] dmLetProgram .int := by
  exact ⟨.var 6, ⟨0, 7⟩, dmLetTerminal, dmLet_ddSynth, [],
    dmLet_ddSynthOrigin, dmLet_terminalAudit, rfl⟩

/-! ## `let` polymorphism across the two matcher producers

The accepted idiom for the nested-capability boundary pair: `let`
polymorphism gives each use of the shared consumer its own instance of the
generalized domain, so no demand-free coercion is needed.  The
demand-directed derivation closes at exactly the executable raw result
shape pinned by
`AcceptanceGapRegression.nestedCapLetProgram_raw_target_shape`: a bare
matcher in the first component and an unlifted product of two bare
matchers in the second, at pairwise-distinct targets.  Both argument
alignments are ordinary demand-free solves against a variable expectation
— no branch of `DDAlign` invents a slot head for either producer. -/

/-- Prevailing substitution after the first-use function alignment
`fn ?1 ?1 ≐ fn ?2 ?3`. -/
def nestedCapLetAlign1 : Subst :=
  Subst.seq ⟨CapSubst.id, fnDiagonalDelta 1 2 3⟩ Subst.id

/-- Prevailing substitution after the first argument check resolves the
first instance domain to the bare matcher producer. -/
def nestedCapLetCheck1 : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 2 (.matcher .any (.var 4))⟩ nestedCapLetAlign1

/-- Prevailing substitution after the second-use function alignment
`fn ?5 ?5 ≐ fn ?6 ?7`. -/
def nestedCapLetAlign2 : Subst :=
  Subst.seq ⟨CapSubst.id, fnDiagonalDelta 5 6 7⟩ nestedCapLetCheck1

/-- Terminal substitution: the second argument check resolves the second
instance domain to the raw, unlifted product of matcher producers. -/
def nestedCapLetTerminal : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 6
      (.prod [.matcher .any (.var 8), .matcher .any (.var 9)])⟩
    nestedCapLetAlign2

/-- The first use: a fresh instance `fn ?2 ?3` whose domain receives the
bare matcher producer by an ordinary demand-free alignment. -/
def nestedCapLetFirstFunction_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("f", dmIdScheme)]
      (.var "f") (.fn (.var 1) (.var 1)) ⟨0, 2⟩ Subst.id := by
  simpa only [dmIdScheme_instance_value, dmIdScheme_instance_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("f", dmIdScheme)]) (name := "f")
      (scheme := dmIdScheme) (by
        simp [Context.applySubst, Context.find?]))

theorem nestedCapLetFirstFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetFirstFunction_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst Subst.id [("f", dmIdScheme)]).find? "f" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  rw [← dmIdScheme_instance_value ⟨0, 1⟩,
    ← dmIdScheme_instance_supply ⟨0, 1⟩]
  refine ⟨DDSynth.var (signature := emptySignature) lookup, ?_⟩
  simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.var (ledger := []) lookup)

theorem nestedCapLetFirstArgument_ddCheck :
    DDCheck emptySignature ⟨0, 4⟩ nestedCapLetAlign1 [("f", dmIdScheme)]
      .something (.var 2) ⟨0, 5⟩ nestedCapLetCheck1 := by
  exact .mk .something (.ordinary rfl (.ordinary rfl
    (ExactPairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide))))

theorem nestedCapLetFirstArgument_ddCheckOrigin :
    DDCheckOrigin emptySignature nestedCapLetFirstArgument_ddCheck [] [] := by
  refine .mk (synthesized := DDSynth.something (signature := emptySignature)
    (q := ⟨0, 4⟩) (S := nestedCapLetAlign1) (Γ := [("f", dmIdScheme)]))
    .something ?_
  exact .ordinary (S := nestedCapLetAlign1)
    (raw := .matcher .any (.var 4)) (expected := .var 2) rfl
    (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide))))

theorem nestedCapLetFirstApp_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("f", dmIdScheme)]
      (.app (.var "f") .something) (.var 3) ⟨0, 5⟩ nestedCapLetCheck1 := by
  exact DDSynth.app (q₁ := ⟨0, 2⟩) (S₁ := Subst.id)
    (S₂ := nestedCapLetAlign1)
    (functionTarget := .fn (.var 1) (.var 1))
    nestedCapLetFirstFunction_ddSynth
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    nestedCapLetFirstArgument_ddCheck

theorem nestedCapLetFirstApp_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetFirstApp_ddSynth [] [] := by
  exact .app nestedCapLetFirstFunction_ddSynthOrigin
    (.ordinary (S := Subst.id) (left := .fn (.var 1) (.var 1))
      (right := .fn (.var 2) (.var 3)) rfl
      (originSafePairedCapId []
        (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide)
          (by decide)))) nestedCapLetFirstArgument_ddCheckOrigin

/-- The second use: its own fresh instance `fn ?6 ?7` whose domain receives
the raw product of matcher producers unlifted — a variable expectation is
no slot demand. -/
def nestedCapLetSecondFunction_ddSynth :
    DDSynth emptySignature ⟨0, 5⟩ nestedCapLetCheck1 [("f", dmIdScheme)]
      (.var "f") (.fn (.var 5) (.var 5)) ⟨0, 6⟩ nestedCapLetCheck1 := by
  simpa only [dmIdScheme_instance_value, dmIdScheme_instance_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 5⟩)
      (S := nestedCapLetCheck1) (Γ := [("f", dmIdScheme)])
      (name := "f") (scheme := dmIdScheme) (by
        simp [Context.applySubst, Context.find?]))

theorem nestedCapLetSecondFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetSecondFunction_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst nestedCapLetCheck1
      [("f", dmIdScheme)]).find? "f" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  rw [← dmIdScheme_instance_value ⟨0, 5⟩,
    ← dmIdScheme_instance_supply ⟨0, 5⟩]
  refine ⟨DDSynth.var (signature := emptySignature) lookup, ?_⟩
  simpa [DDLedger.markSchemeInstance, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.var (ledger := []) lookup)

theorem nestedCapLetSecondTuple_ddSynth :
    DDSynth emptySignature ⟨0, 8⟩ nestedCapLetAlign2 [("f", dmIdScheme)]
      (.tuple [.something, .something])
      (.prod [.matcher .any (.var 8), .matcher .any (.var 9)])
      ⟨0, 10⟩ nestedCapLetAlign2 :=
  .tuple (.cons .something (.cons .something .nil))

theorem nestedCapLetSecondTuple_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetSecondTuple_ddSynth [] [] :=
  .tuple (.cons .something (.cons .something .nil))

theorem nestedCapLetSecondArgument_ddCheck :
    DDCheck emptySignature ⟨0, 8⟩ nestedCapLetAlign2 [("f", dmIdScheme)]
      (.tuple [.something, .something]) (.var 6) ⟨0, 10⟩
      nestedCapLetTerminal := by
  exact .mk nestedCapLetSecondTuple_ddSynth
    (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight
        (.prod [.matcher .any (.var 8), .matcher .any (.var 9)]) 6
        (by decide))))

theorem nestedCapLetSecondArgument_ddCheckOrigin :
    DDCheckOrigin emptySignature nestedCapLetSecondArgument_ddCheck [] [] := by
  exact .mk nestedCapLetSecondTuple_ddSynthOrigin
    (.ordinary (S := nestedCapLetAlign2)
      (raw := .prod [.matcher .any (.var 8), .matcher .any (.var 9)])
      (expected := .var 6) rfl
      (.ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.varRight
          (.prod [.matcher .any (.var 8), .matcher .any (.var 9)]) 6
          (by decide)))))

theorem nestedCapLetSecondApp_ddSynth :
    DDSynth emptySignature ⟨0, 5⟩ nestedCapLetCheck1 [("f", dmIdScheme)]
      (.app (.var "f") (.tuple [.something, .something])) (.var 7) ⟨0, 10⟩
      nestedCapLetTerminal := by
  exact DDSynth.app (q₁ := ⟨0, 6⟩) (S₁ := nestedCapLetCheck1)
    (S₂ := nestedCapLetAlign2)
    (functionTarget := .fn (.var 5) (.var 5))
    nestedCapLetSecondFunction_ddSynth
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 5 6 7 (by decide) (by decide) (by decide)))
    nestedCapLetSecondArgument_ddCheck

theorem nestedCapLetSecondApp_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetSecondApp_ddSynth [] [] := by
  exact .app nestedCapLetSecondFunction_ddSynthOrigin
    (.ordinary (S := nestedCapLetCheck1)
      (left := .fn (.var 5) (.var 5))
      (right := .fn (.var 6) (.var 7)) rfl
      (originSafePairedCapId []
        (ExactPairedMGU.fnDiagonal 5 6 7 (by decide) (by decide)
          (by decide)))) nestedCapLetSecondArgument_ddCheckOrigin

def nestedCapLetValue_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] (.lam "m" (.var "m"))
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
  apply DDSynth.lam
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("m", Scheme.mono (.var 0))]) (name := "m")
      (scheme := Scheme.mono (.var 0)) (by
        simp [Context.applySubst, Context.find?]))

theorem nestedCapLetValue_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetValue_ddSynth [] [] := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst Subst.id
      [("m", Scheme.mono (.var 0))]).find? "m" =
      some (Scheme.mono (.var 0)) := by
    simp [Context.applySubst, Context.find?]
  have bodyOrigin : DDSynthOrigin emptySignature
      (DDSynth.var (q := ⟨0, 1⟩) lookup) [] [] := by
    simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, Scheme.mono,
      Scheme.canonicalCapImages, CapabilityOriginLedger.setOrigins] using
      (DDSynthOrigin.var (signature := emptySignature) (q := ⟨0, 1⟩)
        (ledger := []) lookup)
  let raw₀ := DDSynth.lam (signature := emptySignature) (q := ⟨0, 0⟩)
    (DDSynth.var (q := ⟨0, 1⟩) lookup)
  have origin₀ : DDSynthOrigin emptySignature raw₀ [] [] :=
    DDSynthOrigin.lam (q := ⟨0, 0⟩) bodyOrigin
  have raw₀' : DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      (.lam "m" (.var "m")) (.fn (.var 0) (.var 0)) ⟨0, 1⟩
      Subst.id := by
    simpa only [raw₀, InferenceBase.instantiateScheme_mono_value,
      InferenceBase.instantiateScheme_mono_supply] using raw₀
  exact ⟨raw₀', by
    simpa only [raw₀, InferenceBase.instantiateScheme_mono_value,
      InferenceBase.instantiateScheme_mono_supply] using origin₀⟩

theorem nestedCapLetProgram_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      AcceptanceGapRegression.nestedCapLetProgram (.prod [.var 3, .var 7])
      ⟨0, 10⟩ nestedCapLetTerminal :=
  .letE nestedCapLetValue_ddSynth
    (.tuple (.cons nestedCapLetFirstApp_ddSynth
      (.cons nestedCapLetSecondApp_ddSynth .nil)))

theorem nestedCapLetProgram_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetProgram_ddSynth [] [] := by
  exact .letE nestedCapLetValue_ddSynthOrigin
    (.tuple (.cons nestedCapLetFirstApp_ddSynthOrigin
      (.cons nestedCapLetSecondApp_ddSynthOrigin .nil)))

def nestedCapLetFirstFunction_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetFirstFunction_ddSynthOrigin := by
  let lookup : (Context.applySubst Subst.id [("f", dmIdScheme)]).find? "f" =
      some dmIdScheme := by simp [Context.applySubst, Context.find?]
  let origin₀ := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 1⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      origin₀ := DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [dmIdScheme_instance_value, dmIdScheme_instance_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins] using source₀

def nestedCapLetFirstApp_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetFirstApp_ddSynthOrigin := by
  let argumentSynthOrigin := DDSynthOrigin.something
    (signature := emptySignature) (q := ⟨0, 4⟩)
    (S := nestedCapLetAlign1) (context := [("f", dmIdScheme)]) (ledger := [])
  let argumentSynthAudit : DDSynthTerminalAudit nestedCapLetTerminal
      emptySignature argumentSynthOrigin := DDSynthTerminalAudit.something
  let argumentAligned : DDAlignWithLedger [] nestedCapLetAlign1
      (.matcher .any (.var 4)) (.var 2) nestedCapLetCheck1 :=
    .ordinary rfl (.ordinary rfl (originSafePairedCapId []
      (ExactPairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    argumentSynthAudit
  let functionAligned : DDAlignTypesWithLedger [] Subst.id
      (.fn (.var 1) (.var 1)) (.fn (.var 2) (.var 3))
      nestedCapLetAlign1 := .ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        nestedCapLetFirstFunction_terminalAudit argumentAudit))

def nestedCapLetSecondFunction_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetSecondFunction_ddSynthOrigin := by
  let lookup : (Context.applySubst nestedCapLetCheck1
      [("f", dmIdScheme)]).find? "f" = some dmIdScheme := by
    simp [Context.applySubst, Context.find?]
  let origin₀ := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 5⟩) (ledger := []) lookup
  let audit₀ : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      origin₀ := DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [dmIdScheme_instance_value, dmIdScheme_instance_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins] using source₀

def nestedCapLetSecondTuple_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetSecondTuple_ddSynthOrigin := by
  let firstOrigin := DDSynthOrigin.something (signature := emptySignature)
    (q := ⟨0, 8⟩) (S := nestedCapLetAlign2)
    (context := [("f", dmIdScheme)]) (ledger := [])
  let firstAudit : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      firstOrigin := DDSynthTerminalAudit.something
  let secondOrigin := DDSynthOrigin.something (signature := emptySignature)
    (q := ⟨0, 9⟩) (S := nestedCapLetAlign2)
    (context := [("f", dmIdScheme)]) (ledger := [])
  let secondAudit : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      secondOrigin := DDSynthTerminalAudit.something
  let nilOrigin := DDSynthsOrigin.nil (signature := emptySignature)
    (q := ⟨0, 10⟩) (S := nestedCapLetAlign2)
    (context := [("f", dmIdScheme)]) (ledger := [])
  let nilAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      nilOrigin := DDSynthsTerminalAudit.nil
  let tailOrigin := DDSynthsOrigin.cons secondOrigin nilOrigin
  let tailAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      tailOrigin := DDSynthsTerminalAudit.cons secondAudit nilAudit
  let childrenOrigin := DDSynthsOrigin.cons firstOrigin tailOrigin
  let childrenAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      childrenOrigin := DDSynthsTerminalAudit.cons firstAudit tailAudit
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.tuple childrenAudit))

def nestedCapLetSecondApp_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetSecondApp_ddSynthOrigin := by
  let argumentAligned : DDAlignWithLedger [] nestedCapLetAlign2
      (.prod [.matcher .any (.var 8), .matcher .any (.var 9)]) (.var 6)
      nestedCapLetTerminal := .ordinary rfl (.ordinary rfl
        (originSafePairedCapId [] (ExactPairedMGU.varRight
          (.prod [.matcher .any (.var 8), .matcher .any (.var 9)]) 6
          (by decide))))
  let argumentAudit := DDCheckTerminalAudit.mk (aligned := argumentAligned)
    nestedCapLetSecondTuple_terminalAudit
  let functionAligned : DDAlignTypesWithLedger [] nestedCapLetCheck1
      (.fn (.var 5) (.var 5)) (.fn (.var 6) (.var 7))
      nestedCapLetAlign2 := .ordinary rfl (originSafePairedCapId []
        (ExactPairedMGU.fnDiagonal 5 6 7 (by decide) (by decide) (by decide)))
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.app (aligned := functionAligned)
        nestedCapLetSecondFunction_terminalAudit argumentAudit))

def nestedCapLetValue_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetValue_ddSynthOrigin := by
  let lookup : (Context.applySubst Subst.id
      [("m", Scheme.mono (.var 0))]).find? "m" =
      some (Scheme.mono (.var 0)) := by
    simp [Context.applySubst, Context.find?]
  let bodyOrigin := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨0, 1⟩) (ledger := []) lookup
  let bodyAudit : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      bodyOrigin := DDSynthTerminalAudit.var (lookup := lookup)
  let origin₀ := DDSynthOrigin.lam (q := ⟨0, 0⟩) bodyOrigin
  let audit₀ : DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      origin₀ := DDSynthTerminalAudit.lam bodyAudit
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, bodyAudit, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
    Scheme.FreshOpening.capImages, Scheme.mono] using source₀

def nestedCapLetProgram_terminalAudit :
    DDSynthTerminalAudit nestedCapLetTerminal emptySignature
      nestedCapLetProgram_ddSynthOrigin := by
  let nilOrigin := DDSynthsOrigin.nil (signature := emptySignature)
    (q := ⟨0, 10⟩) (S := nestedCapLetTerminal)
    (context := [("f", dmIdScheme)])
    (ledger := [])
  let nilAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      nilOrigin := DDSynthsTerminalAudit.nil
  let tailOrigin := DDSynthsOrigin.cons
    nestedCapLetSecondApp_ddSynthOrigin nilOrigin
  let tailAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      tailOrigin := DDSynthsTerminalAudit.cons
        nestedCapLetSecondApp_terminalAudit nilAudit
  let childrenOrigin := DDSynthsOrigin.cons
    nestedCapLetFirstApp_ddSynthOrigin tailOrigin
  let childrenAudit : DDSynthsTerminalAudit nestedCapLetTerminal emptySignature
      childrenOrigin := DDSynthsTerminalAudit.cons
        nestedCapLetFirstApp_terminalAudit tailAudit
  let bodyAudit := DDSynthTerminalAudit.tuple childrenAudit
  let stable :
      (emptySignature.generalize
        (Context.applySubst Subst.id ([] : Context))
        (Subst.id.apply (.fn (.var 0) (.var 0)))).applyMeta
          nestedCapLetTerminal =
      emptySignature.generalize
        (Context.applySubst nestedCapLetTerminal ([] : Context))
        (nestedCapLetTerminal.apply (.fn (.var 0) (.var 0))) := by
    native_decide
  let facts : DDTerminalAudit.LetFacts nestedCapLetTerminal emptySignature []
      (.fn (.var 0) (.var 0)) Subst.id := ⟨by simpa using stable⟩
  exact DDSynthTerminalAudit.transportBuilt
    (DDSynthTerminalAudit.BuiltAudit.of
      (DDSynthTerminalAudit.letE
        nestedCapLetValue_terminalAudit bodyAudit facts))

/-- The `let`-polymorphic pairing of the two producers closes in the
demand-directed judgment at exactly the executable raw result shape. -/
theorem nestedCapLetProgram_ddTyping :
    DDTyping emptySignature [] AcceptanceGapRegression.nestedCapLetProgram
      (.prod [.matcher .any (.var 4),
        .prod [.matcher .any (.var 8), .matcher .any (.var 9)]]) := by
  exact ⟨.prod [.var 3, .var 7], ⟨0, 10⟩, nestedCapLetTerminal,
    nestedCapLetProgram_ddSynth, [], nestedCapLetProgram_ddSynthOrigin,
    nestedCapLetProgram_terminalAudit, rfl⟩

/-! ## The nested-capability boundary: no demand-directed derivation exists

`nestedCapProgram` shares one monomorphic consumer between a bare matcher
producer and a product of matcher producers.  Its state-free runtime
certificates can insert coercions at argument positions with no slot demand
(`AcceptanceGapRegression.nestedCapProgram_typed`), and the executable
pipeline rejects it.  The inversion below fixes the boundary at the level
of the judgment itself: no demand-directed derivation exists, for any
published type and any choice of most general solve deltas.  The forced
chain is delta-independent.  The first function alignment can map the
fresh domain only to a variable (`varConstraint_target_image_var`), so the
first argument check is an ordinary alignment that pins the shared domain
to a matcher head; the second use then meets a matcher-headed — not
slot-headed — expectation, where every coercion branch of `DDAlign` is
unavailable and ordinary alignment fails on the `prod`/`matcher`
constructor clash. -/

theorem nestedCapProgram_no_ddTyping (target : Ty) :
    ¬ DDTyping emptySignature []
      AcceptanceGapRegression.nestedCapProgram target := by
  rintro ⟨raw, q', S', synth, -⟩
  cases synth with
  | app functionSynth outerAlign outerCheck =>
  cases functionSynth with
  | lam bodySynth =>
  cases bodySynth with
  | tuple componentsSynth =>
  cases componentsSynth with
  | cons firstSynth restSynth =>
  cases restSynth with
  | cons secondSynth nilSynth =>
  -- First application: pin the lookup and force the fresh-domain alignment.
  cases firstSynth with
  | app fSynth firstAlign firstCheck =>
  cases fSynth with
  | var lookup =>
  rename_i scheme1
  have pinned1 : some scheme1 =
      some ((Scheme.mono (Ty.var 0)).applyMeta Subst.id) :=
    lookup.symm.trans rfl
  injection pinned1 with pinnedScheme1
  subst pinnedScheme1
  have initial : Inference.initialSupply emptySignature [] = ⟨0, 0⟩ := by
    native_decide
  simp only [initial, Nat.zero_add] at firstAlign
  rw [instantiateScheme_monoApplySubst_value,
    Scheme.applyMeta_mono, InferenceBase.instantiateScheme_mono_supply]
      at firstAlign
  simp only [Subst.apply_id] at firstAlign
  change DDAlignTypes Subst.id (Ty.var 0)
    (.fn (.var 1) (.var 2)) _ at firstAlign
  cases firstAlign with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hclass1 firstMGU =>
  rename_i delta1
  have firstMGU' : PairedMGU (Ty.var 0) (.fn (.var 1) (.var 2)) delta1 :=
    firstMGU.1
  obtain ⟨w, hw⟩ :=
    firstMGU'.varConstraint_target_image_var (by decide)
      (varId := 1) (by decide)
  -- First argument check: only ordinary alignment fits a variable
  -- expectation, and it pins the domain to a matcher head.
  cases firstCheck with
  | mk somethingSynth firstArgAlign =>
  cases somethingSynth with
  | something =>
  cases firstArgAlign with
  | productMatcherLift _ hslot _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hslot)
  | slotTupleLift _ _ hslot _ _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hslot)
  | matcherToSlot _ hslot _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hslot)
  | slotToSlot hraw _ _ _ => nomatch hraw
  | ordinary hclassA firstArgAligned =>
  cases firstArgAligned with
  | matcherPair _ hright _ _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hright)
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hpairA firstArgMGU =>
  rename_i delta3
  have factC :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 1) =
        .matcher .any
          ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
            (Ty.var 3)) :=
    firstArgMGU.1.1.symm
  have factA :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 0) =
        .fn ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 1))
          ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
            (Ty.var 2)) :=
    congrArg (Subst.apply delta3) firstMGU'.1
  have domainResolved :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 0) =
        .fn (.matcher .any
            ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
              (Ty.var 3)))
          ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
            (Ty.var 2)) := by
    rw [factA, factC]
  -- Second application: the consumer's resolved type now has a
  -- matcher-headed domain.
  cases secondSynth with
  | app fSynth2 secondAlign secondCheck =>
  cases fSynth2 with
  | var lookup2 =>
  rename_i scheme2
  have pinned2 : some scheme2 =
      some ((Scheme.mono (Ty.var 0)).applyMeta
        (Subst.seq delta3 (Subst.seq delta1 Subst.id))) :=
    lookup2.symm.trans rfl
  injection pinned2 with pinnedScheme2
  subst pinnedScheme2
  rw [instantiateScheme_monoApplySubst_value] at secondAlign
  rw [domainResolved] at secondAlign
  cases secondAlign with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hclassB secondMGU =>
  rename_i delta4
  have components := secondMGU.1.1
  injection components with hdom hcod
  -- `hdom` pins the resolved shared domain to a matcher head, for every
  -- delta choice.  The second argument check: the raw product of matchers
  -- meets that matcher-headed expectation and every branch fails.
  cases secondCheck with
  | mk tupleSynth secondArgAlign =>
  cases tupleSynth with
  | tuple pairSynth =>
  cases pairSynth with
  | cons s1 rest1 =>
  cases s1 with
  | something =>
  cases rest1 with
  | cons s2 rest2 =>
  cases s2 with
  | something =>
  cases rest2 with
  | nil =>
  cases secondArgAlign with
  | productMatcherLift _ hslot _ => nomatch hdom.trans hslot
  | slotTupleLift _ _ hslot _ _ => nomatch hdom.trans hslot
  | matcherToSlot hraw _ _ => nomatch hraw
  | slotToSlot hraw _ _ _ => nomatch hraw
  | ordinary hclassC secondArgAligned =>
  cases secondArgAligned with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hpairC secondArgMGU =>
  rename_i delta5
  nomatch secondArgMGU.1.1.trans (congrArg (Subst.apply delta5) hdom.symm)

/-- The swapped order has no demand-directed derivation either, for any
published type and any choice of most general solve deltas.  The forced
chain is the mirror image: the first argument is now the product of
matcher producers, whose only available alignment against the
variable-headed domain expectation is ordinary, pinning the shared domain
to a *product* head; the second use then feeds the bare `something` — a
matcher-headed raw — into that product-headed expectation, where every
coercion branch of `DDAlign` is unavailable and ordinary alignment fails
on the `matcher`/`prod` constructor clash. -/
theorem nestedCapSwappedProgram_no_ddTyping (target : Ty) :
    ¬ DDTyping emptySignature []
      AcceptanceGapRegression.nestedCapSwappedProgram target := by
  rintro ⟨raw, q', S', synth, -⟩
  cases synth with
  | app functionSynth outerAlign outerCheck =>
  cases functionSynth with
  | lam bodySynth =>
  cases bodySynth with
  | tuple componentsSynth =>
  cases componentsSynth with
  | cons firstSynth restSynth =>
  cases restSynth with
  | cons secondSynth nilSynth =>
  -- First application: pin the lookup and force the fresh-domain alignment.
  cases firstSynth with
  | app fSynth firstAlign firstCheck =>
  cases fSynth with
  | var lookup =>
  rename_i scheme1
  have pinned1 : some scheme1 =
      some ((Scheme.mono (Ty.var 0)).applyMeta Subst.id) :=
    lookup.symm.trans rfl
  injection pinned1 with pinnedScheme1
  subst pinnedScheme1
  have initial : Inference.initialSupply emptySignature [] = ⟨0, 0⟩ := by
    native_decide
  simp only [initial, Nat.zero_add] at firstAlign
  rw [instantiateScheme_monoApplySubst_value,
    Scheme.applyMeta_mono, InferenceBase.instantiateScheme_mono_supply]
      at firstAlign
  simp only [Subst.apply_id] at firstAlign
  change DDAlignTypes Subst.id (Ty.var 0)
    (.fn (.var 1) (.var 2)) _ at firstAlign
  cases firstAlign with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hclass1 firstMGU =>
  rename_i delta1
  have firstMGU' : PairedMGU (Ty.var 0) (.fn (.var 1) (.var 2)) delta1 :=
    firstMGU.1
  obtain ⟨w, hw⟩ :=
    firstMGU'.varConstraint_target_image_var (by decide)
      (varId := 1) (by decide)
  -- First argument check: the raw product of matchers meets a variable
  -- expectation, so only ordinary alignment fits, and it pins the shared
  -- domain to a product head.
  cases firstCheck with
  | mk tupleSynth firstArgAlign =>
  cases tupleSynth with
  | tuple pairSynth =>
  cases pairSynth with
  | cons s1 rest1 =>
  cases s1 with
  | something =>
  cases rest1 with
  | cons s2 rest2 =>
  cases s2 with
  | something =>
  cases rest2 with
  | nil =>
  cases firstArgAlign with
  | productMatcherLift _ hslot _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hslot)
  | slotTupleLift _ _ hslot _ _ =>
      nomatch hw.symm.trans (show delta1.target 1 = _ from hslot)
  | matcherToSlot hraw _ _ => nomatch hraw
  | slotToSlot hraw _ _ _ => nomatch hraw
  | ordinary hclassA firstArgAligned =>
  cases firstArgAligned with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hpairA firstArgMGU =>
  rename_i delta3
  have factC :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 1) =
        .prod [.matcher .any
            ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
              (Ty.var 3)),
          .matcher .any
            ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
              (Ty.var 4))] :=
    firstArgMGU.1.1.symm
  have factA :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 0) =
        .fn ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 1))
          ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
            (Ty.var 2)) :=
    congrArg (Subst.apply delta3) firstMGU'.1
  have domainResolved :
      (Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply (Ty.var 0) =
        .fn (.prod [.matcher .any
              ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
                (Ty.var 3)),
            .matcher .any
              ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
                (Ty.var 4))])
          ((Subst.seq delta3 (Subst.seq delta1 Subst.id)).apply
            (Ty.var 2)) := by
    rw [factA, factC]
  -- Second application: the consumer's resolved type now has a
  -- product-headed domain.
  cases secondSynth with
  | app fSynth2 secondAlign secondCheck =>
  cases fSynth2 with
  | var lookup2 =>
  rename_i scheme2
  have pinned2 : some scheme2 =
      some ((Scheme.mono (Ty.var 0)).applyMeta
        (Subst.seq delta3 (Subst.seq delta1 Subst.id))) :=
    lookup2.symm.trans rfl
  injection pinned2 with pinnedScheme2
  subst pinnedScheme2
  rw [instantiateScheme_monoApplySubst_value] at secondAlign
  rw [domainResolved] at secondAlign
  cases secondAlign with
  | matcherPair hleft _ _ _ => nomatch hleft
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hclassB secondMGU =>
  rename_i delta4
  have components := secondMGU.1.1
  injection components with hdom hcod
  -- `hdom` pins the resolved shared domain to a product head, for every
  -- delta choice.  The second argument check: the bare matcher raw meets
  -- that product-headed expectation and every branch fails.
  cases secondCheck with
  | mk somethingSynth secondArgAlign =>
  cases somethingSynth with
  | something =>
  cases secondArgAlign with
  | productMatcherLift _ hslot _ => nomatch hdom.trans hslot
  | slotTupleLift _ _ hslot _ _ => nomatch hdom.trans hslot
  | matcherToSlot _ hslot _ => nomatch hdom.trans hslot
  | slotToSlot hraw _ _ _ => nomatch hraw
  | ordinary hclassC secondArgAligned =>
  cases secondArgAligned with
  | matcherPair _ hright _ _ => nomatch hdom.trans hright
  | slotPair hleft _ _ _ => nomatch hleft
  | ordinary hpairC secondArgMGU =>
  rename_i delta5
  nomatch secondArgMGU.1.1.trans (congrArg (Subst.apply delta5) hdom.symm)

/-! ## Boundary: in-constraint swaps force the solved-form clause

Support and range confinement remove renamings of variables outside a solve
delta's constraint, but not within it.  On the trivially satisfied
constraint `fn ?0 ?1 ≐ fn ?0 ?1` the involutive swap of `?0` and `?1` is
sound, most general (every unifier factors by un-swapping), and both
supported and ranged within the constraint — yet applying it twice undoes
it.  Such a delta breaks prevailing-substitution absorption
(`Subst.seq_absorbs_of_idempotent` needs idempotency): a mid-derivation
view of an already-threaded type disagrees with the terminal view, so
context types would not transport to the terminal `RuntimeTyping` statement
of the state-erasure map.  The solved-form clause is the exactness
condition that rejects exactly this residue. -/

/-- The involutive swap of `?0` and `?1`. -/
def inConstraintSwap : Subst :=
  ⟨CapSubst.id, fun candidate =>
    if candidate = 0 then .var 1
    else if candidate = 1 then .var 0
    else .var candidate⟩

/-- The trivially satisfied constraint side. -/
def swapConstraint : Ty := .fn (.var 0) (.var 1)

/-- The swap is a genuine most general paired solution of the trivial
constraint: every unifier factors through it by un-swapping. -/
theorem inConstraintSwap_pairedMGU :
    PairedMGU swapConstraint swapConstraint inConstraintSwap := by
  constructor
  · rfl
  · intro U _
    refine ⟨⟨U.cap, fun candidate =>
      if candidate = 0 then U.target 1
      else if candidate = 1 then U.target 0
      else U.target candidate⟩, ?_⟩
    have targetEq : U.target = fun candidate =>
        Subst.apply
          ⟨U.cap, fun candidate =>
            if candidate = 0 then U.target 1
            else if candidate = 1 then U.target 0
            else U.target candidate⟩
          (inConstraintSwap.target candidate) := by
      funext candidate
      by_cases hzero : candidate = 0
      · subst hzero
        simp [inConstraintSwap, Subst.apply, Ty.applyCapability,
          Ty.applyTarget]
      · by_cases hone : candidate = 1
        · subst hone
          simp [inConstraintSwap, Subst.apply, Ty.applyCapability,
            Ty.applyTarget]
        · simp [inConstraintSwap, hzero, hone, Subst.apply,
            Ty.applyCapability, Ty.applyTarget]
    exact congrArg (Subst.mk U.cap) targetEq

/-- The swap's target action is supported within the constraint. -/
theorem inConstraintSwap_supportWithin :
    inConstraintSwap.target.SupportWithin
      (swapConstraint.ftv ++ swapConstraint.ftv) := by
  intro candidate outside
  have hzero : ¬ candidate = 0 := fun h => outside (by
    cases h
    simp [swapConstraint, Ty.ftv])
  have hone : ¬ candidate = 1 := fun h => outside (by
    cases h
    simp [swapConstraint, Ty.ftv])
  simp [inConstraintSwap, hzero, hone]

/-- The swap's target images stay within the constraint. -/
theorem inConstraintSwap_rangeWithin :
    inConstraintSwap.target.RangeWithin
      (swapConstraint.ftv ++ swapConstraint.ftv) := by
  intro candidate mem image imageMem
  by_cases hzero : candidate = 0
  · subst hzero
    have h : image = 1 := by
      simpa [inConstraintSwap, Ty.ftv] using imageMem
    subst h
    simp [swapConstraint, Ty.ftv]
  · by_cases hone : candidate = 1
    · subst hone
      have h : image = 0 := by
        simpa [inConstraintSwap, Ty.ftv] using imageMem
      subst h
      simp [swapConstraint, Ty.ftv]
    · have h : image = candidate := by
        simpa [inConstraintSwap, hzero, hone, Ty.ftv] using imageMem
      simpa [h] using mem

/-- The swap's images carry no capability variables. -/
theorem inConstraintSwap_capRangeWithin :
    inConstraintSwap.target.CapRangeWithin
      (swapConstraint.ftv ++ swapConstraint.ftv)
      (swapConstraint.fcv ++ swapConstraint.fcv) := by
  intro candidate _ image imageMem
  by_cases hzero : candidate = 0
  · subst hzero
    nomatch imageMem
  · by_cases hone : candidate = 1
    · subst hone
      nomatch imageMem
    · rw [show inConstraintSwap.target candidate = .var candidate from by
        simp [inConstraintSwap, hzero, hone]] at imageMem
      nomatch imageMem

/-- Applying the swap twice undoes it: it is not in solved form. -/
theorem inConstraintSwap_not_idempotent :
    ¬ Subst.Idempotent inConstraintSwap := by
  intro idem
  nomatch idem (.var 0)

/-- Concrete absorption failure: with the identity continuation, the
composite substitution disagrees on the prevailing view of `?0`. -/
theorem inConstraintSwap_breaks_absorption :
    (Subst.seq Subst.id inConstraintSwap).apply
        (inConstraintSwap.apply (.var 0)) ≠
      (Subst.seq Subst.id inConstraintSwap).apply (.var 0) := by
  intro h
  nomatch h

/-- The strengthened exactness rejects the swap. -/
theorem inConstraintSwap_exact_refuted :
    ¬ ExactPairedMGU swapConstraint swapConstraint inConstraintSwap :=
  fun exact => inConstraintSwap_not_idempotent exact.2.2.2.2.2.2

/-- The boundary in one statement: the in-constraint swap satisfies
soundness, most-generality, and every confinement clause of exactness, yet
is not idempotent — the solved-form clause is what rejects it. -/
theorem inConstraintSwap_forces_solvedForm :
    PairedMGU swapConstraint swapConstraint inConstraintSwap ∧
      inConstraintSwap.cap.SupportWithin
        (swapConstraint.fcv ++ swapConstraint.fcv) ∧
      inConstraintSwap.target.SupportWithin
        (swapConstraint.ftv ++ swapConstraint.ftv) ∧
      inConstraintSwap.cap.RangeWithin
        (swapConstraint.fcv ++ swapConstraint.fcv) ∧
      inConstraintSwap.target.RangeWithin
        (swapConstraint.ftv ++ swapConstraint.ftv) ∧
      inConstraintSwap.target.CapRangeWithin
        (swapConstraint.ftv ++ swapConstraint.ftv)
        (swapConstraint.fcv ++ swapConstraint.fcv) ∧
      ¬ Subst.Idempotent inConstraintSwap ∧
      ¬ ExactPairedMGU swapConstraint swapConstraint inConstraintSwap :=
  ⟨inConstraintSwap_pairedMGU, CapSubst.id_supportWithin _,
    inConstraintSwap_supportWithin, CapSubst.id_rangeWithin _,
    inConstraintSwap_rangeWithin, inConstraintSwap_capRangeWithin,
    inConstraintSwap_not_idempotent, inConstraintSwap_exact_refuted⟩

/-! ## Pattern layer: the or-pattern `matchAll` program

The same or-pattern program whose executable acceptance is pinned by
`AcceptanceGapRegression.orProgram_accepted` carries a demand-directed
derivation: both alternatives allocate independent capability/target metas
for `x`, dual alignment unifies them, binding alignment matches the binder
by name, the match-target alignment resolves the shared binder target to
`Int`, and the `something` matcher expression meets the pattern's slot
expectation through the one-way producer-to-slot solution. -/

section OrPattern

variable (signature : FrozenSig)

/-- Prevailing substitution after the or-alternative capability alignment. -/
def orCapAlign : Subst :=
  Subst.seq ⟨Unification.CapSubst.single ⟨0⟩ (.var ⟨1⟩), TySubst.id⟩ Subst.id

/-- Prevailing substitution after the or-alternative target alignment. -/
def orDualAlign : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 1 (.var 2)⟩ orCapAlign

/-- Prevailing substitution after the or binding alignment: the binder types
are already shared, so the delta is an identity solve. -/
def orBindingsAlign : Subst := Subst.seq Subst.id orDualAlign

/-- Prevailing substitution after the match-target alignment. -/
def orTargetAlign : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 2 .int⟩ orBindingsAlign

/-- One-way capability component of the producer-to-slot solution: the
pattern's capability meta receives the `something` producer `Any`. -/
def orOneWayCap : CapSubst :=
  CapMatch.Bindings.toSubstWithin (Cap.var ⟨1⟩).fcv [(⟨1⟩, Cap.any)]

theorem orOneWayCap_eq_single :
    orOneWayCap = Unification.CapSubst.single ⟨1⟩ .any := by
  funext candidate
  by_cases same : (⟨1⟩ : CapVar) = candidate
  · subst candidate
    simp [orOneWayCap, CapMatch.Bindings.toSubstWithin,
      CapMatch.Bindings.toSubst, Unification.CapSubst.single, Cap.fcv]
  · simp [orOneWayCap, CapMatch.Bindings.toSubstWithin,
      Unification.CapSubst.single, Cap.fcv, same,
      Ne.symm same]

/-- Terminal substitution of the or-pattern program. -/
def orTerminal : Subst :=
  Subst.seq ⟨orOneWayCap, Unification.TySubst.single 3 .int⟩ orTargetAlign

def orPatternLedger₁ : CapabilityOriginLedger :=
  DDLedger.markFreshCap [] ⟨0, 1⟩

def orPatternLedger₂ : CapabilityOriginLedger :=
  DDLedger.markFreshCap orPatternLedger₁ ⟨1, 2⟩

theorem orLeft_ddPattern :
    DDPattern signature ⟨0, 1⟩ Subst.id [] [] [] (.pvar "x")
      ⟨.var ⟨0⟩, .var 1⟩ [("x", .var 1)] ⟨1, 2⟩ Subst.id :=
  .pvar (by simp [MonoCtx.names])

def orLeft_ddPatternOrigin :
    DDPatternOrigin signature (orLeft_ddPattern signature) []
      orPatternLedger₁ :=
  DDPatternOrigin.pvar (signature := signature) (q := ⟨0, 1⟩)
    (S := Subst.id) (context := []) (parameters := []) (bindings := [])
      (ledger := []) (by simp [MonoCtx.names])

theorem orRight_ddPattern :
    DDPattern signature ⟨1, 2⟩ Subst.id [] [] [] (.pvar "x")
      ⟨.var ⟨1⟩, .var 2⟩ [("x", .var 2)] ⟨2, 3⟩ Subst.id :=
  .pvar (by simp [MonoCtx.names])

def orRight_ddPatternOrigin :
    DDPatternOrigin signature (orRight_ddPattern signature) orPatternLedger₁
      orPatternLedger₂ :=
  DDPatternOrigin.pvar (signature := signature) (q := ⟨1, 2⟩)
    (S := Subst.id) (context := []) (parameters := []) (bindings := [])
      (ledger := orPatternLedger₁) (by simp [MonoCtx.names])

/-- The or pattern synthesizes the left alternative's dual: independent
fresh metas per alternative, dual alignment across the alternatives, and
positional binding alignment on the shared binder name. -/
theorem orPattern_ddPattern :
    DDPattern signature ⟨0, 1⟩ Subst.id [] [] []
      (.por (.pvar "x") (.pvar "x")) ⟨.var ⟨0⟩, .var 1⟩ [("x", .var 1)]
      ⟨2, 3⟩ orBindingsAlign := by
  refine DDPattern.por (S₃ := orDualAlign)
    (.pvar (by simp [MonoCtx.names]))
    (.pvar (by simp [MonoCtx.names])) ?_ ?_
  · exact .mk (ExactCapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide))
      (.ordinary rfl (ExactPairedMGU.varLeft 1 (.var 2) (by decide)))
  · exact .cons rfl (.ordinary rfl (ExactPairedMGU.refl (.var 2))) .nil

def orPattern_ddPatternOrigin :
    DDPatternOrigin signature (orPattern_ddPattern signature) []
      orPatternLedger₂ := by
  refine DDPatternOrigin.por (S₃ := orDualAlign)
    (orLeft_ddPatternOrigin signature) (orRight_ddPatternOrigin signature) ?_ ?_
  · exact .mk (S := Subst.id) (left := ⟨.var ⟨0⟩, .var 1⟩)
      (right := ⟨.var ⟨1⟩, .var 2⟩)
      ⟨ExactCapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide),
        PairedUnification.admissible_single_structuralFlexible
          orPatternLedger₂ ⟨0⟩ (.var ⟨1⟩) (by
            simp [orPatternLedger₂, orPatternLedger₁,
              DDLedger.markFreshCap])⟩
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.varLeft 1 (.var 2) (by decide))))
  · exact .cons (S := orDualAlign)
      (left := ("x", Ty.var 1)) (right := ("x", Ty.var 2)) rfl
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.refl (.var 2)))) .nil

/-- Raw synthesis of the or-pattern program at the initial supply. -/
theorem orProgram_ddSynth :
    DDSynth signature ⟨0, 1⟩ Subst.id []
      AcceptanceGapRegression.orProgram (Ty.listT .int) ⟨2, 4⟩ orTerminal := by
  refine DDSynth.matchAll (S₃ := orTargetAlign) (q₃ := ⟨2, 4⟩)
    (S₄ := orTerminal) .lit (orPattern_ddPattern signature) ?_ ?_ ?_
  · exact .ordinary rfl (ExactPairedMGU.varLeft 2 .int (by decide))
  · exact .mk .something (.matcherToSlot rfl rfl
      ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
        ExactTargetMGU.varLeft 3 .int (by decide)⟩)
  · simpa only [InferenceBase.instantiateScheme_mono_value,
      InferenceBase.instantiateScheme_mono_supply, MonoCtx.toContext,
      List.map, List.append_nil] using
      (DDSynth.var (signature := signature) (q := ⟨2, 4⟩)
        (S := orTerminal) (Γ := [("x", Scheme.mono (.var 1))])
        (name := "x") (scheme := Scheme.mono .int) (by native_decide))

theorem orMatcher_ddCheck :
    DDCheck signature ⟨2, 3⟩ orTargetAlign [] .something
      (.slot (.var ⟨0⟩) .int) ⟨2, 4⟩ orTerminal := by
  exact .mk .something (.matcherToSlot rfl rfl
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩)

def orMatcher_ddCheckOrigin :
    DDCheckOrigin signature (orMatcher_ddCheck signature) orPatternLedger₂
      orPatternLedger₂ := by
  refine .mk (synthesized := DDSynth.something (signature := signature)
    (q := ⟨2, 3⟩) (S := orTargetAlign) (Γ := [])) .something ?_
  exact .matcherToSlot rfl rfl ⟨
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩,
    ⟨by
      rw [orOneWayCap_eq_single]
      exact PairedUnification.admissible_single_structuralFlexible
        orPatternLedger₂ ⟨1⟩ .any (by
          simp [orPatternLedger₂, DDLedger.markFreshCap])⟩⟩

def orBody_ddSynth :
    DDSynth signature ⟨2, 4⟩ orTerminal
      [("x", Scheme.mono (.var 1))] (.var "x") .int ⟨2, 4⟩
      orTerminal := by
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := signature) (q := ⟨2, 4⟩)
      (S := orTerminal) (Γ := [("x", Scheme.mono (.var 1))])
      (name := "x") (scheme := Scheme.mono .int) (by native_decide))

def orBody_ddSynthOrigin :
    DDSynthOrigin signature (orBody_ddSynth signature) orPatternLedger₂
      orPatternLedger₂ := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst orTerminal
      [("x", Scheme.mono (.var 1))]).find?
      "x" = some (Scheme.mono .int) := by native_decide
  let raw₀ := DDSynth.var (signature := signature) (q := ⟨2, 4⟩)
    lookup
  have origin₀ : DDSynthOrigin signature raw₀ orPatternLedger₂
      orPatternLedger₂ := by
    simpa [raw₀, DDLedger.markSchemeInstance,
      CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
      Scheme.FreshOpening.capImages, Scheme.mono] using
      (DDSynthOrigin.var (signature := signature) (q := ⟨2, 4⟩)
        (ledger := orPatternLedger₂) lookup)
  have source₀ : ∃ raw, DDSynthOrigin signature raw orPatternLedger₂
      orPatternLedger₂ := ⟨raw₀, origin₀⟩
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using source₀

def orProgram_ddSynthOrigin :
    DDSynthOrigin signature (orProgram_ddSynth signature) []
      orPatternLedger₂ := by
  refine .matchAll .lit (orPattern_ddPatternOrigin signature)
    (.ordinary rfl (originSafePairedCapId orPatternLedger₂
      (ExactPairedMGU.varLeft 2 .int (by decide))))
    (orMatcher_ddCheckOrigin signature) (orBody_ddSynthOrigin signature)

def orBody_terminalAudit :
    DDSynthTerminalAudit orTerminal signature
      (orBody_ddSynthOrigin signature) := by
  let lookup : (Context.applySubst orTerminal
      [("x", Scheme.mono (.var 1))]).find? "x" =
      some (Scheme.mono .int) := by native_decide
  let origin₀ := DDSynthOrigin.var (signature := signature)
    (q := ⟨2, 4⟩) (ledger := orPatternLedger₂) lookup
  let audit₀ : DDSynthTerminalAudit orTerminal signature origin₀ :=
    DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
    Scheme.FreshOpening.capImages, Scheme.mono] using source₀

def orLeft_terminalAudit :
    DDPatternTerminalAudit orTerminal signature
      (orLeft_ddPatternOrigin signature) :=
  DDPatternTerminalAudit.pvar (freshName := by simp [MonoCtx.names])

def orRight_terminalAudit :
    DDPatternTerminalAudit orTerminal signature
      (orRight_ddPatternOrigin signature) :=
  DDPatternTerminalAudit.pvar (freshName := by simp [MonoCtx.names])

def orPattern_terminalAudit :
    DDPatternTerminalAudit orTerminal signature
      (orPattern_ddPatternOrigin signature) := by
  let dualsAligned : DDAlignDualWithLedger orPatternLedger₂ Subst.id
      ⟨.var ⟨0⟩, .var 1⟩ ⟨.var ⟨1⟩, .var 2⟩ orDualAlign :=
    .mk
      ⟨ExactCapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide),
        PairedUnification.admissible_single_structuralFlexible
          orPatternLedger₂ ⟨0⟩ (.var ⟨1⟩) (by
            simp [orPatternLedger₂, orPatternLedger₁,
              DDLedger.markFreshCap])⟩
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.varLeft 1 (.var 2) (by decide))))
  let bindingsAligned : DDAlignBindingsWithLedger orPatternLedger₂ orDualAlign
      [("x", .var 1)] [("x", .var 2)] orBindingsAlign :=
    .cons rfl
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.refl (.var 2)))) .nil
  exact DDPatternTerminalAudit.por (dualsAligned := dualsAligned)
    (bindingsAligned := bindingsAligned) (orLeft_terminalAudit signature)
    (orRight_terminalAudit signature)

def orMatcher_terminalAudit :
    DDCheckTerminalAudit orTerminal signature
      (orMatcher_ddCheckOrigin signature) := by
  let aligned : DDAlignWithLedger orPatternLedger₂ orTargetAlign
      (.matcher .any (.var 3)) (.slot (.var ⟨0⟩) .int) orTerminal :=
    .matcherToSlot rfl rfl ⟨
      ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
        ExactTargetMGU.varLeft 3 .int (by decide)⟩,
      ⟨by
        rw [orOneWayCap_eq_single]
        exact PairedUnification.admissible_single_structuralFlexible
          orPatternLedger₂ ⟨1⟩ .any (by
            simp [orPatternLedger₂, DDLedger.markFreshCap])⟩⟩
  exact DDCheckTerminalAudit.mk (aligned := aligned)
    DDSynthTerminalAudit.something

def orProgram_terminalAudit :
    DDSynthTerminalAudit orTerminal signature
      (orProgram_ddSynthOrigin signature) := by
  let targetAligned : DDAlignTypesWithLedger orPatternLedger₂ orBindingsAlign
      (.var 1) .int orTargetAlign :=
    .ordinary rfl (originSafePairedCapId orPatternLedger₂
      (ExactPairedMGU.varLeft 2 .int (by decide)))
  exact .matchAll (targetAligned := targetAligned) .lit
    (orPattern_terminalAudit signature) (orMatcher_terminalAudit signature)
    (orBody_terminalAudit signature)

/-- The or-pattern program closes at `List Int` in the demand-directed
judgment, mirroring its executable acceptance. -/
theorem orProgram_ddTyping :
    Inference.initialSupply signature [] = ⟨0, 1⟩ →
    DDTyping signature [] AcceptanceGapRegression.orProgram
      (Ty.listT .int) := by
  intro initial
  unfold DDTyping
  rw [initial]
  exact ⟨Ty.listT .int, ⟨2, 4⟩, orTerminal,
    orProgram_ddSynth signature, orPatternLedger₂,
    orProgram_ddSynthOrigin signature, orProgram_terminalAudit signature,
    rfl⟩

end OrPattern

/-! ## Pattern layer: a delegating matcher literal

One catch-all clause `[$ something [(v → matchAll 0 something $y y)]]`: the
primitive hole allocates a fresh hole capability against the shared matcher
target, `something` feeds the hole slot one-way, and the variable arm's body
— itself a `matchAll` — aligns `List Int` with the decomposition-result type
`List ?0`, resolving the shared target to `Int`.  Finalization consumes the
same executable coverage checks as the executable traversal, and the literal
closes at `Matcher Any Int`. -/

/-- The inner arm body `matchAll 0 something $y y`. -/
def delegatingBody : Expr :=
  .matchAll (.lit 0) .something (.pvar "y") (.var "y")

/-- The delegating matcher literal. -/
def delegatingMatcher : Expr :=
  .matcher [.mk .hole .something [.mk (.var "v") delegatingBody]]

/-- One-way capability component feeding the hole slot from `something`. -/
def delegatingHoleCap : CapSubst :=
  CapMatch.Bindings.toSubstWithin (Cap.var ⟨0⟩).fcv [(⟨0⟩, Cap.any)]

theorem delegatingHoleCap_eq_single :
    delegatingHoleCap = Unification.CapSubst.single ⟨0⟩ .any := by
  funext candidate
  by_cases same : (⟨0⟩ : CapVar) = candidate
  · subst candidate
    simp [delegatingHoleCap, CapMatch.Bindings.toSubstWithin,
      CapMatch.Bindings.toSubst, Unification.CapSubst.single, Cap.fcv]
  · simp [delegatingHoleCap, CapMatch.Bindings.toSubstWithin,
      Unification.CapSubst.single, Cap.fcv, same,
      Ne.symm same]

/-- Prevailing substitution after the next-matcher slot check. -/
def delegatingCheck1 : Subst :=
  Subst.seq ⟨delegatingHoleCap, Unification.TySubst.single 1 (.var 0)⟩
    Subst.id

/-- Prevailing substitution after the inner match-target alignment. -/
def delegatingInner1 : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 2 .int⟩ delegatingCheck1

/-- One-way capability component of the inner `something` check. -/
def delegatingInnerCap : CapSubst :=
  CapMatch.Bindings.toSubstWithin (Cap.var ⟨1⟩).fcv [(⟨1⟩, Cap.any)]

theorem delegatingInnerCap_eq_single :
    delegatingInnerCap = Unification.CapSubst.single ⟨1⟩ .any := by
  funext candidate
  by_cases same : (⟨1⟩ : CapVar) = candidate
  · subst candidate
    simp [delegatingInnerCap, CapMatch.Bindings.toSubstWithin,
      CapMatch.Bindings.toSubst, Unification.CapSubst.single, Cap.fcv]
  · simp [delegatingInnerCap, CapMatch.Bindings.toSubstWithin,
      Unification.CapSubst.single, Cap.fcv, same,
      Ne.symm same]

/-- Prevailing substitution after the inner slot check. -/
def delegatingInner2 : Subst :=
  Subst.seq ⟨delegatingInnerCap, Unification.TySubst.single 3 .int⟩
    delegatingInner1

/-- Terminal substitution of the delegating matcher: the arm-body alignment
resolves the shared matcher target to `Int`. -/
def delegatingTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 0 .int⟩ delegatingInner2

def delegatingLedger₀ : CapabilityOriginLedger :=
  DDLedger.markFreshCap [] ⟨0, 1⟩

def delegatingLedger₁ : CapabilityOriginLedger :=
  DDLedger.markFreshCap delegatingLedger₀ ⟨1, 2⟩

/-- Most general paired solution of the arm-body alignment
`List Int ≐ List ?0`. -/
theorem delegating_bodyMGU :
    PairedMGU (Ty.listT .int) (Ty.listT (.var 0))
      ⟨CapSubst.id, Unification.TySubst.single 0 .int⟩ := by
  constructor
  · rfl
  · intro U unifies
    have components :
        Ty.data "List" [Ty.int] =
          Ty.data "List" [((Ty.var 0).applyCapability U.cap).applyTarget
            U.target] := unifies
    have listEq :
        [Ty.int] = [((Ty.var 0).applyCapability U.cap).applyTarget
          U.target] := by
      injection components
    have headEq : Ty.int =
        ((Ty.var 0).applyCapability U.cap).applyTarget U.target := by
      injection listEq
    have targetEq : U.target = fun candidate =>
        U.apply (Unification.TySubst.single 0 .int candidate) := by
      funext candidate
      by_cases hcase : (0 : TypePM.TyVar) = candidate
      · cases hcase
        simp only [Unification.TySubst.single]
        exact headEq.symm
      · simp only [Unification.TySubst.single, if_neg hcase]
        rfl
    exact ⟨U, congrArg (Subst.mk U.cap) targetEq⟩

/-- The arm-body solution is exact. -/
theorem delegating_bodyMGU_exact :
    ExactPairedMGU (Ty.listT .int) (Ty.listT (.var 0))
      ⟨CapSubst.id, Unification.TySubst.single 0 .int⟩ := by
  refine ⟨delegating_bodyMGU, CapSubst.id_supportWithin _, ?_,
    CapSubst.id_rangeWithin _,
    tySingle_rangeWithin (fun image mem => nomatch mem),
    tySingle_capRangeWithin (fun image mem => nomatch mem),
    Subst.idempotent_of_capId
      (Unification.tySingle_idempotent (by decide))⟩
  intro candidate outside
  have hne : ¬ (0 : TypePM.TyVar) = candidate := fun h => outside (by
    cases h
    simp [Ty.listT, Ty.ftv, Ty.ftvList])
  simp [Unification.TySubst.single, hne]

/-- The next-matcher check: `something` delivers the hole slot one-way. -/
theorem delegatingNextHead_ddCheck :
    DDCheck emptySignature ⟨1, 1⟩ Subst.id [] .something
      (.slot (.var ⟨0⟩) (.var 0)) ⟨1, 2⟩ delegatingCheck1 := by
  exact .mk .something (.matcherToSlot rfl rfl
    ⟨[(⟨0⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 1 (.var 0) (by decide)⟩)

def delegatingNextHead_ddCheckOrigin :
    DDCheckOrigin emptySignature delegatingNextHead_ddCheck delegatingLedger₀
      delegatingLedger₀ := by
  refine .mk (synthesized := DDSynth.something (signature := emptySignature)
    (q := ⟨1, 1⟩) (S := Subst.id) (Γ := [])) .something ?_
  exact .matcherToSlot rfl rfl ⟨
    ⟨[(⟨0⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 1 (.var 0) (by decide)⟩,
    ⟨by
      rw [delegatingHoleCap_eq_single]
      exact PairedUnification.admissible_single_structuralFlexible
        delegatingLedger₀ ⟨0⟩ .any (by
          simp [delegatingLedger₀, DDLedger.markFreshCap])⟩⟩

theorem delegatingNext_ddChecks :
    DDChecks emptySignature ⟨1, 1⟩ Subst.id [] [.something]
      [.slot (.var ⟨0⟩) (.var 0)] ⟨1, 2⟩ delegatingCheck1 := by
  exact .cons delegatingNextHead_ddCheck .nil

def delegatingNext_ddChecksOrigin :
    DDChecksOrigin emptySignature delegatingNext_ddChecks delegatingLedger₀
      delegatingLedger₀ := by
  exact .cons delegatingNextHead_ddCheckOrigin .nil

theorem delegatingInnerPattern_ddPattern :
    DDPattern emptySignature ⟨1, 2⟩ delegatingCheck1
      [("v", Scheme.mono (.var 0))] [] [] (.pvar "y")
      ⟨.var ⟨1⟩, .var 2⟩ [("y", .var 2)] ⟨2, 3⟩
      delegatingCheck1 :=
  .pvar (by simp [MonoCtx.names])

def delegatingInnerPattern_ddPatternOrigin :
    DDPatternOrigin emptySignature delegatingInnerPattern_ddPattern
      delegatingLedger₀ delegatingLedger₁ :=
  DDPatternOrigin.pvar (signature := emptySignature) (q := ⟨1, 2⟩)
    (S := delegatingCheck1)
    (context := [("v", Scheme.mono (.var 0))]) (parameters := [])
    (bindings := []) (ledger := delegatingLedger₀)
      (by simp [MonoCtx.names])

theorem delegatingInnerMatcher_ddCheck :
    DDCheck emptySignature ⟨2, 3⟩ delegatingInner1
      [("v", Scheme.mono (.var 0))] .something
      (.slot (.var ⟨1⟩) .int) ⟨2, 4⟩ delegatingInner2 := by
  exact .mk .something (.matcherToSlot rfl rfl
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩)

def delegatingInnerMatcher_ddCheckOrigin :
    DDCheckOrigin emptySignature delegatingInnerMatcher_ddCheck
      delegatingLedger₁ delegatingLedger₁ := by
  refine .mk (synthesized := DDSynth.something (signature := emptySignature)
    (q := ⟨2, 3⟩) (S := delegatingInner1)
    (Γ := [("v", Scheme.mono (.var 0))])) .something ?_
  exact .matcherToSlot rfl rfl ⟨
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩,
    ⟨by
      rw [delegatingInnerCap_eq_single]
      exact PairedUnification.admissible_single_structuralFlexible
        delegatingLedger₁ ⟨1⟩ .any (by
          simp [delegatingLedger₁, DDLedger.markFreshCap])⟩⟩

def delegatingInnerBodyVar_ddSynth :
    DDSynth emptySignature ⟨2, 4⟩ delegatingInner2
      [("y", Scheme.mono (.var 2)), ("v", Scheme.mono (.var 0))]
      (.var "y") .int ⟨2, 4⟩ delegatingInner2 := by
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨2, 4⟩)
      (S := delegatingInner2)
      (Γ := [("y", Scheme.mono (.var 2)), ("v", Scheme.mono (.var 0))])
      (name := "y") (scheme := Scheme.mono .int) (by native_decide))

def delegatingInnerBodyVar_ddSynthOrigin :
    DDSynthOrigin emptySignature delegatingInnerBodyVar_ddSynth
      delegatingLedger₁ delegatingLedger₁ := by
  apply DDSynthOrigin.transportSome
  let lookup : (Context.applySubst delegatingInner2
      [("y", Scheme.mono (.var 2)),
        ("v", Scheme.mono (.var 0))]).find? "y" =
      some (Scheme.mono .int) := by native_decide
  let raw₀ := DDSynth.var (signature := emptySignature) (q := ⟨2, 4⟩)
    lookup
  have origin₀ : DDSynthOrigin emptySignature raw₀ delegatingLedger₁
      delegatingLedger₁ := by
    simpa [raw₀, DDLedger.markSchemeInstance,
      CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
      Scheme.FreshOpening.capImages, Scheme.mono] using
      (DDSynthOrigin.var (signature := emptySignature) (q := ⟨2, 4⟩)
        (ledger := delegatingLedger₁) lookup)
  have source₀ : ∃ raw, DDSynthOrigin emptySignature raw delegatingLedger₁
      delegatingLedger₁ := ⟨raw₀, origin₀⟩
  simpa only [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] using source₀

theorem delegatingBody_ddSynth :
    DDSynth emptySignature ⟨1, 2⟩ delegatingCheck1
      [("v", Scheme.mono (.var 0))] delegatingBody (Ty.listT .int)
      ⟨2, 4⟩ delegatingInner2 := by
  exact DDSynth.matchAll (S₃ := delegatingInner1) (q₃ := ⟨2, 4⟩)
    (S₄ := delegatingInner2) .lit delegatingInnerPattern_ddPattern
    (.ordinary rfl (ExactPairedMGU.varLeft 2 .int (by decide)))
    delegatingInnerMatcher_ddCheck delegatingInnerBodyVar_ddSynth

def delegatingBody_ddSynthOrigin :
    DDSynthOrigin emptySignature delegatingBody_ddSynth delegatingLedger₀
      delegatingLedger₁ := by
  exact .matchAll .lit delegatingInnerPattern_ddPatternOrigin
    (.ordinary rfl (originSafePairedCapId delegatingLedger₁
      (ExactPairedMGU.varLeft 2 .int (by decide))))
    delegatingInnerMatcher_ddCheckOrigin delegatingInnerBodyVar_ddSynthOrigin

/-- The delegating arm body: the inner `matchAll` synthesizes `List Int` and
aligns with the decomposition-result type `List ?0`. -/
theorem delegatingBody_ddCheck :
    DDCheck emptySignature ⟨1, 2⟩ delegatingCheck1
      [("v", Scheme.mono (.var 0))] delegatingBody (Ty.listT (.var 0))
      ⟨2, 4⟩ delegatingTerminal := by
  refine .mk (raw := Ty.listT .int) (q₁ := ⟨2, 4⟩)
    (S₁ := delegatingInner2) ?_ ?_
  · refine DDSynth.matchAll (S₃ := delegatingInner1) (q₃ := ⟨2, 4⟩)
      (S₄ := delegatingInner2) .lit
      (.pvar (by simp [MonoCtx.names])) ?_ ?_ ?_
    · exact .ordinary rfl (ExactPairedMGU.varLeft 2 .int (by decide))
    · exact .mk .something (.matcherToSlot rfl rfl
        ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
          ExactTargetMGU.varLeft 3 .int (by decide)⟩)
    · simpa only [InferenceBase.instantiateScheme_mono_value,
        InferenceBase.instantiateScheme_mono_supply, MonoCtx.toContext,
        List.map, List.append, List.nil_append, List.cons_append] using
        (DDSynth.var (signature := emptySignature) (q := ⟨2, 4⟩)
          (S := delegatingInner2)
          (Γ := [("y", Scheme.mono (.var 2)),
            ("v", Scheme.mono (.var 0))])
          (name := "y") (scheme := Scheme.mono .int) (by native_decide))
  · exact .ordinary rfl (.ordinary rfl delegating_bodyMGU_exact)

def delegatingBody_ddCheckOrigin :
    DDCheckOrigin emptySignature delegatingBody_ddCheck delegatingLedger₀
      delegatingLedger₁ := by
  exact .mk delegatingBody_ddSynthOrigin
    (.ordinary (S := delegatingInner2) (raw := Ty.listT .int)
      (expected := Ty.listT (.var 0)) rfl (.ordinary rfl
      (originSafePairedCapId delegatingLedger₁ delegating_bodyMGU_exact)))

/-- The single delegating clause: hole against the shared target, one
next-matcher slot check, and one variable arm. -/
theorem delegatingArms_ddArms :
    DDArms emptySignature ⟨1, 2⟩ delegatingCheck1 [] []
      [.mk (.var "v") delegatingBody] (.var 0)
      (Ty.listT (prodTy [Ty.var 0])) ⟨2, 4⟩ delegatingTerminal := by
  exact .cons .var (fun name _ => by simp [MonoCtx.names])
    delegatingBody_ddCheck .nil

def delegatingArms_ddArmsOrigin :
    DDArmsOrigin emptySignature delegatingArms_ddArms delegatingLedger₀
      delegatingLedger₁ := by
  exact .cons .var (fun name _ => by simp [MonoCtx.names])
    delegatingBody_ddCheckOrigin .nil

theorem delegatingClause_ddClause :
    DDClause emptySignature ⟨0, 1⟩ Subst.id []
      (.mk .hole .something [.mk (.var "v") delegatingBody]) (.var 0)
      [⟨.var ⟨0⟩, .var 0⟩] ⟨2, 4⟩ delegatingTerminal := by
  refine .mk .hole rfl delegatingNext_ddChecks ?_
  exact delegatingArms_ddArms

def delegatingClause_ddClauseOrigin :
    DDClauseOrigin emptySignature delegatingClause_ddClause []
      delegatingLedger₁ :=
  .mk .hole rfl delegatingNext_ddChecksOrigin delegatingArms_ddArmsOrigin

theorem delegatingClauses_ddClauses :
    DDClauses emptySignature ⟨0, 1⟩ Subst.id []
      [.mk .hole .something [.mk (.var "v") delegatingBody]] (.var 0)
      [[⟨.var ⟨0⟩, .var 0⟩]] ⟨2, 4⟩ delegatingTerminal :=
  .cons delegatingClause_ddClause .nil

def delegatingClauses_ddClausesOrigin :
    DDClausesOrigin emptySignature delegatingClauses_ddClauses []
      delegatingLedger₁ :=
  .cons delegatingClause_ddClauseOrigin .nil

theorem delegatingMatcher_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] delegatingMatcher
      (.matcher .any (.var 0)) ⟨2, 4⟩ delegatingTerminal := by
  exact DDSynth.matcher (evidence := [.unseen]) (capability := .any)
    delegatingClauses_ddClauses rfl rfl rfl rfl rfl rfl rfl

def delegatingMatcher_ddSynthOrigin :
    DDSynthOrigin emptySignature delegatingMatcher_ddSynth []
      delegatingLedger₁ := by
  simpa [delegatingMatcher, DDLedger.freezeMatcherProducer,
    DDLedger.matcherProducerLeaves, Inference.matcherProducerLedgerLeaves,
    Cap.fcv, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.matcher (signature := emptySignature)
      (evidence := [.unseen]) (capability := .any)
      delegatingClauses_ddClausesOrigin rfl rfl rfl rfl rfl rfl rfl)

def delegatingInnerBodyVar_terminalAudit :
    DDSynthTerminalAudit delegatingTerminal emptySignature
      delegatingInnerBodyVar_ddSynthOrigin := by
  let lookup : (Context.applySubst delegatingInner2
      [("y", Scheme.mono (.var 2)),
        ("v", Scheme.mono (.var 0))]).find? "y" =
      some (Scheme.mono .int) := by native_decide
  let origin₀ := DDSynthOrigin.var (signature := emptySignature)
    (q := ⟨2, 4⟩) (ledger := delegatingLedger₁) lookup
  let audit₀ : DDSynthTerminalAudit delegatingTerminal emptySignature
      origin₀ := DDSynthTerminalAudit.var (lookup := lookup)
  apply DDSynthTerminalAudit.transportBuilt
  let source₀ := DDSynthTerminalAudit.BuiltAudit.of audit₀
  rw [InferenceBase.instantiateScheme_mono_value,
    InferenceBase.instantiateScheme_mono_supply] at source₀
  simpa [audit₀, DDLedger.markSchemeInstance,
    CapabilityOriginLedger.setOrigins, Scheme.canonicalCapImages,
    Scheme.FreshOpening.capImages, Scheme.mono] using source₀

def delegatingNextHead_terminalAudit :
    DDCheckTerminalAudit delegatingTerminal emptySignature
      delegatingNextHead_ddCheckOrigin := by
  let aligned : DDAlignWithLedger delegatingLedger₀ Subst.id
      (.matcher .any (.var 1)) (.slot (.var ⟨0⟩) (.var 0))
      delegatingCheck1 :=
    .matcherToSlot rfl rfl ⟨
      ⟨[(⟨0⟩, Cap.any)], rfl, rfl,
        ExactTargetMGU.varLeft 1 (.var 0) (by decide)⟩,
      ⟨by
        rw [delegatingHoleCap_eq_single]
        exact PairedUnification.admissible_single_structuralFlexible
          delegatingLedger₀ ⟨0⟩ .any (by
            simp [delegatingLedger₀, DDLedger.markFreshCap])⟩⟩
  exact DDCheckTerminalAudit.mk (aligned := aligned)
    DDSynthTerminalAudit.something

def delegatingNext_terminalAudit :
    DDChecksTerminalAudit delegatingTerminal emptySignature
      delegatingNext_ddChecksOrigin :=
  .cons delegatingNextHead_terminalAudit .nil

def delegatingInnerPattern_terminalAudit :
    DDPatternTerminalAudit delegatingTerminal emptySignature
      delegatingInnerPattern_ddPatternOrigin :=
  .pvar (freshName := by simp [MonoCtx.names])

def delegatingInnerMatcher_terminalAudit :
    DDCheckTerminalAudit delegatingTerminal emptySignature
      delegatingInnerMatcher_ddCheckOrigin := by
  let aligned : DDAlignWithLedger delegatingLedger₁ delegatingInner1
      (.matcher .any (.var 3)) (.slot (.var ⟨1⟩) .int)
      delegatingInner2 :=
    .matcherToSlot rfl rfl ⟨
      ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
        ExactTargetMGU.varLeft 3 .int (by decide)⟩,
      ⟨by
        rw [delegatingInnerCap_eq_single]
        exact PairedUnification.admissible_single_structuralFlexible
          delegatingLedger₁ ⟨1⟩ .any (by
            simp [delegatingLedger₁, DDLedger.markFreshCap])⟩⟩
  exact DDCheckTerminalAudit.mk (aligned := aligned)
    DDSynthTerminalAudit.something

def delegatingBodySynth_terminalAudit :
    DDSynthTerminalAudit delegatingTerminal emptySignature
      delegatingBody_ddSynthOrigin := by
  let targetAligned : DDAlignTypesWithLedger delegatingLedger₁
      delegatingCheck1 (.var 2) .int delegatingInner1 :=
    .ordinary rfl (originSafePairedCapId delegatingLedger₁
      (ExactPairedMGU.varLeft 2 .int (by decide)))
  exact .matchAll (targetAligned := targetAligned) .lit
    delegatingInnerPattern_terminalAudit delegatingInnerMatcher_terminalAudit
    delegatingInnerBodyVar_terminalAudit

def delegatingBodyCheck_terminalAudit :
    DDCheckTerminalAudit delegatingTerminal emptySignature
      delegatingBody_ddCheckOrigin := by
  let aligned : DDAlignWithLedger delegatingLedger₁ delegatingInner2
      (Ty.listT .int) (Ty.listT (.var 0)) delegatingTerminal :=
    .ordinary rfl (.ordinary rfl
      (originSafePairedCapId delegatingLedger₁ delegating_bodyMGU_exact))
  exact DDCheckTerminalAudit.mk (aligned := aligned)
    delegatingBodySynth_terminalAudit

def delegatingArms_terminalAudit :
    DDArmsTerminalAudit delegatingTerminal emptySignature
      delegatingArms_ddArmsOrigin := by
  apply DDArmsTerminalAudit.cons
    (patternOrigin := DDDPatOrigin.var)
    (disjoint := fun name _ => by simp [MonoCtx.names])
  · exact delegatingBodyCheck_terminalAudit
  · exact .nil

def delegatingClause_terminalAudit :
    DDClauseTerminalAudit delegatingTerminal emptySignature
      delegatingClause_ddClauseOrigin := by
  apply DDClauseTerminalAudit.mk
    (ppOrigin := DDPPatOrigin.hole)
    (decomposed := rfl)
  · exact delegatingNext_terminalAudit
  · exact delegatingArms_terminalAudit

def delegatingClauses_terminalAudit :
    DDClausesTerminalAudit delegatingTerminal emptySignature
      delegatingClauses_ddClausesOrigin :=
  .cons delegatingClause_terminalAudit .nil

theorem delegatingMatcher_terminalFacts :
    DDTerminalAudit.MatcherFacts delegatingTerminal emptySignature
      [.mk .hole .something [.mk (.var "v") delegatingBody]]
      [[⟨.var ⟨0⟩, .var 0⟩]] .any (.var 0) := by
  constructor
  exact ⟨[.unseen], rfl, rfl, rfl, rfl, rfl⟩

def delegatingMatcher_terminalAudit :
    DDSynthTerminalAudit delegatingTerminal emptySignature
      delegatingMatcher_ddSynthOrigin := by
  exact DDSynthTerminalAudit.matcher (q := ⟨0, 0⟩)
    (evidence := [.unseen]) (capability := .any)
    (collected := rfl) (inferred := rfl) (clauseCaps := rfl)
    (catchAll := rfl) (binders := rfl) (arms := rfl) (coverage := rfl)
    delegatingClauses_terminalAudit delegatingMatcher_terminalFacts

/-- The delegating matcher literal closes at `Matcher Any Int` through the
demand-directed judgment, its finalization discharged by the same executable
coverage checks the executable traversal consumes. -/
theorem delegatingMatcher_ddTyping :
    DDTyping emptySignature [] delegatingMatcher (.matcher .any .int) := by
  exact ⟨.matcher .any (.var 0), ⟨2, 4⟩, delegatingTerminal,
    delegatingMatcher_ddSynth, delegatingLedger₁,
    delegatingMatcher_ddSynthOrigin, delegatingMatcher_terminalAudit, rfl⟩

/-- The executable pipeline accepts the delegating matcher as well: the
demand-directed derivation mirrors an actually accepted program. -/
theorem delegatingMatcher_accepted :
    Inference.inferenceSucceeds emptySignature [] delegatingMatcher = true := by
  native_decide

/-! ## Signature closedness and the bounded published type

The signature-closedness hypothesis of the freshness sweep is not vacuous:
the empty signature holds it trivially, the generic list signature holds it
by one decidable check per table, and the flagship polymorphic-let
derivation instantiates the closed-wrapper corollary.
-/

/-- The empty signature is closed. -/
theorem emptySignature_schemesClosed : emptySignature.SchemesClosed :=
  FrozenSig.SchemesClosed.of_entries (fun _ mem => nomatch mem)
    (fun _ mem => nomatch mem) (fun _ mem => nomatch mem)
    (fun _ mem => nomatch mem)

/-- The generic list signature is closed: every constructor and
pattern-constructor scheme quantifies all of its variables. -/
theorem listSignature_schemesClosed :
    RecursiveExamples.listSignature.SchemesClosed :=
  FrozenSig.SchemesClosed.of_entries (by decide) (by decide) (by decide)
    (by decide)

/-- The multiset signature is closed as well. -/
theorem multisetSignature_schemesClosed :
    RecursiveExamples.multisetSignature.SchemesClosed :=
  FrozenSig.SchemesClosed.of_entries (by decide) (by decide) (by decide)
    (by decide)

/-- The flagship polymorphic-let derivation publishes a type bounded by a
terminal supply extending the initial supply: the freshness sweep fires on
a concrete end-to-end derivation. -/
theorem dmLet_published_boundedBy :
    ∃ q', SupplyExtends
        (Inference.initialSupply emptySignature []) q' ∧
      Ty.BoundedBy q' Ty.int :=
  DDTyping.published_boundedBy dmLet_ddTyping emptySignature_schemesClosed

end DemandTypingRegression
end TypePM
