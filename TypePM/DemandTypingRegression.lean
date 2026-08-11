import TypePM.DemandTypingOriginMetatheory
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
theorem identity_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] identityExpr
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
  exact .lam (DDSynth.var (scheme := NamedScheme.mono (.var 0)) rfl)

theorem identity_ddSynthOrigin :
    DDSynthOrigin emptySignature identity_ddSynth [] [] := by
  refine .lam (bodyRaw := DDSynth.var
    (signature := emptySignature) (scheme := NamedScheme.mono (.var 0)) rfl) ?_
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, NamedScheme.mono,
    CapabilityOriginLedger.setOrigins]
    using (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 1⟩) (S := Subst.id) (context :=
        [("x", NamedScheme.mono (.var 0))]) (scheme := NamedScheme.mono (.var 0)) rfl)

/-- The closed wrapper publishes the identity type unchanged. -/
theorem identity_ddTyping :
    DDTyping emptySignature [] identityExpr (.fn (.var 0) (.var 0)) :=
  ⟨.fn (.var 0) (.var 0), ⟨0, 1⟩, Subst.id, identity_ddSynth, [],
    identity_ddSynthOrigin, rfl⟩

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

theorem applicationArgument_ddCheckOrigin :
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

theorem application_ddSynthOrigin :
    DDSynthOrigin emptySignature application_ddSynth [] [] := by
  exact .app identity_ddSynthOrigin
    (.ordinary rfl (originSafePairedCapId [] applicationDelta_pairedMGU))
    applicationArgument_ddCheckOrigin

/-- `(λx. x) 1` closes at `Int` through one domain alignment and one
demand-free ordinary argument alignment. -/
theorem application_ddTyping :
    DDTyping emptySignature [] (.app identityExpr (.lit 1)) .int := by
  exact ⟨.var 2, ⟨0, 3⟩, applicationTerminal, application_ddSynth, [],
    application_ddSynthOrigin, rfl⟩

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
def dmIdScheme : NamedScheme := ⟨[], [0], .fn (.var 0) (.var 0)⟩

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
theorem dmInnerFunction_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("id", dmIdScheme)]
      (.var "id") (.fn (.var 1) (.var 1)) ⟨0, 2⟩ Subst.id := by
  simpa [dmIdScheme, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("id", dmIdScheme)]) (scheme := dmIdScheme) rfl)

theorem dmInnerFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature dmInnerFunction_ddSynth [] [] := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages,
    dmIdScheme, CapabilityOriginLedger.setOrigins,
    InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyTarget, Cap.apply] using
    (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 1⟩) (S := Subst.id) (context := [("id", dmIdScheme)])
      (scheme := dmIdScheme) rfl)

theorem dmInnerArgumentVar_ddSynth :
    DDSynth emptySignature ⟨0, 4⟩ dmAlign1 [("id", dmIdScheme)]
      (.var "id") (.fn (.var 4) (.var 4)) ⟨0, 5⟩ dmAlign1 := by
  simpa [dmIdScheme, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 4⟩)
      (S := dmAlign1) (Γ := [("id", dmIdScheme)])
      (scheme := dmIdScheme) rfl)

theorem dmInnerArgumentVar_ddSynthOrigin :
    DDSynthOrigin emptySignature dmInnerArgumentVar_ddSynth [] [] := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages,
    dmIdScheme, CapabilityOriginLedger.setOrigins,
    InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyTarget, Cap.apply] using
    (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 4⟩) (S := dmAlign1) (context := [("id", dmIdScheme)])
      (scheme := dmIdScheme) rfl)

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
  refine .letE identity_ddSynthOrigin dmOuterApp_ddSynthOrigin ?_
  decide

/-- The polymorphic-`let` witness closes at `Int` through the demand-directed
judgment: the `let` rule generalizes the value type in the substituted
context, and each use of `id` instantiates the quantified scheme at a fresh
supply-indexed image. -/
theorem dmLet_ddTyping :
    DDTyping emptySignature [] dmLetProgram .int := by
  exact ⟨.var 6, ⟨0, 7⟩, dmLetTerminal, dmLet_ddSynth, [],
    dmLet_ddSynthOrigin, rfl⟩

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
theorem nestedCapLetFirstFunction_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("f", dmIdScheme)]
      (.var "f") (.fn (.var 1) (.var 1)) ⟨0, 2⟩ Subst.id := by
  simpa [dmIdScheme, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 1⟩)
      (S := Subst.id) (Γ := [("f", dmIdScheme)]) (scheme := dmIdScheme) rfl)

theorem nestedCapLetFirstFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetFirstFunction_ddSynth [] [] := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, dmIdScheme,
    CapabilityOriginLedger.setOrigins, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 1⟩) (S := Subst.id) (context := [("f", dmIdScheme)])
      (scheme := dmIdScheme) rfl)

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
theorem nestedCapLetSecondFunction_ddSynth :
    DDSynth emptySignature ⟨0, 5⟩ nestedCapLetCheck1 [("f", dmIdScheme)]
      (.var "f") (.fn (.var 5) (.var 5)) ⟨0, 6⟩ nestedCapLetCheck1 := by
  simpa [dmIdScheme, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynth.var (signature := emptySignature) (q := ⟨0, 5⟩)
      (S := nestedCapLetCheck1) (Γ := [("f", dmIdScheme)])
      (scheme := dmIdScheme) rfl)

theorem nestedCapLetSecondFunction_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetSecondFunction_ddSynth [] [] := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, dmIdScheme,
    CapabilityOriginLedger.setOrigins, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply] using
    (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 5⟩) (S := nestedCapLetCheck1)
      (context := [("f", dmIdScheme)]) (scheme := dmIdScheme) rfl)

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

theorem nestedCapLetValue_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] (.lam "m" (.var "m"))
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
  exact .lam (DDSynth.var (scheme := NamedScheme.mono (.var 0)) rfl)

theorem nestedCapLetValue_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetValue_ddSynth [] [] := by
  refine .lam (bodyRaw := DDSynth.var (signature := emptySignature)
    (scheme := NamedScheme.mono (.var 0)) rfl) ?_
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages, NamedScheme.mono,
    CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.var (signature := emptySignature) (ledger := [])
      (q := ⟨0, 1⟩) (S := Subst.id)
      (context := [("m", NamedScheme.mono (.var 0))])
      (scheme := NamedScheme.mono (.var 0)) rfl)

theorem nestedCapLetProgram_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      AcceptanceGapRegression.nestedCapLetProgram (.prod [.var 3, .var 7])
      ⟨0, 10⟩ nestedCapLetTerminal :=
  .letE nestedCapLetValue_ddSynth
    (.tuple (.cons nestedCapLetFirstApp_ddSynth
      (.cons nestedCapLetSecondApp_ddSynth .nil)))

theorem nestedCapLetProgram_ddSynthOrigin :
    DDSynthOrigin emptySignature nestedCapLetProgram_ddSynth [] [] := by
  refine .letE nestedCapLetValue_ddSynthOrigin
    (.tuple (.cons nestedCapLetFirstApp_ddSynthOrigin
      (.cons nestedCapLetSecondApp_ddSynthOrigin .nil))) ?_
  decide

/-- The `let`-polymorphic pairing of the two producers closes in the
demand-directed judgment at exactly the executable raw result shape. -/
theorem nestedCapLetProgram_ddTyping :
    DDTyping emptySignature [] AcceptanceGapRegression.nestedCapLetProgram
      (.prod [.matcher .any (.var 4),
        .prod [.matcher .any (.var 8), .matcher .any (.var 9)]]) := by
  exact ⟨.prod [.var 3, .var 7], ⟨0, 10⟩, nestedCapLetTerminal,
    nestedCapLetProgram_ddSynth, [], nestedCapLetProgram_ddSynthOrigin, rfl⟩

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
      some ((NamedScheme.mono (Ty.var 0)).applySubst Subst.id) :=
    lookup.symm.trans rfl
  injection pinned1 with pinnedScheme1
  subst pinnedScheme1
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
      some ((NamedScheme.mono (Ty.var 0)).applySubst
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
      some ((NamedScheme.mono (Ty.var 0)).applySubst Subst.id) :=
    lookup.symm.trans rfl
  injection pinned1 with pinnedScheme1
  subst pinnedScheme1
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
      some ((NamedScheme.mono (Ty.var 0)).applySubst
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

/-! ## Boundary: bare most-generality does not transport value flow

The no-guess theorems bound every most general solve delta to at most a
renaming of variables outside its constraint.  That residual freedom is
already enough to break delta-wise transport of declarative value-flow
instances: a most general solution of `?1 ≐ Int` may additionally swap the
unrelated variables `?3` and `?9`.  If `?9` is the binder of a partially
generalized scheme with `?3` free, the masked scheme substitution captures
— `∀9. 9 → 3` becomes `∀9. 9 → 9` — while the transported instance
`Int → ?9` is no instance of the captured scheme.  This fixes, as a
boundary theorem, why the forgetting map to `RuntimeTyping` cannot be proved by
transporting instances along bare `PairedMGU` deltas, and it motivates the
exactness strengthening (identity outside the constraint) of the
judgment's solve deltas: the swap is exactly what exactness removes. -/

/-- A most general solution of `?1 ≐ Int` that additionally swaps the
unrelated variables `?3` and `?9`. -/
def swappingDelta : Subst :=
  ⟨CapSubst.id, fun candidate =>
    if candidate = 1 then .int
    else if candidate = 3 then .var 9
    else if candidate = 9 then .var 3
    else .var candidate⟩

/-- The swap delta is a genuine most general paired solution: any unifier
factors through it by un-swapping. -/
theorem swappingDelta_pairedMGU : PairedMGU (.var 1) .int swappingDelta := by
  constructor
  · rfl
  · intro U unifies
    have fixesOne : U.target 1 = .int := unifies
    refine ⟨⟨U.cap, fun candidate =>
      if candidate = 3 then U.target 9
      else if candidate = 9 then U.target 3
      else U.target candidate⟩, ?_⟩
    have targetEq : U.target = fun candidate =>
        Subst.apply
          ⟨U.cap, fun candidate =>
            if candidate = 3 then U.target 9
            else if candidate = 9 then U.target 3
            else U.target candidate⟩
          (swappingDelta.target candidate) := by
      funext candidate
      by_cases hone : candidate = 1
      · subst hone
        simpa [swappingDelta] using fixesOne
      · by_cases hthree : candidate = 3
        · subst hthree
          simp [swappingDelta, Subst.apply, Ty.applyCapability,
            Ty.applyTarget]
        · by_cases hnine : candidate = 9
          · subst hnine
            simp [swappingDelta, Subst.apply, Ty.applyCapability,
              Ty.applyTarget]
          · simp [swappingDelta, hone, hthree, hnine, Subst.apply,
              Ty.applyCapability, Ty.applyTarget]
    exact congrArg (Subst.mk U.cap) targetEq

/-- The partially generalized scheme `∀9. 9 → 3`: `?9` is quantified,
`?3` is shared with the ambient context. -/
def capturedScheme : NamedScheme := ⟨[], [9], .fn (.var 9) (.var 3)⟩

/-- Before transport: `Int → ?3` is a value-flow instance. -/
theorem capturedScheme_instance :
    capturedScheme.ValueFlowInst (.fn .int (.var 3)) := by
  refine ⟨CapSubst.id, fun candidate =>
    if candidate = 9 then .int else .var candidate, ?_⟩
  refine
    { capSupport := CapSubst.id_supportWithin _
      tySupport := ?_
      capBinderVariable := ?_
      result := ?_ }
  · intro candidate outside
    have : ¬ candidate = 9 := by
      intro h
      exact outside (by simp [capturedScheme, h])
    simp [this]
  · intro varId membership
    nomatch membership
  · rfl

/-- After transport by the swap delta the instance is gone: the masked
scheme substitution captured the binder. -/
theorem capturedScheme_transport_refuted :
    ¬ (capturedScheme.applySubst swappingDelta).ValueFlowInst
      (swappingDelta.apply (.fn .int (.var 3))) := by
  rintro ⟨C, T, inst⟩
  have components := inst.result
  have captured :
      Ty.fn (((Ty.var 9).applyCapability C).applyTarget T)
        (((Ty.var 9).applyCapability C).applyTarget T) =
      Ty.fn .int (.var 9) := components
  injection captured with domainEq codomainEq
  rw [domainEq] at codomainEq
  nomatch codomainEq

/-- The boundary in one statement: the swap delta is most general, the
instance holds before transport, and fails after. -/
theorem valueFlow_transport_needs_exactness :
    PairedMGU (.var 1) .int swappingDelta ∧
      capturedScheme.ValueFlowInst (.fn .int (.var 3)) ∧
      ¬ (capturedScheme.applySubst swappingDelta).ValueFlowInst
        (swappingDelta.apply (.fn .int (.var 3))) :=
  ⟨swappingDelta_pairedMGU, capturedScheme_instance,
    capturedScheme_transport_refuted⟩

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

/-! ## Boundary: the capability-freeze axis reaches the forgetting map

The demand-directed judgment deliberately omits the capability-freeze/export
ledger axis.  This boundary shows the omission is visible to the forgetting
map itself, not only to acceptance: over a context binding a quantified
matcher producer `m : ∀κ α. Matcher κ α`, the program

```
(λh. (h something, h m)) (λz. z)
```

shares one monomorphic consumer between the `Any`-capped `something` and an
instance of `m`.  The demand-directed derivation resolves the shared domain
from the first use and then structures the fresh instance capability of `m`
to `Any` by an ordinary matcher-pair solve — an exact most general solve,
so no-guess and exactness are respected.  The published type
`(Matcher Any ?4, Matcher Any ?4)` nevertheless has no `RuntimeTyping`
certificate: its value-flow instance maps a quantified capability
binder only to a capability *variable*, and every coercion rule that could
retype `m` either concludes at a slot head or carries the violating
instance in its premise.  Unconditional forgetting from `DDTyping` to
`RuntimeTyping` over an arbitrary context is therefore false.  The DD family
must gain the freeze ledger axis before unconditional state erasure is valid. -/

/-- A quantified matcher producer: `∀κ α. Matcher κ α`. -/
def producerScheme : NamedScheme := ⟨[⟨0⟩], [0], .matcher (.var ⟨0⟩) (.var 0)⟩

/-- The seeded context binding the producer. -/
def producerContext : Context := [("m", producerScheme)]

/-- One monomorphic consumer shared between `something` and the producer. -/
def capFreezeProgram : Expr :=
  .app (.lam "h" (.tuple
    [.app (.var "h") .something, .app (.var "h") (.var "m")]))
    (.lam "z" (.var "z"))

/-- The inner context of the consumer body. -/
def capFreezeInnerContext : Context :=
  ("h", NamedScheme.mono (.var 1)) :: producerContext

/-- Prevailing substitution after the first-use function alignment. -/
def capFreezeAlign1 : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 1 (.fn (.var 2) (.var 3))⟩ Subst.id

/-- Prevailing substitution after the first argument check resolves the
shared domain to the `Any`-capped matcher producer. -/
def capFreezeCheck1 : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 2 (.matcher .any (.var 4))⟩ capFreezeAlign1

/-- Prevailing substitution after the second-use function alignment. -/
def capFreezeAlign2 : Subst :=
  Subst.seq ⟨CapSubst.id,
    fnFreshDelta (.matcher .any (.var 4)) (.var 3) 5 6⟩ capFreezeCheck1

/-- Prevailing substitution after the matcher-pair solve structures the
fresh instance capability of the producer to `Any`. -/
def capFreezeStructure : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 7 (.var 4)⟩
    (Subst.seq ⟨Unification.CapSubst.single ⟨1⟩ .any, TySubst.id⟩
      capFreezeAlign2)

/-- Prevailing substitution after the outer function alignment. -/
def capFreezeAlign3 : Subst :=
  Subst.seq ⟨CapSubst.id,
    fnFreshDelta (.fn (.matcher .any (.var 4)) (.var 3))
      (.prod [.var 3, .var 3]) 8 9⟩ capFreezeStructure

/-- Terminal substitution: the identity argument collapses its shared
domain/codomain onto the resolved consumer domain. -/
def capFreezeTerminal : Subst :=
  Subst.seq ⟨CapSubst.id,
    fnSharedFreshDelta 10 (.matcher .any (.var 4)) 3⟩ capFreezeAlign3

/-- The first use pins the shared domain to the bare producer. -/
theorem capFreezeFirstApp_ddSynth :
    DDSynth emptySignature ⟨1, 2⟩ Subst.id capFreezeInnerContext
      (.app (.var "h") .something) (.var 3) ⟨1, 5⟩ capFreezeCheck1 := by
  exact DDSynth.app (q₁ := ⟨1, 2⟩) (S₁ := Subst.id) (S₂ := capFreezeAlign1)
    (functionTarget := .var 1)
    (DDSynth.var (scheme := NamedScheme.mono (.var 1)) rfl)
    (.ordinary rfl (ExactPairedMGU.varLeft 1 (.fn (.var 2) (.var 3))
      (by decide)))
    (.mk .something (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide)))))

/-- The second use structures the fresh instance capability of `m` to `Any`
by an ordinary matcher-pair solve: an exact most general solve with no slot
demand anywhere. -/
theorem capFreezeSecondApp_ddSynth :
    DDSynth emptySignature ⟨1, 5⟩ capFreezeCheck1 capFreezeInnerContext
      (.app (.var "h") (.var "m")) (.var 6) ⟨2, 8⟩ capFreezeStructure := by
  exact DDSynth.app (q₁ := ⟨1, 5⟩) (S₁ := capFreezeCheck1)
    (S₂ := capFreezeAlign2)
    (functionTarget := .fn (.matcher .any (.var 4)) (.var 3))
    (DDSynth.var
      (scheme := NamedScheme.mono (.fn (.matcher .any (.var 4)) (.var 3))) rfl)
    (.ordinary rfl (ExactPairedMGU.fnFresh (.matcher .any (.var 4))
      (.var 3) 5 6 (by decide) (by decide) (by decide) (by decide)
      (by decide)))
    (.mk (DDSynth.var (scheme := producerScheme) rfl)
      (.ordinary rfl
        (.matcherPair rfl rfl (ExactCapMGU.varLeft ⟨1⟩ .any (by decide))
          (ExactPairedMGU.varLeft 7 (.var 4) (by decide)))))

/-! The ledger-aware alignment kernel closes the acceptance gap at the exact
failing cut.  Context lookup instantiates the quantified capability binder as
fresh variable `⟨1⟩` and marks it rename-only, so the otherwise exact
solution `⟨1⟩ := Any` is not origin-admissible. -/

def producerInstanceLedger : CapabilityOriginLedger :=
  DDLedger.markSchemeInstance [] ⟨1, 5⟩ producerScheme

def producerAnyCapDelta : CapSubst :=
  Unification.CapSubst.single ⟨1⟩ .any

theorem producerAnyExact_not_originSafe {delta : CapSubst} :
    ¬ OriginSafeExactCapMGU producerInstanceLedger (.var ⟨1⟩) .any
      delta := by
  intro safe
  have origin : producerInstanceLedger.originOf ⟨1⟩ = .renameOnly :=
    DDLedger.markSchemeInstance_origin_of_mem [] ⟨1, 5⟩ producerScheme
      ⟨1⟩ (by simp [Inference.freshCapImages, producerScheme])
  have imageEquation : delta ⟨1⟩ = .any := by
    simpa [Cap.apply] using safe.exact.1.1
  rcases safe.admissible.renameOnly_image_variable origin imageEquation with
    ⟨image, impossible, _⟩
  nomatch impossible

theorem producerAnyCapDelta_not_originSafe :
    ¬ OriginSafeExactCapMGU producerInstanceLedger (.var ⟨1⟩) .any
      producerAnyCapDelta :=
  producerAnyExact_not_originSafe

/-- At the concrete matcher-pair cut, no output substitution can be produced
by the ledger-aware alignment relation: exact solving forces the rename-only
producer image to be `Any`, which admissibility forbids. -/
theorem producerAny_no_ledger_alignment :
    ¬ ∃ S', DDAlignTypesWithLedger producerInstanceLedger Subst.id
      (.matcher (.var ⟨1⟩) (.var 7)) (.matcher .any (.var 4)) S' := by
  rintro ⟨S', aligned⟩
  cases aligned with
  | matcherPair leftView rightView capSafe targetSafe =>
      rw [Subst.apply_id] at leftView rightView
      cases leftView
      cases rightView
      exact producerAnyExact_not_originSafe capSafe
  | slotPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      nomatch leftView
  | ordinary pairClass _ =>
      rw [Subst.apply_id, Subst.apply_id] at pairClass
      nomatch pairClass

/-- The origin-aware public judgment rejects the seeded capability-freeze
counterexample at the producer's second-use cut. -/
theorem capFreezeProgram_no_ddTyping (target : Ty) :
    ¬ DDTyping emptySignature producerContext capFreezeProgram target := by
  rintro ⟨_raw, _q', _S', _derived, _ledger', origin, _published⟩
  cases origin with
  | app functionOrigin _outerAligned _outerArgumentOrigin =>
  cases functionOrigin with
  | lam bodyOrigin =>
  cases bodyOrigin with
  | tuple componentsOrigin =>
  cases componentsOrigin with
  | cons firstOrigin restOrigin =>
  cases restOrigin with
  | cons secondOrigin _nilOrigin =>
  cases firstOrigin with
  | app firstFunctionOrigin firstAligned firstArgumentOrigin =>
  have closed : emptySignature.SchemesClosed :=
    FrozenSig.SchemesClosed.of_entries (fun _ mem => nomatch mem)
      (fun _ mem => nomatch mem) (fun _ mem => nomatch mem)
      (fun _ mem => nomatch mem)
  have producerCapFree : producerScheme.fcv = [] := by decide
  have producerTyFree : producerScheme.ftv = [] := by decide
  have producerStable : ∀ post : Subst,
      producerScheme.applySubst post = producerScheme := by
    intro post
    apply NamedScheme.applySubst_eq_self_of_free_fixed
    · intro varId mem
      nomatch producerCapFree ▸ mem
    · intro varId mem
      nomatch producerTyFree ▸ mem
  have innerContextBounded : Context.BoundedBy ⟨1, 2⟩
      capFreezeInnerContext := by
    intro entry mem
    simp only [capFreezeInnerContext, producerContext, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact NamedScheme.BoundedBy.ofMono (Ty.BoundedBy.varOf (by decide))
    · exact ⟨
        (fun varId mem => nomatch producerCapFree ▸ mem),
        (fun varId mem => nomatch producerTyFree ▸ mem)⟩
  have firstCuts := firstFunctionOrigin.appCutsBounded firstAligned closed
    (Subst.boundedBy_id ⟨1, 2⟩) innerContextBounded
  have firstArgumentContextBounded := innerContextBounded.mono
    (firstFunctionOrigin.erase.supplyExtends.trans
      (SupplyExtends.bumpTy _ 2))
  have firstArgumentSubstBounded := firstArgumentOrigin.outputBounded closed
    firstCuts.alignedSubst firstArgumentContextBounded
      firstCuts.argumentDomain
  have firstArgumentRaw := firstArgumentOrigin.erase
  cases firstFunctionOrigin with
  | var lookup1 =>
  simp [Context.applySubst, Context.find?] at lookup1
  subst_vars
  change DDAlignTypesWithLedger [] Subst.id (.var 1)
    (.fn (.var 2) (.var 3)) _ at firstAligned
  obtain ⟨domainImage, domainView⟩ :=
    firstAligned.var_fn_domain_variable (by decide) (by decide) (by decide)
  have firstOutput := firstAligned.output_equal
  cases firstArgumentOrigin with
  | mk somethingOrigin firstArgumentAligned =>
  cases somethingOrigin with
  | something =>
  have firstArgumentReplay := DDAlign.replayExtends firstArgumentAligned.erase
  cases firstArgumentAligned with
  | productMatcherLift _ slotView _ =>
      exact nomatch domainView.symm.trans slotView
  | slotTupleLift _ _ slotView _ _ =>
      exact nomatch domainView.symm.trans slotView
  | matcherToSlot _ slotView _ =>
      exact nomatch domainView.symm.trans slotView
  | slotToSlot rawView _ _ _ => nomatch rawView
  | ordinary _ firstArgumentTypes =>
  have argumentOutput := firstArgumentTypes.output_equal
  cases firstArgumentTypes with
  | matcherPair _ rightView _ _ =>
      exact nomatch domainView.symm.trans rightView
  | slotPair leftView _ _ _ => nomatch leftView
  | ordinary _ _firstArgumentSafe =>
  have sharedOutput := firstArgumentReplay.apply_eq firstOutput
  cases secondOrigin with
  | app secondFunctionOrigin secondAligned secondArgumentOrigin =>
  have secondContextBounded := firstArgumentContextBounded.mono
    firstArgumentRaw.supplyExtends
  have secondCuts := secondFunctionOrigin.appCutsBounded secondAligned closed
    firstArgumentSubstBounded secondContextBounded
  cases secondFunctionOrigin with
  | var lookup2 =>
  simp [Context.applySubst, Context.find?] at lookup2
  subst_vars
  rw [InferenceBase.instantiateNamedScheme_mono_value] at secondAligned
  have initialTy :
      (Inference.initialSupply emptySignature producerContext).nextTy = 1 :=
    by decide
  rw [initialTy] at secondAligned
  rw [sharedOutput] at secondAligned
  simp only [InferenceBase.instantiateNamedScheme_mono_supply, initialTy,
    Nat.reduceAdd] at argumentOutput secondAligned
  simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget, Cap.apply]
    at argumentOutput secondAligned
  rw [← argumentOutput] at secondAligned
  have secondOutput := secondAligned.output_equal
  simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget, Cap.apply]
    at secondOutput
  injection secondOutput with secondDomainOutput _secondCodomainOutput
  cases secondArgumentOrigin with
  | mk producerOrigin producerAligned =>
  cases producerOrigin with
  | var lookupProducer =>
  simp [Context.applySubst, Context.find?, producerContext, producerStable]
    at lookupProducer
  subst_vars
  have initialCap :
      (Inference.initialSupply emptySignature producerContext).nextCap = 1 :=
    by decide
  simp only [InferenceBase.instantiateNamedScheme_mono_supply, initialTy,
    initialCap, Nat.reduceAdd] at producerAligned secondCuts
  simp [InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst, producerScheme,
    Cap.apply, Subst.apply, Ty.applyCapability, Ty.applyTarget]
    at producerAligned
  apply producerAligned.not_of_nonStructuralMatcher_any
  · change _ = Ty.matcher (.var ⟨1⟩) _
    simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget]
    congr 1
    simpa [Cap.apply] using secondCuts.argumentFreshCapFixed
  · simpa [Subst.apply, Ty.applyCapability, Ty.applyTarget] using
      secondDomainOutput.symm
  · intro structural
    change (DDLedger.markSchemeInstance _ ⟨1, 7⟩
      producerScheme).originOf ⟨1⟩ = .structuralFlexible at structural
    rw [DDLedger.markSchemeInstance_origin_of_mem _ ⟨1, 7⟩
      producerScheme ⟨1⟩
        (by simp [Inference.freshCapImages, producerScheme])] at structural
    cases structural

/-- No instance of the quantified producer is `Any`-capped: the declarative
value flow maps the capability binder only to a variable. -/
theorem producerScheme_no_any_instance (target : Ty) :
    ¬ producerScheme.ValueFlowInst (.matcher .any target) := by
  rintro ⟨C, T, inst⟩
  have caps : Cap.apply C (Cap.var ⟨0⟩) = Cap.any := by
    have components :
        Ty.matcher (Cap.apply C (Cap.var ⟨0⟩))
          (((Ty.var 0).applyCapability C).applyTarget T) =
        Ty.matcher .any target := inst.result
    injection components with capEq _
  obtain ⟨image, imageEq⟩ := inst.capBinderVariable ⟨0⟩ (by decide)
  have caps' : C ⟨0⟩ = Cap.any := caps
  nomatch imageEq.symm.trans caps'

/-- The published type has no runtime certificate: the shared
monomorphic consumer forces `m` to inhabit the `Any`-capped matcher type,
which no value-flow instance provides. -/
theorem capFreezeProgram_not_runtimeTyping :
    ¬ RuntimeTyping emptySignature producerContext capFreezeProgram
      (.prod [.matcher .any (.var 4), .matcher .any (.var 4)]) := by
  intro typing
  cases typing with
  | app hfun harg =>
  cases hfun with
  | lam hbody =>
  cases hbody with
  | tuple hcomponents =>
  cases hcomponents with
  | cons hfirst hrest =>
  cases hrest with
  | cons hsecond hnil =>
  cases hsecond with
  | app hfun2 harg2 =>
  cases hfun2 with
  | var hfind2 hinst2 =>
  rename_i outerDomain innerDomain scheme2
  have pinned2 : some scheme2 = some (NamedScheme.mono outerDomain) :=
    hfind2.symm.trans rfl
  injection pinned2 with pinnedScheme2
  subst pinnedScheme2
  have domainEq := hinst2.mono_eq
  subst domainEq
  cases harg with
  | lam hz =>
  cases hz with
  | var hfindz hinstz =>
  rename_i schemez
  have pinnedz : some schemez = some (NamedScheme.mono _) :=
    hfindz.symm.trans rfl
  injection pinnedz with pinnedSchemez
  subst pinnedSchemez
  have argEq := hinstz.mono_eq
  subst argEq
  cases harg2 with
  | var hfindm hinstm =>
  rename_i schemem
  have pinnedm : some schemem = some producerScheme :=
    hfindm.symm.trans rfl
  injection pinnedm with pinnedSchemem
  subst pinnedSchemem
  exact producerScheme_no_any_instance _ hinstm

/-! ## Capability freeze through `let`: the second forgetting-gap source

The seeded gap above quantifies its matcher producer in the ambient
context.  This block shows the same freeze-axis separation arises with no
polymorphic seed at all: `let` generalization over a capability-polymorphic
constructor field creates the quantified producer itself.  Under
`m2 : Matcher (con "c" []) Int`,

  `let f = λx. Pack x in (f something, f m2)`

closes in `DDTyping` at `(Packed, Packed)`: the value's domain resolves to
`Matcher ?κ ?α`, mid-derivation generalization quantifies the capability
meta, and each use structures its own fresh instance capability by an
ordinary matcher-pair solve (`Any` at the first use, `con "c" []` at the
second).  No state-free certificate can choose a λ domain serving both uses: a
variable-capped domain violates the variable-only value-flow condition,
and any structural cap collides with one of the two divergent demands.
The required freeze provenance therefore cannot be a condition on the
ambient context alone — it must constrain
`let`-generalized schemes as well. -/

open AcceptanceGapRegression (packSignature packScheme)

/-- One monomorphic structurally-capped consumer seed. -/
def letCapContext : Context :=
  [("m2", NamedScheme.mono (.matcher (.con "c" []) .int))]

/-- `let f = λx. Pack x in (f something, f m2)`. -/
def letCapFreezeProgram : Expr :=
  .letE "f" (.lam "x" (.ctor "Pack" [.var "x"]))
    (.tuple [.app (.var "f") .something, .app (.var "f") (.var "m2")])

/-- Prevailing substitution after the value's constructor-argument check
resolves the λ domain to the instantiated `Pack` field. -/
def letCapValueSubst : Subst :=
  Subst.seq ⟨CapSubst.id,
    Unification.TySubst.single 1 (.matcher (.var ⟨1⟩) (.var 2))⟩ Subst.id

/-- The mid-derivation generalization of the value type quantifies the
still-unresolved instance capability. -/
def letCapScheme : NamedScheme :=
  ⟨[⟨1⟩], [2], .fn (.matcher (.var ⟨1⟩) (.var 2)) (.data "Packed" [])⟩

/-- The body context binding the generalized producer. -/
def letCapBodyContext : Context := ("f", letCapScheme) :: letCapContext

/-- Prevailing substitution after the first-use function alignment. -/
def letCapFn1 : Subst :=
  Subst.seq ⟨CapSubst.id,
    fnFreshDelta (.matcher (.var ⟨3⟩) (.var 5)) (.data "Packed" []) 6 7⟩
    letCapValueSubst

/-- Prevailing substitution after the first argument check structures the
first fresh instance capability to `Any`. -/
def letCapStructure1 : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 8 (.var 5)⟩
    (Subst.seq ⟨Unification.CapSubst.single ⟨3⟩ .any, TySubst.id⟩ letCapFn1)

/-- Prevailing substitution after the second-use function alignment. -/
def letCapFn2 : Subst :=
  Subst.seq ⟨CapSubst.id,
    fnFreshDelta (.matcher (.var ⟨5⟩) (.var 11)) (.data "Packed" []) 12 13⟩
    letCapStructure1

/-- Terminal substitution: the second argument check structures the second
fresh instance capability to `con "c" []`. -/
def letCapTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 11 .int⟩
    (Subst.seq ⟨Unification.CapSubst.single ⟨5⟩ (.con "c" []), TySubst.id⟩
      letCapFn2)

/-- The value synthesizes at `?1 → Packed` with the domain resolved to the
instantiated constructor field `Matcher ?⟨1⟩ ?2`. -/
theorem letCapValue_ddSynth :
    DDSynth packSignature ⟨1, 1⟩ Subst.id letCapContext
      (.lam "x" (.ctor "Pack" [.var "x"]))
      (.fn (.var 1) (.data "Packed" [])) ⟨2, 3⟩ letCapValueSubst := by
  exact DDSynth.lam
    (DDSynth.ctor (scheme := packScheme) rfl
      (.cons (.mk (DDSynth.var (scheme := NamedScheme.mono (.var 1)) rfl)
        (.ordinary rfl (.ordinary rfl
          (ExactPairedMGU.varLeft 1 (.matcher (.var ⟨1⟩) (.var 2))
            (by decide)))))
        .nil))

/-- The first use structures the fresh instance capability of `f` to `Any`
by an ordinary matcher-pair solve against `something`. -/
theorem letCapUse1_ddSynth :
    DDSynth packSignature ⟨2, 3⟩ letCapValueSubst letCapBodyContext
      (.app (.var "f") .something) (.var 7) ⟨4, 9⟩ letCapStructure1 := by
  exact DDSynth.app (q₁ := ⟨4, 6⟩) (S₁ := letCapValueSubst) (S₂ := letCapFn1)
    (functionTarget := .fn (.matcher (.var ⟨3⟩) (.var 5)) (.data "Packed" []))
    (DDSynth.var (scheme := letCapScheme) rfl)
    (.ordinary rfl (ExactPairedMGU.fnFresh (.matcher (.var ⟨3⟩) (.var 5))
      (.data "Packed" []) 6 7 (by decide) (by decide) (by decide) (by decide)
      (by decide)))
    (.mk .something (.ordinary rfl (.matcherPair rfl rfl
      (ExactCapMGU.varRight .any ⟨3⟩ (by decide))
      (ExactPairedMGU.varLeft 8 (.var 5) (by decide)))))

/-! The first let-generalized lookup has the same value-flow freeze boundary:
fresh image `⟨3⟩` is rename-only and therefore cannot be specialized to
`Any`, even though the symmetric `varRight` delta is an exact MGU. -/

def letCapInstanceLedger : CapabilityOriginLedger :=
  DDLedger.markSchemeInstance [] ⟨2, 3⟩ letCapScheme

def letCapAnyCapDelta : CapSubst :=
  Unification.CapSubst.single ⟨3⟩ .any

theorem letCapAnyExact_not_originSafe {delta : CapSubst} :
    ¬ OriginSafeExactCapMGU letCapInstanceLedger .any (.var ⟨3⟩)
      delta := by
  intro safe
  have origin : letCapInstanceLedger.originOf ⟨3⟩ = .renameOnly :=
    DDLedger.markSchemeInstance_origin_of_mem [] ⟨2, 3⟩ letCapScheme
      ⟨3⟩ (by simp [Inference.freshCapImages, letCapScheme])
  have imageEquation : delta ⟨3⟩ = .any := by
    simpa [Cap.apply] using safe.exact.1.1.symm
  rcases safe.admissible.renameOnly_image_variable origin imageEquation with
    ⟨image, impossible, _⟩
  nomatch impossible

theorem letCapAnyCapDelta_not_originSafe :
    ¬ OriginSafeExactCapMGU letCapInstanceLedger .any (.var ⟨3⟩)
      letCapAnyCapDelta :=
  letCapAnyExact_not_originSafe

/-- The complete matcher-pair alignment at the first let-body use is likewise
impossible under the lookup ledger, independently of which exact MGU witness
is chosen. -/
theorem letCapAny_no_ledger_alignment :
    ¬ ∃ S', DDAlignTypesWithLedger letCapInstanceLedger Subst.id
      (.matcher .any (.var 8)) (.matcher (.var ⟨3⟩) (.var 5)) S' := by
  rintro ⟨S', aligned⟩
  cases aligned with
  | matcherPair leftView rightView capSafe targetSafe =>
      rw [Subst.apply_id] at leftView rightView
      cases leftView
      cases rightView
      exact letCapAnyExact_not_originSafe capSafe
  | slotPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      nomatch leftView
  | ordinary pairClass _ =>
      rw [Subst.apply_id, Subst.apply_id] at pairClass
      nomatch pairClass

/-- The public origin-aware judgment rejects the let-generalized capability
freeze counterexample at its first body use: the generalized capability
binder is instantiated as a rename-only fresh image, while `something`
demands `Any`. -/
theorem letCapFreezeProgram_no_ddTyping (target : Ty) :
    ¬ DDTyping packSignature letCapContext letCapFreezeProgram target := by
  rintro ⟨_raw, _q', _S', _derived, _ledger', origin, _published⟩
  have initial : Inference.initialSupply packSignature letCapContext =
      ⟨1, 1⟩ := by decide
  cases origin with
  | letE valueOrigin bodyOrigin stable =>
  cases valueOrigin with
  | lam valueBodyOrigin =>
  cases valueBodyOrigin with
  | ctor packLookup packArgsOrigin =>
  have packFound : packSignature.findDataCtor "Pack" = some packScheme :=
    by decide
  rw [packFound] at packLookup
  injection packLookup with pinnedPack
  subst pinnedPack
  cases packArgsOrigin with
  | cons packArgOrigin packArgsNil =>
  cases packArgOrigin with
  | mk xOrigin valueAligned =>
  cases xOrigin with
  | var xLookup =>
  simp [initial, Context.find?] at xLookup
  subst_vars
  cases packArgsNil with
  | nil =>
  cases valueAligned with
  | productMatcherLift rawProduct _ _ =>
      rw [InferenceBase.instantiateNamedScheme_mono_value, Subst.apply_id]
        at rawProduct
      nomatch rawProduct
  | slotTupleLift _ _ expectedSlot _ _ =>
      simp [initial, packScheme] at expectedSlot
  | matcherToSlot _ expectedSlot _ =>
      simp [initial, packScheme] at expectedSlot
  | slotToSlot rawSlot _ _ _ =>
      rw [InferenceBase.instantiateNamedScheme_mono_value, Subst.apply_id]
        at rawSlot
      nomatch rawSlot
  | ordinary valueClass valueTypeAligned =>
  change DDAlignTypesWithLedger _ Subst.id (.var 1)
    (.matcher (.var ⟨1⟩) (.var 2)) _ at valueTypeAligned
  cases valueTypeAligned with
  | matcherPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      nomatch leftView
  | slotPair leftView _ _ _ =>
      rw [Subst.apply_id] at leftView
      nomatch leftView
  | @ordinary valueDelta valuePairClass valueSafe =>
  have canonicalUnifies :
      (Subst.mk CapSubst.id
          (Unification.TySubst.single 1
            (.matcher (.var ⟨1⟩) (.var 2)))).apply (.var 1) =
        (Subst.mk CapSubst.id
          (Unification.TySubst.single 1
            (.matcher (.var ⟨1⟩) (.var 2)))).apply
          (.matcher (.var ⟨1⟩) (.var 2)) :=
    (ExactPairedMGU.varLeft 1 (.matcher (.var ⟨1⟩) (.var 2))
      (by decide)).1.1
  obtain ⟨valueCap, valueCapImage⟩ :=
    valueSafe.exact.1.cap_image_var_of_fixing_unifier canonicalUnifies
      (varId := ⟨1⟩) rfl
  have valueEquation := valueSafe.exact.1.1
  rw [Subst.apply_id, Subst.apply_id] at valueEquation
  have valueDomainView :
      valueDelta.apply (.var 1) =
        .matcher (.var valueCap) (valueDelta.apply (.var 2)) := by
    simpa only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
      Cap.apply, valueCapImage] using valueEquation
  have valueCapBinder : valueCap ∈
      (packSignature.generalize
        (Context.applySubst (Subst.seq valueDelta Subst.id) letCapContext)
        ((Subst.seq valueDelta Subst.id).apply
          (.fn (.var 1) (.data "Packed" [])))).capBinders := by
    apply mem_generalize_capBinders
    · rw [Subst.seq_apply, Subst.apply_id]
      change valueCap ∈
        (Ty.fn (valueDelta.apply (.var 1))
          (valueDelta.apply (.data "Packed" []))).fcv
      rw [valueDomainView]
      simp [Ty.fcv, Cap.fcv]
    · intro inEnvironment
      rw [List.mem_append] at inEnvironment
      rcases inEnvironment with inSignature | inContext
      · simp [AcceptanceGapRegression.packSignature, FrozenSig.fcv,
          packScheme, CtorScheme.fcv, Ty.fcvList, Ty.fcv, Cap.fcv]
          at inSignature
      · change valueCap ∈
          (NamedScheme.mono
            (valueDelta.apply (.matcher (.con "c" []) .int))).fcv
          at inContext
        simp [NamedScheme.fcv, NamedScheme.mono, Ty.fcv, Cap.apply, Cap.applyList,
          Cap.fcv, Cap.fcvList] at inContext
  cases bodyOrigin with
  | tuple componentsOrigin =>
  cases componentsOrigin with
  | cons firstOrigin restOrigin =>
  cases restOrigin with
  | cons secondOrigin nilOrigin =>
  cases firstOrigin with
  | app firstFunctionOrigin firstAligned firstArgumentOrigin =>
  cases firstFunctionOrigin with
  | @var firstQ firstS firstContext firstName firstScheme firstLedger
      firstLookup =>
  simp [Context.applySubst, Context.find?] at firstLookup
  subst_vars
  have valueCapBinder' : valueCap ∈
      (packSignature.generalize (Context.applySubst valueDelta letCapContext)
        (valueDelta.apply (.fn (.var 1) (.data "Packed" [])))).capBinders := by
    simpa [Subst.seq_apply] using valueCapBinder
  let generalized := packSignature.generalize
    (Context.applySubst valueDelta letCapContext)
    (valueDelta.apply (.fn (.var 1) (.data "Packed" [])))
  let firstScheme := generalized.applySubst valueDelta
  let firstSupply : InferenceBase.FreshSupply := ⟨2, 3⟩
  let firstPostSupply :=
    (InferenceBase.instantiateNamedScheme firstSupply firstScheme).supply
  let preLookupLedger :=
    DDLedger.freezeExport
      (DDLedger.markSchemeInstance
        (DDLedger.markCtorInstance [] ⟨1, 2⟩ packScheme)
        ⟨2, 3⟩ (NamedScheme.mono (.var 1)))
      valueDelta
      (Inference.freshCapImages ⟨1, 2⟩ packScheme.capBinders)
      (InferenceBase.instantiateCtorScheme ⟨1, 2⟩ packScheme).value.2
  have instanceView :=
    SchemeInstanceCapOccurrenceView.ofGeneralizedBinder
      preLookupLedger firstSupply packSignature
      (Context.applySubst valueDelta letCapContext)
      (valueDelta.apply (.fn (.var 1) (.data "Packed" [])))
      valueDelta valueCapBinder'
  have generalizedBody : generalized.body =
      .fn (.matcher (.var valueCap) (valueDelta.apply (.var 2)))
        (.data "Packed" []) := by
    change valueDelta.apply (.fn (.var 1) (.data "Packed" [])) = _
    rw [Subst.apply_fn, valueDomainView]
    rfl
  have firstSchemeBody : firstScheme.body =
      .fn (.matcher (.var valueCap)
        ((Subst.mk (valueDelta.cap.mask generalized.capBinders)
          (valueDelta.target.mask generalized.tyBinders)).apply
            (valueDelta.apply (.var 2))))
        ((Subst.mk (valueDelta.cap.mask generalized.capBinders)
          (valueDelta.target.mask generalized.tyBinders)).apply
            (.data "Packed" [])) := by
    exact NamedScheme.applySubst_body_fnMatcherView_of_bound generalized
      valueDelta valueCapBinder' generalizedBody
  have instantiatedView :=
    instanceView.toSchemeInstanceCapView.value_fnMatcherView firstSchemeBody
  let firstImage : CapVar := ⟨firstSupply.nextCap + valueCap.id⟩
  have firstImageNe : firstImage ≠ ⟨1⟩ := by
    intro equality
    have ids := congrArg CapVar.id equality
    simp [firstImage, firstSupply] at ids
    omega
  have valueDeltaFixesFirstImage : valueDelta.cap firstImage =
      .var firstImage := by
    apply valueSafe.exact.2.1
    simpa [Subst.apply_id, Ty.fcv, Cap.fcv] using firstImageNe
  have resolvedInstance :
      valueDelta.apply
          (InferenceBase.instantiateNamedScheme firstSupply firstScheme).value =
        .fn
          (.matcher (.var firstImage)
            (valueDelta.apply
              ((InferenceBase.instantiateNamedScheme firstSupply firstScheme).subst.apply
                ((Subst.mk (valueDelta.cap.mask generalized.capBinders)
                  (valueDelta.target.mask generalized.tyBinders)).apply
                    (valueDelta.apply (.var 2))))))
          (valueDelta.apply
            ((InferenceBase.instantiateNamedScheme firstSupply firstScheme).subst.apply
              ((Subst.mk (valueDelta.cap.mask generalized.capBinders)
                (valueDelta.target.mask generalized.tyBinders)).apply
                  (.data "Packed" [])))) := by
    rw [instantiatedView]
    change Ty.fn
      (Ty.matcher
        (((Cap.var firstImage).apply
          valueDelta.cap)) _)
      _ = _
    rw [show (Cap.var firstImage).apply
      valueDelta.cap = .var firstImage from valueDeltaFixesFirstImage]
    simp [firstScheme]
    constructor <;> rfl
  simp only [initial, InferenceBase.instantiateNamedScheme_mono_supply]
    at firstAligned
  simp [packScheme] at firstAligned
  change DDAlignTypesWithLedger
    (DDLedger.markSchemeInstance preLookupLedger firstSupply firstScheme)
    valueDelta
    (InferenceBase.instantiateNamedScheme firstSupply firstScheme).value
    (.fn (.var firstPostSupply.nextTy)
      (.var (firstPostSupply.nextTy + 1))) _
    at firstAligned
  cases firstAligned with
  | matcherPair leftView _ _ _ =>
      rw [resolvedInstance] at leftView
      nomatch leftView
  | slotPair leftView _ _ _ =>
      rw [resolvedInstance] at leftView
      nomatch leftView
  | @ordinary functionDelta functionClass functionSafe =>
  have functionEquation := functionSafe.exact.1.1
  rw [resolvedInstance] at functionEquation
  injection functionEquation with domainEquation codomainEquation
  have firstImageOrigin := instanceView.markedOrigin
  rcases functionSafe.admissible.cap.renameOnly firstImageOrigin with
    ⟨renamedImage, renamedEquation, renamedNonStructural⟩
  have expectedDomainView :
      (Subst.seq functionDelta valueDelta).apply
          (.var firstPostSupply.nextTy) =
        .matcher (.var renamedImage)
          (functionDelta.apply
            (valueDelta.apply
              ((InferenceBase.instantiateNamedScheme firstSupply firstScheme).subst.apply
                ((Subst.mk (valueDelta.cap.mask generalized.capBinders)
                  (valueDelta.target.mask generalized.tyBinders)).apply
                    (valueDelta.apply (.var 2)))))) := by
    rw [Subst.seq_apply]
    have domainEquation' := domainEquation.symm
    simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget, Cap.apply]
      at domainEquation'
    rw [renamedEquation] at domainEquation'
    simpa only [Subst.apply, Ty.applyCapability,
      Ty.applyTarget, Cap.apply] using domainEquation'
  cases firstArgumentOrigin with
  | mk somethingOrigin firstArgumentAligned =>
  cases somethingOrigin with
  | something =>
  have rawSomethingView :
      (Subst.seq functionDelta valueDelta).apply
          (.matcher .any
            (.var
              { firstPostSupply with
                nextTy := firstPostSupply.nextTy + 2 }.nextTy)) =
        .matcher .any
          ((Subst.seq functionDelta valueDelta).apply
            (.var
              { firstPostSupply with
                nextTy := firstPostSupply.nextTy + 2 }.nextTy)) :=
    rfl
  exact firstArgumentAligned.not_of_any_nonStructuralMatcher
    rawSomethingView expectedDomainView renamedNonStructural

/-- The second use structures its own fresh instance capability to
`con "c" []`: two divergent structural solves of the same generalized
capability binder. -/
theorem letCapUse2_ddSynth :
    DDSynth packSignature ⟨4, 9⟩ letCapStructure1 letCapBodyContext
      (.app (.var "f") (.var "m2")) (.var 13) ⟨6, 14⟩ letCapTerminal := by
  exact DDSynth.app (q₁ := ⟨6, 12⟩) (S₁ := letCapStructure1)
    (S₂ := letCapFn2)
    (functionTarget := .fn (.matcher (.var ⟨5⟩) (.var 11)) (.data "Packed" []))
    (DDSynth.var (scheme := letCapScheme) rfl)
    (.ordinary rfl (ExactPairedMGU.fnFresh (.matcher (.var ⟨5⟩) (.var 11))
      (.data "Packed" []) 12 13 (by decide) (by decide) (by decide)
      (by decide) (by decide)))
    (.mk (DDSynth.var
        (scheme := NamedScheme.mono (.matcher (.con "c" []) .int)) rfl)
      (.ordinary rfl (.matcherPair rfl rfl
        (ExactCapMGU.varRight (.con "c" []) ⟨5⟩ (by decide))
        (ExactPairedMGU.varRight .int 11 (by decide)))))

/-- `something` typed at any matcher-headed type has capability `Any`. -/
theorem something_matcher_cap {context : Context} {published : Ty}
    (typing : RuntimeTyping packSignature context .something published)
    {capability : Cap} {target : Ty}
    (headEq : published = .matcher capability target) :
    capability = .any := by
  cases typing with
  | something =>
      injection headEq with capEq _
      exact capEq.symm
  | coerceProductMatcher premise => cases premise
  | coerceMatcherToSlot _ _ => nomatch headEq
  | coerceSlotTuple _ => nomatch headEq

/-- The seeded monomorphic consumer typed at any matcher-headed type has
capability `con "c" []`. -/
theorem m2var_matcher_cap {context : Context} {published : Ty}
    (contextFind :
      context.find? "m2" = some (NamedScheme.mono (.matcher (.con "c" []) .int)))
    (typing : RuntimeTyping packSignature context (.var "m2") published)
    {capability : Cap} {target : Ty}
    (headEq : published = .matcher capability target) :
    capability = .con "c" [] := by
  cases typing with
  | var find inst =>
      rename_i scheme
      have pinned : some scheme =
          some (NamedScheme.mono (.matcher (.con "c" []) .int)) :=
        find.symm.trans contextFind
      injection pinned with pinned
      subst pinned
      exact congrArg (fun τ => match τ with
        | Ty.matcher head _ => head
        | _ => Cap.any) (headEq.symm.trans inst.mono_eq)
  | coerceProductMatcher premise =>
      cases premise with
      | var find inst =>
          rename_i scheme
          have pinned : some scheme =
              some (NamedScheme.mono (.matcher (.con "c" []) .int)) :=
            find.symm.trans contextFind
          injection pinned with pinned
          subst pinned
          nomatch inst.mono_eq
  | coerceMatcherToSlot _ _ => nomatch headEq
  | coerceSlotTuple _ => nomatch headEq

/-- Any runtime certificate for the value body `Pack x` forces the λ domain
to be matcher-headed or a product of matchers: coercion wrappers only move
the published head, never the domain constraint. -/
theorem packCtor_domain_shape {domain : Ty} :
    ∀ {context : Context} {expression : Expr} {published : Ty},
      RuntimeTyping packSignature context expression published →
      expression = .ctor "Pack" [.var "x"] →
      context.find? "x" = some (NamedScheme.mono domain) →
      (∃ capability target, domain = .matcher capability target) ∨
        (∃ duals : List Dual,
          domain = .prod (duals.map fun dual =>
            .matcher dual.cap dual.target))
  | _, _, _, .ctor find inst args, exprEq, contextFind => by
      rename_i targets scheme
      injection exprEq with nameEq exprsEq
      subst nameEq
      subst exprsEq
      have pinned : some scheme = some packScheme := find.symm.trans rfl
      injection pinned with pinned
      subst pinned
      obtain ⟨C, T, _, _, argsEq, _⟩ := inst
      cases args with
      | cons argTyping argsNil =>
      rename_i argTarget restTargets
      injection argsEq with headEq _
      have headEq' : argTarget =
          .matcher (C 0) (((Ty.var 0).applyCapability C).applyTarget T) :=
        headEq.symm
      cases argTyping with
      | var findX instX =>
          rename_i schemeX
          have pinnedX : some schemeX = some (NamedScheme.mono domain) :=
            findX.symm.trans contextFind
          injection pinnedX with pinnedX
          subst pinnedX
          exact Or.inl ⟨_, _, instX.mono_eq.symm.trans headEq'⟩
      | coerceProductMatcher premise =>
          cases premise with
          | var findX instX =>
              rename_i schemeX
              have pinnedX : some schemeX = some (NamedScheme.mono domain) :=
                findX.symm.trans contextFind
              injection pinnedX with pinnedX
              subst pinnedX
              exact Or.inr ⟨_, instX.mono_eq.symm⟩
      | coerceMatcherToSlot _ _ => nomatch headEq'
      | coerceSlotTuple _ => nomatch headEq'
  | _, _, _, .coerceMatcherToSlot premise _, exprEq, contextFind =>
      packCtor_domain_shape premise exprEq contextFind
  | _, _, _, .coerceProductMatcher premise, exprEq, contextFind =>
      packCtor_domain_shape premise exprEq contextFind
  | _, _, _, .coerceSlotTuple premise, exprEq, contextFind =>
      packCtor_domain_shape premise exprEq contextFind
  | _, _, _, .var _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .lam _, exprEq, _ => nomatch exprEq
  | _, _, _, .app _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .letE _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .fixE _ _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .lit, exprEq, _ => nomatch exprEq
  | _, _, _, .tuple _, exprEq, _ => nomatch exprEq
  | _, _, _, .prim _ _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .something, exprEq, _ => nomatch exprEq
  | _, _, _, .matchAll _ _ _ _, exprEq, _ => nomatch exprEq
  | _, _, _, .matcher _ _ _ _ _ _ _, exprEq, _ => nomatch exprEq

/-- The two divergent uses admit no runtime certificate: no λ-domain choice
serves both an `Any`-capped and a `con`-capped consumer under the
variable-only value-flow condition. -/
theorem letCapFreezeProgram_not_runtimeTyping :
    ¬ RuntimeTyping packSignature letCapContext letCapFreezeProgram
      (.prod [.data "Packed" [], .data "Packed" []]) := by
  intro typing
  cases typing with
  | letE hvalue hbody =>
  cases hbody with
  | tuple hcomponents =>
  cases hcomponents with
  | cons hfirst hrest =>
  cases hrest with
  | cons hsecond hnil =>
  cases hfirst with
  | app hfun1 harg1 =>
  cases hfun1 with
  | var hfind1 hinst1 =>
  rename_i domain1 scheme1
  have pinned1 :
      some scheme1 = some (packSignature.generalize letCapContext _) :=
    hfind1.symm.trans rfl
  injection pinned1 with pinned1
  subst pinned1
  obtain ⟨C₁, T₁, inst1⟩ := hinst1
  cases hsecond with
  | app hfun2 harg2 =>
  cases hfun2 with
  | var hfind2 hinst2 =>
  rename_i domain2 scheme2
  have pinned2 :
      some scheme2 = some (packSignature.generalize letCapContext _) :=
    hfind2.symm.trans rfl
  injection pinned2 with pinned2
  subst pinned2
  obtain ⟨C₂, T₂, inst2⟩ := hinst2
  cases hvalue with
  | lam hlamBody =>
    rename_i domain codomain
    rcases packCtor_domain_shape hlamBody rfl rfl with
      ⟨dc, dt, rfl⟩ | ⟨duals, rfl⟩
    · -- matcher-headed domain: the two instances force divergent caps
      have valueEq1 := inst1.result
      injection valueEq1 with domainEq1 _
      have headForm1 :
          Ty.matcher (dc.apply C₁) ((dt.applyCapability C₁).applyTarget T₁) =
            domain1 := domainEq1
      have valueEq2 := inst2.result
      injection valueEq2 with domainEq2 _
      have headForm2 :
          Ty.matcher (dc.apply C₂) ((dt.applyCapability C₂).applyTarget T₂) =
            domain2 := domainEq2
      have cap1 : dc.apply C₁ = .any :=
        something_matcher_cap harg1 headForm1.symm
      have cap2 : dc.apply C₂ = .con "c" [] :=
        m2var_matcher_cap rfl harg2 headForm2.symm
      cases dc with
      | any => nomatch cap2
      | var κ =>
          have binderMem :
              κ ∈ (packSignature.generalize letCapContext
                (.fn (.matcher (.var κ) dt) codomain)).capBinders := by
            apply mem_generalize_capBinders
            · simp [Ty.fcv, Cap.fcv]
            · exact fun h => nomatch h
          obtain ⟨image, imageEq⟩ := inst1.capBinderVariable κ binderMem
          have capVar1 : C₁ κ = Cap.any := cap1
          nomatch imageEq.symm.trans capVar1
      | skolem _ => nomatch cap1
      | con _ _ => nomatch cap1
      | prod _ => nomatch cap1
    · -- product-of-matchers domain: `something` has no product typing
      have valueEq1 := inst1.result
      injection valueEq1 with domainEq1 _
      rw [← domainEq1] at harg1
      cases harg1
  | coerceMatcherToSlot _ _ => nomatch inst1.result
  | coerceProductMatcher _ => nomatch inst1.result
  | coerceSlotTuple _ => nomatch inst1.result

/-! ## Pattern layer: the or-pattern `matchAll` program

The same or-pattern program whose executable acceptance is pinned by
`AcceptanceGapRegression.orProgram_accepted` carries a demand-directed
derivation: both alternatives allocate independent capability/target metas
for `x`, dual alignment unifies them, binding alignment matches the binder
by name, the match-target alignment resolves the shared binder target to
`Int`, and the `something` matcher expression meets the pattern's slot
expectation through the one-way producer-to-slot solution. -/

/-- Prevailing substitution after the or-alternative capability alignment. -/
def orCapAlign : Subst :=
  Subst.seq ⟨Unification.CapSubst.single ⟨0⟩ (.var ⟨1⟩), TySubst.id⟩ Subst.id

/-- Prevailing substitution after the or-alternative target alignment. -/
def orDualAlign : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 0 (.var 1)⟩ orCapAlign

/-- Prevailing substitution after the or binding alignment: the binder types
are already shared, so the delta is an identity solve. -/
def orBindingsAlign : Subst := Subst.seq Subst.id orDualAlign

/-- Prevailing substitution after the match-target alignment. -/
def orTargetAlign : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 1 .int⟩ orBindingsAlign

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
  Subst.seq ⟨orOneWayCap, Unification.TySubst.single 2 .int⟩ orTargetAlign

def orPatternLedger₁ : CapabilityOriginLedger :=
  DDLedger.markFreshCap [] ⟨0, 0⟩

def orPatternLedger₂ : CapabilityOriginLedger :=
  DDLedger.markFreshCap orPatternLedger₁ ⟨1, 1⟩

theorem orLeft_ddPattern :
    DDPattern emptySignature ⟨0, 0⟩ Subst.id [] [] [] (.pvar "x")
      ⟨.var ⟨0⟩, .var 0⟩ [("x", .var 0)] ⟨1, 1⟩ Subst.id :=
  .pvar (by simp [MonoCtx.names])

theorem orLeft_ddPatternOrigin :
    DDPatternOrigin emptySignature orLeft_ddPattern [] orPatternLedger₁ :=
  DDPatternOrigin.pvar (signature := emptySignature) (q := ⟨0, 0⟩)
    (S := Subst.id) (context := []) (parameters := []) (bindings := [])
      (ledger := []) (by simp [MonoCtx.names])

theorem orRight_ddPattern :
    DDPattern emptySignature ⟨1, 1⟩ Subst.id [] [] [] (.pvar "x")
      ⟨.var ⟨1⟩, .var 1⟩ [("x", .var 1)] ⟨2, 2⟩ Subst.id :=
  .pvar (by simp [MonoCtx.names])

theorem orRight_ddPatternOrigin :
    DDPatternOrigin emptySignature orRight_ddPattern orPatternLedger₁
      orPatternLedger₂ :=
  DDPatternOrigin.pvar (signature := emptySignature) (q := ⟨1, 1⟩)
    (S := Subst.id) (context := []) (parameters := []) (bindings := [])
      (ledger := orPatternLedger₁) (by simp [MonoCtx.names])

/-- The or pattern synthesizes the left alternative's dual: independent
fresh metas per alternative, dual alignment across the alternatives, and
positional binding alignment on the shared binder name. -/
theorem orPattern_ddPattern :
    DDPattern emptySignature ⟨0, 0⟩ Subst.id [] [] []
      (.por (.pvar "x") (.pvar "x")) ⟨.var ⟨0⟩, .var 0⟩ [("x", .var 0)]
      ⟨2, 2⟩ orBindingsAlign := by
  refine DDPattern.por (S₃ := orDualAlign)
    (.pvar (by simp [MonoCtx.names]))
    (.pvar (by simp [MonoCtx.names])) ?_ ?_
  · exact .mk (ExactCapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide))
      (.ordinary rfl (ExactPairedMGU.varLeft 0 (.var 1) (by decide)))
  · exact .cons rfl (.ordinary rfl (ExactPairedMGU.refl (.var 1))) .nil

theorem orPattern_ddPatternOrigin :
    DDPatternOrigin emptySignature orPattern_ddPattern [] orPatternLedger₂ := by
  refine DDPatternOrigin.por (S₃ := orDualAlign)
    orLeft_ddPatternOrigin orRight_ddPatternOrigin ?_ ?_
  · exact .mk (S := Subst.id) (left := ⟨.var ⟨0⟩, .var 0⟩)
      (right := ⟨.var ⟨1⟩, .var 1⟩)
      ⟨ExactCapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide),
        PairedUnification.admissible_single_structuralFlexible
          orPatternLedger₂ ⟨0⟩ (.var ⟨1⟩) (by
            simp [orPatternLedger₂, orPatternLedger₁,
              DDLedger.markFreshCap])⟩
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.varLeft 0 (.var 1) (by decide))))
  · exact .cons (S := orDualAlign)
      (left := ("x", Ty.var 0)) (right := ("x", Ty.var 1)) rfl
      (.ordinary rfl (originSafePairedCapId orPatternLedger₂
        (ExactPairedMGU.refl (.var 1)))) .nil

/-- Raw synthesis of the or-pattern program at the initial supply. -/
theorem orProgram_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      AcceptanceGapRegression.orProgram (Ty.listT .int) ⟨2, 3⟩ orTerminal := by
  refine DDSynth.matchAll (S₃ := orTargetAlign) (q₃ := ⟨2, 3⟩)
    (S₄ := orTerminal) .lit orPattern_ddPattern ?_ ?_ ?_
  · exact .ordinary rfl (ExactPairedMGU.varLeft 1 .int (by decide))
  · exact .mk .something (.matcherToSlot rfl rfl
      ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
        ExactTargetMGU.varLeft 2 .int (by decide)⟩)
  · exact DDSynth.var (scheme := NamedScheme.mono .int) rfl

theorem orMatcher_ddCheck :
    DDCheck emptySignature ⟨2, 2⟩ orTargetAlign [] .something
      (.slot (.var ⟨0⟩) .int) ⟨2, 3⟩ orTerminal := by
  exact .mk .something (.matcherToSlot rfl rfl
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 2 .int (by decide)⟩)

theorem orMatcher_ddCheckOrigin :
    DDCheckOrigin emptySignature orMatcher_ddCheck orPatternLedger₂
      orPatternLedger₂ := by
  refine .mk (synthesized := DDSynth.something (signature := emptySignature)
    (q := ⟨2, 2⟩) (S := orTargetAlign) (Γ := [])) .something ?_
  exact .matcherToSlot rfl rfl ⟨
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 2 .int (by decide)⟩,
    ⟨by
      rw [orOneWayCap_eq_single]
      exact PairedUnification.admissible_single_structuralFlexible
        orPatternLedger₂ ⟨1⟩ .any (by
          simp [orPatternLedger₂, DDLedger.markFreshCap])⟩⟩

theorem orBody_ddSynth :
    DDSynth emptySignature ⟨2, 3⟩ orTerminal
      [("x", NamedScheme.mono (.var 0))] (.var "x") .int ⟨2, 3⟩
      orTerminal := by
  simpa [InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyTarget, Cap.apply, NamedScheme.mono] using
    (DDSynth.var (signature := emptySignature) (q := ⟨2, 3⟩)
      (S := orTerminal) (Γ := [("x", NamedScheme.mono (.var 0))])
      (scheme := NamedScheme.mono .int) rfl)

theorem orBody_ddSynthOrigin :
    DDSynthOrigin emptySignature orBody_ddSynth orPatternLedger₂
      orPatternLedger₂ := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages,
    NamedScheme.mono, CapabilityOriginLedger.setOrigins,
    InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyTarget, Cap.apply] using
    (DDSynthOrigin.var (signature := emptySignature)
      (ledger := orPatternLedger₂) (q := ⟨2, 3⟩) (S := orTerminal)
      (context := [("x", NamedScheme.mono (.var 0))])
      (scheme := NamedScheme.mono .int) rfl)

theorem orProgram_ddSynthOrigin :
    DDSynthOrigin emptySignature orProgram_ddSynth [] orPatternLedger₂ := by
  refine .matchAll .lit orPattern_ddPatternOrigin
    (.ordinary rfl (originSafePairedCapId orPatternLedger₂
      (ExactPairedMGU.varLeft 1 .int (by decide))))
    orMatcher_ddCheckOrigin orBody_ddSynthOrigin

/-- The or-pattern program closes at `List Int` in the demand-directed
judgment, mirroring its executable acceptance. -/
theorem orProgram_ddTyping :
    DDTyping emptySignature [] AcceptanceGapRegression.orProgram
      (Ty.listT .int) :=
  ⟨Ty.listT .int, ⟨2, 3⟩, orTerminal, orProgram_ddSynth,
    orPatternLedger₂, orProgram_ddSynthOrigin, rfl⟩

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

theorem delegatingNextHead_ddCheckOrigin :
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

theorem delegatingNext_ddChecksOrigin :
    DDChecksOrigin emptySignature delegatingNext_ddChecks delegatingLedger₀
      delegatingLedger₀ := by
  exact .cons delegatingNextHead_ddCheckOrigin .nil

theorem delegatingInnerPattern_ddPattern :
    DDPattern emptySignature ⟨1, 2⟩ delegatingCheck1
      [("v", NamedScheme.mono (.var 0))] [] [] (.pvar "y")
      ⟨.var ⟨1⟩, .var 2⟩ [("y", .var 2)] ⟨2, 3⟩
      delegatingCheck1 :=
  .pvar (by simp [MonoCtx.names])

theorem delegatingInnerPattern_ddPatternOrigin :
    DDPatternOrigin emptySignature delegatingInnerPattern_ddPattern
      delegatingLedger₀ delegatingLedger₁ :=
  DDPatternOrigin.pvar (signature := emptySignature) (q := ⟨1, 2⟩)
    (S := delegatingCheck1)
    (context := [("v", NamedScheme.mono (.var 0))]) (parameters := [])
    (bindings := []) (ledger := delegatingLedger₀)
      (by simp [MonoCtx.names])

theorem delegatingInnerMatcher_ddCheck :
    DDCheck emptySignature ⟨2, 3⟩ delegatingInner1
      [("v", NamedScheme.mono (.var 0))] .something
      (.slot (.var ⟨1⟩) .int) ⟨2, 4⟩ delegatingInner2 := by
  exact .mk .something (.matcherToSlot rfl rfl
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩)

theorem delegatingInnerMatcher_ddCheckOrigin :
    DDCheckOrigin emptySignature delegatingInnerMatcher_ddCheck
      delegatingLedger₁ delegatingLedger₁ := by
  refine .mk (synthesized := DDSynth.something (signature := emptySignature)
    (q := ⟨2, 3⟩) (S := delegatingInner1)
    (Γ := [("v", NamedScheme.mono (.var 0))])) .something ?_
  exact .matcherToSlot rfl rfl ⟨
    ⟨[(⟨1⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 3 .int (by decide)⟩,
    ⟨by
      rw [delegatingInnerCap_eq_single]
      exact PairedUnification.admissible_single_structuralFlexible
        delegatingLedger₁ ⟨1⟩ .any (by
          simp [delegatingLedger₁, DDLedger.markFreshCap])⟩⟩

theorem delegatingInnerBodyVar_ddSynth :
    DDSynth emptySignature ⟨2, 4⟩ delegatingInner2
      [("y", NamedScheme.mono (.var 2)), ("v", NamedScheme.mono (.var 0))]
      (.var "y") .int ⟨2, 4⟩ delegatingInner2 := by
  simpa [InferenceBase.instantiateNamedScheme, InferenceBase.instantiateBinders,
    InferenceBase.freshCapSubst, InferenceBase.freshTySubst,
    InferenceBase.binderSpan, Subst.apply, Ty.applyCapability,
    Ty.applyTarget, Cap.apply, NamedScheme.mono] using
    (DDSynth.var (signature := emptySignature) (q := ⟨2, 4⟩)
      (S := delegatingInner2)
      (Γ := [("y", NamedScheme.mono (.var 2)), ("v", NamedScheme.mono (.var 0))])
      (scheme := NamedScheme.mono .int) rfl)

theorem delegatingInnerBodyVar_ddSynthOrigin :
    DDSynthOrigin emptySignature delegatingInnerBodyVar_ddSynth
      delegatingLedger₁ delegatingLedger₁ := by
  simpa [DDLedger.markSchemeInstance, Inference.freshCapImages,
    CapabilityOriginLedger.setOrigins, InferenceBase.instantiateNamedScheme,
    InferenceBase.instantiateBinders, InferenceBase.freshCapSubst,
    InferenceBase.freshTySubst, InferenceBase.binderSpan, Subst.apply,
    Ty.applyCapability, Ty.applyTarget, Cap.apply, NamedScheme.mono] using
    (DDSynthOrigin.var (signature := emptySignature)
      (ledger := delegatingLedger₁) (q := ⟨2, 4⟩)
      (S := delegatingInner2)
      (context := [("y", NamedScheme.mono (.var 2)),
        ("v", NamedScheme.mono (.var 0))])
      (scheme := NamedScheme.mono .int) rfl)

theorem delegatingBody_ddSynth :
    DDSynth emptySignature ⟨1, 2⟩ delegatingCheck1
      [("v", NamedScheme.mono (.var 0))] delegatingBody (Ty.listT .int)
      ⟨2, 4⟩ delegatingInner2 := by
  exact DDSynth.matchAll (S₃ := delegatingInner1) (q₃ := ⟨2, 4⟩)
    (S₄ := delegatingInner2) .lit delegatingInnerPattern_ddPattern
    (.ordinary rfl (ExactPairedMGU.varLeft 2 .int (by decide)))
    delegatingInnerMatcher_ddCheck delegatingInnerBodyVar_ddSynth

theorem delegatingBody_ddSynthOrigin :
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
      [("v", NamedScheme.mono (.var 0))] delegatingBody (Ty.listT (.var 0))
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
    · exact DDSynth.var (scheme := NamedScheme.mono .int) rfl
  · exact .ordinary rfl (.ordinary rfl delegating_bodyMGU_exact)

theorem delegatingBody_ddCheckOrigin :
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

theorem delegatingArms_ddArmsOrigin :
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

theorem delegatingClause_ddClauseOrigin :
    DDClauseOrigin emptySignature delegatingClause_ddClause []
      delegatingLedger₁ :=
  .mk .hole rfl delegatingNext_ddChecksOrigin delegatingArms_ddArmsOrigin

theorem delegatingClauses_ddClauses :
    DDClauses emptySignature ⟨0, 1⟩ Subst.id []
      [.mk .hole .something [.mk (.var "v") delegatingBody]] (.var 0)
      [[⟨.var ⟨0⟩, .var 0⟩]] ⟨2, 4⟩ delegatingTerminal :=
  .cons delegatingClause_ddClause .nil

theorem delegatingClauses_ddClausesOrigin :
    DDClausesOrigin emptySignature delegatingClauses_ddClauses []
      delegatingLedger₁ :=
  .cons delegatingClause_ddClauseOrigin .nil

theorem delegatingMatcher_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] delegatingMatcher
      (.matcher .any (.var 0)) ⟨2, 4⟩ delegatingTerminal := by
  exact DDSynth.matcher (evidence := [.unseen]) (capability := .any)
    delegatingClauses_ddClauses rfl rfl rfl rfl rfl rfl rfl

theorem delegatingMatcher_ddSynthOrigin :
    DDSynthOrigin emptySignature delegatingMatcher_ddSynth []
      delegatingLedger₁ := by
  simpa [delegatingMatcher, DDLedger.freezeMatcherProducer,
    DDLedger.matcherProducerLeaves,
    Cap.fcv, CapabilityOriginLedger.setOrigins] using
    (DDSynthOrigin.matcher (signature := emptySignature)
      (evidence := [.unseen]) (capability := .any)
      delegatingClauses_ddClausesOrigin rfl rfl rfl rfl rfl rfl rfl)

/-- The delegating matcher literal closes at `Matcher Any Int` through the
demand-directed judgment, its finalization discharged by the same executable
coverage checks the executable traversal consumes. -/
theorem delegatingMatcher_ddTyping :
    DDTyping emptySignature [] delegatingMatcher (.matcher .any .int) := by
  exact ⟨.matcher .any (.var 0), ⟨2, 4⟩, delegatingTerminal,
    delegatingMatcher_ddSynth, delegatingLedger₁,
    delegatingMatcher_ddSynthOrigin, rfl⟩

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
