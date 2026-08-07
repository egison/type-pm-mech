import TypePM.DemandTyping
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

/-! ## Solve-free synthesis -/

/-- `λx. x` with a fresh metavariable domain. -/
def identityExpr : Expr := .lam "x" (.var "x")

/-- The identity function synthesizes its λ domain as a fresh metavariable
and consumes no solve. -/
theorem identity_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id [] identityExpr
      (.fn (.var 0) (.var 0)) ⟨0, 1⟩ Subst.id := by
  exact .lam (DDSynth.var (scheme := Scheme.mono (.var 0)) rfl)

/-- The closed wrapper publishes the identity type unchanged. -/
theorem identity_ddTyping :
    DDTyping emptySignature [] identityExpr (.fn (.var 0) (.var 0)) :=
  ⟨.fn (.var 0) (.var 0), ⟨0, 1⟩, Subst.id, identity_ddSynth, rfl⟩

/-! ## One application: domain alignment and argument solve -/

/-- The most general paired solution of the application-function alignment
`fn ?0 ?0 ≐ fn ?1 ?2`. -/
def applicationDelta : TySubst := fnDiagonalDelta 0 1 2

theorem applicationDelta_pairedMGU :
    ExactPairedMGU (.fn (.var 0) (.var 0)) (.fn (.var 1) (.var 2))
      ⟨CapSubst.id, applicationDelta⟩ :=
  ExactPairedMGU.fnDiagonal 0 1 2 (by decide) (by decide) (by decide)

/-- Terminal substitution of `(λx. x) 1`: the function alignment followed by
the argument solve. -/
def applicationTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 1 .int⟩
    (Subst.seq ⟨CapSubst.id, applicationDelta⟩ Subst.id)

/-- `(λx. x) 1` closes at `Int` through one domain alignment and one
demand-free ordinary argument alignment. -/
theorem application_ddTyping :
    DDTyping emptySignature [] (.app identityExpr (.lit 1)) .int := by
  refine ⟨.var 2, ⟨0, 3⟩, applicationTerminal, ?_, rfl⟩
  exact .app identity_ddSynth
    (.ordinary rfl applicationDelta_pairedMGU)
    (.mk .lit (.ordinary rfl
      (.ordinary rfl (ExactPairedMGU.varRight .int 1 (by decide)))))

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
  refine ⟨pairTargetDelta_targetMGU, ?_, ?_, ?_⟩
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
def dmIdScheme : Scheme := ⟨[], [0], .fn (.var 0) (.var 0)⟩

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
theorem dmInnerApp_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("id", dmIdScheme)]
      (.app (.var "id") (.var "id")) (.var 3) ⟨0, 5⟩ dmInner := by
  exact DDSynth.app (q₁ := ⟨0, 2⟩) (S₁ := Subst.id) (S₂ := dmAlign1)
    (functionTarget := .fn (.var 1) (.var 1))
    (DDSynth.var (scheme := dmIdScheme) rfl)
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    (.mk (DDSynth.var (scheme := dmIdScheme) rfl)
      (.ordinary rfl (.ordinary rfl
        (ExactPairedMGU.varRight (.fn (.var 4) (.var 4)) 2 (by decide)))))

/-- The polymorphic-`let` witness closes at `Int` through the demand-directed
judgment: the `let` rule generalizes the value type in the substituted
context, and each use of `id` instantiates the quantified scheme at a fresh
supply-indexed image. -/
theorem dmLet_ddTyping :
    DDTyping emptySignature [] dmLetProgram .int := by
  refine ⟨.var 6, ⟨0, 7⟩, dmLetTerminal, ?_, rfl⟩
  refine .letE identity_ddSynth ?_
  exact DDSynth.app (q₁ := ⟨0, 5⟩) (S₁ := dmInner) (S₂ := dmAlign2)
    (functionTarget := .var 3)
    dmInnerApp_ddSynth
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 4 5 6 (by decide) (by decide) (by decide)))
    (.mk .lit (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight .int 5 (by decide)))))

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
theorem nestedCapLetFirstApp_ddSynth :
    DDSynth emptySignature ⟨0, 1⟩ Subst.id [("f", dmIdScheme)]
      (.app (.var "f") .something) (.var 3) ⟨0, 5⟩ nestedCapLetCheck1 := by
  exact DDSynth.app (q₁ := ⟨0, 2⟩) (S₁ := Subst.id)
    (S₂ := nestedCapLetAlign1)
    (functionTarget := .fn (.var 1) (.var 1))
    (DDSynth.var (scheme := dmIdScheme) rfl)
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    (.mk .something (.ordinary rfl (.ordinary rfl
      (ExactPairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide)))))

/-- The second use: its own fresh instance `fn ?6 ?7` whose domain receives
the raw product of matcher producers unlifted — a variable expectation is
no slot demand. -/
theorem nestedCapLetSecondApp_ddSynth :
    DDSynth emptySignature ⟨0, 5⟩ nestedCapLetCheck1 [("f", dmIdScheme)]
      (.app (.var "f") (.tuple [.something, .something])) (.var 7) ⟨0, 10⟩
      nestedCapLetTerminal := by
  exact DDSynth.app (q₁ := ⟨0, 6⟩) (S₁ := nestedCapLetCheck1)
    (S₂ := nestedCapLetAlign2)
    (functionTarget := .fn (.var 5) (.var 5))
    (DDSynth.var (scheme := dmIdScheme) rfl)
    (.ordinary rfl
      (ExactPairedMGU.fnDiagonal 5 6 7 (by decide) (by decide) (by decide)))
    (.mk (.tuple (.cons .something (.cons .something .nil)))
      (.ordinary rfl (.ordinary rfl
        (ExactPairedMGU.varRight
          (.prod [.matcher .any (.var 8), .matcher .any (.var 9)]) 6
          (by decide)))))

/-- The `let`-polymorphic pairing of the two producers closes in the
demand-directed judgment at exactly the executable raw result shape. -/
theorem nestedCapLetProgram_ddTyping :
    DDTyping emptySignature [] AcceptanceGapRegression.nestedCapLetProgram
      (.prod [.matcher .any (.var 4),
        .prod [.matcher .any (.var 8), .matcher .any (.var 9)]]) := by
  refine ⟨.prod [.var 3, .var 7], ⟨0, 10⟩, nestedCapLetTerminal, ?_, rfl⟩
  exact .letE (.lam (DDSynth.var (scheme := Scheme.mono (.var 0)) rfl))
    (.tuple (.cons nestedCapLetFirstApp_ddSynth
      (.cons nestedCapLetSecondApp_ddSynth .nil)))

/-! ## The nested-capability boundary: no demand-directed derivation exists

`nestedCapProgram` shares one monomorphic consumer between a bare matcher
producer and a product of matcher producers.  Its wide declarative typings
insert coercions at argument positions with no slot demand
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
      some ((Scheme.mono (Ty.var 0)).applySubst Subst.id) :=
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
      some ((Scheme.mono (Ty.var 0)).applySubst
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

/-! ## Boundary: bare most-generality does not transport value flow

The no-guess theorems bound every most general solve delta to at most a
renaming of variables outside its constraint.  That residual freedom is
already enough to break delta-wise transport of declarative value-flow
instances: a most general solution of `?1 ≐ Int` may additionally swap the
unrelated variables `?3` and `?9`.  If `?9` is the binder of a partially
generalized scheme with `?3` free, the masked scheme substitution captures
— `∀9. 9 → 3` becomes `∀9. 9 → 9` — while the transported instance
`Int → ?9` is no instance of the captured scheme.  This fixes, as a
boundary theorem, why the forgetting map to `HasTy` cannot be proved by
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
def capturedScheme : Scheme := ⟨[], [9], .fn (.var 9) (.var 3)⟩

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
`(Matcher Any ?4, Matcher Any ?4)` is nevertheless not declaratively
derivable: the declarative value-flow instance maps a quantified capability
binder only to a capability *variable*, and every coercion rule that could
retype `m` either concludes at a slot head or carries the violating
instance in its premise.  Unconditional forgetting from `DDTyping` to
`HasTy` over an arbitrary context is therefore false, and the forgetting
theorem of stage 3-2 must carry a freeze-side correspondence condition
(mirroring the `FreezeCompatible` condition of stage 3-3) or the judgment
must gain the ledger axis. -/

/-- A quantified matcher producer: `∀κ α. Matcher κ α`. -/
def producerScheme : Scheme := ⟨[⟨0⟩], [0], .matcher (.var ⟨0⟩) (.var 0)⟩

/-- The seeded context binding the producer. -/
def producerContext : Context := [("m", producerScheme)]

/-- One monomorphic consumer shared between `something` and the producer. -/
def capFreezeProgram : Expr :=
  .app (.lam "h" (.tuple
    [.app (.var "h") .something, .app (.var "h") (.var "m")]))
    (.lam "z" (.var "z"))

/-- The inner context of the consumer body. -/
def capFreezeInnerContext : Context :=
  ("h", Scheme.mono (.var 1)) :: producerContext

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
    (DDSynth.var (scheme := Scheme.mono (.var 1)) rfl)
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
      (scheme := Scheme.mono (.fn (.matcher .any (.var 4)) (.var 3))) rfl)
    (.ordinary rfl (ExactPairedMGU.fnFresh (.matcher .any (.var 4))
      (.var 3) 5 6 (by decide) (by decide) (by decide) (by decide)
      (by decide)))
    (.mk (DDSynth.var (scheme := producerScheme) rfl)
      (.ordinary rfl
        (.matcherPair rfl rfl (ExactCapMGU.varLeft ⟨1⟩ .any (by decide))
          (ExactPairedMGU.varLeft 7 (.var 4) (by decide)))))

/-- The whole program closes in the demand-directed judgment at the
`Any`-capped pair. -/
theorem capFreezeProgram_ddTyping :
    DDTyping emptySignature producerContext capFreezeProgram
      (.prod [.matcher .any (.var 4), .matcher .any (.var 4)]) := by
  refine ⟨.var 9, ⟨2, 11⟩, capFreezeTerminal, ?_, rfl⟩
  exact DDSynth.app (q₁ := ⟨2, 8⟩) (S₁ := capFreezeStructure)
    (S₂ := capFreezeAlign3)
    (functionTarget := .fn (.var 1) (.prod [.var 3, .var 6]))
    (.lam (.tuple (.cons capFreezeFirstApp_ddSynth
      (.cons capFreezeSecondApp_ddSynth .nil))))
    (.ordinary rfl (ExactPairedMGU.fnFresh
      (.fn (.matcher .any (.var 4)) (.var 3)) (.prod [.var 3, .var 3]) 8 9
      (by decide) (by decide) (by decide) (by decide) (by decide)))
    (.mk (.lam (DDSynth.var (scheme := Scheme.mono (.var 10)) rfl))
      (.ordinary rfl (.ordinary rfl
        (ExactPairedMGU.fnSharedFresh 10 (.matcher .any (.var 4)) 3
          (by decide) (by decide) (by decide)))))

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

/-- The published type is not declaratively derivable: the shared
monomorphic consumer forces `m` to inhabit the `Any`-capped matcher type,
which no value-flow instance provides. -/
theorem capFreezeProgram_not_hasTy :
    ¬ HasTy emptySignature producerContext capFreezeProgram
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
  have pinned2 : some scheme2 = some (Scheme.mono outerDomain) :=
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
  have pinnedz : some schemez = some (Scheme.mono _) :=
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

/-- The boundary in one statement: the demand-directed derivation exists,
the declarative typing does not.  Unconditional forgetting over an
arbitrary context is refuted; the stage 3-2 forgetting map must carry a
freeze-side correspondence condition. -/
theorem capFreeze_forgetting_gap :
    DDTyping emptySignature producerContext capFreezeProgram
        (.prod [.matcher .any (.var 4), .matcher .any (.var 4)]) ∧
      ¬ HasTy emptySignature producerContext capFreezeProgram
        (.prod [.matcher .any (.var 4), .matcher .any (.var 4)]) :=
  ⟨capFreezeProgram_ddTyping, capFreezeProgram_not_hasTy⟩

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

/-- Terminal substitution of the or-pattern program. -/
def orTerminal : Subst :=
  Subst.seq ⟨orOneWayCap, Unification.TySubst.single 2 .int⟩ orTargetAlign

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
  · exact DDSynth.var (scheme := Scheme.mono .int) rfl

/-- The or-pattern program closes at `List Int` in the demand-directed
judgment, mirroring its executable acceptance. -/
theorem orProgram_ddTyping :
    DDTyping emptySignature [] AcceptanceGapRegression.orProgram
      (Ty.listT .int) :=
  ⟨Ty.listT .int, ⟨2, 3⟩, orTerminal, orProgram_ddSynth, rfl⟩

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

/-- Prevailing substitution after the inner slot check. -/
def delegatingInner2 : Subst :=
  Subst.seq ⟨delegatingInnerCap, Unification.TySubst.single 3 .int⟩
    delegatingInner1

/-- Terminal substitution of the delegating matcher: the arm-body alignment
resolves the shared matcher target to `Int`. -/
def delegatingTerminal : Subst :=
  Subst.seq ⟨CapSubst.id, Unification.TySubst.single 0 .int⟩ delegatingInner2

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
    tySingle_capRangeWithin (fun image mem => nomatch mem)⟩
  intro candidate outside
  have hne : ¬ (0 : TypePM.TyVar) = candidate := fun h => outside (by
    cases h
    simp [Ty.listT, Ty.ftv, Ty.ftvList])
  simp [Unification.TySubst.single, hne]

/-- The next-matcher check: `something` delivers the hole slot one-way. -/
theorem delegatingNext_ddChecks :
    DDChecks emptySignature ⟨1, 1⟩ Subst.id [] [.something]
      [.slot (.var ⟨0⟩) (.var 0)] ⟨1, 2⟩ delegatingCheck1 := by
  refine .cons (.mk .something ?_) .nil
  exact .matcherToSlot rfl rfl
    ⟨[(⟨0⟩, Cap.any)], rfl, rfl,
      ExactTargetMGU.varLeft 1 (.var 0) (by decide)⟩

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
    · exact DDSynth.var (scheme := Scheme.mono .int) rfl
  · exact .ordinary rfl (.ordinary rfl delegating_bodyMGU_exact)

/-- The single delegating clause: hole against the shared target, one
next-matcher slot check, and one variable arm. -/
theorem delegatingClause_ddClause :
    DDClause emptySignature ⟨0, 1⟩ Subst.id []
      (.mk .hole .something [.mk (.var "v") delegatingBody]) (.var 0)
      [⟨.var ⟨0⟩, .var 0⟩] ⟨2, 4⟩ delegatingTerminal := by
  refine .mk .hole rfl delegatingNext_ddChecks ?_
  exact .cons .var (fun name _ => by simp [MonoCtx.names])
    delegatingBody_ddCheck .nil

/-- The delegating matcher literal closes at `Matcher Any Int` through the
demand-directed judgment, its finalization discharged by the same executable
coverage checks the executable traversal consumes. -/
theorem delegatingMatcher_ddTyping :
    DDTyping emptySignature [] delegatingMatcher (.matcher .any .int) := by
  refine ⟨.matcher .any (.var 0), ⟨2, 4⟩, delegatingTerminal, ?_, rfl⟩
  exact DDSynth.matcher (evidence := [.unseen]) (capability := .any)
    (.cons delegatingClause_ddClause .nil) rfl rfl rfl rfl rfl rfl rfl

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
