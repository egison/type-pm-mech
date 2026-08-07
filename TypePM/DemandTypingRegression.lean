import TypePM.DemandTyping
import TypePM.CertifiedInferenceRegression
import TypePM.AcceptanceGapRegression

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
    PairedMGU (.fn (.var 0) (.var 0)) (.fn (.var 1) (.var 2))
      ⟨CapSubst.id, applicationDelta⟩ :=
  PairedMGU.fnDiagonal 0 1 2 (by decide) (by decide) (by decide)

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
      (.ordinary rfl (PairedMGU.varRight .int 1 (by decide)))))

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
    ⟨[], rfl, by rfl, pairTargetDelta_targetMGU⟩

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
  | ordinary _ mgu => nomatch mgu.1

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
      (PairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    (.mk (DDSynth.var (scheme := dmIdScheme) rfl)
      (.ordinary rfl (.ordinary rfl
        (PairedMGU.varRight (.fn (.var 4) (.var 4)) 2 (by decide)))))

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
      (PairedMGU.fnDiagonal 4 5 6 (by decide) (by decide) (by decide)))
    (.mk .lit (.ordinary rfl (.ordinary rfl
      (PairedMGU.varRight .int 5 (by decide)))))

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
      (PairedMGU.fnDiagonal 1 2 3 (by decide) (by decide) (by decide)))
    (.mk .something (.ordinary rfl (.ordinary rfl
      (PairedMGU.varRight (.matcher .any (.var 4)) 2 (by decide)))))

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
      (PairedMGU.fnDiagonal 5 6 7 (by decide) (by decide) (by decide)))
    (.mk (.tuple (.cons .something (.cons .something .nil)))
      (.ordinary rfl (.ordinary rfl
        (PairedMGU.varRight
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
  · exact .mk (CapMGU.varLeft ⟨0⟩ (.var ⟨1⟩) (by decide))
      (.ordinary rfl (PairedMGU.varLeft 0 (.var 1) (by decide)))
  · exact .cons rfl (.ordinary rfl (PairedMGU.refl (.var 1))) .nil

/-- Raw synthesis of the or-pattern program at the initial supply. -/
theorem orProgram_ddSynth :
    DDSynth emptySignature ⟨0, 0⟩ Subst.id []
      AcceptanceGapRegression.orProgram (Ty.listT .int) ⟨2, 3⟩ orTerminal := by
  refine DDSynth.matchAll (S₃ := orTargetAlign) (q₃ := ⟨2, 3⟩)
    (S₄ := orTerminal) .lit orPattern_ddPattern ?_ ?_ ?_
  · exact .ordinary rfl (PairedMGU.varLeft 1 .int (by decide))
  · exact .mk .something (.matcherToSlot rfl rfl
      ⟨[(⟨1⟩, Cap.any)], rfl, rfl, TargetMGU.varLeft 2 .int (by decide)⟩)
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

/-- The next-matcher check: `something` delivers the hole slot one-way. -/
theorem delegatingNext_ddChecks :
    DDChecks emptySignature ⟨1, 1⟩ Subst.id [] [.something]
      [.slot (.var ⟨0⟩) (.var 0)] ⟨1, 2⟩ delegatingCheck1 := by
  refine .cons (.mk .something ?_) .nil
  exact .matcherToSlot rfl rfl
    ⟨[(⟨0⟩, Cap.any)], rfl, rfl, TargetMGU.varLeft 1 (.var 0) (by decide)⟩

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
    · exact .ordinary rfl (PairedMGU.varLeft 2 .int (by decide))
    · exact .mk .something (.matcherToSlot rfl rfl
        ⟨[(⟨1⟩, Cap.any)], rfl, rfl, TargetMGU.varLeft 3 .int (by decide)⟩)
    · exact DDSynth.var (scheme := Scheme.mono .int) rfl
  · exact .ordinary rfl (.ordinary rfl delegating_bodyMGU)

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

end DemandTypingRegression
end TypePM
