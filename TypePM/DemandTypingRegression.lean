import TypePM.DemandTyping
import TypePM.CertifiedInferenceRegression

/-!
# Demand-directed judgment regressions

Concrete inhabitants and refutations for the expression-layer `DDSynth`/
`DDCheck` judgments: a solve-free synthesis, an application whose domain
alignment and argument check each perform one paired solve, a positive
slot-demand coercion of a product of matchers at a slot-headed expectation,
and the align-level refutation showing that the same product admits no
checking cut against a matcher-headed expectation.  The positive/negative
pair pins the slot-demand boundary for the judgment itself, mirroring the
selector-level regressions of `CertifiedInferenceRegression`.
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
def applicationDelta : TySubst := fun candidate =>
  if candidate = 0 then .var 1
  else if candidate = 2 then .var 1
  else .var candidate

theorem applicationDelta_pairedMGU :
    PairedMGU (.fn (.var 0) (.var 0)) (.fn (.var 1) (.var 2))
      ⟨CapSubst.id, applicationDelta⟩ := by
  constructor
  · rfl
  · intro U unifies
    have components :
        Ty.fn (U.target 0) (U.target 0) = Ty.fn (U.target 1) (U.target 2) :=
      unifies
    have headEq : U.target 0 = U.target 1 := by
      injection components
    have tailEq : U.target 0 = U.target 2 := by
      injection components with _ tailEq
    refine ⟨U, congrArg (Subst.mk U.cap) ?_⟩
    funext candidate
    by_cases hzero : candidate = 0
    · subst hzero
      exact headEq
    · by_cases htwo : candidate = 2
      · subst htwo
        simp only [applicationDelta, if_neg hzero]
        exact tailEq.symm.trans headEq
      · simp only [applicationDelta, if_neg hzero, if_neg htwo]
        rfl

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

end DemandTypingRegression
end TypePM
