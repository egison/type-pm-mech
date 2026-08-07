import TypePM.Inference

/-!
# Demand-directed typing (`DDTyping`), expression layer

This module defines the syntax-directed, state-threaded demand-directed
judgments `DDSynth`/`DDCheck` announced by the roadmap, independently of the
executable inference functions.  The two judgments thread a fresh supply `q`
and a prevailing substitution `S` in input/output position:

```
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       -- DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  -- DDCheck
```

Design commitments realized here:

* **Synthesis-first checking.**  `DDCheck` has exactly one rule: synthesize
  the expression without an expected type, then align the raw result with the
  expected type at the exact output cut `q₁; S₁` (`DDAlign`).
* **Slot-demand coercion.**  A non-identity coercion branch is available only
  when the substituted expected type already exposes a `MatcherSlot` head at
  the cut.  Branch selection is classified by the deterministic
  `demandClass`, computed on the *cut-resolved* source view `S₁ τraw` — not
  on the raw synthesized type.  The raw-source visibility restriction of the
  current executable selector is therefore a separate fragment condition
  (`RawSourceVisible`), not part of this judgment.
* **No-guess solves.**  Every solve delta is required to be a most general
  unifier of exactly the constraint resolved at its cut (`CapMGU`,
  `TargetMGU`, `PairedMGU`), or the exact one-way producer-to-slot solution
  (`OneWayDelta`).  λ domains are fresh metavariables; no rule structures an
  unrelated metavariable to enable a coercion.
* **No executable-inference dependency.**  The rules never mention
  `inferRaw`/`infer` or reconstruction certificates.  They reuse only the
  deterministic supply-indexed instantiation helpers and the pure syntactic
  recognizers shared with the rest of the development.

The judgments cover the expression layer whose subterms stay outside the
pattern fragment: `matcher` literals, `matchAll`, and the matcher-bodied
`fix` template have no rules yet, so derivations exist only for programs
avoiding those forms.  The pattern-layer families are the remaining part of
roadmap stage 3-1.  The capability-freeze/export ledger axis is deliberately
absent: it is the separate `FreezeCompatible` correspondence condition of
stage 3-3, not part of the demand specification.
-/

namespace TypePM

open Inference (productMatcherDuals? productSlotDuals? matcherProducingRoot
  initialSupply)

/-! ## Most-general solve deltas, in specification form

The shapes mirror the proof-carrying kernel certificates
(`Unification.CapResult`/`TyResult` and the paired-kernel results), stated
relationally so the judgment does not depend on any solver run.
-/

/-- `subst` unifies two capabilities and every unifier factors through it. -/
def CapMGU (left right : Cap) (subst : CapSubst) : Prop :=
  left.apply subst = right.apply subst ∧
  ∀ U : CapSubst, left.apply U = right.apply U →
    ∃ R : CapSubst, U = CapSubst.comp R subst

/-- `subst` unifies two targets and every unifier factors through it. -/
def TargetMGU (left right : Ty) (subst : TySubst) : Prop :=
  left.applyTarget subst = right.applyTarget subst ∧
  ∀ U : TySubst, left.applyTarget U = right.applyTarget U →
    ∃ R : TySubst, U = TySubst.comp R subst

/-- `subst` is a most general *paired* unifier: it solves both sorts at once
and every paired unifier factors through it under cross-sort-aware
sequencing. -/
def PairedMGU (left right : Ty) (subst : Subst) : Prop :=
  subst.apply left = subst.apply right ∧
  ∀ U : Subst, U.apply left = U.apply right →
    ∃ R : Subst, U = Subst.seq R subst

/-- The exact one-way producer-to-slot solution: the capability component is
the restricted `matchCap` binding substitution, and the target component is a
most general unifier of the capability-adjusted targets. -/
def OneWayDelta (producerCap : Cap) (producerTarget : Ty)
    (consumerCap : Cap) (consumerTarget : Ty) (delta : Subst) : Prop :=
  ∃ bindings,
    CapMatch.matchCap producerCap consumerCap = some bindings ∧
    delta.cap = bindings.toSubstWithin consumerCap.fcv ∧
    TargetMGU (producerTarget.applyCapability delta.cap)
      (consumerTarget.applyCapability delta.cap) delta.target

/-! ### Reflexive and single-binding witnesses -/

/-- Identity is a most general unifier of syntactically equal capabilities. -/
theorem CapMGU.refl (capability : Cap) :
    CapMGU capability capability CapSubst.id := by
  refine ⟨rfl, fun U _ => ⟨U, ?_⟩⟩
  funext candidate
  show (CapSubst.id candidate).apply U = U candidate
  rfl

/-- Identity is a most general unifier of syntactically equal targets. -/
theorem TargetMGU.refl (target : Ty) :
    TargetMGU target target TySubst.id := by
  refine ⟨rfl, fun U _ => ⟨U, ?_⟩⟩
  funext candidate
  show (TySubst.id candidate).applyTarget U = U candidate
  rfl

/-- Identity is a most general paired unifier of syntactically equal types. -/
theorem PairedMGU.refl (target : Ty) :
    PairedMGU target target Subst.id :=
  ⟨rfl, fun U _ => ⟨U, (Subst.seq_id_right U).symm⟩⟩

/-- Binding one absent target variable is a most general paired solution of a
variable-versus-type constraint. -/
theorem PairedMGU.varLeft (varId : TypePM.TyVar) (target : Ty)
    (notMem : varId ∉ target.ftv) :
    PairedMGU (.var varId) target
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  constructor
  · show ((Ty.var varId).applyCapability CapSubst.id).applyTarget
        (Unification.TySubst.single varId target) =
      (target.applyCapability CapSubst.id).applyTarget
        (Unification.TySubst.single varId target)
    rw [Ty.applyCapability_id, Ty.applyCapability_id,
      Unification.Ty.applyTarget_single_of_not_mem varId target target notMem]
    show Unification.TySubst.single varId target varId = target
    simp [Unification.TySubst.single]
  · intro U unifies
    refine ⟨U, ?_⟩
    have targetEq : U.target = fun candidate =>
        U.apply (Unification.TySubst.single varId target candidate) := by
      funext candidate
      by_cases hcase : varId = candidate
      · subst hcase
        simp only [Unification.TySubst.single, if_true]
        exact unifies
      · simp only [Unification.TySubst.single, if_neg hcase]
        rfl
    exact congrArg (Subst.mk U.cap) targetEq

/-- Symmetric form of `PairedMGU.varLeft`. -/
theorem PairedMGU.varRight (target : Ty) (varId : TypePM.TyVar)
    (notMem : varId ∉ target.ftv) :
    PairedMGU target (.var varId)
      ⟨CapSubst.id, Unification.TySubst.single varId target⟩ := by
  obtain ⟨sound, universal⟩ := PairedMGU.varLeft varId target notMem
  exact ⟨sound.symm, fun U unifies => universal U unifies.symm⟩

/-! ## Deterministic branch classifiers

Checking dispatches on cut-resolved views only.  The classifiers make the
branch choice a function of the two resolved types, so the coercion rules of
`DDAlign` are mutually exclusive by construction and the selector-determinacy
principle holds definitionally.
-/

/-- Head classification for ordinary equality alignment. -/
inductive AlignPairClass where
  | matcherPair
  | slotPair
  | ordinary
deriving Repr, DecidableEq

/-- Classify one resolved pair for ordinary equality alignment. -/
def alignPairClass : Ty → Ty → AlignPairClass
  | .matcher _ _, .matcher _ _ => .matcherPair
  | .slot _ _, .slot _ _ => .slotPair
  | _, _ => .ordinary

/-- Branch classification at one checking cut. -/
inductive DemandClass where
  | productMatcherLift
  | slotTupleLift
  | matcherToSlot
  | slotToSlot
  | ordinary
deriving Repr, DecidableEq

/-- Classify one checking cut from the resolved source and expected views.
Product-of-matchers has precedence for the empty product, mirroring the
executable selector.  Every non-`ordinary` class requires a slot-headed
expected view: this is the slot-demand principle as a case split. -/
def demandClass (source expected : Ty) : DemandClass :=
  match productMatcherDuals? source, productSlotDuals? source, expected with
  | some _, _, .slot _ _ => .productMatcherLift
  | _, some _, .slot _ _ => .slotTupleLift
  | _, _, _ =>
    match source, expected with
    | .matcher _ _, .slot _ _ => .matcherToSlot
    | .slot _ _, .slot _ _ => .slotToSlot
    | _, _ => .ordinary

/-- Every non-identity demand class exposes a slot-headed expected view. -/
theorem demandClass_slotDemand {source expected : Ty}
    (nonOrdinary : demandClass source expected ≠ .ordinary) :
    ∃ consumerCap consumerTarget,
      expected = .slot consumerCap consumerTarget := by
  unfold demandClass at nonOrdinary
  split at nonOrdinary
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · split at nonOrdinary
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact absurd rfl nonOrdinary

/-- A matcher-headed expectation is never a coercion demand. -/
theorem demandClass_matcherExpected (source : Ty)
    {consumerCap : Cap} {consumerTarget : Ty} :
    demandClass source (.matcher consumerCap consumerTarget) = .ordinary := by
  unfold demandClass
  split <;> (try split) <;> simp_all

/-! ## State-threaded alignment relations

`DDAlignTypes` mirrors ordinary equality alignment: annotated pairs solve the
capability sort first and then the capability-adjusted targets; every other
pair is one paired solve of the resolved views.  `DDAlign` is the complete
checking cut: branch selection by `demandClass` on the resolved views,
followed by the alignment steps of the selected branch.  Each solve composes
its delta onto the prevailing substitution with cross-sort-aware sequencing.
-/

/-- Ordinary equality alignment at one cut. -/
inductive DDAlignTypes : Subst → Ty → Ty → Subst → Prop where
  | matcherPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .matcher leftCap leftTarget →
      S.apply right = .matcher rightCap rightTarget →
      CapMGU leftCap rightCap capDelta →
      PairedMGU (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypes S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | slotPair {S : Subst} {left right : Ty} {leftCap rightCap : Cap}
      {leftTarget rightTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply left = .slot leftCap leftTarget →
      S.apply right = .slot rightCap rightTarget →
      CapMGU leftCap rightCap capDelta →
      PairedMGU (leftTarget.applyCapability capDelta)
        (rightTarget.applyCapability capDelta) targetDelta →
      DDAlignTypes S left right
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {left right : Ty} {delta : Subst} :
      alignPairClass (S.apply left) (S.apply right) = .ordinary →
      PairedMGU (S.apply left) (S.apply right) delta →
      DDAlignTypes S left right (Subst.seq delta S)

/-- The complete checking cut: demand-classified coercion selection and
alignment of one raw synthesized type against one raw expected type. -/
inductive DDAlign : Subst → Ty → Ty → Subst → Prop where
  | productMatcherLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      productMatcherDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      OneWayDelta (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))
        consumerCap consumerTarget delta →
      DDAlign S raw expected (Subst.seq delta S)
  | slotTupleLift {S : Subst} {raw expected : Ty} {duals : List Dual}
      {consumerCap : Cap} {consumerTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .slotTupleLift →
      productSlotDuals? (S.apply raw) = some duals →
      S.apply expected = .slot consumerCap consumerTarget →
      CapMGU (.prod (duals.map Dual.cap)) consumerCap capDelta →
      PairedMGU ((Ty.prod (duals.map Dual.target)).applyCapability capDelta)
        (consumerTarget.applyCapability capDelta) targetDelta →
      DDAlign S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | matcherToSlot {S : Subst} {raw expected : Ty}
      {producerCap : Cap} {producerTarget : Ty}
      {consumerCap : Cap} {consumerTarget : Ty} {delta : Subst} :
      S.apply raw = .matcher producerCap producerTarget →
      S.apply expected = .slot consumerCap consumerTarget →
      OneWayDelta producerCap producerTarget consumerCap consumerTarget
        delta →
      DDAlign S raw expected (Subst.seq delta S)
  | slotToSlot {S : Subst} {raw expected : Ty}
      {sourceCap : Cap} {sourceTarget : Ty}
      {requestedCap : Cap} {requestedTarget : Ty} {capDelta : CapSubst}
      {targetDelta : Subst} :
      S.apply raw = .slot sourceCap sourceTarget →
      S.apply expected = .slot requestedCap requestedTarget →
      CapMGU sourceCap requestedCap capDelta →
      PairedMGU (sourceTarget.applyCapability capDelta)
        (requestedTarget.applyCapability capDelta) targetDelta →
      DDAlign S raw expected
        (Subst.seq targetDelta (Subst.seq ⟨capDelta, TySubst.id⟩ S))
  | ordinary {S : Subst} {raw expected : Ty} {S' : Subst} :
      demandClass (S.apply raw) (S.apply expected) = .ordinary →
      DDAlignTypes S raw expected S' →
      DDAlign S raw expected S'

/-- Any checking cut whose derivation is not ordinary alignment already has a
slot-headed resolved expected view: the slot-demand principle at the level of
the judgment. -/
theorem DDAlign.slotDemand {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlign S raw expected S') :
    DDAlignTypes S raw expected S' ∨
      ∃ consumerCap consumerTarget,
        S.apply expected = .slot consumerCap consumerTarget := by
  cases aligned with
  | productMatcherLift _ slotView _ => exact Or.inr ⟨_, _, slotView⟩
  | slotTupleLift _ _ slotView _ _ => exact Or.inr ⟨_, _, slotView⟩
  | matcherToSlot _ slotView _ => exact Or.inr ⟨_, _, slotView⟩
  | slotToSlot _ slotView _ _ => exact Or.inr ⟨_, _, slotView⟩
  | ordinary _ aligned => exact Or.inl aligned

/-- Under a matcher-headed resolved expectation every checking-cut derivation
degenerates to ordinary alignment: matcher expectations admit only the
ordinary alignment of the raw synthesized type. -/
theorem DDAlign.matcherExpected {S : Subst} {raw expected : Ty} {S' : Subst}
    {consumerCap : Cap} {consumerTarget : Ty}
    (aligned : DDAlign S raw expected S')
    (matcherView :
      S.apply expected = .matcher consumerCap consumerTarget) :
    DDAlignTypes S raw expected S' := by
  cases aligned with
  | productMatcherLift _ slotView _ =>
      rw [matcherView] at slotView; cases slotView
  | slotTupleLift _ _ slotView _ _ =>
      rw [matcherView] at slotView; cases slotView
  | matcherToSlot _ slotView _ =>
      rw [matcherView] at slotView; cases slotView
  | slotToSlot _ slotView _ _ =>
      rw [matcherView] at slotView; cases slotView
  | ordinary _ aligned => exact aligned

/-! ## The demand-directed judgments -/

/-- The synthesis-order recursive-binder placeholder is restricted to the
non-matcher template while the pattern layer is outside the fragment. -/
abbrev NonMatcherBody (body : Expr) : Prop :=
  matcherProducingRoot body = false

mutual

/-- Demand-directed synthesis `q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'`.

Rules mirror the left-to-right synthesis traversal: context lookup applies
the prevailing substitution first, λ and application domains are fresh
metavariables, `let` generalizes the value type in the substituted context,
and constructor/primitive arguments are checked against the supply-indexed
instantiation of the declared scheme.  `matcher` literals and `matchAll`
have no rules yet (pattern layer, roadmap stage 3-1). -/
inductive DDSynth (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → Expr → Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | var {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {scheme : Scheme} :
      (Γ.applySubst S).find? name = some scheme →
      DDSynth signature q S Γ (.var name)
        (InferenceBase.instantiateScheme q scheme).value
        (InferenceBase.instantiateScheme q scheme).supply S
  | lam {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {body : Expr} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature { q with nextTy := q.nextTy + 1 } S
        ((name, Scheme.mono (.var q.nextTy)) :: Γ) body bodyTarget q' S' →
      DDSynth signature q S Γ (.lam name body)
        (.fn (.var q.nextTy) bodyTarget) q' S'
  | fix {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {self argument : String} {body : Expr} {bodyTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      self ≠ argument →
      DirectSelf.Holds self body →
      NonMatcherBody body →
      DDSynth signature { q with nextTy := q.nextTy + 2 } S
        ((argument, Scheme.mono (.var q.nextTy)) ::
          (self, Scheme.mono
            (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: Γ)
        body bodyTarget q₁ S₁ →
      DDAlignTypes S₁ bodyTarget (.var (q.nextTy + 1)) S' →
      DDSynth signature q S Γ (.fix self argument body)
        (.fn (.var q.nextTy) (.var (q.nextTy + 1))) q₁ S'
  | app {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {function argument : Expr} {functionTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₃ : Subst} :
      DDSynth signature q S Γ function functionTarget q₁ S₁ →
      DDAlignTypes S₁ functionTarget
        (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂ →
      DDCheck signature { q₁ with nextTy := q₁.nextTy + 2 } S₂ Γ argument
        (.var q₁.nextTy) q₂ S₃ →
      DDSynth signature q S Γ (.app function argument)
        (.var (q₁.nextTy + 1)) q₂ S₃
  | lit {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {value : Int} :
      DDSynth signature q S Γ (.lit value) .int q S
  | tuple {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expressions : List Expr} {targets : List Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynths signature q S Γ expressions targets q' S' →
      DDSynth signature q S Γ (.tuple expressions) (.prod targets) q' S'
  | ctor {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      signature.findDataCtor name = some scheme →
      DDChecks signature (InferenceBase.instantiateCtorScheme q scheme).supply
        S Γ expressions
        (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S' →
      DDSynth signature q S Γ (.ctor name expressions)
        (InferenceBase.instantiateCtorScheme q scheme).value.2 q' S'
  | prim {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {op : PrimOp} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      signature.findPrimitive op = some scheme →
      DDChecks signature (InferenceBase.instantiateCtorScheme q scheme).supply
        S Γ expressions
        (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S' →
      DDSynth signature q S Γ (.prim op expressions)
        (InferenceBase.instantiateCtorScheme q scheme).value.2 q' S'
  | letE {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {name : String} {value body : Expr} {valueTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature q S Γ value valueTarget q₁ S₁ →
      DDSynth signature q₁ S₁
        ((name, signature.generalize (Γ.applySubst S₁)
          (S₁.apply valueTarget)) :: Γ) body bodyTarget q' S' →
      DDSynth signature q S Γ (.letE name value body) bodyTarget q' S'
  | something {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDSynth signature q S Γ .something (.matcher .any (.var q.nextTy))
        { q with nextTy := q.nextTy + 1 } S

/-- Left-to-right synthesis of an expression list. -/
inductive DDSynths (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → List Expr → List Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDSynths signature q S Γ [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expressions : List Expr} {target : Ty}
      {targets : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDSynth signature q S Γ expression target q₁ S₁ →
      DDSynths signature q₁ S₁ Γ expressions targets q' S' →
      DDSynths signature q S Γ (expression :: expressions)
        (target :: targets) q' S'

/-- Demand-directed checking `q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'`: synthesize
first, then align at the exact output cut. -/
inductive DDCheck (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → Expr → Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | mk {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expected raw : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst} :
      DDSynth signature q S Γ expression raw q₁ S₁ →
      DDAlign S₁ raw expected S' →
      DDCheck signature q S Γ expression expected q₁ S'

/-- Pointwise checking of equal-length expression/type lists. -/
inductive DDChecks (signature : FrozenSig) :
    InferenceBase.FreshSupply → Subst → Context → List Expr → List Ty →
      InferenceBase.FreshSupply → Subst → Prop where
  | nil {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} :
      DDChecks signature q S Γ [] [] q S
  | cons {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
      {expression : Expr} {expressions : List Expr} {expected : Ty}
      {expecteds : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst} :
      DDCheck signature q S Γ expression expected q₁ S₁ →
      DDChecks signature q₁ S₁ Γ expressions expecteds q' S' →
      DDChecks signature q S Γ (expression :: expressions)
        (expected :: expecteds) q' S'

end

/-- The closed wrapper: start from the source-scope supply and the identity
substitution, and publish the terminal substitution applied to the raw
result. -/
def DDTyping (signature : FrozenSig) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ raw q' S',
    DDSynth signature (initialSupply signature context) Subst.id context
      expression raw q' S' ∧
    target = S'.apply raw

/-! ## Prevailing replay

Every judgment output substitution is the input substitution extended by a
chronological chain of solve deltas, mirroring the replay factorization of
the executable trace. -/

/-- Chronological delta replay onto an existing prevailing substitution. -/
def replayDeltas : Subst → List Subst → Subst
  | S, [] => S
  | S, delta :: deltas => replayDeltas (Subst.seq delta S) deltas

@[simp] theorem replayDeltas_nil (S : Subst) : replayDeltas S [] = S := rfl

theorem replayDeltas_append (S : Subst) (first rest : List Subst) :
    replayDeltas S (first ++ rest) =
      replayDeltas (replayDeltas S first) rest := by
  induction first generalizing S with
  | nil => rfl
  | cons delta deltas ih =>
      simpa [replayDeltas] using ih (Subst.seq delta S)

/-- The later substitution replays the earlier one through a chronological
delta chain. -/
def ReplayExtends (earlier later : Subst) : Prop :=
  ∃ deltas, later = replayDeltas earlier deltas

theorem ReplayExtends.refl (S : Subst) : ReplayExtends S S :=
  ⟨[], rfl⟩

theorem ReplayExtends.solve {S : Subst} (delta : Subst) :
    ReplayExtends S (Subst.seq delta S) :=
  ⟨[delta], rfl⟩

theorem ReplayExtends.trans {S₁ S₂ S₃ : Subst}
    (first : ReplayExtends S₁ S₂) (second : ReplayExtends S₂ S₃) :
    ReplayExtends S₁ S₃ := by
  obtain ⟨firstDeltas, firstEq⟩ := first
  obtain ⟨secondDeltas, secondEq⟩ := second
  exact ⟨firstDeltas ++ secondDeltas, by
    rw [replayDeltas_append, ← firstEq, secondEq]⟩

/-- Ordinary alignment extends the prevailing substitution by replay. -/
theorem DDAlignTypes.replayExtends {S : Subst} {left right : Ty} {S' : Subst}
    (aligned : DDAlignTypes S left right S') : ReplayExtends S S' := by
  cases aligned with
  | matcherPair _ _ _ _ =>
      exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | slotPair _ _ _ _ =>
      exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | ordinary _ _ =>
      exact ⟨[_], rfl⟩

/-- Every checking cut extends the prevailing substitution by replay. -/
theorem DDAlign.replayExtends {S : Subst} {raw expected : Ty} {S' : Subst}
    (aligned : DDAlign S raw expected S') : ReplayExtends S S' := by
  cases aligned with
  | productMatcherLift _ _ _ => exact ⟨[_], rfl⟩
  | slotTupleLift _ _ _ _ _ => exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | matcherToSlot _ _ _ => exact ⟨[_], rfl⟩
  | slotToSlot _ _ _ _ => exact ⟨[⟨_, TySubst.id⟩, _], rfl⟩
  | ordinary _ aligned => exact aligned.replayExtends

mutual

/-- Synthesis extends the prevailing substitution by chronological replay. -/
theorem DDSynth.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {τ : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDSynth signature q S Γ e τ q' S' → ReplayExtends S S'
  | .var _ => ReplayExtends.refl _
  | .lam body => body.replayExtends
  | .fix _ _ _ body aligned =>
      (body.replayExtends).trans aligned.replayExtends
  | .app function aligned argument =>
      ((function.replayExtends).trans aligned.replayExtends).trans
        argument.replayExtends
  | .lit => ReplayExtends.refl _
  | .tuple expressions => expressions.replayExtends
  | .ctor _ arguments => arguments.replayExtends
  | .prim _ arguments => arguments.replayExtends
  | .letE value body =>
      (value.replayExtends).trans body.replayExtends
  | .something => ReplayExtends.refl _

/-- List synthesis extends the prevailing substitution by replay. -/
theorem DDSynths.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {τs : List Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDSynths signature q S Γ es τs q' S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail =>
      (head.replayExtends).trans tail.replayExtends

/-- Checking extends the prevailing substitution by replay. -/
theorem DDCheck.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {expected : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDCheck signature q S Γ e expected q' S' → ReplayExtends S S'
  | .mk synthesized aligned =>
      (synthesized.replayExtends).trans aligned.replayExtends

/-- List checking extends the prevailing substitution by replay. -/
theorem DDChecks.replayExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDChecks signature q S Γ es expecteds q' S' → ReplayExtends S S'
  | .nil => ReplayExtends.refl _
  | .cons head tail =>
      (head.replayExtends).trans tail.replayExtends

end

/-! ## Supply monotonicity -/

/-- Componentwise order on fresh supplies. -/
def SupplyExtends (earlier later : InferenceBase.FreshSupply) : Prop :=
  earlier.nextCap ≤ later.nextCap ∧ earlier.nextTy ≤ later.nextTy

theorem SupplyExtends.refl (q : InferenceBase.FreshSupply) :
    SupplyExtends q q :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem SupplyExtends.trans {q₁ q₂ q₃ : InferenceBase.FreshSupply}
    (first : SupplyExtends q₁ q₂) (second : SupplyExtends q₂ q₃) :
    SupplyExtends q₁ q₃ :=
  ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩

theorem SupplyExtends.bumpTy (q : InferenceBase.FreshSupply) (count : Nat) :
    SupplyExtends q { q with nextTy := q.nextTy + count } :=
  ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

/-- Scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateScheme
    (q : InferenceBase.FreshSupply) (scheme : Scheme) :
    SupplyExtends q (InferenceBase.instantiateScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Constructor-scheme instantiation only advances both counters. -/
theorem SupplyExtends.instantiateCtorScheme
    (q : InferenceBase.FreshSupply) (scheme : CtorScheme) :
    SupplyExtends q (InferenceBase.instantiateCtorScheme q scheme).supply :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

mutual

/-- Synthesis only advances the fresh supply. -/
theorem DDSynth.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {τ : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDSynth signature q S Γ e τ q' S' → SupplyExtends q q'
  | .var (scheme := scheme) _ => SupplyExtends.instantiateScheme _ scheme
  | .lam body =>
      (SupplyExtends.bumpTy _ 1).trans body.supplyExtends
  | .fix _ _ _ body _ =>
      (SupplyExtends.bumpTy _ 2).trans body.supplyExtends
  | .app function _ argument =>
      (function.supplyExtends).trans
        ((SupplyExtends.bumpTy _ 2).trans argument.supplyExtends)
  | .lit => SupplyExtends.refl _
  | .tuple expressions => expressions.supplyExtends
  | .ctor (scheme := scheme) _ arguments =>
      (SupplyExtends.instantiateCtorScheme _ scheme).trans
        arguments.supplyExtends
  | .prim (scheme := scheme) _ arguments =>
      (SupplyExtends.instantiateCtorScheme _ scheme).trans
        arguments.supplyExtends
  | .letE value body =>
      (value.supplyExtends).trans body.supplyExtends
  | .something => SupplyExtends.bumpTy _ 1

/-- List synthesis only advances the fresh supply. -/
theorem DDSynths.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {τs : List Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst} :
    DDSynths signature q S Γ es τs q' S' → SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail =>
      (head.supplyExtends).trans tail.supplyExtends

/-- Checking only advances the fresh supply. -/
theorem DDCheck.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context} {e : Expr}
    {expected : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDCheck signature q S Γ e expected q' S' → SupplyExtends q q'
  | .mk synthesized _ => synthesized.supplyExtends

/-- List checking only advances the fresh supply. -/
theorem DDChecks.supplyExtends {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {Γ : Context}
    {es : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst} :
    DDChecks signature q S Γ es expecteds q' S' → SupplyExtends q q'
  | .nil => SupplyExtends.refl _
  | .cons head tail =>
      (head.supplyExtends).trans tail.supplyExtends

end

end TypePM
