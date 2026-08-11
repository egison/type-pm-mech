import TypePM.DemandTypingErasureFactorization
import TypePM.DemandTypingErasureTransport

/-!
# Expression-side runtime erasure for demand typing

This module records the expression-facing half of DD state erasure.  Each
constructor lemma consumes only its recursively erased children at the
constructor's terminal cut, plus the small algebraic certificate which the
corresponding `RuntimeTyping` constructor needs.  In particular, no lemma
stores or assumes a `RuntimeTyping` derivation for the expression being
proved.

Earlier children in a sequential traversal must be transported to the final
cut before the structural lemma applies.  Those obligations are deliberately
visible as `...AtTerminal` premises; they are the induction invariant needed
by the full mutual erasure theorem.
-/

namespace TypePM

/-! ## Checking alignment at the runtime boundary -/

/--
The normalized, state-free action of one checking cut.  This is the minimal
algebraic certificate needed by the runtime constructors: equality, one
matcher-to-slot demand, product lifting followed by that demand, or slot
tuple lifting.  It contains no expression typing derivation.
-/
inductive RuntimeAlignment : Ty -> Ty -> Prop where
  | equal {left right : Ty} (equality : left = right) :
      RuntimeAlignment left right
  | matcherToSlot {producer consumer : Cap} {target : Ty}
      (demand : CapabilityDemand producer consumer) :
      RuntimeAlignment (.matcher producer target) (.slot consumer target)
  | productMatcherToSlot {duals : List Dual} {consumer : Cap}
      (demand : CapabilityDemand (.prod (duals.map Dual.cap)) consumer) :
      RuntimeAlignment
        (.prod (duals.map fun dual => Ty.matcher dual.cap dual.target))
        (.slot consumer (.prod (duals.map Dual.target)))
  | slotTuple {duals : List Dual} :
      RuntimeAlignment
        (.prod (duals.map fun dual => Ty.slot dual.cap dual.target))
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- A normalized alignment acts on a runtime derivation structurally. -/
theorem RuntimeAlignment.transport
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {raw expected : Ty} (alignment : RuntimeAlignment raw expected)
    (typing : RuntimeTyping signature context expression raw) :
    RuntimeTyping signature context expression expected := by
  cases alignment with
  | equal equality => rw [← equality]; exact typing
  | matcherToSlot demand => exact RuntimeTyping.coerceMatcherToSlot typing demand
  | productMatcherToSlot demand =>
      exact RuntimeTyping.coerceMatcherToSlot
        (RuntimeTyping.coerceProductMatcher typing) demand
  | slotTuple => exact RuntimeTyping.coerceSlotTuple typing

/-- The algebraic terminal obligation left by an origin-aware DD alignment. -/
def DDAlignWithLedger.RuntimeCertificate
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} (_aligned : DDAlignWithLedger ledger S raw expected S') : Prop :=
  RuntimeAlignment (S'.apply raw) (S'.apply expected)

private theorem OneWayDelta.capabilityDemand
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {delta : Subst}
    (oneWay : OneWayDelta producerCap producerTarget consumerCap
      consumerTarget delta) :
    CapabilityDemand (producerCap.apply delta.cap)
      (consumerCap.apply delta.cap) := by
  rcases oneWay with ⟨bindings, matched, capSubstitution, _target⟩
  rw [capSubstitution]
  exact CapabilityDemand.ofOneWayAt
    (CapMatch.matchCap_restricted_sound matched)

private theorem OneWayDelta.targetEquality
    {producerCap consumerCap : Cap} {producerTarget consumerTarget : Ty}
    {delta : Subst}
    (oneWay : OneWayDelta producerCap producerTarget consumerCap
      consumerTarget delta) :
    delta.apply producerTarget = delta.apply consumerTarget := by
  rcases oneWay with ⟨_bindings, _matched, _capSubstitution, target⟩
  simpa only [Subst.apply] using target.1.1

private theorem Subst.apply_productMatchers
    (S : Subst) (duals : List Dual) :
    S.apply (.prod (duals.map fun dual => Ty.matcher dual.cap dual.target)) =
      .prod ((duals.map (Dual.applySubst S)).map fun dual =>
        Ty.matcher dual.cap dual.target) := by
  simp [Subst.apply_prod, List.map_map, Dual.applySubst, Dual.apply,
    Function.comp_def]

private theorem Subst.apply_productSlots
    (S : Subst) (duals : List Dual) :
    S.apply (.prod (duals.map fun dual => Ty.slot dual.cap dual.target)) =
      .prod ((duals.map (Dual.applySubst S)).map fun dual =>
        Ty.slot dual.cap dual.target) := by
  simp [Subst.apply_prod, List.map_map, Dual.applySubst, Dual.apply,
    Function.comp_def]

/-- A later common substitution preserves a normalized runtime alignment. -/
theorem RuntimeAlignment.apply
    {raw expected : Ty} (post : Subst)
    (alignment : RuntimeAlignment raw expected) :
    RuntimeAlignment (post.apply raw) (post.apply expected) := by
  cases alignment with
  | equal equality => exact .equal (congrArg post.apply equality)
  | @matcherToSlot producer consumer target demand =>
      simpa only [Subst.apply_matcher, Subst.apply_slot] using
        (RuntimeAlignment.matcherToSlot (demand.apply post.cap))
  | @productMatcherToSlot duals consumer demand =>
      have mappedDemand : CapabilityDemand
          (.prod ((duals.map (Dual.applySubst post)).map Dual.cap))
          (consumer.apply post.cap) := by
        simpa [Dual.applySubst, Dual.apply, List.map_map,
          Function.comp_def] using demand.apply post.cap
      rw [Subst.apply_productMatchers, Subst.apply_slot, Subst.apply_prod]
      simpa only [Dual.map_target_applySubst] using
        (RuntimeAlignment.productMatcherToSlot
          (duals := duals.map (Dual.applySubst post)) mappedDemand)
  | @slotTuple duals =>
      rw [Subst.apply_productSlots, Subst.apply_slot, Cap.apply_prod,
        Subst.apply_prod]
      simpa only [Cap.applyList_eq_map, Dual.map_cap_applySubst,
        Dual.map_target_applySubst] using
        (RuntimeAlignment.slotTuple
          (duals := duals.map (Dual.applySubst post)))

/-- Every ledger-aware checking alignment determines its normalized runtime
action without an expression-typing premise. -/
theorem DDAlignWithLedger.runtimeCertificate
    {ledger : CapabilityOriginLedger} {S : Subst} {raw expected : Ty}
    {S' : Subst} (aligned : DDAlignWithLedger ledger S raw expected S') :
    aligned.RuntimeCertificate := by
  cases aligned with
  | productMatcherLift rawView expectedView safe =>
      rename_i duals consumerCap consumerTarget delta
      unfold RuntimeCertificate
      rw [Subst.seq_apply, Subst.seq_apply,
        Inference.productMatcherDuals?_sound rawView, expectedView,
        Subst.apply_productMatchers, Subst.apply_slot]
      have targetEquality := safe.exact.targetEquality
      have demand := safe.exact.capabilityDemand
      have mappedDemand : CapabilityDemand
          (.prod ((duals.map (Dual.applySubst delta)).map Dual.cap))
          (consumerCap.apply delta.cap) := by
        simpa [Dual.applySubst, Dual.apply, List.map_map,
          Function.comp_def] using demand
      rw [← targetEquality]
      simpa [Dual.applySubst, Dual.apply, List.map_map, Function.comp_def,
        Subst.apply_prod] using
        (RuntimeAlignment.productMatcherToSlot
          (duals := duals.map (Dual.applySubst delta)) mappedDemand)
  | slotTupleLift demandView rawView expectedView capSafe targetSafe =>
      rename_i duals consumerCap consumerTarget capDelta targetDelta
      unfold RuntimeCertificate
      simp only [Subst.seq_apply]
      rw [Inference.productSlotDuals?_sound rawView, expectedView,
        Subst.apply_productSlots, Subst.apply_slot,
        Subst.apply_productSlots, Subst.apply_slot]
      have capEquality := capSafe.exact.1.1
      have targetEquality := targetSafe.exact.1.1
      simp only [Subst.apply, Ty.applyCapability]
        at targetEquality
      have finalCapEquality := congrArg
        (fun capability => capability.apply targetDelta.cap) capEquality
      let finalDuals := (duals.map
        (Dual.applySubst ⟨capDelta, TySubst.id⟩)).map
          (Dual.applySubst targetDelta)
      have finalCapEquality' :
          .prod (finalDuals.map Dual.cap) =
          (consumerCap.apply capDelta).apply targetDelta.cap := by
        simpa [finalDuals, Dual.applySubst, Dual.apply, List.map_map,
          Function.comp_def] using finalCapEquality
      have finalTargetEquality :
          .prod (finalDuals.map Dual.target) =
          targetDelta.apply
            (consumerTarget.applyCapability capDelta) := by
        simpa [finalDuals, Dual.applySubst, Dual.apply, List.map_map,
          Function.comp_def, Subst.apply, Subst.apply_prod,
          Ty.applyCapabilityList_eq_map, Ty.applyTargetList_eq_map,
          Ty.applyTarget, Ty.applyTarget_id] using targetEquality
      have finalTargetEquality' :
          .prod (finalDuals.map Dual.target) =
          targetDelta.apply
            ((Subst.mk capDelta TySubst.id).apply consumerTarget) := by
        simpa only [Subst.apply, Ty.applyTarget_id] using finalTargetEquality
      rw [← finalCapEquality', ← finalTargetEquality']
      exact RuntimeAlignment.slotTuple (duals := finalDuals)
  | matcherToSlot rawView expectedView safe =>
      rename_i producerCap producerTarget consumerCap consumerTarget delta
      unfold RuntimeCertificate
      rw [Subst.seq_apply, Subst.seq_apply, rawView, expectedView,
        Subst.apply_matcher, Subst.apply_slot]
      have targetEquality := safe.exact.targetEquality
      rw [← targetEquality]
      exact RuntimeAlignment.matcherToSlot safe.exact.capabilityDemand
  | slotToSlot rawView expectedView capSafe targetSafe =>
      rename_i sourceCap sourceTarget requestedCap requestedTarget capDelta
        targetDelta
      unfold RuntimeCertificate
      apply RuntimeAlignment.equal
      simp only [Subst.seq_apply]
      rw [rawView, expectedView]
      have capEquality := capSafe.exact.1.1
      have targetEquality := targetSafe.exact.1.1
      simp only [Subst.apply]
        at targetEquality
      simp only [Subst.apply, Ty.applyCapability, Ty.applyTarget,
        Ty.applyTarget_id]
      rw [capEquality, targetEquality]
  | ordinary _ ordinaryAligned =>
      exact RuntimeAlignment.equal ordinaryAligned.output_equal

/-! ## Runtime-erasure conclusions for checking families -/

namespace DDCheckOrigin

/-- Terminal state-free conclusion for one origin-aware check. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDCheckOrigin signature raw ledger ledger') : Prop :=
  RuntimeTyping signature (context.applySubst S') expression
    (S'.apply expected)

/-- Checking is runtime-alignment transport after synthesis has reached the
checking cut's terminal substitution. -/
theorem runtimeErasure_mk_of_terminal_synthesis
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected raw : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    {synthesized : DDSynth signature q S context expression raw q1 S1}
    (synthOrigin : DDSynthOrigin signature synthesized ledger ledger1)
    (aligned : DDAlignWithLedger ledger1 S1 raw expected S')
    (synthesisAtTerminal : RuntimeTyping signature (context.applySubst S')
      expression (S'.apply raw))
    (certificate : aligned.RuntimeCertificate) :
    RuntimeErasure (DDCheckOrigin.mk synthOrigin aligned) :=
  certificate.transport synthesisAtTerminal

/-- The DD alignment itself supplies the algebraic runtime action. -/
theorem runtimeErasure_mk
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected raw : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    {synthesized : DDSynth signature q S context expression raw q1 S1}
    (synthOrigin : DDSynthOrigin signature synthesized ledger ledger1)
    (aligned : DDAlignWithLedger ledger1 S1 raw expected S')
    (synthesisAtTerminal : RuntimeTyping signature (context.applySubst S')
      expression (S'.apply raw)) :
    RuntimeErasure (DDCheckOrigin.mk synthOrigin aligned) :=
  runtimeErasure_mk_of_terminal_synthesis synthOrigin aligned
    synthesisAtTerminal aligned.runtimeCertificate

end DDCheckOrigin

namespace DDChecksOrigin

/-- Terminal state-free conclusion for an origin-aware checking list. -/
def RuntimeErasure
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDChecksOrigin signature raw ledger ledger') : Prop :=
  ExprsTy signature (context.applySubst S') expressions
    (expecteds.map S'.apply)

theorem runtimeErasure_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    RuntimeErasure
      (DDChecksOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) :=
  ExprsTy.nil

/-- Checking-list composition once its earlier head has reached the final cut. -/
theorem runtimeErasure_cons_of_terminal_head
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q1 q' : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 ledger' : CapabilityOriginLedger}
    {head : DDCheck signature q S context expression expected q1 S1}
    {tail : DDChecks signature q1 S1 context expressions expecteds q' S'}
    (headOrigin : DDCheckOrigin signature head ledger ledger1)
    (tailOrigin : DDChecksOrigin signature tail ledger1 ledger')
    (headAtTerminal : RuntimeTyping signature (context.applySubst S')
      expression (S'.apply expected))
    (tailErasure : RuntimeErasure tailOrigin) :
    RuntimeErasure (DDChecksOrigin.cons headOrigin tailOrigin) :=
  ExprsTy.cons headAtTerminal tailErasure

end DDChecksOrigin

/-! ## Structural expression constructors -/

namespace DDSynthOrigin

/-! ## The child-to-parent transport invariant -/

/--
Runtime erasure stable under any later origin-admissible suffix.

The invariant quantifies only the actual origin-admissible suffix beginning at
this derivation's output cut.  In particular it does not assume a global
context-flow oracle.  Variable leaves must recover their selected scheme
instance from the `markSchemeInstance` policy carried by that exact suffix.
-/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDSynthOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' ->
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post ->
    RuntimeTyping signature (context.applySubst finalSubst) expression
      (finalSubst.apply target)

/-- Literals are stable under every later suffix. -/
theorem runtimeErasureUnder_lit
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (value : Int) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDSynthOrigin.lit (signature := signature) (q := q) (S := S)
        (context := context) (value := value) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  simp only [Subst.apply_int]
  exact RuntimeTyping.lit

/-- The polymorphic `something` leaf is stable under every later suffix. -/
theorem runtimeErasureUnder_something
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDSynthOrigin.something (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  simp only [Subst.apply_matcher, Cap.apply]
  exact RuntimeTyping.something

/-- Lambda erasure is structural under the same actual later suffix as its
body; the monomorphic parameter is normalized with the final substitution. -/
theorem runtimeErasureUnder_lam
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {body : Expr} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, NamedScheme.mono (.var q.nextTy)) :: context) body bodyTarget q' S'}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger')
    (bodyUnder : RuntimeErasureUnder bodyOrigin) :
    RuntimeErasureUnder (DDSynthOrigin.lam bodyOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have bodyTyping := bodyUnder terminalEquation admissible
  simp only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
    Subst.apply_fn] at bodyTyping ⊢
  exact RuntimeTyping.lam bodyTyping

end DDSynthOrigin

namespace DDSynthsOrigin

/-- Later-post-stable erasure for a synthesis traversal. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDSynthsOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' ->
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post ->
    ExprsTy signature (context.applySubst finalSubst) expressions
      (targets.map finalSubst.apply)

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDSynthsOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact ExprsTy.nil

/-- A list cons composes the tail factorization with the external suffix to
transport the earlier head directly to the common final cut. -/
theorem runtimeErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q1 q' : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 ledger' : CapabilityOriginLedger}
    {head : DDSynth signature q S context expression target q1 S1}
    {tail : DDSynths signature q1 S1 context expressions targets q' S'}
    (headOrigin : DDSynthOrigin signature head ledger ledger1)
    (tailOrigin : DDSynthsOrigin signature tail ledger1 ledger')
    (headUnder : DDSynthOrigin.RuntimeErasureUnder headOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeErasureUnder (DDSynthsOrigin.cons headOrigin tailOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  obtain ⟨S1b, _headBounded⟩ :=
    headOrigin.erase.boundedBy closed Sb contextBounded
  have tailFactor := DDSynthsOrigin.factorize tailOrigin closed S1b
    (contextBounded.mono headOrigin.erase.supplyExtends)
  rcases tailFactor with ⟨tailPost, tailEquation, tailAdmissible⟩
  have headEquation : finalSubst =
      Subst.seq (Subst.seq post tailPost) S1 := by
    rw [terminalEquation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S1
  have headTyping := headUnder headEquation
    (tailAdmissible.seq admissible)
  have tailTyping := tailUnder terminalEquation admissible
  exact ExprsTy.cons headTyping tailTyping

end DDSynthsOrigin

namespace DDSynthOrigin

/-- Tuple synthesis inherits the later-post-stable erasure of its ordered
child traversal. -/
theorem runtimeErasureUnder_tuple
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    {children : DDSynths signature q S context expressions targets q' S'}
    (childrenOrigin : DDSynthsOrigin signature children ledger ledger')
    (childrenUnder : DDSynthsOrigin.RuntimeErasureUnder childrenOrigin) :
    RuntimeErasureUnder (DDSynthOrigin.tuple childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have childrenTyping := childrenUnder terminalEquation admissible
  simp only [Subst.apply_prod]
  exact RuntimeTyping.tuple childrenTyping

/-- Monomorphic recursion composes the body's alignment factor with the later
parent suffix; no terminal body typing premise is needed. -/
theorem runtimeErasureUnder_fix
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {body : Expr}
    {bodyTarget : Ty} {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, NamedScheme.mono (.var q.nextTy)) ::
        (self, NamedScheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
      body bodyTarget q1 S1}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 bodyTarget
      (.var (q.nextTy + 1)) S')
    (bodyUnder : RuntimeErasureUnder bodyOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeErasureUnder
      (DDSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have extension := SupplyExtends.bumpTy q 2
  have domainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
      (.var q.nextTy) := Ty.BoundedBy.varOf
    (show q.nextTy < q.nextTy + 2 by omega)
  have codomainB : Ty.BoundedBy { q with nextTy := q.nextTy + 2 }
      (.var (q.nextTy + 1)) := Ty.BoundedBy.varOf
    (show q.nextTy + 1 < q.nextTy + 2 by omega)
  have bodyContextB : Context.BoundedBy
      { q with nextTy := q.nextTy + 2 }
      ((argument, NamedScheme.mono (.var q.nextTy)) ::
        (self, NamedScheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context) :=
    Context.BoundedBy.cons (NamedScheme.BoundedBy.ofMono domainB)
      (Context.BoundedBy.cons
        (NamedScheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
        (contextBounded.mono extension))
  obtain ⟨S1b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
    (Sb.mono extension) bodyContextB
  rcases aligned.factorPost S1b bodyB
      (codomainB.mono bodyOrigin.erase.supplyExtends) with
    ⟨alignPost, alignEquation, alignAdmissible⟩
  have bodyEquation : finalSubst =
      Subst.seq (Subst.seq post alignPost) S1 := by
    rw [terminalEquation, alignEquation]
    exact PhasedPost.seq_assoc post alignPost S1
  have bodyTyping := bodyUnder bodyEquation
    (alignAdmissible.seq admissible)
  have finalResultEquality : finalSubst.apply bodyTarget =
      finalSubst.apply (.var (q.nextTy + 1)) := by
    rw [terminalEquation, Subst.seq_apply, Subst.seq_apply]
    exact congrArg post.apply aligned.output_equal
  have bodyExpected : RuntimeTyping signature
      (Context.applySubst finalSubst
        ((argument, NamedScheme.mono (.var q.nextTy)) ::
        (self, NamedScheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context))
      body (finalSubst.apply (.var (q.nextTy + 1))) := by
    rw [← finalResultEquality]
    exact bodyTyping
  have bodyExpected' : RuntimeTyping signature
      ((argument, NamedScheme.mono (finalSubst.apply (.var q.nextTy))) ::
        (self, NamedScheme.mono
          (.fn (finalSubst.apply (.var q.nextTy))
            (finalSubst.apply (.var (q.nextTy + 1))))) ::
        context.applySubst finalSubst)
      body (finalSubst.apply (.var (q.nextTy + 1))) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyExpected
  exact RuntimeTyping.fixE distinct direct bodyExpected'

end DDSynthOrigin

namespace DDCheckOrigin

/-- Later-post-stable erasure for one checking derivation. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDCheckOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' ->
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post ->
    RuntimeTyping signature (context.applySubst finalSubst) expression
      (finalSubst.apply expected)

/-- Checking composes synthesis with its own alignment factor and then applies
the normalized runtime action at the final cut. -/
theorem runtimeErasureUnder_mk
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expected raw : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    {synthesized : DDSynth signature q S context expression raw q1 S1}
    (synthOrigin : DDSynthOrigin signature synthesized ledger ledger1)
    (aligned : DDAlignWithLedger ledger1 S1 raw expected S')
    (synthUnder : DDSynthOrigin.RuntimeErasureUnder synthOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedBounded : expected.BoundedBy q) :
    RuntimeErasureUnder (DDCheckOrigin.mk synthOrigin aligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  obtain ⟨S1b, rawB⟩ :=
    synthOrigin.erase.boundedBy closed Sb contextBounded
  have expectedB := expectedBounded.mono synthOrigin.erase.supplyExtends
  rcases aligned.factorPost S1b rawB expectedB with
    ⟨alignPost, alignEquation, alignAdmissible⟩
  have synthEquation : finalSubst =
      Subst.seq (Subst.seq post alignPost) S1 := by
    rw [terminalEquation, alignEquation]
    exact PhasedPost.seq_assoc post alignPost S1
  have synthTyping := synthUnder synthEquation
    (alignAdmissible.seq admissible)
  have finalAlignment : RuntimeAlignment (finalSubst.apply raw)
      (finalSubst.apply expected) := by
    have transported := aligned.runtimeCertificate.apply post
    simpa only [terminalEquation, Subst.seq_apply] using transported
  exact finalAlignment.transport synthTyping

end DDCheckOrigin

namespace DDChecksOrigin

/-- Later-post-stable erasure for an ordered checking traversal. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDChecksOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' ->
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post ->
    ExprsTy signature (context.applySubst finalSubst) expressions
      (expecteds.map finalSubst.apply)

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (context : Context) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDChecksOrigin.nil (signature := signature) (q := q) (S := S)
        (context := context) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact ExprsTy.nil

/-- A checking cons transports its earlier head through the tail
factorization before applying the common external suffix. -/
theorem runtimeErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {expected : Ty} {expecteds : List Ty}
    {q1 q' : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 ledger' : CapabilityOriginLedger}
    {head : DDCheck signature q S context expression expected q1 S1}
    {tail : DDChecks signature q1 S1 context expressions expecteds q' S'}
    (headOrigin : DDCheckOrigin signature head ledger ledger1)
    (tailOrigin : DDChecksOrigin signature tail ledger1 ledger')
    (headUnder : DDCheckOrigin.RuntimeErasureUnder headOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context)
    (expectedsBounded : ∀ item ∈ expected :: expecteds,
      item.BoundedBy q) :
    RuntimeErasureUnder (DDChecksOrigin.cons headOrigin tailOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have expectedB : expected.BoundedBy q :=
    expectedsBounded expected (by simp)
  have S1b := headOrigin.erase.boundedBy closed Sb contextBounded expectedB
  have tailFactor := DDChecksOrigin.factorize tailOrigin closed S1b
    (contextBounded.mono headOrigin.erase.supplyExtends)
    (fun item membership =>
      (expectedsBounded item (by simp [membership])).mono
        headOrigin.erase.supplyExtends)
  rcases tailFactor with ⟨tailPost, tailEquation, tailAdmissible⟩
  have headEquation : finalSubst =
      Subst.seq (Subst.seq post tailPost) S1 := by
    rw [terminalEquation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S1
  have headTyping := headUnder headEquation
    (tailAdmissible.seq admissible)
  have tailTyping := tailUnder terminalEquation admissible
  exact ExprsTy.cons headTyping tailTyping

end DDChecksOrigin

namespace DDSynthOrigin

/-- Application transports the function child across the shape-allocation,
alignment, argument-checking, and external suffixes.  The argument already
starts after the function-shape alignment, so it uses only the external
suffix. -/
theorem runtimeErasureUnder_app
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {function argument : Expr} {functionTarget : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 S2 : Subst}
    {q2 : InferenceBase.FreshSupply} {S3 : Subst}
    {ledger ledger1 ledger3 : CapabilityOriginLedger}
    {functionRaw : DDSynth signature q S context function functionTarget q1 S1}
    (functionOrigin : DDSynthOrigin signature functionRaw ledger ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 functionTarget
      (.fn (.var q1.nextTy) (.var (q1.nextTy + 1))) S2)
    {argumentRaw : DDCheck signature
      { q1 with nextTy := q1.nextTy + 2 } S2 context argument
      (.var q1.nextTy) q2 S3}
    (argumentOrigin : DDCheckOrigin signature argumentRaw ledger1 ledger3)
    (functionUnder : RuntimeErasureUnder functionOrigin)
    (argumentUnder : DDCheckOrigin.RuntimeErasureUnder argumentOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeErasureUnder
      (DDSynthOrigin.app functionOrigin aligned argumentOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  obtain ⟨S1b, functionB⟩ := functionOrigin.erase.boundedBy closed Sb
    contextBounded
  have extension := SupplyExtends.bumpTy q1 2
  have domainB : Ty.BoundedBy { q1 with nextTy := q1.nextTy + 2 }
      (.var q1.nextTy) := Ty.BoundedBy.varOf
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
  have codomainB : Ty.BoundedBy { q1 with nextTy := q1.nextTy + 2 }
      (.var (q1.nextTy + 1)) := Ty.BoundedBy.varOf (Nat.lt_succ_self _)
  have shapeB : Ty.BoundedBy { q1 with nextTy := q1.nextTy + 2 }
      (.fn (.var q1.nextTy) (.var (q1.nextTy + 1))) :=
    Ty.BoundedBy.fnOf domainB codomainB
  have S2b := aligned.erase.boundedBy (S1b.mono extension)
    (functionB.mono extension) shapeB
  have argumentFactor := DDCheckOrigin.factorize argumentOrigin closed S2b
    (contextBounded.mono
      (functionOrigin.erase.supplyExtends.trans extension)) domainB
  have allocation := DDErasure.StateFactorization.ofTransition
    (S := S1) extension (DDLedger.RefinesBelow.refl q1 ledger1)
  have alignment := DDErasure.StateFactorization.ofAlignTypes aligned
    (S1b.mono extension) (functionB.mono extension) shapeB
  have remainderFactor := (allocation.trans alignment).trans argumentFactor
  rcases argumentFactor with
    ⟨argumentPost, argumentEquation, argumentAdmissible⟩
  rcases remainderFactor with
    ⟨remainderPost, remainderEquation, remainderAdmissible⟩
  have functionEquation : finalSubst =
      Subst.seq (Subst.seq post remainderPost) S1 := by
    rw [terminalEquation, remainderEquation]
    exact PhasedPost.seq_assoc post remainderPost S1
  have functionTyping := functionUnder functionEquation
    (remainderAdmissible.seq admissible)
  have argumentTyping := argumentUnder terminalEquation admissible
  have functionShapeAtS3 : S3.apply functionTarget =
      S3.apply (.fn (.var q1.nextTy) (.var (q1.nextTy + 1))) := by
    rw [argumentEquation, Subst.seq_apply, Subst.seq_apply]
    exact congrArg argumentPost.apply aligned.output_equal
  have finalFunctionShape : finalSubst.apply functionTarget =
      finalSubst.apply (.fn (.var q1.nextTy)
        (.var (q1.nextTy + 1))) := by
    rw [terminalEquation, Subst.seq_apply, Subst.seq_apply]
    exact congrArg post.apply functionShapeAtS3
  have functionExpectedRaw : RuntimeTyping signature
      (context.applySubst finalSubst) function
      (finalSubst.apply
        (.fn (.var q1.nextTy) (.var (q1.nextTy + 1)))) := by
    rw [← finalFunctionShape]
    exact functionTyping
  have functionExpected : RuntimeTyping signature
      (context.applySubst finalSubst) function
      (.fn (finalSubst.apply (.var q1.nextTy))
        (finalSubst.apply (.var (q1.nextTy + 1)))) := by
    simpa only [Subst.apply_fn] using functionExpectedRaw
  exact RuntimeTyping.app functionExpected argumentTyping

/-- Constructor synthesis transports its checked children across the final
export-freezing transition.  Closed declarations make the canonical fresh
constructor instance compositional under the final substitution. -/
theorem runtimeErasureUnder_ctor
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenUnder : DDChecksOrigin.RuntimeErasureUnder childrenOrigin)
    (closed : signature.SchemesClosed) :
    RuntimeErasureUnder (DDSynthOrigin.ctor lookup childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have freezing := DDErasure.AdmissiblePostBetween.ofTransition
    (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeExport q' ledger1 S'
      (Inference.freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2)
  have childrenAdmissible : DDErasure.AdmissiblePostBetween q' final
      ledger1 finalLedger post := by
    simpa only [Subst.seq_id_right] using freezing.seq admissible
  have childrenTyping := childrenUnder terminalEquation childrenAdmissible
  have instanceTyping : scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map
        finalSubst.apply)
      (finalSubst.apply
        (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
    apply CtorScheme.Inst.transport
      (InferenceBase.instantiateCtorScheme_sound q scheme)
    apply CtorScheme.instCompositionAdm_of_free_fixed
    · intro varId membership
      rw [(closed.dataCtors lookup).1] at membership
      exact nomatch membership
    · intro varId membership
      rw [(closed.dataCtors lookup).2] at membership
      exact nomatch membership
  exact RuntimeTyping.ctor lookup instanceTyping childrenTyping

/-- Primitive synthesis has the same allocation/check/freeze erasure shape
as constructor synthesis. -/
theorem runtimeErasureUnder_prim
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findPrimitive op = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenUnder : DDChecksOrigin.RuntimeErasureUnder childrenOrigin)
    (closed : signature.SchemesClosed) :
    RuntimeErasureUnder (DDSynthOrigin.prim lookup childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have freezing := DDErasure.AdmissiblePostBetween.ofTransition
    (SupplyExtends.refl q')
    (DDLedger.RefinesBelow.freezeExport q' ledger1 S'
      (Inference.freshCapImages q scheme.capBinders)
      (InferenceBase.instantiateCtorScheme q scheme).value.2)
  have childrenAdmissible : DDErasure.AdmissiblePostBetween q' final
      ledger1 finalLedger post := by
    simpa only [Subst.seq_id_right] using freezing.seq admissible
  have childrenTyping := childrenUnder terminalEquation childrenAdmissible
  have instanceTyping : scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map
        finalSubst.apply)
      (finalSubst.apply
        (InferenceBase.instantiateCtorScheme q scheme).value.2) := by
    apply CtorScheme.Inst.transport
      (InferenceBase.instantiateCtorScheme_sound q scheme)
    apply CtorScheme.instCompositionAdm_of_free_fixed
    · intro varId membership
      rw [(closed.primitives lookup).1] at membership
      exact nomatch membership
    · intro varId membership
      rw [(closed.primitives lookup).2] at membership
      exact nomatch membership
  exact RuntimeTyping.prim lookup instanceTyping childrenTyping

/-- Matcher-specific recursion transports its matcher body through the final
ordinary alignment and the external suffix.  Placeholder construction
supplies the domain/codomain bounds needed at the body cut. -/
theorem runtimeErasureUnder_fixMatcher
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {clauses : List Clause}
    {domain codomain : Ty} {q0 : InferenceBase.FreshSupply}
    {bodyTarget : Ty} {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholder : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q0))
    {bodyRaw : DDSynth signature q0 S
      ((argument, NamedScheme.mono domain) ::
        (self, NamedScheme.mono (.fn domain codomain)) :: context)
      (.matcher clauses) bodyTarget q1 S1}
    (bodyOrigin : DDSynthOrigin signature bodyRaw
      (DDLedger.markCapRange ledger q q0) ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 bodyTarget codomain S')
    (bodyUnder : RuntimeErasureUnder bodyOrigin)
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (contextBounded : Context.BoundedBy q context) :
    RuntimeErasureUnder
      (DDSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin
        aligned) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  obtain ⟨domainB, codomainB⟩ :=
    fixMatcherPlaceholderSupply_boundedBy placeholder
  have extension := SupplyExtends.fixMatcherPlaceholder placeholder
  have bodyContextB : Context.BoundedBy q0
      ((argument, NamedScheme.mono domain) ::
        (self, NamedScheme.mono (.fn domain codomain)) :: context) :=
    Context.BoundedBy.cons (NamedScheme.BoundedBy.ofMono domainB)
      (Context.BoundedBy.cons
        (NamedScheme.BoundedBy.ofMono (Ty.BoundedBy.fnOf domainB codomainB))
        (contextBounded.mono extension))
  obtain ⟨S1b, bodyB⟩ := bodyOrigin.erase.boundedBy closed
    (Sb.mono extension) bodyContextB
  rcases aligned.factorPost S1b bodyB
      (codomainB.mono bodyOrigin.erase.supplyExtends) with
    ⟨alignPost, alignEquation, alignAdmissible⟩
  have bodyEquation : finalSubst =
      Subst.seq (Subst.seq post alignPost) S1 := by
    rw [terminalEquation, alignEquation]
    exact PhasedPost.seq_assoc post alignPost S1
  have bodyTyping := bodyUnder bodyEquation
    (alignAdmissible.seq admissible)
  have finalResultEquality : finalSubst.apply bodyTarget =
      finalSubst.apply codomain := by
    rw [terminalEquation, Subst.seq_apply, Subst.seq_apply]
    exact congrArg post.apply aligned.output_equal
  have bodyExpected : RuntimeTyping signature
      (Context.applySubst finalSubst
        ((argument, NamedScheme.mono domain) ::
          (self, NamedScheme.mono (.fn domain codomain)) :: context))
      (.matcher clauses) (finalSubst.apply codomain) := by
    rw [← finalResultEquality]
    exact bodyTyping
  have bodyExpected' : RuntimeTyping signature
      ((argument, NamedScheme.mono (finalSubst.apply domain)) ::
        (self, NamedScheme.mono
          (.fn (finalSubst.apply domain) (finalSubst.apply codomain))) ::
        context.applySubst finalSubst)
      (.matcher clauses) (finalSubst.apply codomain) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyExpected
  exact RuntimeTyping.fixE distinct direct bodyExpected'

theorem runtimeErasure_fix_of_terminal_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {body : Expr}
    {bodyTarget : Ty} {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (distinct : self ≠ argument) (direct : DirectSelf.Holds self body)
    (nonMatcher : NonMatcherBody body)
    {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, NamedScheme.mono (.var q.nextTy)) ::
        (self, NamedScheme.mono (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) ::
        context) body bodyTarget q1 S1}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 bodyTarget
      (.var (q.nextTy + 1)) S')
    (bodyAtTerminal : RuntimeTyping signature
      ((argument, NamedScheme.mono (S'.apply (.var q.nextTy))) ::
        (self, NamedScheme.mono
          (.fn (S'.apply (.var q.nextTy))
            (S'.apply (.var (q.nextTy + 1))))) ::
        context.applySubst S') body (S'.apply bodyTarget)) :
    RuntimeErasure
      (DDSynthOrigin.fix distinct direct nonMatcher bodyOrigin aligned) := by
  unfold RuntimeErasure
  simp only [Subst.apply_fn]
  have bodyAtRawContext : RuntimeTyping signature
      (Context.applySubst S' ((argument, NamedScheme.mono (.var q.nextTy)) ::
        (self, NamedScheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context))
      body (S'.apply bodyTarget) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyAtTerminal
  have bodyExpectedRaw := aligned.transportRuntime
    (signature := signature)
    (context := (argument, NamedScheme.mono (.var q.nextTy)) ::
      (self, NamedScheme.mono
        (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
    (expression := body) bodyAtRawContext
  have bodyExpected : RuntimeTyping signature
      ((argument, NamedScheme.mono (S'.apply (.var q.nextTy))) ::
        (self, NamedScheme.mono
          (.fn (S'.apply (.var q.nextTy))
            (S'.apply (.var (q.nextTy + 1))))) ::
        context.applySubst S') body (S'.apply (.var (q.nextTy + 1))) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyExpectedRaw
  exact RuntimeTyping.fixE distinct direct bodyExpected

theorem runtimeErasure_app_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {function argument : Expr} {functionTarget : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 S2 : Subst}
    {q2 : InferenceBase.FreshSupply} {S3 : Subst}
    {ledger ledger1 ledger3 : CapabilityOriginLedger}
    {functionRaw : DDSynth signature q S context function functionTarget q1 S1}
    (functionOrigin : DDSynthOrigin signature functionRaw ledger ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 functionTarget
      (.fn (.var q1.nextTy) (.var (q1.nextTy + 1))) S2)
    {argumentRaw : DDCheck signature
      { q1 with nextTy := q1.nextTy + 2 } S2 context argument
      (.var q1.nextTy) q2 S3}
    (argumentOrigin : DDCheckOrigin signature argumentRaw ledger1 ledger3)
    (functionAtTerminal : RuntimeTyping signature (context.applySubst S3)
      function (.fn (S3.apply (.var q1.nextTy))
        (S3.apply (.var (q1.nextTy + 1)))))
    (argumentErasure : DDCheckOrigin.RuntimeErasure argumentOrigin) :
    RuntimeErasure
      (DDSynthOrigin.app functionOrigin aligned argumentOrigin) := by
  unfold RuntimeErasure
  change RuntimeTyping signature (context.applySubst S3) argument
    (S3.apply (.var q1.nextTy)) at argumentErasure
  exact RuntimeTyping.app functionAtTerminal argumentErasure

theorem runtimeErasure_ctor_of_children_and_instance
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenErasure : DDChecksOrigin.RuntimeErasure childrenOrigin)
    (instanceTyping : scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map S'.apply)
      (S'.apply (InferenceBase.instantiateCtorScheme q scheme).value.2)) :
    RuntimeErasure (DDSynthOrigin.ctor lookup childrenOrigin) := by
  unfold RuntimeErasure
  change ExprsTy signature (context.applySubst S') expressions
    ((InferenceBase.instantiateCtorScheme q scheme).value.1.map S'.apply)
    at childrenErasure
  exact RuntimeTyping.ctor lookup instanceTyping childrenErasure

/-- Closed frozen declarations discharge ordinary constructor composition. -/
theorem runtimeErasure_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenErasure : DDChecksOrigin.RuntimeErasure childrenOrigin)
    (closed : signature.SchemesClosed) :
    RuntimeErasure (DDSynthOrigin.ctor lookup childrenOrigin) := by
  apply runtimeErasure_ctor_of_children_and_instance lookup childrenOrigin
    childrenErasure
  apply CtorScheme.Inst.transport
    (InferenceBase.instantiateCtorScheme_sound q scheme)
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    rw [(closed.dataCtors lookup).1] at membership
    exact nomatch membership
  · intro varId membership
    rw [(closed.dataCtors lookup).2] at membership
    exact nomatch membership

theorem runtimeErasure_prim_of_children_and_instance
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findPrimitive op = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenErasure : DDChecksOrigin.RuntimeErasure childrenOrigin)
    (instanceTyping : scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map S'.apply)
      (S'.apply (InferenceBase.instantiateCtorScheme q scheme).value.2)) :
    RuntimeErasure (DDSynthOrigin.prim lookup childrenOrigin) := by
  unfold RuntimeErasure
  change ExprsTy signature (context.applySubst S') expressions
    ((InferenceBase.instantiateCtorScheme q scheme).value.1.map S'.apply)
    at childrenErasure
  exact RuntimeTyping.prim lookup instanceTyping childrenErasure

/-- Closed frozen declarations discharge primitive-instance composition. -/
theorem runtimeErasure_prim_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {op : PrimOp} {expressions : List Expr}
    {scheme : CtorScheme} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (lookup : signature.findPrimitive op = some scheme)
    {children : DDChecks signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S context
      expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
    (childrenOrigin : DDChecksOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger1)
    (childrenErasure : DDChecksOrigin.RuntimeErasure childrenOrigin)
    (closed : signature.SchemesClosed) :
    RuntimeErasure (DDSynthOrigin.prim lookup childrenOrigin) := by
  apply runtimeErasure_prim_of_children_and_instance lookup childrenOrigin
    childrenErasure
  apply CtorScheme.Inst.transport
    (InferenceBase.instantiateCtorScheme_sound q scheme)
  apply CtorScheme.instCompositionAdm_of_free_fixed
  · intro varId membership
    rw [(closed.primitives lookup).1] at membership
    exact nomatch membership
  · intro varId membership
    rw [(closed.primitives lookup).2] at membership
    exact nomatch membership

theorem runtimeErasure_let_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {name : String} {value body : Expr}
    {valueTarget : Ty} {q1 : InferenceBase.FreshSupply} {S1 : Subst}
    {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 ledger' : CapabilityOriginLedger}
    {valueRaw : DDSynth signature q S context value valueTarget q1 S1}
    (valueOrigin : DDSynthOrigin signature valueRaw ledger ledger1)
    {bodyRaw : DDSynth signature q1 S1
      ((name, signature.generalize (context.applySubst S1)
        (S1.apply valueTarget)) :: context) body bodyTarget q' S'}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger1 ledger')
    (stable :
      (signature.generalize (context.applySubst S1)
        (S1.apply valueTarget)).applySubst S' =
      signature.generalize (context.applySubst S') (S'.apply valueTarget))
    (valueAtTerminal : RuntimeTyping signature (context.applySubst S')
      value (S'.apply valueTarget))
    (bodyErasure : RuntimeErasure bodyOrigin) :
    RuntimeErasure (DDSynthOrigin.letE valueOrigin bodyOrigin stable) := by
  unfold RuntimeErasure at bodyErasure |- 
  change RuntimeTyping signature
    ((name, (signature.generalize (context.applySubst S1)
      (S1.apply valueTarget)).applySubst S') :: context.applySubst S')
    body (S'.apply bodyTarget) at bodyErasure
  rw [stable] at bodyErasure
  exact RuntimeTyping.letE valueAtTerminal bodyErasure

/--
Matcher finalization is structural once the mutually erased clause family has
produced the shared resolved-clause certificate.  `capabilityFixed` is the
small remaining ledger-to-substitution fact: final producer leaves must no
longer change at this terminal cut.
-/
theorem runtimeErasure_matcher_of_clauses
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {clauses : List Clause}
    {rawHoleLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst} {evidence : List Shape.Evidence} {capability : Cap}
    {ledger ledger1 : CapabilityOriginLedger}
    {clausesRaw : DDClauses signature
      { q with nextTy := q.nextTy + 1 } S context clauses
      (.var q.nextTy) rawHoleLists q' S'}
    (clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger1)
    (collected : Inference.collectClauseEvidence signature.toMatcherSig
      clauses (terminalHoleCaps S' rawHoleLists) = some evidence)
    (inferred : Shape.inferShape signature.observability evidence =
      some capability)
    (clauseCaps : Inference.clauseCapsListCheck signature capability clauses
      (terminalHoleCaps S' rawHoleLists) = true)
    (catchAll : Inference.catchAllLastCheck clauses = true)
    (binders : Inference.matcherBindersCheck clauses = true)
    (arms : Inference.armExhaustiveCheck signature clauses
      (S'.apply (.var q.nextTy)) = true)
    (coverage : Inference.coverageCheck signature.toMatcherSig clauses
      capability = true)
    (clausesErasure : ResolvedClausesTy signature (context.applySubst S')
      clauses capability (S'.apply (.var q.nextTy)) evidence)
    (capabilityFixed : capability.apply S'.cap = capability) :
    RuntimeErasure
      (DDSynthOrigin.matcher clausesOrigin collected inferred clauseCaps
        catchAll binders arms coverage) := by
  unfold RuntimeErasure
  rw [Subst.apply_matcher, capabilityFixed]
  have binderWitness := Inference.matcherBindersCheck_sound binders
  exact RuntimeTyping.matcher clausesErasure inferred
    (Inference.catchAllLastCheck_sound catchAll)
    (Inference.armExhaustiveCheck_sound arms) binderWitness.1 binderWitness.2
    (Inference.coverageCheck_sound coverage)

theorem runtimeErasure_matchAll_of_terminal_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {target matcher : Expr} {pattern : Pattern}
    {body : Expr} {targetTarget : Ty}
    {q1 : InferenceBase.FreshSupply} {S1 : Subst}
    {dual : Dual} {bindings : MonoCtx} {q2 : InferenceBase.FreshSupply}
    {S2 S3 : Subst} {q3 : InferenceBase.FreshSupply} {S4 : Subst}
    {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger1 ledger2 ledger3 ledger' : CapabilityOriginLedger}
    {targetRaw : DDSynth signature q S context target targetTarget q1 S1}
    (targetOrigin : DDSynthOrigin signature targetRaw ledger ledger1)
    {patternRaw : DDPattern signature q1 S1 context [] [] pattern dual
      bindings q2 S2}
    (patternOrigin : DDPatternOrigin signature patternRaw ledger1 ledger2)
    (targetAligned : DDAlignTypesWithLedger ledger2 S2 dual.target
      targetTarget S3)
    {matcherRaw : DDCheck signature q2 S3 context matcher
      (.slot dual.cap targetTarget) q3 S4}
    (matcherOrigin : DDCheckOrigin signature matcherRaw ledger2 ledger3)
    {bodyRaw : DDSynth signature q3 S4
      (bindings.toContext ++ context) body bodyTarget q' S'}
    (bodyOrigin : DDSynthOrigin signature bodyRaw ledger3 ledger')
    (targetAtTerminal : RuntimeTyping signature (context.applySubst S')
      target (S'.apply targetTarget))
    (patternAtTerminal : ResolvedPatternTy signature S'
      (context.applySubst S') [] [] pattern
      (dual.cap.apply S'.cap) (S'.apply targetTarget)
      (bindings.applySubst S'))
    (matcherAtTerminal : RuntimeTyping signature (context.applySubst S')
      matcher (.slot (dual.cap.apply S'.cap) (S'.apply targetTarget)))
    (bodyErasure : RuntimeErasure bodyOrigin) :
    RuntimeErasure
      (DDSynthOrigin.matchAll targetOrigin patternOrigin targetAligned
        matcherOrigin bodyOrigin) := by
  unfold RuntimeErasure at bodyErasure |- 
  rw [Context.applySubst_append, ← MonoCtx.toContext_applySubst]
    at bodyErasure
  simpa only [Subst.apply_listT] using
    RuntimeTyping.matchAll targetAtTerminal patternAtTerminal matcherAtTerminal
      bodyErasure

theorem runtimeErasure_fixMatcher_of_terminal_body
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : Context} {self argument : String} {clauses : List Clause}
    {domain codomain : Ty} {q0 : InferenceBase.FreshSupply}
    {bodyTarget : Ty} {q1 : InferenceBase.FreshSupply} {S1 S' : Subst}
    {ledger ledger1 : CapabilityOriginLedger}
    (distinct : self ≠ argument)
    (direct : DirectSelf.Holds self (.matcher clauses))
    (placeholder : fixMatcherPlaceholderSupply signature clauses q =
      some (domain, codomain, q0))
    {bodyRaw : DDSynth signature q0 S
      ((argument, NamedScheme.mono domain) ::
        (self, NamedScheme.mono (.fn domain codomain)) :: context)
      (.matcher clauses) bodyTarget q1 S1}
    (bodyOrigin : DDSynthOrigin signature bodyRaw
      (DDLedger.markCapRange ledger q q0) ledger1)
    (aligned : DDAlignTypesWithLedger ledger1 S1 bodyTarget codomain S')
    (bodyAtTerminal : RuntimeTyping signature
      ((argument, NamedScheme.mono (S'.apply domain)) ::
        (self, NamedScheme.mono (.fn (S'.apply domain) (S'.apply codomain))) ::
        context.applySubst S') (.matcher clauses) (S'.apply bodyTarget)) :
    RuntimeErasure
      (DDSynthOrigin.fixMatcher distinct direct placeholder bodyOrigin
        aligned) := by
  unfold RuntimeErasure
  simp only [Subst.apply_fn]
  have bodyAtRawContext : RuntimeTyping signature
      (Context.applySubst S' ((argument, NamedScheme.mono domain) ::
        (self, NamedScheme.mono (.fn domain codomain)) :: context))
      (.matcher clauses) (S'.apply bodyTarget) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyAtTerminal
  have bodyExpectedRaw := aligned.transportRuntime
    (signature := signature)
    (context := (argument, NamedScheme.mono domain) ::
      (self, NamedScheme.mono (.fn domain codomain)) :: context)
    (expression := .matcher clauses) bodyAtRawContext
  have bodyExpected : RuntimeTyping signature
      ((argument, NamedScheme.mono (S'.apply domain)) ::
        (self, NamedScheme.mono (.fn (S'.apply domain) (S'.apply codomain))) ::
        context.applySubst S') (.matcher clauses) (S'.apply codomain) := by
    simpa only [Context.applySubst, List.map_cons, NamedScheme.applySubst_mono,
      Subst.apply_fn] using bodyExpectedRaw
  exact RuntimeTyping.fixE distinct direct bodyExpected

end DDSynthOrigin

end TypePM
