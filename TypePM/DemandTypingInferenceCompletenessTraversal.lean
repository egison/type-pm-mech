import TypePM.DemandTypingInferenceCompletenessStateMutual
import TypePM.DemandTypingInferenceCompletenessSolver
import TypePM.DemandTypingInferenceCompletenessContext
import TypePM.DemandTypingInferenceCompletenessContextBisimulation
import TypePM.DemandTypingInferenceCompletenessProtected
import TypePM.DemandTypingInferenceCompletenessIdempotence
import TypePM.DemandTypingOriginMetatheory

/-!
# Raw traversal completeness

This module is the traversal-facing half of inference completeness.  The DD
and executable solvers may choose different orientations for the same MGU, so
the induction invariant does not identify their prevailing substitutions.
Instead it threads mutual factorization together with the pieces of mutable
state that syntax-directed allocation determines literally: the fresh supply
and capability-origin ledger.

The result packages below deliberately stop before terminal validation.  They
are the common motives for the mutually recursive raw traversal proof.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessTraversal

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessSolver
open DemandTypingInferenceCompletenessProtected
open DemandTypingInferenceCompletenessContext
open DemandTypingInferenceCompletenessContextBisimulation

/-- State relation used at every recursive traversal boundary.  History,
protected producer leaves, and provenance sources are append-only evidence
owned by the executable run; the DD indices determine only supply, prevailing
substitution up to mutual MGU factorization, and the chronological origin
ledger. -/
structure TraversalStateCorrespondence
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (executable : InferState) : Type where
  supply_eq : executable.supply = q
  ledger_eq : executable.capabilityOrigins = ledger
  prevailing : StateBisimulation ledger declarative executable
  declarative_bounded : declarative.BoundedBy q
  executable_bounded : executable.prevailing.BoundedBy q
  forward_bounded : prevailing.forward.BoundedBy q
  reverse_bounded : prevailing.reverse.BoundedBy q
  ledger_below : DDLedger.LedgerBelow q ledger
  protected_origins : ProtectedCapOrigins executable
  protected_below : ProtectedCapsBelowSupply executable
  allocated_recorded : AllocatedCapsRecorded executable

/-- Extending the origin ledger with a canonical scheme-instance batch
preserves an admissible post that is bounded at the incoming supply.  Old
variables retain their origin, while every newly allocated variable is fixed
by boundedness and is therefore admissible at its new rename-only origin. -/
theorem admissiblePost_markSchemeInstance_of_bounded
    {q : InferenceBase.FreshSupply} {ledger : CapabilityOriginLedger}
    {post : Subst} (admissible : AdmissiblePost ledger post)
    (bounded : post.BoundedBy q) (scheme : Scheme) :
    AdmissiblePost (DDLedger.markSchemeInstance ledger q scheme) post := by
  constructor
  intro varId
  by_cases below : varId.id < q.nextCap
  · have notFresh : varId ∉ Scheme.canonicalCapImages q scheme := by
      intro membership
      exact Nat.not_le_of_lt below
        (Scheme.mem_canonicalCapImages_bounds membership).1
    rw [DDLedger.markSchemeInstance,
      CapabilityOriginLedger.originOf_setOrigins_eq, if_neg notFresh]
    cases oldOrigin : ledger.originOf varId with
    | rigid => exact admissible.cap.rigid oldOrigin
    | renameOnly =>
        rcases admissible.cap.renameOnly oldOrigin with
          ⟨image, imageEquation, imageSafe⟩
        refine ⟨image, imageEquation, ?_⟩
        by_cases imageFresh : image ∈ Scheme.canonicalCapImages q scheme
        · rw [CapabilityOriginLedger.originOf_setOrigins_of_mem _ _ _ _
              imageFresh]
          simp
        · rw [CapabilityOriginLedger.originOf_setOrigins_eq,
            if_neg imageFresh]
          exact imageSafe
    | structuralFlexible => trivial
  · have fixed := bounded.capFixedAbove varId (Nat.le_of_not_gt below)
    cases origin : (DDLedger.markSchemeInstance ledger q scheme).originOf varId with
    | rigid => exact fixed
    | renameOnly => exact ⟨varId, fixed, by simp [origin]⟩
    | structuralFlexible => trivial

theorem subst_seq_self_eq_of_idempotent {substitution : Subst}
    (idempotent : substitution.Idempotent) :
    Subst.seq substitution substitution = substitution := by
  apply PhasedPost.subst_ext
  · funext varId
    have fixed := idempotent (.matcher (.var varId) .unit)
    have capFixed :
        (substitution.cap varId).apply substitution.cap =
          substitution.cap varId :=
      (Ty.matcher.inj fixed).1
    simpa only [Subst.seq, CapSubst.comp] using capFixed
  · funext varId
    change substitution.apply (substitution.target varId) =
      substitution.target varId
    simpa only [Subst.apply, Ty.applyCapability, Ty.applyTarget] using
      idempotent (.var varId)

/-- A scheme obtained by looking up an already-normalized context is fixed
by the idempotent substitution used for that normalization. -/
theorem normalizedContext_lookup_scheme_fixed
    {substitution : Subst} {context : Context} {name : String}
    {scheme : Scheme} (idempotent : substitution.Idempotent)
    (lookup : (context.applySubst substitution).find? name = some scheme) :
    scheme.applyMeta substitution = scheme := by
  have contextFixed :
      (context.applySubst substitution).applySubst substitution =
        context.applySubst substitution := by
    rw [← Context.applySubst_seq,
      subst_seq_self_eq_of_idempotent idempotent]
  have lookupFixed := congrArg (fun actual : Context => actual.find? name)
    contextFixed
  rw [Context.find?_applySubst, lookup] at lookupFixed
  exact Option.some.inj lookupFixed

/-- Trace-only events preserve a traversal boundary. -/
def TraversalStateCorrespondence.recordEvent
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (event : TraceEvent)
    (eventRecorded : ∀ varId, varId ∈ event.allocatedCapVars →
      varId ∈ state.capabilityOrigins.map Prod.fst) :
    TraversalStateCorrespondence q declarative ledger
      (state.recordEvent event) := by
  let extension := relation.prevailing.recordEventExtension event
  exact
    ⟨relation.supply_eq, relation.ledger_eq, extension.after,
      relation.declarative_bounded, relation.executable_bounded,
      relation.forward_bounded, relation.reverse_bounded,
      relation.ledger_below,
      relation.protected_origins.recordEvent event,
      relation.protected_below.recordEvent_of_allocated event,
      relation.allocated_recorded.recordEvent event eventRecorded⟩

/-- Provenance-source recording is state-neutral for the typing relation. -/
def stateBisimulationRecordSourceExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (relation : StateBisimulation ledger declarative state)
    (source : ProducerSource) :
    BisimulationExtension relation ledger declarative
      (state.recordSource source) where
  after :=
    { forward := relation.forward
      forwardEquation := by simpa [InferState.prevailing,
        InferState.recordSource] using relation.forwardEquation
      forwardAdmissible := relation.forwardAdmissible
      declarativeIdempotent := relation.declarativeIdempotent
      reverse := relation.reverse
      reverseEquation := by simpa [InferState.prevailing,
        InferState.recordSource] using relation.reverseEquation
      reverseAdmissible := relation.reverseAdmissible
      executableIdempotent := relation.executableIdempotent }
  transportTy := by
    intro declarativeTarget executableTarget related
    exact ⟨by simpa [InferState.prevailing, InferState.recordSource]
        using related.forward,
      by simpa [InferState.prevailing, InferState.recordSource]
        using related.reverse⟩

def TraversalStateCorrespondence.recordSource
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (source : ProducerSource) :
    TraversalStateCorrespondence q declarative ledger
      (state.recordSource source) := by
  let extension := stateBisimulationRecordSourceExtension
    relation.prevailing source
  exact
    ⟨relation.supply_eq, relation.ledger_eq, extension.after,
      relation.declarative_bounded, relation.executable_bounded,
      relation.forward_bounded, relation.reverse_bounded,
      relation.ledger_below,
      relation.protected_origins.recordSource source,
      relation.protected_below.recordSource source,
      relation.allocated_recorded.recordSource source⟩

/-- Visiting one syntax node is trace-only. -/
def TraversalStateCorrespondence.visit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) := by
  exact relation.recordEvent (.visit kind path) (by simp [TraceEvent.allocatedCapVars])

def TraversalStateCorrespondence.visitExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    BisimulationExtension relation.prevailing ledger declarative
      (Inference.visit state kind path) :=
  relation.prevailing.recordEventExtension (.visit kind path)

def TraversalStateCorrespondence.afterVisit
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) :
    TraversalStateCorrespondence q declarative ledger
      (Inference.visit state kind path) :=
  relation.visit kind path

def stateBisimulationFreshTyExtension
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {state : InferState}
    (before : StateBisimulation ledger declarative state)
    (origin : ConstraintOrigin) :
    BisimulationExtension before ledger declarative
      (state.freshTy origin).2 where
  after :=
    { forward := before.forward
      forwardEquation := by
        change declarative = Subst.seq before.forward state.prevailing
        exact before.forwardEquation
      forwardAdmissible := before.forwardAdmissible
      declarativeIdempotent := before.declarativeIdempotent
      reverse := before.reverse
      reverseEquation := by
        change state.prevailing = Subst.seq before.reverse declarative
        exact before.reverseEquation
      reverseAdmissible := before.reverseAdmissible
      executableIdempotent := before.executableIdempotent }
  transportTy := by
    intro declarativeTarget executableTarget related
    refine ⟨?_, ?_⟩
    · change declarative.apply declarativeTarget =
        before.forward.apply (state.prevailing.apply executableTarget)
      exact related.forward
    · change state.prevailing.apply executableTarget =
        before.reverse.apply (declarative.apply declarativeTarget)
      exact related.reverse

def TraversalStateCorrespondence.afterVisitFreshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (kind : NodeKind) (path : SyntaxPath) (origin : ConstraintOrigin) :
    TraversalStateCorrespondence { q with nextTy := q.nextTy + 1 }
      declarative ledger ((Inference.visit state kind path).freshTy origin).2 :=
  by
    let entered := relation.visit kind path
    let extension := SupplyExtends.bumpTy q 1
    refine
      ⟨?_, relation.ledger_eq,
        (stateBisimulationFreshTyExtension
          (relation.visitExtension kind path).after origin).after,
        entered.declarative_bounded.mono extension,
        entered.executable_bounded.mono extension,
        entered.forward_bounded.mono extension,
        entered.reverse_bounded.mono extension,
        entered.ledger_below.mono extension,
        entered.protected_origins.freshTy origin,
        entered.protected_below.freshTy origin,
        entered.allocated_recorded.freshTy origin⟩
    change { state.supply with nextTy := state.supply.nextTy + 1 } =
      { q with nextTy := q.nextTy + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextTy := supply.nextTy + 1 }) relation.supply_eq

def bisimulationExtensionChain3
    {ledger₀ ledger₁ ledger₂ ledger₃ : CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ : Subst} {s₀ s₁ s₂ s₃ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃) :
    BisimulationExtension before ledger₃ S₃ s₃ where
  after := third.after
  transportTy := fun related =>
    third.transportTy (second.transportTy (first.transportTy related))

def bisimulationExtensionChain4
    {ledger₀ ledger₁ ledger₂ ledger₃ ledger₄ :
      CapabilityOriginLedger}
    {S₀ S₁ S₂ S₃ S₄ : Subst}
    {s₀ s₁ s₂ s₃ s₄ : InferState}
    {before : StateBisimulation ledger₀ S₀ s₀}
    (first : BisimulationExtension before ledger₁ S₁ s₁)
    (second : BisimulationExtension first.after ledger₂ S₂ s₂)
    (third : BisimulationExtension second.after ledger₃ S₃ s₃)
    (fourth : BisimulationExtension third.after ledger₄ S₄ s₄) :
    BisimulationExtension before ledger₄ S₄ s₄ where
  after := fourth.after
  transportTy := fun related => fourth.transportTy
    (third.transportTy (second.transportTy (first.transportTy related)))

structure FreshTyCompletion
    (q : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (state : InferState)
    (origin : ConstraintOrigin) : Type where
  target_eq : (state.freshTy origin).1 = .var q.nextTy
  state : TraversalStateCorrespondence
    { q with nextTy := q.nextTy + 1 } declarative ledger
    (state.freshTy origin).2

/-- One target allocation agrees literally with the supply-indexed DD
allocation and leaves the prevailing substitution and origin ledger alone. -/
def TraversalStateCorrespondence.freshTy
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    FreshTyCompletion q declarative ledger state origin := by
  let extension := SupplyExtends.bumpTy q 1
  constructor
  · change Ty.var state.supply.nextTy = Ty.var q.nextTy
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      Ty.var supply.nextTy) relation.supply_eq
  · refine
      ⟨?_, relation.ledger_eq,
        (stateBisimulationFreshTyExtension relation.prevailing origin).after,
        relation.declarative_bounded.mono extension,
        relation.executable_bounded.mono extension,
        relation.forward_bounded.mono extension,
        relation.reverse_bounded.mono extension,
        relation.ledger_below.mono extension,
        relation.protected_origins.freshTy origin,
        relation.protected_below.freshTy origin,
        relation.allocated_recorded.freshTy origin⟩
    change { state.supply with nextTy := state.supply.nextTy + 1 } =
      { q with nextTy := q.nextTy + 1 }
    exact congrArg (fun supply : InferenceBase.FreshSupply =>
      { supply with nextTy := supply.nextTy + 1 }) relation.supply_eq

def TraversalStateCorrespondence.freshTyExtension
    {q : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger state)
    (origin : ConstraintOrigin) :
    BisimulationExtension relation.prevailing ledger declarative
      (state.freshTy origin).2 :=
  stateBisimulationFreshTyExtension relation.prevailing origin

/-- Exact-state initialization is the diagonal of the traversal relation. -/
def TraversalStateCorrespondence.refl
    (state : InferState) (idempotent : state.prevailing.Idempotent)
    (bounded : state.prevailing.BoundedBy state.supply)
    (ledgerBelow : DDLedger.LedgerBelow state.supply
      state.capabilityOrigins)
    (protectedOrigins : ProtectedCapOrigins state)
    (protectedBelow : ProtectedCapsBelowSupply state)
    (allocatedRecorded : AllocatedCapsRecorded state) :
    TraversalStateCorrespondence state.supply state.prevailing
      state.capabilityOrigins state :=
  let prevailing := StateBisimulation.refl _ _ idempotent
  ⟨rfl, rfl, prevailing, bounded, bounded,
    Subst.boundedBy_id _, Subst.boundedBy_id _, ledgerBelow,
    protectedOrigins, protectedBelow, allocatedRecorded⟩

/-- Output relation for one raw synthesized type.  The two raw types need not
be syntactically equal (context instantiation may see differently oriented
prevailing MGUs), but their resolved forms are mutual instances through the
same residuals that relate the two prevailing states. -/
structure TypedTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTarget : Ty)
    (executable : InferState) (executableTarget : Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  target : TyBisimulation state.prevailing declarativeTarget executableTarget

/-- Output relation for a left-to-right list of synthesized types. -/
structure TypedListTraversalStateCorrespondence
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (declarativeTargets : List Ty)
    (executable : InferState) (executableTargets : List Ty) : Type where
  state : TraversalStateCorrespondence q' declarative ledger executable
  targets : TyListBisimulation state.prevailing declarativeTargets
    executableTargets

/-- A common raw type on both sides automatically gives a typed relation. -/
def TypedTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedTraversalStateCorrespondence q' declarative ledger target executable
      target := by
  exact ⟨relation, relation.prevailing.sameTarget target⟩

/-- A common raw list gives the pointwise list relation. -/
def TypedListTraversalStateCorrespondence.of_sameRaw
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {targets : List Ty}
    {executable : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger executable) :
    TypedListTraversalStateCorrespondence q' declarative ledger targets
      executable targets := by
  refine ⟨relation, ?_⟩
  induction targets with
  | nil => exact .nil
  | cons target targets induction =>
      exact .cons (relation.prevailing.sameTarget target) induction

/-- Pointwise mutual type correspondence is closed under product formation. -/
theorem tyListBisimulation_prod
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeTargets executableTargets : List Ty}
    (relation : TyListBisimulation state declarativeTargets executableTargets) :
    TyBisimulation state (.prod declarativeTargets)
      (.prod executableTargets) := by
  constructor
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).forward
    | cons head tail induction =>
        have headForward := head.forward
        unfold Subst.apply at headForward
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headForward]
        injection induction with tailEquality
        rw [tailEquality]
  · induction relation with
    | nil => exact (state.sameTarget (.prod [])).reverse
    | cons head tail induction =>
        have headReverse := head.reverse
        unfold Subst.apply at headReverse
        simp only [Subst.apply, Ty.applyCapability, Ty.applyCapabilityList,
          Ty.applyTarget, Ty.applyTargetList] at induction ⊢
        rw [headReverse]
        injection induction with tailEquality
        rw [tailEquality]

/-- Mutual type correspondence is compositional for function types. -/
theorem tyBisimulation_fn
    {ledger : CapabilityOriginLedger} {declarative : Subst}
    {executable : InferState}
    {state : StateBisimulation ledger declarative executable}
    {declarativeDomain declarativeBody executableDomain executableBody : Ty}
    (domain : TyBisimulation state declarativeDomain executableDomain)
    (body : TyBisimulation state declarativeBody executableBody) :
    TyBisimulation state (.fn declarativeDomain declarativeBody)
      (.fn executableDomain executableBody) := by
  constructor
  · have domainForward := domain.forward
    have bodyForward := body.forward
    unfold Subst.apply at domainForward bodyForward ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainForward, bodyForward]
  · have domainReverse := domain.reverse
    have bodyReverse := body.reverse
    unfold Subst.apply at domainReverse bodyReverse ⊢
    simp only [Ty.applyCapability, Ty.applyTarget]
    rw [domainReverse, bodyReverse]

/-- Output package for expression synthesis. -/
def SynthCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (target : Ty)
    (result : ExprResult) : Type :=
  TypedTraversalStateCorrespondence q' declarative ledger target result.state
    result.target

/-- Output package for expression-list synthesis. -/
def SynthsCompletion
    (q' : InferenceBase.FreshSupply) (declarative : Subst)
    (ledger : CapabilityOriginLedger) (targets : List Ty)
    (result : ExprsResult) : Type :=
  TypedListTraversalStateCorrespondence q' declarative ledger targets
    result.state result.targets

/-- Deterministic completion package for one context-scheme instantiation.
It is separated from expression synthesis because variable traversal may add
a direct-self source after instantiation, while `let` reuses the same paired
context and canonical-opening bridge. -/
structure SchemeInstantiationCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (result : Ty × InferState) (q' : InferenceBase.FreshSupply)
    (ledger' : CapabilityOriginLedger) (target : Ty) : Type where
  supply_eq : result.2.supply = q'
  ledger_eq : result.2.capabilityOrigins = ledger'
  transition : BisimulationExtension before.prevailing ledger' S result.2
  declarative_bounded : S.BoundedBy q'
  executable_bounded : result.2.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger'
  protected_origins : ProtectedCapOrigins result.2
  protected_below : ProtectedCapsBelowSupply result.2
  allocated_recorded : AllocatedCapsRecorded result.2
  target : TyBisimulation transition.after target result.1

/-- Corresponding normalized schemes instantiate in lockstep.  The fresh
images and ledger update are determined solely by binder arities; ambient
metavariable transport affects only the instantiated body. -/
def instantiateSchemeInState_complete
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger initial)
    (signature : FrozenSig) (rawContext normalizedContext : Context)
    (name : String) (declarativeScheme executableScheme : Scheme)
    (forwardScheme : declarativeScheme =
      executableScheme.applyMeta before.prevailing.forward)
    (reverseScheme : executableScheme =
      declarativeScheme.applyMeta before.prevailing.reverse)
    (declarativeNormalized : declarativeScheme.applyMeta S =
      declarativeScheme)
    (executableNormalized : executableScheme.applyMeta initial.prevailing =
      executableScheme) :
    SchemeInstantiationCompletion before
      (instantiateSchemeInState signature rawContext normalizedContext name
        initial executableScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).supply
      (DDLedger.markSchemeInstance ledger q declarativeScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).value := by
  let operation := instantiateSchemeInState signature rawContext
    normalizedContext name initial executableScheme
  let q' := (InferenceBase.instantiateScheme q declarativeScheme).supply
  let ledger' := DDLedger.markSchemeInstance ledger q declarativeScheme
  have supplyExtension : SupplyExtends q q' := by
    exact SupplyExtends.instantiateScheme q declarativeScheme
  let after : StateBisimulation ledger' S operation.2 :=
    { forward := before.prevailing.forward
      forwardEquation := by
        change S = Subst.seq before.prevailing.forward operation.2.prevailing
        simpa [operation, Inference.instantiateSchemeInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.forwardEquation
      forwardAdmissible :=
        admissiblePost_markSchemeInstance_of_bounded
          before.prevailing.forwardAdmissible before.forward_bounded
          declarativeScheme
      declarativeIdempotent := before.prevailing.declarativeIdempotent
      reverse := before.prevailing.reverse
      reverseEquation := by
        change operation.2.prevailing = Subst.seq before.prevailing.reverse S
        simpa [operation, Inference.instantiateSchemeInState,
          InferState.prevailing, InferState.recordEvent] using
          before.prevailing.reverseEquation
      reverseAdmissible :=
        admissiblePost_markSchemeInstance_of_bounded
          before.prevailing.reverseAdmissible before.reverse_bounded
          declarativeScheme
      executableIdempotent := before.prevailing.executableIdempotent }
  let transition : BisimulationExtension before.prevailing ledger' S
      operation.2 :=
    { after := after
      transportTy := by
        intro declarativeTarget executableTarget related
        exact ⟨by simpa [after, operation, Inference.instantiateSchemeInState,
            InferState.prevailing, InferState.recordEvent]
            using related.forward,
          by simpa [after, operation, Inference.instantiateSchemeInState,
            InferState.prevailing, InferState.recordEvent]
            using related.reverse⟩ }
  have actualTarget : operation.1 =
      (InferenceBase.instantiateScheme q executableScheme).value := by
    simp [operation, Inference.instantiateSchemeInState, before.supply_eq]
  have canonical := canonicalInstantiation_tyBisimulation before.prevailing q
    declarativeScheme executableScheme before.declarative_bounded
    before.executable_bounded before.forward_bounded before.reverse_bounded
    forwardScheme reverseScheme declarativeNormalized executableNormalized
  have schemeSupplyEq :
      (InferenceBase.instantiateScheme q executableScheme).supply = q' := by
    dsimp [q']
    rw [forwardScheme]
    cases executableScheme
    rfl
  refine
    { supply_eq := ?_
      ledger_eq := ?_
      transition := transition
      declarative_bounded := before.declarative_bounded.mono supplyExtension
      executable_bounded := ?_
      forward_bounded := before.forward_bounded.mono supplyExtension
      reverse_bounded := before.reverse_bounded.mono supplyExtension
      ledger_below := DDLedger.LedgerBelow.markSchemeInstance declarativeScheme
        before.ledger_below
      protected_origins := before.protected_origins.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      protected_below := before.protected_below.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      allocated_recorded := before.allocated_recorded.instantiateSchemeInState
        signature rawContext normalizedContext name executableScheme
      target := ?_ }
  · simpa [operation, Inference.instantiateSchemeInState,
      before.supply_eq] using schemeSupplyEq
  · simp [DDLedger.markSchemeInstance, Inference.instantiateSchemeInState,
      before.supply_eq, before.ledger_eq, forwardScheme]
  · change initial.prevailing.BoundedBy
      (InferenceBase.instantiateScheme q declarativeScheme).supply
    exact before.executable_bounded.mono supplyExtension
  · rw [actualTarget]
    exact transition.transportTy canonical

/-- A successful executable expression run paired with its typed output
correspondence.  The package lives in `Type` because the state bisimulation
retains the concrete residual substitutions used by later cuts. -/
structure SynthRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (target : Ty) : Type where
  result : ExprResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  ledger_eq : result.state.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  target : TyBisimulation transition.after target result.target

/-- List counterpart of `SynthRunCompletion`. -/
structure SynthsRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option ExprsResult) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger)
    (targets : List Ty) : Type where
  result : ExprsResult
  success : operation = some result
  supply_eq : result.state.supply = q'
  ledger_eq : result.state.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result.state
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.state.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  protected_origins : ProtectedCapOrigins result.state
  protected_below : ProtectedCapsBelowSupply result.state
  allocated_recorded : AllocatedCapsRecorded result.state
  targets : TyListBisimulation transition.after targets result.targets

/-- Repackage a run's proof-relevant transition as the output-only relation. -/
def SynthRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger} {target : Ty}
    (run : SynthRunCompletion before operation q' declarative ledger target) :
    SynthCompletion q' declarative ledger target run.result :=
  ⟨⟨run.supply_eq, run.ledger_eq, run.transition.after,
      run.declarative_bounded, run.executable_bounded,
      run.forward_bounded, run.reverse_bounded, run.ledger_below,
      run.protected_origins, run.protected_below, run.allocated_recorded⟩,
    run.target⟩

def SynthsRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option ExprsResult} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {targets : List Ty}
    (run : SynthsRunCompletion before operation q' declarative ledger targets) :
    SynthsCompletion q' declarative ledger targets run.result :=
  ⟨⟨run.supply_eq, run.ledger_eq, run.transition.after,
      run.declarative_bounded, run.executable_bounded,
      run.forward_bounded, run.reverse_bounded, run.ledger_below,
      run.protected_origins, run.protected_below, run.allocated_recorded⟩,
    run.targets⟩

/-- State-only run package used by alignment cuts. -/
structure StateRunCompletion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    (before : TraversalStateCorrespondence q S ledger₀ initial)
    (operation : Option InferState) (q' : InferenceBase.FreshSupply)
    (declarative : Subst) (ledger : CapabilityOriginLedger) : Type where
  result : InferState
  success : operation = some result
  supply_eq : result.supply = q'
  ledger_eq : result.capabilityOrigins = ledger
  transition : BisimulationExtension before.prevailing ledger declarative
    result
  declarative_bounded : declarative.BoundedBy q'
  executable_bounded : result.prevailing.BoundedBy q'
  forward_bounded : transition.after.forward.BoundedBy q'
  reverse_bounded : transition.after.reverse.BoundedBy q'
  ledger_below : DDLedger.LedgerBelow q' ledger
  protected_origins : ProtectedCapOrigins result
  protected_below : ProtectedCapsBelowSupply result
  allocated_recorded : AllocatedCapsRecorded result

def StateRunCompletion.completion
    {q : InferenceBase.FreshSupply} {S : Subst}
    {ledger₀ : CapabilityOriginLedger} {initial : InferState}
    {before : TraversalStateCorrespondence q S ledger₀ initial}
    {operation : Option InferState} {q' : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    (run : StateRunCompletion before operation q' declarative ledger) :
    TraversalStateCorrespondence q' declarative ledger run.result :=
  ⟨run.supply_eq, run.ledger_eq, run.transition.after,
    run.declarative_bounded, run.executable_bounded,
    run.forward_bounded, run.reverse_bounded, run.ledger_below,
    run.protected_origins, run.protected_below, run.allocated_recorded⟩

/-! ## Ordinary paired alignment -/

/-- Once solver completeness supplies the concrete target-equality step, one
resolved equality cut preserves the proof-relevant traversal invariant.  This
lemma isolates the traversal algebra from the executable solver's fuel proof. -/
noncomputable def runResolvedTargetEq_complete_of_step
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin} {step : SolveStep}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta)
    (solver : PairedUnification.PairedResult ledger
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
    (stepSuccess : solveResolvedWithLedger ledger initial.trace.solves.length
      origin (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step)
    (stepDelta : step.delta = solver.subst) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.targetEq (initial.prevailing.apply executableLeft)
          (initial.prevailing.apply executableRight))) q
      (Subst.seq delta S) ledger := by
  let result := initial.recordSolve step
  let transition := relation.prevailing.pairedCut_recordSolve left right dd
    solver stepDelta
  have ddDeltaBounded : delta.BoundedBy q :=
    dd.exact.boundedBy
      (relation.declarative_bounded.apply declarativeLeftBounded)
      (relation.declarative_bounded.apply declarativeRightBounded)
  have executableDeltaBounded : solver.subst.BoundedBy q :=
    solver.exactPairedMGU.boundedBy
      (relation.executable_bounded.apply executableLeftBounded)
      (relation.executable_bounded.apply executableRightBounded)
  refine
    { result := result
      success := ?_
      supply_eq := relation.supply_eq
      ledger_eq := relation.ledger_eq
      transition := transition
      declarative_bounded := ddDeltaBounded.seq relation.declarative_bounded
      executable_bounded := ?_
      forward_bounded := ?_
      reverse_bounded := ?_
      ledger_below := relation.ledger_below
      protected_origins := relation.protected_origins.recordSolve step
      protected_below := relation.protected_below.recordSolve step
      allocated_recorded := relation.allocated_recorded.recordSolve step }
  · unfold runResolvedConstraint
    rw [relation.ledger_eq, stepSuccess]
    rfl
  · rw [InferState.prevailing_recordSolve, stepDelta]
    exact executableDeltaBounded.seq relation.executable_bounded
  · change (Subst.seq delta relation.prevailing.forward).BoundedBy q
    exact ddDeltaBounded.seq relation.forward_bounded
  · change (Subst.seq solver.subst relation.prevailing.reverse).BoundedBy q
    exact executableDeltaBounded.seq relation.reverse_bounded

/-- A DD solution on the declarative views supplies an admissible solution on
the bisimilar executable views.  Paired-solver completeness therefore creates
the concrete step internally; callers need not predict its orientation. -/
noncomputable def runResolvedTargetEq_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta) :
    StateRunCompletion relation
      (runResolvedConstraint initial origin
        (.targetEq (initial.prevailing.apply executableLeft)
          (initial.prevailing.apply executableRight))) q
      (Subst.seq delta S) ledger := by
  let combined := Subst.seq delta relation.prevailing.forward
  have combinedAdmissible : AdmissiblePost ledger combined :=
    AdmissiblePost.seq dd.admissible relation.prevailing.forwardAdmissible
  have combinedSound :
      combined.apply (initial.prevailing.apply executableLeft) =
        combined.apply (initial.prevailing.apply executableRight) := by
    simp only [combined, Subst.seq_apply, ← left.forward, ← right.forward]
    exact dd.exact.1.1
  have solverExists :=
    solveTargetEqWithLedger_complete_of_admissible combinedAdmissible
      combinedSound initial.trace.solves.length origin
  let solver := Classical.choose solverExists
  have stepExists := Classical.choose_spec solverExists
  let step := Classical.choose stepExists
  have stepFacts := Classical.choose_spec stepExists
  have solverSuccess := stepFacts.1
  have stepDelta := stepFacts.2
  have stepSuccess : solveResolvedWithLedger ledger
      initial.trace.solves.length origin
      (.targetEq (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight)) = some step := by
    exact solverSuccess
  exact runResolvedTargetEq_complete_of_step relation left right
    declarativeLeftBounded declarativeRightBounded executableLeftBounded
    executableRightBounded dd solver stepSuccess stepDelta

/-- The ordinary branch of `alignTypes` is complete.  Matcher/slot two-stage
branches are added by the same state-cut lemma after capability-solver
completeness is connected. -/
noncomputable def alignTypes_ordinary_complete
    {q : InferenceBase.FreshSupply} {S delta : Subst}
    {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeLeft declarativeRight executableLeft executableRight : Ty}
    {origin : ConstraintOrigin}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (left : TyBisimulation relation.prevailing declarativeLeft executableLeft)
    (right : TyBisimulation relation.prevailing declarativeRight executableRight)
    (declarativeLeftBounded : declarativeLeft.BoundedBy q)
    (declarativeRightBounded : declarativeRight.BoundedBy q)
    (executableLeftBounded : executableLeft.BoundedBy q)
    (executableRightBounded : executableRight.BoundedBy q)
    (_declarativeClass :
      alignPairClass (S.apply declarativeLeft) (S.apply declarativeRight) =
        .ordinary)
    (executableClass :
      alignPairClass (initial.prevailing.apply executableLeft)
        (initial.prevailing.apply executableRight) = .ordinary)
    (dd : OriginSafeExactPairedMGU ledger
      (S.apply declarativeLeft) (S.apply declarativeRight) delta) :
    StateRunCompletion relation
      (alignTypes initial origin executableLeft executableRight) q
      (Subst.seq delta S) ledger := by
  have core := runResolvedTargetEq_complete (origin := origin) relation left right
    declarativeLeftBounded declarativeRightBounded executableLeftBounded
    executableRightBounded dd
  let aligned := core.result
  let result := aligned.recordEvent (.typeAlignment
    initial.trace.solves.length aligned.trace.solves.length executableLeft
    executableRight (initial.prevailing.apply executableLeft)
    (initial.prevailing.apply executableRight))
  let finishExtension := core.transition.after.recordEventExtension
    (.typeAlignment initial.trace.solves.length aligned.trace.solves.length
      executableLeft executableRight
      (initial.prevailing.apply executableLeft)
      (initial.prevailing.apply executableRight))
  refine
    { result := result
      success := ?_
      supply_eq := core.supply_eq
      ledger_eq := core.ledger_eq
      transition := core.transition.seq finishExtension
      declarative_bounded := core.declarative_bounded
      executable_bounded := core.executable_bounded
      forward_bounded := core.forward_bounded
      reverse_bounded := core.reverse_bounded
      ledger_below := core.ledger_below
      protected_origins := core.protected_origins.recordEvent _
      protected_below := core.protected_below.recordEvent_of_allocated _
      allocated_recorded := core.allocated_recorded.recordEvent _
        (by simp [TraceEvent.allocatedCapVars]) }
  · have coreEq : alignTypesCore initial origin executableLeft
        executableRight =
        runResolvedConstraint initial origin
          (.targetEq (initial.prevailing.apply executableLeft)
            (initial.prevailing.apply executableRight)) := by
      generalize leftEq : initial.prevailing.apply executableLeft = leftView
      generalize rightEq : initial.prevailing.apply executableRight = rightView
      cases leftView <;> cases rightView <;>
        simp_all [alignTypesCore, alignPairClass]
    unfold alignTypes
    rw [coreEq, core.success]
    rfl

/-- Finishing an expression changes only the trace and retains its raw target. -/
def synthCompletion_finishExpr
    {q' : InferenceBase.FreshSupply} {declarative : Subst}
    {ledger : CapabilityOriginLedger} {target : Ty} {state : InferState}
    (relation : TraversalStateCorrespondence q' declarative ledger state)
    (expression : Expr) (path : SyntaxPath) :
    SynthCompletion q' declarative ledger target
      (finishExpr expression path target state) := by
  exact TypedTraversalStateCorrespondence.of_sameRaw
    (relation.recordEvent (.inferredExpr expression target path)
      (by simp [TraceEvent.allocatedCapVars]))

/-! ## Solver-independent expression constructors -/

/-- Integer literals always complete at any positive fuel. -/
def inferExprFuel_lit_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {value : Int} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path (.lit value)
        initial) q declarative ledger .int := by
  let entered := visit initial .exprLit path
  let result := finishExpr (.lit value) path .int entered
  let visitExtension := relation.visitExtension .exprLit path
  let finishExtension := visitExtension.after.recordEventExtension
    (.inferredExpr (.lit value) .int path)
  let finalRelation := (relation.visit .exprLit path).recordEvent
    (.inferredExpr (.lit value) .int path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := relation.supply_eq
      ledger_eq := relation.ledger_eq
      transition := visitExtension.seq finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp [inferExprFuel, result, entered, finishExpr, visit]
  exact (visitExtension.seq finishExtension).after.sameTarget .int

/-- Variable synthesis is complete for paired declarative/executable
contexts.  Lookup determines corresponding normalized schemes; canonical
fresh instantiation then advances both traversals through the same binder
spans and origin-ledger batch. -/
noncomputable def inferExprFuel_var_complete
    {signature : FrozenSig}
    {declarativeContext executableContext : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {name : String} {q : InferenceBase.FreshSupply}
    {S : Subst} {ledger : CapabilityOriginLedger} {initial : InferState}
    {declarativeScheme : Scheme}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (contexts : ContextBisimulation relation.prevailing declarativeContext
      executableContext)
    (lookup : (declarativeContext.applySubst S).find? name =
      some declarativeScheme)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature executableContext selfEnv path
        (.var name) initial)
      (InferenceBase.instantiateScheme q declarativeScheme).supply S
      (DDLedger.markSchemeInstance ledger q declarativeScheme)
      (InferenceBase.instantiateScheme q declarativeScheme).value := by
  cases executableLookup :
      (executableContext.applySubst initial.prevailing).find? name with
  | none =>
      have impossible := congrArg (fun context : Context => context.find? name)
        contexts.forward
      simp [lookup, Context.find?_applySubst, executableLookup] at impossible
  | some executableScheme =>
      have schemeDirections := contexts.lookup lookup executableLookup
      have declarativeNormalized := normalizedContext_lookup_scheme_fixed
        relation.prevailing.declarativeIdempotent lookup
      have executableNormalized := normalizedContext_lookup_scheme_fixed
        relation.prevailing.executableIdempotent executableLookup
      let entered := visit initial .exprVar path
      let enteredRelation := relation.visit .exprVar path
      let normalizedExecutable := executableContext.applySubst entered.prevailing
      have executableLookupEntered : normalizedExecutable.find? name =
          some executableScheme := by
        simpa [normalizedExecutable, entered, visit, InferState.prevailing,
          InferState.recordEvent] using executableLookup
      have forwardEntered : declarativeScheme =
          executableScheme.applyMeta enteredRelation.prevailing.forward := by
        exact schemeDirections.1
      have reverseEntered : executableScheme =
          declarativeScheme.applyMeta enteredRelation.prevailing.reverse := by
        exact schemeDirections.2
      have executableNormalizedEntered :
          executableScheme.applyMeta entered.prevailing = executableScheme := by
        simpa [entered, visit, InferState.prevailing, InferState.recordEvent]
          using executableNormalized
      let instantiated := instantiateSchemeInState signature executableContext
        normalizedExecutable name entered executableScheme
      let instantiationComplete := instantiateSchemeInState_complete
        enteredRelation signature executableContext normalizedExecutable name
        declarativeScheme executableScheme forwardEntered reverseEntered
        declarativeNormalized executableNormalizedEntered
      let instantiatedRelation : TraversalStateCorrespondence
          (InferenceBase.instantiateScheme q declarativeScheme).supply S
          (DDLedger.markSchemeInstance ledger q declarativeScheme)
          instantiated.2 :=
        ⟨instantiationComplete.supply_eq, instantiationComplete.ledger_eq,
          instantiationComplete.transition.after,
          instantiationComplete.declarative_bounded,
          instantiationComplete.executable_bounded,
          instantiationComplete.forward_bounded,
          instantiationComplete.reverse_bounded,
          instantiationComplete.ledger_below,
          instantiationComplete.protected_origins,
          instantiationComplete.protected_below,
          instantiationComplete.allocated_recorded⟩
      let visitExtension := relation.visitExtension .exprVar path
      cases selfLookup : selfEnv.find? name with
      | none =>
          let finishEvent := TraceEvent.inferredExpr (.var name)
            instantiated.1 path
          let finishExtension :=
            instantiationComplete.transition.after.recordEventExtension
              finishEvent
          let result := finishExpr (.var name) path instantiated.1
            instantiated.2
          let finalRelation := instantiatedRelation.recordEvent finishEvent
            (by simp [finishEvent, TraceEvent.allocatedCapVars])
          refine
            { result := result
              success := ?_
              supply_eq := finalRelation.supply_eq
              ledger_eq := finalRelation.ledger_eq
              transition :=
                (visitExtension.seq instantiationComplete.transition).seq
                  finishExtension
              declarative_bounded := finalRelation.declarative_bounded
              executable_bounded := finalRelation.executable_bounded
              forward_bounded := finalRelation.forward_bounded
              reverse_bounded := finalRelation.reverse_bounded
              ledger_below := finalRelation.ledger_below
              protected_origins := finalRelation.protected_origins
              protected_below := finalRelation.protected_below
              allocated_recorded := finalRelation.allocated_recorded
              target := finishExtension.transportTy
                instantiationComplete.target }
          simp [inferExprFuel, entered, normalizedExecutable, instantiated,
            result, executableLookupEntered, selfLookup]
      | some placeholder =>
          let selfEvent := TraceEvent.directSelfReference name placeholder path
          let selfSource := ProducerSource.selfReference name placeholder path
          let selfEventExtension :=
            instantiationComplete.transition.after.recordEventExtension selfEvent
          let selfSourceExtension := stateBisimulationRecordSourceExtension
            selfEventExtension.after selfSource
          let referenced := recordSelfReference instantiated.2 name placeholder path
          let finishEvent := TraceEvent.inferredExpr (.var name)
            instantiated.1 path
          let finishExtension := selfSourceExtension.after.recordEventExtension
            finishEvent
          let result := finishExpr (.var name) path instantiated.1 referenced
          let finalRelation :=
            ((instantiatedRelation.recordEvent selfEvent
                (by simp [selfEvent, TraceEvent.allocatedCapVars])).recordSource
              selfSource).recordEvent finishEvent
                (by simp [finishEvent, TraceEvent.allocatedCapVars])
          refine
            { result := result
              success := ?_
              supply_eq := finalRelation.supply_eq
              ledger_eq := finalRelation.ledger_eq
              transition :=
                (((visitExtension.seq instantiationComplete.transition).seq
                    selfEventExtension).seq selfSourceExtension).seq
                  finishExtension
              declarative_bounded := finalRelation.declarative_bounded
              executable_bounded := finalRelation.executable_bounded
              forward_bounded := finalRelation.forward_bounded
              reverse_bounded := finalRelation.reverse_bounded
              ledger_below := finalRelation.ledger_below
              protected_origins := finalRelation.protected_origins
              protected_below := finalRelation.protected_below
              allocated_recorded := finalRelation.allocated_recorded
              target := finishExtension.transportTy
                (selfSourceExtension.transportTy
                  (selfEventExtension.transportTy
                    instantiationComplete.target)) }
          simp [inferExprFuel, entered, normalizedExecutable, instantiated,
            referenced, recordSelfReference, result, executableLookupEntered,
            selfLookup]

/-- `something` performs exactly one deterministic target allocation. -/
def inferExprFuel_something_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {path : SyntaxPath} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path .something
        initial) { q with nextTy := q.nextTy + 1 } declarative ledger
          (.matcher .any (.var q.nextTy)) := by
  let entered := visit initial .exprSomething path
  have enteredRelation := relation.visit .exprSomething path
  let allocated := entered.freshTy
    (freshOrigin .expression path "something-target")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "something-target")
  let result := finishExpr .something path (.matcher .any (.var q.nextTy))
    allocated.2
  let visitExtension := relation.visitExtension .exprSomething path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "something-target")
  let finishExtension := freshExtension.after.recordEventExtension
    (.inferredExpr .something (.matcher .any (.var q.nextTy)) path)
  let finalRelation := allocatedRelation.state.recordEvent
    (.inferredExpr .something (.matcher .any (.var q.nextTy)) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := allocatedRelation.state.supply_eq
      ledger_eq := allocatedRelation.state.ledger_eq
      transition :=
        bisimulationExtensionChain3 visitExtension freshExtension finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := by
        change relation.prevailing.forward.BoundedBy
          { q with nextTy := q.nextTy + 1 }
        exact relation.forward_bounded.mono (SupplyExtends.bumpTy q 1)
      reverse_bounded := by
        change relation.prevailing.reverse.BoundedBy
          { q with nextTy := q.nextTy + 1 }
        exact relation.reverse_bounded.mono (SupplyExtends.bumpTy q 1)
      ledger_below := finalRelation.ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by
      exact allocatedRelation.target_eq]
  exact finishExtension.after.sameTarget _

/-- Lambda synthesis is structural once the recursive body run has been
constructed from the deterministically allocated domain metavariable. -/
def inferExprFuel_lam_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {name : String} {body : Expr}
    {bodyTarget : Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (bodyComplete : SynthRunCompletion
      (relation.afterVisitFreshTy .exprLam path
        (freshOrigin .expression path "lambda-domain"))
      (inferExprFuel fuel signature
        ((name, Scheme.mono (.var q.nextTy)) :: context)
        (selfEnv.erase name) (0 :: path) body
        ((visit initial .exprLam path).freshTy
          (freshOrigin .expression path "lambda-domain")).2)
      q' S' ledger' bodyTarget) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.lam name body) initial) q' S' ledger'
        (.fn (.var q.nextTy) bodyTarget) := by
  let entered := visit initial .exprLam path
  have enteredRelation := relation.visit .exprLam path
  let allocated := entered.freshTy
    (freshOrigin .expression path "lambda-domain")
  have allocatedRelation := enteredRelation.freshTy
    (freshOrigin .expression path "lambda-domain")
  let bodyResult := bodyComplete.result
  let result := finishExpr (.lam name body) path
    (.fn (.var q.nextTy) bodyResult.target) bodyResult.state
  let visitExtension := relation.visitExtension .exprLam path
  let freshExtension := stateBisimulationFreshTyExtension visitExtension.after
    (freshOrigin .expression path "lambda-domain")
  let prefixExtension : BisimulationExtension relation.prevailing ledger S
      ((visit initial .exprLam path).freshTy
        (freshOrigin .expression path "lambda-domain")).2 :=
    { after := (relation.afterVisitFreshTy .exprLam path
          (freshOrigin .expression path "lambda-domain")).prevailing
      transportTy := by
        intro declarativeTarget executableTarget related
        have carried := freshExtension.transportTy
          (visitExtension.transportTy related)
        exact carried }
  let finishExtension := bodyComplete.transition.after.recordEventExtension
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyResult.target) path)
  let finalRelation := bodyComplete.completion.state.recordEvent
    (.inferredExpr (.lam name body)
      (.fn (.var q.nextTy) bodyResult.target) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := bodyComplete.supply_eq
      ledger_eq := bodyComplete.ledger_eq
      transition := prefixExtension.seq bodyComplete.transition |>.seq
        finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp only [inferExprFuel]
    rw [show allocated.1 = .var q.nextTy by exact allocatedRelation.target_eq]
    rw [bodyComplete.success]
  · have domainAtFinal : TyBisimulation
        bodyComplete.transition.after
        (.var q.nextTy) (.var q.nextTy) :=
      bodyComplete.transition.after.sameTarget _
    exact finishExtension.transportTy
      (tyBisimulation_fn domainAtFinal bodyComplete.target)

/-! ## List and tuple constructor slices

These lemmas expose the recursive hypotheses expected by the eventual mutual
induction.  Their fuel parameter is the predecessor passed uniformly to all
children by `inferExprFuel`.
-/

/-- The empty expression list succeeds without inspecting solver state. -/
def inferExprsFuel_nil_complete
    {signature : FrozenSig} {context : Context} {selfEnv : SelfEnv}
    {parent : SyntaxPath} {index : Nat} {q : InferenceBase.FreshSupply}
    {declarative : Subst} {ledger : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q declarative ledger initial)
    (fuel : Nat) :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index []
        initial) q declarative ledger [] := by
  refine
    { result := ⟨[], initial⟩
      success := ?_
      supply_eq := relation.supply_eq
      ledger_eq := relation.ledger_eq
      transition := .refl relation.prevailing
      declarative_bounded := relation.declarative_bounded
      executable_bounded := relation.executable_bounded
      forward_bounded := relation.forward_bounded
      reverse_bounded := relation.reverse_bounded
      ledger_below := relation.ledger_below
      protected_origins := relation.protected_origins
      protected_below := relation.protected_below
      allocated_recorded := relation.allocated_recorded
      targets := .nil }
  simp [inferExprsFuel]

/-- One expression-list cell composes the head and tail completion packages. -/
def inferExprsFuel_cons_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {parent : SyntaxPath} {index : Nat}
    {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (headComplete : SynthRunCompletion relation
      (inferExprFuel fuel signature context selfEnv (index :: parent)
        expression initial) q₁ S₁ ledger₁ target)
    (tailComplete : SynthsRunCompletion headComplete.completion.state
      (inferExprsFuel fuel signature context selfEnv parent (index + 1)
        expressions headComplete.result.state) q' S' ledger' targets)
    :
    SynthsRunCompletion relation
      (inferExprsFuel (fuel + 1) signature context selfEnv parent index
        (expression :: expressions) initial) q' S' ledger'
        (target :: targets) := by
  let head := headComplete.result
  let tail := tailComplete.result
  have headSuccess := headComplete.success
  have tailSuccess := tailComplete.success
  refine
    { result := ⟨head.target :: tail.targets, tail.state⟩
      success := ?_
      supply_eq := tailComplete.supply_eq
      ledger_eq := tailComplete.ledger_eq
      transition := headComplete.transition.seq tailComplete.transition
      declarative_bounded := tailComplete.declarative_bounded
      executable_bounded := tailComplete.executable_bounded
      forward_bounded := tailComplete.forward_bounded
      reverse_bounded := tailComplete.reverse_bounded
      ledger_below := tailComplete.ledger_below
      protected_origins := tailComplete.protected_origins
      protected_below := tailComplete.protected_below
      allocated_recorded := tailComplete.allocated_recorded
      targets := ?_ }
  · simp [inferExprsFuel, headSuccess, tailSuccess, head, tail]
  · exact .cons (tailComplete.transition.transportTy headComplete.target)
      tailComplete.targets

/-- Tuple synthesis is immediate once its list traversal completes. -/
def inferExprFuel_tuple_complete
    {fuel : Nat} {signature : FrozenSig} {context : Context}
    {selfEnv : SelfEnv} {path : SyntaxPath} {expressions : List Expr}
    {targets : List Ty} {q q' : InferenceBase.FreshSupply}
    {S S' : Subst} {ledger ledger' : CapabilityOriginLedger}
    {initial : InferState}
    (relation : TraversalStateCorrespondence q S ledger initial)
    (childrenComplete : SynthsRunCompletion
      (relation.afterVisit .exprTuple path)
      (inferExprsFuel fuel signature context selfEnv path 0 expressions
        (visit initial .exprTuple path)) q' S' ledger' targets) :
    SynthRunCompletion relation
      (inferExprFuel (fuel + 1) signature context selfEnv path
        (.tuple expressions) initial) q' S' ledger' (.prod targets) := by
  let children := childrenComplete.result
  have childrenSuccess := childrenComplete.success
  let result := finishExpr (.tuple expressions) path (.prod children.targets)
    children.state
  let visitExtension := relation.visitExtension .exprTuple path
  let finishExtension := childrenComplete.transition.after.recordEventExtension
    (.inferredExpr (.tuple expressions) (.prod children.targets) path)
  let finalRelation := childrenComplete.completion.state.recordEvent
    (.inferredExpr (.tuple expressions) (.prod children.targets) path)
    (by simp [TraceEvent.allocatedCapVars])
  refine
    { result := result
      success := ?_
      supply_eq := childrenComplete.supply_eq
      ledger_eq := childrenComplete.ledger_eq
      transition := bisimulationExtensionChain3 visitExtension
        childrenComplete.transition finishExtension
      declarative_bounded := finalRelation.declarative_bounded
      executable_bounded := finalRelation.executable_bounded
      forward_bounded := finalRelation.forward_bounded
      reverse_bounded := finalRelation.reverse_bounded
      ledger_below := finalRelation.ledger_below
      protected_origins := finalRelation.protected_origins
      protected_below := finalRelation.protected_below
      allocated_recorded := finalRelation.allocated_recorded
      target := ?_ }
  · simp [inferExprFuel, childrenSuccess, result, children]
  · exact finishExtension.transportTy
      (tyListBisimulation_prod childrenComplete.targets)

end DemandTypingInferenceCompletenessTraversal
end TypePM
