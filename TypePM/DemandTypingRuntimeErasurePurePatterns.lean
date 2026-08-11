import TypePM.DemandTypingErasureFactorization
import TypePM.SourceSubstitution

/-!
# Later-cut runtime erasure for pure pattern families

The four families in this module contain no expression leaves.  Their
strengthened erasure conclusions therefore quantify only an admissible
factored suffix: no context-flow or recursive expression-typing callback is
needed.  Constructor lemmas compose the already-proved state factorization
with that suffix, lift alignment equalities to the selected later cut, and
transport closed constructor instances there.
-/

namespace TypePM

private theorem liftTyEquality
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {ledger ledger' : CapabilityOriginLedger} {left right : Ty}
    (factorization : DDErasure.StateFactorization q S ledger q' S' ledger')
    (equality : S.apply left = S.apply right) :
    S'.apply left = S'.apply right := by
  rcases factorization with ⟨post, rfl, _admissible⟩
  simpa only [Subst.seq_apply] using congrArg post.apply equality

private theorem admissible_before_freezeExport
    {q final : InferenceBase.FreshSupply} {S post : Subst}
    {ledger finalLedger : CapabilityOriginLedger}
    {capImages : List CapVar} {payload : Ty}
    (admissible : DDErasure.AdmissiblePostBetween q final
      (DDLedger.freezeExport ledger S capImages payload) finalLedger post) :
    DDErasure.AdmissiblePostBetween q final ledger finalLedger post := by
  have freezing := DDErasure.AdmissiblePostBetween.ofTransition
    (SupplyExtends.refl q)
    (DDLedger.RefinesBelow.freezeExport q ledger S capImages payload)
  simpa only [Subst.seq_id_right] using freezing.seq admissible

private theorem closedDataCtorInstance
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String} {scheme : CtorScheme}
    (lookup : signature.findDataCtor name = some scheme)
    (q : InferenceBase.FreshSupply) (post : Subst) :
    scheme.Inst
      ((InferenceBase.instantiateCtorScheme q scheme).value.1.map post.apply)
      (post.apply
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

private theorem closedPatternCtorInstance
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {name : String}
    {entry : PatternCtorScheme signature.observability}
    (lookup : signature.findPatternCtor name = some entry)
    (q : InferenceBase.FreshSupply) (post : Subst) :
    entry.Inst
      ((InferenceBase.instantiateCtorScheme q entry.scheme).value.1.map
        post.apply)
      (post.apply
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

namespace DDDPatOrigin

/-- Data-pattern erasure stable under every later admissible suffix. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    DPatTy signature pattern (finalSubst.apply expected)
      (bindings.applySubst finalSubst)

/-- The later-cut invariant specializes to the derivation's own terminal
cut via reflexive factorization. -/
theorem runtimeErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDDPatOrigin signature raw ledger ledger'}
    (under : RuntimeErasureUnder origin) :
    DPatTy signature pattern (S'.apply expected)
      (bindings.applySubst S') := by
  rcases DDErasure.StateFactorization.refl q' S' ledger' with
    ⟨post, equation, admissible⟩
  exact under equation admissible

theorem runtimeErasureUnder_var
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDDPatOrigin.var (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact DPatTy.var

theorem runtimeErasureUnder_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDDPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact DPatTy.wild

end DDDPatOrigin

namespace DDDPatsOrigin

/-- Data-pattern-list erasure stable under every later admissible suffix. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDDPatsOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    DPatTys signature patterns (targets.map finalSubst.apply)
      (bindings.applySubst finalSubst)

theorem runtimeErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDDPatsOrigin signature raw ledger ledger'}
    (under : RuntimeErasureUnder origin) :
    DPatTys signature patterns (targets.map S'.apply)
      (bindings.applySubst S') := by
  rcases DDErasure.StateFactorization.refl q' S' ledger' with
    ⟨post, equation, admissible⟩
  exact under equation admissible

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDDPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact DPatTys.nil

end DDDPatsOrigin

namespace DDDPatOrigin

set_option maxHeartbeats 300000 in
/-- Recursive constructor closure.  The child factorization supplies both
the terminal alignment equality and the pre-freeze suffix required by the
strengthened child invariant. -/
theorem runtimeErasureUnder_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List DPat} {expected : Ty}
    {scheme : CtorScheme} {S₁ : Subst} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findDataCtor name = some scheme)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q scheme) S
      (InferenceBase.instantiateCtorScheme q scheme).value.2 expected S₁)
    {children : DDDPats signature
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q scheme) ledger₂)
    (childrenUnder : DDDPatsOrigin.RuntimeErasureUnder childrenOrigin)
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q scheme).supply S₁
      (DDLedger.markCtorInstance ledger q scheme) q' S' ledger₂)
    (closed : signature.SchemesClosed) :
    RuntimeErasureUnder
      (DDDPatOrigin.ctor lookup aligned childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have childAdmissible : DDErasure.AdmissiblePostBetween q' final ledger₂
      finalLedger post := by
    exact admissible_before_freezeExport admissible
  have childrenAtFinal := childrenUnder terminalEquation childAdmissible
  have laterFactor : DDErasure.StateFactorization q' S'
      (DDLedger.freezeExport ledger₂ S'
        (Inference.freshCapImages q scheme.capBinders)
        (Inference.capabilityExportPayload []
          (expected :: bindings.map fun entry => entry.2)))
      final finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  have freezing : DDErasure.StateFactorization q' S' ledger₂ q' S'
      (DDLedger.freezeExport ledger₂ S'
        (Inference.freshCapImages q scheme.capBinders)
        (Inference.capabilityExportPayload []
          (expected :: bindings.map fun entry => entry.2))) :=
    DDErasure.StateFactorization.ofTransition (S := S')
      (SupplyExtends.refl q')
      (DDLedger.RefinesBelow.freezeExport q' ledger₂ S'
        (Inference.freshCapImages q scheme.capBinders)
        (Inference.capabilityExportPayload []
          (expected :: bindings.map fun entry => entry.2)))
  have resultEquality := liftTyEquality
    ((childrenFactorization.trans freezing).trans laterFactor)
    aligned.output_equal
  change DPatTy signature (.ctor name patterns) (finalSubst.apply expected)
    (bindings.applySubst finalSubst)
  rw [← resultEquality]
  exact DPatTy.ctor lookup childrenAtFinal
    (closedDataCtorInstance closed lookup q finalSubst)

theorem runtimeErasureUnder_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {expected : Ty} {S₁ : Subst}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDDPats signature
      (freshTargetsSupply patterns.length q).2 S₁ patterns
      (freshTargetsSupply patterns.length q).1 bindings q' S'}
    (childrenOrigin : DDDPatsOrigin signature children ledger ledger')
    (childrenUnder : DDDPatsOrigin.RuntimeErasureUnder childrenOrigin)
    (childrenFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S₁ ledger q' S' ledger') :
    RuntimeErasureUnder (DDDPatOrigin.tuple aligned childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have childrenAtFinal := childrenUnder terminalEquation admissible
  have laterFactor : DDErasure.StateFactorization q' S' ledger' final
      finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  have resultEquality := liftTyEquality
    (childrenFactorization.trans laterFactor) aligned.output_equal
  change DPatTy signature (.tuple patterns) (finalSubst.apply expected)
    (bindings.applySubst finalSubst)
  rw [← resultEquality]
  simpa only [Subst.apply_prod] using DPatTy.tuple childrenAtFinal

end DDDPatOrigin

namespace DDDPatsOrigin

theorem runtimeErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {patterns : List DPat} {target : Ty}
    {targets : List Ty} {bindings restBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDDPat signature q S pattern target bindings q₁ S₁}
    {tail : DDDPats signature q₁ S₁ patterns targets restBindings q' S'}
    (headOrigin : DDDPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDDPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headUnder : DDDPatOrigin.RuntimeErasureUnder headOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (tailFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q' S' ledger') :
    RuntimeErasureUnder
      (DDDPatsOrigin.cons headOrigin tailOrigin disjoint) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  rcases tailFactorization with ⟨tailPost, tailEquation, tailAdmissible⟩
  have combinedAdmissible := tailAdmissible.seq admissible
  have combinedEquation :
      finalSubst = Subst.seq (Subst.seq post tailPost) S₁ := by
    rw [terminalEquation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S₁
  have headAtFinal := headUnder combinedEquation combinedAdmissible
  have tailAtFinal := tailUnder terminalEquation admissible
  have movedDistinct : ∀ name,
      name ∈ (bindings.applySubst finalSubst).names →
      name ∉ (restBindings.applySubst finalSubst).names := by
    simpa only [MonoCtx.names_applySubst] using disjoint
  change DPatTys signature (pattern :: patterns)
    ((target :: targets).map finalSubst.apply)
    ((bindings ++ restBindings).applySubst finalSubst)
  simpa only [List.map_cons, MonoCtx.applySubst, List.map_append] using
    DPatTys.cons headAtFinal tailAtFinal movedDistinct

end DDDPatsOrigin

namespace DDPPatOrigin

/-- Primitive-pattern erasure stable under every later admissible suffix. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    TerminalPPatResolution signature finalSubst pattern
      (finalSubst.apply expected)
      (holes.map (Dual.applySubst finalSubst))
      (bindings.applySubst finalSubst)

theorem runtimeErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDPPatOrigin signature raw ledger ledger'}
    (under : RuntimeErasureUnder origin) :
    TerminalPPatResolution signature S' pattern (S'.apply expected)
      (holes.map (Dual.applySubst S')) (bindings.applySubst S') := by
  rcases DDErasure.StateFactorization.refl q' S' ledger' with
    ⟨post, equation, admissible⟩
  exact under equation admissible

theorem runtimeErasureUnder_hole
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {expected : Ty} {ledger : CapabilityOriginLedger}
    (fresh : signature.FreshCapFor ⟨q.nextCap⟩ expected) :
    RuntimeErasureUnder
      (DDPPatOrigin.hole (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact TerminalPPatResolution.hole fresh

theorem runtimeErasureUnder_wild
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDPPatOrigin.wild (signature := signature) (q := q) (S := S)
        (expectedTarget := expected) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact TerminalPPatResolution.wild

theorem runtimeErasureUnder_pval
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (name : String) (expected : Ty) (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDPPatOrigin.pval (signature := signature) (q := q) (S := S)
        (name := name) (expectedTarget := expected) (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact TerminalPPatResolution.pval

end DDPPatOrigin

namespace DDPPatsOrigin

/-- Primitive-pattern-list erasure stable under later admissible suffixes. -/
def RuntimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_origin : DDPPatsOrigin signature raw ledger ledger') : Prop :=
  ∀ {final : InferenceBase.FreshSupply} {finalSubst post : Subst}
      {finalLedger : CapabilityOriginLedger},
    finalSubst = Subst.seq post S' →
    DDErasure.AdmissiblePostBetween q' final ledger' finalLedger post →
    TerminalPPatResolutions signature finalSubst patterns
      (targets.map finalSubst.apply)
      (holes.map (Dual.applySubst finalSubst))
      (bindings.applySubst finalSubst)

theorem runtimeErasure_of_under
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    {origin : DDPPatsOrigin signature raw ledger ledger'}
    (under : RuntimeErasureUnder origin) :
    TerminalPPatResolutions signature S' patterns (targets.map S'.apply)
      (holes.map (Dual.applySubst S')) (bindings.applySubst S') := by
  rcases DDErasure.StateFactorization.refl q' S' ledger' with
    ⟨post, equation, admissible⟩
  exact under equation admissible

theorem runtimeErasureUnder_nil
    (signature : FrozenSig) (q : InferenceBase.FreshSupply) (S : Subst)
    (ledger : CapabilityOriginLedger) :
    RuntimeErasureUnder
      (DDPPatsOrigin.nil (signature := signature) (q := q) (S := S)
        (ledger := ledger)) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  exact TerminalPPatResolutions.nil

end DDPPatsOrigin

namespace DDPPatOrigin

theorem runtimeErasureUnder_ctor_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {name : String} {patterns : List PPat} {expected : Ty}
    {entry : PatternCtorScheme signature.observability} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₂ : CapabilityOriginLedger}
    (lookup : signature.findPatternCtor name = some entry)
    (aligned : DDAlignTypesWithLedger
      (DDLedger.markCtorInstance ledger q entry.scheme) S
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.2 expected S₁)
    {children : DDPPats signature
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁ patterns
      (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 holes bindings
      q' S'}
    (childrenOrigin : DDPPatsOrigin signature children
      (DDLedger.markCtorInstance ledger q entry.scheme) ledger₂)
    (childrenUnder : DDPPatsOrigin.RuntimeErasureUnder childrenOrigin)
    (childrenFactorization : DDErasure.StateFactorization
      (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
      (DDLedger.markCtorInstance ledger q entry.scheme) q' S' ledger₂)
    (closed : signature.SchemesClosed) :
    RuntimeErasureUnder
      (DDPPatOrigin.ctor lookup aligned childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have childAdmissible : DDErasure.AdmissiblePostBetween q' final ledger₂
      finalLedger post := admissible_before_freezeExport admissible
  have childrenAtFinal := childrenUnder terminalEquation childAdmissible
  have laterFactor : DDErasure.StateFactorization q' S'
      (DDLedger.freezeExport ledger₂ S'
        (Inference.freshCapImages q entry.scheme.capBinders)
        (Inference.capabilityExportPayload (holes.map Dual.cap)
          (holes.map Dual.target ++ expected ::
            bindings.map fun binding => binding.2)))
      final finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  have freezing : DDErasure.StateFactorization q' S' ledger₂ q' S'
      (DDLedger.freezeExport ledger₂ S'
        (Inference.freshCapImages q entry.scheme.capBinders)
        (Inference.capabilityExportPayload (holes.map Dual.cap)
          (holes.map Dual.target ++ expected ::
            bindings.map fun binding => binding.2))) :=
    DDErasure.StateFactorization.ofTransition (S := S')
      (SupplyExtends.refl q')
      (DDLedger.RefinesBelow.freezeExport q' ledger₂ S'
        (Inference.freshCapImages q entry.scheme.capBinders)
        (Inference.capabilityExportPayload (holes.map Dual.cap)
          (holes.map Dual.target ++ expected ::
            bindings.map fun binding => binding.2)))
  have resultEquality := liftTyEquality
    ((childrenFactorization.trans freezing).trans laterFactor)
    aligned.output_equal
  change TerminalPPatResolution signature finalSubst (.ctor name patterns)
    (finalSubst.apply expected) (holes.map (Dual.applySubst finalSubst))
    (bindings.applySubst finalSubst)
  rw [← resultEquality]
  exact TerminalPPatResolution.ctor lookup childrenAtFinal
    (closedPatternCtorInstance closed lookup q finalSubst)

theorem runtimeErasureUnder_tuple_of_children
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {expected : Ty} {S₁ : Subst}
    {holes : List Dual} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger' : CapabilityOriginLedger}
    (aligned : DDAlignTypesWithLedger ledger S
      (.prod (freshTargetsSupply patterns.length q).1) expected S₁)
    {children : DDPPats signature
      (freshTargetsSupply patterns.length q).2 S₁ patterns
      (freshTargetsSupply patterns.length q).1 holes bindings q' S'}
    (childrenOrigin : DDPPatsOrigin signature children ledger ledger')
    (childrenUnder : DDPPatsOrigin.RuntimeErasureUnder childrenOrigin)
    (childrenFactorization : DDErasure.StateFactorization
      (freshTargetsSupply patterns.length q).2 S₁ ledger q' S' ledger') :
    RuntimeErasureUnder (DDPPatOrigin.tuple aligned childrenOrigin) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  have childrenAtFinal := childrenUnder terminalEquation admissible
  have laterFactor : DDErasure.StateFactorization q' S' ledger' final
      finalSubst finalLedger := ⟨post, terminalEquation, admissible⟩
  have resultEquality := liftTyEquality
    (childrenFactorization.trans laterFactor) aligned.output_equal
  change TerminalPPatResolution signature finalSubst (.tuple patterns)
    (finalSubst.apply expected) (holes.map (Dual.applySubst finalSubst))
    (bindings.applySubst finalSubst)
  rw [← resultEquality]
  simpa only [Subst.apply_prod] using
    TerminalPPatResolution.tuple childrenAtFinal

end DDPPatOrigin

namespace DDPPatsOrigin

theorem runtimeErasureUnder_cons
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {patterns : List PPat} {target : Ty}
    {targets : List Ty} {holes restHoles : List Dual}
    {bindings restBindings : MonoCtx}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {head : DDPPat signature q S pattern target holes bindings q₁ S₁}
    {tail : DDPPats signature q₁ S₁ patterns targets restHoles
      restBindings q' S'}
    (headOrigin : DDPPatOrigin signature head ledger ledger₁)
    (tailOrigin : DDPPatsOrigin signature tail ledger₁ ledger')
    (disjoint : ∀ name, name ∈ bindings.names →
      name ∉ restBindings.names)
    (headUnder : DDPPatOrigin.RuntimeErasureUnder headOrigin)
    (tailUnder : RuntimeErasureUnder tailOrigin)
    (tailFactorization : DDErasure.StateFactorization q₁ S₁ ledger₁
      q' S' ledger') :
    RuntimeErasureUnder
      (DDPPatsOrigin.cons headOrigin tailOrigin disjoint) := by
  intro final finalSubst post finalLedger terminalEquation admissible
  rcases tailFactorization with ⟨tailPost, tailEquation, tailAdmissible⟩
  have combinedAdmissible := tailAdmissible.seq admissible
  have combinedEquation :
      finalSubst = Subst.seq (Subst.seq post tailPost) S₁ := by
    rw [terminalEquation, tailEquation]
    exact PhasedPost.seq_assoc post tailPost S₁
  have headAtFinal := headUnder combinedEquation combinedAdmissible
  have tailAtFinal := tailUnder terminalEquation admissible
  have movedDistinct : ∀ name,
      name ∈ (bindings.applySubst finalSubst).names →
      name ∉ (restBindings.applySubst finalSubst).names := by
    simpa only [MonoCtx.names_applySubst] using disjoint
  change TerminalPPatResolutions signature finalSubst (pattern :: patterns)
    ((target :: targets).map finalSubst.apply)
    ((holes ++ restHoles).map (Dual.applySubst finalSubst))
    ((bindings ++ restBindings).applySubst finalSubst)
  simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
    TerminalPPatResolutions.cons headAtFinal tailAtFinal movedDistinct

end DDPPatsOrigin

/-! ## Premise-free mutual closure -/

mutual

theorem DDDPatOrigin.runtimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expected : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expected bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    DDDPatOrigin.RuntimeErasureUnder origin :=
  match origin with
  | .var => DDDPatOrigin.runtimeErasureUnder_var _ _ _ _ _ _
  | .wild => DDDPatOrigin.runtimeErasureUnder_wild _ _ _ _ _
  | @DDDPatOrigin.ctor _ q S name _ expected scheme S₁ _ _ _ ledger _
      lookup aligned _ childrenOrigin => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.dataCtors lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q scheme
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) instB.2
        (expectedBounded.mono ext)
      exact DDDPatOrigin.runtimeErasureUnder_ctor_of_children lookup aligned
        childrenOrigin
        (DDDPatsOrigin.runtimeErasureUnder childrenOrigin closed S₁b instB.1)
        (DDDPatsOrigin.factorize childrenOrigin closed S₁b instB.1) closed
  | @DDDPatOrigin.tuple _ q S patterns expected S₁ _ _ _ ledger _ aligned _
      childrenOrigin => by
      have targetsB := freshTargetsSupply_boundedBy patterns.length q
      have ext := SupplyExtends.freshTargets patterns.length q
      have productB := Ty.BoundedBy.prodOfForall targetsB
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) productB
        (expectedBounded.mono ext)
      exact DDDPatOrigin.runtimeErasureUnder_tuple_of_children aligned
        childrenOrigin
        (DDDPatsOrigin.runtimeErasureUnder childrenOrigin closed S₁b targetsB)
        (DDDPatsOrigin.factorize childrenOrigin closed S₁b targetsB)

theorem DDDPatsOrigin.runtimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDDPatsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q) :
    DDDPatsOrigin.RuntimeErasureUnder origin :=
  match origin with
  | .nil => DDDPatsOrigin.runtimeErasureUnder_nil _ _ _ _
  | @DDDPatsOrigin.cons _ _ _ _ _ target tailTargets _ _ qNext _ _ _ _ _ _ _ _
      headOrigin tailOrigin disjoint => by
      have headB : target.BoundedBy q := targetsBounded target (by simp)
      obtain ⟨S₁b, _⟩ := headOrigin.erase.boundedBy closed Sb headB
      have tailB : ∀ item ∈ tailTargets,
          item.BoundedBy qNext := by
        intro item mem
        exact (targetsBounded item (by simp [mem])).mono
          headOrigin.erase.supplyExtends
      exact DDDPatsOrigin.runtimeErasureUnder_cons headOrigin tailOrigin disjoint
        (DDDPatOrigin.runtimeErasureUnder headOrigin closed Sb headB)
        (DDDPatsOrigin.runtimeErasureUnder tailOrigin closed S₁b tailB)
        (DDDPatsOrigin.factorize tailOrigin closed S₁b tailB)

end

mutual

theorem DDPPatOrigin.runtimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expected : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expected holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (expectedBounded : expected.BoundedBy q) :
    DDPPatOrigin.RuntimeErasureUnder origin :=
  match origin with
  | .hole => DDPPatOrigin.runtimeErasureUnder_hole
      (closed.freshCapForNext expectedBounded)
  | .wild => DDPPatOrigin.runtimeErasureUnder_wild _ _ _ _ _
  | .pval => DDPPatOrigin.runtimeErasureUnder_pval _ _ _ _ _ _
  | @DDPPatOrigin.ctor _ q S name _ expected entry S₁ _ _ _ _ ledger _
      lookup aligned _ childrenOrigin => by
      have instB := instantiateCtorScheme_boundedBy (q := q)
        ((closed.patternCtors lookup).boundedBy)
      have ext := SupplyExtends.instantiateCtorScheme q entry.scheme
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) instB.2
        (expectedBounded.mono ext)
      exact DDPPatOrigin.runtimeErasureUnder_ctor_of_children lookup aligned
        childrenOrigin
        (DDPPatsOrigin.runtimeErasureUnder childrenOrigin closed S₁b instB.1)
        (DDPPatsOrigin.factorize childrenOrigin closed S₁b instB.1) closed
  | @DDPPatOrigin.tuple _ q S patterns expected _ _ _ _ _ ledger _
      aligned _ childrenOrigin => by
      have targetsB := freshTargetsSupply_boundedBy patterns.length q
      have ext := SupplyExtends.freshTargets patterns.length q
      have productB := Ty.BoundedBy.prodOfForall targetsB
      have S₁b := aligned.erase.boundedBy (Sb.mono ext) productB
        (expectedBounded.mono ext)
      exact DDPPatOrigin.runtimeErasureUnder_tuple_of_children aligned
        childrenOrigin
        (DDPPatsOrigin.runtimeErasureUnder childrenOrigin closed S₁b targetsB)
        (DDPPatsOrigin.factorize childrenOrigin closed S₁b targetsB)

theorem DDPPatsOrigin.runtimeErasureUnder
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (origin : DDPPatsOrigin signature raw ledger ledger')
    (closed : signature.SchemesClosed) (Sb : S.BoundedBy q)
    (targetsBounded : ∀ target ∈ targets, target.BoundedBy q) :
    DDPPatsOrigin.RuntimeErasureUnder origin :=
  match origin with
  | .nil => DDPPatsOrigin.runtimeErasureUnder_nil _ _ _ _
  | @DDPPatsOrigin.cons _ _ _ _ _ target tailTargets _ _ _ _ qNext _ _ _ _ _ _ _ _
      headOrigin tailOrigin disjoint => by
      have headB : target.BoundedBy q := targetsBounded target (by simp)
      obtain ⟨S₁b, _, _⟩ := headOrigin.erase.boundedBy closed Sb headB
      have tailB : ∀ item ∈ tailTargets, item.BoundedBy qNext := by
        intro item mem
        exact (targetsBounded item (by simp [mem])).mono
          headOrigin.erase.supplyExtends
      exact DDPPatsOrigin.runtimeErasureUnder_cons headOrigin tailOrigin disjoint
        (DDPPatOrigin.runtimeErasureUnder headOrigin closed Sb headB)
        (DDPPatsOrigin.runtimeErasureUnder tailOrigin closed S₁b tailB)
        (DDPPatsOrigin.factorize tailOrigin closed S₁b tailB)

end

end TypePM
