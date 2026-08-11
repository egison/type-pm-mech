import TypePM.DemandTyping

/-!
# Intrinsic capability-origin certificates for demand-directed typing

The raw demand-directed families record fresh supplies and prevailing
substitutions.  This module adds a second, intrinsic layer indexed by those
raw derivations.  Its constructors mirror the raw constructors one for one,
while threading the capability-origin ledger chronologically.  Consequently
there is no premise permitting an arbitrary ledger transition: every output
ledger is fixed by fresh allocation, constructor instantiation, export
freezing, or the recursively certified child traversal.

The certificates cover every expression, user-pattern, clause, and primitive
pattern family.  Pattern-constructor capability projection is indexed
separately because its fallback branch contains an internal allocation and
solve sequence.
-/

namespace TypePM

/-! ## Pattern-constructor capability projection -/

/-- Origin provenance for one existing `DDPatternCtorCap` derivation.

The exact-projection path only allocates the fresh variables introduced while
freshening its result skeleton.  The fallback path first exposes the shared
result-assignment range, performs its capability solves at that ledger cut,
and only then exposes variables allocated by the final skeleton. -/
inductive DDPatternCtorCapOrigin (signature : FrozenSig)
    (entry : PatternCtorScheme signature.observability) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} ->
    {childCaps : List Cap} -> {capability : Cap} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDPatternCtorCap signature entry q S childCaps capability q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | project
      {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
      {projected : Shape.Evidence} {capability : Cap}
      {q' : InferenceBase.FreshSupply}
      {ledger : CapabilityOriginLedger}
      (projection :
        Projection.projectSignature entry.projection
          ((childCaps.map fun child => child.apply S.cap).map Shape.ofCap) =
            some projected)
      (freshened :
        freshenSkeletonSupply signature.observability projected q =
          some (capability, q')) :
      DDPatternCtorCapOrigin signature entry
        (.project projection freshened) ledger
        (DDLedger.markCapRange ledger q q')
  | fallback
      {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
      {resultVariables : List TypePM.TyVar} {demands : List (Option Cap)}
      {S₁ : Subst} {projected : Shape.Evidence} {capability : Cap}
      {q' : InferenceBase.FreshSupply}
      {ledger : CapabilityOriginLedger}
      (projectionMiss :
        Projection.projectSignature entry.projection
          ((childCaps.map fun child => child.apply S.cap).map Shape.ofCap) =
            none)
      (resultVars :
        Projection.relevantVars signature.observability
          (Projection.targetVars entry.projection.resultType)
          entry.projection.resultType = some resultVariables)
      (fieldDemands :
        Inference.patternCtorFieldDemands signature.observability
          resultVariables.eraseDups
          (patternCtorAssignmentsSupply resultVariables.eraseDups q).1
          entry.projection.fieldTypes = some demands)
      (aligned : DDAlignCtorCapsWithLedger
        (DDLedger.markCapRange ledger q
          (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
        S childCaps demands S₁)
      (projectionHit :
        Projection.projectSignature entry.projection
          ((childCaps.map fun child => child.apply S₁.cap).map Shape.ofCap) =
            some projected)
      (freshened :
        freshenSkeletonSupply signature.observability projected
          (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 =
            some (capability, q')) :
      DDPatternCtorCapOrigin signature entry
        (.fallback projectionMiss resultVars fieldDemands aligned.erase
          projectionHit freshened)
        ledger
        (DDLedger.markCapRange
          (DDLedger.markCapRange ledger q
            (patternCtorAssignmentsSupply resultVariables.eraseDups q).2)
          (patternCtorAssignmentsSupply resultVariables.eraseDups q).2 q')

/-- The indexed raw pattern-constructor derivation is the erasure of its
origin certificate. -/
def DDPatternCtorCapOrigin.erase
    {signature : FrozenSig}
    {entry : PatternCtorScheme signature.observability}
    {q : InferenceBase.FreshSupply} {S : Subst} {childCaps : List Cap}
    {capability : Cap} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatternCtorCap signature entry q S childCaps capability q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDPatternCtorCapOrigin signature entry raw ledger ledger') :
    DDPatternCtorCap signature entry q S childCaps capability q' S' :=
  raw

/-! ## Primitive data patterns -/

mutual

/-- Origin provenance for an existing primitive data-pattern derivation. -/
inductive DDDPatOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {pattern : DPat} ->
    {expectedTarget : Ty} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDDPat signature q S pattern expectedTarget bindings q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | var
      {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {expectedTarget : Ty} {ledger : CapabilityOriginLedger} :
      DDDPatOrigin signature (.var (q := q) (S := S) (name := name)
        (expectedTarget := expectedTarget)) ledger ledger
  | wild
      {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDDPatOrigin signature (.wild (q := q) (S := S)
        (expectedTarget := expectedTarget)) ledger ledger
  | ctor
      {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {patterns : List DPat} {expectedTarget : Ty} {scheme : CtorScheme}
      {S₁ : Subst} {bindings : MonoCtx} {q' : InferenceBase.FreshSupply}
      {S' : Subst} {ledger ledger₂ : CapabilityOriginLedger}
      (lookup : signature.findDataCtor name = some scheme)
      (aligned : DDAlignTypesWithLedger
        (DDLedger.markCtorInstance ledger q scheme) S
        (InferenceBase.instantiateCtorScheme q scheme).value.2
        expectedTarget S₁)
      {children : DDDPats signature
        (InferenceBase.instantiateCtorScheme q scheme).supply S₁ patterns
        (InferenceBase.instantiateCtorScheme q scheme).value.1 bindings q' S'}
      (childrenOrigin : DDDPatsOrigin signature children
        (DDLedger.markCtorInstance ledger q scheme) ledger₂) :
      DDDPatOrigin signature
        (.ctor lookup aligned.erase children) ledger
        (DDLedger.freezeExport ledger₂ S'
          (Inference.freshCapImages q scheme.capBinders)
          (Inference.capabilityExportPayload []
            (expectedTarget :: bindings.map fun entry => entry.2)))
  | tuple
      {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List DPat}
      {expectedTarget : Ty} {S₁ : Subst} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger' : CapabilityOriginLedger}
      (aligned : DDAlignTypesWithLedger ledger S
        (.prod (freshTargetsSupply patterns.length q).1) expectedTarget S₁)
      {children : DDDPats signature
        (freshTargetsSupply patterns.length q).2 S₁ patterns
        (freshTargetsSupply patterns.length q).1 bindings q' S'}
      (childrenOrigin : DDDPatsOrigin signature children ledger ledger') :
      DDDPatOrigin signature (.tuple aligned.erase children) ledger ledger'

/-- Origin provenance for an existing primitive data-pattern list
derivation. -/
inductive DDDPatsOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} ->
    {patterns : List DPat} -> {targets : List Ty} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDDPats signature q S patterns targets bindings q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst}
      {ledger : CapabilityOriginLedger} :
      DDDPatsOrigin signature (.nil (q := q) (S := S)) ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {pattern : DPat}
      {patterns : List DPat} {target : Ty} {targets : List Ty}
      {bindings restBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply}
      {S₁ : Subst} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDDPat signature q S pattern target bindings q₁ S₁}
      {tail : DDDPats signature q₁ S₁ patterns targets restBindings q' S'}
      (headOrigin : DDDPatOrigin signature head ledger ledger₁)
      (tailOrigin : DDDPatsOrigin signature tail ledger₁ ledger')
      (disjoint :
        ∀ name, name ∈ bindings.names -> name ∉ restBindings.names) :
      DDDPatsOrigin signature (.cons head tail disjoint) ledger ledger'

end

/-- Erase a primitive data-pattern origin certificate. -/
def DDDPatOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : DPat} {expectedTarget : Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPat signature q S pattern expectedTarget bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDDPatOrigin signature raw ledger ledger') :
    DDDPat signature q S pattern expectedTarget bindings q' S' :=
  raw

/-- Erase a primitive data-pattern list origin certificate. -/
def DDDPatsOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List DPat} {targets : List Ty} {bindings : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDDPats signature q S patterns targets bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDDPatsOrigin signature raw ledger ledger') :
    DDDPats signature q S patterns targets bindings q' S' :=
  raw

/-! ## Primitive-pattern patterns -/

mutual

/-- Origin provenance for an existing primitive-pattern derivation. -/
inductive DDPPatOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {pattern : PPat} ->
    {expectedTarget : Ty} -> {holes : List Dual} -> {bindings : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDPPat signature q S pattern expectedTarget holes bindings q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | hole
      {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDPPatOrigin signature (.hole (q := q) (S := S)
        (expectedTarget := expectedTarget)) ledger
        (DDLedger.markFreshCap ledger q)
  | wild
      {q : InferenceBase.FreshSupply} {S : Subst} {expectedTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDPPatOrigin signature (.wild (q := q) (S := S)
        (expectedTarget := expectedTarget)) ledger ledger
  | pval
      {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {expectedTarget : Ty} {ledger : CapabilityOriginLedger} :
      DDPPatOrigin signature (.pval (q := q) (S := S) (name := name)
        (expectedTarget := expectedTarget)) ledger ledger
  | ctor
      {q : InferenceBase.FreshSupply} {S : Subst} {name : String}
      {patterns : List PPat} {expectedTarget : Ty}
      {entry : PatternCtorScheme signature.observability} {S₁ : Subst}
      {holes : List Dual} {bindings : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₂ : CapabilityOriginLedger}
      (lookup : signature.findPatternCtor name = some entry)
      (aligned : DDAlignTypesWithLedger
        (DDLedger.markCtorInstance ledger q entry.scheme) S
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.2
        expectedTarget S₁)
      {children : DDPPats signature
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply S₁
        patterns (InferenceBase.instantiateCtorScheme q entry.scheme).value.1
        holes bindings q' S'}
      (childrenOrigin : DDPPatsOrigin signature children
        (DDLedger.markCtorInstance ledger q entry.scheme) ledger₂) :
      DDPPatOrigin signature
        (.ctor lookup aligned.erase children) ledger
        (DDLedger.freezeExport ledger₂ S'
          (Inference.freshCapImages q entry.scheme.capBinders)
          (Inference.capabilityExportPayload (holes.map Dual.cap)
            (holes.map Dual.target ++ expectedTarget ::
              bindings.map fun binding => binding.2)))
  | tuple
      {q : InferenceBase.FreshSupply} {S : Subst} {patterns : List PPat}
      {expectedTarget : Ty} {S₁ : Subst} {holes : List Dual}
      {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger' : CapabilityOriginLedger}
      (aligned : DDAlignTypesWithLedger ledger S
        (.prod (freshTargetsSupply patterns.length q).1) expectedTarget S₁)
      {children : DDPPats signature
        (freshTargetsSupply patterns.length q).2 S₁ patterns
        (freshTargetsSupply patterns.length q).1 holes bindings q' S'}
      (childrenOrigin : DDPPatsOrigin signature children ledger ledger') :
      DDPPatOrigin signature (.tuple aligned.erase children) ledger ledger'

/-- Origin provenance for an existing primitive-pattern list derivation. -/
inductive DDPPatsOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} ->
    {patterns : List PPat} -> {targets : List Ty} -> {holes : List Dual} ->
    {bindings : MonoCtx} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    DDPPats signature q S patterns targets holes bindings q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst}
      {ledger : CapabilityOriginLedger} :
      DDPPatsOrigin signature (.nil (q := q) (S := S)) ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {pattern : PPat}
      {patterns : List PPat} {target : Ty} {targets : List Ty}
      {holes restHoles : List Dual} {bindings restBindings : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDPPat signature q S pattern target holes bindings q₁ S₁}
      {tail : DDPPats signature q₁ S₁ patterns targets restHoles
        restBindings q' S'}
      (headOrigin : DDPPatOrigin signature head ledger ledger₁)
      (tailOrigin : DDPPatsOrigin signature tail ledger₁ ledger')
      (disjoint :
        ∀ name, name ∈ bindings.names -> name ∉ restBindings.names) :
      DDPPatsOrigin signature (.cons head tail disjoint) ledger ledger'

end

/-- Erase a primitive-pattern origin certificate. -/
def DDPPatOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {pattern : PPat} {expectedTarget : Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPat signature q S pattern expectedTarget holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDPPatOrigin signature raw ledger ledger') :
    DDPPat signature q S pattern expectedTarget holes bindings q' S' :=
  raw

/-- Erase a primitive-pattern list origin certificate. -/
def DDPPatsOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {patterns : List PPat} {targets : List Ty} {holes : List Dual}
    {bindings : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPPats signature q S patterns targets holes bindings q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDPPatsOrigin signature raw ledger ledger') :
    DDPPats signature q S patterns targets holes bindings q' S' :=
  raw

/-! ## Expression, user-pattern, arm, and clause families -/

mutual

/-- Origin provenance for an existing expression-synthesis derivation. -/
inductive DDSynthOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {expression : Expr} -> {target : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDSynth signature q S context expression target q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | var
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {name : String} {scheme : NamedScheme} {ledger : CapabilityOriginLedger}
      (lookup : (context.applySubst S).find? name = some scheme) :
      DDSynthOrigin signature (.var (q := q) lookup) ledger
        (DDLedger.markSchemeInstance ledger q scheme)
  | lam
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {name : String} {body : Expr} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger' : CapabilityOriginLedger}
      {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 1 } S
        ((name, NamedScheme.mono (.var q.nextTy)) :: context) body bodyTarget q' S'}
      (bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger') :
      DDSynthOrigin signature (.lam bodyRaw) ledger ledger'
  | fix
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {self argument : String} {body : Expr} {bodyTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      (distinct : self ≠ argument)
      (direct : DirectSelf.Holds self body)
      (nonMatcher : NonMatcherBody body)
      {bodyRaw : DDSynth signature { q with nextTy := q.nextTy + 2 } S
        ((argument, NamedScheme.mono (.var q.nextTy)) ::
          (self, NamedScheme.mono
            (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
        body bodyTarget q₁ S₁}
      (bodyOrigin : DDSynthOrigin signature bodyRaw ledger ledger₁)
      (aligned : DDAlignTypesWithLedger ledger₁ S₁ bodyTarget
        (.var (q.nextTy + 1)) S') :
      DDSynthOrigin signature
        (.fix distinct direct nonMatcher bodyRaw aligned.erase) ledger ledger₁
  | app
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {function argument : Expr} {functionTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₃ : Subst}
      {ledger ledger₁ ledger₃ : CapabilityOriginLedger}
      {functionRaw : DDSynth signature q S context function functionTarget q₁ S₁}
      (functionOrigin : DDSynthOrigin signature functionRaw ledger ledger₁)
      (aligned : DDAlignTypesWithLedger ledger₁ S₁ functionTarget
        (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂)
      {argumentRaw : DDCheck signature
        { q₁ with nextTy := q₁.nextTy + 2 } S₂ context argument
        (.var q₁.nextTy) q₂ S₃}
      (argumentOrigin : DDCheckOrigin signature argumentRaw ledger₁ ledger₃) :
      DDSynthOrigin signature
        (.app functionRaw aligned.erase argumentRaw) ledger ledger₃
  | lit
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {value : Int} {ledger : CapabilityOriginLedger} :
      DDSynthOrigin signature (.lit (q := q) (S := S) (value := value)
        (Γ := context)) ledger ledger
  | tuple
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {expressions : List Expr} {targets : List Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger' : CapabilityOriginLedger}
      {children : DDSynths signature q S context expressions targets q' S'}
      (childrenOrigin : DDSynthsOrigin signature children ledger ledger') :
      DDSynthOrigin signature (.tuple children) ledger ledger'
  | ctor
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {name : String} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      (lookup : signature.findDataCtor name = some scheme)
      {children : DDChecks signature
        (InferenceBase.instantiateCtorScheme q scheme).supply S context
        expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
      (childrenOrigin : DDChecksOrigin signature children
        (DDLedger.markCtorInstance ledger q scheme) ledger₁) :
      DDSynthOrigin signature (.ctor lookup children) ledger
        (DDLedger.freezeExport ledger₁ S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
  | prim
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {op : PrimOp} {expressions : List Expr} {scheme : CtorScheme}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      (lookup : signature.findPrimitive op = some scheme)
      {children : DDChecks signature
        (InferenceBase.instantiateCtorScheme q scheme).supply S context
        expressions (InferenceBase.instantiateCtorScheme q scheme).value.1 q' S'}
      (childrenOrigin : DDChecksOrigin signature children
        (DDLedger.markCtorInstance ledger q scheme) ledger₁) :
      DDSynthOrigin signature (.prim lookup children) ledger
        (DDLedger.freezeExport ledger₁ S'
          (Inference.freshCapImages q scheme.capBinders)
          (InferenceBase.instantiateCtorScheme q scheme).value.2)
  | letE
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {name : String} {value body : Expr} {valueTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {bodyTarget : Ty}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {valueRaw : DDSynth signature q S context value valueTarget q₁ S₁}
      (valueOrigin : DDSynthOrigin signature valueRaw ledger ledger₁)
      {bodyRaw : DDSynth signature q₁ S₁
        ((name, signature.generalize (context.applySubst S₁)
          (S₁.apply valueTarget)) :: context) body bodyTarget q' S'}
      (bodyOrigin : DDSynthOrigin signature bodyRaw ledger₁ ledger')
      (stable :
        (signature.generalize (context.applySubst S₁)
          (S₁.apply valueTarget)).applySubst S' =
        signature.generalize (context.applySubst S')
          (S'.apply valueTarget)) :
      DDSynthOrigin signature (.letE valueRaw bodyRaw) ledger ledger'
  | something
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {ledger : CapabilityOriginLedger} :
      DDSynthOrigin signature (.something (q := q) (S := S)
        (Γ := context)) ledger ledger
  | matcher
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {clauses : List Clause} {rawHoleLists : List (List Dual)}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {evidence : List Shape.Evidence} {capability : Cap}
      {ledger ledger₁ : CapabilityOriginLedger}
      {clausesRaw : DDClauses signature
        { q with nextTy := q.nextTy + 1 } S context clauses
        (.var q.nextTy) rawHoleLists q' S'}
      (clausesOrigin : DDClausesOrigin signature clausesRaw ledger ledger₁)
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
        capability = true) :
      DDSynthOrigin signature
        (.matcher clausesRaw collected inferred clauseCaps catchAll binders
          arms coverage) ledger
        (DDLedger.freezeMatcherProducer ledger₁ capability)
  | matchAll
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {target matcher : Expr} {pattern : Pattern} {body : Expr}
      {targetTarget : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {dual : Dual} {bindings : MonoCtx} {q₂ : InferenceBase.FreshSupply}
      {S₂ S₃ : Subst} {q₃ : InferenceBase.FreshSupply} {S₄ : Subst}
      {bodyTarget : Ty} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger₂ ledger₃ ledger' : CapabilityOriginLedger}
      {targetRaw : DDSynth signature q S context target targetTarget q₁ S₁}
      (targetOrigin : DDSynthOrigin signature targetRaw ledger ledger₁)
      {patternRaw : DDPattern signature q₁ S₁ context [] [] pattern dual
        bindings q₂ S₂}
      (patternOrigin : DDPatternOrigin signature patternRaw ledger₁ ledger₂)
      (targetAligned : DDAlignTypesWithLedger ledger₂ S₂ dual.target
        targetTarget S₃)
      {matcherRaw : DDCheck signature q₂ S₃ context matcher
        (.slot dual.cap targetTarget) q₃ S₄}
      (matcherOrigin : DDCheckOrigin signature matcherRaw ledger₂ ledger₃)
      {bodyRaw : DDSynth signature q₃ S₄
        (bindings.toContext ++ context) body bodyTarget q' S'}
      (bodyOrigin : DDSynthOrigin signature bodyRaw ledger₃ ledger') :
      DDSynthOrigin signature
        (.matchAll targetRaw patternRaw targetAligned.erase matcherRaw bodyRaw)
        ledger ledger'
  | fixMatcher
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {self argument : String} {clauses : List Clause} {domain codomain : Ty}
      {q₀ : InferenceBase.FreshSupply} {bodyTarget : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      (distinct : self ≠ argument)
      (direct : DirectSelf.Holds self (.matcher clauses))
      (placeholder : fixMatcherPlaceholderSupply signature clauses q =
        some (domain, codomain, q₀))
      {bodyRaw : DDSynth signature q₀ S
        ((argument, NamedScheme.mono domain) ::
          (self, NamedScheme.mono (.fn domain codomain)) :: context)
        (.matcher clauses) bodyTarget q₁ S₁}
      (bodyOrigin : DDSynthOrigin signature bodyRaw
        (DDLedger.markCapRange ledger q q₀) ledger₁)
      (aligned : DDAlignTypesWithLedger ledger₁ S₁ bodyTarget codomain S') :
      DDSynthOrigin signature
        (.fixMatcher distinct direct placeholder bodyRaw aligned.erase)
        ledger ledger₁

/-- Origin provenance for an existing expression-synthesis list. -/
inductive DDSynthsOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {expressions : List Expr} -> {targets : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDSynths signature q S context expressions targets q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {ledger : CapabilityOriginLedger} :
      DDSynthsOrigin signature (.nil (q := q) (S := S) (Γ := context))
        ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {expression : Expr} {expressions : List Expr} {target : Ty}
      {targets : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDSynth signature q S context expression target q₁ S₁}
      {tail : DDSynths signature q₁ S₁ context expressions targets q' S'}
      (headOrigin : DDSynthOrigin signature head ledger ledger₁)
      (tailOrigin : DDSynthsOrigin signature tail ledger₁ ledger') :
      DDSynthsOrigin signature (.cons head tail) ledger ledger'

/-- Origin provenance for an existing expression-checking derivation. -/
inductive DDCheckOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {expression : Expr} -> {expected : Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDCheck signature q S context expression expected q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | mk
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {expression : Expr} {expected raw : Ty}
      {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      {synthesized : DDSynth signature q S context expression raw q₁ S₁}
      (synthOrigin : DDSynthOrigin signature synthesized ledger ledger₁)
      (aligned : DDAlignWithLedger ledger₁ S₁ raw expected S') :
      DDCheckOrigin signature (.mk synthesized aligned.erase) ledger ledger₁

/-- Origin provenance for an existing expression-checking list. -/
inductive DDChecksOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {expressions : List Expr} -> {expecteds : List Ty} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDChecks signature q S context expressions expecteds q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {ledger : CapabilityOriginLedger} :
      DDChecksOrigin signature (.nil (q := q) (S := S) (Γ := context))
        ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {expression : Expr} {expressions : List Expr} {expected : Ty}
      {expecteds : List Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDCheck signature q S context expression expected q₁ S₁}
      {tail : DDChecks signature q₁ S₁ context expressions expecteds q' S'}
      (headOrigin : DDCheckOrigin signature head ledger ledger₁)
      (tailOrigin : DDChecksOrigin signature tail ledger₁ ledger') :
      DDChecksOrigin signature (.cons head tail) ledger ledger'

/-- Origin provenance for an existing user-pattern derivation. -/
inductive DDPatternOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {parameters : PatternCtx} -> {bindingsIn : MonoCtx} ->
    {pattern : Pattern} -> {dual : Dual} -> {bindingsOut : MonoCtx} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | pvar
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {name : String}
      {ledger : CapabilityOriginLedger}
      (freshName : name ∉ bindings.names) :
      DDPatternOrigin signature (.pvar (q := q) freshName) ledger
        (DDLedger.markFreshCap ledger q)
  | wild
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx}
      {ledger : CapabilityOriginLedger} :
      DDPatternOrigin signature (.wild (q := q) (S := S) (Γ := context)
        (Φ := parameters) (Δ := bindings)) ledger
        (DDLedger.markFreshCap ledger q)
  | pval
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {expression : Expr}
      {target : Ty} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      {expressionRaw : DDSynth signature q S
        (bindings.toContext ++ context) expression target q₁ S₁}
      (expressionOrigin : DDSynthOrigin signature expressionRaw ledger ledger₁) :
      DDPatternOrigin signature (.pval expressionRaw) ledger
        (DDLedger.markFreshCap ledger₁ q₁)
  | embed
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {name : String}
      {dual : Dual} {ledger : CapabilityOriginLedger}
      (lookup : parameters.find? name = some dual) :
      DDPatternOrigin signature (.embed lookup) ledger ledger
  | ptuple
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx}
      {patterns : List Pattern} {duals : List Dual} {bindings' : MonoCtx}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger' : CapabilityOriginLedger}
      {children : DDPatterns signature q S context parameters bindings
        patterns duals bindings' q' S'}
      (childrenOrigin : DDPatternsOrigin signature children ledger ledger') :
      DDPatternOrigin signature (.ptuple children) ledger ledger'
  | pctor
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {name : String}
      {patterns : List Pattern}
      {entry : PatternCtorScheme signature.observability}
      {duals : List Dual} {bindings' : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ S₂ : Subst}
      {capability : Cap} {q₂ : InferenceBase.FreshSupply} {S₃ : Subst}
      {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
      (lookup : signature.findPatternCtor name = some entry)
      {children : DDPatterns signature
        (InferenceBase.instantiateCtorScheme q entry.scheme).supply S context
        parameters bindings patterns duals bindings' q₁ S₁}
      (childrenOrigin : DDPatternsOrigin signature children
        (DDLedger.markCtorInstance ledger q entry.scheme) ledger₁)
      (targetsAligned : DDAlignTargetListWithLedger ledger₁ S₁ duals
        (InferenceBase.instantiateCtorScheme q entry.scheme).value.1 S₂)
      {capRaw : DDPatternCtorCap signature entry q₁ S₂
        (duals.map Dual.cap) capability q₂ S₃}
      (capOrigin : DDPatternCtorCapOrigin signature entry capRaw
        ledger₁ ledger₂)
      (compatible : Inference.capCompatibleCheck entry
        ((duals.map Dual.cap).map fun child => child.apply S₃.cap)
        (capability.apply S₃.cap) = true) :
      DDPatternOrigin signature
        (.pctor lookup children targetsAligned.erase capRaw compatible) ledger
        (DDLedger.freezeExport ledger₂ S₃
          (Inference.freshCapImages q entry.scheme.capBinders)
          (Inference.capabilityExportPayload [capability]
            ((InferenceBase.instantiateCtorScheme q entry.scheme).value.2 ::
              bindings'.map fun binding => binding.2)))
  | pand
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {left right : Pattern}
      {leftDual : Dual} {leftBindings : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {rightDual : Dual} {bindings' : MonoCtx}
      {q₂ : InferenceBase.FreshSupply} {S₂ S' : Subst}
      {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
      {leftRaw : DDPattern signature q S context parameters bindings left
        leftDual leftBindings q₁ S₁}
      (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
      {rightRaw : DDPattern signature q₁ S₁ context parameters
        leftBindings right rightDual bindings' q₂ S₂}
      (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
      (aligned : DDAlignDualWithLedger ledger₂ S₂ leftDual rightDual S') :
      DDPatternOrigin signature (.pand leftRaw rightRaw aligned.erase)
        ledger ledger₂
  | por
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {left right : Pattern}
      {leftDual : Dual} {leftBindings : MonoCtx}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {rightDual : Dual} {rightBindings : MonoCtx}
      {q₂ : InferenceBase.FreshSupply} {S₂ S₃ S' : Subst}
      {ledger ledger₁ ledger₂ : CapabilityOriginLedger}
      {leftRaw : DDPattern signature q S context parameters bindings left
        leftDual leftBindings q₁ S₁}
      (leftOrigin : DDPatternOrigin signature leftRaw ledger ledger₁)
      {rightRaw : DDPattern signature q₁ S₁ context parameters bindings
        right rightDual rightBindings q₂ S₂}
      (rightOrigin : DDPatternOrigin signature rightRaw ledger₁ ledger₂)
      (dualsAligned : DDAlignDualWithLedger ledger₂ S₂ leftDual
        rightDual S₃)
      (bindingsAligned : DDAlignBindingsWithLedger ledger₂ S₃
        leftBindings rightBindings S') :
      DDPatternOrigin signature
        (.por leftRaw rightRaw dualsAligned.erase bindingsAligned.erase)
        ledger ledger₂
  | papp
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {name : String}
      {patterns : List Pattern} {scheme : DualScheme} {duals : List Dual}
      {bindings' : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ S' : Subst}
      {ledger ledger₁ : CapabilityOriginLedger}
      (lookup : signature.findPatternFun name = some scheme)
      {children : DDPatterns signature
        (InferenceBase.instantiateDualScheme q scheme).supply S context
        parameters bindings patterns duals bindings' q₁ S₁}
      (childrenOrigin : DDPatternsOrigin signature children
        (DDLedger.markDualInstance ledger q scheme) ledger₁)
      (aligned : DDAlignDualListWithLedger ledger₁ S₁ duals
        (InferenceBase.instantiateDualScheme q scheme).value.1 S') :
      DDPatternOrigin signature (.papp lookup children aligned.erase)
        ledger ledger₁

/-- Origin provenance for an existing user-pattern list derivation. -/
inductive DDPatternsOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {parameters : PatternCtx} -> {bindingsIn : MonoCtx} ->
    {patterns : List Pattern} -> {duals : List Dual} ->
    {bindingsOut : MonoCtx} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    DDPatterns signature q S context parameters bindingsIn patterns duals
      bindingsOut q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx}
      {ledger : CapabilityOriginLedger} :
      DDPatternsOrigin signature (.nil (q := q) (S := S) (Γ := context)
        (Φ := parameters) (Δ := bindings)) ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {parameters : PatternCtx} {bindings : MonoCtx} {pattern : Pattern}
      {patterns : List Pattern} {dual : Dual} {duals : List Dual}
      {bindings₁ : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {bindings' : MonoCtx} {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDPattern signature q S context parameters bindings pattern dual
        bindings₁ q₁ S₁}
      {tail : DDPatterns signature q₁ S₁ context parameters bindings₁
        patterns duals bindings' q' S'}
      (headOrigin : DDPatternOrigin signature head ledger ledger₁)
      (tailOrigin : DDPatternsOrigin signature tail ledger₁ ledger') :
      DDPatternsOrigin signature (.cons head tail) ledger ledger'

/-- Origin provenance for one matcher-clause arm list. -/
inductive DDArmsOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {ppBindings : MonoCtx} -> {arms : List Arm} -> {clauseTarget : Ty} ->
    {bodyTarget : Ty} -> {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDArms signature q S context ppBindings arms clauseTarget bodyTarget q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {ppBindings : MonoCtx} {clauseTarget bodyTarget : Ty}
      {ledger : CapabilityOriginLedger} :
      DDArmsOrigin signature (.nil (q := q) (S := S) (Γ := context)
        (ppBindings := ppBindings) (clauseTarget := clauseTarget)
        (bodyTarget := bodyTarget)) ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {ppBindings : MonoCtx} {dataPattern : DPat} {body : Expr}
      {arms : List Arm} {clauseTarget bodyTarget : Ty}
      {armBindings : MonoCtx} {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
      {patternRaw : DDDPat signature q S dataPattern clauseTarget armBindings q₁ S₁}
      (patternOrigin : DDDPatOrigin signature patternRaw ledger ledger₁)
      (disjoint :
        ∀ name, name ∈ armBindings.names -> name ∉ ppBindings.names)
      {bodyRaw : DDCheck signature q₁ S₁
        (armBindings.toContext ++ ppBindings.toContext ++ context) body
        bodyTarget q₂ S₂}
      (bodyOrigin : DDCheckOrigin signature bodyRaw ledger₁ ledger₂)
      {tailRaw : DDArms signature q₂ S₂ context ppBindings arms
        clauseTarget bodyTarget q' S'}
      (tailOrigin : DDArmsOrigin signature tailRaw ledger₂ ledger') :
      DDArmsOrigin signature
        (.cons patternRaw disjoint bodyRaw tailRaw) ledger ledger'

/-- Origin provenance for one matcher clause. -/
inductive DDClauseOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {clause : Clause} -> {sharedTarget : Ty} -> {holes : List Dual} ->
    {q' : InferenceBase.FreshSupply} -> {S' : Subst} ->
    DDClause signature q S context clause sharedTarget holes q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | mk
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {pp : PPat} {next : Expr} {arms : List Arm} {sharedTarget : Ty}
      {holes : List Dual} {ppBindings : MonoCtx} {nextMatchers : List Expr}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q₂ : InferenceBase.FreshSupply} {S₂ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger₂ ledger' : CapabilityOriginLedger}
      {ppRaw : DDPPat signature q S pp sharedTarget holes ppBindings q₁ S₁}
      (ppOrigin : DDPPatOrigin signature ppRaw ledger ledger₁)
      (decomposed : decomposeME next holes.length = some nextMatchers)
      {nextRaw : DDChecks signature q₁ S₁ context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) q₂ S₂}
      (nextOrigin : DDChecksOrigin signature nextRaw ledger₁ ledger₂)
      {armsRaw : DDArms signature q₂ S₂ context ppBindings arms
        sharedTarget (Ty.listT (prodTy (holes.map Dual.target))) q' S'}
      (armsOrigin : DDArmsOrigin signature armsRaw ledger₂ ledger') :
      DDClauseOrigin signature
        (.mk ppRaw decomposed nextRaw armsRaw) ledger ledger'

/-- Origin provenance for a matcher-clause list. -/
inductive DDClausesOrigin (signature : FrozenSig) :
    {q : InferenceBase.FreshSupply} -> {S : Subst} -> {context : NamedContext} ->
    {clauses : List Clause} -> {sharedTarget : Ty} ->
    {holeLists : List (List Dual)} -> {q' : InferenceBase.FreshSupply} ->
    {S' : Subst} ->
    DDClauses signature q S context clauses sharedTarget holeLists q' S' ->
    CapabilityOriginLedger -> CapabilityOriginLedger -> Prop where
  | nil
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {sharedTarget : Ty} {ledger : CapabilityOriginLedger} :
      DDClausesOrigin signature (.nil (q := q) (S := S) (Γ := context)
        (sharedTarget := sharedTarget)) ledger ledger
  | cons
      {q : InferenceBase.FreshSupply} {S : Subst} {context : NamedContext}
      {clause : Clause} {clauses : List Clause} {sharedTarget : Ty}
      {holes : List Dual} {holeLists : List (List Dual)}
      {q₁ : InferenceBase.FreshSupply} {S₁ : Subst}
      {q' : InferenceBase.FreshSupply} {S' : Subst}
      {ledger ledger₁ ledger' : CapabilityOriginLedger}
      {head : DDClause signature q S context clause sharedTarget holes q₁ S₁}
      {tail : DDClauses signature q₁ S₁ context clauses sharedTarget
        holeLists q' S'}
      (headOrigin : DDClauseOrigin signature head ledger ledger₁)
      (tailOrigin : DDClausesOrigin signature tail ledger₁ ledger') :
      DDClausesOrigin signature (.cons head tail) ledger ledger'

end

/-! Each intrinsic certificate erases definitionally to its raw derivation. -/

def DDSynthOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynth signature q S context expression target q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDSynthOrigin signature raw ledger ledger') :
    DDSynth signature q S context expression target q' S' :=
  raw

def DDSynthsOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDSynths signature q S context expressions targets q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDSynthsOrigin signature raw ledger ledger') :
    DDSynths signature q S context expressions targets q' S' :=
  raw

def DDCheckOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDCheck signature q S context expression expected q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDCheckOrigin signature raw ledger ledger') :
    DDCheck signature q S context expression expected q' S' :=
  raw

def DDChecksOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {expressions : List Expr} {expecteds : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDChecks signature q S context expressions expecteds q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDChecksOrigin signature raw ledger ledger') :
    DDChecks signature q S context expressions expecteds q' S' :=
  raw

def DDPatternOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {pattern : Pattern} {dual : Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDPatternOrigin signature raw ledger ledger') :
    DDPattern signature q S context parameters bindingsIn pattern dual
      bindingsOut q' S' :=
  raw

def DDPatternsOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {parameters : PatternCtx} {bindingsIn : MonoCtx}
    {patterns : List Pattern} {duals : List Dual} {bindingsOut : MonoCtx}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDPatterns signature q S context parameters bindingsIn patterns
      duals bindingsOut q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDPatternsOrigin signature raw ledger ledger') :
    DDPatterns signature q S context parameters bindingsIn patterns duals
      bindingsOut q' S' :=
  raw

def DDArmsOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {ppBindings : MonoCtx} {arms : List Arm}
    {clauseTarget bodyTarget : Ty} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDArms signature q S context ppBindings arms clauseTarget bodyTarget
      q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDArmsOrigin signature raw ledger ledger') :
    DDArms signature q S context ppBindings arms clauseTarget bodyTarget q' S' :=
  raw

def DDClauseOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {clause : Clause} {sharedTarget : Ty}
    {holes : List Dual} {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DDClause signature q S context clause sharedTarget holes q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDClauseOrigin signature raw ledger ledger') :
    DDClause signature q S context clause sharedTarget holes q' S' :=
  raw

def DDClausesOrigin.erase
    {signature : FrozenSig} {q : InferenceBase.FreshSupply} {S : Subst}
    {context : NamedContext} {clauses : List Clause} {sharedTarget : Ty}
    {holeLists : List (List Dual)} {q' : InferenceBase.FreshSupply}
    {S' : Subst}
    {raw : DDClauses signature q S context clauses sharedTarget holeLists q' S'}
    {ledger ledger' : CapabilityOriginLedger}
    (_ : DDClausesOrigin signature raw ledger ledger') :
    DDClauses signature q S context clauses sharedTarget holeLists q' S' :=
  raw

/-! ## Public origin-aware source typing -/

/-- Public source acceptance: raw demand-directed synthesis from the canonical
initial state, accompanied by its complete capability-origin provenance. -/
def DDTyping (signature : FrozenSig) (context : NamedContext)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ raw q' S',
    ∃ derived : DDSynth signature (Inference.initialSupply signature context)
        Subst.id context expression raw q' S',
      ∃ ledger', DDSynthOrigin signature derived [] ledger' ∧
      target = S'.apply raw

/-- Every origin-aware published type is bounded by the terminal supply. -/
theorem DDTyping.published_boundedBy {signature : FrozenSig}
    {context : NamedContext} {expression : Expr} {target : Ty}
    (typed : DDTyping signature context expression target)
    (closed : signature.SchemesClosed) :
    ∃ q', SupplyExtends (Inference.initialSupply signature context) q' ∧
      Ty.BoundedBy q' target := by
  obtain ⟨raw, q', S', derived, _ledger', _origin, published⟩ := typed
  obtain ⟨S'b, rawB⟩ := derived.boundedBy closed
    (Subst.boundedBy_id _)
    (initialSupply_context_boundedBy signature context)
  exact ⟨q', derived.supplyExtends, published ▸ S'b.apply rawB⟩

end TypePM
