import TypePM.CertifiedInference
import TypePM.CoherentSurface
import TypePM.DamasMilner

/-!
# Mutual coherent surface typing and the annotation-freeness goal

`CoherentSurface.lean` pins the raw/actual context connection of pattern
leaves, but its independent judgments keep `HasTy` oracles at value-pattern
premises, so they cannot serve as the hypothesis of a recursive completeness
statement.  This module supplies the missing mutually inductive domain: ten
families covering expressions, expression lists, threaded pattern resolution,
resolved patterns, arms, and clauses, in which every expression premise is the
coherent judgment itself.

The families deliberately mirror the consumed core of
`Reconstruction.ExprDeriv`, with two additions on the certless product lifts:
`coerceProductMatcher` and `coerceSlotTuple` carry a raw-source type and a
lift substitution whose image is the coerced product.  These indices are
provenance hooks for a future raw-head-visibility fragment statement; the
identity witness is always available (`Subst.apply_id`), so they do not
restrict the judgment.  The pattern layer is threaded-only, matching
`ResolvedPatternDeriv.ofThreaded`; aligned surface evidence without value
patterns embeds separately and is not a primitive constructor here.

Proved boundaries:

* `toExprDeriv`/`ofExprDeriv`: the coherent judgment and the reconstruction
  certificate are interderivable.  The `ofExprDeriv` direction supplies the
  degenerate identity provenance on product lifts.
* `CoherentExpr.toHasTy`: coherent typings are surface typings.
* `infer_success_coherent`: successful public inference lands in the coherent
  judgment.
* `CoherentPattern.toThreadedSurface`: the mutual pattern family forgets onto
  the documented standalone threaded boundary.

`AnnotationFree` states the top-level project goal — acceptance completeness
of public inference for closed declaratively typed programs — as a named
proposition only.  It is not asserted, not axiomatized, and remains open;
neither algorithmic completeness nor any principality claim is made here.
-/

namespace TypePM
namespace Coherent

open Inference.Reconstruction

mutual

/-- Coherent expression typing.  Expression-level constructors mirror `HasTy`
and `ExprDeriv`; pattern, arm, and clause premises stay inside this mutual
family, and the product lifts retain raw-source provenance indices. -/
inductive CoherentExpr (signature : FrozenSig) : Context -> Expr -> Ty -> Prop where
  | var {context name scheme target} :
      context.find? name = some scheme ->
      scheme.ValueFlowInst target ->
      CoherentExpr signature context (.var name) target
  | lam {context name body domain codomain} :
      CoherentExpr signature ((name, Scheme.mono domain) :: context) body
        codomain ->
      CoherentExpr signature context (.lam name body) (.fn domain codomain)
  | app {context function argument domain codomain} :
      CoherentExpr signature context function (.fn domain codomain) ->
      CoherentExpr signature context argument domain ->
      CoherentExpr signature context (.app function argument) codomain
  | letE {context name value body valueTy bodyTy} :
      CoherentExpr signature context value valueTy ->
      CoherentExpr signature
        ((name, signature.generalize context valueTy) :: context) body bodyTy ->
      CoherentExpr signature context (.letE name value body) bodyTy
  | fixE {context self argument body domain codomain} :
      self ≠ argument ->
      DirectSelf.Holds self body ->
      CoherentExpr signature
        ((argument, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: context)
        body codomain ->
      CoherentExpr signature context (.fix self argument body)
        (.fn domain codomain)
  | lit {context value} :
      CoherentExpr signature context (.lit value) .int
  | tuple {context expressions targets} :
      CoherentExprs signature context expressions targets ->
      CoherentExpr signature context (.tuple expressions) (.prod targets)
  | ctor {context name expressions targets result scheme} :
      signature.findDataCtor name = some scheme ->
      scheme.Inst targets result ->
      CoherentExprs signature context expressions targets ->
      CoherentExpr signature context (.ctor name expressions) result
  | prim {context op expressions targets result scheme} :
      signature.findPrimitive op = some scheme ->
      scheme.Inst targets result ->
      CoherentExprs signature context expressions targets ->
      CoherentExpr signature context (.prim op expressions) result
  | something {context target} :
      CoherentExpr signature context .something (.matcher .any target)
  | matchAll
      {prevailing context target matcher pattern body targetTy patternCap
       bindings result} :
      CoherentExpr signature context target targetTy ->
      CoherentResolvedPattern signature prevailing context [] [] pattern
        patternCap targetTy bindings ->
      CoherentExpr signature context matcher (.slot patternCap targetTy) ->
      CoherentExpr signature (bindings.toContext ++ context) body result ->
      CoherentExpr signature context (.matchAll target matcher pattern body)
        (Ty.listT result)
  | matcher {context clauses target capability evidence} :
      CoherentResolvedClauses signature context clauses capability target
        evidence ->
      Shape.inferShape signature.observability evidence = some capability ->
      CatchAllLast clauses ->
      ArmExhaustive signature clauses target ->
      PPBindNodup clauses ->
      ArmBindNodup clauses ->
      CoverageOK signature.toMatcherSig clauses capability ->
      CoherentExpr signature context (.matcher clauses)
        (.matcher capability target)
  | coerceMatcherToSlot
      {context expression producerCap producerTarget consumerCap consumerTarget
       bindings C T post} :
      CoherentExpr signature context expression
        (.matcher ((producerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply producerTarget))) ->
      MatcherToSlotRawCert producerCap consumerCap producerTarget
        consumerTarget bindings C T ->
      VariablePost post ->
      CoherentExpr signature context expression
        (.slot ((consumerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply consumerTarget)))
  | checkSlotToSlot
      {context expression sourceCap sourceTarget requestedCap requestedTarget C
       T post} :
      CoherentExpr signature context expression
        (.slot ((sourceCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply sourceTarget))) ->
      SlotToSlotRawCert sourceCap requestedCap sourceTarget requestedTarget
        C T ->
      VariablePost post ->
      CoherentExpr signature context expression
        (.slot ((requestedCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply requestedTarget)))
  | coerceProductMatcher
      {context expression} {rawSource : Ty} {lift : Subst}
      {duals : List Dual} :
      CoherentExpr signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target)) ->
      lift.apply rawSource
        = .prod (duals.map fun dual => .matcher dual.cap dual.target) ->
      CoherentExpr signature context expression
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  | coerceSlotTuple
      {context expression} {rawSource : Ty} {lift : Subst}
      {duals : List Dual} :
      CoherentExpr signature context expression
        (.prod (duals.map fun dual => .slot dual.cap dual.target)) ->
      lift.apply rawSource
        = .prod (duals.map fun dual => .slot dual.cap dual.target) ->
      CoherentExpr signature context expression
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- Coherent expression-list typing with exact source order and arity. -/
inductive CoherentExprs (signature : FrozenSig) :
    Context -> List Expr -> List Ty -> Prop where
  | nil {context} : CoherentExprs signature context [] []
  | cons {context expression target expressions targets} :
      CoherentExpr signature context expression target ->
      CoherentExprs signature context expressions targets ->
      CoherentExprs signature context (expression :: expressions)
        (target :: targets)

/-- Coherent user-pattern resolution under one fixed raw expression context
and pattern-parameter context, with the raw monomorphic context threaded
left-to-right.  Value-pattern leaves recurse into `CoherentExpr` at their
prevailing-applied occurrence. -/
inductive CoherentPattern (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | pvar {context parameters bindings name capVar tyVar} :
      name ∉ bindings.names ->
      FreshCap signature context parameters bindings capVar ->
      FreshTy signature context parameters bindings tyVar ->
      CoherentPattern signature prevailing
        context parameters bindings (.pvar name)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        (bindings ++ [(name, Ty.var tyVar)])
  | wild {context parameters bindings capVar tyVar} :
      FreshCap signature context parameters bindings capVar ->
      FreshTy signature context parameters bindings tyVar ->
      CoherentPattern signature prevailing
        context parameters bindings .wild
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (.var tyVar))
        bindings
  | pval {context parameters bindings expression rawTarget capVar} :
      FreshCap signature context parameters bindings capVar ->
      capVar ∉ rawTarget.fcv ->
      CoherentExpr signature
        ((bindings.applySubst prevailing).toContext ++
          context.applySubst prevailing)
        expression (prevailing.apply rawTarget) ->
      CoherentPattern signature prevailing
        context parameters bindings (.pval expression)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply rawTarget)
        bindings
  | embed {context : Context} {parameters : PatternCtx}
      {bindings : MonoCtx} {name : String} {rawDual : Dual} :
      parameters.find? name = some rawDual ->
      (parameters.applySubst prevailing).find? name =
        some (rawDual.applySubst prevailing) ->
      CoherentPattern signature prevailing
        context parameters bindings (.embed name)
        (rawDual.cap.apply prevailing.cap)
        (prevailing.apply rawDual.target)
        bindings
  | tuple {context parameters bindings patterns duals resultBindings} :
      CoherentPatterns signature prevailing context parameters bindings
        patterns duals resultBindings ->
      CoherentPattern signature prevailing context parameters bindings
        (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry ->
      CoherentPatterns signature prevailing context parameters bindings
        patterns duals resultBindings ->
      entry.CapCompatible (duals.map Dual.cap) result.cap ->
      entry.Inst (duals.map Dual.target) result.target ->
      CoherentPattern signature prevailing context parameters bindings
        (.pctor name patterns) result.cap result.target resultBindings
  | and {context parameters bindings left right cap target middle result} :
      CoherentPattern signature prevailing context parameters bindings
        left cap target middle ->
      CoherentPattern signature prevailing context parameters middle
        right cap target result ->
      CoherentPattern signature prevailing context parameters bindings
        (.pand left right) cap target result
  | or {context parameters bindings left right cap target result} :
      CoherentPattern signature prevailing context parameters bindings
        left cap target result ->
      CoherentPattern signature prevailing context parameters bindings
        right cap target result ->
      CoherentPattern signature prevailing context parameters bindings
        (.por left right) cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme ->
      CoherentPatterns signature prevailing context parameters bindings
        patterns duals resultBindings ->
      scheme.ValueFlowInst duals result ->
      CoherentPattern signature prevailing context parameters bindings
        (.papp name patterns) result.cap result.target resultBindings

/-- Left-to-right raw-context-threaded coherent pattern list. -/
inductive CoherentPatterns (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> List Pattern -> List Dual ->
      MonoCtx -> Prop where
  | nil {context parameters bindings} :
      CoherentPatterns signature prevailing context parameters bindings
        [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle patterns duals
       result} :
      CoherentPattern signature prevailing context parameters bindings
        pattern cap target middle ->
      CoherentPatterns signature prevailing context parameters middle
        patterns duals result ->
      CoherentPatterns signature prevailing context parameters bindings
        (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/-- Coherent user pattern under one occurrence-wide substitution. -/
inductive CoherentResolvedPattern (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | ofThreaded
      {rawContext rawParameters rawBindings pattern capability target
       rawResultBindings} :
      CoherentPattern signature prevailing rawContext rawParameters
        rawBindings pattern capability target rawResultBindings ->
      CoherentResolvedPattern signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) pattern capability target
        (rawResultBindings.applySubst prevailing)

/-- Coherent matcher arm. -/
inductive CoherentArm (signature : FrozenSig) :
    Context -> Ty -> MonoCtx -> Ty -> Arm -> Prop where
  | mk {context target ppBindings result pattern body armBindings} :
      DPatDeriv signature pattern target armBindings ->
      CoherentExpr signature
        (armBindings.toContext ++ ppBindings.toContext ++ context)
        body result ->
      CoherentArm signature context target ppBindings result (.mk pattern body)

/-- Coherent matcher arm list. -/
inductive CoherentArms (signature : FrozenSig) :
    Context -> Ty -> MonoCtx -> Ty -> List Arm -> Prop where
  | nil {context target ppBindings result} :
      CoherentArms signature context target ppBindings result []
  | cons {context target ppBindings result arm arms} :
      CoherentArm signature context target ppBindings result arm ->
      CoherentArms signature context target ppBindings result arms ->
      CoherentArms signature context target ppBindings result (arm :: arms)

/-- Coherent actual clause under its shared prevailing substitution. -/
inductive CoherentClause (signature : FrozenSig) :
    Subst -> Context -> Clause -> Cap -> Ty -> Shape.Evidence -> Prop where
  | mk {context capability target pp next arms holes ppBindings nextMatchers
        evidence} :
      PPatCoreOrder pp ->
      ResolvedPPatDeriv signature prevailing pp target holes ppBindings ->
      PPatCapsAt signature true pp (holes.map Dual.cap) capability ->
      decomposeME next holes.length = some nextMatchers ->
      CoherentExprs signature context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) ->
      CoherentArms signature context target ppBindings
        (Ty.listT (prodTy (holes.map Dual.target))) arms ->
      clauseEvidence signature.toMatcherSig pp (holes.map Dual.cap) =
        some evidence ->
      CoherentClause signature prevailing context (.mk pp next arms)
        capability target evidence

/-- Coherent clause list with one shared prevailing substitution. -/
inductive CoherentClauses (signature : FrozenSig) :
    Subst -> Context -> List Clause -> Cap -> Ty -> List Shape.Evidence ->
      Prop where
  | nil {context target} :
      CoherentClauses signature prevailing context [] capability target []
  | cons {context clause clauses target evidence evidences} :
      CoherentClause signature prevailing context clause capability target
        evidence ->
      CoherentClauses signature prevailing context clauses capability target
        evidences ->
      CoherentClauses signature prevailing context (clause :: clauses)
        capability target (evidence :: evidences)

/-- Existential package of the shared coherent clause substitution. -/
inductive CoherentResolvedClauses (signature : FrozenSig) :
    Context -> List Clause -> Cap -> Ty -> List Shape.Evidence -> Prop where
  | ofShared {prevailing context clauses capability target evidence} :
      CoherentClauses signature prevailing context clauses capability target
        evidence ->
      CoherentResolvedClauses signature context clauses capability target
        evidence

end

/-! ## Certification: the coherent judgment maps onto reconstruction evidence -/

mutual

/-- Erase product-lift provenance and land in the reconstruction certificate. -/
def CoherentExpr.toExprDeriv
    {signature context expression target}
    (derivation : CoherentExpr signature context expression target) :
    ExprDeriv signature context expression target :=
  match derivation with
  | .var lookup flow => .var lookup flow
  | .lam body => .lam body.toExprDeriv
  | .app function argument => .app function.toExprDeriv argument.toExprDeriv
  | .letE value body => .letE value.toExprDeriv body.toExprDeriv
  | .fixE distinct direct body => .fixE distinct direct body.toExprDeriv
  | .lit => .lit
  | .tuple expressions => .tuple expressions.toExprsDeriv
  | .ctor lookup instanceTyping expressions =>
      .ctor lookup instanceTyping expressions.toExprsDeriv
  | .prim lookup instanceTyping expressions =>
      .prim lookup instanceTyping expressions.toExprsDeriv
  | .something => .something
  | .matchAll target resolved matcher body =>
      .matchAll target.toExprDeriv resolved.toResolvedPatternDeriv
        matcher.toExprDeriv body.toExprDeriv
  | .matcher clauses shape catchAll exhaustive ppNodup armNodup coverage =>
      .matcher clauses.toResolvedClausesDeriv shape catchAll exhaustive
        ppNodup armNodup coverage
  | .coerceMatcherToSlot premise certificate post =>
      .coerceMatcherToSlot premise.toExprDeriv certificate post
  | .checkSlotToSlot premise certificate post =>
      .checkSlotToSlot premise.toExprDeriv certificate post
  | .coerceProductMatcher premise _provenance =>
      .coerceProductMatcher premise.toExprDeriv
  | .coerceSlotTuple premise _provenance =>
      .coerceSlotTuple premise.toExprDeriv

/-- List form of `CoherentExpr.toExprDeriv`. -/
def CoherentExprs.toExprsDeriv
    {signature context expressions targets}
    (derivation : CoherentExprs signature context expressions targets) :
    ExprsDeriv signature context expressions targets :=
  match derivation with
  | .nil => .nil
  | .cons head tail => .cons head.toExprDeriv tail.toExprsDeriv

/-- Pattern form of the certification map. -/
def CoherentPattern.toPatternResolutionDeriv
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : CoherentPattern signature prevailing context parameters
      bindings pattern capability target result) :
    PatternResolutionDeriv signature prevailing context parameters bindings
      pattern capability target result :=
  match derivation with
  | .pvar missing freshCap freshTy => .pvar missing freshCap freshTy
  | .wild freshCap freshTy => .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate expressionTyping.toExprDeriv
  | .embed rawLookup actualLookup => .embed rawLookup actualLookup
  | .tuple children => .tuple children.toPatternResolutionsDeriv
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup children.toPatternResolutionsDeriv compatible
        instanceTyping
  | .and left right =>
      .and left.toPatternResolutionDeriv right.toPatternResolutionDeriv
  | .or left right =>
      .or left.toPatternResolutionDeriv right.toPatternResolutionDeriv
  | .app lookup children instanceTyping =>
      .app lookup children.toPatternResolutionsDeriv instanceTyping

/-- Pattern-list form of the certification map. -/
def CoherentPatterns.toPatternResolutionsDeriv
    {signature prevailing context parameters bindings patterns duals result}
    (derivation : CoherentPatterns signature prevailing context parameters
      bindings patterns duals result) :
    PatternResolutionsDeriv signature prevailing context parameters bindings
      patterns duals result :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons head.toPatternResolutionDeriv tail.toPatternResolutionsDeriv

/-- Resolved-pattern form of the certification map. -/
def CoherentResolvedPattern.toResolvedPatternDeriv
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : CoherentResolvedPattern signature prevailing context
      parameters bindings pattern capability target result) :
    ResolvedPatternDeriv signature prevailing context parameters bindings
      pattern capability target result :=
  match derivation with
  | .ofThreaded threaded => .ofThreaded threaded.toPatternResolutionDeriv

/-- Arm form of the certification map. -/
def CoherentArm.toArmDeriv
    {signature context target ppBindings result arm}
    (derivation : CoherentArm signature context target ppBindings result arm) :
    ArmDeriv signature context target ppBindings result arm :=
  match derivation with
  | .mk dataPattern body => .mk dataPattern body.toExprDeriv

/-- Arm-list form of the certification map. -/
def CoherentArms.toArmsDeriv
    {signature context target ppBindings result arms}
    (derivation : CoherentArms signature context target ppBindings result
      arms) :
    ArmsDeriv signature context target ppBindings result arms :=
  match derivation with
  | .nil => .nil
  | .cons head tail => .cons head.toArmDeriv tail.toArmsDeriv

/-- Clause form of the certification map. -/
def CoherentClause.toClauseDeriv
    {signature prevailing context clause capability target evidence}
    (derivation : CoherentClause signature prevailing context clause capability
      target evidence) :
    ClauseDeriv signature prevailing context clause capability target
      evidence :=
  match derivation with
  | .mk order resolvedPP caps decompose nextMatchers arms evidenceEq =>
      .mk order resolvedPP caps decompose nextMatchers.toExprsDeriv
        arms.toArmsDeriv evidenceEq

/-- Clause-list form of the certification map. -/
def CoherentClauses.toClausesDeriv
    {signature prevailing context clauses capability target evidences}
    (derivation : CoherentClauses signature prevailing context clauses
      capability target evidences) :
    ClausesDeriv signature prevailing context clauses capability target
      evidences :=
  match derivation with
  | .nil => .nil
  | .cons head tail => .cons head.toClauseDeriv tail.toClausesDeriv

/-- Resolved-clause form of the certification map. -/
def CoherentResolvedClauses.toResolvedClausesDeriv
    {signature context clauses capability target evidences}
    (derivation : CoherentResolvedClauses signature context clauses capability
      target evidences) :
    ResolvedClausesDeriv signature context clauses capability target
      evidences :=
  match derivation with
  | .ofShared shared => .ofShared shared.toClausesDeriv

end

/-! ## Reconstruction evidence is coherent -/

mutual

/-- Reconstruction certificates enter the coherent judgment; product lifts
receive the degenerate identity provenance. -/
def CoherentExpr.ofExprDeriv
    {signature context expression target}
    (derivation : ExprDeriv signature context expression target) :
    CoherentExpr signature context expression target :=
  match derivation with
  | .var lookup flow => .var lookup flow
  | .lam body => .lam (CoherentExpr.ofExprDeriv body)
  | .app function argument =>
      .app (CoherentExpr.ofExprDeriv function)
        (CoherentExpr.ofExprDeriv argument)
  | .letE value body =>
      .letE (CoherentExpr.ofExprDeriv value) (CoherentExpr.ofExprDeriv body)
  | .fixE distinct direct body =>
      .fixE distinct direct (CoherentExpr.ofExprDeriv body)
  | .lit => .lit
  | .tuple expressions => .tuple (CoherentExprs.ofExprsDeriv expressions)
  | .ctor lookup instanceTyping expressions =>
      .ctor lookup instanceTyping (CoherentExprs.ofExprsDeriv expressions)
  | .prim lookup instanceTyping expressions =>
      .prim lookup instanceTyping (CoherentExprs.ofExprsDeriv expressions)
  | .something => .something
  | .matchAll target resolved matcher body =>
      .matchAll (CoherentExpr.ofExprDeriv target)
        (CoherentResolvedPattern.ofResolvedPatternDeriv resolved)
        (CoherentExpr.ofExprDeriv matcher) (CoherentExpr.ofExprDeriv body)
  | .matcher clauses shape catchAll exhaustive ppNodup armNodup coverage =>
      .matcher (CoherentResolvedClauses.ofResolvedClausesDeriv clauses) shape
        catchAll exhaustive ppNodup armNodup coverage
  | .coerceMatcherToSlot premise certificate post =>
      .coerceMatcherToSlot (CoherentExpr.ofExprDeriv premise) certificate post
  | .checkSlotToSlot premise certificate post =>
      .checkSlotToSlot (CoherentExpr.ofExprDeriv premise) certificate post
  | .coerceProductMatcher premise =>
      .coerceProductMatcher (CoherentExpr.ofExprDeriv premise)
        (Subst.apply_id _)
  | .coerceSlotTuple premise =>
      .coerceSlotTuple (CoherentExpr.ofExprDeriv premise) (Subst.apply_id _)

/-- List form of `CoherentExpr.ofExprDeriv`. -/
def CoherentExprs.ofExprsDeriv
    {signature context expressions targets}
    (derivation : ExprsDeriv signature context expressions targets) :
    CoherentExprs signature context expressions targets :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons (CoherentExpr.ofExprDeriv head) (CoherentExprs.ofExprsDeriv tail)

/-- Pattern form of the embedding. -/
def CoherentPattern.ofPatternResolutionDeriv
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : PatternResolutionDeriv signature prevailing context
      parameters bindings pattern capability target result) :
    CoherentPattern signature prevailing context parameters bindings pattern
      capability target result :=
  match derivation with
  | .pvar missing freshCap freshTy => .pvar missing freshCap freshTy
  | .wild freshCap freshTy => .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate (CoherentExpr.ofExprDeriv expressionTyping)
  | .embed rawLookup actualLookup => .embed rawLookup actualLookup
  | .tuple children =>
      .tuple (CoherentPatterns.ofPatternResolutionsDeriv children)
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup (CoherentPatterns.ofPatternResolutionsDeriv children)
        compatible instanceTyping
  | .and left right =>
      .and (CoherentPattern.ofPatternResolutionDeriv left)
        (CoherentPattern.ofPatternResolutionDeriv right)
  | .or left right =>
      .or (CoherentPattern.ofPatternResolutionDeriv left)
        (CoherentPattern.ofPatternResolutionDeriv right)
  | .app lookup children instanceTyping =>
      .app lookup (CoherentPatterns.ofPatternResolutionsDeriv children)
        instanceTyping

/-- Pattern-list form of the embedding. -/
def CoherentPatterns.ofPatternResolutionsDeriv
    {signature prevailing context parameters bindings patterns duals result}
    (derivation : PatternResolutionsDeriv signature prevailing context
      parameters bindings patterns duals result) :
    CoherentPatterns signature prevailing context parameters bindings patterns
      duals result :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons (CoherentPattern.ofPatternResolutionDeriv head)
        (CoherentPatterns.ofPatternResolutionsDeriv tail)

/-- Resolved-pattern form of the embedding. -/
def CoherentResolvedPattern.ofResolvedPatternDeriv
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : ResolvedPatternDeriv signature prevailing context parameters
      bindings pattern capability target result) :
    CoherentResolvedPattern signature prevailing context parameters bindings
      pattern capability target result :=
  match derivation with
  | .ofThreaded threaded =>
      .ofThreaded (CoherentPattern.ofPatternResolutionDeriv threaded)

/-- Arm form of the embedding. -/
def CoherentArm.ofArmDeriv
    {signature context target ppBindings result arm}
    (derivation : ArmDeriv signature context target ppBindings result arm) :
    CoherentArm signature context target ppBindings result arm :=
  match derivation with
  | .mk dataPattern body =>
      .mk dataPattern (CoherentExpr.ofExprDeriv body)

/-- Arm-list form of the embedding. -/
def CoherentArms.ofArmsDeriv
    {signature context target ppBindings result arms}
    (derivation : ArmsDeriv signature context target ppBindings result arms) :
    CoherentArms signature context target ppBindings result arms :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons (CoherentArm.ofArmDeriv head) (CoherentArms.ofArmsDeriv tail)

/-- Clause form of the embedding. -/
def CoherentClause.ofClauseDeriv
    {signature prevailing context clause capability target evidence}
    (derivation : ClauseDeriv signature prevailing context clause capability
      target evidence) :
    CoherentClause signature prevailing context clause capability target
      evidence :=
  match derivation with
  | .mk order resolvedPP caps decompose nextMatchers arms evidenceEq =>
      .mk order resolvedPP caps decompose
        (CoherentExprs.ofExprsDeriv nextMatchers)
        (CoherentArms.ofArmsDeriv arms) evidenceEq

/-- Clause-list form of the embedding. -/
def CoherentClauses.ofClausesDeriv
    {signature prevailing context clauses capability target evidences}
    (derivation : ClausesDeriv signature prevailing context clauses capability
      target evidences) :
    CoherentClauses signature prevailing context clauses capability target
      evidences :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons (CoherentClause.ofClauseDeriv head)
        (CoherentClauses.ofClausesDeriv tail)

/-- Resolved-clause form of the embedding. -/
def CoherentResolvedClauses.ofResolvedClausesDeriv
    {signature context clauses capability target evidences}
    (derivation : ResolvedClausesDeriv signature context clauses capability
      target evidences) :
    CoherentResolvedClauses signature context clauses capability target
      evidences :=
  match derivation with
  | .ofShared shared => .ofShared (CoherentClauses.ofClausesDeriv shared)

end

/-! ## Surface soundness and inference corollaries -/

/-- Coherent typings are surface typings. -/
theorem CoherentExpr.toHasTy
    {signature context expression target}
    (derivation : CoherentExpr signature context expression target) :
    HasTy signature context expression target :=
  derivation.toExprDeriv.toHasTy

/-- Successful public inference lands in the coherent judgment. -/
theorem infer_success_coherent
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {result : Inference.ExprResult}
    (success : Inference.infer signature context expression = some result) :
    CoherentExpr signature
      (Inference.ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget :=
  CoherentExpr.ofExprDeriv (Inference.infer_success_reconstruct success)

/-! ## Forgetting onto the standalone threaded boundary -/

mutual

/-- The mutual pattern family forgets its recursive value-pattern premises to
`HasTy` and lands in the documented standalone threaded boundary. -/
def CoherentPattern.toThreadedSurface
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : CoherentPattern signature prevailing context parameters
      bindings pattern capability target result) :
    CoherentSurface.ThreadedPatternResolution signature prevailing context
      parameters bindings pattern capability target result :=
  match derivation with
  | .pvar missing freshCap freshTy => .pvar missing freshCap freshTy
  | .wild freshCap freshTy => .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate expressionTyping.toHasTy
  | .embed rawLookup actualLookup => .embed rawLookup actualLookup
  | .tuple children => .tuple children.toThreadedSurfaces
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup children.toThreadedSurfaces compatible instanceTyping
  | .and left right =>
      .and left.toThreadedSurface right.toThreadedSurface
  | .or left right =>
      .or left.toThreadedSurface right.toThreadedSurface
  | .app lookup children instanceTyping =>
      .app lookup children.toThreadedSurfaces instanceTyping

/-- List form of `CoherentPattern.toThreadedSurface`. -/
def CoherentPatterns.toThreadedSurfaces
    {signature prevailing context parameters bindings patterns duals result}
    (derivation : CoherentPatterns signature prevailing context parameters
      bindings patterns duals result) :
    CoherentSurface.ThreadedPatternResolutions signature prevailing context
      parameters bindings patterns duals result :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons head.toThreadedSurface tail.toThreadedSurfaces

end

/-! ## The match-free fragment is coherent

Coherence restricts only pattern provenance, so surface typings of
expressions without `matchAll` and matcher literals are all coherent: their
typing constructors mirror the reconstruction certificate one to one.  This
discharges the declarative half of the staged Damas–Milner acceptance goal —
every DM typing embeds into the coherent judgment and hence carries a
recursive core certificate. -/

mutual

/-- Expressions that contain no `matchAll` and no matcher literal. -/
def matchFree : Expr → Bool
  | .var _ => true
  | .lam _ body => matchFree body
  | .fix _ _ body => matchFree body
  | .app function argument => matchFree function && matchFree argument
  | .lit _ => true
  | .tuple expressions => matchFreeList expressions
  | .ctor _ expressions => matchFreeList expressions
  | .prim _ expressions => matchFreeList expressions
  | .letE _ value body => matchFree value && matchFree body
  | .something => true
  | .matcher _ => false
  | .matchAll _ _ _ _ => false

/-- List form of `matchFree`. -/
def matchFreeList : List Expr → Bool
  | [] => true
  | expression :: expressions =>
      matchFree expression && matchFreeList expressions

end

mutual

/-- Every surface typing of a match-free expression is coherent. -/
theorem coherent_of_matchFree {signature : FrozenSig} :
    ∀ {context : Context} {expression : Expr} {target : Ty},
      HasTy signature context expression target →
      matchFree expression = true →
      CoherentExpr signature context expression target
  | _, _, _, .var lookup flow, _ => .var lookup flow
  | _, _, _, .lam bodyTyping, hfree =>
      .lam (coherent_of_matchFree bodyTyping hfree)
  | _, _, _, .app functionTyping argumentTyping, hfree => by
      simp only [matchFree, Bool.and_eq_true] at hfree
      exact .app (coherent_of_matchFree functionTyping hfree.1)
        (coherent_of_matchFree argumentTyping hfree.2)
  | _, _, _, .letE valueTyping bodyTyping, hfree => by
      simp only [matchFree, Bool.and_eq_true] at hfree
      exact .letE (coherent_of_matchFree valueTyping hfree.1)
        (coherent_of_matchFree bodyTyping hfree.2)
  | _, _, _, .fixE distinct direct bodyTyping, hfree =>
      .fixE distinct direct (coherent_of_matchFree bodyTyping hfree)
  | _, _, _, .lit, _ => .lit
  | _, _, _, .tuple typings, hfree =>
      .tuple (coherents_of_matchFree typings hfree)
  | _, _, _, .ctor lookup instanceTyping typings, hfree =>
      .ctor lookup instanceTyping (coherents_of_matchFree typings hfree)
  | _, _, _, .prim lookup instanceTyping typings, hfree =>
      .prim lookup instanceTyping (coherents_of_matchFree typings hfree)
  | _, _, _, .something, _ => .something
  | _, _, _, .matchAll _ _ _ _, hfree => by
      simp [matchFree] at hfree
  | _, _, _, .matcher _ _ _ _ _ _ _, hfree => by
      simp [matchFree] at hfree
  | _, _, _, .coerceMatcherToSlot premise certificate post, hfree =>
      .coerceMatcherToSlot (coherent_of_matchFree premise hfree)
        certificate post
  | _, _, _, .checkSlotToSlot premise certificate post, hfree =>
      .checkSlotToSlot (coherent_of_matchFree premise hfree) certificate post
  | _, _, _, .coerceProductMatcher premise, hfree =>
      .coerceProductMatcher (coherent_of_matchFree premise hfree)
        (Subst.apply_id _)
  | _, _, _, .coerceSlotTuple premise, hfree =>
      .coerceSlotTuple (coherent_of_matchFree premise hfree)
        (Subst.apply_id _)

/-- List form of `coherent_of_matchFree`. -/
theorem coherents_of_matchFree {signature : FrozenSig} :
    ∀ {context : Context} {expressions : List Expr} {targets : List Ty},
      ExprsTy signature context expressions targets →
      matchFreeList expressions = true →
      CoherentExprs signature context expressions targets
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons head tail, hfree => by
      simp only [matchFreeList, Bool.and_eq_true] at hfree
      exact .cons (coherent_of_matchFree head hfree.1)
        (coherents_of_matchFree tail hfree.2)

end

/-- Match-free surface typings carry recursive core certificates. -/
theorem certified_of_matchFree {signature : FrozenSig}
    {context : Context} {expression : Expr} {target : Ty}
    (typing : HasTy signature context expression target)
    (hfree : matchFree expression = true) :
    ExprDeriv signature context expression target :=
  (coherent_of_matchFree typing hfree).toExprDeriv

mutual

/-- Damas–Milner typable expressions never contain match constructs. -/
theorem matchFree_of_dm :
    ∀ {context : DM.SCtx} {expression : Expr} {target : DM.STy},
      DM.HasTy context expression target → matchFree expression = true
  | _, _, _, .var _ _ => rfl
  | _, _, _, .lam bodyTyping => by
      simp only [matchFree]
      exact matchFree_of_dm bodyTyping
  | _, _, _, .app functionTyping argumentTyping => by
      simp only [matchFree, Bool.and_eq_true]
      exact ⟨matchFree_of_dm functionTyping, matchFree_of_dm argumentTyping⟩
  | _, _, _, .letE valueTyping bodyTyping => by
      simp only [matchFree, Bool.and_eq_true]
      exact ⟨matchFree_of_dm valueTyping, matchFree_of_dm bodyTyping⟩
  | _, _, _, .fixE _ _ bodyTyping => by
      simp only [matchFree]
      exact matchFree_of_dm bodyTyping
  | _, _, _, .lit => rfl
  | _, _, _, .tuple typings => by
      simp only [matchFree]
      exact matchFreeList_of_dm typings

/-- List form of `matchFree_of_dm`. -/
theorem matchFreeList_of_dm :
    ∀ {context : DM.SCtx} {expressions : List Expr} {targets : List DM.STy},
      DM.HasTys context expressions targets →
        matchFreeList expressions = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons head tail => by
      simp only [matchFreeList, Bool.and_eq_true]
      exact ⟨matchFree_of_dm head, matchFreeList_of_dm tail⟩

end

/-- Every Damas–Milner typing embeds into the coherent judgment: the
declarative half of the staged DM acceptance goal.  The algorithmic half —
public inference succeeding on these programs — remains open. -/
theorem dm_coherent {signature : FrozenSig} (sigFtv : signature.ftv = [])
    {context : DM.SCtx} {expression : Expr} {target : DM.STy}
    (typing : DM.HasTy context expression target) :
    CoherentExpr signature (DM.SCtx.emb context) expression target.emb :=
  coherent_of_matchFree (DM.HasTy.emb sigFtv typing)
    (matchFree_of_dm typing)

/-! ## The annotation-freeness goal -/

/--
The top-level project goal, stated as a named proposition only: closed
declaratively typed programs are accepted by public executable inference
without any annotation.  The core syntax has no annotation form, so this
acceptance completeness is the precise meaning of annotation-freeness.

The proposition is deliberately not asserted: it is open.  The staged path
runs through Damas–Milner algorithmic acceptance, fragment-restricted
completeness over this module's coherent judgment (raw-head-visible lifts,
freeze-compatible capability instances), and finally the removal of the
selector's raw-head blind spot via cut-indexed coercion events.  The
mechanized principality counterexample is compatible with this goal: it
refutes substitution-only recovery of every typing from the inferred result,
not acceptance itself.
-/
def AnnotationFree : Prop :=
  ∀ (signature : FrozenSig) (expression : Expr) (target : Ty),
    HasTy signature [] expression target →
    Inference.inferenceSucceeds signature [] expression = true

end Coherent
end TypePM
