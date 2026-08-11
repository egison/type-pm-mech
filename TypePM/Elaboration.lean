import TypePM.Source

/-!
# Explicit coercion plans

The internal `RuntimeTyping` certificate keeps only the terminal semantic
effect of coercion.  This module separately records the executable raw solver
evidence used by reconstruction as an explicit outer coercion plan.

`SynthHead` records one non-coercion certificate rule at
the root, while `CoercionPlan` records the (possibly empty) outer coercion
spine explicitly.  Erasing a plan yields `RuntimeTyping`; the converse is not
claimed because semantic runtime evidence intentionally forgets solver
provenance.

The premises of `SynthHead` intentionally remain `RuntimeTyping` certificates here.
Thus this is the root factorization consumed by the recursive core
factorization in `TypePM.CoreTyping` and the mutual coherent reconstruction in
`TypePM.CoherentTyping`.
-/

namespace TypePM
namespace Elaboration

/-- A runtime certificate whose root rule synthesizes a type rather than
applying an implicit matcher/slot coercion.  Recursive premises remain
`RuntimeTyping`; later core reconstruction can refine them independently. -/
inductive SynthHead (signature : FrozenSig) : Context -> Expr -> Ty -> Prop where
  | var {context name scheme target} :
      context.find? name = some scheme ->
      scheme.ValueFlowInst target ->
      SynthHead signature context (.var name) target
  | lam {context name body domain codomain} :
      RuntimeTyping signature ((name, NamedScheme.mono domain) :: context) body codomain ->
      SynthHead signature context (.lam name body) (.fn domain codomain)
  | app {context function argument domain codomain} :
      RuntimeTyping signature context function (.fn domain codomain) ->
      RuntimeTyping signature context argument domain ->
      SynthHead signature context (.app function argument) codomain
  | letE {context name value body valueTy bodyTy} :
      RuntimeTyping signature context value valueTy ->
      RuntimeTyping signature
        ((name, signature.generalize context valueTy) :: context) body bodyTy ->
      SynthHead signature context (.letE name value body) bodyTy
  | fixE {context self argument body domain codomain} :
      self ≠ argument ->
      DirectSelf.Holds self body ->
      RuntimeTyping signature
        ((argument, NamedScheme.mono domain) ::
          (self, NamedScheme.mono (.fn domain codomain)) :: context)
        body codomain ->
      SynthHead signature context (.fix self argument body)
        (.fn domain codomain)
  | lit {context value} :
      SynthHead signature context (.lit value) .int
  | tuple {context expressions targets} :
      ExprsTy signature context expressions targets ->
      SynthHead signature context (.tuple expressions) (.prod targets)
  | ctor {context name expressions targets result scheme} :
      signature.findDataCtor name = some scheme ->
      scheme.Inst targets result ->
      ExprsTy signature context expressions targets ->
      SynthHead signature context (.ctor name expressions) result
  | prim {context op expressions targets result scheme} :
      signature.findPrimitive op = some scheme ->
      scheme.Inst targets result ->
      ExprsTy signature context expressions targets ->
      SynthHead signature context (.prim op expressions) result
  | something {context target} :
      SynthHead signature context .something (.matcher .any target)
  | matchAll
      {prevailing context target matcher pattern body targetTy patternCap
       bindings result} :
      RuntimeTyping signature context target targetTy ->
      ResolvedPatternTy signature prevailing context [] [] pattern
        patternCap targetTy bindings ->
      RuntimeTyping signature context matcher (.slot patternCap targetTy) ->
      RuntimeTyping signature (bindings.toContext ++ context) body result ->
      SynthHead signature context (.matchAll target matcher pattern body)
        (Ty.listT result)
  | matcher {context clauses target capability evidence} :
      ResolvedClausesTy signature context clauses capability target evidence ->
      Shape.inferShape signature.observability evidence = some capability ->
      CatchAllLast clauses ->
      ArmExhaustive signature clauses target ->
      PPBindNodup clauses ->
      ArmBindNodup clauses ->
      CoverageOK signature.toMatcherSig clauses capability ->
      SynthHead signature context (.matcher clauses)
        (.matcher capability target)

/-- Forget the root synthesis boundary and recover the existing surface
typing judgment. -/
theorem SynthHead.toRuntimeTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : SynthHead signature context expression target) :
    RuntimeTyping signature context expression target := by
  cases typing with
  | var lookup instanceTyping => exact .var lookup instanceTyping
  | lam bodyTyping => exact .lam bodyTyping
  | app functionTyping argumentTyping =>
      exact .app functionTyping argumentTyping
  | letE valueTyping bodyTyping => exact .letE valueTyping bodyTyping
  | fixE distinct direct bodyTyping =>
      exact .fixE distinct direct bodyTyping
  | lit => exact .lit
  | tuple expressionsTyping => exact .tuple expressionsTyping
  | ctor lookup instanceTyping expressionsTyping =>
      exact .ctor lookup instanceTyping expressionsTyping
  | prim lookup instanceTyping expressionsTyping =>
      exact .prim lookup instanceTyping expressionsTyping
  | something => exact .something
  | matchAll targetTyping patternTyping matcherTyping bodyTyping =>
      exact .matchAll targetTyping patternTyping matcherTyping bodyTyping
  | matcher clausesTyping shape catchAll exhaustive ppNodup armNodup coverage =>
      exact .matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
        coverage

/-- Explicit evidence for one surface coercion spine.  The indices expose the
pre-coercion and post-coercion types, so head-changing conversions are no
longer confused with ordinary substitution instances. -/
inductive CoercionPlan (signature : FrozenSig) :
    Context -> Expr -> Ty -> Ty -> Prop where
  | refl {context expression target} :
      CoercionPlan signature context expression target target
  | matcherToSlot
      {context expression producerCap producerTarget consumerCap consumerTarget
       bindings C T post} :
      MatcherToSlotRawCert producerCap consumerCap producerTarget
        consumerTarget bindings C T ->
      VariablePost post ->
      CoercionPlan signature context expression
        (.matcher ((producerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply producerTarget)))
        (.slot ((consumerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply consumerTarget)))
  | checkSlotToSlot
      {context expression sourceCap sourceTarget requestedCap requestedTarget C T
       post} :
      SlotToSlotRawCert sourceCap requestedCap sourceTarget requestedTarget
        C T ->
      VariablePost post ->
      CoercionPlan signature context expression
        (.slot ((sourceCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply sourceTarget)))
        (.slot ((requestedCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply requestedTarget)))
  | productMatcher {context expression} {duals : List Dual} :
      CoercionPlan signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target))
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  | slotTuple {context expression} {duals : List Dual} :
      CoercionPlan signature context expression
        (.prod (duals.map fun dual => .slot dual.cap dual.target))
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  | trans {context expression source middle target} :
      CoercionPlan signature context expression source middle ->
      CoercionPlan signature context expression middle target ->
      CoercionPlan signature context expression source target

/-- Bidirectional checking at the surface/core boundary: first synthesize a
pre-coercion root type, then check the requested surface view by an explicit
coercion plan. -/
def CheckHead (signature : FrozenSig) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ source,
    SynthHead signature context expression source ∧
    CoercionPlan signature context expression source target

/-- Replay explicit coercion evidence on top of a pre-coercion typing. -/
theorem CoercionPlan.toRuntimeTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : CoercionPlan signature context expression source target)
    (typing : RuntimeTyping signature context expression source) :
    RuntimeTyping signature context expression target := by
  induction plan with
  | refl => exact typing
  | matcherToSlot raw post =>
      rw [← raw.postTargetEquality _]
      exact .coerceMatcherToSlot typing (raw.postCapabilityDemand _)
  | checkSlotToSlot raw post =>
      rename_i sourceCap sourceTarget requestedCap requestedTarget C T postSubst
      change RuntimeTyping signature context expression
        (postSubst.apply ((Subst.mk C T).apply
          (.slot requestedCap requestedTarget)))
      change RuntimeTyping signature context expression
        (postSubst.apply ((Subst.mk C T).apply
          (.slot sourceCap sourceTarget))) at typing
      exact raw.postSlotEquality postSubst ▸ typing
  | productMatcher => exact .coerceProductMatcher typing
  | slotTuple => exact .coerceSlotTuple typing
  | trans _ _ firstIH secondIH => exact secondIH (firstIH typing)


/-- Checking evidence erases to the existing surface judgment. -/
theorem CheckHead.toRuntimeTyping
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (checking : CheckHead signature context expression target) :
    RuntimeTyping signature context expression target := by
  rcases checking with ⟨source, synthesis, plan⟩
  exact plan.toRuntimeTyping synthesis.toRuntimeTyping

/-- Explicit checking evidence soundly erases to the semantic runtime
certificate. -/
theorem checkHead_sound
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty} (checking : CheckHead signature context expression target) :
    RuntimeTyping signature context expression target :=
  checking.toRuntimeTyping

end Elaboration
end TypePM
