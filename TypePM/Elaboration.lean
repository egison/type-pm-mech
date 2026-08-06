import TypePM.Source

/-!
# Surface elaboration and explicit coercion plans

The source judgment `HasTy` deliberately includes the implicit matcher/slot
coercions used by the surface language.  That makes it the right boundary for
dynamic safety, but not the right judgment for an ordinary principal-type
statement: a single expression may have derivable types with different head
constructors.

This module starts the syntax-directed elaboration layer without changing the
existing safety boundary.  `SynthHead` records one non-coercion source rule at
the root, while `CoercionPlan` records the (possibly empty) outer coercion
spine explicitly.  `HasTy.factorHead` proves that every surface typing admits
this decomposition.

The premises of `SynthHead` intentionally remain surface judgments for now.
Thus this is the root factorization needed by the future mutually recursive
core judgment, not yet a claim of full core principality.  Keeping that
distinction explicit prevents the negative result in
`PrincipalityCounterexample` from being hidden by terminology.
-/

namespace TypePM
namespace Elaboration

/-- A source typing whose root rule synthesizes a type rather than applying an
implicit matcher/slot coercion.  Recursive premises remain the existing
surface judgments; later core elaboration can refine them independently. -/
inductive SynthHead (signature : FrozenSig) : Context -> Expr -> Ty -> Prop where
  | var {context name scheme target} :
      context.find? name = some scheme ->
      scheme.ValueFlowInst target ->
      SynthHead signature context (.var name) target
  | lam {context name body domain codomain} :
      HasTy signature ((name, Scheme.mono domain) :: context) body codomain ->
      SynthHead signature context (.lam name body) (.fn domain codomain)
  | app {context function argument domain codomain} :
      HasTy signature context function (.fn domain codomain) ->
      HasTy signature context argument domain ->
      SynthHead signature context (.app function argument) codomain
  | letE {context name value body valueTy bodyTy} :
      HasTy signature context value valueTy ->
      HasTy signature
        ((name, signature.generalize context valueTy) :: context) body bodyTy ->
      SynthHead signature context (.letE name value body) bodyTy
  | fixE {context self argument body domain codomain} :
      self ≠ argument ->
      DirectSelf.Holds self body ->
      HasTy signature
        ((argument, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: context)
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
      HasTy signature context target targetTy ->
      ResolvedPatternTy signature prevailing context [] [] pattern
        patternCap targetTy bindings ->
      HasTy signature context matcher (.slot patternCap targetTy) ->
      HasTy signature (bindings.toContext ++ context) body result ->
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
theorem SynthHead.toHasTy
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : SynthHead signature context expression target) :
    HasTy signature context expression target := by
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
theorem CoercionPlan.toHasTy
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {source target : Ty}
    (plan : CoercionPlan signature context expression source target)
    (typing : HasTy signature context expression source) :
    HasTy signature context expression target := by
  induction plan with
  | refl => exact typing
  | matcherToSlot raw post =>
      exact .coerceMatcherToSlot typing raw post
  | checkSlotToSlot raw post =>
      exact .checkSlotToSlot typing raw post
  | productMatcher => exact .coerceProductMatcher typing
  | slotTuple => exact .coerceSlotTuple typing
  | trans _ _ firstIH secondIH => exact secondIH (firstIH typing)

/-- Every surface typing is a non-coercion root typing followed by an explicit
coercion plan.  This is the first factorization boundary used by the planned
principal-core theorem. -/
theorem HasTy.factorHead
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : HasTy signature context expression target) :
    ∃ source,
      SynthHead signature context expression source ∧
      CoercionPlan signature context expression source target := by
  apply HasTy.rec
    (motive_1 := fun context expression target _ =>
      ∃ source,
        SynthHead signature context expression source ∧
        CoercionPlan signature context expression source target)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ => True)
    (t := typing)
  all_goals intros
  all_goals
    first
    | trivial
    | (refine ⟨_, ?_, .refl⟩; constructor <;> assumption)
    | (rcases ‹∃ source, SynthHead _ _ _ source ∧
          CoercionPlan _ _ _ source _› with ⟨source, synthesis, plan⟩
       refine ⟨source, synthesis, .trans plan ?_⟩
       first
       | exact .matcherToSlot (by assumption) (by assumption)
       | exact .checkSlotToSlot (by assumption) (by assumption)
       | exact .productMatcher
       | exact .slotTuple)

/-- Package surface factorization as the root checking judgment. -/
theorem HasTy.toCheckHead
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : HasTy signature context expression target) :
    CheckHead signature context expression target := by
  rcases HasTy.factorHead typing with ⟨source, synthesis, plan⟩
  exact ⟨source, synthesis, plan⟩

/-- Replaying the factorization obtained from a surface derivation recovers a
surface derivation at the original target. -/
theorem HasTy.factorHead_sound
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target source : Ty}
    (synthesis : SynthHead signature context expression source)
    (plan : CoercionPlan signature context expression source target) :
    HasTy signature context expression target :=
  plan.toHasTy synthesis.toHasTy

/-- Checking evidence erases to the existing surface judgment. -/
theorem CheckHead.toHasTy
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (checking : CheckHead signature context expression target) :
    HasTy signature context expression target := by
  rcases checking with ⟨source, synthesis, plan⟩
  exact plan.toHasTy synthesis.toHasTy

/-- The current surface relation is exactly a synthesized root followed by an
explicit outer coercion spine. -/
theorem checkHead_iff_surface
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty} :
    CheckHead signature context expression target ↔
      HasTy signature context expression target :=
  ⟨CheckHead.toHasTy, HasTy.toCheckHead⟩

end Elaboration
end TypePM
