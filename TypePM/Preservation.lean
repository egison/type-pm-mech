import TypePM.Dynamic

/-!
# Preservation support for the two-sorted core

This module collects the concrete frozen-signature obligations, terminal
source-typing elimination, and pointwise list lemma used by the complete
mutual `Eval`/`PPM`/`MAtom`/`Step`/`Search` preservation proof in `Safety`.

The only signature-specific dynamic premise is primitive delta preservation.
Source coercions use their cumulative-substitution-normalized premise, so
the terminal eliminator below recurses under the same runtime context.
-/

namespace TypePM

/-! ## Concrete signature obligations -/

/--
The executable core checker succeeds only when it finds a genuinely
irrefutable variable or wildcard arm; either pattern matches every value.
-/
theorem basicArmExhaustive_success
    {patterns : List DPat} {target : Ty} {value : Value}
    (checked : basicArmExhaustive patterns target = true) :
    ∃ pattern, pattern ∈ patterns ∧
      ∃ environment, pdMatch pattern value = some environment := by
  induction patterns with
  | nil =>
      simp [basicArmExhaustive] at checked
  | cons pattern patterns induction =>
      cases pattern with
      | var name =>
          exact ⟨.var name, by simp, [(name, value)], rfl⟩
      | wild =>
          exact ⟨.wild, by simp, [], rfl⟩
      | ctor name children =>
          have tailChecked : basicArmExhaustive patterns target = true := by
            simpa [basicArmExhaustive, DPat.isIrrefutable] using checked
          obtain ⟨found, member, environment, matched⟩ := induction tailChecked
          exact ⟨found, by simp [member], environment, matched⟩
      | tuple children =>
          have tailChecked : basicArmExhaustive patterns target = true := by
            simpa [basicArmExhaustive, DPat.isIrrefutable] using checked
          obtain ⟨found, member, environment, matched⟩ := induction tailChecked
          exact ⟨found, by simp [member], environment, matched⟩

/-! ## Canonical primitive schemes -/

/-- The canonical scheme of the `append` decomposition primitive. -/
def appendCanonicalScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [.data "List" [.var 0], .data "List" [.var 0]]
  result := .data "List" [.var 0]

/-- The canonical scheme of the `splits` decomposition primitive. -/
def splitsCanonicalScheme : CtorScheme where
  capBinders := []
  tyBinders := [0]
  args := [.data "List" [.var 0]]
  result := .data "List"
    [.prod [.data "List" [.var 0], .data "List" [.var 0]]]

/-- The canonical scheme demanded for each declared primitive operation. -/
def primCanonicalScheme : PrimOp → CtorScheme
  | .append => appendCanonicalScheme
  | .splits => splitsCanonicalScheme

/-- Public well-formedness conditions for a frozen signature.  Closedness
supports demand-directed state erasure; the remaining fields are consumed by the dynamic
kernel. -/
structure FrozenSigWF (signature : FrozenSig) : Prop where
  /-- Public frozen signatures contain no metavariables outside scheme
  binders; all polymorphism is represented by the binders themselves. -/
  schemesClosed : signature.SchemesClosed
  /-- The distinguished `List` constructors have their concrete core shape. -/
  listSigWF : ListSigWF signature
  /-- Pattern-function lookup is a finite map with no shadowed names. -/
  patternFunNamesNodup :
    (signature.patternFuns.map Prod.fst).Nodup
  /-- A declared data constructor always produces a canonical data root. -/
  dataResult :
    ∀ {name scheme targets result},
      signature.findDataCtor name = some scheme →
      scheme.Inst targets result →
      ∃ former arguments, result = .data former arguments
  /-- A constructor result determines the instantiated field targets. -/
  dataInstArgsUnique :
    ∀ {name scheme leftTargets rightTargets result},
      signature.findDataCtor name = some scheme →
      scheme.Inst leftTargets result →
      scheme.Inst rightTargets result →
      leftTargets = rightTargets
  /-- A pattern-constructor result determines its instantiated field targets. -/
  patternInstArgsUnique :
    ∀ {name entry leftTargets rightTargets result},
      signature.findPatternCtor name = some entry →
      entry.Inst leftTargets result →
      entry.Inst rightTargets result →
      leftTargets = rightTargets
  /-- A pattern-constructor capability result determines its child caps. -/
  patternCapArgsUnique :
    ∀ {name entry leftCaps rightCaps result},
      signature.findPatternCtor name = some entry →
      entry.CapCompatible leftCaps result →
      entry.CapCompatible rightCaps result →
      leftCaps = rightCaps
  /--
  One-way compatibility of constructor results descends pointwise to their
  field capabilities.  This is the demand-aware replacement for using
  `patternCapArgsUnique` when a consumer contains an explicit `any`.
  -/
  patternCapDemands :
    ∀ {name entry producerCaps consumerCaps producerResult consumerResult},
      signature.findPatternCtor name = some entry →
      entry.CapCompatible producerCaps producerResult →
      entry.CapCompatible consumerCaps consumerResult →
      CapabilityDemand producerResult consumerResult →
      CapabilityDemands producerCaps consumerCaps
  /--
  Every compatible pattern-constructor instance has a canonical data-former
  capability and occurs at its exact arity in the frozen coverage index for
  that former.
  This is the coherence condition connecting `patternCtors` with the otherwise
  independent `constructorsByFormer` table.
  -/
  patternCtorIndexed :
    ∀ {name entry childCaps capability},
      signature.findPatternCtor name = some entry →
      entry.CapCompatible childCaps capability →
      ∃ former arguments constructors,
        capability = .con former arguments ∧
        signature.toMatcherSig.constructorsFor? former = some constructors ∧
        (name, childCaps.length) ∈ constructors
  /-- The frozen primitive delta implementation preserves its declared type. -/
  primEvalTyped :
    ∀ {op scheme values targets result value},
      signature.findPrimitive op = some scheme →
      scheme.Inst targets result →
      ValueTys signature values targets →
      primEval op values = some value →
      ValueTy signature value result
  /-- The core uses exactly the conservative executable checker. -/
  armExhaustiveBasic : signature.armExhaustive = basicArmExhaustive
  /-- Only the canonical `nil`/`cons` declarations instantiate to a list
  result, so every value typed at `Ty.listT` is a decodable `nil`/`cons`
  chain.  `dataResult` alone still admits foreign constructors targeting
  the `List` former; this field closes that gap for decode totality. -/
  listCtorsExclusive :
    ∀ {name scheme targets element},
      signature.findDataCtor name = some scheme →
      scheme.Inst targets (Ty.listT element) →
      (name = "nil" ∧ targets = []) ∨
      (name = "cons" ∧ targets = [element, Ty.listT element])
  /-- Every declared primitive uses exactly its canonical scheme; primitive
  delta totality on typed arguments follows from the canonical shapes. -/
  primitivesCanonical :
    ∀ {op scheme},
      signature.findPrimitive op = some scheme →
      scheme = primCanonicalScheme op

/-- A positive frozen checker result identifies a successful data arm. -/
theorem FrozenSigWF.armExhaustiveSuccess
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {patterns : List DPat} {target : Ty} {value : Value}
    (checked : signature.armExhaustive patterns target = true) :
    ∃ pattern, pattern ∈ patterns ∧
      ∃ environment, pdMatch pattern value = some environment := by
  rw [signatureWF.armExhaustiveBasic] at checked
  exact basicArmExhaustive_success checked

/-! ## Canonical products and source coercion closure -/

/-- A value at an ordinary product type is an actual tuple with typed fields. -/
theorem ValueTy.product_inversion
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {value : Value} {targets : List Ty}
    (typing : ValueTy signature value (.prod targets)) :
    ∃ values,
      value = .tuple values ∧ ValueTys signature values targets := by
  refine ValueTy.rec
    (motive_1 := fun actualValue actualTarget _ =>
      ∀ requestedTargets, actualTarget = .prod requestedTargets →
        ∃ values,
          actualValue = .tuple values ∧
            ValueTys signature values requestedTargets)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    typing targets rfl
  · intro literal requestedTargets equality
    cases equality
  · intro name scheme values ctorTargets result hfind hinst valuesTyped _
      requestedTargets targetEquality
    obtain ⟨former, arguments, resultEquality⟩ :=
      signatureWF.dataResult hfind hinst
    rw [resultEquality] at targetEquality
    cases targetEquality
  · intro values tupleTargets valuesTyped _ requestedTargets targetEquality
    cases targetEquality
    exact ⟨values, rfl, valuesTyped⟩
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · trivial
  · intros
    trivial

/-!
`TypingInvariant` is a mutually inductive proposition, so a separate proof-relevant
predicate records the non-coercion cases without eliminating source evidence
into data.  Its constructors are exactly the terminal source rules.
-/
namespace TypingInvariant

inductive Terminal {signature : FrozenSig} :
    {context : Context} → {expression : Expr} → {target : Ty} →
    TypingInvariant signature context expression target → Prop where
  | var {context : Context} {name : String} {scheme : Scheme} {target : Ty}
      (hfind : Context.find? context name = some scheme)
      (hinst : scheme.ValueFlowInst target) :
      Terminal (TypingInvariant.var hfind hinst)
  | lam {context : Context} {name : String} {body : Expr}
      {domain codomain : Ty}
      (bodyTyping :
        TypingInvariant signature ((name, Scheme.mono domain) :: context) body codomain) :
      Terminal (TypingInvariant.lam bodyTyping)
  | app {context : Context} {function argument : Expr}
      {domain codomain : Ty}
      (functionTyping :
        TypingInvariant signature context function (.fn domain codomain))
      (argumentTyping : TypingInvariant signature context argument domain) :
      Terminal (TypingInvariant.app functionTyping argumentTyping)
  | letE {context : Context} {name : String} {value body : Expr}
      {valueTy bodyTy : Ty}
      (valueTyping : TypingInvariant signature context value valueTy)
      (bodyTyping :
        TypingInvariant signature
          ((name, signature.generalize context valueTy) :: context)
          body bodyTy) :
      Terminal (TypingInvariant.letE valueTyping bodyTyping)
  | fixE {context : Context} {self argument : String} {body : Expr}
      {domain codomain : Ty}
      (distinct : self ≠ argument)
      (direct : DirectSelf.Holds self body)
      (bodyTyping :
        TypingInvariant signature
          ((argument, Scheme.mono domain) ::
            (self, Scheme.mono (.fn domain codomain)) :: context)
          body codomain) :
      Terminal (TypingInvariant.fixE distinct direct bodyTyping)
  | lit {context : Context} {value : Int} :
      Terminal (@TypingInvariant.lit signature context value)
  | tuple {context : Context} {expressions : List Expr} {targets : List Ty}
      (expressionsTyping :
        ExprsTy signature context expressions targets) :
      Terminal (TypingInvariant.tuple expressionsTyping)
  | ctor {context : Context} {name : String} {expressions : List Expr}
      {targets : List Ty} {result : Ty} {scheme : CtorScheme}
      (hfind : signature.findDataCtor name = some scheme)
      (hinst : scheme.Inst targets result)
      (expressionsTyping :
        ExprsTy signature context expressions targets) :
      Terminal (TypingInvariant.ctor hfind hinst expressionsTyping)
  | prim {context : Context} {op : PrimOp} {expressions : List Expr}
      {targets : List Ty} {result : Ty} {scheme : CtorScheme}
      (hfind : signature.findPrimitive op = some scheme)
      (hinst : scheme.Inst targets result)
      (expressionsTyping :
        ExprsTy signature context expressions targets) :
      Terminal (TypingInvariant.prim hfind hinst expressionsTyping)
  | something {context : Context} {target : Ty} :
      Terminal (@TypingInvariant.something signature context target)
  | matchAll
      {prevailing : Subst} {context : Context} {target matcher body : Expr}
      {pattern : Pattern} {targetTy result : Ty} {patternCap : Cap}
      {bindings : MonoCtx}
      (targetTyping : TypingInvariant signature context target targetTy)
      (patternTyping :
        ResolvedPatternTy signature prevailing context [] [] pattern
          patternCap targetTy bindings)
      (matcherTyping :
        TypingInvariant signature context matcher (.slot patternCap targetTy))
      (bodyTyping :
        TypingInvariant signature (bindings.toContext ++ context) body result) :
      Terminal
        (TypingInvariant.matchAll targetTyping patternTyping matcherTyping bodyTyping)
  | matcher {context : Context} {clauses : List Clause} {target : Ty}
      {capability : Cap} {evidence : List Shape.Evidence}
      (clausesTyping :
        ResolvedClausesTy signature context clauses capability target evidence)
      (shape :
        Shape.inferShape signature.observability evidence = some capability)
      (catchAll : CatchAllLast clauses)
      (exhaustive : ArmExhaustive signature clauses target)
      (ppNodup : PPBindNodup clauses)
      (armNodup : ArmBindNodup clauses)
      (coverage : CoverageOK signature.toMatcherSig clauses capability) :
      Terminal
        (TypingInvariant.matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
          coverage)
end TypingInvariant

/--
Lift a terminal typing-invariant result through the unary source coercions.

The recursive calls are on strict premise derivations of `TypingInvariant`.  Source
coercion premises have already been transported by their retained cumulative
substitution, so every recursive call uses the unchanged environment typing.
-/
def preserveSourceCoercions
    {signature : FrozenSig}
    (signatureWF : FrozenSigWF signature)
    {environment : Env} {expression : Expr} {value : Value}
    {context : Context} {target : Ty}
    (typing : TypingInvariant signature context expression target)
    (environmentTyping : EnvTyped signature context environment)
    (terminal :
      ∀ {terminalContext terminalTarget}
        (terminalTyping :
          TypingInvariant signature terminalContext expression terminalTarget),
        terminalTyping.Terminal →
        EnvTyped signature terminalContext environment →
        ValueTy signature value terminalTarget) :
    ValueTy signature value target :=
  match typing with
  | .coerceMatcherToSlot inner demand =>
      ValueTy.matcherToSlot
        (preserveSourceCoercions signatureWF inner environmentTyping terminal)
        demand
  | .coerceProductMatcher inner =>
      let innerValue :=
        preserveSourceCoercions signatureWF inner
          environmentTyping terminal
      match ValueTy.product_inversion signatureWF innerValue with
      | ⟨_values, equality, valuesTyped⟩ =>
          equality.symm ▸ ValueTy.matcherProduct valuesTyped
  | .coerceSlotTuple inner =>
      let innerValue :=
        preserveSourceCoercions signatureWF inner
          environmentTyping terminal
      match ValueTy.product_inversion signatureWF innerValue with
      | ⟨_values, equality, valuesTyped⟩ =>
          equality.symm ▸ ValueTy.slotProduct valuesTyped
  | terminalTyping@(.var hfind hinst) =>
      terminal terminalTyping (.var hfind hinst) environmentTyping
  | terminalTyping@(.lam bodyTyping) =>
      terminal terminalTyping (.lam bodyTyping) environmentTyping
  | terminalTyping@(.app functionTyping argumentTyping) =>
      terminal terminalTyping (.app functionTyping argumentTyping)
        environmentTyping
  | terminalTyping@(.letE valueTyping bodyTyping) =>
      terminal terminalTyping (.letE valueTyping bodyTyping) environmentTyping
  | terminalTyping@(.fixE distinct direct bodyTyping) =>
      terminal terminalTyping (.fixE distinct direct bodyTyping)
        environmentTyping
  | terminalTyping@(.lit) =>
      terminal terminalTyping .lit environmentTyping
  | terminalTyping@(.tuple expressionsTyping) =>
      terminal terminalTyping (.tuple expressionsTyping) environmentTyping
  | terminalTyping@(.ctor hfind hinst expressionsTyping) =>
      terminal terminalTyping (.ctor hfind hinst expressionsTyping)
        environmentTyping
  | terminalTyping@(.prim hfind hinst expressionsTyping) =>
      terminal terminalTyping (.prim hfind hinst expressionsTyping)
        environmentTyping
  | terminalTyping@(.something) =>
      terminal terminalTyping .something environmentTyping
  | terminalTyping@(.matchAll targetTyping patternTyping matcherTyping bodyTyping) =>
      terminal terminalTyping
        (.matchAll targetTyping patternTyping matcherTyping bodyTyping)
        environmentTyping
  | terminalTyping@(.matcher clausesTyping shape catchAll exhaustive ppNodup
      armNodup coverage) =>
      terminal terminalTyping
        (.matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
          coverage)
        environmentTyping
/-! ## Pointwise evaluated expression lists -/

/--
Turn source list typing into runtime list typing using the pointwise induction
hypotheses supplied by `Eval.rec`.
-/
def valueTys_of_evalZip
    {signature : FrozenSig} {context : Context}
    {expressions : List Expr} {targets : List Ty}
    (sourceTyping : ExprsTy signature context expressions targets) :
    ∀ {values : List Value},
      expressions.length = values.length →
      (∀ pair ∈ expressions.zip values,
        ∀ target,
          TypingInvariant signature context pair.1 target →
          ValueTy signature pair.2 target) →
      ValueTys signature values targets
  | [], hlength, _ => by
      cases sourceTyping with
      | nil => exact ValueTys.nil
      | cons => simp at hlength
  | value :: values, hlength, pointwise => by
      cases sourceTyping with
      | nil => simp at hlength
      | cons headTyping tailTyping =>
          refine ValueTys.cons
            (pointwise _ (by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inl rfl) _ headTyping) ?_
          apply valueTys_of_evalZip tailTyping
          · simpa using hlength
          · intro pair hmember target targetTyping
            exact pointwise pair
              (by
                simp only [List.zip_cons_cons, List.mem_cons]
                exact Or.inr hmember)
              target targetTyping

end TypePM
