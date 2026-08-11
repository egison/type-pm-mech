import TypePM.Source
import TypePM.Semantics

/-!
# Concrete runtime typing for the two-sorted core

This module connects the type-erased operational objects in
`TypePM.Semantics` directly to the coverage-required two-sorted source
calculus in `TypePM.Source`.  No abstract runtime specification, oracle, or
claimed type safety theorem occurs here.

A runtime matcher literal retains an internal state-free certificate

```text
RuntimeTyping signature context (.matcher clauses) (.matcher capability target)
```

for exactly its captured clause list.  Consequently matcher inversion recovers
the concrete clause evidence and `CoverageOK` required by T-MATCHER.
-/

namespace TypePM

/-! ## Concrete built-in list signature -/

/-- Exact frozen declarations used by the concrete `nil`/`cons` encoding. -/
structure ListSigWF (signature : FrozenSig) : Prop where
  nilDeclared : ∃ scheme,
    signature.findDataCtor "nil" = some scheme ∧
    ∀ target, scheme.Inst [] (Ty.listT target)
  consDeclared : ∃ scheme,
    signature.findDataCtor "cons" = some scheme ∧
    ∀ target,
      scheme.Inst [target, Ty.listT target] (Ty.listT target)

/-! ## Runtime matcher cursors -/

/--
`current` is a runtime suffix/cursor of the original source matcher literal.
Primitive-pattern failure drops a whole head clause; data-pattern failure
drops only the head arm of the current head clause.
-/
inductive MatcherCursor : List Clause → List Clause → Prop where
  | refl {clauses} : MatcherCursor clauses clauses
  | nextClause {pp next arms clauses original} :
      MatcherCursor (.mk pp next arms :: clauses) original →
      MatcherCursor clauses original
  | nextArm {pp next arm arms clauses original} :
      MatcherCursor (.mk pp next (arm :: arms) :: clauses) original →
      MatcherCursor (.mk pp next arms :: clauses) original

/-! ## Runtime values -/

mutual

/-- Coverage-preserving runtime value typing for the concrete two-sorted source core. -/
inductive ValueTy (signature : FrozenSig) : Value → Ty → Prop where
  | lit {value} :
      ValueTy signature (.lit value) .int
  | ctor {name scheme values targets result} :
      signature.findDataCtor name = some scheme →
      scheme.Inst targets result →
      ValueTys signature values targets →
      ValueTy signature (.ctor name values) result
  | tuple {values targets} :
      ValueTys signature values targets →
      ValueTy signature (.tuple values) (.prod targets)
  | closure {self environment parameter body domain codomain}
      (context : NamedContext) :
      (∀ name value,
        Env.find? environment name = some value →
          ∃ scheme, NamedContext.find? context name = some scheme) →
      (∀ name value scheme target,
        Env.find? environment name = some value →
        NamedContext.find? context name = some scheme →
        scheme.ValueFlowInst target →
        ValueTy signature value target) →
      (self = none →
        RuntimeTyping signature
          ((parameter, NamedScheme.mono domain) :: context) body codomain) →
      (∀ name, self = some name →
        RuntimeTyping signature
          ((parameter, NamedScheme.mono domain) ::
            (name, NamedScheme.mono (.fn domain codomain)) :: context)
          body codomain) →
      ValueTy signature (.closure self environment parameter body)
        (.fn domain codomain)
  | matcherLiteral {environment currentClauses originalClauses capability target}
      (context : NamedContext) :
      (∀ name value,
        Env.find? environment name = some value →
          ∃ scheme, NamedContext.find? context name = some scheme) →
      (∀ name value scheme instanceTarget,
        Env.find? environment name = some value →
        NamedContext.find? context name = some scheme →
        scheme.ValueFlowInst instanceTarget →
        ValueTy signature value instanceTarget) →
      RuntimeTyping signature context (.matcher originalClauses)
        (.matcher capability target) →
      MatcherCursor currentClauses originalClauses →
      ValueTy signature
        (.matcherV environment originalClauses currentClauses)
        (.matcher capability target)
  | something {target} :
      ValueTy signature .something (.matcher .any target)
  | matcherProduct {values} {duals : List Dual} :
      ValueTys signature values
        (duals.map fun dual => .matcher dual.cap dual.target) →
      ValueTy signature (.tuple values)
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  /-- State-erased matcher-to-slot evidence: dynamic safety needs only the
  terminal producer/consumer demand relation at one common target. -/
  | matcherToSlot
      {value producerCap consumerCap target} :
      ValueTy signature value
        (.matcher producerCap target) →
      CapabilityDemand producerCap consumerCap →
      ValueTy signature value
        (.slot consumerCap target)
  | slotProduct {values} {duals : List Dual} :
      ValueTys signature values
        (duals.map fun dual => .slot dual.cap dual.target) →
      ValueTy signature (.tuple values)
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- Pointwise runtime value typing with exact order and arity. -/
inductive ValueTys (signature : FrozenSig) : List Value → List Ty → Prop where
  | nil :
      ValueTys signature [] []
  | cons {value target values targets} :
      ValueTy signature value target →
      ValueTys signature values targets →
      ValueTys signature (value :: values) (target :: targets)

end

/-! ## Pristine runtime values -/

mutual

/--
No matcher cursor stored anywhere inside a runtime value has been advanced.
This is a state-boundary invariant: suffix cursors are used only internally
while deriving one `MAtom` reduction and never escape into successor states.
-/
inductive ValuePristine : Value → Prop where
  | lit {value} : ValuePristine (.lit value)
  | ctor {name values} :
      ValuesPristine values → ValuePristine (.ctor name values)
  | tuple {values} :
      ValuesPristine values → ValuePristine (.tuple values)
  | closure {self environment parameter body} :
      EnvPristine environment →
      ValuePristine (.closure self environment parameter body)
  | matcherLiteral {environment clauses} :
      EnvPristine environment →
      ValuePristine (.matcherV environment clauses clauses)
  | something : ValuePristine .something

/-- Pointwise pristine runtime values. -/
inductive ValuesPristine : List Value → Prop where
  | nil : ValuesPristine []
  | cons {value values} :
      ValuePristine value →
      ValuesPristine values →
      ValuesPristine (value :: values)

/-- Every value reachable from a runtime environment is pristine. -/
inductive EnvPristine : Env → Prop where
  | nil : EnvPristine []
  | cons {name value environment} :
      ValuePristine value →
      EnvPristine environment →
      EnvPristine ((name, value) :: environment)

end

/-! ## Runtime environments and matching substitutions -/

/--
The concrete source context types every lookup from a runtime environment at
all safe value-flow instances of the scheme found at the same name.  This is
exactly the relation consumed by source T-VAR; runtime lookup cannot select a
structurally stronger capability instance.
-/
def EnvTyped
    (signature : FrozenSig) (context : NamedContext) (environment : Env) : Prop :=
  ∀ name value, Env.find? environment name = some value →
    ∃ scheme,
      NamedContext.find? context name = some scheme ∧
      ∀ target,
        scheme.ValueFlowInst target →
        ValueTy signature value target

/--
A matching substitution has the reverse runtime order of its source binding
context, and every source binding resolves to a value of its declared target.
-/
def MatchSubstTyped
    (signature : FrozenSig) (bindings : MonoCtx)
    (substitution : MatchSubst) : Prop :=
  bindings.names.Nodup ∧
  bindings.names = (substitution.map Prod.fst).reverse ∧
  ∀ entry ∈ bindings,
    ∃ value,
      Env.find? substitution entry.1 = some value ∧
      ValueTy signature value entry.2

/-- Empty matching substitutions are typed by the empty binding context. -/
@[simp] theorem matchSubstTyped_nil (signature : FrozenSig) :
    MatchSubstTyped signature [] [] := by
  exact ⟨List.nodup_nil, rfl, fun entry hmember => by contradiction⟩

/-- Pointwise value typing preserves list arity. -/
theorem ValueTys.length
    {signature : FrozenSig} :
    ∀ {values : List Value} {targets : List Ty},
      ValueTys signature values targets →
      values.length = targets.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest =>
      congrArg Nat.succ (ValueTys.length rest)

/-! ## Environment lookup and extension -/

/-- Repackage the two environment premises stored by a closure or matcher. -/
theorem envTyped_of_parts
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    (domain : ∀ name value,
      Env.find? environment name = some value →
        ∃ scheme, NamedContext.find? context name = some scheme)
    (instances : ∀ name value scheme target,
      Env.find? environment name = some value →
      NamedContext.find? context name = some scheme →
      scheme.ValueFlowInst target →
      ValueTy signature value target) :
    EnvTyped signature context environment := by
  intro name value hfind
  obtain ⟨scheme, hscheme⟩ := domain name value hfind
  exact ⟨scheme, hscheme,
    fun target hinst =>
      instances name value scheme target hfind hscheme hinst⟩

/-- The domain half of a typed runtime environment. -/
theorem EnvTyped.domain
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    (typing : EnvTyped signature context environment)
    {name : String} {value : Value}
    (hfind : Env.find? environment name = some value) :
    ∃ scheme, NamedContext.find? context name = some scheme := by
  obtain ⟨scheme, hscheme, _⟩ := typing name value hfind
  exact ⟨scheme, hscheme⟩

/-- Lookup at a particular source-scheme instance. -/
theorem EnvTyped.lookup
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    (typing : EnvTyped signature context environment)
    {name : String} {value : Value} {scheme : NamedScheme} {target : Ty}
    (hvalue : Env.find? environment name = some value)
    (hscheme : NamedContext.find? context name = some scheme)
    (hinstance :
      scheme.ValueFlowInst target) :
    ValueTy signature value target := by
  obtain ⟨found, hfound, hvalues⟩ := typing name value hvalue
  have equality : scheme = found :=
    Option.some.inj (hscheme.symm.trans hfound)
  subst found
  exact hvalues target hinstance

/-- Extend a typed environment by a source scheme and all its safe instances. -/
theorem EnvTyped.consScheme
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    {name : String} {value : Value} {scheme : NamedScheme}
    (valueInstances :
      ∀ target,
        scheme.ValueFlowInst target →
        ValueTy signature value target)
    (typing : EnvTyped signature context environment) :
    EnvTyped signature ((name, scheme) :: context)
      ((name, value) :: environment) := by
  intro sought found hfind
  simp only [Env.find?, List.find?] at hfind
  cases hnames : (name == sought) with
  | true =>
      rw [hnames] at hfind
      simp only [Option.map] at hfind
      obtain rfl := Option.some.inj hfind
      refine ⟨scheme, ?_, valueInstances⟩
      simp only [NamedContext.find?, List.find?]
      rw [hnames]
      rfl
  | false =>
      rw [hnames] at hfind
      obtain ⟨foundScheme, hscheme, hinstances⟩ :=
        typing sought found hfind
      refine ⟨foundScheme, ?_, ?_⟩
      simp only [NamedContext.find?, List.find?] at hscheme ⊢
      rw [hnames]
      · exact hscheme
      · intro target hinstance
        apply hinstances target
        exact hinstance

/-- Extend a typed environment by one monomorphic value. -/
theorem EnvTyped.cons
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    {name : String} {value : Value} {target : Ty}
    (valueTyping : ValueTy signature value target)
    (typing : EnvTyped signature context environment) :
    EnvTyped signature ((name, NamedScheme.mono target) :: context)
      ((name, value) :: environment) :=
  typing.consScheme (fun actual hinstance => by
    rw [hinstance.mono_eq]
    exact valueTyping)

/-! ## Recursive self closures and application environments -/

/-- A concrete recursive self closure preserves its source body derivation. -/
theorem selfClosure_typed
    {signature : FrozenSig} {context : NamedContext} {environment : Env}
    {name parameter : String} {body : Expr} {domain codomain : Ty}
    (environmentTyping : EnvTyped signature context environment)
    (bodyTyping : RuntimeTyping signature
      ((parameter, NamedScheme.mono domain) ::
        (name, NamedScheme.mono (.fn domain codomain)) :: context)
      body codomain) :
    ValueTy signature (selfClosure name environment parameter body)
      (.fn domain codomain) := by
  refine ValueTy.closure context
    (fun sought value hfind => environmentTyping.domain hfind)
    (fun sought value scheme target hvalue hscheme hinstance =>
      environmentTyping.lookup hvalue hscheme hinstance)
    ?_ ?_
  · intro impossible
    contradiction
  · intro self hself
    have equality : self = name :=
      Option.some.inj hself.symm
    subst self
    exact bodyTyping

/--
Applying a typed closure yields a typed argument/self environment and the
runtime certificate of its body in that same context.
-/
theorem pushArg_typed
    {signature : FrozenSig} {self : Option String} {environment : Env}
    {parameter : String} {body : Expr} {domain codomain : Ty}
    {argument : Value}
    (functionTyping :
      ValueTy signature (.closure self environment parameter body)
        (.fn domain codomain))
    (argumentTyping : ValueTy signature argument domain) :
    ∃ bodyContext,
      EnvTyped signature bodyContext
        (pushArg self environment parameter body argument) ∧
      RuntimeTyping signature bodyContext body codomain := by
  cases functionTyping with
  | closure context domainPart instancePart noneBody someBody =>
      have environmentTyping : EnvTyped signature context environment :=
        envTyped_of_parts domainPart instancePart
      cases self with
      | none =>
          refine ⟨(parameter, NamedScheme.mono domain) :: context,
            environmentTyping.cons argumentTyping, ?_⟩
          exact noneBody rfl
      | some name =>
          have bodyTyping := someBody name rfl
          have selfTyping :
              ValueTy signature
                (selfClosure name environment parameter body)
                (.fn domain codomain) :=
            selfClosure_typed environmentTyping bodyTyping
          refine
            ⟨(parameter, NamedScheme.mono domain) ::
                (name, NamedScheme.mono (.fn domain codomain)) :: context,
              (environmentTyping.cons selfTyping).cons argumentTyping,
              bodyTyping⟩

/-! ## Concrete matcher-literal inversion -/

/-- Runtime view of one coverage-certified concrete matcher literal. -/
def CoveredMatcherLiteralView
    (signature : FrozenSig) (environment : Env)
    (originalClauses currentClauses : List Clause)
    (capability : Cap) (target : Ty) : Prop :=
  ∃ context evidence,
    EnvTyped signature context environment ∧
    MatcherCursor currentClauses originalClauses ∧
    RuntimeTyping signature context (.matcher originalClauses)
      (.matcher capability target) ∧
    ResolvedClausesTy signature context originalClauses capability target
      evidence ∧
    Shape.inferShape signature.observability evidence = some capability ∧
    CatchAllLast originalClauses ∧
    ArmExhaustive signature originalClauses target ∧
    PPBindNodup originalClauses ∧
    ArmBindNodup originalClauses ∧
    CoverageOK signature.toMatcherSig originalClauses capability

/-- Invert the concrete source derivation retained by a matcher runtime value. -/
theorem ValueTy.matcherLiteral_inversion
    {signature : FrozenSig} {environment : Env}
    {originalClauses currentClauses : List Clause}
    {capability : Cap} {target : Ty}
    (typing : ValueTy signature
      (.matcherV environment originalClauses currentClauses)
      (.matcher capability target)) :
    ∃ context,
      EnvTyped signature context environment ∧
      MatcherCursor currentClauses originalClauses ∧
      RuntimeTyping signature context (.matcher originalClauses)
        (.matcher capability target) := by
  cases typing with
  | matcherLiteral context domainPart instancePart sourceTyping cursor =>
      exact ⟨context, envTyped_of_parts domainPart instancePart, cursor,
        sourceTyping⟩

/--
Covered matcher-literal inversion recovers actual evidence and concrete
coverage, rather than an arbitrary runtime specification.
-/
theorem ValueTy.coveredMatcherLiteral_inversion
    {signature : FrozenSig} {environment : Env}
    {originalClauses currentClauses : List Clause}
    {capability : Cap} {target : Ty}
    (typing : ValueTy signature
      (.matcherV environment originalClauses currentClauses)
      (.matcher capability target)) :
    CoveredMatcherLiteralView signature environment originalClauses
      currentClauses capability target := by
  obtain ⟨context, environmentTyped, cursor, sourceTyping⟩ :=
    typing.matcherLiteral_inversion
  obtain ⟨evidence, clausesTyped, shape, catchAll, armsExhaustive,
      ppNodup, armNodup, coverage⟩ := sourceTyping.matcher_inversion
  exact ⟨context, evidence, environmentTyped, cursor,
    sourceTyping, clausesTyped, shape, catchAll, armsExhaustive, ppNodup,
    armNodup, coverage⟩

/-- A concrete runtime matcher literal exposes coverage of its actual clauses. -/
theorem ValueTy.matcherLiteral_original_coverage
    {signature : FrozenSig} {environment : Env}
    {originalClauses currentClauses : List Clause}
    {capability : Cap} {target : Ty}
    (typing : ValueTy signature
      (.matcherV environment originalClauses currentClauses)
      (.matcher capability target)) :
    MatcherCursor currentClauses originalClauses ∧
      CoverageOK signature.toMatcherSig originalClauses capability := by
  rcases typing.coveredMatcherLiteral_inversion with
    ⟨_, _, _, cursor, _, _, _, _, _, _, _, coverage⟩
  exact ⟨cursor, coverage⟩

/-- `something` has the unique catch-all producer capability `any`. -/
theorem ValueTy.something_capability_unique
    {signature : FrozenSig} {capability : Cap} {target : Ty}
    (typing : ValueTy signature .something (.matcher capability target)) :
    capability = .any := by
  cases typing
  rfl

/-- A deterministic evidence result determines one literal capability. -/
theorem matcherLiteral_capability_unique_of_same_evidence
    {signature : FrozenSig} {evidence : List Shape.Evidence}
    {left right : Cap}
    (hleft :
      Shape.inferShape signature.observability evidence = some left)
    (hright :
      Shape.inferShape signature.observability evidence = some right) :
    left = right :=
  Option.some.inj (hleft.symm.trans hright)

/-! ## Typed atoms, pattern environments, trees, stacks, and states -/

/-- Reflexive pointwise demand evidence. -/
def CapabilityDemand.equalList : (capabilities : List Cap) →
    CapabilityDemands capabilities capabilities
  | [] => .nil
  | _ :: capabilities => .cons .equal (equalList capabilities)

/-- Runtime demand lists retain exact arity. -/
theorem CapabilityDemands.length :
    ∀ {producers consumers : List Cap},
      CapabilityDemands producers consumers →
      producers.length = consumers.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ tail =>
      congrArg Nat.succ (CapabilityDemands.length tail)

/-- Direct inversion when both product endpoints are already exposed. -/
theorem CapabilityDemand.prod_children
    {producers consumers : List Cap}
    (demand : CapabilityDemand (.prod producers) (.prod consumers)) :
    CapabilityDemands producers consumers := by
  cases demand with
  | equal => exact CapabilityDemand.equalList producers
  | prod children => exact children

/-- Direct inversion when both constructor endpoints are already exposed. -/
theorem CapabilityDemand.con_children
    {name : String} {producers consumers : List Cap}
    (demand : CapabilityDemand (.con name producers) (.con name consumers)) :
    CapabilityDemands producers consumers := by
  cases demand with
  | equal => exact CapabilityDemand.equalList producers
  | con children => exact children

/--
A usable matcher retains its hidden producer capability together with the
normalized endpoint evidence by which the requested consumer capability may
use it.  Thus a checked `Slot any a` need not originate from `Matcher any a`.
This runtime abstraction does not retain the raw consumer syntax or the
matcher-to-slot certificate that produced the endpoint evidence.
-/
def MatcherUsable
    (signature : FrozenSig) (matcher : Value)
    (capability : Cap) (target : Ty) : Prop :=
  ∃ producerCapability,
    ValueTy signature matcher (.matcher producerCapability target) ∧
    CapabilityDemand producerCapability capability

/-- An exact producer matcher is usable at its own capability. -/
def MatcherUsable.ofMatcher
    {signature : FrozenSig} {matcher : Value} {capability : Cap} {target : Ty}
    (typing : ValueTy signature matcher (.matcher capability target)) :
    MatcherUsable signature matcher capability target :=
  ⟨capability, typing, .equal⟩

/--
A primitive or catch-all pattern observes only the matched target.  Its
matcher may therefore have any producer/slot capability at that same target;
structural pattern dispatch continues to use `MatcherUsable` with the exact
capability inferred for the pattern.
-/
def MatcherAtTarget
    (signature : FrozenSig) (matcher : Value) (target : Ty) : Prop :=
  ∃ capability, MatcherUsable signature matcher capability target

/--
One matching atom consumes a source binding context left to right under the
prevailing substitution retained by that atom.
-/
inductive AtomTy (signature : FrozenSig)
    (context : NamedContext) (parameters : PatternCtx) :
    MonoCtx → Atom → MonoCtx → Prop where
  | mk {prevailing : Subst}
      {input output pattern matcher value capability target} :
      ResolvedPatternTy signature prevailing context parameters input pattern
        capability target output →
      MatcherUsable signature matcher capability target →
      ValueTy signature value target →
      AtomTy signature context parameters input
        ⟨pattern, matcher, value⟩ output
  | primitive {prevailing : Subst}
      {input output pattern matcher value capability target} :
      ResolvedPatternTy signature prevailing context parameters input pattern
        capability target output →
      pattern.isPrimForm = true →
      MatcherAtTarget signature matcher target →
      ValueTy signature value target →
      AtomTy signature context parameters input
        ⟨pattern, matcher, value⟩ output

/-!
An inner mnode occurrence resolves through its own fixed `piE`, because the
resolved actual pattern is pushed back onto the enclosing stack by
`Step.mnodeVarpat`.
-/
mutual

/-- Embedded parameters may not occur below an `or` branch. -/
def Pattern.noEmbedInOr : Pattern → Bool
  | .pvar _ => true
  | .wild => true
  | .pval _ => true
  | .embed _ => true
  | .pctor _ patterns => Pattern.noEmbedInOrList patterns
  | .pand left right => left.noEmbedInOr && right.noEmbedInOr
  | .por left right => left.embedVars.isEmpty && right.embedVars.isEmpty &&
      left.noEmbedInOr && right.noEmbedInOr
  | .papp _ patterns => Pattern.noEmbedInOrList patterns
  | .ptuple patterns => Pattern.noEmbedInOrList patterns

/-- List form of `Pattern.noEmbedInOr`. -/
def Pattern.noEmbedInOrList : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      pattern.noEmbedInOr && Pattern.noEmbedInOrList patterns

end

mutual
def treeEmbedOccs : Tree → List String
  | .atom atom => atom.p.embedVars
  | .mnode trees _ _ piE =>
      (stackEmbedOccs trees).flatMap fun name =>
        match List.find? (fun entry => entry.1 == name) piE with
        | some (_, pattern) => pattern.embedVars
        | none => [name]

def stackEmbedOccs : List Tree → List String
  | [] => []
  | tree :: trees => treeEmbedOccs tree ++ stackEmbedOccs trees
end

/-!
The ordered embed stream of an isolated pattern-function node is invariant
under inner reduction only when no `or` branch can duplicate or discard an
embedded parameter.  The source pattern-function checker establishes this
property for a fresh node, and `TreeTy.mnode` retains it for every cursor.
-/
mutual

/-- A tree contains no embedded parameter below an `or` alternative. -/
def treeNoEmbedInOr : Tree → Bool
  | .atom atom => atom.p.noEmbedInOr
  | .mnode trees _ _ piE =>
      stackNoEmbedInOr trees &&
        Pattern.noEmbedInOrList (piE.map Prod.snd)

/-- Every tree in a stack satisfies the node-local embedding discipline. -/
def stackNoEmbedInOr : List Tree → Bool
  | [] => true
  | tree :: trees => treeNoEmbedInOr tree && stackNoEmbedInOr trees

end

/-- Remaining actual arguments paired with their source-threaded duals. -/
inductive PiEnvTyped (signature : FrozenSig)
    (context : NamedContext) (parameters : PatternCtx) :
    MonoCtx → PiEnv → List Dual → MonoCtx → Prop where
  | nil {bindings} :
      PiEnvTyped signature context parameters bindings [] [] bindings
  | cons
      {prevailing : Subst}
      {input middle output name pattern capability target rest inner} :
      ResolvedPatternTy signature prevailing context parameters input pattern
        capability target middle →
      PiEnvTyped signature context parameters middle rest inner
        output →
      PiEnvTyped signature context parameters input
        ((name, pattern) :: rest) (⟨capability, target⟩ :: inner) output

/--
Every remaining actual argument uses the dual assigned to the same formal in
the fixed inner parameter context.  The fixed context does not shrink.
-/
def RemInParameters (fixed : PatternCtx) : PiEnv → List Dual → Prop
  | [], [] => True
  | (name, _) :: rest, dual :: duals =>
      fixed.find? name = some dual ∧ RemInParameters fixed rest duals
  | _, _ => False

mutual

/-- Well-typed matching trees, including isolated pattern-function nodes. -/
inductive TreeTy (signature : FrozenSig) :
    NamedContext → PatternCtx → MonoCtx → Tree → MonoCtx → Prop where
  | atom {context parameters input atom output} :
      AtomTy signature context parameters input atom output →
      TreeTy signature context parameters input (.atom atom) output
  | mnode
      {context parameters input output trees environment substitution piE
       innerParameters innerBindings innerOutput rem duals} :
      (∃ index, rem = piE.drop index) →
      (piE.map Prod.fst).Nodup →
      stackNoEmbedInOr trees = true →
      Pattern.noEmbedInOrList (piE.map Prod.snd) = true →
      stackEmbedOccs trees = rem.map Prod.fst →
      PiEnvTyped signature context parameters input rem duals output →
      RemInParameters innerParameters rem duals →
      EnvTyped signature context environment →
      MatchSubstTyped signature innerBindings substitution →
      StackTy signature context innerParameters innerBindings
        trees innerOutput →
      TreeTy signature context parameters input
        (.mnode trees environment substitution piE) output

/-- A well-typed matching stack threads bindings through every tree. -/
inductive StackTy (signature : FrozenSig) :
    NamedContext → PatternCtx → MonoCtx → List Tree → MonoCtx → Prop where
  | nil {context parameters bindings} :
      StackTy signature context parameters bindings [] bindings
  | cons {context parameters input middle output tree trees} :
      TreeTy signature context parameters input tree middle →
      StackTy signature context parameters middle trees output →
      StackTy signature context parameters input (tree :: trees)
        output

end

/-- Every runtime value stored by one matching atom is pristine. -/
def AtomPristine (atom : Atom) : Prop :=
  ValuePristine atom.m ∧ ValuePristine atom.v

mutual

/-- Pristineness of values recursively stored in a matching tree. -/
inductive TreePristine : Tree → Prop where
  | atom {atom} :
      AtomPristine atom → TreePristine (.atom atom)
  | mnode {trees environment substitution piE} :
      StackPristine trees →
      EnvPristine environment →
      EnvPristine substitution →
      TreePristine (.mnode trees environment substitution piE)

/-- Pointwise pristine matching stacks. -/
inductive StackPristine : List Tree → Prop where
  | nil : StackPristine []
  | cons {tree trees} :
      TreePristine tree →
      StackPristine trees →
      StackPristine (tree :: trees)

end

/-- No advanced matcher cursor occurs anywhere in one public matching state. -/
def MStatePristine (state : MState) : Prop :=
  StackPristine state.S ∧ EnvPristine state.ρ ∧ EnvPristine state.θ

/-- A well-typed matching state under an explicit pattern-parameter context. -/
def MStateTyAt
    (signature : FrozenSig) (context : NamedContext) (parameters : PatternCtx)
    (state : MState) (goal : MonoCtx) : Prop :=
  MStatePristine state ∧
  stackNoEmbedInOr state.S = true ∧
  EnvTyped signature context state.ρ ∧
  ∃ input,
    MatchSubstTyped signature input state.θ ∧
    StackTy signature context parameters input state.S goal

/-- Top-level matching-state typing has no embedded pattern parameters. -/
abbrev MStateTy
    (signature : FrozenSig) (context : NamedContext)
    (state : MState) (goal : MonoCtx) : Prop :=
  MStateTyAt signature context [] state goal

/-- The empty stack leaves its binding context unchanged. -/
theorem StackTy.nil_inversion
    {signature : FrozenSig} {context : NamedContext} {parameters : PatternCtx}
    {input output : MonoCtx}
    (typing :
      StackTy signature context parameters input [] output) :
    output = input := by
  cases typing
  rfl

/-- A terminal typed state carries a substitution typed at its goal context. -/
theorem MStateTyAt.terminal_substitution
    {signature : FrozenSig} {context : NamedContext} {parameters : PatternCtx}
    {environment : Env} {substitution : MatchSubst} {goal : MonoCtx}
    (typing : MStateTyAt signature context parameters
      ⟨[], environment, substitution⟩ goal) :
    MatchSubstTyped signature goal substitution := by
  rcases typing with ⟨_, _, _, input, substitutionTyped, stackTyped⟩
  have equality : goal = input := stackTyped.nil_inversion
  subst goal
  exact substitutionTyped

end TypePM
