import TypePM.Source
import TypePM.Semantics

/-!
# Pattern-function definitions and frozen runtime agreement

Pattern functions cannot call themselves directly, including below embedded
expressions.  Their embedded parameters must occur exactly once, in
declaration order, and never under an or-alternative.  The source judgment
records the generalized two-sorted dual scheme; the runtime agreement
predicate ensures that `Step.patfunEnter` expands the same checked parameter
list and body.
-/

namespace TypePM

/-! ## Linear embedded-parameter traversal -/

mutual

/-- Return embedded parameters in order, rejecting every embed below `or`. -/
def Pattern.linearEmbeds : Pattern → Option (List String)
  | .pvar _ => some []
  | .wild => some []
  | .pval _ => some []
  | .embed name => some [name]
  | .pctor _ patterns => Pattern.linearEmbedsList patterns
  | .pand left right => do
      let leftNames ← left.linearEmbeds
      let rightNames ← right.linearEmbeds
      pure (leftNames ++ rightNames)
  | .por _ _ => none
  | .papp _ patterns => Pattern.linearEmbedsList patterns
  | .ptuple patterns => Pattern.linearEmbedsList patterns

/-- List traversal for `Pattern.linearEmbeds`. -/
def Pattern.linearEmbedsList : List Pattern → Option (List String)
  | [] => some []
  | pattern :: patterns => do
      let head ← pattern.linearEmbeds
      let tail ← Pattern.linearEmbedsList patterns
      pure (head ++ tail)

end

/-- The formal core's linear, ordered parameter-use condition. -/
def LinearPatternParameters
    (parameters : List String) (body : Pattern) : Prop :=
  body.linearEmbeds = some parameters

instance (parameters : List String) (body : Pattern) :
    Decidable (LinearPatternParameters parameters body) :=
  inferInstanceAs (Decidable (body.linearEmbeds = some parameters))

/-! ## Non-recursive call traversal -/

mutual

/-- Pattern-function calls occurring anywhere below an expression. -/
def Expr.patternFunCalls : Expr → List String
  | .var _ => []
  | .lam _ body => body.patternFunCalls
  | .fix _ _ body => body.patternFunCalls
  | .app function argument =>
      function.patternFunCalls ++ argument.patternFunCalls
  | .lit _ => []
  | .tuple expressions => Expr.patternFunCallsList expressions
  | .ctor _ expressions => Expr.patternFunCallsList expressions
  | .prim _ expressions => Expr.patternFunCallsList expressions
  | .letE _ value body => value.patternFunCalls ++ body.patternFunCalls
  | .something => []
  | .matcher clauses => Clause.patternFunCallsList clauses
  | .matchAll target matcher pattern body =>
      target.patternFunCalls ++ matcher.patternFunCalls ++
        pattern.patternFunCalls ++ body.patternFunCalls

/-- Pattern-function calls occurring in an expression list. -/
def Expr.patternFunCallsList : List Expr → List String
  | [] => []
  | expression :: expressions =>
      expression.patternFunCalls ++ Expr.patternFunCallsList expressions

/-- Pattern-function calls occurring anywhere below a user pattern. -/
def Pattern.patternFunCalls : Pattern → List String
  | .pvar _ => []
  | .wild => []
  | .pval expression => expression.patternFunCalls
  | .embed _ => []
  | .pctor _ patterns => Pattern.patternFunCallsList patterns
  | .pand left right => left.patternFunCalls ++ right.patternFunCalls
  | .por left right => left.patternFunCalls ++ right.patternFunCalls
  | .papp name patterns => name :: Pattern.patternFunCallsList patterns
  | .ptuple patterns => Pattern.patternFunCallsList patterns

/-- Pattern-function calls occurring in a user-pattern list. -/
def Pattern.patternFunCallsList : List Pattern → List String
  | [] => []
  | pattern :: patterns =>
      pattern.patternFunCalls ++ Pattern.patternFunCallsList patterns

/-- Pattern-function calls occurring in one matcher arm. -/
def Arm.patternFunCalls : Arm → List String
  | .mk _ body => body.patternFunCalls

/-- Pattern-function calls occurring in an arm list. -/
def Arm.patternFunCallsList : List Arm → List String
  | [] => []
  | arm :: arms => arm.patternFunCalls ++ Arm.patternFunCallsList arms

/-- Pattern-function calls occurring in one matcher clause. -/
def Clause.patternFunCalls : Clause → List String
  | .mk _ next arms =>
      next.patternFunCalls ++ Arm.patternFunCallsList arms

/-- Pattern-function calls occurring in a clause list. -/
def Clause.patternFunCallsList : List Clause → List String
  | [] => []
  | clause :: clauses =>
      clause.patternFunCalls ++ Clause.patternFunCallsList clauses

end

/-! ## Source definition judgment -/

/-- One source pattern-function definition. -/
structure PatternDef where
  name : String
  parameters : List (String × Ty)
  body : Pattern
deriving Repr

/-- Parameter names in declaration order. -/
def PatternDef.parameterNames (definition : PatternDef) : List String :=
  definition.parameters.map Prod.fst

/-- Parameter target types in declaration order. -/
def PatternDef.parameterTargets (definition : PatternDef) : List Ty :=
  definition.parameters.map Prod.snd

/-- A pattern-function body contains no direct or nested call to itself. -/
def NonrecursivePatternDef (definition : PatternDef) : Prop :=
  definition.name ∉ definition.body.patternFunCalls

instance (definition : PatternDef) :
    Decidable (NonrecursivePatternDef definition) :=
  inferInstanceAs
    (Decidable (definition.name ∉ definition.body.patternFunCalls))

/-- Build the fresh dual context used while checking a definition body. -/
def patternParameterContext
    (parameters : List (String × Ty)) (capabilities : List Cap) : PatternCtx :=
  (parameters.zip capabilities).map fun entry =>
    (entry.1.1, ⟨entry.2, entry.1.2⟩)

/-- The dual list corresponding to definition parameters. -/
def patternParameterDuals
    (parameters : List (String × Ty)) (capabilities : List Cap) : List Dual :=
  (parameters.zip capabilities).map fun entry =>
    ⟨entry.2, entry.1.2⟩

/-- The canonical core payload of a pattern-function definition.  The
definition being checked is removed before generalization, and singleton
local capabilities are defaulted by `FrozenSig.generalizeDual`. -/
def PatternDef.coreScheme
    (definition : PatternDef) (signature : FrozenSig) (context : NamedContext)
    (capabilities : List Cap) (result : Dual) : DualScheme :=
  ({ signature with
      patternFuns := signature.patternFuns.filter
        fun named => named.1 != definition.name }).generalizeDual context
    (patternParameterDuals definition.parameters capabilities) result

/-- The canonical singleton-default action that normalizes raw argument/result
indices into the canonical core payload.  It is not identified with the
prevailing substitution stored by `ResolvedPatternTy`. -/
def PatternDef.coreCapSubst
    (definition : PatternDef) (signature : FrozenSig) (context : NamedContext)
    (capabilities : List Cap) (result : Dual) : CapSubst :=
  singletonDefaultSubst
    (({ signature with
        patternFuns := signature.patternFuns.filter
          fun named => named.1 != definition.name }).fcv ++ context.fcv)
    (patternParameterDuals definition.parameters capabilities) result

/-- The core payload is exactly the raw argument/result payload after the
single canonical defaulting action; no later value-flow instance performs
this structural `Any` replacement. -/
theorem PatternDef.coreScheme_payload
    (definition : PatternDef) (signature : FrozenSig) (context : NamedContext)
    (capabilities : List Cap) (result : Dual) :
    let C := definition.coreCapSubst signature context capabilities result
    (definition.coreScheme signature context capabilities result).args =
        (patternParameterDuals definition.parameters capabilities).map
          (Dual.apply C TySubst.id) ∧
      (definition.coreScheme signature context capabilities result).result =
        result.apply C TySubst.id := by
  dsimp only [PatternDef.coreScheme, PatternDef.coreCapSubst,
    FrozenSig.generalizeDual, normalizeDualSingletons]
  exact ⟨rfl, rfl⟩

/-- Fixed parameter context of the normalized pattern-function core. -/
def PatternDef.coreParameters
    (definition : PatternDef) (signature : FrozenSig) (context : NamedContext)
    (capabilities : List Cap) (result : Dual) : PatternCtx :=
  definition.parameterNames.zip
    (definition.coreScheme signature context capabilities result).args

/--
Two frozen dual schemes are observationally the same declaration when they
admit exactly the same safe value-flow instances.  This is the alpha-insensitive
boundary used by pattern-function definitions: locally fresh binder names may
change with the source context, while the frozen lookup scheme remains fixed.
-/
structure DualScheme.ValueFlowEquivalent
    (left right : DualScheme) : Prop where
  /-- Equivalent declarations admit exactly the same safe instances. -/
  instances : ∀ args result, left.ValueFlowInst args result ↔
    right.ValueFlowInst args result
  /-- Equivalent declarations expose the same free capability variables. -/
  freeCaps : left.fcv = right.fcv
  /-- Equivalent declarations expose the same free target variables. -/
  freeTargets : left.ftv = right.ftv

/-- Value-flow equivalence is reflexive. -/
theorem DualScheme.ValueFlowEquivalent.refl (scheme : DualScheme) :
    scheme.ValueFlowEquivalent scheme := by
  exact ⟨fun _ _ => Iff.rfl, rfl, rfl⟩

/-- PATFUN-DEF for the concrete two-sorted source calculus. -/
inductive PatternDefTy (signature : FrozenSig) (context : NamedContext) :
    PatternDef → DualScheme → Prop where
  | mk
      {definition capabilities result resultBindings scheme bodyPrevailing} :
      signature.findPatternFun definition.name = some scheme →
      NonrecursivePatternDef definition →
      definition.parameters.length = capabilities.length →
      definition.parameterNames.Nodup →
      (∀ capability ∈ capabilities,
        ∃ varId, capability = .var varId ∧
          FreshCap signature context [] [] varId) →
      capabilities.Nodup →
      ResolvedPatternTy signature bodyPrevailing context
        (definition.coreParameters signature context capabilities result)
        [] definition.body
        (definition.coreScheme signature context capabilities result).result.cap
        (definition.coreScheme signature context capabilities result).result.target
        resultBindings →
      LinearPatternParameters definition.parameterNames definition.body →
      scheme.ValueFlowEquivalent
        (definition.coreScheme signature context capabilities result) →
      PatternDefTy signature context definition scheme

/-- Runtime erasure of a checked pattern-function definition. -/
def PatternDef.runtime (definition : PatternDef) : PatFunRuntimeSig :=
  ⟨definition.parameterNames, definition.body⟩

/-- A runtime signature entry is the erasure of a checked source definition. -/
def RuntimeEntryTyped
    (signature : FrozenSig) (context : NamedContext)
    (entry : String × PatFunRuntimeSig) : Prop :=
  ∃ definition scheme,
    entry = (definition.name, definition.runtime) ∧
    PatternDefTy signature context definition scheme

/-- Every runtime pattern function is backed by a checked source definition. -/
def RuntimeSigTyped
    (signature : FrozenSig) (context : NamedContext)
    (runtime : RuntimeSigF) : Prop :=
  ∀ entry ∈ runtime, RuntimeEntryTyped signature context entry

/-! ## Executable regressions for the definition boundaries -/

example :
    ¬ NonrecursivePatternDef
      { name := "self"
        parameters := []
        body :=
          .pval
            (.matchAll .something .something
              (.papp "self" []) .something) } := by
  decide

example :
    ¬ NonrecursivePatternDef
      { name := "self"
        parameters := []
        body :=
          .pval
            (.matcher
              [.mk .hole
                (.matchAll .something .something
                  (.papp "self" []) .something)
                []]) } := by
  decide

example :
    ¬ NonrecursivePatternDef
      { name := "self"
        parameters := []
        body :=
          .pval
            (.matcher
              [.mk .hole .something
                [.mk .wild
                  (.matchAll .something .something
                    (.papp "self" []) .something)]]) } := by
  decide

example :
    NonrecursivePatternDef
      { name := "self"
        parameters := []
        body :=
          .pval
            (.matchAll .something .something
              (.papp "other" [.pval (.matcher
                [.mk .hole .something
                  [.mk .wild
                    (.matchAll .something .something
                      (.papp "helper" []) .something)]])])
              .something) } := by
  decide

example :
    LinearPatternParameters ["x", "y"]
      (.pand (.embed "x") (.pctor "cons" [.embed "y", .wild])) := by
  decide

example :
    ¬ LinearPatternParameters ["x"]
      (.por (.embed "x") .wild) := by
  decide

example :
    ¬ LinearPatternParameters ["x"]
      (.pand (.embed "x") (.embed "x")) := by
  decide

end TypePM
