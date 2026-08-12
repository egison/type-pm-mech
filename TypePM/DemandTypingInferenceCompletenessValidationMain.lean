import TypePM.DemandTypingInferenceCompletenessCertifiedRun

/-!
# Constructor-wise validator composition

The global completeness recursion constructs raw run completions and validator
coverage together.  This module supplies the second half of that construction:
small chains which follow the executable order of each expression constructor.
They consume child `ValidatorRunExtension`s while those child runs are still in
scope; no theorem attempts to recover intermediate states from an opaque parent
completion after the fact.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessValidationMain

open Inference
open Inference.Reconstruction
open DemandTypingInferenceCompletenessCertifiedRun

/-- A solve-free expression leaf visits its node and records its result. -/
theorem synthLeaf
    (terminal : Subst) (signature : FrozenSig) (initial : InferState)
    (kind : NodeKind) (path : SyntaxPath) (expression : Expr) (target : Ty) :
    ValidatorRunExtension terminal signature initial
      (finishExpr expression path target (visit initial kind path)).state :=
  (ValidatorRunExtension.visit terminal signature initial kind path).trans
    (ValidatorRunExtension.finishExpr terminal signature _ expression path
      target)

theorem synthLit
    (terminal : Subst) (signature : FrozenSig) (initial : InferState)
    (path : SyntaxPath) (value : Int) :
    ValidatorRunExtension terminal signature initial
      (finishExpr (.lit value) path .int (visit initial .exprLit path)).state :=
  synthLeaf terminal signature initial .exprLit path (.lit value) .int

/-- `something` visits, allocates its target, then records the matcher result. -/
theorem synthSomething
    (terminal : Subst) (signature : FrozenSig) (initial : InferState)
    (path : SyntaxPath) :
    let entered := visit initial .exprSomething path
    let allocated := entered.freshTy
      (freshOrigin .expression path "something-target")
    ValidatorRunExtension terminal signature initial
      (finishExpr .something path (.matcher .any allocated.1)
        allocated.2).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial
    .exprSomething path).trans
      ((ValidatorRunExtension.freshTy terminal signature _ _).trans
        (ValidatorRunExtension.finishExpr terminal signature _ .something path
          _))

/-- Inactive variable lookup: visit, canonical scheme instantiation, finish. -/
theorem synthVar
    {terminal : Subst} {signature : FrozenSig}
    {rawContext normalizedContext : Context} {name : String}
    {initial : InferState} {scheme : Scheme} {path : SyntaxPath}
    (terminalLookup : ∀ future,
      (instantiateSchemeInState signature rawContext normalizedContext name
        (visit initial .exprVar path) scheme).2.StateExtension future →
      (rawContext.applySubst future.prevailing).find? name =
        some (scheme.applyMeta future.prevailing)) :
    let entered := visit initial .exprVar path
    let instantiated := instantiateSchemeInState signature rawContext
      normalizedContext name entered scheme
    ValidatorRunExtension terminal signature initial
      (finishExpr (.var name) path instantiated.1 instantiated.2).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial .exprVar
    path).trans
      ((ValidatorRunExtension.instantiateSchemeInState terminalLookup).trans
        (ValidatorRunExtension.finishExpr terminal signature _ (.var name)
          path _))

/-- Active direct-self lookup adds its reference event and source record before
the ordinary variable result event. -/
theorem synthSelfVar
    {terminal : Subst} {signature : FrozenSig}
    {rawContext normalizedContext : Context} {name : String}
    {initial : InferState} {scheme : Scheme} {path : SyntaxPath}
    (placeholder : Ty)
    (terminalLookup : ∀ future,
      (instantiateSchemeInState signature rawContext normalizedContext name
        (visit initial .exprVar path) scheme).2.StateExtension future →
      (rawContext.applySubst future.prevailing).find? name =
        some (scheme.applyMeta future.prevailing)) :
    let entered := visit initial .exprVar path
    let instantiated := instantiateSchemeInState signature rawContext
      normalizedContext name entered scheme
    let referenced := recordSelfReference instantiated.2 name placeholder path
    ValidatorRunExtension terminal signature initial
      (finishExpr (.var name) path instantiated.1 referenced).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial .exprVar
    path).trans
      ((ValidatorRunExtension.instantiateSchemeInState terminalLookup).trans
        ((ValidatorRunExtension.recordSelfReference terminal signature _ name
          placeholder path).trans
          (ValidatorRunExtension.finishExpr terminal signature _ (.var name)
            path _)))

/-- A lambda surrounds its already-certified body by visit/fresh and finish
events. -/
theorem synthLam
    {terminal : Subst} {signature : FrozenSig} {initial bodyState : InferState}
    {path : SyntaxPath} {name : String} {body : Expr} {bodyTarget : Ty}
    (child : ValidatorRunExtension terminal signature
      ((visit initial .exprLam path).freshTy
        (freshOrigin .expression path "lambda-domain")).2 bodyState) :
    let entered := visit initial .exprLam path
    let allocated := entered.freshTy
      (freshOrigin .expression path "lambda-domain")
    ValidatorRunExtension terminal signature initial
      (finishExpr (.lam name body) path (.fn allocated.1 bodyTarget)
        bodyState).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial .exprLam
    path).trans
      ((ValidatorRunExtension.freshTy terminal signature _ _).trans
        (child.trans
          (ValidatorRunExtension.finishExpr terminal signature _
            (.lam name body) path _)))

/-- Tuple synthesis has one visit, a left-to-right certified child-list run,
and one result event. -/
theorem synthTuple
    {terminal : Subst} {signature : FrozenSig} {initial final : InferState}
    {path : SyntaxPath} {expressions : List Expr} {targets : List Ty}
    (children : ValidatorRunExtension terminal signature
      (visit initial .exprTuple path) final) :
    ValidatorRunExtension terminal signature initial
      (finishExpr (.tuple expressions) path (.prod targets) final).state :=
  (ValidatorRunExtension.visit terminal signature initial .exprTuple
    path).trans
      (children.trans
        (ValidatorRunExtension.finishExpr terminal signature final
          (.tuple expressions) path (.prod targets)))

/-- Application validation is purely chronological once the function
alignment and argument checking cuts have supplied their own extensions. -/
theorem synthApp
    {terminal : Subst} {signature : FrozenSig}
    {initial functionState alignedState argumentState : InferState}
    {path : SyntaxPath} {function argument : Expr} {target : Ty}
    (functionRun : ValidatorRunExtension terminal signature
      (visit initial .exprApp path) functionState)
    (alignmentRun : ValidatorRunExtension terminal signature functionState
      alignedState)
    (argumentRun : ValidatorRunExtension terminal signature alignedState
      argumentState) :
    ValidatorRunExtension terminal signature initial
      (finishExpr (.app function argument) path target argumentState).state :=
  (ValidatorRunExtension.visit terminal signature initial .exprApp path).trans
    (functionRun.trans (alignmentRun.trans (argumentRun.trans
      (ValidatorRunExtension.finishExpr terminal signature argumentState
        (.app function argument) path target))))

/-- Checking performs no independent node visit: it is synthesis followed by
the selected expected-alignment cut. -/
theorem check
    {terminal : Subst} {signature : FrozenSig}
    {initial synthesized aligned : InferState}
    (synthesis : ValidatorRunExtension terminal signature initial synthesized)
    (alignment : ValidatorRunExtension terminal signature synthesized aligned) :
    ValidatorRunExtension terminal signature initial aligned :=
  synthesis.trans alignment

/-- Empty left-to-right traversal contributes no events. -/
theorem listNil
    (terminal : Subst) (signature : FrozenSig) (state : InferState) :
    ValidatorRunExtension terminal signature state state :=
  ValidatorRunExtension.refl terminal signature state

/-- Every expression/pattern/arm/clause list composes by the same chronological
head-then-tail law. -/
theorem listCons
    {terminal : Subst} {signature : FrozenSig}
    {initial middle final : InferState}
    (head : ValidatorRunExtension terminal signature initial middle)
    (tail : ValidatorRunExtension terminal signature middle final) :
    ValidatorRunExtension terminal signature initial final :=
  head.trans tail

/-- `let` inserts its terminal-sensitive generalization event between the
value and body traversals. -/
theorem synthLet
    {terminal : Subst} {signature : FrozenSig}
    {initial valueState bodyState : InferState}
    {path : SyntaxPath} {name : String} {value body : Expr}
    {rawContext : Context} {valueTarget bodyTarget : Ty}
    (valueRun : ValidatorRunExtension terminal signature
      (visit initial .exprLet path) valueState)
    (facts : DDTerminalAudit.LetFacts terminal signature rawContext valueTarget
      valueState.prevailing)
    (bodyRun : ValidatorRunExtension terminal signature
      (valueState.recordEvent (.letGeneralization
        valueState.trace.solves.length name rawContext valueTarget
        (rawContext.applySubst valueState.prevailing)
        (valueState.prevailing.apply valueTarget)
        (signature.generalize (rawContext.applySubst valueState.prevailing)
          (valueState.prevailing.apply valueTarget)))) bodyState) :
    ValidatorRunExtension terminal signature initial
      (finishExpr (.letE name value body) path bodyTarget bodyState).state :=
  (ValidatorRunExtension.visit terminal signature initial .exprLet path).trans
    (valueRun.trans
      ((ValidatorRunExtension.recordLetGeneralization facts).trans
        (bodyRun.trans
          (ValidatorRunExtension.finishExpr terminal signature bodyState
            (.letE name value body) path bodyTarget))))

/-- Constructor and primitive calls share the instantiate/check/freeze/finish
validation suffix. -/
theorem synthCtorLike
    {terminal : Subst} {signature : FrozenSig}
    {initial checked : InferState} {path : SyntaxPath}
    {expression : Expr} {kind : NodeKind} {scheme : CtorScheme}
    {capImages : List CapVar} {payload target : Ty}
    (closed : scheme.Closed)
    (children : ValidatorRunExtension terminal signature
      (instantiateCtorInState (visit initial kind path) scheme).2 checked) :
    let frozen := checked.freezeCapabilityExport capImages payload
    ValidatorRunExtension terminal signature initial
      (finishExpr expression path target frozen).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial kind path).trans
    ((ValidatorRunExtension.instantiateCtorInState
      (terminal := terminal) (signature := signature) _ scheme closed).trans
      (children.trans
        ((ValidatorRunExtension.freezeCapabilityExport terminal signature _
          capImages payload).trans
          (ValidatorRunExtension.finishExpr terminal signature _ expression
            path target))))

/-- Matcher literals allocate their target, traverse clauses, discharge the
terminal-sensitive finalization, protect the exported capability, and finish. -/
theorem synthMatcher
    {terminal : Subst} {signature : FrozenSig}
    {initial clausesState : InferState} {path : SyntaxPath}
    {clauses : List Clause} {rawTarget : Ty}
    {rawHoleLists : List (List Dual)} {evidence : List Shape.Evidence}
    {capability : Cap}
    (clausesRun : ValidatorRunExtension terminal signature
      ((visit initial .exprMatcher path).freshTy
        (freshOrigin .expression path "matcher-target")).2 clausesState)
    (catchAll : catchAllLastCheck clauses = true)
    (binders : matcherBindersCheck clauses = true)
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      rawHoleLists capability rawTarget) :
    let finalized :=
      (clausesState.recordEvent (.literalCoverage clauses capability)).recordEvent
        (.matcherFinalization
          (clausesState.recordEvent
            (.literalCoverage clauses capability)).trace.solves.length
          clauses rawTarget rawHoleLists
          ((clausesState.recordEvent
            (.literalCoverage clauses capability)).prevailing.apply rawTarget)
          (resolvedHoleCaps
            (clausesState.recordEvent
              (.literalCoverage clauses capability)).prevailing rawHoleLists)
          evidence capability)
    let protectedState := finalized.protectMatcherCapability capability
    ValidatorRunExtension terminal signature initial
      (finishExpr (.matcher clauses) path (.matcher capability rawTarget)
        protectedState).state := by
  dsimp only
  exact (ValidatorRunExtension.visit terminal signature initial .exprMatcher
    path).trans
      ((ValidatorRunExtension.freshTy terminal signature _ _).trans
        (clausesRun.trans
          ((ValidatorRunExtension.recordLiteralMatcherFinalization catchAll
            binders facts).trans
            (ValidatorRunExtension.finishExpr terminal signature _
              (.matcher clauses) path (.matcher capability rawTarget)))))

end DemandTypingInferenceCompletenessValidationMain
end TypePM
