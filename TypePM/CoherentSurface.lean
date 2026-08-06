import TypePM.Reconstruction

/-!
# Coherent terminal surface patterns

`TerminalPatternResolution` deliberately permits a leaf's terminal occurrence
context to be supplied independently of the raw context that justified its
fresh variables.  The derivation-structured `Prop` certificate reconstructed
from Algorithm W is stronger: every leaf occurrence context is definitionally
the image of its raw allocation context under the one prevailing substitution.

This module records that stronger boundary as an independent, indices-only
judgment.  It leaves the permissive surface constructors unchanged and proves
both a forgetful map to them and a map from reconstruction evidence.  A second,
stronger threaded judgment fixes one raw expression/parameter context across
the whole pattern tree and threads only the raw binding context left-to-right.
Reconstruction now retains exactly these raw indices, and the W reconstruction
motive generates the threaded evidence directly.  Its recursive value-pattern
premise is `ExprDeriv`; only the independent surface judgment below forgets
that premise to ordinary `HasTy`.  These bridges establish coherent core
provenance, but imply neither inference completeness nor principality.
-/

namespace TypePM
namespace CoherentSurface

open Inference.Reconstruction

mutual

/-- Terminal pattern resolution with the raw/actual context connection fixed
definitionally at every leaf. -/
inductive CoherentTerminalPatternResolution (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | pvar {rawContext rawParameters rawBindings name capVar tyVar} :
      name ∉ rawBindings.names ->
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      CoherentTerminalPatternResolution signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.pvar name)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        ((rawBindings ++ [(name, Ty.var tyVar)]).applySubst prevailing)
  | wild {rawContext rawParameters rawBindings capVar tyVar} :
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      CoherentTerminalPatternResolution signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) .wild
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (.var tyVar))
        (rawBindings.applySubst prevailing)
  | pval
      {rawContext rawParameters rawBindings expression rawTarget capVar} :
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      capVar ∉ rawTarget.fcv ->
      HasTy signature
        ((rawBindings.applySubst prevailing).toContext ++
          rawContext.applySubst prevailing)
        expression (prevailing.apply rawTarget) ->
      CoherentTerminalPatternResolution signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.pval expression)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply rawTarget)
        (rawBindings.applySubst prevailing)
  | embed {rawContext : Context} {rawParameters : PatternCtx}
      {rawBindings : MonoCtx} {name : String} {rawDual : Dual} :
      rawParameters.find? name = some rawDual ->
      (rawParameters.applySubst prevailing).find? name =
        some (rawDual.applySubst prevailing) ->
      CoherentTerminalPatternResolution signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.embed name)
        (rawDual.cap.apply prevailing.cap)
        (prevailing.apply rawDual.target)
        (rawBindings.applySubst prevailing)
  | tuple {context parameters bindings patterns duals resultBindings} :
      CoherentTerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry ->
      CoherentTerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings ->
      entry.CapCompatible (duals.map Dual.cap) result.cap ->
      entry.Inst (duals.map Dual.target) result.target ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings (.pctor name patterns) result.cap result.target resultBindings
  | and {context parameters bindings left right cap target middle result} :
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings left cap target middle ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        middle right cap target result ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings (.pand left right) cap target result
  | or {context parameters bindings left right cap target result} :
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings left cap target result ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings right cap target result ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings (.por left right) cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme ->
      CoherentTerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings ->
      scheme.ValueFlowInst duals result ->
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings (.papp name patterns) result.cap result.target resultBindings

/-- Left-to-right list form of coherent terminal pattern resolution. -/
inductive CoherentTerminalPatternResolutions (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> List Pattern -> List Dual ->
      MonoCtx -> Prop where
  | nil {context parameters bindings} :
      CoherentTerminalPatternResolutions signature prevailing context parameters
        bindings [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle patterns duals
       result} :
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings pattern cap target middle ->
      CoherentTerminalPatternResolutions signature prevailing context parameters
        middle patterns duals result ->
      CoherentTerminalPatternResolutions signature prevailing context parameters
        bindings (pattern :: patterns) (⟨cap, target⟩ :: duals) result

end

/-! ## Top-level raw provenance threaded through a pattern tree -/

mutual

/--
Terminal pattern resolution under one fixed raw context and parameter context.
The monomorphic context remains raw as well, but is threaded left-to-right so
later children see bindings introduced by earlier children.  Capabilities,
targets, and constructor certificates stay at their terminal indices.
-/
inductive ThreadedPatternResolution
    (signature : FrozenSig) (prevailing : Subst)
    (rawContext : Context) (rawParameters : PatternCtx) :
    MonoCtx -> Pattern -> Cap -> Ty -> MonoCtx -> Prop where
  | pvar {rawBindings name capVar tyVar} :
      name ∉ rawBindings.names ->
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.pvar name)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        (rawBindings ++ [(name, Ty.var tyVar)])
  | wild {rawBindings capVar tyVar} :
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings .wild ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (.var tyVar)) rawBindings
  | pval {rawBindings expression rawTarget capVar} :
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      capVar ∉ rawTarget.fcv ->
      HasTy signature
        ((rawBindings.applySubst prevailing).toContext ++
          rawContext.applySubst prevailing)
        expression (prevailing.apply rawTarget) ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.pval expression)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply rawTarget) rawBindings
  | embed {rawBindings name rawDual} :
      rawParameters.find? name = some rawDual ->
      (rawParameters.applySubst prevailing).find? name =
        some (rawDual.applySubst prevailing) ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.embed name) (rawDual.cap.apply prevailing.cap)
        (prevailing.apply rawDual.target) rawBindings
  | tuple {rawBindings patterns duals rawResultBindings} :
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawBindings patterns duals rawResultBindings ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) rawResultBindings
  | ctor
      {rawBindings name entry patterns duals rawResultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry ->
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawBindings patterns duals rawResultBindings ->
      entry.CapCompatible (duals.map Dual.cap) result.cap ->
      entry.Inst (duals.map Dual.target) result.target ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.pctor name patterns) result.cap result.target
        rawResultBindings
  | and
      {rawBindings left right cap target rawMiddleBindings rawResultBindings} :
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings left cap target rawMiddleBindings ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawMiddleBindings right cap target rawResultBindings ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.pand left right) cap target rawResultBindings
  | or {rawBindings left right cap target rawResultBindings} :
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings left cap target rawResultBindings ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings right cap target rawResultBindings ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.por left right) cap target rawResultBindings
  | app
      {rawBindings name scheme patterns duals rawResultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme ->
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawBindings patterns duals rawResultBindings ->
      scheme.ValueFlowInst duals result ->
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings (.papp name patterns) result.cap result.target
        rawResultBindings

/-- Left-to-right list form of top-level raw pattern provenance. -/
inductive ThreadedPatternResolutions
    (signature : FrozenSig) (prevailing : Subst)
    (rawContext : Context) (rawParameters : PatternCtx) :
    MonoCtx -> List Pattern -> List Dual -> MonoCtx -> Prop where
  | nil {rawBindings} :
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawBindings [] [] rawBindings
  | cons
      {rawBindings pattern cap target rawMiddleBindings patterns duals
       rawResultBindings} :
      ThreadedPatternResolution signature prevailing rawContext rawParameters
        rawBindings pattern cap target rawMiddleBindings ->
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawMiddleBindings patterns duals rawResultBindings ->
      ThreadedPatternResolutions signature prevailing rawContext rawParameters
        rawBindings (pattern :: patterns) (⟨cap, target⟩ :: duals)
        rawResultBindings

end

mutual

/--
Forget the top-level raw provenance while applying its raw binding indices at
the existing coherent terminal boundary.
-/
def ThreadedPatternResolution.toCoherentSurface
    {signature prevailing rawContext rawParameters rawBindings pattern
     capability target rawResultBindings}
    (derivation : ThreadedPatternResolution signature prevailing rawContext
      rawParameters rawBindings pattern capability target rawResultBindings) :
    CoherentTerminalPatternResolution signature prevailing
      (rawContext.applySubst prevailing)
      (rawParameters.applySubst prevailing)
      (rawBindings.applySubst prevailing) pattern capability target
      (rawResultBindings.applySubst prevailing) :=
  match derivation with
  | .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | .wild freshCap freshTy =>
      .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate expressionTyping
  | .embed rawLookup actualLookup =>
      .embed rawLookup actualLookup
  | .tuple children =>
      .tuple children.toCoherentSurface
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup children.toCoherentSurface compatible instanceTyping
  | .and left right =>
      .and left.toCoherentSurface right.toCoherentSurface
  | .or left right =>
      .or left.toCoherentSurface right.toCoherentSurface
  | .app lookup children instanceTyping =>
      .app lookup children.toCoherentSurface instanceTyping

/-- List forgetful map from threaded raw provenance. -/
def ThreadedPatternResolutions.toCoherentSurface
    {signature prevailing rawContext rawParameters rawBindings patterns duals
     rawResultBindings}
    (derivation : ThreadedPatternResolutions signature prevailing rawContext
      rawParameters rawBindings patterns duals rawResultBindings) :
    CoherentTerminalPatternResolutions signature prevailing
      (rawContext.applySubst prevailing)
      (rawParameters.applySubst prevailing)
      (rawBindings.applySubst prevailing) patterns duals
      (rawResultBindings.applySubst prevailing) :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons head.toCoherentSurface tail.toCoherentSurface

end

/-- Coherent counterpart of `ResolvedPatternTy`.  Aligned raw evidence is
already context coherent; terminal evidence must use the stricter judgment
above. -/
inductive CoherentResolvedPatternTy (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | ofAligned
      {rawContext rawParameters rawBindings pattern rawCap rawTarget
       rawResultBindings} :
      PatternResolution signature prevailing rawContext rawParameters
        rawBindings pattern rawCap rawTarget rawResultBindings ->
      CoherentResolvedPatternTy signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) pattern
        (rawCap.apply prevailing.cap) (prevailing.apply rawTarget)
        (rawResultBindings.applySubst prevailing)
  | ofTerminal
      {context parameters bindings pattern capability target resultBindings} :
      CoherentTerminalPatternResolution signature prevailing context parameters
        bindings pattern capability target resultBindings ->
      CoherentResolvedPatternTy signature prevailing context parameters bindings
        pattern capability target resultBindings

mutual

/-- Forget context coherence while retaining the same terminal indices. -/
def CoherentTerminalPatternResolution.toTerminalPatternResolution
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : CoherentTerminalPatternResolution signature prevailing context
      parameters bindings pattern capability target result) :
    TerminalPatternResolution signature prevailing context parameters bindings
      pattern capability target result :=
  match derivation with
  | .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | .wild freshCap freshTy =>
      .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate expressionTyping
  | .embed (rawContext := rawContext) rawLookup actualLookup =>
      .embed (rawContext := rawContext) rawLookup actualLookup
  | .tuple children =>
      .tuple children.toTerminalPatternResolutions
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup children.toTerminalPatternResolutions compatible
        instanceTyping
  | .and left right =>
      .and left.toTerminalPatternResolution
        right.toTerminalPatternResolution
  | .or left right =>
      .or left.toTerminalPatternResolution
        right.toTerminalPatternResolution
  | .app lookup children instanceTyping =>
      .app lookup children.toTerminalPatternResolutions instanceTyping

/-- List forgetful map for coherent terminal patterns. -/
def CoherentTerminalPatternResolutions.toTerminalPatternResolutions
    {signature prevailing context parameters bindings patterns duals result}
    (derivation : CoherentTerminalPatternResolutions signature prevailing context
      parameters bindings patterns duals result) :
    TerminalPatternResolutions signature prevailing context parameters bindings
      patterns duals result :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons head.toTerminalPatternResolution
        tail.toTerminalPatternResolutions

end

/-- Forget coherence at the resolved-pattern boundary. -/
def CoherentResolvedPatternTy.toResolvedPatternTy
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : CoherentResolvedPatternTy signature prevailing context
      parameters bindings pattern capability target result) :
    ResolvedPatternTy signature prevailing context parameters bindings pattern
      capability target result :=
  match derivation with
  | .ofAligned aligned => .ofAligned aligned
  | .ofTerminal terminal =>
      .ofTerminal terminal.toTerminalPatternResolution

mutual

/-- Reconstruction evidence retains the full top-level raw provenance required
by the threaded surface boundary. -/
def PatternResolutionDeriv.toThreadedSurface
    {signature prevailing rawContext rawParameters rawBindings pattern capability
     target rawResult}
    (derivation : PatternResolutionDeriv signature prevailing rawContext
      rawParameters rawBindings pattern capability target rawResult) :
    ThreadedPatternResolution signature prevailing rawContext rawParameters
      rawBindings pattern capability target rawResult :=
  match derivation with
  | .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | .wild freshCap freshTy =>
      .wild freshCap freshTy
  | .pval freshCap separate expressionTyping =>
      .pval freshCap separate expressionTyping.toHasTy
  | .embed rawLookup actualLookup =>
      .embed rawLookup actualLookup
  | .tuple children =>
      .tuple (PatternResolutionsDeriv.toThreadedSurface children)
  | .ctor lookup children compatible instanceTyping =>
      .ctor lookup (PatternResolutionsDeriv.toThreadedSurface children)
        compatible instanceTyping
  | .and left right =>
      .and (PatternResolutionDeriv.toThreadedSurface left)
        (PatternResolutionDeriv.toThreadedSurface right)
  | .or left right =>
      .or (PatternResolutionDeriv.toThreadedSurface left)
        (PatternResolutionDeriv.toThreadedSurface right)
  | .app lookup children instanceTyping =>
      .app lookup (PatternResolutionsDeriv.toThreadedSurface children)
        instanceTyping

/-- List reconstruction retains the same left-to-right raw binding thread. -/
def PatternResolutionsDeriv.toThreadedSurface
    {signature prevailing rawContext rawParameters rawBindings patterns duals
     rawResult}
    (derivation : PatternResolutionsDeriv signature prevailing rawContext
      rawParameters rawBindings patterns duals rawResult) :
    ThreadedPatternResolutions signature prevailing rawContext rawParameters
      rawBindings patterns duals rawResult :=
  match derivation with
  | .nil => .nil
  | .cons head tail =>
      .cons (PatternResolutionDeriv.toThreadedSurface head)
        (PatternResolutionsDeriv.toThreadedSurface tail)

end

/-- Apply the threaded raw indices to obtain the existing coherent terminal
surface view. -/
def PatternResolutionDeriv.toCoherentSurface
    {signature prevailing rawContext rawParameters rawBindings pattern capability
     target rawResult}
    (derivation : PatternResolutionDeriv signature prevailing rawContext
      rawParameters rawBindings pattern capability target rawResult) :
    CoherentTerminalPatternResolution signature prevailing
      (rawContext.applySubst prevailing)
      (rawParameters.applySubst prevailing)
      (rawBindings.applySubst prevailing) pattern capability target
      (rawResult.applySubst prevailing) :=
  ThreadedPatternResolution.toCoherentSurface
    (PatternResolutionDeriv.toThreadedSurface derivation)

/-- List form of the reconstruction-to-coherent-terminal map. -/
def PatternResolutionsDeriv.toCoherentSurface
    {signature prevailing rawContext rawParameters rawBindings patterns duals
     rawResult}
    (derivation : PatternResolutionsDeriv signature prevailing rawContext
      rawParameters rawBindings patterns duals rawResult) :
    CoherentTerminalPatternResolutions signature prevailing
      (rawContext.applySubst prevailing)
      (rawParameters.applySubst prevailing)
      (rawBindings.applySubst prevailing) patterns duals
      (rawResult.applySubst prevailing) :=
  ThreadedPatternResolutions.toCoherentSurface
    (PatternResolutionsDeriv.toThreadedSurface derivation)

/-- Resolved reconstruction evidence lands in the coherent resolved surface
boundary, ready for a future coherent `T-MATCHALL` judgment. -/
def ResolvedPatternDeriv.toCoherentSurface
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : ResolvedPatternDeriv signature prevailing context parameters
      bindings pattern capability target result) :
    CoherentResolvedPatternTy signature prevailing context parameters bindings
      pattern capability target result :=
  match derivation with
  | .ofThreaded terminal =>
      .ofTerminal (PatternResolutionDeriv.toCoherentSurface terminal)

end CoherentSurface
end TypePM
