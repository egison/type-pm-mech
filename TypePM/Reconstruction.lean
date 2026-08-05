import TypePM.InferenceHistory

/-!
# Proof-relevant reconstruction after executable type inference

This module keeps successful inference evidence separate from the declarative
source judgments.  The mutually inductive family below mirrors every source
form, but no constructor stores `HasTy`, `PatternTy`, `PPatTy`, `DPatTy`, or
`ClauseTy`.  The final section is the only forgetful map into those judgments.

In particular, variable and pattern-function reconstruction consumes the
terminal binder-local `ValueFlowInst` evidence produced by the finite trace
validator.  Quantified capability variables therefore remain variables and
cannot be structurally strengthened.
-/

namespace TypePM
namespace Inference
namespace Reconstruction

mutual

/-- Reconstructed expression typing. -/
inductive ExprDeriv (signature : FrozenSig) : Context -> Expr -> Ty -> Prop where
  | var {context name scheme target} :
      context.find? name = some scheme ->
      scheme.ValueFlowInst target ->
      ExprDeriv signature context (.var name) target
  | lam {context name body domain codomain} :
      ExprDeriv signature ((name, Scheme.mono domain) :: context) body codomain ->
      ExprDeriv signature context (.lam name body) (.fn domain codomain)
  | app {context function argument domain codomain} :
      ExprDeriv signature context function (.fn domain codomain) ->
      ExprDeriv signature context argument domain ->
      ExprDeriv signature context (.app function argument) codomain
  | letE {context name value body valueTy bodyTy} :
      ExprDeriv signature context value valueTy ->
      ExprDeriv signature
        ((name, signature.generalize context valueTy) :: context) body bodyTy ->
      ExprDeriv signature context (.letE name value body) bodyTy
  | fixE {context self argument body domain codomain} :
      ExprDeriv signature
        ((argument, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: context)
        body codomain ->
      ExprDeriv signature context (.fix self argument body) (.fn domain codomain)
  | lit {context value} :
      ExprDeriv signature context (.lit value) .int
  | tuple {context expressions targets} :
      ExprsDeriv signature context expressions targets ->
      ExprDeriv signature context (.tuple expressions) (.prod targets)
  | ctor {context name expressions targets result scheme} :
      signature.findDataCtor name = some scheme ->
      scheme.Inst targets result ->
      ExprsDeriv signature context expressions targets ->
      ExprDeriv signature context (.ctor name expressions) result
  | prim {context op expressions targets result scheme} :
      signature.findPrimitive op = some scheme ->
      scheme.Inst targets result ->
      ExprsDeriv signature context expressions targets ->
      ExprDeriv signature context (.prim op expressions) result
  | something {context target} :
      ExprDeriv signature context .something (.matcher .none target)
  | matchAll
      {prevailing context target matcher pattern body targetTy patternCap
       bindings result} :
      ExprDeriv signature context target targetTy ->
      ResolvedPatternDeriv signature prevailing context [] [] pattern
        patternCap targetTy bindings ->
      ExprDeriv signature context matcher (.slot patternCap targetTy) ->
      ExprDeriv signature (bindings.toContext ++ context) body result ->
      ExprDeriv signature context (.matchAll target matcher pattern body)
        (Ty.listT result)
  | matcher {context clauses target capability evidence} :
      ResolvedClausesDeriv signature context clauses capability target evidence ->
      Shape.inferShape signature.observability evidence = some capability ->
      CatchAllLast clauses ->
      ArmExhaustive signature clauses target ->
      PPBindNodup clauses ->
      ArmBindNodup clauses ->
      CoverageOK signature.toMatcherSig clauses capability ->
      ExprDeriv signature context (.matcher clauses)
        (.matcher capability target)
  | coerceMatcherToSlot
      {context expression producerCap producerTarget consumerCap consumerTarget
       bindings C T post} :
      ExprDeriv signature context expression
        (.matcher ((producerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply producerTarget))) ->
      MatcherToSlotRawCert producerCap consumerCap producerTarget
        consumerTarget bindings C T ->
      VariablePost post ->
      ExprDeriv signature context expression
        (.slot ((consumerCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply consumerTarget)))
  | checkSlotToSlot
      {context expression sourceCap sourceTarget requestedCap requestedTarget C T
       post} :
      ExprDeriv signature context expression
        (.slot ((sourceCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply sourceTarget))) ->
      SlotToSlotRawCert sourceCap requestedCap sourceTarget requestedTarget
        C T ->
      VariablePost post ->
      ExprDeriv signature context expression
        (.slot ((requestedCap.apply C).apply post.cap)
          (post.apply ((Subst.mk C T).apply requestedTarget)))
  | coerceTupleMatcher {context expressions} {duals : List Dual} :
      ExprsDeriv signature context expressions
        (duals.map fun dual => .matcher dual.cap dual.target) ->
      ExprDeriv signature context (.tuple expressions)
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  | coerceSlotTuple {context expression} {duals : List Dual} :
      ExprDeriv signature context expression
        (.prod (duals.map fun dual => .slot dual.cap dual.target)) ->
      ExprDeriv signature context expression
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- Reconstructed expression-list typing. -/
inductive ExprsDeriv (signature : FrozenSig) :
    Context -> List Expr -> List Ty -> Prop where
  | nil {context} : ExprsDeriv signature context [] []
  | cons {context expression target expressions targets} :
      ExprDeriv signature context expression target ->
      ExprsDeriv signature context expressions targets ->
      ExprsDeriv signature context (expression :: expressions)
        (target :: targets)

/-- Reconstructed user-pattern typing. -/
inductive PatternDeriv (signature : FrozenSig) :
    Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty -> MonoCtx -> Prop where
  | pvar {context parameters bindings name capVar tyVar} :
      name ∉ bindings.names ->
      FreshCap signature context parameters bindings capVar ->
      FreshTy signature context parameters bindings tyVar ->
      PatternDeriv signature context parameters bindings (.pvar name)
        (.var capVar) (.var tyVar) (bindings ++ [(name, .var tyVar)])
  | wild {context parameters bindings capVar tyVar} :
      FreshCap signature context parameters bindings capVar ->
      FreshTy signature context parameters bindings tyVar ->
      PatternDeriv signature context parameters bindings .wild
        (.var capVar) (.var tyVar) bindings
  | pval {context parameters bindings expression target capVar} :
      ExprDeriv signature (bindings.toContext ++ context) expression target ->
      FreshCap signature context parameters bindings capVar ->
      capVar ∉ target.fcv ->
      PatternDeriv signature context parameters bindings (.pval expression)
        (.var capVar) target bindings
  | embed {context parameters bindings name dual} :
      parameters.find? name = some dual ->
      PatternDeriv signature context parameters bindings (.embed name)
        dual.cap dual.target bindings
  | tuple {context parameters bindings patterns duals resultBindings} :
      PatternsDeriv signature context parameters bindings
        patterns duals resultBindings ->
      PatternDeriv signature context parameters bindings (.ptuple patterns)
        (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))
        resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry ->
      PatternsDeriv signature context parameters bindings
        patterns duals resultBindings ->
      entry.CapCompatible (duals.map Dual.cap) result.cap ->
      entry.Inst (duals.map Dual.target) result.target ->
      PatternDeriv signature context parameters bindings (.pctor name patterns)
        result.cap result.target resultBindings
  | and {context parameters bindings left right cap target middle result} :
      PatternDeriv signature context parameters bindings left cap target middle ->
      PatternDeriv signature context parameters middle right cap target result ->
      PatternDeriv signature context parameters bindings (.pand left right)
        cap target result
  | or {context parameters bindings left right cap target result} :
      PatternDeriv signature context parameters bindings left cap target result ->
      PatternDeriv signature context parameters bindings right cap target result ->
      PatternDeriv signature context parameters bindings (.por left right)
        cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme ->
      PatternsDeriv signature context parameters bindings
        patterns duals resultBindings ->
      scheme.ValueFlowInst duals result ->
      PatternDeriv signature context parameters bindings (.papp name patterns)
        result.cap result.target resultBindings

/-- Reconstructed left-to-right user-pattern list. -/
inductive PatternsDeriv (signature : FrozenSig) :
    Context -> PatternCtx -> MonoCtx -> List Pattern -> List Dual ->
      MonoCtx -> Prop where
  | nil {context parameters bindings} :
      PatternsDeriv signature context parameters bindings [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle
       patterns duals result} :
      PatternDeriv signature context parameters bindings
        pattern cap target middle ->
      PatternsDeriv signature context parameters middle patterns duals result ->
      PatternsDeriv signature context parameters bindings
        (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/-- Reconstructed primitive-pattern typing before shared resolution. -/
inductive PPatDeriv (signature : FrozenSig) :
    PPat -> Ty -> List Dual -> MonoCtx -> Prop where
  | hole {target varId} :
      signature.FreshCapFor varId target ->
      PPatDeriv signature .hole target [⟨Cap.var varId, target⟩] []
  | wild {target} : PPatDeriv signature .wild target [] []
  | pval {name target} :
      PPatDeriv signature (.pval name) target [] [(name, target)]
  | ctor {name entry patterns targets result holes bindings} :
      signature.findPatternCtor name = some entry ->
      PPatsDeriv signature patterns targets holes bindings ->
      entry.Inst targets result ->
      PPatDeriv signature (.ctor name patterns) result holes bindings
  | tuple {patterns targets holes bindings} :
      PPatsDeriv signature patterns targets holes bindings ->
      PPatDeriv signature (.tuple patterns) (.prod targets) holes bindings

/-- Reconstructed primitive-pattern list. -/
inductive PPatsDeriv (signature : FrozenSig) :
    List PPat -> List Ty -> List Dual -> MonoCtx -> Prop where
  | nil : PPatsDeriv signature [] [] [] []
  | cons {pattern target holes bindings patterns targets restHoles restBindings} :
      PPatDeriv signature pattern target holes bindings ->
      PPatsDeriv signature patterns targets restHoles restBindings ->
      (∀ name, name ∈ bindings.names -> name ∉ restBindings.names) ->
      PPatsDeriv signature (pattern :: patterns) (target :: targets)
        (holes ++ restHoles) (bindings ++ restBindings)

/-- Actual-indexed primitive-pattern reconstruction under one terminal
prevailing substitution.  Fresh leaves retain their raw allocation origin;
compound nodes are indexed only by their terminal children. -/
inductive PPatResolutionDeriv (signature : FrozenSig) :
    Subst -> PPat -> Ty -> List Dual -> MonoCtx -> Prop where
  | hole {rawTarget varId} :
      signature.FreshCapFor varId rawTarget ->
      PPatResolutionDeriv signature prevailing .hole
        (prevailing.apply rawTarget)
        ([⟨Cap.var varId, rawTarget⟩].map (Dual.applySubst prevailing)) []
  | wild {rawTarget} :
      PPatResolutionDeriv signature prevailing .wild
        (prevailing.apply rawTarget) [] []
  | pval {name rawTarget} :
      PPatResolutionDeriv signature prevailing (.pval name)
        (prevailing.apply rawTarget) []
        (MonoCtx.applySubst prevailing [(name, rawTarget)])
  | ctor {name entry patterns targets result holes bindings} :
      signature.findPatternCtor name = some entry ->
      PPatResolutionsDeriv signature prevailing patterns targets holes
        bindings ->
      entry.Inst targets result ->
      PPatResolutionDeriv signature prevailing (.ctor name patterns) result
        holes bindings
  | tuple {patterns targets holes bindings} :
      PPatResolutionsDeriv signature prevailing patterns targets holes
        bindings ->
      PPatResolutionDeriv signature prevailing (.tuple patterns)
        (.prod targets) holes bindings

/-- List form of aligned primitive-pattern reconstruction. -/
inductive PPatResolutionsDeriv (signature : FrozenSig) :
    Subst -> List PPat -> List Ty -> List Dual -> MonoCtx -> Prop where
  | nil : PPatResolutionsDeriv signature prevailing [] [] [] []
  | cons
      {pattern target holes bindings patterns targets restHoles restBindings} :
      PPatResolutionDeriv signature prevailing pattern target holes bindings ->
      PPatResolutionsDeriv signature prevailing patterns targets restHoles
        restBindings ->
      (∀ name, name ∈ bindings.names -> name ∉ restBindings.names) ->
      PPatResolutionsDeriv signature prevailing (pattern :: patterns)
        (target :: targets) (holes ++ restHoles) (bindings ++ restBindings)

/-- Reconstructed primitive pattern under one occurrence-wide substitution. -/
inductive ResolvedPPatDeriv (signature : FrozenSig) :
    Subst -> PPat -> Ty -> List Dual -> MonoCtx -> Prop where
  | ofTerminal {pattern target holes bindings} :
      PPatResolutionDeriv signature prevailing pattern target holes bindings ->
      ResolvedPPatDeriv signature prevailing pattern target holes bindings

/-- Reconstructed primitive data-pattern typing. -/
inductive DPatDeriv (signature : FrozenSig) :
    DPat -> Ty -> MonoCtx -> Prop where
  | var {name target} :
      DPatDeriv signature (.var name) target [(name, target)]
  | wild {target} : DPatDeriv signature .wild target []
  | ctor {name scheme patterns targets result bindings} :
      signature.findDataCtor name = some scheme ->
      DPatsDeriv signature patterns targets bindings ->
      scheme.Inst targets result ->
      DPatDeriv signature (.ctor name patterns) result bindings
  | tuple {patterns targets bindings} :
      DPatsDeriv signature patterns targets bindings ->
      DPatDeriv signature (.tuple patterns) (.prod targets) bindings

/-- Reconstructed primitive data-pattern list. -/
inductive DPatsDeriv (signature : FrozenSig) :
    List DPat -> List Ty -> MonoCtx -> Prop where
  | nil : DPatsDeriv signature [] [] []
  | cons {pattern target bindings patterns targets restBindings} :
      DPatDeriv signature pattern target bindings ->
      DPatsDeriv signature patterns targets restBindings ->
      (∀ name, name ∈ bindings.names -> name ∉ restBindings.names) ->
      DPatsDeriv signature (pattern :: patterns) (target :: targets)
        (bindings ++ restBindings)

/-- Actual-indexed user-pattern reconstruction under one terminal prevailing
substitution.  This is the proof-relevant counterpart of
`TerminalPatternResolution`, without storing a source judgment. -/
inductive PatternResolutionDeriv (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | pvar {rawContext rawParameters rawBindings name capVar tyVar} :
      name ∉ rawBindings.names ->
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      PatternResolutionDeriv signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.pvar name)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        ((rawBindings ++ [(name, Ty.var tyVar)]).applySubst prevailing)
  | wild {rawContext rawParameters rawBindings capVar tyVar} :
      FreshCap signature rawContext rawParameters rawBindings capVar ->
      FreshTy signature rawContext rawParameters rawBindings tyVar ->
      PatternResolutionDeriv signature prevailing
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
      ExprDeriv signature
        ((rawBindings.applySubst prevailing).toContext ++
          rawContext.applySubst prevailing)
        expression (prevailing.apply rawTarget) ->
      PatternResolutionDeriv signature prevailing
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
      PatternResolutionDeriv signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.embed name)
        (rawDual.cap.apply prevailing.cap)
        (prevailing.apply rawDual.target)
        (rawBindings.applySubst prevailing)
  | tuple {context parameters bindings patterns duals resultBindings} :
      PatternResolutionsDeriv signature prevailing context parameters bindings
        patterns duals resultBindings ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry ->
      PatternResolutionsDeriv signature prevailing context parameters bindings
        patterns duals resultBindings ->
      entry.CapCompatible (duals.map Dual.cap) result.cap ->
      entry.Inst (duals.map Dual.target) result.target ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        (.pctor name patterns) result.cap result.target resultBindings
  | and {context parameters bindings left right cap target middle result} :
      PatternResolutionDeriv signature prevailing context parameters bindings
        left cap target middle ->
      PatternResolutionDeriv signature prevailing context parameters middle
        right cap target result ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        (.pand left right) cap target result
  | or {context parameters bindings left right cap target result} :
      PatternResolutionDeriv signature prevailing context parameters bindings
        left cap target result ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        right cap target result ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        (.por left right) cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme ->
      PatternResolutionsDeriv signature prevailing context parameters bindings
        patterns duals resultBindings ->
      scheme.ValueFlowInst duals result ->
      PatternResolutionDeriv signature prevailing context parameters bindings
        (.papp name patterns) result.cap result.target resultBindings

/-- Left-to-right aligned user-pattern list reconstruction. -/
inductive PatternResolutionsDeriv (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> List Pattern -> List Dual ->
      MonoCtx -> Prop where
  | nil {context parameters bindings} :
      PatternResolutionsDeriv signature prevailing context parameters bindings
        [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle patterns duals
       result} :
      PatternResolutionDeriv signature prevailing context parameters bindings
        pattern cap target middle ->
      PatternResolutionsDeriv signature prevailing context parameters middle
        patterns duals result ->
      PatternResolutionsDeriv signature prevailing context parameters bindings
        (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/-- Reconstructed user pattern under one occurrence-wide substitution. -/
inductive ResolvedPatternDeriv (signature : FrozenSig) :
    Subst -> Context -> PatternCtx -> MonoCtx -> Pattern -> Cap -> Ty ->
      MonoCtx -> Prop where
  | ofTerminal
      {context parameters bindings pattern capability target resultBindings} :
      PatternResolutionDeriv signature prevailing context parameters bindings
        pattern capability target resultBindings ->
      ResolvedPatternDeriv signature prevailing context parameters bindings
        pattern capability target resultBindings

/-- Reconstructed matcher arm. -/
inductive ArmDeriv (signature : FrozenSig) :
    Context -> Ty -> MonoCtx -> Ty -> Arm -> Prop where
  | mk {context target ppBindings result pattern body armBindings} :
      DPatDeriv signature pattern target armBindings ->
      ExprDeriv signature
        (armBindings.toContext ++ ppBindings.toContext ++ context)
        body result ->
      ArmDeriv signature context target ppBindings result (.mk pattern body)

/-- Reconstructed matcher arm list. -/
inductive ArmsDeriv (signature : FrozenSig) :
    Context -> Ty -> MonoCtx -> Ty -> List Arm -> Prop where
  | nil {context target ppBindings result} :
      ArmsDeriv signature context target ppBindings result []
  | cons {context target ppBindings result arm arms} :
      ArmDeriv signature context target ppBindings result arm ->
      ArmsDeriv signature context target ppBindings result arms ->
      ArmsDeriv signature context target ppBindings result (arm :: arms)

/-- Reconstructed actual clause under its shared prevailing substitution. -/
inductive ClauseDeriv (signature : FrozenSig) :
    Subst -> Context -> Clause -> Cap -> Ty -> Shape.Evidence -> Prop where
  | mk {context capability target pp next arms holes ppBindings nextMatchers
        evidence} :
      PPatCoreOrder pp ->
      ResolvedPPatDeriv signature prevailing pp target holes ppBindings ->
      PPatCapsAt signature true pp (holes.map Dual.cap) capability ->
      decomposeME next holes.length = some nextMatchers ->
      ExprsDeriv signature context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) ->
      ArmsDeriv signature context target ppBindings
        (Ty.listT (prodTy (holes.map Dual.target))) arms ->
      clauseEvidence signature.toMatcherSig pp (holes.map Dual.cap) =
        some evidence ->
      ClauseDeriv signature prevailing context (.mk pp next arms)
        capability target evidence

/-- Reconstructed clause list with one shared prevailing substitution. -/
inductive ClausesDeriv (signature : FrozenSig) :
    Subst -> Context -> List Clause -> Cap -> Ty -> List Shape.Evidence -> Prop where
  | nil {context target} :
      ClausesDeriv signature prevailing context [] capability target []
  | cons {context clause clauses target evidence evidences} :
      ClauseDeriv signature prevailing context clause capability target evidence ->
      ClausesDeriv signature prevailing context clauses capability target
        evidences ->
      ClausesDeriv signature prevailing context (clause :: clauses) capability
        target (evidence :: evidences)

/-- Existential package of the reconstructed shared clause substitution. -/
inductive ResolvedClausesDeriv (signature : FrozenSig) :
    Context -> List Clause -> Cap -> Ty -> List Shape.Evidence -> Prop where
  | ofShared {prevailing context clauses capability target evidence} :
      ClausesDeriv signature prevailing context clauses capability target
        evidence ->
      ResolvedClausesDeriv signature context clauses capability target evidence

end


/-! ## Forgetful soundness map -/


syntax "solve_reconstruction_with " term ", " term ", " term : tactic

macro_rules
  | `(tactic| solve_reconstruction_with $recursor, $signature, $derivation) =>
      `(tactic|
        apply $recursor
          (motive_1 := fun context expression target _ =>
            HasTy $signature context expression target)
          (motive_2 := fun context expressions targets _ =>
            ExprsTy $signature context expressions targets)
          (motive_3 := fun context parameters bindings pattern capability target
              result _ =>
            PatternTy $signature context parameters bindings pattern capability
              target result)
          (motive_4 := fun context parameters bindings patterns duals result _ =>
            PatternTys $signature context parameters bindings patterns duals result)
          (motive_5 := fun pattern target holes bindings _ =>
            PPatTy $signature pattern target holes bindings)
          (motive_6 := fun patterns targets holes bindings _ =>
            PPatTys $signature patterns targets holes bindings)
          (motive_7 := fun prevailing pattern target holes bindings _ =>
            TerminalPPatResolution $signature prevailing pattern target holes
              bindings)
          (motive_8 := fun prevailing patterns targets holes bindings _ =>
            TerminalPPatResolutions $signature prevailing patterns targets holes
              bindings)
          (motive_9 := fun prevailing pattern target holes bindings _ =>
            ResolvedPPatTy $signature prevailing pattern target holes bindings)
          (motive_10 := fun pattern target bindings _ =>
            DPatTy $signature pattern target bindings)
          (motive_11 := fun patterns targets bindings _ =>
            DPatTys $signature patterns targets bindings)
          (motive_12 := fun prevailing context parameters bindings pattern
              capability target result _ =>
            TerminalPatternResolution $signature prevailing context parameters
              bindings pattern capability target result)
          (motive_13 := fun prevailing context parameters bindings patterns duals
              result _ =>
            TerminalPatternResolutions $signature prevailing context parameters
              bindings patterns duals result)
          (motive_14 := fun prevailing context parameters bindings pattern
              capability target result _ =>
            ResolvedPatternTy $signature prevailing context parameters bindings
              pattern capability target result)
          (motive_15 := fun context target ppBindings result arm _ =>
            ArmTy $signature context target ppBindings result arm)
          (motive_16 := fun context target ppBindings result arms _ =>
            ArmsTy $signature context target ppBindings result arms)
          (motive_17 := fun prevailing context clause capability target
              evidence _ =>
            ClauseTy $signature prevailing context clause capability target
              evidence)
          (motive_18 := fun prevailing context clauses capability target
              evidence _ =>
            ClausesTy $signature prevailing context clauses capability target
              evidence)
          (motive_19 := fun context clauses capability target evidence _ =>
            ResolvedClausesTy $signature context clauses capability target
              evidence)
          (t := $derivation))

/-- Uniform constructor discharge for the combined reconstruction recursor.
Resolved-evidence constructors are tried before their generic `ofRaw`
inclusions, which prevents raw freshness premises from being invented. -/
syntax "finish_reconstruction" : tactic

macro_rules
  | `(tactic| finish_reconstruction) =>
      `(tactic|
        all_goals intros <;>
        first
          | apply HasTy.checkSlotToSlot <;> assumption
          | apply TerminalPPatResolution.hole <;> assumption
          | exact TerminalPPatResolution.wild
          | exact TerminalPPatResolution.pval
          | apply TerminalPPatResolution.ctor <;> assumption
          | apply TerminalPPatResolution.tuple <;> assumption
          | exact TerminalPPatResolutions.nil
          | apply TerminalPPatResolutions.cons <;> assumption
          | apply TerminalPatternResolution.pvar <;> assumption
          | apply TerminalPatternResolution.wild <;> assumption
          | apply TerminalPatternResolution.pval <;> assumption
          | apply TerminalPatternResolution.embed <;> assumption
          | apply TerminalPatternResolution.tuple <;> assumption
          | apply TerminalPatternResolution.ctor <;> assumption
          | apply TerminalPatternResolution.and <;> assumption
          | apply TerminalPatternResolution.or <;> assumption
          | apply TerminalPatternResolution.app <;> assumption
          | exact TerminalPatternResolutions.nil
          | apply TerminalPatternResolutions.cons <;> assumption
          | apply ResolvedPPatTy.ofTerminal <;> assumption
          | apply ResolvedPatternTy.ofTerminal <;> assumption
          | apply ResolvedClausesTy.ofShared <;> assumption
          | constructor <;> assumption)

/-- The combined mutual recursor discharges every recursive source premise. -/
theorem ExprDeriv.toHasTy
    {signature context expression target}
    (derivation : ExprDeriv signature context expression target) :
    HasTy signature context expression target := by
  apply ExprDeriv.rec
    (motive_1 := fun context expression target _ =>
      HasTy signature context expression target)
    (motive_2 := fun context expressions targets _ =>
      ExprsTy signature context expressions targets)
    (motive_3 := fun context parameters bindings pattern capability target
        result _ =>
      PatternTy signature context parameters bindings pattern capability target
        result)
    (motive_4 := fun context parameters bindings patterns duals result _ =>
      PatternTys signature context parameters bindings patterns duals result)
    (motive_5 := fun pattern target holes bindings _ =>
      PPatTy signature pattern target holes bindings)
    (motive_6 := fun patterns targets holes bindings _ =>
      PPatTys signature patterns targets holes bindings)
    (motive_7 := fun prevailing pattern target holes bindings _ =>
      TerminalPPatResolution signature prevailing pattern target holes bindings)
    (motive_8 := fun prevailing patterns targets holes bindings _ =>
      TerminalPPatResolutions signature prevailing patterns targets holes
        bindings)
    (motive_9 := fun prevailing pattern target holes bindings _ =>
      ResolvedPPatTy signature prevailing pattern target holes bindings)
    (motive_10 := fun pattern target bindings _ =>
      DPatTy signature pattern target bindings)
    (motive_11 := fun patterns targets bindings _ =>
      DPatTys signature patterns targets bindings)
    (motive_12 := fun prevailing context parameters bindings pattern capability
        target result _ =>
      TerminalPatternResolution signature prevailing context parameters bindings
        pattern capability target result)
    (motive_13 := fun prevailing context parameters bindings patterns duals
        result _ =>
      TerminalPatternResolutions signature prevailing context parameters bindings
        patterns duals result)
    (motive_14 := fun prevailing context parameters bindings pattern capability
        target result _ =>
      ResolvedPatternTy signature prevailing context parameters bindings pattern
        capability target result)
    (motive_15 := fun context target ppBindings result arm _ =>
      ArmTy signature context target ppBindings result arm)
    (motive_16 := fun context target ppBindings result arms _ =>
      ArmsTy signature context target ppBindings result arms)
    (motive_17 := fun prevailing context clause capability target evidence _ =>
      ClauseTy signature prevailing context clause capability target evidence)
    (motive_18 := fun prevailing context clauses capability target evidence _ =>
      ClausesTy signature prevailing context clauses capability target evidence)
    (motive_19 := fun context clauses capability target evidence _ =>
      ResolvedClausesTy signature context clauses capability target evidence)
    (t := derivation)
  finish_reconstruction

theorem ExprsDeriv.toExprsTy
    {signature context expressions targets}
    (derivation : ExprsDeriv signature context expressions targets) :
    ExprsTy signature context expressions targets := by
  solve_reconstruction_with ExprsDeriv.rec, signature, derivation
  finish_reconstruction

theorem PatternDeriv.toPatternTy
    {signature context parameters bindings pattern capability target result}
    (derivation : PatternDeriv signature context parameters bindings pattern
      capability target result) :
    PatternTy signature context parameters bindings pattern capability target
      result := by
  solve_reconstruction_with PatternDeriv.rec, signature, derivation
  finish_reconstruction

theorem PatternsDeriv.toPatternTys
    {signature context parameters bindings patterns duals result}
    (derivation : PatternsDeriv signature context parameters bindings patterns
      duals result) :
    PatternTys signature context parameters bindings patterns duals result := by
  solve_reconstruction_with PatternsDeriv.rec, signature, derivation
  finish_reconstruction

theorem PPatDeriv.toPPatTy
    {signature pattern target holes bindings}
    (derivation : PPatDeriv signature pattern target holes bindings) :
    PPatTy signature pattern target holes bindings := by
  solve_reconstruction_with PPatDeriv.rec, signature, derivation
  finish_reconstruction

theorem PPatsDeriv.toPPatTys
    {signature patterns targets holes bindings}
    (derivation : PPatsDeriv signature patterns targets holes bindings) :
    PPatTys signature patterns targets holes bindings := by
  solve_reconstruction_with PPatsDeriv.rec, signature, derivation
  finish_reconstruction

theorem PPatResolutionDeriv.toTerminalPPatResolution
    {signature prevailing pattern target holes bindings}
    (derivation :
      PPatResolutionDeriv signature prevailing pattern target holes bindings) :
    TerminalPPatResolution signature prevailing pattern target holes bindings := by
  solve_reconstruction_with PPatResolutionDeriv.rec, signature, derivation
  finish_reconstruction

theorem PPatResolutionsDeriv.toTerminalPPatResolutions
    {signature prevailing patterns targets holes bindings}
    (derivation :
      PPatResolutionsDeriv signature prevailing patterns targets holes bindings) :
    TerminalPPatResolutions signature prevailing patterns targets holes
      bindings := by
  solve_reconstruction_with PPatResolutionsDeriv.rec, signature, derivation
  finish_reconstruction

theorem ResolvedPPatDeriv.toResolvedPPatTy
    {signature prevailing pattern target holes bindings}
    (derivation :
      ResolvedPPatDeriv signature prevailing pattern target holes bindings) :
    ResolvedPPatTy signature prevailing pattern target holes bindings := by
  solve_reconstruction_with ResolvedPPatDeriv.rec, signature, derivation
  finish_reconstruction

theorem DPatDeriv.toDPatTy
    {signature pattern target bindings}
    (derivation : DPatDeriv signature pattern target bindings) :
    DPatTy signature pattern target bindings := by
  solve_reconstruction_with DPatDeriv.rec, signature, derivation
  finish_reconstruction

theorem DPatsDeriv.toDPatTys
    {signature patterns targets bindings}
    (derivation : DPatsDeriv signature patterns targets bindings) :
    DPatTys signature patterns targets bindings := by
  solve_reconstruction_with DPatsDeriv.rec, signature, derivation
  finish_reconstruction

theorem PatternResolutionDeriv.toTerminalPatternResolution
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : PatternResolutionDeriv signature prevailing context parameters
      bindings pattern capability target result) :
    TerminalPatternResolution signature prevailing context parameters bindings
      pattern capability target result := by
  solve_reconstruction_with PatternResolutionDeriv.rec, signature, derivation
  finish_reconstruction

theorem PatternResolutionsDeriv.toTerminalPatternResolutions
    {signature prevailing context parameters bindings patterns duals result}
    (derivation : PatternResolutionsDeriv signature prevailing context parameters
      bindings patterns duals result) :
    TerminalPatternResolutions signature prevailing context parameters bindings
      patterns duals result := by
  solve_reconstruction_with PatternResolutionsDeriv.rec, signature, derivation
  finish_reconstruction

theorem ResolvedPatternDeriv.toResolvedPatternTy
    {signature prevailing context parameters bindings pattern capability target
     result}
    (derivation : ResolvedPatternDeriv signature prevailing context parameters
      bindings pattern capability target result) :
    ResolvedPatternTy signature prevailing context parameters bindings pattern
      capability target result := by
  solve_reconstruction_with ResolvedPatternDeriv.rec, signature, derivation
  finish_reconstruction

theorem ArmDeriv.toArmTy
    {signature context target ppBindings result arm}
    (derivation : ArmDeriv signature context target ppBindings result arm) :
    ArmTy signature context target ppBindings result arm := by
  solve_reconstruction_with ArmDeriv.rec, signature, derivation
  finish_reconstruction

theorem ArmsDeriv.toArmsTy
    {signature context target ppBindings result arms}
    (derivation : ArmsDeriv signature context target ppBindings result arms) :
    ArmsTy signature context target ppBindings result arms := by
  solve_reconstruction_with ArmsDeriv.rec, signature, derivation
  finish_reconstruction

theorem ClauseDeriv.toClauseTy
    {signature prevailing context clause capability target evidence}
    (derivation : ClauseDeriv signature prevailing context clause capability
      target evidence) :
    ClauseTy signature prevailing context clause capability target evidence := by
  solve_reconstruction_with ClauseDeriv.rec, signature, derivation
  finish_reconstruction

theorem ClausesDeriv.toClausesTy
    {signature prevailing context clauses capability target evidence}
    (derivation : ClausesDeriv signature prevailing context clauses capability
      target evidence) :
    ClausesTy signature prevailing context clauses capability target evidence := by
  solve_reconstruction_with ClausesDeriv.rec, signature, derivation
  finish_reconstruction

theorem ResolvedClausesDeriv.toResolvedClausesTy
    {signature context clauses capability target evidence}
    (derivation : ResolvedClausesDeriv signature context clauses capability target
      evidence) :
    ResolvedClausesTy signature context clauses capability target evidence := by
  solve_reconstruction_with ResolvedClausesDeriv.rec, signature, derivation
  finish_reconstruction

/-! ## Named algorithmic bridge conditions -/

/-- The stronger all-variable signature audit implies the free-variable
freshness required by the source rules. -/
private theorem frozenSig_fcv_mem_capVars
    {signature : FrozenSig} {varId : CapVar}
    (membership : varId ∈ signature.fcv) :
    varId ∈ signature.capVars := by
  simp only [FrozenSig.fcv, FrozenSig.capVars, List.mem_append,
    List.mem_flatMap] at membership ⊢
  rcases membership with
    ((dataMembership | patternCtorMembership) | patternFunMembership) |
      primitiveMembership
  · rcases dataMembership with ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember,
      CtorScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩))
  · rcases patternCtorMembership with
      ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inl (Or.inr ⟨entry, entryMember,
      CtorScheme.mem_capVars_of_mem_fcv entry.2.scheme variableMember⟩))
  · rcases patternFunMembership with
      ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inr ⟨entry, entryMember,
      DualScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩)
  · rcases primitiveMembership with ⟨entry, entryMember, variableMember⟩
    exact Or.inr ⟨entry, entryMember,
      CtorScheme.mem_capVars_of_mem_fcv entry.2 variableMember⟩

private theorem frozenSig_ftv_mem_tyVars
    {signature : FrozenSig} {varId : TypePM.TyVar}
    (membership : varId ∈ signature.ftv) :
    varId ∈ signature.tyVars := by
  simp only [FrozenSig.ftv, FrozenSig.tyVars, List.mem_append,
    List.mem_flatMap] at membership ⊢
  rcases membership with
    ((dataMembership | patternCtorMembership) | patternFunMembership) |
      primitiveMembership
  · rcases dataMembership with ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inl (Or.inl ⟨entry, entryMember,
      CtorScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩))
  · rcases patternCtorMembership with
      ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inl (Or.inr ⟨entry, entryMember,
      CtorScheme.mem_tyVars_of_mem_ftv entry.2.scheme variableMember⟩))
  · rcases patternFunMembership with
      ⟨entry, entryMember, variableMember⟩
    exact Or.inl (Or.inr ⟨entry, entryMember,
      DualScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩)
  · rcases primitiveMembership with ⟨entry, entryMember, variableMember⟩
    exact Or.inr ⟨entry, entryMember,
      CtorScheme.mem_tyVars_of_mem_ftv entry.2 variableMember⟩

/-- Executable source-freshness audit for primitive holes.  The successful
traversal records the raw target and the exact capability meta in the
`inferredPPat` event, so this check has no declarative judgment as input. -/
def primitiveHoleEventCheck (signature : FrozenSig) : TraceEvent -> Bool
  | .inferredPPat .hole target
      [⟨.var varId, holeTarget⟩] [] _ =>
      decide (holeTarget = target) &&
      decide (varId ∉ signature.capVars) &&
      decide (varId ∉ target.fcv)
  | .inferredPPat .hole _ _ _ _ => false
  | _ => true

def tracePrimitiveHoleCheck
    (signature : FrozenSig) (trace : InferTrace) : Bool :=
  trace.events.all (primitiveHoleEventCheck signature)

theorem tracePrimitiveHoleCheck_hole
    {signature : FrozenSig} {trace : InferTrace}
    (checked : tracePrimitiveHoleCheck signature trace = true)
    {target : Ty} {varId : CapVar} {path : SyntaxPath}
    (membership : .inferredPPat .hole target
      [⟨.var varId, target⟩] [] path ∈ trace.events) :
    signature.FreshCapFor varId target := by
  have accepted := List.all_eq_true.mp checked _ membership
  simp only [primitiveHoleEventCheck, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  have allFresh : varId ∉ signature.capVars := by
    simpa [primitiveHoleEventCheck] using accepted.1
  have targetFresh : varId ∉ target.fcv := by
    simpa [primitiveHoleEventCheck] using accepted.2
  exact ⟨fun freeMembership =>
    allFresh (frozenSig_fcv_mem_capVars freeMembership), targetFresh⟩

/-- Finite freshness checks for the three user-pattern leaf allocations. -/
def patternLeafEventCheck (signature : FrozenSig) : TraceEvent -> Bool
  | .patternVarFresh context parameters bindings capVar tyVar =>
      decide (capVar ∉ signature.capVars) &&
      decide (capVar ∉ context.fcv) &&
      decide (capVar ∉ parameters.fcv) &&
      decide (capVar ∉ bindings.fcv) &&
      decide (tyVar ∉ signature.tyVars) &&
      decide (tyVar ∉ context.ftv) &&
      decide (tyVar ∉ parameters.ftv) &&
      decide (tyVar ∉ bindings.ftv)
  | .patternWildFresh context parameters bindings capVar tyVar =>
      decide (capVar ∉ signature.capVars) &&
      decide (capVar ∉ context.fcv) &&
      decide (capVar ∉ parameters.fcv) &&
      decide (capVar ∉ bindings.fcv) &&
      decide (tyVar ∉ signature.tyVars) &&
      decide (tyVar ∉ context.ftv) &&
      decide (tyVar ∉ parameters.ftv) &&
      decide (tyVar ∉ bindings.ftv)
  | .patternValueFresh context parameters bindings capVar target =>
      decide (capVar ∉ signature.capVars) &&
      decide (capVar ∉ context.fcv) &&
      decide (capVar ∉ parameters.fcv) &&
      decide (capVar ∉ bindings.fcv) &&
      decide (capVar ∉ target.fcv)
  | _ => true

def tracePatternLeafCheck
    (signature : FrozenSig) (trace : InferTrace) : Bool :=
  trace.events.all (patternLeafEventCheck signature)

theorem tracePatternLeafCheck_var
    {signature : FrozenSig} {trace : InferTrace}
    (checked : tracePatternLeafCheck signature trace = true)
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {capVar : CapVar} {tyVar : TypePM.TyVar}
    (membership : .patternVarFresh context parameters bindings capVar tyVar ∈
      trace.events) :
    FreshCap signature context parameters bindings capVar ∧
      FreshTy signature context parameters bindings tyVar := by
  have accepted := List.all_eq_true.mp checked _ membership
  simp only [patternLeafEventCheck, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with
    ⟨⟨⟨⟨⟨⟨⟨capSignature, capContext⟩, capParameters⟩,
      capBindings⟩, tySignature⟩, tyContext⟩, tyParameters⟩, tyBindings⟩
  exact ⟨⟨fun freeMembership =>
      capSignature (frozenSig_fcv_mem_capVars freeMembership),
      capContext, capParameters, capBindings⟩,
    ⟨fun freeMembership =>
      tySignature (frozenSig_ftv_mem_tyVars freeMembership),
      tyContext, tyParameters, tyBindings⟩⟩

theorem tracePatternLeafCheck_wild
    {signature : FrozenSig} {trace : InferTrace}
    (checked : tracePatternLeafCheck signature trace = true)
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {capVar : CapVar} {tyVar : TypePM.TyVar}
    (membership : .patternWildFresh context parameters bindings capVar tyVar ∈
      trace.events) :
    FreshCap signature context parameters bindings capVar ∧
      FreshTy signature context parameters bindings tyVar := by
  have accepted := List.all_eq_true.mp checked _ membership
  simp only [patternLeafEventCheck, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with
    ⟨⟨⟨⟨⟨⟨⟨capSignature, capContext⟩, capParameters⟩,
      capBindings⟩, tySignature⟩, tyContext⟩, tyParameters⟩, tyBindings⟩
  exact ⟨⟨fun freeMembership =>
      capSignature (frozenSig_fcv_mem_capVars freeMembership),
      capContext, capParameters, capBindings⟩,
    ⟨fun freeMembership =>
      tySignature (frozenSig_ftv_mem_tyVars freeMembership),
      tyContext, tyParameters, tyBindings⟩⟩

theorem tracePatternLeafCheck_value
    {signature : FrozenSig} {trace : InferTrace}
    (checked : tracePatternLeafCheck signature trace = true)
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {capVar : CapVar} {target : Ty}
    (membership : .patternValueFresh context parameters bindings capVar target ∈
      trace.events) :
    FreshCap signature context parameters bindings capVar ∧
      capVar ∉ target.fcv := by
  have accepted := List.all_eq_true.mp checked _ membership
  simp only [patternLeafEventCheck, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with
    ⟨⟨⟨⟨capSignature, capContext⟩, capParameters⟩, capBindings⟩,
      separate⟩
  exact ⟨⟨fun freeMembership =>
      capSignature (frozenSig_fcv_mem_capVars freeMembership),
      capContext, capParameters, capBindings⟩, separate⟩

/-- Executable terminal audit for every user-constructor capability event. -/
def tracePatternCtorCheck
    (signature : FrozenSig) (state : InferState) : Bool :=
  state.trace.events.all fun event =>
    match event with
    | .patternCtorCompatibility solveCount name childCaps resultCap =>
        decide (solveCount ≤ state.trace.solves.length) &&
        match signature.findPatternCtor name with
        | none => false
        | some entry =>
            capCompatibleCheck entry
              (childCaps.map fun cap => cap.apply state.prevailing.cap)
              (resultCap.apply state.prevailing.cap)
    | _ => true

theorem tracePatternCtorCheck_final
    {signature : FrozenSig} {state : InferState}
    (checked : tracePatternCtorCheck signature state = true)
    {solveCount : Nat} {name : String} {childCaps : List Cap}
    {resultCap : Cap} {entry : PatternCtorScheme signature.observability}
    (membership : .patternCtorCompatibility solveCount name childCaps
      resultCap ∈ state.trace.events)
    (lookup : signature.findPatternCtor name = some entry) :
    entry.CapCompatible
      (childCaps.map fun cap => cap.apply state.prevailing.cap)
      (resultCap.apply state.prevailing.cap) := by
  have accepted := List.all_eq_true.mp checked _ membership
  simp only [lookup, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  exact capCompatibleCheck_sound accepted.2

/-- Terminal algebraic instances reconstructed from recorded W allocations.

Only the complete reconstruction cut is needed.  A checker may construct the
binder-supported substitutions directly from the recorded incoming supply
and verify their result equations; no condition is imposed at intermediate
solver prefixes.
-/
def TraceInstanceSuffixConditions
    (_signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .schemeInstantiation solveCount _ _scheme name rawContext _context
        _fixedCaps _fixedTys _reservedCaps _reservedTys fresh _capImages
        _tyImages =>
        solveCount ≤ state.trace.solves.length ∧
        ∃ terminalScheme,
          (rawContext.applySubst state.prevailing).find? name =
              some terminalScheme ∧
          terminalScheme.ValueFlowInst (state.prevailing.apply fresh)
    | .dualInstantiation solveCount _ scheme _rawContext _rawParameters
        _rawBindings _context _parameters _bindings _fixedCaps _fixedTys
        _reservedCaps _reservedTys args result _capImages _tyImages =>
        solveCount ≤ state.trace.solves.length ∧
        scheme.ValueFlowInst
          (args.map (Dual.applySubst state.prevailing))
          (result.applySubst state.prevailing)
    | .ctorInstantiation solveCount _ scheme args result _ =>
        solveCount ≤ state.trace.solves.length ∧
        scheme.Inst (args.map state.prevailing.apply)
          (state.prevailing.apply result)
    | _ => True

/-- Half-open chronological solve slice used by every terminal-cut audit. -/
def solveSlice (trace : InferTrace) (start stop : Nat) : List SolveStep :=
  (trace.solves.take stop).drop start

/-- Ordinary alignment provenance and equality at the complete public cut. -/
def TraceTypeAlignmentConditions (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .typeAlignment start stop rawLeft rawRight localLeft localRight =>
        start ≤ stop ∧ stop ≤ state.trace.solves.length ∧
        localLeft =
          (replay (state.trace.solves.take start)).apply rawLeft ∧
        localRight =
          (replay (state.trace.solves.take start)).apply rawRight ∧
        state.prevailing.apply rawLeft = state.prevailing.apply rawRight
    | _ => True

/-- Dual alignment provenance and componentwise equality at the complete
public cut. -/
def TraceDualAlignmentConditions (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .dualAlignment start stop rawLeft rawRight localLeft localRight =>
        start ≤ stop ∧ stop ≤ state.trace.solves.length ∧
        localLeft = rawLeft.applySubst
          (replay (state.trace.solves.take start)) ∧
        localRight = rawRight.applySubst
          (replay (state.trace.solves.take start)) ∧
        rawLeft.applySubst state.prevailing =
          rawRight.applySubst state.prevailing
    | _ => True

/-- Eliminate a recorded ordinary alignment at the complete public cut. -/
theorem TraceTypeAlignmentConditions.final_eq
    {state : InferState} (conditions : TraceTypeAlignmentConditions state)
    {start stop : Nat} {rawLeft rawRight localLeft localRight : Ty}
    (membership : .typeAlignment start stop rawLeft rawRight localLeft
      localRight ∈ state.trace.events) :
    state.prevailing.apply rawLeft = state.prevailing.apply rawRight := by
  rcases conditions _ membership with
    ⟨_startStop, _stopBound, _localLeft, _localRight, finalEq⟩
  exact finalEq

/-- Eliminate a recorded dual alignment at the complete public cut. -/
theorem TraceDualAlignmentConditions.final_eq
    {state : InferState} (conditions : TraceDualAlignmentConditions state)
    {start stop : Nat} {rawLeft rawRight localLeft localRight : Dual}
    (membership : .dualAlignment start stop rawLeft rawRight localLeft
      localRight ∈ state.trace.events) :
    rawLeft.applySubst state.prevailing =
      rawRight.applySubst state.prevailing := by
  rcases conditions _ membership with
    ⟨_startStop, _stopBound, _localLeft, _localRight, finalEq⟩
  exact finalEq

/-- A recorded constructor instance is valid at the complete public cut. -/
theorem TraceInstanceSuffixConditions.ctor_final
    {signature : FrozenSig} {state : InferState}
    (conditions : TraceInstanceSuffixConditions signature state)
    {solveCount : Nat} {supply : InferenceBase.FreshSupply}
    {scheme : CtorScheme} {arguments : List Ty} {target : Ty}
    {capImages : List CapVar}
    (membership : .ctorInstantiation solveCount supply scheme arguments target
      capImages ∈ state.trace.events) :
    scheme.Inst (arguments.map state.prevailing.apply)
      (state.prevailing.apply target) := by
  rcases conditions _ membership with ⟨bound, terminals⟩
  exact terminals

/-- A recorded expression-scheme instance transports to the complete public
cut together with the context lookup that selected it. -/
theorem TraceInstanceSuffixConditions.scheme_final
    {signature : FrozenSig} {state : InferState}
    (conditions : TraceInstanceSuffixConditions signature state)
    {solveCount : Nat} {supply : InferenceBase.FreshSupply}
    {scheme : Scheme} {name : String} {rawContext context : Context}
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {fresh : Ty} {capImages : List CapVar} {tyImages : List TypePM.TyVar}
    (membership : .schemeInstantiation solveCount supply scheme name rawContext
      context fixedCaps fixedTys reservedCaps reservedTys fresh capImages
      tyImages ∈ state.trace.events) :
    ∃ terminalScheme,
      (rawContext.applySubst state.prevailing).find? name =
          some terminalScheme ∧
      terminalScheme.ValueFlowInst (state.prevailing.apply fresh) := by
  exact (conditions _ membership).2

/-- A recorded dual-scheme instance transports both its argument list and its
result dual to the complete public cut. -/
theorem TraceInstanceSuffixConditions.dual_final
    {signature : FrozenSig} {state : InferState}
    (conditions : TraceInstanceSuffixConditions signature state)
    {solveCount : Nat} {supply : InferenceBase.FreshSupply}
    {scheme : DualScheme} {rawContext : Context}
    {rawParameters : PatternCtx} {rawBindings : MonoCtx}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {arguments : List Dual} {result : Dual} {capImages : List CapVar}
    {tyImages : List TypePM.TyVar}
    (membership : .dualInstantiation solveCount supply scheme rawContext
      rawParameters rawBindings context parameters bindings fixedCaps fixedTys
      reservedCaps reservedTys arguments result capImages tyImages ∈
        state.trace.events) :
    scheme.ValueFlowInst
      (arguments.map (Dual.applySubst state.prevailing))
      (result.applySubst state.prevailing) := by
  exact (conditions _ membership).2

/-- Algebraic outcome of one recorded expected-type alignment at the complete
public cut.  The coercion branch retains the exact raw solver interval and its
raw certificate; `post` is only a capability-variable,
payload-equivalent suffix.
No matcher or unifier is rerun on suffix-transformed inputs. -/
inductive SlotAlignmentAtTerminal
    (localSteps terminalSteps : List SolveStep)
    (inferred requested : Ty) : Prop where
  | equal
      (aligned : applyDeltas terminalSteps inferred =
        applyDeltas terminalSteps requested) :
      SlotAlignmentAtTerminal localSteps terminalSteps inferred requested
  | matcherToSlot
      {producerCap consumerCap : Cap}
      {producerTarget consumerTarget : Ty}
      {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
      {step : SolveStep} {post : Subst}
      (inferredEq : inferred = .matcher producerCap producerTarget)
      (requestedEq : requested = .slot consumerCap consumerTarget)
      (localEq : localSteps = [step])
      (constraintEq : step.constraint = .producerToSlot producerCap
        producerTarget consumerCap consumerTarget)
      (deltaEq : step.delta = Subst.mk C T)
      (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
        consumerTarget bindings C T)
      (postVariable : VariablePost post)
      (producerResult :
        applyDeltas terminalSteps inferred =
          post.apply (.matcher (producerCap.apply C)
            ((Subst.mk C T).apply producerTarget)))
      (consumerResult :
        applyDeltas terminalSteps requested =
          post.apply (.slot (consumerCap.apply C)
            ((Subst.mk C T).apply consumerTarget))) :
      SlotAlignmentAtTerminal localSteps terminalSteps inferred requested

/-- Every expected-type event has a certificate at the complete public cut. -/
def TraceSlotAlignmentConditions (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .slotAlignment start stop inferred requested =>
        start ≤ stop ∧ stop ≤ state.trace.solves.length ∧
        SlotAlignmentAtTerminal
          (solveSlice state.trace start stop)
          (solveSlice state.trace start state.trace.solves.length)
          inferred requested
    | _ => True

/-- Eliminate a recorded expected-type alignment at the complete public cut. -/
theorem TraceSlotAlignmentConditions.final
    {state : InferState} (conditions : TraceSlotAlignmentConditions state)
    {start stop : Nat} {inferred requested : Ty}
    (membership : .slotAlignment start stop inferred requested ∈
      state.trace.events) :
    SlotAlignmentAtTerminal
      (solveSlice state.trace start stop)
      (solveSlice state.trace start state.trace.solves.length)
      inferred requested := by
  exact (conditions _ membership).2.2

/-- Resolve the raw hole ledger at one chronological solver cut. -/
def resolvedHoleCaps
    (prevailing : Subst) (rawHoleLists : List (List Dual)) :
    List (List Cap) :=
  rawHoleLists.map fun holes =>
    (holes.map (Dual.applySubst prevailing)).map Dual.cap

/-- Matcher finalization is rechecked at the complete reconstruction cut.
The event retains raw target and hole data, so intermediate-prefix obligations
are unnecessary. -/
def TraceFinalizationSuffixConditions
    (signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .matcherFinalization solveCount clauses rawTarget rawHoleLists localTarget
        localHoleLists _localEvidence localCapability =>
        solveCount ≤ state.trace.solves.length ∧
        localTarget =
          (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
        localHoleLists = resolvedHoleCaps
          (replay (state.trace.solves.take solveCount)) rawHoleLists ∧
        let terminalTarget := state.prevailing.apply rawTarget
        let terminalHoleLists :=
          resolvedHoleCaps state.prevailing rawHoleLists
        let terminalCapability :=
          Cap.apply state.prevailing.cap localCapability
        ∃ evidence,
          collectClauseEvidence signature.toMatcherSig clauses
              terminalHoleLists = some evidence ∧
          Shape.inferShape signature.observability evidence =
              some terminalCapability ∧
          clauseCapsListCheck signature terminalCapability clauses
              terminalHoleLists = true ∧
          catchAllLastCheck clauses = true ∧
          matcherBindersCheck clauses = true ∧
          armExhaustiveCheck signature clauses terminalTarget = true ∧
          coverageCheck signature.toMatcherSig clauses terminalCapability = true
    | _ => True

/-- Algebraic let-generalization facts at the complete reconstruction cut.

The generalized scheme is allowed to evolve when constraints from the body
specialize variables shared with the surrounding context.  What matters for
T-LET is the exact commuting equation at the terminal cut: applying the
terminal substitution to the scheme recorded after the value traversal must
produce the scheme obtained by generalizing the terminal context and value
type.  Requiring the recorded context, value, and scheme themselves to stay
unchanged is both unnecessary and false for ordinary successful programs.
-/
def TraceGeneralizationConditions
    (signature : FrozenSig) (state : InferState) : Prop :=
  ∀ event, event ∈ state.trace.events ->
    match event with
    | .letGeneralization solveCount _name rawContext rawTarget context target
        scheme =>
        solveCount ≤ state.trace.solves.length ∧
        context = rawContext.applySubst
          (replay (state.trace.solves.take solveCount)) ∧
        target = (replay (state.trace.solves.take solveCount)).apply rawTarget ∧
        scheme = signature.generalize context target ∧
        scheme.applySubst state.prevailing =
          signature.generalize (rawContext.applySubst state.prevailing)
            (state.prevailing.apply rawTarget)
    | _ => True

/-- Internal, purely algebraic side conditions for reconstruction.  No field
contains a source or reconstruction judgment. -/
structure WBridgeWF
    (signature : FrozenSig) (state : InferState) : Prop where
  primitiveHoles :
    tracePrimitiveHoleCheck signature state.trace = true
  patternLeaves : tracePatternLeafCheck signature state.trace = true
  patternCtors : tracePatternCtorCheck signature state = true
  instanceSuffixes : TraceInstanceSuffixConditions signature state
  slotAlignments : TraceSlotAlignmentConditions state
  typeAlignments : TraceTypeAlignmentConditions state
  dualAlignments : TraceDualAlignmentConditions state
  finalizationSuffixes : TraceFinalizationSuffixConditions signature state
  generalization : TraceGeneralizationConditions signature state

/-! ## Terminal reconstruction of the syntax-directed traversals -/

/-- Replaying the suffix after a recursive call is exactly terminal paired
application to every raw target owned by that call. -/
theorem history_terminal_apply_eq
    {earlier terminal : InferState}
    (history : earlier.HistoryPrefix terminal) (target : Ty) :
    terminal.prevailing.apply target =
      applyDeltas
        (solveSlice terminal.trace earlier.trace.solves.length
          terminal.trace.solves.length)
        (earlier.prevailing.apply target) := by
  have replayConditions := traceReplayConditions terminal.trace.solves
  rcases history with ⟨suffix, _eventSuffix, solves, _events⟩
  have suffixConditions :
      ReplayConditions (replay earlier.trace.solves) suffix := by
    rw [solves] at replayConditions
    exact TraceReplayConditions.afterPrefix replayConditions
  have sequential := suffixConditions.apply_eq_sequential target
  simp only [InferState.prevailing, solveSlice, List.take_length]
  rw [solves, replay, replayFrom_append]
  rw [List.drop_append_length]
  simpa only [replay] using sequential

/-- Successful pointwise pattern-target alignment identifies every child
target at an enclosing terminal cut. -/
theorem alignPatternTargets_terminal_eq
    {terminal : InferState}
    (typeAlignments : TraceTypeAlignmentConditions terminal)
    {state result : InferState} {origin : ConstraintOrigin}
    {duals : List Dual} {targets : List Ty}
    (success : alignPatternTargets state origin duals targets = some result)
    (history : result.HistoryPrefix terminal) :
    duals.map (fun dual => terminal.prevailing.apply dual.target) =
      targets.map terminal.prevailing.apply := by
  induction duals generalizing targets state result with
  | nil =>
      cases targets <;> simp [alignPatternTargets] at success ⊢
  | cons dual duals induction =>
      cases targets with
      | nil => simp [alignPatternTargets] at success
      | cons target targets =>
          simp only [alignPatternTargets] at success
          cases alignmentEq : alignTypes state origin dual.target target with
          | none => simp [alignmentEq] at success
          | some middle =>
              simp [alignmentEq] at success
              have middleHistory : middle.HistoryPrefix result :=
                alignPatternTargets_historyPrefix success
              have alignmentMembership := alignTypes_event_mem alignmentEq
              have terminalMembership := InferState.HistoryPrefix.event_mem
                (middleHistory.trans history) alignmentMembership
              have headEq := typeAlignments.final_eq terminalMembership
              have tailEq := induction success history
              simp only [List.map_cons, headEq, tailEq]

/-- Successful pointwise dual alignment identifies both components of every
argument at an enclosing terminal cut. -/
theorem alignDualLists_terminal_eq
    {terminal : InferState}
    (dualAlignments : TraceDualAlignmentConditions terminal)
    {state result : InferState} {origin : ConstraintOrigin}
    {left right : List Dual}
    (success : alignDualLists state origin left right = some result)
    (history : result.HistoryPrefix terminal) :
    left.map (Dual.applySubst terminal.prevailing) =
      right.map (Dual.applySubst terminal.prevailing) := by
  induction left generalizing right state result with
  | nil =>
      cases right <;> simp [alignDualLists] at success ⊢
  | cons dual duals induction =>
      cases right with
      | nil => simp [alignDualLists] at success
      | cons expected expecteds =>
          simp only [alignDualLists] at success
          cases alignmentEq : alignDuals state origin dual expected with
          | none => simp [alignmentEq] at success
          | some middle =>
              simp [alignmentEq] at success
              have middleHistory : middle.HistoryPrefix result :=
                alignDualLists_historyPrefix success
              have alignmentMembership := alignDuals_event_mem alignmentEq
              have terminalMembership := InferState.HistoryPrefix.event_mem
                (middleHistory.trans history) alignmentMembership
              have headEq := dualAlignments.final_eq terminalMembership
              have tailEq := induction success history
              simp only [List.map_cons, headEq, tailEq]

/-- Actual primitive-pattern W reconstructed at one enclosing terminal cut.
The certificate follows the algorithm's terminal equalities recursively. -/
theorem inferPPatFuel_terminalAt
    {terminal : InferState}
    (instanceSuffixes : TraceInstanceSuffixConditions signature terminal)
    (typeAlignments : TraceTypeAlignmentConditions terminal)
    (primitiveHoles :
      tracePrimitiveHoleCheck signature terminal.trace = true)
    {fuel path pattern expected state result}
    (success : inferPPatFuel fuel signature path pattern expected state =
      some result)
    (history : result.state.HistoryPrefix terminal) :
    PPatResolutionDeriv signature terminal.prevailing pattern
      (terminal.prevailing.apply expected)
      (result.holes.map (Dual.applySubst terminal.prevailing))
      (result.bindings.applySubst terminal.prevailing) := by
  revert terminal
  apply inferPPatFuel.induct
    (motive_1 := fun fuel signature path pattern expected state =>
      ∀ result,
        inferPPatFuel fuel signature path pattern expected state = some result ->
        ∀ terminal,
        TraceInstanceSuffixConditions signature terminal ->
        TraceTypeAlignmentConditions terminal ->
        tracePrimitiveHoleCheck signature terminal.trace = true ->
        result.state.HistoryPrefix terminal ->
        PPatResolutionDeriv signature terminal.prevailing pattern
          (terminal.prevailing.apply expected)
          (result.holes.map (Dual.applySubst terminal.prevailing))
          (result.bindings.applySubst terminal.prevailing))
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferPPatsFuel fuel signature path index patterns targets state =
            some result ->
        ∀ terminal,
        TraceInstanceSuffixConditions signature terminal ->
        TraceTypeAlignmentConditions terminal ->
        tracePrimitiveHoleCheck signature terminal.trace = true ->
        result.state.HistoryPrefix terminal ->
        PPatResolutionsDeriv signature terminal.prevailing patterns
          (targets.map terminal.prevailing.apply)
          (result.holes.map (Dual.applySubst terminal.prevailing))
          (result.bindings.applySubst terminal.prevailing))
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferPPatFuel, inferPPatsFuel, Option.some.injEq]
  all_goals try contradiction
  all_goals try subst_vars
  all_goals try exact PPatResolutionDeriv.wild
  all_goals try exact PPatResolutionDeriv.pval
  all_goals try exact PPatResolutionsDeriv.nil
  all_goals try assumption
  case case2 =>
    rename_i fuel' signature' path' expectedTarget initial capability freshState
      freshEq terminal instanceSuffixes typeAlignments primitiveHoles
      terminalHistory
    have localMembership :
        TraceEvent.inferredPPat .hole expectedTarget
          [⟨capability, expectedTarget⟩] [] path' ∈
          ((visit freshState .ppatHole path').recordEvent
            (.inferredPPat .hole expectedTarget
              [⟨capability, expectedTarget⟩] [] path')).trace.events := by
      simp [InferState.recordEvent]
    have finalMembership :=
      InferState.HistoryPrefix.event_mem terminalHistory localMembership
    simp only [InferState.freshCap, Prod.mk.injEq] at freshEq
    rcases freshEq with ⟨capabilityEq, stateEq⟩
    subst capability
    subst freshState
    let varId : CapVar := ⟨initial.supply.nextCap⟩
    have fresh := tracePrimitiveHoleCheck_hole primitiveHoles finalMembership
    simpa only [List.map_cons, List.map_nil, Dual.applySubst,
      Dual.apply, Cap.apply, MonoCtx.applySubst,
      InferenceBase.freshCapMeta] using
      (PPatResolutionDeriv.hole (prevailing := terminal.prevailing) fresh)
  case case8 =>
    rename_i fuel' signature' path' expectedTarget initial ctor patterns entry
      lookup fieldTargets resultTarget instState instEq alignedState alignEq
      results childrenEq terminal childrenIH instanceSuffixes typeAlignments
      primitiveHoles terminalHistory
    have childrenHistory : alignedState.HistoryPrefix results.state :=
      inferPPatsFuel_historyPrefix childrenEq
    have resultHistory : results.state.HistoryPrefix terminal :=
      (visit_historyPrefix results.state .ppatCtor path').trans
        ((InferState.historyPrefix_recordEvent _ _).trans terminalHistory)
    have alignmentHistory : alignedState.HistoryPrefix terminal :=
      childrenHistory.trans resultHistory
    have instantiationHistory : instState.HistoryPrefix terminal :=
      (alignTypes_historyPrefix alignEq).trans alignmentHistory
    rcases instantiateCtorInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, capImages, localInstantiationMembership⟩
    have instantiationMembership :=
      InferState.HistoryPrefix.event_mem instantiationHistory
        localInstantiationMembership
    have instantiated := instanceSuffixes.ctor_final instantiationMembership
    have localAlignmentMembership := alignTypes_event_mem alignEq
    have alignmentMembership :=
      InferState.HistoryPrefix.event_mem alignmentHistory
        localAlignmentMembership
    have aligned := typeAlignments.final_eq alignmentMembership
    rw [← aligned]
    exact PPatResolutionDeriv.ctor lookup
      (childrenIH results rfl terminal instanceSuffixes typeAlignments
        primitiveHoles resultHistory)
      instantiated
  case case11 =>
    rename_i fuel' signature' path' expectedTarget initial patterns targets
      freshState freshEq alignedState alignEq results childrenEq terminal
      childrenIH instanceSuffixes typeAlignments primitiveHoles terminalHistory
    have childrenHistory : alignedState.HistoryPrefix results.state :=
      inferPPatsFuel_historyPrefix childrenEq
    have resultHistory : results.state.HistoryPrefix terminal :=
      (visit_historyPrefix results.state .ppatTuple path').trans
        ((InferState.historyPrefix_recordEvent _ _).trans terminalHistory)
    have alignmentHistory : alignedState.HistoryPrefix terminal :=
      childrenHistory.trans resultHistory
    have localAlignmentMembership := alignTypes_event_mem alignEq
    have alignmentMembership :=
      InferState.HistoryPrefix.event_mem alignmentHistory
        localAlignmentMembership
    have aligned := typeAlignments.final_eq alignmentMembership
    rw [Subst.apply_prod] at aligned
    rw [← aligned]
    exact PPatResolutionDeriv.tuple
      (childrenIH results rfl terminal instanceSuffixes typeAlignments
        primitiveHoles resultHistory)
  case case16 =>
    rename_i fuel' signature' parent index pattern patterns target targets
      initial head headEq results tailEq distinct result terminal headIH tailIH
      resultEq instanceSuffixes typeAlignments primitiveHoles terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at *
    subst_vars
    have headDeriv := headIH head rfl terminal instanceSuffixes typeAlignments
      primitiveHoles
      ((inferPPatsFuel_historyPrefix tailEq).trans terminalHistory)
    have tailDeriv := tailIH results rfl terminal instanceSuffixes typeAlignments
      primitiveHoles terminalHistory
    have transportedDistinct : ∀ name,
        name ∈ (head.bindings.applySubst terminal.prevailing).names ->
        name ∉ (results.bindings.applySubst terminal.prevailing).names := by
      simpa only [MonoCtx.names_applySubst] using
        (namesDisjoint_eq_true _ _).mp distinct
    simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
      PPatResolutionsDeriv.cons headDeriv tailDeriv transportedDistinct

/-- Primitive data-pattern inference reconstructs directly at an enclosing
terminal cut.  This two-family lemma is kept independent of expression
generalization, so matcher-arm reconstruction can consume it without any
scheme-transport assumption. -/
theorem inferDPatFuel_reconstructAt
    {terminal : InferState}
    (instanceSuffixes : TraceInstanceSuffixConditions signature terminal)
    (typeAlignments : TraceTypeAlignmentConditions terminal)
    {fuel path pattern expected state result}
    (success : inferDPatFuel fuel signature path pattern expected state =
      some result)
    (history : result.state.HistoryPrefix terminal) :
    DPatDeriv signature pattern (terminal.prevailing.apply expected)
      (result.bindings.applySubst terminal.prevailing) := by
  revert terminal
  apply inferDPatFuel.induct
    (motive_1 := fun fuel signature path pattern expected state =>
      ∀ result,
        inferDPatFuel fuel signature path pattern expected state = some result ->
        ∀ terminal,
        TraceInstanceSuffixConditions signature terminal ->
        TraceTypeAlignmentConditions terminal ->
        result.state.HistoryPrefix terminal ->
        DPatDeriv signature pattern (terminal.prevailing.apply expected)
          (result.bindings.applySubst terminal.prevailing))
    (motive_2 := fun fuel signature path index patterns targets state =>
      ∀ result,
        inferDPatsFuel fuel signature path index patterns targets state =
            some result ->
        ∀ terminal,
        TraceInstanceSuffixConditions signature terminal ->
        TraceTypeAlignmentConditions terminal ->
        result.state.HistoryPrefix terminal ->
        DPatsDeriv signature patterns
          (targets.map terminal.prevailing.apply)
          (result.bindings.applySubst terminal.prevailing))
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferDPatFuel, inferDPatsFuel, Option.some.injEq]
  all_goals try contradiction
  all_goals try subst_vars
  all_goals try exact DPatDeriv.var
  all_goals try exact DPatDeriv.wild
  all_goals try exact DPatsDeriv.nil
  all_goals try assumption
  case case7 =>
    rename_i fuel' signature' path' expectedTarget initial ctor patterns scheme
      lookup fieldTargets resultTarget instState instEq alignedState alignEq
      results childrenEq terminal childrenIH instanceSuffixes typeAlignments
      terminalHistory
    have instantiationEvent := instantiateCtorInState_event_mem_of_eq
      instEq
    rcases instantiationEvent with
      ⟨solveCount, supply, capImages, instantiationMembership⟩
    have childrenHistory : alignedState.HistoryPrefix results.state :=
      inferDPatsFuel_historyPrefix childrenEq
    have resultHistory : results.state.HistoryPrefix terminal :=
      (visit_historyPrefix results.state .dpatCtor path').trans
        ((InferState.historyPrefix_recordEvent _ _).trans terminalHistory)
    have alignmentHistory : alignedState.HistoryPrefix terminal :=
      childrenHistory.trans resultHistory
    have instantiationHistory : instState.HistoryPrefix terminal :=
      (alignTypes_historyPrefix alignEq).trans alignmentHistory
    have finalInstantiationMembership :=
      InferState.HistoryPrefix.event_mem (later := terminal)
        instantiationHistory
        instantiationMembership
    have instantiated :=
      instanceSuffixes.ctor_final finalInstantiationMembership
    have alignmentEvent := alignTypes_event_mem alignEq
    have finalAlignmentMembership :=
      InferState.HistoryPrefix.event_mem (later := terminal)
        alignmentHistory
        alignmentEvent
    have aligned := typeAlignments.final_eq finalAlignmentMembership
    rw [← aligned]
    exact DPatDeriv.ctor lookup
      (childrenIH results rfl terminal instanceSuffixes typeAlignments
        resultHistory)
      instantiated
  case case10 =>
    rename_i fuel' signature' path' expectedTarget initial patterns targets
      freshState freshEq alignedState alignEq results childrenEq terminal
      childrenIH instanceSuffixes typeAlignments terminalHistory
    have childrenHistory : alignedState.HistoryPrefix results.state :=
      inferDPatsFuel_historyPrefix childrenEq
    have resultHistory : results.state.HistoryPrefix terminal :=
      (visit_historyPrefix results.state .dpatTuple path').trans
        ((InferState.historyPrefix_recordEvent _ _).trans terminalHistory)
    have alignmentHistory : alignedState.HistoryPrefix terminal :=
      childrenHistory.trans resultHistory
    have alignmentEvent := alignTypes_event_mem alignEq
    have finalAlignmentMembership :=
      InferState.HistoryPrefix.event_mem (later := terminal)
        alignmentHistory
        alignmentEvent
    have aligned := typeAlignments.final_eq finalAlignmentMembership
    rw [Subst.apply_prod] at aligned
    rw [← aligned]
    apply DPatDeriv.tuple
    exact childrenIH results rfl terminal instanceSuffixes typeAlignments
      resultHistory
  case case15 =>
    rename_i fuel' signature' parent index pattern patterns target targets
      initial head headEq results tailEq distinct result terminal headIH tailIH
      resultEq instanceSuffixes typeAlignments terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at *
    subst_vars
    have headDeriv := headIH head rfl terminal instanceSuffixes typeAlignments
        ((inferDPatsFuel_historyPrefix tailEq).trans terminalHistory)
    have tailDeriv := tailIH results rfl terminal instanceSuffixes typeAlignments
        terminalHistory
    have transportedDistinct : ∀ name,
        name ∈ (head.bindings.applySubst terminal.prevailing).names ->
        name ∉ (results.bindings.applySubst terminal.prevailing).names := by
      simpa only [MonoCtx.names_applySubst] using
        (namesDisjoint_eq_true _ _).mp distinct
    simpa only [List.map_cons, MonoCtx.applySubst, List.map_append] using
      DPatsDeriv.cons headDeriv tailDeriv transportedDistinct

set_option maxHeartbeats 4000000 in
/-- The complete mutually recursive W traversal reconstructs a proof-relevant
source derivation at any enclosing terminal trace cut. -/
theorem inferExprFuel_reconstructAt
    {terminal : InferState}
    (bridge : WBridgeWF signature terminal)
    {fuel context selfEnv path expression state result}
    (success : inferExprFuel fuel signature context selfEnv path expression
      state = some result)
    (history : result.state.HistoryPrefix terminal) :
    ExprDeriv signature (context.applySubst terminal.prevailing) expression
      (terminal.prevailing.apply result.target) := by
  revert terminal
  apply inferExprFuel.induct
    (motive1 := fun fuel signature context selfEnv path expression state =>
      ∀ result,
        inferExprFuel fuel signature context selfEnv path expression state =
            some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          ExprDeriv signature (context.applySubst terminal.prevailing)
            expression (terminal.prevailing.apply result.target))
    (motive2 := fun fuel signature context selfEnv path expression expected
        state =>
      ∀ result,
        checkExprFuel fuel signature context selfEnv path expression expected
            state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.HistoryPrefix terminal ->
          ExprDeriv signature (context.applySubst terminal.prevailing)
            expression (terminal.prevailing.apply expected))
    (motive3 := fun fuel signature context parameters bindings selfEnv path
        pattern state =>
      ∀ result,
        inferPatternFuel fuel signature context parameters bindings selfEnv path
            pattern state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          PatternResolutionDeriv signature terminal.prevailing
            (context.applySubst terminal.prevailing)
            (parameters.applySubst terminal.prevailing)
            (bindings.applySubst terminal.prevailing) pattern
            (result.dual.applySubst terminal.prevailing).cap
            (result.dual.applySubst terminal.prevailing).target
            (result.bindings.applySubst terminal.prevailing))
    (motive4 := fun fuel signature context parameters bindings selfEnv path
        index patterns state =>
      ∀ result,
        inferPatternsFuel fuel signature context parameters bindings selfEnv
            path index patterns state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          PatternResolutionsDeriv signature terminal.prevailing
            (context.applySubst terminal.prevailing)
            (parameters.applySubst terminal.prevailing)
            (bindings.applySubst terminal.prevailing) patterns
            (result.duals.map (Dual.applySubst terminal.prevailing))
            (result.bindings.applySubst terminal.prevailing))
    (motive5 := fun fuel signature context selfEnv path clauses state =>
      ∀ result,
        inferMatcherFuel fuel signature context selfEnv path clauses state =
            some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          ExprDeriv signature (context.applySubst terminal.prevailing)
            (.matcher clauses) (terminal.prevailing.apply result.target))
    (motive6 := fun fuel signature context selfEnv path index clauses target
        state =>
      ∀ result,
        inferClausesFuel fuel signature context selfEnv path index clauses target
            state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          ∀ capability evidences,
            ClauseCapsList signature clauses
                (resolvedHoleCaps terminal.prevailing result.rawHoleLists)
                capability ->
            ClauseEvidenceList signature.toMatcherSig clauses
                (resolvedHoleCaps terminal.prevailing result.rawHoleLists)
                evidences ->
            ClausesDeriv signature terminal.prevailing
              (context.applySubst terminal.prevailing) clauses capability
              (terminal.prevailing.apply target) evidences)
    (motive7 := fun fuel signature context selfEnv path clause target state =>
      ∀ result,
        inferClauseFuel fuel signature context selfEnv path clause target state =
            some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          ∀ capability evidence,
            PPatCapsAt signature true clause.pp
                ((result.rawHoles.map
                    (Dual.applySubst terminal.prevailing)).map Dual.cap)
                capability ->
            clauseEvidence signature.toMatcherSig clause.pp
                ((result.rawHoles.map
                    (Dual.applySubst terminal.prevailing)).map Dual.cap) =
                  some evidence ->
            ClauseDeriv signature terminal.prevailing
              (context.applySubst terminal.prevailing) clause capability
              (terminal.prevailing.apply target) evidence)
    (motive8 := fun fuel signature context selfEnv bindings path index arms
        target bodyTarget state =>
      ∀ result,
        checkArmsFuel fuel signature context selfEnv bindings path index arms
            target bodyTarget state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.HistoryPrefix terminal ->
          ArmsDeriv signature (context.applySubst terminal.prevailing)
            (terminal.prevailing.apply target)
            (bindings.applySubst terminal.prevailing)
            (terminal.prevailing.apply bodyTarget) arms)
    (motive9 := fun fuel signature context selfEnv path index expressions
        expecteds state =>
      ∀ result,
        checkExprsFuel fuel signature context selfEnv path index expressions
            expecteds state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.HistoryPrefix terminal ->
          ExprsDeriv signature (context.applySubst terminal.prevailing)
            expressions (expecteds.map terminal.prevailing.apply))
    (motive10 := fun fuel signature context selfEnv path index expressions
        state =>
      ∀ result,
        inferExprsFuel fuel signature context selfEnv path index expressions
            state = some result ->
        ∀ terminal,
          WBridgeWF signature terminal ->
          result.state.HistoryPrefix terminal ->
          ExprsDeriv signature (context.applySubst terminal.prevailing)
            expressions (result.targets.map terminal.prevailing.apply))
  all_goals intros
  all_goals try simp_all (config := { zetaDelta := true }) only
    [inferExprFuel, checkExprFuel, inferPatternFuel, inferPatternsFuel,
      inferMatcherFuel, inferClausesFuel, inferClauseFuel, checkArmsFuel,
      checkExprsFuel, inferExprsFuel, Option.some.injEq]
  all_goals try contradiction
  all_goals try subst_vars
  all_goals try exact ExprsDeriv.nil
  all_goals try exact PatternResolutionsDeriv.nil
  all_goals try exact ArmsDeriv.nil
  all_goals try exact ClausesDeriv.nil
  all_goals try exact ExprDeriv.lit
  all_goals try assumption
  case case3 =>
    rename_i fuel' signature' context' selfEnv' path' initial name scheme target
      instState visited normalizedContext terminal lookup instEq bridge'
      terminalHistory
    have selfHistory : instState.HistoryPrefix
        (match selfEnv'.find? name with
         | none => instState
         | some placeholder =>
             recordSelfReference instState name placeholder path') := by
      cases selfLookup : selfEnv'.find? name with
      | none => exact InferState.HistoryPrefix.refl _
      | some placeholder =>
          exact recordSelfReference_historyPrefix instState name placeholder
            path'
    have instHistory : instState.HistoryPrefix terminal :=
      selfHistory.trans
        ((finishExpr_historyPrefix (.var name) path' target _).trans
          terminalHistory)
    rcases instantiateSchemeInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, fixedCaps, fixedTys, reservedCaps, reservedTys,
        capImages, tyImages, localMembership⟩
    have finalMembership := instHistory.event_mem localMembership
    rcases bridge'.instanceSuffixes.scheme_final finalMembership with
      ⟨terminalScheme, terminalLookup, instantiated⟩
    exact ExprDeriv.var terminalLookup instantiated
  case case5 =>
    rename_i fuel' signature' context' selfEnv' path' initial name body domain
      freshState bodyResult bodyEq visited terminal freshEq bodyIH bridge'
      terminalHistory
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.lam name body) path'
        (.fn domain bodyResult.target) bodyResult.state).trans terminalHistory
    have bodyDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    simpa [finishExpr, Subst.apply_fn, Context.applySubst,
      Scheme.applySubst, Scheme.mono] using ExprDeriv.lam bodyDeriv
  case case9 =>
    rename_i fuel' signature' context' selfEnv' path' initial self argument body
      direct domain codomain builtState placeholder recordedState shadowed
      insideSelf insideContext bodyResult alignedState visited result terminal
      bodyEq alignEq buildEq bodyIH resultEq bridge' terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.fix self argument body) path'
        (.fn domain codomain) alignedState).trans terminalHistory
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (alignTypes_historyPrefix alignEq).trans alignedHistory
    have bodyDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    have localAlignment := alignTypes_event_mem alignEq
    have finalAlignment := alignedHistory.event_mem localAlignment
    have aligned := bridge'.typeAlignments.final_eq finalAlignment
    have bodyDeriv' : ExprDeriv signature'
        (((argument, Scheme.mono (terminal.prevailing.apply domain)) ::
          (self, Scheme.mono
            (.fn (terminal.prevailing.apply domain)
              (terminal.prevailing.apply codomain))) ::
          context'.applySubst terminal.prevailing))
        body (terminal.prevailing.apply codomain) := by
      simpa only [Context.applySubst, List.map_cons, Scheme.applySubst_mono,
        Subst.apply_fn, aligned] using bodyDeriv
    simpa [finishExpr, Subst.apply_fn] using ExprDeriv.fixE bodyDeriv'
  case case14 =>
    rename_i fuel' signature' context' selfEnv' path' initial function argument
      functionResult argumentResult argumentEq resultTarget freshState freshEq
      alignedState alignEq visited terminal functionEq functionIH argumentIH
      bridge' terminalHistory
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.app function argument) path' resultTarget
        alignedState).trans terminalHistory
    have freshHistory : argumentResult.state.HistoryPrefix freshState :=
      InferState.HistoryPrefix.snd_of_eq
        (InferState.historyPrefix_freshTy argumentResult.state
          (freshOrigin .expression path' "application-result")) freshEq
    have argumentHistory : argumentResult.state.HistoryPrefix terminal :=
      freshHistory.trans
        ((alignTypes_historyPrefix alignEq).trans alignedHistory)
    have functionHistory : functionResult.state.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix argumentEq).trans argumentHistory
    have functionDeriv := functionIH functionResult rfl terminal bridge'
      functionHistory
    have argumentDeriv := argumentIH argumentResult rfl terminal bridge'
      argumentHistory
    have localAlignment := alignTypes_event_mem alignEq
    have finalAlignment := alignedHistory.event_mem localAlignment
    have aligned := bridge'.typeAlignments.final_eq finalAlignment
    rw [aligned] at functionDeriv
    exact ExprDeriv.app functionDeriv argumentDeriv
  case case17 =>
    rename_i fuel' signature' context' selfEnv' path' initial expressions
      results visited terminal listEq listIH bridge' terminalHistory
    have listHistory : results.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.tuple expressions) path'
        (.prod results.targets) results.state).trans terminalHistory
    have listDeriv := listIH results rfl terminal bridge' listHistory
    simpa [finishExpr, Subst.apply_prod] using ExprDeriv.tuple listDeriv
  case case20 =>
    rename_i fuel' signature' context' selfEnv' path' initial name expressions
      scheme lookup expecteds resultTarget instState checkedState checkEq visited
      terminal instEq listIH bridge' terminalHistory
    have checkedHistory : checkedState.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.ctor name expressions) path' resultTarget
        checkedState).trans terminalHistory
    have instHistory : instState.HistoryPrefix terminal :=
      (checkExprsFuel_historyPrefix checkEq).trans checkedHistory
    rcases instantiateCtorInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, capImages, localMembership⟩
    have instantiated := bridge'.instanceSuffixes.ctor_final
      (instHistory.event_mem localMembership)
    exact ExprDeriv.ctor lookup
      instantiated (listIH checkedState rfl terminal bridge' checkedHistory)
  case case23 =>
    rename_i fuel' signature' context' selfEnv' path' initial op expressions
      scheme lookup expecteds resultTarget instState checkedState checkEq visited
      terminal instEq listIH bridge' terminalHistory
    have checkedHistory : checkedState.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.prim op expressions) path' resultTarget
        checkedState).trans terminalHistory
    have instHistory : instState.HistoryPrefix terminal :=
      (checkExprsFuel_historyPrefix checkEq).trans checkedHistory
    rcases instantiateCtorInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, capImages, localMembership⟩
    have instantiated := bridge'.instanceSuffixes.ctor_final
      (instHistory.event_mem localMembership)
    exact ExprDeriv.prim lookup
      instantiated (listIH checkedState rfl terminal bridge' checkedHistory)
  case case26 =>
    rename_i fuel' signature' context' selfEnv' path' initial name value body
      valueResult normalizedContext normalizedValue scheme generalizedState
      bodyResult visited terminal bodyEq valueEq valueIH bodyIH bridge'
      terminalHistory
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.letE name value body) path' bodyResult.target
        bodyResult.state).trans terminalHistory
    have generalizedHistory : generalizedState.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix bodyEq).trans bodyHistory
    let generalizationEvent := TraceEvent.letGeneralization
      valueResult.state.trace.solves.length name context' valueResult.target
      normalizedContext normalizedValue scheme
    have valueHistory : valueResult.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent valueResult.state
        generalizationEvent).trans generalizedHistory
    have valueDeriv := valueIH valueResult rfl terminal bridge' valueHistory
    have bodyDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    have localMembership : generalizationEvent ∈
        (valueResult.state.recordEvent generalizationEvent).trace.events := by
      simp [generalizationEvent, InferState.recordEvent]
    have finalMembership := generalizedHistory.event_mem localMembership
    rcases bridge'.generalization generalizationEvent finalMembership with
      ⟨solveBound, normalizedContextEq, normalizedValueEq, schemeEq,
        schemeAtTerminal⟩
    have bodyContextEq :
        Context.applySubst terminal.prevailing ((name, scheme) :: context') =
          (name, signature'.generalize
            (context'.applySubst terminal.prevailing)
            (terminal.prevailing.apply valueResult.target)) ::
            context'.applySubst terminal.prevailing := by
      change (name, scheme.applySubst terminal.prevailing) ::
          context'.applySubst terminal.prevailing =
        (name, signature'.generalize
          (context'.applySubst terminal.prevailing)
          (terminal.prevailing.apply valueResult.target)) ::
          context'.applySubst terminal.prevailing
      exact congrArg (fun terminalScheme =>
        (name, terminalScheme) :: context'.applySubst terminal.prevailing)
        schemeAtTerminal
    rw [bodyContextEq] at bodyDeriv
    simpa [finishExpr] using ExprDeriv.letE valueDeriv bodyDeriv
  case case27 =>
    rename_i fuel' signature' context' selfEnv' path' initial target freshState
      visited terminal freshEq bridge' terminalHistory
    simpa [finishExpr, Subst.apply_matcher, Cap.apply] using
      (ExprDeriv.something (signature := signature')
        (context := context'.applySubst terminal.prevailing)
        (target := terminal.prevailing.apply target))
  case case29 =>
    rename_i fuel' signature' context' selfEnv' path' initial clauses
      matcherResult visited terminal matcherEq matcherIH bridge' terminalHistory
    exact matcherIH matcherResult rfl terminal bridge'
      ((finishExpr_historyPrefix (.matcher clauses) path' matcherResult.target
        matcherResult.state).trans terminalHistory)
  case case35 =>
    rename_i fuel' signature' context' selfEnv' path' initial target matcher
      pattern body targetResult patternResult patternEq alignedState alignEq
      matcherState matcherEq bodyContext bodyEnv bodyResult visited terminal
      bodyEq targetEq targetIH patternIH matcherIH bodyIH bridge'
      terminalHistory
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (finishExpr_historyPrefix (.matchAll target matcher pattern body) path'
        bodyResult.target.listT bodyResult.state).trans terminalHistory
    have matcherHistory : matcherState.HistoryPrefix terminal :=
      (inferExprFuel_historyPrefix bodyEq).trans bodyHistory
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (checkExprFuel_historyPrefix matcherEq).trans matcherHistory
    have patternHistory : patternResult.state.HistoryPrefix terminal :=
      (alignTypes_historyPrefix alignEq).trans alignedHistory
    have targetHistory : targetResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix patternEq).trans patternHistory
    have targetDeriv := targetIH targetResult rfl terminal bridge' targetHistory
    have rawPatternDeriv := patternIH patternResult rfl terminal bridge'
      patternHistory
    have patternDeriv : PatternResolutionDeriv signature' terminal.prevailing
        (context'.applySubst terminal.prevailing) [] [] pattern
        (patternResult.dual.applySubst terminal.prevailing).cap
        (patternResult.dual.applySubst terminal.prevailing).target
        (patternResult.bindings.applySubst terminal.prevailing) := by
      simpa [PatternCtx.applySubst, MonoCtx.applySubst] using rawPatternDeriv
    have localAlignment := alignTypes_event_mem alignEq
    have targetsAligned := bridge'.typeAlignments.final_eq
      (alignedHistory.event_mem localAlignment)
    have patternDeriv' : PatternResolutionDeriv signature'
        terminal.prevailing (context'.applySubst terminal.prevailing) [] []
        pattern (patternResult.dual.applySubst terminal.prevailing).cap
        (terminal.prevailing.apply targetResult.target)
        (patternResult.bindings.applySubst terminal.prevailing) := by
      rw [← targetsAligned]
      exact patternDeriv
    have matcherDeriv := matcherIH matcherState rfl terminal bridge'
      matcherHistory
    have prevailingEta :
        Subst.mk terminal.prevailing.cap terminal.prevailing.target =
          terminal.prevailing := by
      cases terminal.prevailing
      rfl
    have matcherDeriv' : ExprDeriv signature'
        (context'.applySubst terminal.prevailing) matcher
        (.slot (patternResult.dual.applySubst terminal.prevailing).cap
          (terminal.prevailing.apply targetResult.target)) := by
      simpa [Subst.apply_slot, Dual.applySubst, Dual.apply,
        prevailingEta] using matcherDeriv
    have bodyDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    have bodyDeriv' : ExprDeriv signature'
        ((patternResult.bindings.applySubst terminal.prevailing).toContext ++
          context'.applySubst terminal.prevailing)
        body (terminal.prevailing.apply bodyResult.target) := by
      simpa only [Context.applySubst_append,
        MonoCtx.toContext_applySubst] using bodyDeriv
    simpa [finishExpr, Subst.apply_listT] using
      (ExprDeriv.matchAll targetDeriv
        (ResolvedPatternDeriv.ofTerminal patternDeriv') matcherDeriv'
        bodyDeriv')
  case case39 =>
    rename_i fuel' signature' context' selfEnv' path' expression expected
      initial bodyResult bodyEq alignedState alignEq terminal bodyIH bridge'
      terminalHistory
    let slotEvent := TraceEvent.slotAlignment
      bodyResult.state.trace.solves.length alignedState.trace.solves.length
      (bodyResult.state.prevailing.apply bodyResult.target)
      (bodyResult.state.prevailing.apply expected)
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent alignedState slotEvent).trans
        terminalHistory
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (alignAtSlot_historyPrefix alignEq).trans alignedHistory
    have inferredDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    have localMembership : slotEvent ∈
        (alignedState.recordEvent slotEvent).trace.events := by
      simp [slotEvent, InferState.recordEvent]
    have finalMembership := terminalHistory.event_mem localMembership
    have slotCertificate := bridge'.slotAlignments.final finalMembership
    have inferredTerminal := history_terminal_apply_eq bodyHistory
      bodyResult.target
    have requestedTerminal := history_terminal_apply_eq bodyHistory expected
    cases slotCertificate with
    | equal aligned =>
        have finalEq : terminal.prevailing.apply bodyResult.target =
            terminal.prevailing.apply expected := by
          rw [inferredTerminal, requestedTerminal]
          exact aligned
        rw [← finalEq]
        exact inferredDeriv
    | matcherToSlot inferredEq requestedEq localEq constraintEq deltaEq raw
        postVariable producerResult consumerResult =>
        rw [inferredTerminal, producerResult] at inferredDeriv
        have coerced := ExprDeriv.coerceMatcherToSlot
          (by simpa only [Subst.apply_matcher] using inferredDeriv)
          raw postVariable
        rw [requestedTerminal, consumerResult]
        simpa only [Subst.apply_slot] using coerced
  case case42 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial name absent capability capState capEq target targetState targetEq
      result terminal resultEq bridge' terminalHistory
    simp only [Bool.false_eq_true, if_false, Option.some.injEq] at resultEq
    subst result
    have capabilityEq : capability = .var ⟨initial.supply.nextCap⟩ := by
      have equality := congrArg Prod.fst capEq
      simpa [InferState.freshCap, InferenceBase.freshCapMeta] using equality.symm
    have targetValueEq : target = .var capState.supply.nextTy := by
      have equality := congrArg Prod.fst targetEq
      simpa [InferState.freshTy, InferenceBase.freshTyMeta] using equality.symm
    let leafEvent := TraceEvent.patternVarFresh context' parameters bindings
      ⟨initial.supply.nextCap⟩ capState.supply.nextTy
    have localMembership : leafEvent ∈
        ((visit (targetState.recordEvent leafEvent) .patternVar path').recordEvent
          (.inferredPattern (.pvar name) ⟨capability, target⟩
            (bindings ++ [(name, target)]) path')).trace.events := by
      simp [leafEvent, visit, InferState.recordEvent]
    have fresh := tracePatternLeafCheck_var bridge'.patternLeaves
      (terminalHistory.event_mem localMembership)
    have nameFresh : name ∉ bindings.names := by
      simpa using absent
    simpa [capabilityEq, targetValueEq, Dual.applySubst, Dual.apply,
      MonoCtx.applySubst, List.map_append] using
      (PatternResolutionDeriv.pvar (prevailing := terminal.prevailing)
        nameFresh fresh.1 fresh.2)
  case case43 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial capability capState capEq target targetState targetEq terminal
      bridge' terminalHistory
    have capabilityEq : capability = .var ⟨initial.supply.nextCap⟩ := by
      have equality := congrArg Prod.fst capEq
      simpa [InferState.freshCap, InferenceBase.freshCapMeta] using equality.symm
    have targetValueEq : target = .var capState.supply.nextTy := by
      have equality := congrArg Prod.fst targetEq
      simpa [InferState.freshTy, InferenceBase.freshTyMeta] using equality.symm
    let leafEvent := TraceEvent.patternWildFresh context' parameters bindings
      ⟨initial.supply.nextCap⟩ capState.supply.nextTy
    have localMembership : leafEvent ∈
        ((visit (targetState.recordEvent leafEvent) .patternWild path').recordEvent
          (.inferredPattern .wild ⟨capability, target⟩ bindings path')).trace.events := by
      simp [leafEvent, visit, InferState.recordEvent]
    have fresh := tracePatternLeafCheck_wild bridge'.patternLeaves
      (terminalHistory.event_mem localMembership)
    simpa [capabilityEq, targetValueEq, Dual.applySubst, Dual.apply] using
      (PatternResolutionDeriv.wild (prevailing := terminal.prevailing)
        fresh.1 fresh.2)
  case case45 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial expression bodyResult bodyEq capability capState capEq terminal
      bodyIH bridge' terminalHistory
    have capabilityEq :
        capability = .var ⟨bodyResult.state.supply.nextCap⟩ := by
      have equality := congrArg Prod.fst capEq
      simpa [InferState.freshCap, InferenceBase.freshCapMeta] using equality.symm
    let leafEvent := TraceEvent.patternValueFresh context' parameters bindings
      ⟨bodyResult.state.supply.nextCap⟩ bodyResult.target
    have capStateHistory : capState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent capState leafEvent).trans
        ((InferState.historyPrefix_recordEvent _
          (.inferredPattern (.pval expression) ⟨capability, bodyResult.target⟩
            bindings path')).trans terminalHistory)
    have bodyHistory : bodyResult.state.HistoryPrefix terminal :=
      (InferState.HistoryPrefix.snd_of_eq
        (InferState.historyPrefix_freshCap bodyResult.state
          (freshOrigin .pattern path' "pattern-value-capability")) capEq).trans
        capStateHistory
    have localMembership : leafEvent ∈
        ((capState.recordEvent leafEvent).recordEvent
          (.inferredPattern (.pval expression) ⟨capability, bodyResult.target⟩
            bindings path')).trace.events := by
      simp [leafEvent, InferState.recordEvent]
    have fresh := tracePatternLeafCheck_value bridge'.patternLeaves
      (terminalHistory.event_mem localMembership)
    have bodyDeriv := bodyIH bodyResult rfl terminal bridge' bodyHistory
    have bodyDeriv' : ExprDeriv signature'
        ((bindings.applySubst terminal.prevailing).toContext ++
          context'.applySubst terminal.prevailing)
        expression (terminal.prevailing.apply bodyResult.target) := by
      simpa only [Context.applySubst_append,
        MonoCtx.toContext_applySubst] using bodyDeriv
    simpa [capabilityEq, Dual.applySubst, Dual.apply] using
      (PatternResolutionDeriv.pval (prevailing := terminal.prevailing)
        fresh.1 fresh.2 bodyDeriv')
  case case47 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial name dual lookup terminal bridge' terminalHistory
    exact PatternResolutionDeriv.embed lookup (by
      rw [PatternCtx.find?_applySubst, lookup]
      rfl)
  case case49 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial patterns results patternsEq terminal patternsIH bridge'
      terminalHistory
    have resultsHistory : results.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans terminalHistory
    have children := patternsIH results rfl terminal bridge' resultsHistory
    simpa only [Dual.applySubst, Dual.apply, Cap.apply_prod,
      Subst.apply_prod, List.map_map, Function.comp_def] using
      PatternResolutionDeriv.tuple children
  case case55 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial name patterns entry lookup expecteds resultTarget instState instEq
      results patternsEq alignedState alignEq childCaps projected capability
      skeletonState result terminal projectionEq skeletonEq compatible patternsIH
      resultEq bridge' terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    let compatibilityEvent := TraceEvent.patternCtorCompatibility
      skeletonState.trace.solves.length name childCaps capability
    let inferredEvent := TraceEvent.inferredPattern (.pctor name patterns)
      ⟨capability, resultTarget⟩ results.bindings path'
    have skeletonHistory : skeletonState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent skeletonState compatibilityEvent).trans
        ((InferState.historyPrefix_recordEvent _ inferredEvent).trans
          terminalHistory)
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (freshenSkeleton_historyPrefix skeletonEq).trans skeletonHistory
    have resultsHistory : results.state.HistoryPrefix terminal :=
      (alignPatternTargets_historyPrefix alignEq).trans alignedHistory
    have children := patternsIH results rfl terminal bridge' resultsHistory
    have targetsAligned := alignPatternTargets_terminal_eq
      bridge'.typeAlignments alignEq alignedHistory
    have instHistory : instState.HistoryPrefix terminal :=
      (visit_historyPrefix instState .patternCtor path').trans
        ((inferPatternsFuel_historyPrefix patternsEq).trans resultsHistory)
    rcases instantiateCtorInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, capImages, localInstantiation⟩
    have instantiated := bridge'.instanceSuffixes.ctor_final
      (instHistory.event_mem localInstantiation)
    rw [← targetsAligned] at instantiated
    have localCompatibility : compatibilityEvent ∈
        ((skeletonState.recordEvent compatibilityEvent).recordEvent
          inferredEvent).trace.events := by
      simp [compatibilityEvent, inferredEvent, InferState.recordEvent]
    have capabilityCompatible := tracePatternCtorCheck_final
      bridge'.patternCtors (terminalHistory.event_mem localCompatibility) lookup
    have capabilityCompatible' : entry.CapCompatible
        ((results.duals.map (Dual.applySubst terminal.prevailing)).map Dual.cap)
        (((⟨capability, resultTarget⟩ : Dual).applySubst
          terminal.prevailing).cap) := by
      simpa [childCaps, Dual.applySubst, Dual.apply, List.map_map,
        Function.comp_def] using capabilityCompatible
    have instantiated' : entry.Inst
        ((results.duals.map (Dual.applySubst terminal.prevailing)).map
          Dual.target)
        (((⟨capability, resultTarget⟩ : Dual).applySubst
          terminal.prevailing).target) := by
      have prevailingEta :
          Subst.mk terminal.prevailing.cap terminal.prevailing.target =
            terminal.prevailing := by
        cases terminal.prevailing
        rfl
      simpa [Dual.applySubst, Dual.apply, List.map_map, Function.comp_def,
        prevailingEta, PatternCtorScheme.Inst] using instantiated
    exact PatternResolutionDeriv.ctor lookup children capabilityCompatible'
      instantiated'
  case case60 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial left right leftResult leftEq rightResult rightEq alignedState
      alignEq terminal leftIH rightIH bridge' terminalHistory
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans terminalHistory
    have rightHistory : rightResult.state.HistoryPrefix terminal :=
      (alignDuals_historyPrefix alignEq).trans alignedHistory
    have leftHistory : leftResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix rightEq).trans rightHistory
    have leftDeriv := leftIH leftResult rfl terminal bridge' leftHistory
    have rightDeriv := rightIH rightResult rfl terminal bridge' rightHistory
    have localAlignment := alignDuals_event_mem alignEq
    have aligned := bridge'.dualAlignments.final_eq
      (alignedHistory.event_mem localAlignment)
    have rightDeriv' : PatternResolutionDeriv signature' terminal.prevailing
        (context'.applySubst terminal.prevailing)
        (parameters.applySubst terminal.prevailing)
        (leftResult.bindings.applySubst terminal.prevailing) right
        (leftResult.dual.applySubst terminal.prevailing).cap
        (leftResult.dual.applySubst terminal.prevailing).target
        (rightResult.bindings.applySubst terminal.prevailing) := by
      rw [aligned]
      exact rightDeriv
    exact PatternResolutionDeriv.and leftDeriv rightDeriv'
  case case64 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial left right leftResult leftEq rightResult rightEq sameBindings
      alignedState alignEq result terminal leftIH rightIH resultEq bridge'
      terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans terminalHistory
    have rightHistory : rightResult.state.HistoryPrefix terminal :=
      (alignDuals_historyPrefix alignEq).trans alignedHistory
    have leftHistory : leftResult.state.HistoryPrefix terminal :=
      (inferPatternFuel_historyPrefix rightEq).trans rightHistory
    have leftDeriv := leftIH leftResult rfl terminal bridge' leftHistory
    have rightDeriv := rightIH rightResult rfl terminal bridge' rightHistory
    rw [← sameBindings] at rightDeriv
    have localAlignment := alignDuals_event_mem alignEq
    have aligned := bridge'.dualAlignments.final_eq
      (alignedHistory.event_mem localAlignment)
    have rightDeriv' : PatternResolutionDeriv signature' terminal.prevailing
        (context'.applySubst terminal.prevailing)
        (parameters.applySubst terminal.prevailing)
        (bindings.applySubst terminal.prevailing) right
        (leftResult.dual.applySubst terminal.prevailing).cap
        (leftResult.dual.applySubst terminal.prevailing).target
        (leftResult.bindings.applySubst terminal.prevailing) := by
      rw [aligned]
      exact rightDeriv
    simpa only [sameBindings] using
      PatternResolutionDeriv.or leftDeriv rightDeriv'
  case case69 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' path'
      initial name patterns scheme lookup normalizedContext normalizedParameters
      normalizedBindings expectedArgs resultDual instState results alignedState
      terminal instEq patternsEq alignEq patternsIH bridge' terminalHistory
    have alignedHistory : alignedState.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent _ _).trans terminalHistory
    have resultsHistory : results.state.HistoryPrefix terminal :=
      (alignDualLists_historyPrefix alignEq).trans alignedHistory
    have children := patternsIH results rfl terminal bridge' resultsHistory
    have argumentsAligned := alignDualLists_terminal_eq
      bridge'.dualAlignments alignEq alignedHistory
    have instHistory : instState.HistoryPrefix terminal :=
      (visit_historyPrefix instState .patternApp path').trans
        ((inferPatternsFuel_historyPrefix patternsEq).trans resultsHistory)
    rcases instantiateDualInState_event_mem_of_eq instEq with
      ⟨solveCount, supply, fixedCaps, fixedTys, reservedCaps, reservedTys,
        capImages, tyImages, localInstantiation⟩
    have instantiated := bridge'.instanceSuffixes.dual_final
      (instHistory.event_mem localInstantiation)
    rw [← argumentsAligned] at instantiated
    exact PatternResolutionDeriv.app lookup children instantiated
  case case74 =>
    rename_i fuel' signature' context' parameters bindings selfEnv' parent index
      pattern patterns initial head headEq tail tailEq terminal headIH tailIH
      bridge' terminalHistory
    have headDeriv := headIH head rfl terminal bridge'
      ((inferPatternsFuel_historyPrefix tailEq).trans terminalHistory)
    have tailDeriv := tailIH tail rfl terminal bridge' terminalHistory
    simpa only [List.map_cons] using
      PatternResolutionsDeriv.cons headDeriv tailDeriv
  case case79 =>
    rename_i fuel' signature' context' selfEnv' path' clauses initial target
      freshState freshEq clausesResult clausesEq finalHoleLists evidences
      capability finalTarget result terminal collectEq shapeEq checks clausesIH
      resultEq bridge' terminalHistory
    simp only [if_pos trivial, Option.some.injEq] at resultEq
    subst result
    let coverageEvent := TraceEvent.literalCoverage clauses capability
    let finalizationEvent := TraceEvent.matcherFinalization
      (clausesResult.state.recordEvent coverageEvent).trace.solves.length clauses
      target clausesResult.rawHoleLists
      (clausesResult.state.prevailing.apply target) finalHoleLists evidences
      capability
    have clausesHistory : clausesResult.state.HistoryPrefix terminal :=
      (InferState.historyPrefix_recordEvent clausesResult.state
        coverageEvent).trans
        ((InferState.historyPrefix_recordEvent _ finalizationEvent).trans
          terminalHistory)
    have localMembership : finalizationEvent ∈
        ((clausesResult.state.recordEvent coverageEvent).recordEvent
          finalizationEvent).trace.events := by
      simp [coverageEvent, finalizationEvent, InferState.recordEvent]
    have finalMembership := terminalHistory.event_mem localMembership
    rcases bridge'.finalizationSuffixes finalizationEvent finalMembership with
      ⟨solveBound, localTargetEq, localHolesEq, finalized⟩
    dsimp only at finalized
    rcases finalized with
      ⟨finalEvidences, finalCollect, finalShape, finalCaps, finalCatchAll,
        finalBinders, finalExhaustive, finalCoverage⟩
    have capsWitness := clauseCapsListCheck_sound finalCaps
    have evidenceWitness := collectClauseEvidence_sound finalCollect
    have clausesDeriv := clausesIH clausesResult rfl terminal bridge'
      clausesHistory (capability.apply terminal.prevailing.cap) finalEvidences
      capsWitness evidenceWitness
    have binderWitness := matcherBindersCheck_sound finalBinders
    simpa only [Subst.apply_matcher] using
      (ExprDeriv.matcher
        (ResolvedClausesDeriv.ofShared clausesDeriv) finalShape
        (catchAllLastCheck_sound finalCatchAll)
        (armExhaustiveCheck_sound finalExhaustive) binderWitness.1
        binderWitness.2 (coverageCheck_sound finalCoverage))
  case case82 =>
    rename_i n signature' context' selfEnv' path' index target initial terminal
      capability evidences bridge' terminalHistory caps evidence
    cases caps
    cases evidence
    exact ClausesDeriv.nil
  case case85 =>
    rename_i fuel' signature' context' selfEnv' parent index clause clauses
      target initial head headEq tail tailEq terminal capability evidences
      headIH tailIH bridge' terminalHistory caps evidence
    cases caps with
    | cons headCaps tailCaps =>
        cases evidence with
        | cons headEvidence tailEvidence =>
            exact ClausesDeriv.cons
              (headIH head rfl terminal bridge'
                ((inferClausesFuel_historyPrefix tailEq).trans terminalHistory)
                _ _ headCaps headEvidence)
              (tailIH tail rfl terminal bridge' terminalHistory _ _ tailCaps
                tailEvidence)
  case case91 =>
    rename_i fuel' signature' context' selfEnv' path' primitivePattern next
      arms target initial ppatResult ppatEq nextMatchers decompose slotTargets
      nextState bodyTarget armsState terminal capability evidence nextEq armsEq
      nextIH armsIH bridge' terminalHistory caps evidenceEq
    have nextStateHistory : nextState.HistoryPrefix terminal :=
      (checkArmsFuel_historyPrefix armsEq).trans terminalHistory
    have ppatHistory : ppatResult.state.HistoryPrefix terminal :=
      (checkExprsFuel_historyPrefix nextEq).trans nextStateHistory
    have ppatDeriv := inferPPatFuel_terminalAt bridge'.instanceSuffixes
      bridge'.typeAlignments bridge'.primitiveHoles ppatEq ppatHistory
    have nextDeriv := nextIH nextState rfl terminal bridge' nextStateHistory
    have nextDeriv' : ExprsDeriv signature'
        (context'.applySubst terminal.prevailing) nextMatchers
        ((ppatResult.holes.map (Dual.applySubst terminal.prevailing)).map
          (fun hole => .slot hole.cap hole.target)) := by
      simpa only [Dual.map_slot_applySubst] using nextDeriv
    have armsDeriv := armsIH armsState rfl terminal bridge' terminalHistory
    have prevailingEta :
        Subst.mk terminal.prevailing.cap terminal.prevailing.target =
          terminal.prevailing := by
      cases terminal.prevailing
      rfl
    have armsDeriv' : ArmsDeriv signature'
        (context'.applySubst terminal.prevailing)
        (terminal.prevailing.apply target)
        (ppatResult.bindings.applySubst terminal.prevailing)
        (Ty.listT (prodTy
          ((ppatResult.holes.map (Dual.applySubst terminal.prevailing)).map
            Dual.target))) arms := by
      simpa [Subst.apply_listT, Subst.apply_prodTy, Dual.applySubst,
        Dual.apply, List.map_map, Function.comp_def, prevailingEta] using
        armsDeriv
    have decompose' : decomposeME next
        (ppatResult.holes.map (Dual.applySubst terminal.prevailing)).length =
          some nextMatchers := by
      simpa using decompose
    exact ClauseDeriv.mk (clauseEvidence_coreOrder evidenceEq)
      (ResolvedPPatDeriv.ofTerminal ppatDeriv) caps
      decompose' nextDeriv' armsDeriv' evidenceEq
  case case96 =>
    rename_i fuel' signature' context' selfEnv' ppBindings parent index pattern
      body arms target bodyTarget initial dpatResult dpatEq distinct bodyContext
      bodyEnv bodyState result terminal bodyEq bodyIH tailIH resultEq bridge'
      terminalHistory
    simp only [if_pos trivial] at resultEq
    have tailHistory : result.HistoryPrefix terminal := terminalHistory
    have bodyHistory : bodyState.HistoryPrefix terminal :=
      (checkArmsFuel_historyPrefix resultEq).trans tailHistory
    have dpatHistory : dpatResult.state.HistoryPrefix terminal :=
      (checkExprFuel_historyPrefix bodyEq).trans bodyHistory
    have dpatDeriv := inferDPatFuel_reconstructAt bridge'.instanceSuffixes
      bridge'.typeAlignments dpatEq dpatHistory
    have bodyDeriv := bodyIH bodyState rfl terminal bridge' bodyHistory
    have armDeriv : ArmDeriv signature'
        (context'.applySubst terminal.prevailing)
        (terminal.prevailing.apply target)
        (ppBindings.applySubst terminal.prevailing)
        (terminal.prevailing.apply bodyTarget) (.mk pattern body) := by
      apply ArmDeriv.mk dpatDeriv
      simpa only [Context.applySubst_append,
        MonoCtx.toContext_applySubst] using bodyDeriv
    exact ArmsDeriv.cons armDeriv
      (tailIH result resultEq terminal bridge' terminalHistory)
  case case101 =>
    rename_i fuel' signature' context' selfEnv' parent index expression
      expressions expected expecteds initial middle headEq result terminal headIH
      tailIH tailEq bridge' terminalHistory
    have headDeriv := headIH middle rfl terminal bridge'
      ((checkExprsFuel_historyPrefix tailEq).trans terminalHistory)
    have tailDeriv := tailIH result rfl terminal bridge' terminalHistory
    simpa only [List.map_cons] using ExprsDeriv.cons headDeriv tailDeriv
  case case107 =>
    rename_i fuel' signature' context' selfEnv' parent index expression
      expressions initial head headEq tail tailEq terminal headIH tailIH bridge'
      terminalHistory
    have headDeriv := headIH head rfl terminal bridge'
      ((inferExprsFuel_historyPrefix tailEq).trans terminalHistory)
    have tailDeriv := tailIH tail rfl terminal bridge' terminalHistory
    simpa only [List.map_cons] using ExprsDeriv.cons headDeriv tailDeriv


end Reconstruction

/-- A successful raw W run reconstructs the proof-relevant declarative
derivation when supplied the terminal algebraic bridge.  The public wrapper
constructs this bridge internally. -/
theorem inferRaw_success_reconstruct
    {signature context expression result}
    (success : inferRaw signature context expression = some result)
    (wf : Reconstruction.WBridgeWF signature result.state) :
    Reconstruction.ExprDeriv signature
      (ResolvedContext result.state.prevailing context)
      expression result.resolvedTarget := by
  unfold inferRaw at success
  cases core : inferExprFuel (inferenceFuel expression) signature context [] []
      expression (initialState signature context) with
  | none => simp [core] at success
  | some raw =>
      have guarded : enforceProtectedResult raw = some result := by
        simpa [core] using success
      have rawEq := (enforceProtectedResult_sound guarded).1
      subst raw
      exact Reconstruction.inferExprFuel_reconstructAt wf core
        (InferState.HistoryPrefix.refl result.state)

end Inference
end TypePM
