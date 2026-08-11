import TypePM.Term
import TypePM.Projection
import TypePM.Relation
import TypePM.ClauseEvidence
import TypePM.CapMatch
import TypePM.Unification
import TypePM.DirectSelf
import TypePM.SchemeContext
import TypePM.PolyGeneralization
import TypePM.PolyInstantiation

/-!
# Declarative source layer

This module defines the source calculus of the current two-sorted core.  It
uses the two-sorted `Ty` from `TypePM.Syntax` and the source AST from
`TypePM.Term` throughout.

The signature is a finite, frozen collection of constructor and primitive
schemes.  A pattern-constructor entry also carries the certified generic
projection signature used by clause-evidence extraction.  Thus later source
typing and evidence checking consult the same canonical signature entry.
-/

namespace TypePM

/-! ## Contexts and dual schemes -/

/-- A capability/target pair `κ ▷ τ`. -/
structure Dual where
  cap : Cap
  target : Ty
deriving Repr, DecidableEq, BEq

/-- Monomorphic pattern-variable context `Δ`. -/
abbrev MonoCtx := List (String × Ty)

/-- Pattern-parameter dual context `Φ`. -/
abbrev PatternCtx := List (String × Dual)

/-- Look up a pattern-parameter dual. -/
def PatternCtx.find? (Φ : PatternCtx) (name : String) : Option Dual :=
  (List.find? (fun entry => entry.1 == name) Φ).map Prod.snd

/-- Put monomorphic pattern bindings into an expression context. -/
def MonoCtx.toContext (Δ : MonoCtx) : Context :=
  Δ.map fun entry => (entry.1, Scheme.mono entry.2)

/-- Names in a monomorphic context. -/
def MonoCtx.names (Δ : MonoCtx) : List String :=
  Δ.map Prod.fst

/-- Apply a paired substitution to a dual. -/
def Dual.apply (C : CapSubst) (T : TySubst) (dual : Dual) : Dual :=
  ⟨dual.cap.apply C, (Subst.mk C T).apply dual.target⟩

/-- Paired-substitution form of `Dual.apply`. -/
def Dual.applySubst (S : Subst) (dual : Dual) : Dual :=
  dual.apply S.cap S.target

/-- Free capability variables of a dual. -/
def Dual.fcv (dual : Dual) : List CapVar :=
  dual.cap.fcv ++ dual.target.fcv

/-- Free ordinary type variables of a dual. -/
def Dual.ftv (dual : Dual) : List TypePM.TyVar :=
  dual.target.ftv

/-- Identity substitution changes no dual. -/
@[simp] theorem Dual.applySubst_id (dual : Dual) :
    dual.applySubst Subst.id = dual := by
  cases dual with
  | mk cap target =>
      change
        Dual.mk (cap.apply CapSubst.id) (Subst.id.apply target) =
          Dual.mk cap target
      rw [Cap.apply_id, Subst.apply_id]

/-- Identity substitution changes no list of duals. -/
@[simp] theorem Dual.map_applySubst_id (duals : List Dual) :
    duals.map (Dual.applySubst Subst.id) = duals := by
  induction duals with
  | nil => rfl
  | cons dual duals ih =>
      simp only [List.map_cons, Dual.applySubst_id, ih]

/-- The capability component of paired identity changes no capability. -/
@[simp] theorem Cap.apply_substId_cap (capability : Cap) :
    capability.apply Subst.id.cap = capability := by
  exact Cap.apply_id capability

/-- Apply a paired substitution pointwise to a monomorphic context. -/
def MonoCtx.applySubst (S : Subst) (context : MonoCtx) : MonoCtx :=
  context.map fun entry => (entry.1, S.apply entry.2)

/-- Apply a paired substitution pointwise to a pattern-parameter context. -/
def PatternCtx.applySubst (S : Subst) (context : PatternCtx) : PatternCtx :=
  context.map fun entry => (entry.1, entry.2.applySubst S)

/-- Identity substitution changes no monomorphic context. -/
@[simp] theorem MonoCtx.applySubst_id (context : MonoCtx) :
    context.applySubst Subst.id = context := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      simp [MonoCtx.applySubst, Subst.apply_id]

/-- Identity substitution changes no pattern-parameter context. -/
@[simp] theorem PatternCtx.applySubst_id (context : PatternCtx) :
    context.applySubst Subst.id = context := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      simp [PatternCtx.applySubst]

/-- A separately quantified pattern-function dual scheme. -/
structure DualScheme where
  capBinders : List CapVar
  tyBinders : List TypePM.TyVar
  args : List Dual
  result : Dual
deriving Repr

/-- Free capability variables of a dual scheme, excluding its binders. -/
def DualScheme.fcv (scheme : DualScheme) : List CapVar :=
  (scheme.args.flatMap Dual.fcv ++ scheme.result.fcv).filter
    fun varId => varId ∉ scheme.capBinders

/-- Free ordinary type variables of a dual scheme, excluding its binders. -/
def DualScheme.ftv (scheme : DualScheme) : List TypePM.TyVar :=
  (scheme.args.flatMap Dual.ftv ++ scheme.result.ftv).filter
    fun varId => varId ∉ scheme.tyBinders

/-- Every capability-variable name occurring in a dual scheme. -/
def DualScheme.allCapVars (scheme : DualScheme) : List CapVar :=
  scheme.capBinders ++ scheme.args.flatMap Dual.fcv ++ scheme.result.fcv

/-- Every ordinary-variable name occurring in a dual scheme. -/
def DualScheme.allTyVars (scheme : DualScheme) : List TypePM.TyVar :=
  scheme.tyBinders ++ scheme.args.flatMap Dual.ftv ++ scheme.result.ftv

/-- Simultaneous two-sorted instantiation of a dual scheme. -/
def DualScheme.Inst
    (scheme : DualScheme) (args : List Dual) (result : Dual) : Prop :=
  ∃ C T,
    C.SupportWithin scheme.capBinders ∧
    T.SupportWithin scheme.tyBinders ∧
    scheme.args.map (Dual.apply C T) = args ∧
    scheme.result.apply C T = result

/-! ## Frozen signature -/

/-- A quantified constructor/primitive arrow `args → result`. -/
structure CtorScheme where
  capBinders : List CapVar
  tyBinders : List TypePM.TyVar
  args : List Ty
  result : Ty
deriving Repr, DecidableEq

/-- Two-sorted instantiation of one constructor/primitive scheme. -/
def CtorScheme.Inst
    (scheme : CtorScheme) (args : List Ty) (result : Ty) : Prop :=
  ∃ C T,
    C.SupportWithin scheme.capBinders ∧
    T.SupportWithin scheme.tyBinders ∧
    scheme.args.map (Subst.mk C T).apply = args ∧
    (Subst.mk C T).apply scheme.result = result

/--
A frozen pattern-constructor entry.

The projection input is definitionally tied, by the two equality fields, to
the same generic scheme used by PP and user-pattern typing.
-/
structure PatternCtorScheme (observable : Shape.Observability) where
  scheme : CtorScheme
  projection : Projection.ProjectionSignature observable
  projectionFields : projection.fieldTypes = scheme.args
  projectionResult : projection.resultType = scheme.result

/-- Instantiate the ordinary type side of a pattern-constructor entry. -/
def PatternCtorScheme.Inst
    {observable : Shape.Observability}
    (entry : PatternCtorScheme observable)
    (args : List Ty) (result : Ty) : Prop :=
  entry.scheme.Inst args result

/--
Finite canonical signature `Σ̂` consumed by source checking.

All names and projection roots are resolved before this structure is built.
The lists are the frozen lookup tables; malformed/raw signature validation is
outside the source calculus.
-/
structure FrozenSig where
  observability : Shape.Observability
  dataCtors : List (String × CtorScheme)
  patternCtors : List (String × PatternCtorScheme observability)
  patternFuns : List (String × DualScheme)
  primitives : List (PrimOp × CtorScheme)
  constructorsByFormer : List (String × List GeneralCtor)
  /-- Frozen deterministic data-pattern exhaustiveness checker. -/
  armExhaustive : List DPat → Ty → Bool

/-- Frozen data-constructor lookup. -/
def FrozenSig.findDataCtor
    (signature : FrozenSig) (name : String) : Option CtorScheme :=
  (signature.dataCtors.find? (fun entry => entry.1 == name)).map Prod.snd

/-- Frozen pattern-constructor lookup. -/
def FrozenSig.findPatternCtor
    (signature : FrozenSig) (name : String) :
    Option (PatternCtorScheme signature.observability) :=
  (signature.patternCtors.find? (fun entry => entry.1 == name)).map Prod.snd

/-- Frozen pattern-function lookup. -/
def FrozenSig.findPatternFun
    (signature : FrozenSig) (name : String) : Option DualScheme :=
  (signature.patternFuns.find? (fun entry => entry.1 == name)).map Prod.snd

/-- Frozen primitive-operation lookup. -/
def FrozenSig.findPrimitive
    (signature : FrozenSig) (op : PrimOp) : Option CtorScheme :=
  (signature.primitives.find? (fun entry => entry.1 == op)).map Prod.snd

/-- Forget full frozen declarations and retain the concrete matcher checker. -/
def FrozenSig.toMatcherSig (signature : FrozenSig) : FrozenMatcherSig where
  observability := signature.observability
  patternConstructors :=
    signature.patternCtors.map fun entry => (entry.1, entry.2.projection)
  constructorsByFormer := signature.constructorsByFormer

/--
A constructor's partial projection is compatible with a complete outer
capability when exact evidence merge fills only the projection's unseen
positions.  In particular, a nullary constructor may leave an observable
result parameter unseen; the surrounding matcher capability supplies it.
-/
def PatternCtorScheme.CapCompatible
    {observable : Shape.Observability}
    (entry : PatternCtorScheme observable)
    (children : List Cap) (outer : Cap) : Prop :=
  ∃ projected,
    Projection.projectSignature entry.projection
        (children.map Shape.ofCap) = some projected ∧
      Shape.merge projected (Shape.ofCap outer) =
        some (Shape.ofCap outer)

/-- Capability variables mentioned by a constructor scheme. -/
def CtorScheme.capVars (scheme : CtorScheme) : List CapVar :=
  scheme.capBinders ++ Ty.fcvList scheme.args ++ scheme.result.fcv

/-- Ordinary type variables mentioned by a constructor scheme. -/
def CtorScheme.tyVars (scheme : CtorScheme) : List TypePM.TyVar :=
  scheme.tyBinders ++ Ty.ftvList scheme.args ++ scheme.result.ftv

/-- Free capability variables of a constructor scheme. -/
def CtorScheme.fcv (scheme : CtorScheme) : List CapVar :=
  (Ty.fcvList scheme.args ++ scheme.result.fcv).filter
    fun varId => varId ∉ scheme.capBinders

/-- Free ordinary variables of a constructor scheme. -/
def CtorScheme.ftv (scheme : CtorScheme) : List TypePM.TyVar :=
  (Ty.ftvList scheme.args ++ scheme.result.ftv).filter
    fun varId => varId ∉ scheme.tyBinders

/-- Capability variables mentioned by a dual scheme. -/
def DualScheme.capVars (scheme : DualScheme) : List CapVar :=
  scheme.capBinders ++
    (scheme.args.flatMap fun dual => dual.cap.fcv ++ dual.target.fcv) ++
    scheme.result.cap.fcv ++ scheme.result.target.fcv

/-- Ordinary type variables mentioned by a dual scheme. -/
def DualScheme.tyVars (scheme : DualScheme) : List TypePM.TyVar :=
  scheme.tyBinders ++ scheme.args.flatMap Dual.ftv ++ scheme.result.ftv

/-- Capability variables already reserved by a frozen signature. -/
def FrozenSig.capVars (signature : FrozenSig) : List CapVar :=
  signature.dataCtors.flatMap (fun entry => entry.2.capVars) ++
  signature.patternCtors.flatMap (fun entry => entry.2.scheme.capVars) ++
  signature.patternFuns.flatMap (fun entry => entry.2.capVars) ++
  signature.primitives.flatMap (fun entry => entry.2.capVars)

/-- Ordinary type variables already reserved by a frozen signature. -/
def FrozenSig.tyVars (signature : FrozenSig) : List TypePM.TyVar :=
  signature.dataCtors.flatMap (fun entry => entry.2.tyVars) ++
  signature.patternCtors.flatMap (fun entry => entry.2.scheme.tyVars) ++
  signature.patternFuns.flatMap (fun entry => entry.2.tyVars) ++
  signature.primitives.flatMap (fun entry => entry.2.tyVars)

/-- Free capability variables of a frozen signature, excluding scheme binders. -/
def FrozenSig.fcv (signature : FrozenSig) : List CapVar :=
  signature.dataCtors.flatMap (fun entry => entry.2.fcv) ++
  signature.patternCtors.flatMap (fun entry => entry.2.scheme.fcv) ++
  signature.patternFuns.flatMap (fun entry => entry.2.fcv) ++
  signature.primitives.flatMap (fun entry => entry.2.fcv)

/-- Free ordinary variables of a frozen signature, excluding scheme binders. -/
def FrozenSig.ftv (signature : FrozenSig) : List TypePM.TyVar :=
  signature.dataCtors.flatMap (fun entry => entry.2.ftv) ++
  signature.patternCtors.flatMap (fun entry => entry.2.scheme.ftv) ++
  signature.patternFuns.flatMap (fun entry => entry.2.ftv) ++
  signature.primitives.flatMap (fun entry => entry.2.ftv)

/-! ## Closed frozen signatures -/

/-- A constructor scheme with no free variables outside its binders. -/
def CtorScheme.Closed (scheme : CtorScheme) : Prop :=
  scheme.fcv = [] ∧ scheme.ftv = []

/-- A dual scheme with no free variables outside its binders. -/
def DualScheme.Closed (scheme : DualScheme) : Prop :=
  scheme.fcv = [] ∧ scheme.ftv = []

instance : DecidablePred CtorScheme.Closed := fun scheme =>
  decidable_of_iff (scheme.fcv = [] ∧ scheme.ftv = []) Iff.rfl

instance : DecidablePred DualScheme.Closed := fun scheme =>
  decidable_of_iff (scheme.fcv = [] ∧ scheme.ftv = []) Iff.rfl

/-- Every scheme in the complete frozen tables is closed.  Lookup fields make
the property convenient to consume, while the final two fields also cover
entries shadowed by an earlier table key. -/
structure FrozenSig.SchemesClosed (signature : FrozenSig) : Prop where
  dataCtors : ∀ {name : String} {scheme : CtorScheme},
    signature.findDataCtor name = some scheme → scheme.Closed
  patternCtors : ∀ {name : String}
    {entry : PatternCtorScheme signature.observability},
    signature.findPatternCtor name = some entry → entry.scheme.Closed
  patternFuns : ∀ {name : String} {scheme : DualScheme},
    signature.findPatternFun name = some scheme → scheme.Closed
  primitives : ∀ {op : PrimOp} {scheme : CtorScheme},
    signature.findPrimitive op = some scheme → scheme.Closed
  /-- The complete table representation carries no free capability
  metavariables, including entries shadowed by lookup. -/
  signatureCaps : signature.fcv = []
  /-- Ordinary free metavariables are absent from the complete table
  representation as well. -/
  signatureTargets : signature.ftv = []

/-- Entry-wise sufficient condition for signature closedness. -/
theorem FrozenSig.SchemesClosed.of_entries {signature : FrozenSig}
    (dataClosed : ∀ entry ∈ signature.dataCtors, entry.2.Closed)
    (patternClosed : ∀ entry ∈ signature.patternCtors,
      entry.2.scheme.Closed)
    (funClosed : ∀ entry ∈ signature.patternFuns, entry.2.Closed)
    (primClosed : ∀ entry ∈ signature.primitives, entry.2.Closed) :
    signature.SchemesClosed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name scheme hfind
    unfold FrozenSig.findDataCtor at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.dataCtors with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact dataClosed entry (List.mem_of_find?_eq_some hlist)
  · intro name entry hfind
    unfold FrozenSig.findPatternCtor at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.patternCtors with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some found =>
        rw [hlist] at hfind
        cases hfind
        exact patternClosed found (List.mem_of_find?_eq_some hlist)
  · intro name scheme hfind
    unfold FrozenSig.findPatternFun at hfind
    cases hlist : List.find? (fun entry => entry.1 == name)
        signature.patternFuns with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact funClosed entry (List.mem_of_find?_eq_some hlist)
  · intro op scheme hfind
    unfold FrozenSig.findPrimitive at hfind
    cases hlist : List.find? (fun entry => entry.1 == op)
        signature.primitives with
    | none => rw [hlist] at hfind; exact nomatch hfind
    | some entry =>
        rw [hlist] at hfind
        cases hfind
        exact primClosed entry (List.mem_of_find?_eq_some hlist)
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro varId membership
    simp only [FrozenSig.fcv, List.mem_append] at membership
    rcases membership with ((dataMem | patternMem) | funMem) | primMem
    · rcases List.mem_flatMap.mp dataMem with
        ⟨entry, entryMem, varMem⟩
      rw [(dataClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp patternMem with
        ⟨entry, entryMem, varMem⟩
      rw [(patternClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp funMem with
        ⟨entry, entryMem, varMem⟩
      rw [(funClosed entry entryMem).1] at varMem
      contradiction
    · rcases List.mem_flatMap.mp primMem with
        ⟨entry, entryMem, varMem⟩
      rw [(primClosed entry entryMem).1] at varMem
      contradiction
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro varId membership
    simp only [FrozenSig.ftv, List.mem_append] at membership
    rcases membership with ((dataMem | patternMem) | funMem) | primMem
    · rcases List.mem_flatMap.mp dataMem with
        ⟨entry, entryMem, varMem⟩
      rw [(dataClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp patternMem with
        ⟨entry, entryMem, varMem⟩
      rw [(patternClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp funMem with
        ⟨entry, entryMem, varMem⟩
      rw [(funClosed entry entryMem).2] at varMem
      contradiction
    · rcases List.mem_flatMap.mp primMem with
        ⟨entry, entryMem, varMem⟩
      rw [(primClosed entry entryMem).2] at varMem
      contradiction

/-- Capability metavariables selected by signature-aware generalization. -/
def FrozenSig.generalizedCapVars
    (signature : FrozenSig) (context : Context) (target : Ty) : List CapVar :=
  TypePM.generalizedCapVars (signature.fcv ++ context.fcv) target

/-- Target metavariables selected by signature-aware generalization. -/
def FrozenSig.generalizedTyVars
    (signature : FrozenSig) (context : Context) (target : Ty) :
    List TypePM.TyVar :=
  TypePM.generalizedTyVars (signature.ftv ++ context.ftv) target

/--
Generalize a normalized type relative to both the frozen global signature and
the local expression context.  Global free variables are never quantified.
The selected solver names are immediately closed into finite local indices.
-/
def FrozenSig.generalize
    (signature : FrozenSig) (context : Context) (target : Ty) : Scheme :=
  Scheme.generalize
    (signature.fcv ++ context.fcv) (signature.ftv ++ context.ftv) target

/-- Capability occurrences in the complete pattern-function payload.  The
list intentionally retains duplicates: multiplicity records whether a local
capability expresses sharing between two or more positions. -/
def dualCapOccurrences (args : List Dual) (result : Dual) : List CapVar :=
  args.flatMap Dual.fcv ++ result.fcv

/-- Local payload capabilities that occur exactly once.  Ambient variables
are excluded before defaulting, but occurrence counts are always taken over
the complete argument/result payload. -/
def dualSingletonCaps (ambient : List CapVar)
    (args : List Dual) (result : Dual) : List CapVar :=
  let occurrences := dualCapOccurrences args result
  uniqueVars (occurrences.filter fun varId =>
    varId ∉ ambient ∧ occurrences.count varId = 1)

/-- Local payload capabilities whose repeated occurrences carry observable
sharing and therefore remain quantified. -/
def dualSharedCaps (ambient : List CapVar)
    (args : List Dual) (result : Dual) : List CapVar :=
  let singletons := dualSingletonCaps ambient args result
  let C : CapSubst := fun varId =>
    if varId ∈ singletons then .any else .var varId
  let normalizedArgs := args.map (Dual.apply C TySubst.id)
  let normalizedResult := result.apply C TySubst.id
  uniqueVars
    ((dualCapOccurrences normalizedArgs normalizedResult).filter fun varId =>
      varId ∉ ambient)

/-- Replace only non-ambient singleton capability variables by `Any`. -/
def singletonDefaultSubst (ambient : List CapVar)
    (args : List Dual) (result : Dual) : CapSubst :=
  let singletons := dualSingletonCaps ambient args result
  fun varId => if varId ∈ singletons then .any else .var varId

/-- Normalize all capability occurrences of a dual with the same singleton
defaulting substitution. -/
def normalizeDualSingletons (ambient : List CapVar)
    (args : List Dual) (result : Dual) : List Dual × Dual :=
  let C := singletonDefaultSubst ambient args result
  (args.map (Dual.apply C TySubst.id), result.apply C TySubst.id)

/--
Signature-aware dual generalization for pattern-function definitions.

Non-ambient capability variables are classified by their occurrence count in
the *whole* argument/result payload.  Singletons carry no sharing information
and are canonicalized to `Any`; variables occurring at least twice are
quantified once and retain their repeated identity.  Ambient variables remain
free and are never defaulted or quantified.
-/
def FrozenSig.generalizeDual
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) : DualScheme :=
  let ambientCaps := signature.fcv ++ context.fcv
  let normalized := normalizeDualSingletons ambientCaps args result
  let tyVars := normalized.1.flatMap Dual.ftv ++ normalized.2.ftv
  { capBinders := dualSharedCaps ambientCaps args result
    tyBinders :=
      uniqueVars (tyVars.filter fun varId =>
        varId ∉ signature.ftv ++ context.ftv)
    args := normalized.1
    result := normalized.2 }

/-- Singleton defaulting preserves the pattern-function arity. -/
@[simp] theorem normalizeDualSingletons_args_length
    (ambient : List CapVar) (args : List Dual) (result : Dual) :
    (normalizeDualSingletons ambient args result).1.length = args.length := by
  simp [normalizeDualSingletons]

/-- Dual generalization changes capabilities but never the argument arity. -/
@[simp] theorem FrozenSig.generalizeDual_args_length
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) :
    (signature.generalizeDual context args result).args.length = args.length := by
  simp [FrozenSig.generalizeDual]

/-- Free capability variables in a monomorphic context. -/
def MonoCtx.fcv (context : MonoCtx) : List CapVar :=
  context.flatMap fun entry => entry.2.fcv

/-- Free ordinary variables in a monomorphic context. -/
def MonoCtx.ftv (context : MonoCtx) : List TypePM.TyVar :=
  context.flatMap fun entry => entry.2.ftv

/-- Free capability variables in a pattern-parameter context. -/
def PatternCtx.fcv (context : PatternCtx) : List CapVar :=
  context.flatMap fun entry => entry.2.fcv

/-- Free ordinary variables in a pattern-parameter context. -/
def PatternCtx.ftv (context : PatternCtx) : List TypePM.TyVar :=
  context.flatMap fun entry => entry.2.ftv

/-! ## Dual-scheme fresh instantiation and value flow

Expression schemes use the capture-free opening relations from
`PolyInstantiation`.  Dual schemes use their separate support-restricted
instantiation boundary. -/

/-- One explicit fresh dual-scheme instance and its allocated images. -/
structure DualScheme.FreshInstAt
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (C : CapSubst) (T : TySubst)
    (capImages : List CapVar) (tyImages : List TypePM.TyVar)
    (scheme : DualScheme) (args : List Dual) (result : Dual) : Prop where
  capSupport : C.SupportWithin scheme.capBinders
  tySupport : T.SupportWithin scheme.tyBinders
  capImageVars : scheme.capBinders.map C = capImages.map Cap.var
  tyImageVars : scheme.tyBinders.map T = tyImages.map Ty.var
  capImagesNodup : capImages.Nodup
  tyImagesNodup : tyImages.Nodup
  capImagesFresh : ∀ image, image ∈ capImages → image ∉ reservedCaps
  tyImagesFresh : ∀ image, image ∈ tyImages → image ∉ reservedTys
  rangeFixed : (Subst.mk C T).RangeFixed
  argsResult : scheme.args.map (Dual.apply C T) = args
  resultResult : scheme.result.apply C T = result

/-- Declarative capability-variable/structural-target instance of a dual scheme. -/
structure DualScheme.VariableInstAt
    (C : CapSubst) (T : TySubst)
    (scheme : DualScheme) (args : List Dual) (result : Dual) : Prop where
  capSupport : C.SupportWithin scheme.capBinders
  tySupport : T.SupportWithin scheme.tyBinders
  capBinderVariable :
    ∀ varId, varId ∈ scheme.capBinders → ∃ image, C varId = .var image
  argsResult : scheme.args.map (Dual.apply C T) = args
  resultResult : scheme.result.apply C T = result

/-- Forget Algorithm W's dual allocation facts at the declarative boundary. -/
def DualScheme.FreshInstAt.toVariableInstAt
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {C : CapSubst} {T : TySubst}
    {capImages : List CapVar} {tyImages : List TypePM.TyVar}
    {scheme : DualScheme} {args : List Dual} {result : Dual}
    (freshInstance : scheme.FreshInstAt reservedCaps reservedTys
      C T capImages tyImages args result) :
    scheme.VariableInstAt C T args result := by
  refine
    { capSupport := freshInstance.capSupport
      tySupport := freshInstance.tySupport
      capBinderVariable := ?_
      argsResult := freshInstance.argsResult
      resultResult := freshInstance.resultResult }
  intro varId membership
  have imageMembership : C varId ∈ capImages.map Cap.var := by
    rw [← freshInstance.capImageVars]
    exact List.mem_map.mpr ⟨varId, membership, rfl⟩
  rcases List.mem_map.mp imageMembership with ⟨image, _, equality⟩
  exact ⟨image, equality.symm⟩

/-- Existential paper-style fresh dual instantiation. -/
def DualScheme.FreshInst
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (scheme : DualScheme) (args : List Dual) (result : Dual) : Prop :=
  ∃ C T capImages tyImages,
    scheme.FreshInstAt reservedCaps reservedTys C T capImages tyImages
      args result

/--
Safe dual value flow with a binder-supported capability-variable action and
an independently binder-supported, possibly structural target action.  It
does not require fresh or distinct images.
-/
def DualScheme.ValueFlowInst
    (scheme : DualScheme) (args : List Dual) (result : Dual) : Prop :=
  ∃ C T, scheme.VariableInstAt C T args result

/-- A declarative dual instance is variable-only globally on capabilities. -/
theorem DualScheme.VariableInstAt.capVariable
    {C : CapSubst} {T : TySubst} {scheme : DualScheme}
    {args : List Dual} {result : Dual}
    (instanceTyping : scheme.VariableInstAt C T args result)
    (varId : CapVar) : ∃ image, C varId = .var image := by
  by_cases membership : varId ∈ scheme.capBinders
  · exact instanceTyping.capBinderVariable varId membership
  · exact ⟨varId, instanceTyping.capSupport varId membership⟩

/-- A fresh dual-scheme instance is already a safe dual value-flow instance. -/
theorem DualScheme.FreshInstAt.toValueFlowInst
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {C : CapSubst} {T : TySubst}
    {capImages : List CapVar} {tyImages : List TypePM.TyVar}
    {scheme : DualScheme} {args : List Dual} {result : Dual}
    (freshInstance : scheme.FreshInstAt reservedCaps reservedTys
      C T capImages tyImages args result) :
    scheme.ValueFlowInst args result :=
  ⟨C, T, freshInstance.toVariableInstAt⟩

/-- Free ambient capability variables reserved by expression-scheme lookup. -/
def SourceCapScope (signature : FrozenSig) (context : Context) : List CapVar :=
  signature.fcv ++ context.fcv

/-- Free ambient ordinary variables reserved by expression-scheme lookup. -/
def SourceTyScope
    (signature : FrozenSig) (context : Context) : List TypePM.TyVar :=
  signature.ftv ++ context.ftv

/-- Free ambient capability variables that a source post must leave fixed. -/
def SourceFixedCapScope
    (signature : FrozenSig) (context : Context) : List CapVar :=
  signature.fcv ++ context.fcv

/-- Free ambient ordinary variables that a source post must leave fixed. -/
def SourceFixedTyScope
    (signature : FrozenSig) (context : Context) : List TypePM.TyVar :=
  signature.ftv ++ context.ftv

/-- Free ambient capability variables reserved by pattern-function lookup. -/
def PatternCapScope
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) : List CapVar :=
  signature.fcv ++ context.fcv ++ parameters.fcv ++ bindings.fcv

/-- Free ambient ordinary variables reserved by pattern-function lookup. -/
def PatternTyScope
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) : List TypePM.TyVar :=
  signature.ftv ++ context.ftv ++ parameters.ftv ++ bindings.ftv

/-- Free ambient capability variables that a pattern post must leave fixed. -/
def PatternFixedCapScope
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) : List CapVar :=
  signature.fcv ++ context.fcv ++ parameters.fcv ++ bindings.fcv

/-- Free ambient ordinary variables that a pattern post must leave fixed. -/
def PatternFixedTyScope
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx) : List TypePM.TyVar :=
  signature.ftv ++ context.ftv ++ parameters.ftv ++ bindings.ftv

/-! ## Restricted post-solver transformations -/

/-- Sequencing any later substitution onto an idempotent prevailing
substitution absorbs the prevailing action. -/
theorem Subst.seq_absorbs_of_idempotent {S : Subst}
    (idem : S.Idempotent) (U : Subst) (target : Ty) :
    (Subst.seq U S).apply (S.apply target) =
      (Subst.seq U S).apply target := by
  rw [Subst.seq_apply, Subst.seq_apply, idem]

/-- A solved-form later substitution whose images are fixed by the earlier
substitution yields a solved-form sequential composition. -/
theorem Subst.seq_idempotent {S delta : Subst}
    (idemDelta : delta.Idempotent)
    (fixed : ∀ target : Ty,
      S.apply (delta.apply (S.apply target)) =
        delta.apply (S.apply target)) :
    (Subst.seq delta S).Idempotent := by
  intro target
  rw [Subst.seq_apply, Subst.seq_apply, fixed, idemDelta]

/--
The declarative suffix condition: capability variables remain capability
variables.  `RestrictedPost` can additionally record freshness, distinct
images, and finite allocation domains, but terminal certified inference may
construct this declarative condition directly when those facts are unused.
-/
structure VariablePost (post : Subst) : Prop where
  capVariable : ∀ varId, ∃ image, post.cap varId = .var image

/-- Identity is a declarative capability-variable post. -/
def VariablePost.id : VariablePost Subst.id where
  capVariable := by intro varId; exact ⟨varId, rfl⟩

/-- Sequential application preserves the capability-variable condition. -/
theorem VariablePost.seq
    {later earlier : Subst}
    (laterVariable : VariablePost later)
    (earlierVariable : VariablePost earlier) :
    VariablePost (Subst.seq later earlier) := by
  constructor
  intro varId
  rcases earlierVariable.capVariable varId with ⟨middle, middleEquation⟩
  rcases laterVariable.capVariable middle with ⟨image, imageEquation⟩
  exact ⟨image, by
    simp only [Subst.seq, CapSubst.comp, middleEquation, Cap.apply]
    exact imageEquation⟩

/-- The total capability-variable mapping represented by a declarative post. -/
noncomputable def VariablePost.capRen
    {post : Subst} (postVariable : VariablePost post) (varId : CapVar) : CapVar :=
  Classical.choose (postVariable.capVariable varId)

/-- A declarative post is pointwise its selected capability-variable mapping. -/
theorem VariablePost.capEquation
    {post : Subst} (postVariable : VariablePost post) (varId : CapVar) :
    post.cap varId = .var (postVariable.capRen varId) :=
  Classical.choose_spec (postVariable.capVariable varId)

mutual

/-- Applying a variable-valued capability substitution is pointwise mapping. -/
theorem VariablePost.applyCap_eq_applyRen
    {post : Subst} (postVariable : VariablePost post) (capability : Cap) :
    capability.apply post.cap = capability.applyRen postVariable.capRen := by
  cases capability with
  | any => rfl
  | var varId => exact postVariable.capEquation varId
  | skolem name => rfl
  | con name children =>
      simp only [Cap.apply, Cap.applyRen]
      rw [postVariable.applyCapList_eq_applyRenList]
  | prod components =>
      simp only [Cap.apply, Cap.applyRen]
      rw [postVariable.applyCapList_eq_applyRenList]

/-- List form of `VariablePost.applyCap_eq_applyRen`. -/
theorem VariablePost.applyCapList_eq_applyRenList
    {post : Subst} (postVariable : VariablePost post)
    (capabilities : List Cap) :
    Cap.applyList post.cap capabilities =
      Cap.applyRenList postVariable.capRen capabilities := by
  cases capabilities with
  | nil => rfl
  | cons head tail =>
      simp only [Cap.applyList, Cap.applyRenList]
      rw [postVariable.applyCap_eq_applyRen,
        postVariable.applyCapList_eq_applyRenList]

end

/--
One solver-post transformation.

The capability component is a finite variable-only renaming.  It is identity
outside the declared domain and fresh-image support, every variable maps to a
flexible variable, and the designated domain images are duplicate-free and
fresh for the ambient scope.  It need not be a global permutation: the initial
fresh instance maps a binder to a new name while leaving that new name fixed.
Structural capability images are therefore impossible without excluding valid
scheme instances.  The ordinary component has finite support in `tyDomain`.
Application is ordered capability-then-target, so a target image may mention a
name that is locally bound on the capability side without being captured.
-/
structure RestrictedPost
    (fixedCaps : List CapVar) (fixedTys : List TypePM.TyVar)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (capDomain : List CapVar) (tyDomain : List TypePM.TyVar)
    (capImages : List CapVar) (post : Subst) : Prop where
  /-- The finite variable-only renaming may mention its fresh images. -/
  capSupport : post.cap.SupportWithin (capDomain ++ capImages)
  tySupport : post.target.SupportWithin tyDomain
  capDomainNodup : capDomain.Nodup
  tyDomainNodup : tyDomain.Nodup
  capImageVars : capDomain.map post.cap = capImages.map Cap.var
  capImagesNodup : capImages.Nodup
  /-- Every capability variable is mapped to another capability variable. -/
  capVariable : ∀ varId, ∃ image, post.cap varId = .var image
  capDomainFresh : ∀ varId, varId ∈ capDomain → varId ∉ fixedCaps
  tyDomainFresh : ∀ varId, varId ∈ tyDomain → varId ∉ fixedTys
  capImagesFixedFresh :
    ∀ varId, varId ∈ capImages → varId ∉ fixedCaps
  capImagesFresh : ∀ varId, varId ∈ capImages → varId ∉ reservedCaps

/--
A post chain retains every atomic freshness certificate.  Its index uses
cross-sort-aware sequential composition, so extending the chain applies the
later capability action inside earlier target ranges without replaying raw
`mgu`/`matchCap` evidence or assuming a false commutation equation.
-/
inductive RestrictedPost.Chain
    (fixedCaps : List CapVar) (fixedTys : List TypePM.TyVar)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar) :
    Subst → Prop where
  | one {post} :
      RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
        capDomain tyDomain capImages post →
      Chain fixedCaps fixedTys reservedCaps reservedTys post
  | comp {later earlier} :
      Chain fixedCaps fixedTys reservedCaps reservedTys earlier →
      RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
        capDomain tyDomain capImages later →
      Chain fixedCaps fixedTys reservedCaps reservedTys
        (Subst.seq later earlier)

/-- Identity is the empty restricted post. -/
def RestrictedPost.id
    (fixedCaps : List CapVar) (fixedTys : List TypePM.TyVar)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar) :
    RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      [] [] [] Subst.id where
  capSupport := CapSubst.id_supportWithin []
  tySupport := TySubst.id_supportWithin []
  capDomainNodup := List.nodup_nil
  tyDomainNodup := List.nodup_nil
  capImageVars := rfl
  capImagesNodup := List.nodup_nil
  capVariable := by intro varId; exact ⟨varId, rfl⟩
  capDomainFresh := by intros; contradiction
  tyDomainFresh := by intros; contradiction
  capImagesFixedFresh := by intros; contradiction
  capImagesFresh := by intros; contradiction

/--
Identity may retain nonempty protected domains.  This is the common suffix
when later solving leaves a fresh value instance untouched.
-/
def RestrictedPost.identityOnDomains
    (fixedCaps : List CapVar) (fixedTys : List TypePM.TyVar)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar)
    (capDomain : List CapVar) (tyDomain : List TypePM.TyVar)
    (capDomainNodup : capDomain.Nodup)
    (tyDomainNodup : tyDomain.Nodup)
    (capDomainFresh :
      ∀ varId, varId ∈ capDomain → varId ∉ fixedCaps)
    (tyDomainFresh :
      ∀ varId, varId ∈ tyDomain → varId ∉ fixedTys)
    (capDomainReservedFresh :
      ∀ varId, varId ∈ capDomain → varId ∉ reservedCaps) :
    RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capDomain Subst.id where
  capSupport := CapSubst.id_supportWithin _
  tySupport := TySubst.id_supportWithin _
  capDomainNodup := capDomainNodup
  tyDomainNodup := tyDomainNodup
  capImageVars := by
    induction capDomain with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.map_cons]
        congr
  capImagesNodup := capDomainNodup
  capVariable := by intro varId; exact ⟨varId, rfl⟩
  capDomainFresh := capDomainFresh
  tyDomainFresh := tyDomainFresh
  capImagesFixedFresh := capDomainFresh
  capImagesFresh := capDomainReservedFresh

/-- Identity as a one-element post chain. -/
def RestrictedPost.Chain.id
    (fixedCaps : List CapVar) (fixedTys : List TypePM.TyVar)
    (reservedCaps : List CapVar) (reservedTys : List TypePM.TyVar) :
    RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      Subst.id :=
  .one (RestrictedPost.id fixedCaps fixedTys reservedCaps reservedTys)

/-! ## Signature-aware generalized-instance posts -/

/--
The non-typing certificate for one instance of a let-generalized source type.
Its only movable names are the binders selected by signature-aware
generalization; capability movement has only fresh variable images and target
movement is restricted to the generalized ordinary binders.
-/
structure GeneralizedPost
    (signature : FrozenSig) (context : Context)
    (source target : Ty) (capImages : List CapVar) (post : Subst) : Prop where
  restricted :
    RestrictedPost
      (SourceFixedCapScope signature context)
      (SourceFixedTyScope signature context)
      (SourceCapScope signature context)
      (SourceTyScope signature context)
      (signature.generalizedCapVars context source)
      (signature.generalizedTyVars context source)
      capImages post
  contextFixed : context.applySubst post = context
  result : post.apply source = target

/-- A generalized post can be retained as the first suffix-chain node. -/
def GeneralizedPost.toChain
    {signature : FrozenSig} {context : Context}
    {source target : Ty} {capImages : List CapVar} {post : Subst}
    (generalized :
      GeneralizedPost signature context source target capImages post) :
    RestrictedPost.Chain
      (SourceFixedCapScope signature context)
      (SourceFixedTyScope signature context)
      (SourceCapScope signature context)
      (SourceTyScope signature context) post :=
  .one generalized.restricted

/--
Dual analogue used to specialize a raw pattern-function body at concrete
argument/result duals without storing an arbitrary actual `PatternTy` proof.
-/
structure GeneralizedDualPost
    (signature : FrozenSig) (context : Context)
    (sourceArgs : List Dual) (sourceResult : Dual)
    (targetArgs : List Dual) (targetResult : Dual)
    (capImages : List CapVar) (post : Subst) : Prop where
  restricted :
    RestrictedPost
      (SourceFixedCapScope signature context)
      (SourceFixedTyScope signature context)
      (SourceCapScope signature context)
      (SourceTyScope signature context)
      (signature.generalizeDual context sourceArgs sourceResult).capBinders
      (signature.generalizeDual context sourceArgs sourceResult).tyBinders
      capImages post
  contextFixed : context.applySubst post = context
  argsResult :
    (signature.generalizeDual context sourceArgs sourceResult).args.map
      (Dual.applySubst post) = targetArgs
  resultResult :
    (signature.generalizeDual context sourceArgs sourceResult).result.applySubst
      post = targetResult

/-- An atomic post fixes every ambient free capability variable. -/
theorem RestrictedPost.capFixed
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar} {post : Subst}
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages post)
    {varId : CapVar} (ambient : varId ∈ fixedCaps) :
    post.cap varId = .var varId := by
  apply restricted.capSupport varId
  simp only [List.mem_append, not_or]
  exact ⟨fun domain => restricted.capDomainFresh varId domain ambient,
    fun image => restricted.capImagesFixedFresh varId image ambient⟩

/-- An atomic post fixes every ambient free ordinary variable. -/
theorem RestrictedPost.tyFixed
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar} {post : Subst}
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages post)
    {varId : TypePM.TyVar} (ambient : varId ∈ fixedTys) :
    post.target varId = .var varId := by
  apply restricted.tySupport varId
  intro domain
  exact restricted.tyDomainFresh varId domain ambient

/-- Every chain prefix fixes the same ambient free capability variables. -/
theorem RestrictedPost.Chain.capFixed
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    {varId : CapVar} (ambient : varId ∈ fixedCaps) :
    post.cap varId = .var varId := by
  induction chain with
  | one atomic => exact atomic.capFixed ambient
  | comp earlier later induction =>
      simp only [Subst.seq, CapSubst.comp, induction,
        Cap.apply, later.capFixed ambient]

/-- Every chain prefix fixes the same ambient free ordinary variables. -/
theorem RestrictedPost.Chain.tyFixed
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    {varId : TypePM.TyVar} (ambient : varId ∈ fixedTys) :
    post.target varId = .var varId := by
  induction chain with
  | one atomic => exact atomic.tyFixed ambient
  | comp earlier later induction =>
      simp only [Subst.seq, induction, Subst.apply,
        Ty.applyCapability, Ty.applyTarget, later.tyFixed ambient]

/-- Every capability variable is still mapped to a capability variable. -/
theorem RestrictedPost.capImageVar
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar} {post : Subst}
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages post)
    (varId : CapVar) :
    ∃ image, post.cap varId = .var image :=
  restricted.capVariable varId

/-- A composed post chain also maps every capability variable to a variable. -/
theorem RestrictedPost.Chain.capImageVar
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    (varId : CapVar) :
    ∃ image, post.cap varId = .var image := by
  induction chain generalizing varId with
  | one restricted =>
      exact restricted.capImageVar varId
  | @comp capDomain tyDomain capImages later earlier
      earlierChain laterRestricted induction =>
      obtain ⟨middle, earlierImage⟩ := induction varId
      obtain ⟨image, laterImage⟩ := laterRestricted.capImageVar middle
      exact ⟨image, by
        simp only [Subst.seq, CapSubst.comp, Cap.apply, earlierImage]
        exact laterImage⟩

/-- Forget a strong atomic W post to its declarative meaning. -/
def RestrictedPost.toVariablePost
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {capDomain : List CapVar} {tyDomain : List TypePM.TyVar}
    {capImages : List CapVar} {post : Subst}
    (restricted : RestrictedPost fixedCaps fixedTys reservedCaps reservedTys
      capDomain tyDomain capImages post) : VariablePost post :=
  ⟨restricted.capVariable⟩

/-- Forget a strong W post chain to its declarative meaning. -/
def RestrictedPost.Chain.toVariablePost
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post) : VariablePost post :=
  ⟨chain.capImageVar⟩

/-- The total capability-variable mapping represented by a restricted chain. -/
noncomputable def RestrictedPost.Chain.capRen
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    (varId : CapVar) : CapVar :=
  Classical.choose (chain.capImageVar varId)

/-- The capability substitution is pointwise the chain's variable renaming. -/
theorem RestrictedPost.Chain.capEquation
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    (varId : CapVar) :
    post.cap varId = .var (chain.capRen varId) :=
  Classical.choose_spec (chain.capImageVar varId)

mutual

/-- Applying the chain's capability substitution is its pointwise mapping. -/
theorem RestrictedPost.Chain.applyCap_eq_applyRen
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    (capability : Cap) :
    capability.apply post.cap = capability.applyRen chain.capRen := by
  cases capability with
  | any => rfl
  | var varId => exact chain.capEquation varId
  | skolem name => rfl
  | con name children =>
      simp only [Cap.apply, Cap.applyRen]
      rw [chain.applyCapList_eq_applyRenList]
  | prod components =>
      simp only [Cap.apply, Cap.applyRen]
      rw [chain.applyCapList_eq_applyRenList]

/-- List form of `RestrictedPost.Chain.applyCap_eq_applyRen`. -/
theorem RestrictedPost.Chain.applyCapList_eq_applyRenList
    {fixedCaps : List CapVar} {fixedTys : List TypePM.TyVar}
    {reservedCaps : List CapVar} {reservedTys : List TypePM.TyVar}
    {post : Subst}
    (chain : RestrictedPost.Chain fixedCaps fixedTys reservedCaps reservedTys
      post)
    (capabilities : List Cap) :
    Cap.applyList post.cap capabilities =
      Cap.applyRenList chain.capRen capabilities := by
  cases capabilities with
  | nil => rfl
  | cons head tail =>
      simp only [Cap.applyList, Cap.applyRenList]
      rw [chain.applyCap_eq_applyRen, chain.applyCapList_eq_applyRenList]

end

mutual

/-- A successful exact merge remains successful under any variable renaming. -/
theorem Shape.merge_applyRen_of_success (r : CapVar → CapVar) :
    ∀ {left right merged},
      Shape.merge left right = some merged →
      Shape.merge (left.applyRen r) (right.applyRen r) =
        some (merged.applyRen r)
  | .unseen, right, merged, success => by
      simp only [Shape.merge, Option.some.injEq] at success
      subst merged
      rfl
  | left, .unseen, merged, success => by
      cases left <;>
        simp only [Shape.merge, Option.some.injEq] at success <;>
        subst merged <;> rfl
  | .known left, .known right, merged, success => by
      simp only [Shape.merge] at success
      split at success
      · rename_i equal
        subst right
        simp only [Option.some.injEq] at success
        subst merged
        simp [Shape.Evidence.applyRen, Shape.merge]
      · contradiction
  | .con leftName leftChildren, .con rightName rightChildren,
      merged, success => by
      simp only [Shape.merge] at success
      split at success
      · rename_i equal
        subst rightName
        cases childrenResult :
            Shape.mergeList leftChildren rightChildren with
        | none => simp [childrenResult] at success
        | some children =>
            simp only [childrenResult, Option.some.injEq] at success
            subst merged
            simp [Shape.Evidence.applyRen, Shape.merge,
              Shape.mergeList_applyRen_of_success r childrenResult]
      · contradiction
  | .prod leftComponents, .prod rightComponents, merged, success => by
      simp only [Shape.merge] at success
      cases componentsResult :
          Shape.mergeList leftComponents rightComponents with
      | none => simp [componentsResult] at success
      | some components =>
          simp only [componentsResult, Option.some.injEq] at success
          subst merged
          simp only [Shape.Evidence.applyRen, Shape.merge]
          rw [Shape.mergeList_applyRen_of_success r componentsResult]
  | .known _, .con _ _, _, success
  | .known _, .prod _, _, success
  | .con _ _, .known _, _, success
  | .con _ _, .prod _, _, success
  | .prod _, .known _, _, success
  | .prod _, .con _ _, _, success => by
      simp [Shape.merge] at success

/-- Pointwise form of successful-merge covariance. -/
theorem Shape.mergeList_applyRen_of_success (r : CapVar → CapVar) :
    ∀ {left right merged},
      Shape.mergeList left right = some merged →
      Shape.mergeList
          (Shape.Evidence.applyRenList r left)
          (Shape.Evidence.applyRenList r right) =
        some (Shape.Evidence.applyRenList r merged)
  | [], [], merged, success => by
      simp only [Shape.mergeList, Option.some.injEq] at success
      subst merged
      rfl
  | left :: leftRest, right :: rightRest, merged, success => by
      simp only [Shape.mergeList] at success
      cases headResult : Shape.merge left right with
      | none => simp [headResult] at success
      | some head =>
          cases tailResult : Shape.mergeList leftRest rightRest with
          | none => simp [headResult, tailResult] at success
          | some tail =>
              simp only [headResult, tailResult, Option.some.injEq] at success
              subst merged
              simp only [Shape.Evidence.applyRenList, Shape.mergeList,
                Shape.merge_applyRen_of_success r headResult,
                Shape.mergeList_applyRen_of_success r tailResult]
  | [], _ :: _, _, success
  | _ :: _, [], _, success => by
      simp [Shape.mergeList] at success

end

/-- A successful evidence fold remains successful under any variable renaming. -/
theorem Shape.mergeAll_applyRen_of_success
    (r : CapVar → CapVar) :
    ∀ {evidence merged},
      Shape.mergeAll evidence = some merged →
      Shape.mergeAll (Shape.Evidence.applyRenList r evidence) =
        some (merged.applyRen r)
  | [], merged, success => by
      simp only [Shape.mergeAll, Option.some.injEq] at success
      subst merged
      rfl
  | head :: tail, merged, success => by
      simp only [Shape.mergeAll] at success
      cases tailResult : Shape.mergeAll tail with
      | none => simp [tailResult] at success
      | some accumulated =>
          have renamedTail :=
            Shape.mergeAll_applyRen_of_success r tailResult
          have renamedHead :
              Shape.merge (head.applyRen r) (accumulated.applyRen r) =
                some (merged.applyRen r) :=
            Shape.merge_applyRen_of_success r (by
              simpa only [tailResult] using success)
          simpa only [Shape.Evidence.applyRenList, Shape.mergeAll,
            renamedTail] using renamedHead

/-- Successful shape inference is covariant under any variable renaming. -/
theorem Shape.inferShape_applyRen_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    {evidence : List Shape.Evidence} {capability : Cap}
    (success : Shape.inferShape observable evidence = some capability) :
    Shape.inferShape observable (Shape.Evidence.applyRenList r evidence) =
      some (capability.applyRen r) := by
  unfold Shape.inferShape at success ⊢
  cases mergedResult : Shape.mergeAll evidence with
  | none => simp [mergedResult] at success
  | some merged =>
      rw [mergedResult] at success
      have renamedMerged :=
        Shape.mergeAll_applyRen_of_success r mergedResult
      rw [renamedMerged]
      cases merged with
      | unseen =>
          simp only [Option.some.injEq] at success
          subst capability
          rfl
      | known leaf =>
          change Shape.finalize observable (.known leaf) =
            some capability at success
          change Shape.finalize observable
              ((.known leaf : Shape.Evidence).applyRen r) =
            some (capability.applyRen r)
          rw [Shape.finalize_applyRen, success]
          rfl
      | con name children =>
          change Shape.finalize observable (.con name children) =
            some capability at success
          change Shape.finalize observable
              ((.con name children : Shape.Evidence).applyRen r) =
            some (capability.applyRen r)
          rw [Shape.finalize_applyRen, success]
          rfl
      | prod components =>
          change Shape.finalize observable (.prod components) =
            some capability at success
          change Shape.finalize observable
              ((.prod components : Shape.Evidence).applyRen r) =
            some (capability.applyRen r)
          rw [Shape.finalize_applyRen, success]
          rfl

/-! ### Capability-renaming covariance of frozen projection -/

/-- Rename only the capability evidence stored in a projection assignment. -/
def Projection.renameAssignments
    (r : CapVar → CapVar) : Projection.Assignments → Projection.Assignments
  | [] => []
  | (varId, evidence) :: assignments =>
      (varId, evidence.applyRen r) :: renameAssignments r assignments

/-- Rename the evidence component of a paired constructor field. -/
def Projection.renameFields
    (r : CapVar → CapVar) :
    List Projection.FieldEvidence → List Projection.FieldEvidence
  | [] => []
  | (fieldType, evidence) :: fields =>
      (fieldType, evidence.applyRen r) :: renameFields r fields

/-- Rename every assignment chunk produced by constructor fields. -/
def Projection.renameChunks
    (r : CapVar → CapVar) :
    List Projection.Assignments → List Projection.Assignments
  | [] => []
  | assignments :: chunks =>
      Projection.renameAssignments r assignments ::
        Projection.renameChunks r chunks

/-- Assignment lookup commutes with evidence renaming. -/
theorem Projection.lookupAssignment_rename
    (r : CapVar → CapVar) (varId : TypePM.TyVar) :
    ∀ assignments,
      Projection.lookupAssignment varId
          (Projection.renameAssignments r assignments) =
        (Projection.lookupAssignment varId assignments).map
          (Shape.Evidence.applyRen r)
  | [] => rfl
  | (candidate, evidence) :: assignments => by
      simp only [Projection.renameAssignments, Projection.lookupAssignment]
      by_cases equal : varId = candidate
      · simp [equal]
      · simp [equal, Projection.lookupAssignment_rename r varId assignments]

/-- A successful assignment insertion remains successful after renaming. -/
theorem Projection.insertAssignment_rename_of_success
    (r : CapVar → CapVar) (varId : TypePM.TyVar)
    (evidence : Shape.Evidence) :
    ∀ {assignments updated},
      Projection.insertAssignment varId evidence assignments = some updated →
      Projection.insertAssignment varId (evidence.applyRen r)
          (Projection.renameAssignments r assignments) =
        some (Projection.renameAssignments r updated)
  | [], updated, success => by
      simp only [Projection.insertAssignment, Option.some.injEq] at success
      subst updated
      rfl
  | (candidate, previous) :: assignments, updated, success => by
      by_cases equal : varId = candidate
      · subst varId
        cases mergedResult : Shape.merge previous evidence with
        | none =>
            simp [Projection.insertAssignment, mergedResult] at success
        | some merged =>
            have updatedEq : updated = (candidate, merged) :: assignments := by
              simpa [Projection.insertAssignment, mergedResult] using
                success.symm
            subst updated
            have renamedMerge :=
              Shape.merge_applyRen_of_success r mergedResult
            simp [Projection.renameAssignments, Projection.insertAssignment,
              renamedMerge]
      ·
        cases tailResult :
            Projection.insertAssignment varId evidence assignments with
        | none =>
            simp [Projection.insertAssignment, equal, tailResult] at success
        | some tail =>
            have updatedEq : updated = (candidate, previous) :: tail := by
              simpa [Projection.insertAssignment, equal, tailResult] using
                success.symm
            subst updated
            have renamedTail :=
              Projection.insertAssignment_rename_of_success r varId evidence
                tailResult
            simp [Projection.renameAssignments, Projection.insertAssignment,
              equal, renamedTail]

/-- A successful assignment-environment merge remains successful after renaming. -/
theorem Projection.mergeAssignments_rename_of_success
    (r : CapVar → CapVar) :
    ∀ {left right merged},
      Projection.mergeAssignments left right = some merged →
      Projection.mergeAssignments
          (Projection.renameAssignments r left)
          (Projection.renameAssignments r right) =
        some (Projection.renameAssignments r merged)
  | left, [], merged, success => by
      simp only [Projection.mergeAssignments, Option.some.injEq] at success
      subst merged
      rfl
  | left, (varId, evidence) :: rest, merged, success => by
      cases insertedResult :
          Projection.insertAssignment varId evidence left with
      | none =>
          simp [Projection.mergeAssignments, insertedResult] at success
      | some inserted =>
          have tailSuccess :
              Projection.mergeAssignments inserted rest = some merged := by
            simpa [Projection.mergeAssignments, insertedResult] using success
          have renamedInserted :=
            Projection.insertAssignment_rename_of_success r varId evidence
              insertedResult
          have renamedTail :=
            Projection.mergeAssignments_rename_of_success r tailSuccess
          simpa [Projection.renameAssignments, Projection.mergeAssignments,
            renamedInserted] using renamedTail

/-- Pairing field types with renamed evidence renames exactly the paired fields. -/
theorem Projection.pairFields_rename
    (r : CapVar → CapVar) :
    ∀ fieldTypes childEvidence,
      Projection.pairFields fieldTypes
          (Shape.Evidence.applyRenList r childEvidence) =
        (Projection.pairFields fieldTypes childEvidence).map
          (Projection.renameFields r)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | fieldType :: fieldTypes, evidence :: childEvidence => by
      simp only [Shape.Evidence.applyRenList, Projection.pairFields]
      rw [Projection.pairFields_rename r fieldTypes childEvidence]
      cases paired : Projection.pairFields fieldTypes childEvidence <;>
        simp [Projection.renameFields]

mutual

/-- Successful field assignment collection is covariant under evidence renaming. -/
theorem Projection.collectAssignments_rename_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar) :
    ∀ {fieldType evidence assignments},
      Projection.collectAssignments observable resultVariables
          fieldType evidence = some assignments →
      Projection.collectAssignments observable resultVariables
          fieldType (evidence.applyRen r) =
        some (Projection.renameAssignments r assignments)
  | fieldType, .unseen, assignments, success => by
      simp only [Projection.collectAssignments, Option.some.injEq] at success
      subst assignments
      simp [Shape.Evidence.applyRen, Projection.renameAssignments]
  | fieldType, .known leaf, assignments, success => by
      cases fieldType with
      | var varId =>
          by_cases membership : varId ∈ resultVariables
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
      | data name arguments =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.data name arguments) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp [Projection.collectAssignments, variablesResult] at success
      | prod components =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.prod components) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp [Projection.collectAssignments, variablesResult] at success
      | skolem name
      | unit
      | int
      | bool
      | fn domain codomain
      | matcher capability target
      | slot capability target =>
          simp [Projection.collectAssignments, Projection.relevantVars] at success
          subst assignments
          simp [Projection.collectAssignments, Projection.relevantVars,
            Projection.renameAssignments, Shape.Evidence.applyRen]
  | fieldType, .con evidenceName children, assignments, success => by
      cases fieldType with
      | var varId =>
          by_cases membership : varId ∈ resultVariables
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
      | data typeName arguments =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.data typeName arguments) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp only [Projection.collectAssignments, variablesResult,
                    Shape.Evidence.applyRen] at success ⊢
                  by_cases namesEqual : typeName = evidenceName
                  · subst evidenceName
                    cases maskResult : observable typeName with
                    | none => simp [maskResult] at success
                    | some mask =>
                        simp only [maskResult] at success ⊢
                        exact Projection.collectAssignmentsMasked_rename_of_success
                          r observable resultVariables success
                  · simp [namesEqual] at success
      | prod components =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.prod components) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp [Projection.collectAssignments, variablesResult] at success
      | skolem name
      | unit
      | int
      | bool
      | fn domain codomain
      | matcher capability target
      | slot capability target =>
          simp [Projection.collectAssignments, Projection.relevantVars] at success
          subst assignments
          simp [Projection.collectAssignments, Projection.relevantVars,
            Projection.renameAssignments, Shape.Evidence.applyRen]
  | fieldType, .prod components, assignments, success => by
      cases fieldType with
      | var varId =>
          by_cases membership : varId ∈ resultVariables
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
          · simp [Projection.collectAssignments, Projection.relevantVars,
              membership] at success
            subst assignments
            simp [Projection.collectAssignments, Projection.relevantVars,
              membership, Projection.renameAssignments,
              Shape.Evidence.applyRen]
      | prod componentTypes =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.prod componentTypes) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp only [Projection.collectAssignments, variablesResult,
                    Shape.Evidence.applyRen] at success ⊢
                  exact Projection.collectAssignmentsList_rename_of_success
                    r observable resultVariables success
      | data name arguments =>
          cases variablesResult : Projection.relevantVars observable
              resultVariables (.data name arguments) with
          | none =>
              simp [Projection.collectAssignments, variablesResult] at success
          | some variables =>
              cases variables with
              | nil =>
                  simp [Projection.collectAssignments, variablesResult] at success
                  subst assignments
                  simp [Projection.collectAssignments, variablesResult,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | cons head tail =>
                  simp [Projection.collectAssignments, variablesResult] at success
      | skolem name
      | unit
      | int
      | bool
      | fn domain codomain
      | matcher capability target
      | slot capability target =>
          simp [Projection.collectAssignments, Projection.relevantVars] at success
          subst assignments
          simp [Projection.collectAssignments, Projection.relevantVars,
            Projection.renameAssignments, Shape.Evidence.applyRen]

/-- List form of successful assignment-collection covariance. -/
theorem Projection.collectAssignmentsList_rename_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar) :
    ∀ {fieldTypes evidence assignments},
      Projection.collectAssignmentsList observable resultVariables
          fieldTypes evidence = some assignments →
      Projection.collectAssignmentsList observable resultVariables
          fieldTypes (Shape.Evidence.applyRenList r evidence) =
        some (Projection.renameAssignments r assignments)
  | [], [], assignments, success => by
      simp only [Projection.collectAssignmentsList,
        Option.some.injEq] at success
      subst assignments
      rfl
  | fieldType :: fieldTypes, evidence :: restEvidence, assignments,
      success => by
      simp only [Projection.collectAssignmentsList] at success ⊢
      cases headResult :
          Projection.collectAssignments observable resultVariables
            fieldType evidence with
      | none => simp [headResult] at success
      | some head =>
          cases tailResult :
              Projection.collectAssignmentsList observable resultVariables
                fieldTypes restEvidence with
          | none => simp [headResult, tailResult] at success
          | some tail =>
              cases mergedResult : Projection.mergeAssignments head tail with
              | none => simp [headResult, tailResult, mergedResult] at success
              | some merged =>
                  have assignmentsEq : assignments = merged := by
                    simpa [headResult, tailResult, mergedResult] using
                      success.symm
                  subst assignments
                  have renamedHead :=
                    Projection.collectAssignments_rename_of_success
                      r observable resultVariables headResult
                  have renamedTail :=
                    Projection.collectAssignmentsList_rename_of_success
                      r observable resultVariables tailResult
                  have renamedMerged :=
                    Projection.mergeAssignments_rename_of_success r mergedResult
                  simpa only [Projection.collectAssignmentsList,
                    Shape.Evidence.applyRenList, renamedHead, renamedTail] using
                      renamedMerged
  | [], _ :: _, assignments, success
  | _ :: _, [], assignments, success => by
      simp [Projection.collectAssignmentsList] at success

/-- Masked form of successful assignment-collection covariance. -/
theorem Projection.collectAssignmentsMasked_rename_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar) :
    ∀ {mask fieldTypes evidence assignments},
      Projection.collectAssignmentsMasked observable resultVariables
          mask fieldTypes evidence = some assignments →
      Projection.collectAssignmentsMasked observable resultVariables
          mask fieldTypes (Shape.Evidence.applyRenList r evidence) =
        some (Projection.renameAssignments r assignments)
  | [], [], [], assignments, success => by
      simp only [Projection.collectAssignmentsMasked,
        Option.some.injEq] at success
      subst assignments
      rfl
  | isObservable :: mask, fieldType :: fieldTypes,
      evidence :: restEvidence, assignments, success => by
      cases isObservable with
      | false =>
          simp only [Projection.collectAssignmentsMasked, Bool.false_eq_true,
            if_false] at success ⊢
          cases tailResult :
              Projection.collectAssignmentsMasked observable resultVariables
                mask fieldTypes restEvidence with
          | none => simp [tailResult] at success
          | some tail =>
              cases mergedResult : Projection.mergeAssignments [] tail with
              | none => simp [tailResult, mergedResult] at success
              | some merged =>
                  have assignmentsEq : assignments = merged := by
                    simpa [tailResult, mergedResult] using success.symm
                  subst assignments
                  have renamedTail :=
                    Projection.collectAssignmentsMasked_rename_of_success
                      r observable resultVariables tailResult
                  have renamedMerged :=
                    Projection.mergeAssignments_rename_of_success r mergedResult
                  simpa only [Projection.collectAssignmentsMasked,
                    Shape.Evidence.applyRenList, Bool.false_eq_true, if_false,
                    renamedTail, Projection.renameAssignments] using
                      renamedMerged
      | true =>
          simp only [Projection.collectAssignmentsMasked, if_true] at success ⊢
          cases headResult :
              Projection.collectAssignments observable resultVariables
                fieldType evidence with
          | none => simp [headResult] at success
          | some head =>
              cases tailResult :
                  Projection.collectAssignmentsMasked observable resultVariables
                    mask fieldTypes restEvidence with
              | none => simp [headResult, tailResult] at success
              | some tail =>
                  cases mergedResult : Projection.mergeAssignments head tail with
                  | none =>
                      simp [headResult, tailResult, mergedResult] at success
                  | some merged =>
                      have assignmentsEq : assignments = merged := by
                        simpa [headResult, tailResult, mergedResult] using
                          success.symm
                      subst assignments
                      have renamedHead :=
                        Projection.collectAssignments_rename_of_success
                          r observable resultVariables headResult
                      have renamedTail :=
                        Projection.collectAssignmentsMasked_rename_of_success
                          r observable resultVariables tailResult
                      have renamedMerged :=
                        Projection.mergeAssignments_rename_of_success r
                          mergedResult
                      simpa only [Projection.collectAssignmentsMasked,
                        Shape.Evidence.applyRenList, if_true, renamedHead,
                        renamedTail] using renamedMerged
  | [], [], _ :: _, assignments, success
  | [], _ :: _, [], assignments, success
  | [], _ :: _, _ :: _, assignments, success
  | _ :: _, [], [], assignments, success
  | _ :: _, [], _ :: _, assignments, success
  | _ :: _, _ :: _, [], assignments, success => by
      simp [Projection.collectAssignmentsMasked] at success

end

/-- Per-field assignment chunks are renamed pointwise after evidence renaming. -/
theorem Projection.collectFieldAssignments_rename_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar) :
    ∀ {fields chunks},
      Projection.collectFieldAssignments observable resultVariables fields =
          some chunks →
      Projection.collectFieldAssignments observable resultVariables
          (Projection.renameFields r fields) =
        some (Projection.renameChunks r chunks)
  | [], chunks, success => by
      simp only [Projection.collectFieldAssignments,
        Option.some.injEq] at success
      subst chunks
      rfl
  | (fieldType, evidence) :: fields, chunks, success => by
      simp only [Projection.collectFieldAssignments] at success ⊢
      cases headResult :
          Projection.collectAssignments observable resultVariables
            fieldType evidence with
      | none => simp [headResult] at success
      | some head =>
          cases tailResult :
              Projection.collectFieldAssignments observable resultVariables
                fields with
          | none => simp [headResult, tailResult] at success
          | some tail =>
              have chunksEq : chunks = head :: tail := by
                simpa [headResult, tailResult] using success.symm
              subst chunks
              have renamedHead :=
                Projection.collectAssignments_rename_of_success
                  r observable resultVariables headResult
              have renamedTail :=
                Projection.collectFieldAssignments_rename_of_success
                  r observable resultVariables tailResult
              simp only [Projection.renameFields, Projection.renameChunks,
                Projection.collectFieldAssignments, renamedHead, renamedTail]

/-- Contributions for one target variable are renamed pointwise. -/
theorem Projection.evidenceContributions_rename
    (r : CapVar → CapVar) (varId : TypePM.TyVar) :
    ∀ chunks,
      Projection.evidenceContributions varId
          (Projection.renameChunks r chunks) =
        Shape.Evidence.applyRenList r
          (Projection.evidenceContributions varId chunks)
  | [] => rfl
  | assignments :: chunks => by
      have induction :=
        Projection.evidenceContributions_rename r varId chunks
      change
        List.filterMap (Projection.lookupAssignment varId)
            (Projection.renameChunks r chunks) =
          Shape.Evidence.applyRenList r
            (List.filterMap (Projection.lookupAssignment varId) chunks) at induction
      simp only [Projection.renameChunks, Projection.evidenceContributions,
        List.filterMap_cons, Projection.lookupAssignment_rename, induction]
      cases lookup : Projection.lookupAssignment varId assignments <;>
        simp [Shape.Evidence.applyRenList]

/-- Canonical assignment aggregation preserves every successful result. -/
theorem Projection.canonicalAssignments_rename_of_success
    (r : CapVar → CapVar) :
    ∀ {resultVariables chunks assignments},
      Projection.canonicalAssignments resultVariables chunks =
          some assignments →
      Projection.canonicalAssignments resultVariables
          (Projection.renameChunks r chunks) =
        some (Projection.renameAssignments r assignments)
  | [], chunks, assignments, success => by
      simp only [Projection.canonicalAssignments,
        Option.some.injEq] at success
      subst assignments
      simp [Projection.canonicalAssignments,
        Projection.renameAssignments]
  | varId :: resultVariables, chunks, assignments, success => by
      simp only [Projection.canonicalAssignments] at success ⊢
      cases evidenceResult :
          Shape.mergeAll (Projection.evidenceContributions varId chunks) with
      | none => simp [evidenceResult] at success
      | some evidence =>
          cases tailResult :
              Projection.canonicalAssignments resultVariables chunks with
          | none => simp [evidenceResult, tailResult] at success
          | some tail =>
              have renamedEvidence :=
                Shape.mergeAll_applyRen_of_success r evidenceResult
              have contributions :=
                Projection.evidenceContributions_rename r varId chunks
              have renamedTail :=
                Projection.canonicalAssignments_rename_of_success r tailResult
              cases evidence with
              | unseen =>
                  have assignmentsEq : assignments = tail := by
                    simpa [evidenceResult, tailResult] using success.symm
                  subst assignments
                  simp only [contributions, renamedEvidence, renamedTail,
                    Shape.Evidence.applyRen]
              | known leaf =>
                  have assignmentsEq :
                      assignments = (varId, .known leaf) :: tail := by
                    simpa [evidenceResult, tailResult] using success.symm
                  subst assignments
                  simp only [contributions, renamedEvidence, renamedTail,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | con name children =>
                  have assignmentsEq :
                      assignments = (varId, .con name children) :: tail := by
                    simpa [evidenceResult, tailResult] using success.symm
                  subst assignments
                  simp only [contributions, renamedEvidence, renamedTail,
                    Projection.renameAssignments, Shape.Evidence.applyRen]
              | prod components =>
                  have assignmentsEq :
                      assignments = (varId, .prod components) :: tail := by
                    simpa [evidenceResult, tailResult] using success.symm
                  subst assignments
                  simp only [contributions, renamedEvidence, renamedTail,
                    Projection.renameAssignments, Shape.Evidence.applyRen]

/-- Renaming assignment evidence does not change which variables are assigned. -/
theorem Projection.hasAssignment_rename
    (r : CapVar → CapVar) :
    ∀ variables assignments,
      Projection.hasAssignment variables
          (Projection.renameAssignments r assignments) =
        Projection.hasAssignment variables assignments
  | [], assignments => rfl
  | varId :: variables, assignments => by
      simp only [Projection.hasAssignment,
        Projection.lookupAssignment_rename]
      cases lookup : Projection.lookupAssignment varId assignments <;>
        simp [Projection.hasAssignment_rename r variables assignments]

mutual

/-- Result templates commute exactly with capability-evidence renaming. -/
theorem Projection.buildResultTemplate_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    ∀ target,
      Projection.buildResultTemplate observable resultVariables
          (Projection.renameAssignments r assignments) target =
        (Projection.buildResultTemplate observable resultVariables
          assignments target).map (Shape.Evidence.applyRen r)
  | .var varId => by
      by_cases membership : varId ∈ resultVariables
      · simp only [Projection.buildResultTemplate, membership, if_pos,
          Projection.lookupAssignment_rename]
        cases lookup : Projection.lookupAssignment varId assignments <;>
          simp [Shape.Evidence.applyRen]
      · simp [Projection.buildResultTemplate, membership,
          Shape.Evidence.applyRen, Shape.Leaf.applyRen]
  | .skolem name => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .unit => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .int => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .bool => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .fn domain codomain => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .matcher capability target => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .slot capability target => by
      simp [Projection.buildResultTemplate, Shape.Evidence.applyRen,
        Shape.Leaf.applyRen]
  | .prod componentTypes => by
      cases variablesResult : Projection.relevantVars observable
          resultVariables (.prod componentTypes) with
      | none =>
          simp [Projection.buildResultTemplate, variablesResult]
      | some variables =>
          cases variables with
          | nil =>
              simp [Projection.buildResultTemplate, variablesResult,
                Shape.Evidence.applyRen, Shape.Leaf.applyRen]
          | cons head tail =>
              simp only [Projection.buildResultTemplate, variablesResult,
                Projection.buildResultTemplateList_rename r observable
                  resultVariables assignments componentTypes]
              cases built : Projection.buildResultTemplateList observable
                  resultVariables assignments componentTypes <;>
                simp [Shape.Evidence.applyRen]
  | .data name arguments => by
      cases variablesResult : Projection.relevantVars observable
          resultVariables (.data name arguments) with
      | none =>
          simp [Projection.buildResultTemplate, variablesResult]
      | some variables =>
          cases variables with
          | nil =>
              simp [Projection.buildResultTemplate, variablesResult,
                Shape.Evidence.applyRen, Shape.Leaf.applyRen]
          | cons head tail =>
              cases maskResult : observable name with
              | none =>
                  simp [Projection.buildResultTemplate, variablesResult,
                    maskResult, Shape.Evidence.applyRen, Shape.Leaf.applyRen]
              | some mask =>
                  simp only [Projection.buildResultTemplate, variablesResult,
                    maskResult,
                    Projection.buildResultTemplateMasked_rename r observable
                      resultVariables assignments mask arguments]
                  cases built : Projection.buildResultTemplateMasked observable
                      resultVariables assignments mask arguments <;>
                    simp [Shape.Evidence.applyRen]

/-- List form of result-template covariance. -/
theorem Projection.buildResultTemplateList_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    ∀ targets,
      Projection.buildResultTemplateList observable resultVariables
          (Projection.renameAssignments r assignments) targets =
        (Projection.buildResultTemplateList observable resultVariables
          assignments targets).map (Shape.Evidence.applyRenList r)
  | [] => rfl
  | target :: targets => by
      simp only [Projection.buildResultTemplateList,
        Projection.buildResultTemplate_rename r observable resultVariables
          assignments target,
        Projection.buildResultTemplateList_rename r observable resultVariables
          assignments targets]
      cases headResult : Projection.buildResultTemplate observable
          resultVariables assignments target <;>
        cases tailResult : Projection.buildResultTemplateList observable
          resultVariables assignments targets <;>
        simp [Shape.Evidence.applyRenList]

/-- Masked form of result-template covariance. -/
theorem Projection.buildResultTemplateMasked_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    ∀ mask targets,
      Projection.buildResultTemplateMasked observable resultVariables
          (Projection.renameAssignments r assignments) mask targets =
        (Projection.buildResultTemplateMasked observable resultVariables
          assignments mask targets).map (Shape.Evidence.applyRenList r)
  | [], [] => rfl
  | isObservable :: mask, target :: targets => by
      cases isObservable with
      | false =>
          simp only [Projection.buildResultTemplateMasked,
            Bool.false_eq_true, if_false,
            Projection.buildResultTemplateMasked_rename r observable
              resultVariables assignments mask targets]
          cases tailResult : Projection.buildResultTemplateMasked observable
              resultVariables assignments mask targets <;>
            simp [Shape.Evidence.applyRen, Shape.Evidence.applyRenList,
              Shape.Leaf.applyRen]
      | true =>
          simp only [Projection.buildResultTemplateMasked, if_true,
            Projection.buildResultTemplate_rename r observable resultVariables
              assignments target,
            Projection.buildResultTemplateMasked_rename r observable
              resultVariables assignments mask targets]
          cases headResult : Projection.buildResultTemplate observable
              resultVariables assignments target <;>
            cases tailResult : Projection.buildResultTemplateMasked observable
              resultVariables assignments mask targets <;>
            simp [Shape.Evidence.applyRenList]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

end

/-- Building one result slot commutes with evidence renaming. -/
theorem Projection.buildResultSlot_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments)
    (slotType : Ty) :
    Projection.buildResultSlot observable resultVariables
        (Projection.renameAssignments r assignments) slotType =
      (Projection.buildResultSlot observable resultVariables
        assignments slotType).map (Shape.Evidence.applyRen r) := by
  unfold Projection.buildResultSlot
  cases variablesResult :
      Projection.relevantVars observable resultVariables slotType with
  | none => simp
  | some variables =>
      cases variables with
      | nil =>
          simp [Shape.Evidence.applyRen,
            Shape.Leaf.applyRen]
      | cons head tail =>
          simp only
          rw [Projection.hasAssignment_rename r (head :: tail) assignments]
          by_cases assigned :
              Projection.hasAssignment (head :: tail) assignments
          · simp [assigned,
              Projection.buildResultTemplate_rename r observable
                resultVariables assignments slotType]
          · simp [assigned, Shape.Evidence.applyRen]

mutual

/-- List form of result-slot covariance. -/
theorem Projection.buildResultSlots_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    ∀ slotTypes,
      Projection.buildResultSlots observable resultVariables
          (Projection.renameAssignments r assignments) slotTypes =
        (Projection.buildResultSlots observable resultVariables
          assignments slotTypes).map (Shape.Evidence.applyRenList r)
  | [] => rfl
  | slotType :: slotTypes => by
      simp only [Projection.buildResultSlots,
        Projection.buildResultSlot_rename r observable resultVariables
          assignments slotType,
        Projection.buildResultSlots_rename r observable resultVariables
          assignments slotTypes]
      cases headResult : Projection.buildResultSlot observable
          resultVariables assignments slotType <;>
        cases tailResult : Projection.buildResultSlots observable
          resultVariables assignments slotTypes <;>
        simp [Shape.Evidence.applyRenList]

/-- Masked form of result-slot covariance. -/
theorem Projection.buildResultSlotsMasked_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments) :
    ∀ mask slotTypes,
      Projection.buildResultSlotsMasked observable resultVariables
          (Projection.renameAssignments r assignments) mask slotTypes =
        (Projection.buildResultSlotsMasked observable resultVariables
          assignments mask slotTypes).map (Shape.Evidence.applyRenList r)
  | [], [] => rfl
  | isObservable :: mask, slotType :: slotTypes => by
      cases isObservable with
      | false =>
          simp only [Projection.buildResultSlotsMasked,
            Bool.false_eq_true, if_false,
            Projection.buildResultSlotsMasked_rename r observable
              resultVariables assignments mask slotTypes]
          cases tailResult : Projection.buildResultSlotsMasked observable
              resultVariables assignments mask slotTypes <;>
            simp [Shape.Evidence.applyRen,
              Shape.Evidence.applyRenList, Shape.Leaf.applyRen]
      | true =>
          simp only [Projection.buildResultSlotsMasked, if_true,
            Projection.buildResultSlot_rename r observable resultVariables
              assignments slotType,
            Projection.buildResultSlotsMasked_rename r observable
              resultVariables assignments mask slotTypes]
          cases headResult : Projection.buildResultSlot observable
              resultVariables assignments slotType <;>
            cases tailResult : Projection.buildResultSlotsMasked observable
              resultVariables assignments mask slotTypes <;>
            simp [Shape.Evidence.applyRenList]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

end

/-- Rebuilding the result root commutes exactly with evidence renaming. -/
theorem Projection.buildResultRoot_rename
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultVariables : List TypePM.TyVar)
    (assignments : Projection.Assignments)
    (resultType : Ty) :
    Projection.buildResultRoot observable resultVariables
        (Projection.renameAssignments r assignments) resultType =
      (Projection.buildResultRoot observable resultVariables
        assignments resultType).map (Shape.Evidence.applyRen r) := by
  cases resultType with
  | prod componentTypes =>
      simp only [Projection.buildResultRoot,
        Projection.buildResultSlots_rename r observable resultVariables
          assignments componentTypes]
      cases built : Projection.buildResultSlots observable resultVariables
          assignments componentTypes <;>
        simp [Shape.Evidence.applyRen]
  | data name arguments =>
      cases maskResult : observable name with
      | none => simp [Projection.buildResultRoot, maskResult]
      | some mask =>
          simp only [Projection.buildResultRoot, maskResult,
            Projection.buildResultSlotsMasked_rename r observable
              resultVariables assignments mask arguments]
          cases built : Projection.buildResultSlotsMasked observable
              resultVariables assignments mask arguments <;>
            simp [Shape.Evidence.applyRen]
  | var varId
  | skolem name
  | unit
  | int
  | bool
  | fn domain codomain
  | matcher capability target
  | slot capability target =>
      rfl

/-- Capability embedding commutes with pointwise variable renaming. -/
theorem Shape.map_ofCap_applyRen
    (r : CapVar → CapVar) :
    ∀ capabilities,
      (Cap.applyRenList r capabilities).map Shape.ofCap =
        Shape.Evidence.applyRenList r (capabilities.map Shape.ofCap)
  | [] => rfl
  | capability :: capabilities => by
      simp only [Cap.applyRenList, List.map_cons,
        Shape.Evidence.applyRenList, Shape.ofCap_applyRen,
        Shape.map_ofCap_applyRen r capabilities]

/-- Successful paired projection is covariant under evidence renaming. -/
theorem Projection.projectPaired_rename_of_success
    (r : CapVar → CapVar)
    (observable : Shape.Observability)
    (resultType : Ty) {fields : List Projection.FieldEvidence}
    {result : Shape.Evidence}
    (success : Projection.projectPaired observable resultType fields =
      some result) :
    Projection.projectPaired observable resultType
        (Projection.renameFields r fields) =
      some (result.applyRen r) := by
  cases variablesResult : Projection.relevantVars observable
      (Projection.targetVars resultType) resultType with
  | none =>
      simp [Projection.projectPaired, variablesResult] at success
  | some resultVariables =>
      cases chunksResult :
          Projection.collectFieldAssignments observable resultVariables fields with
      | none =>
          simp [Projection.projectPaired, variablesResult, chunksResult] at success
      | some chunks =>
          cases assignmentsResult :
              Projection.canonicalAssignments resultVariables chunks with
          | none =>
              simp [Projection.projectPaired, variablesResult, chunksResult,
                assignmentsResult] at success
          | some assignments =>
              have resultSuccess :
                  Projection.buildResultRoot observable resultVariables
                      assignments resultType = some result := by
                simpa [Projection.projectPaired, variablesResult, chunksResult,
                  assignmentsResult] using success
              have renamedChunks :=
                Projection.collectFieldAssignments_rename_of_success
                  r observable resultVariables chunksResult
              have renamedAssignments :=
                Projection.canonicalAssignments_rename_of_success r
                  assignmentsResult
              have renamedRoot :=
                Projection.buildResultRoot_rename r observable resultVariables
                  assignments resultType
              have renamedRootSuccess :
                  Projection.buildResultRoot observable resultVariables
                      (Projection.renameAssignments r assignments) resultType =
                    some (result.applyRen r) := by
                rw [renamedRoot, resultSuccess]
                rfl
              simpa [Projection.projectPaired, variablesResult, renamedChunks,
                renamedAssignments] using renamedRootSuccess

/-- The certified projection API preserves success under capability mapping. -/
theorem Projection.projectSignature_rename_of_success
    (r : CapVar → CapVar)
    {observable : Shape.Observability}
    (signature : Projection.ProjectionSignature observable)
    {childEvidence : List Shape.Evidence} {result : Shape.Evidence}
    (success : Projection.projectSignature signature childEvidence =
      some result) :
    Projection.projectSignature signature
        (Shape.Evidence.applyRenList r childEvidence) =
      some (result.applyRen r) := by
  cases fieldsResult :
      Projection.pairFields signature.fieldTypes childEvidence with
  | none =>
      simp [Projection.projectSignature, fieldsResult] at success
  | some fields =>
      have renamedFieldsResult :
          Projection.pairFields signature.fieldTypes
              (Shape.Evidence.applyRenList r childEvidence) =
            some (Projection.renameFields r fields) := by
        rw [Projection.pairFields_rename r signature.fieldTypes childEvidence,
          fieldsResult]
        rfl
      have pairedSuccess :
          Projection.projectPaired observable signature.resultType fields =
            some result := by
        simpa [Projection.projectSignature, fieldsResult] using success
      have renamedSuccess :=
        Projection.projectPaired_rename_of_success r observable
          signature.resultType pairedSuccess
      simpa [Projection.projectSignature, renamedFieldsResult] using
        renamedSuccess

/-- Actual-clause field-head validation and projection preserve renaming. -/
theorem Projection.projectClauseSignature_rename_of_success
    (r : CapVar → CapVar)
    {observable : Shape.Observability}
    (signature : Projection.ProjectionSignature observable)
    {childEvidence : List Shape.Evidence} {result : Shape.Evidence}
    (success : Projection.projectClauseSignature signature childEvidence =
      some result) :
    Projection.projectClauseSignature signature
        (Shape.Evidence.applyRenList r childEvidence) =
      some (result.applyRen r) := by
  cases validationResult :
      Projection.validateFieldHeads observable signature.fieldTypes
        childEvidence with
  | none =>
      simp [Projection.projectClauseSignature, validationResult] at success
  | some validationWitness =>
      cases validationWitness
      have renamedValidation :
          Projection.validateFieldHeads observable signature.fieldTypes
              (Shape.Evidence.applyRenList r childEvidence) =
            some () := by
        rw [Projection.validateFieldHeads_applyRen]
        exact validationResult
      have projectionSuccess :
          Projection.projectSignature signature childEvidence =
            some result := by
        simpa [Projection.projectClauseSignature, validationResult] using
          success
      have renamedProjection :=
        Projection.projectSignature_rename_of_success r signature
          projectionSuccess
      simp [Projection.projectClauseSignature, renamedValidation,
        renamedProjection]

/-- Constructor capability compatibility is preserved by pointwise renaming. -/
theorem PatternCtorScheme.CapCompatible.applyRen
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable}
    {children : List Cap} {outer : Cap}
    (r : CapVar → CapVar)
    (compatible : entry.CapCompatible children outer) :
    entry.CapCompatible (Cap.applyRenList r children) (outer.applyRen r) := by
  rcases compatible with ⟨projected, projectionSuccess, mergeSuccess⟩
  refine ⟨projected.applyRen r, ?_, ?_⟩
  · rw [Shape.map_ofCap_applyRen]
    exact Projection.projectSignature_rename_of_success r entry.projection
      projectionSuccess
  · rw [Shape.ofCap_applyRen]
    have renamedMerge := Shape.merge_applyRen_of_success r mergeSuccess
    simpa only [Shape.ofCap_applyRen] using renamedMerge

/-- Pointwise capability mapping preserves list arity. -/
theorem Cap.applyRenList_length
    (r : CapVar → CapVar) (capabilities : List Cap) :
    (Cap.applyRenList r capabilities).length = capabilities.length := by
  induction capabilities with
  | nil => rfl
  | cons capability capabilities induction =>
      simp [Cap.applyRenList, induction]

/-- Shallow matcher coverage is invariant under pointwise capability mapping. -/
theorem CoverageOK.applyRen
    {signature : FrozenMatcherSig} {clauses : List Clause}
    (r : CapVar → CapVar) {capability : Cap}
    (coverage : CoverageOK signature clauses capability) :
    CoverageOK signature clauses (capability.applyRen r) := by
  cases capability with
  | any => trivial
  | var varId => contradiction
  | skolem name => contradiction
  | con former children => exact coverage
  | prod components =>
      simpa [CoverageOK, Cap.applyRen,
        Cap.applyRenList_length] using coverage

/-- A fresh capability variable for a source pattern judgment. -/
def FreshCap
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (varId : CapVar) : Prop :=
  varId ∉ signature.fcv ∧
  varId ∉ context.fcv ∧
  varId ∉ parameters.fcv ∧
  varId ∉ bindings.fcv

/-- A fresh ordinary variable for a source pattern/expression judgment. -/
def FreshTy
    (signature : FrozenSig) (context : Context)
    (parameters : PatternCtx) (bindings : MonoCtx)
    (varId : TypePM.TyVar) : Prop :=
  varId ∉ signature.ftv ∧
  varId ∉ context.ftv ∧
  varId ∉ parameters.ftv ∧
  varId ∉ bindings.ftv

/-- Freshness required by PP-HOLE for its capability variable. -/
def FrozenSig.FreshCapFor
    (signature : FrozenSig) (varId : CapVar) (target : Ty) : Prop :=
  varId ∉ signature.fcv ∧ varId ∉ target.fcv

/-! ## Matcher-clause helpers -/

/--
`prodty_k`: the nullary tuple at zero, identity at one, product otherwise.

The source and runtime syntax represent Egison's `()` by `.tuple []`, whose
type is the nullary product `.prod []`.  The separate `.unit` type has no
runtime inhabitant in this core and therefore must not be used for zero-hole
decomposition results.
-/
def prodTy : List Ty → Ty
  | [] => .prod []
  | [target] => target
  | targets => .prod targets

/--
Syntactically decompose a next-matcher expression into exactly `arity` slots.
-/
def decomposeME (next : Expr) (arity : Nat) : Option (List Expr) :=
  match arity with
  | 0 =>
      match next with
      | .tuple [] => some []
      | _ => none
  | 1 => some [next]
  | _ + 2 =>
      match next with
      | .tuple expressions =>
          if expressions.length = arity then some expressions else none
      | _ => none

/-- Every actual clause passes the frozen data-arm exhaustiveness checker. -/
def ArmExhaustive
    (signature : FrozenSig) (clauses : List Clause) (target : Ty) : Prop :=
  ∀ clause ∈ clauses,
    signature.armExhaustive clause.armPatterns target = true

/-!
The core checker recognizes the two irrefutable primitive data patterns.  It
is conservative and executable: a positive answer identifies a real
catch-all arm, while an empty arm list is rejected.
-/

/-- Whether a primitive data pattern succeeds on every runtime value. -/
def DPat.isIrrefutable : DPat → Bool
  | .var _ => true
  | .wild => true
  | _ => false

/-- Conservative executable exhaustiveness checker used by core signatures. -/
def basicArmExhaustive (patterns : List DPat) (_target : Ty) : Bool :=
  patterns.any DPat.isIrrefutable

/-- The concrete core checker is insensitive to target specialization. -/
theorem ArmExhaustive.transport_basic
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {clauses : List Clause} {sourceTarget resultTarget : Ty}
    (exhaustive : ArmExhaustive signature clauses sourceTarget) :
    ArmExhaustive signature clauses resultTarget := by
  intro clause member
  have checked := exhaustive clause member
  rw [basic] at checked ⊢
  exact checked

/-! ## Primitive-pattern pattern typing -/

mutual

/-- `Σ̂ ⊢ pp : PPPattern τ ⇝ holes ; Δ`. -/
inductive PPatTy (signature : FrozenSig) :
    PPat → Ty → List Dual → MonoCtx → Prop where
  | hole {target varId} :
      signature.FreshCapFor varId target →
      PPatTy signature .hole target [⟨Cap.var varId, target⟩] []
  | wild {target} :
      PPatTy signature .wild target [] []
  | pval {name target} :
      PPatTy signature (.pval name) target [] [(name, target)]
  | ctor {name entry patterns targets result holes bindings} :
      signature.findPatternCtor name = some entry →
      PPatTys signature patterns targets holes bindings →
      entry.Inst targets result →
      PPatTy signature (.ctor name patterns) result holes bindings
  | tuple {patterns targets holes bindings} :
      PPatTys signature patterns targets holes bindings →
      PPatTy signature (.tuple patterns) (.prod targets) holes bindings

/-- List form of PP typing; holes and bindings retain source order. -/
inductive PPatTys (signature : FrozenSig) :
    List PPat → List Ty → List Dual → MonoCtx → Prop where
  | nil :
      PPatTys signature [] [] [] []
  | cons {pattern target holes bindings patterns targets restHoles restBindings} :
      PPatTy signature pattern target holes bindings →
      PPatTys signature patterns targets restHoles restBindings →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      PPatTys signature (pattern :: patterns) (target :: targets)
        (holes ++ restHoles) (bindings ++ restBindings)

end

/-! ## Structurally aligned primitive-pattern resolution -/

mutual

/--
A raw primitive-pattern derivation and its resolved certificates, aligned at
every constructor.  The indices are raw; actual indices are obtained by
applying `prevailing`.  In particular, the constructor child targets in the
raw and actual instances cannot be chosen independently.
-/
inductive PPatResolution
    (signature : FrozenSig) (prevailing : Subst) :
    PPat → Ty → List Dual → MonoCtx → Prop where
  /-- Identity resolution may retain the whole raw derivation directly. -/
  | identity {pattern target holes bindings} :
      prevailing = Subst.id →
      PPatTy signature pattern target holes bindings →
      PPatResolution signature prevailing pattern target holes bindings
  | hole {target varId} :
      signature.FreshCapFor varId target →
      PPatResolution signature prevailing .hole target
        [⟨Cap.var varId, target⟩] []
  | wild {target} :
      PPatResolution signature prevailing .wild target [] []
  | pval {name target} :
      PPatResolution signature prevailing (.pval name) target []
        [(name, target)]
  | ctor {name entry patterns targets result holes bindings} :
      signature.findPatternCtor name = some entry →
      PPatResolutions signature prevailing patterns targets holes bindings →
      entry.Inst targets result →
      entry.Inst (targets.map prevailing.apply) (prevailing.apply result) →
      PPatResolution signature prevailing (.ctor name patterns) result
        holes bindings
  | tuple {patterns targets holes bindings} :
      PPatResolutions signature prevailing patterns targets holes bindings →
      PPatResolution signature prevailing (.tuple patterns) (.prod targets)
        holes bindings

/-- List form of structurally aligned primitive-pattern resolution. -/
inductive PPatResolutions
    (signature : FrozenSig) (prevailing : Subst) :
    List PPat → List Ty → List Dual → MonoCtx → Prop where
  /-- Identity resolution may retain the whole raw list derivation. -/
  | identity {patterns targets holes bindings} :
      prevailing = Subst.id →
      PPatTys signature patterns targets holes bindings →
      PPatResolutions signature prevailing patterns targets holes bindings
  | nil :
      PPatResolutions signature prevailing [] [] [] []
  | cons
      {pattern target holes bindings patterns targets restHoles restBindings} :
      PPatResolution signature prevailing pattern target holes bindings →
      PPatResolutions signature prevailing patterns targets restHoles
        restBindings →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      PPatResolutions signature prevailing (pattern :: patterns)
        (target :: targets) (holes ++ restHoles) (bindings ++ restBindings)

end

mutual

/-- Recover the raw primitive-pattern derivation retained by an alignment. -/
def PPatResolution.raw
    {signature : FrozenSig} {prevailing : Subst} :
    {pattern : PPat} → {target : Ty} → {holes : List Dual} →
      {bindings : MonoCtx} →
      PPatResolution signature prevailing pattern target holes bindings →
      PPatTy signature pattern target holes bindings
  | _, _, _, _, .identity _ typing => typing
  | _, _, _, _, .hole fresh => .hole fresh
  | _, _, _, _, .wild => .wild
  | _, _, _, _, .pval => .pval
  | _, _, _, _, .ctor lookup children rawInstance _ =>
      .ctor lookup children.raw rawInstance
  | _, _, _, _, .tuple children => .tuple children.raw

/-- List form of `PPatResolution.raw`. -/
def PPatResolutions.raw
    {signature : FrozenSig} {prevailing : Subst} :
    {patterns : List PPat} → {targets : List Ty} →
      {holes : List Dual} → {bindings : MonoCtx} →
      PPatResolutions signature prevailing patterns targets holes bindings →
      PPatTys signature patterns targets holes bindings
  | _, _, _, _, .identity _ typing => typing
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail distinct =>
      .cons head.raw tail.raw distinct

end

/-! ## Terminal primitive-pattern resolution -/

/-- Capability substitution distributes pointwise through a capability list. -/
theorem Cap.applyList_eq_map (C : CapSubst) (capabilities : List Cap) :
    Cap.applyList C capabilities = capabilities.map (Cap.apply C) := by
  induction capabilities with
  | nil => rfl
  | cons capability capabilities induction =>
      simp only [Cap.applyList, List.map_cons, induction]

/-- Capability substitution distributes through a product capability. -/
@[simp] theorem Cap.apply_prod (C : CapSubst) (capabilities : List Cap) :
    (Cap.prod capabilities).apply C =
      .prod (capabilities.map (Cap.apply C)) := by
  change Cap.prod (Cap.applyList C capabilities) = _
  rw [Cap.applyList_eq_map]

/-- Paired substitution distributes pointwise through a target list. -/
theorem Subst.applyList_eq_map (S : Subst) (targets : List Ty) :
    Ty.applyTargetList S.target
        (Ty.applyCapabilityList S.cap targets) =
      targets.map S.apply := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      change S.apply target :: _ = S.apply target :: _
      rw [induction]

/-- Paired substitution distributes through a product target. -/
@[simp] theorem Subst.apply_prod (S : Subst) (targets : List Ty) :
    S.apply (.prod targets) = .prod (targets.map S.apply) := by
  change
    Ty.prod (Ty.applyTargetList S.target
      (Ty.applyCapabilityList S.cap targets)) = _
  rw [Subst.applyList_eq_map]

/-- Pointwise paired identity changes no target list. -/
@[simp] theorem Subst.applyList_id (targets : List Ty) :
    targets.map Subst.id.apply = targets := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [List.map_cons, Subst.apply_id, induction]

/-- Projection of paired substitution on a dual capability. -/
@[simp] theorem Dual.cap_applySubst (S : Subst) (dual : Dual) :
    (dual.applySubst S).cap = dual.cap.apply S.cap := by
  cases dual
  rfl

/-- Projection of paired substitution on a dual target. -/
@[simp] theorem Dual.target_applySubst (S : Subst) (dual : Dual) :
    (dual.applySubst S).target = S.apply dual.target := by
  cases dual
  rfl

/-- Capability projections commute with pointwise dual substitution. -/
@[simp] theorem Dual.map_cap_applySubst (S : Subst) (duals : List Dual) :
    (duals.map (Dual.applySubst S)).map Dual.cap =
      Cap.applyList S.cap (duals.map Dual.cap) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp only [List.map_cons, Dual.cap_applySubst, Cap.applyList, induction]

/-- Target projections commute with pointwise dual substitution. -/
@[simp] theorem Dual.map_target_applySubst (S : Subst) (duals : List Dual) :
    (duals.map (Dual.applySubst S)).map Dual.target =
      (duals.map Dual.target).map S.apply := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp only [List.map_cons, Dual.target_applySubst, induction]

mutual

/--
Primitive-pattern resolution indexed by the actual occurrence.  Fresh leaves
retain their raw origin and apply the prevailing post exactly once; compound
nodes retain only actual children and the final frozen-signature certificate.
-/
inductive TerminalPPatResolution
    (signature : FrozenSig) (prevailing : Subst) :
    PPat → Ty → List Dual → MonoCtx → Prop where
  | hole {rawTarget varId} :
      signature.FreshCapFor varId rawTarget →
      TerminalPPatResolution signature prevailing .hole
        (prevailing.apply rawTarget)
        ([⟨Cap.var varId, rawTarget⟩].map (Dual.applySubst prevailing)) []
  | wild {rawTarget} :
      TerminalPPatResolution signature prevailing .wild
        (prevailing.apply rawTarget) [] []
  | pval {name rawTarget} :
      TerminalPPatResolution signature prevailing (.pval name)
        (prevailing.apply rawTarget) []
        (MonoCtx.applySubst prevailing [(name, rawTarget)])
  | ctor {name entry patterns targets result holes bindings} :
      signature.findPatternCtor name = some entry →
      TerminalPPatResolutions signature prevailing patterns targets holes
        bindings →
      entry.Inst targets result →
      TerminalPPatResolution signature prevailing (.ctor name patterns)
        result holes bindings
  | tuple {patterns targets holes bindings} :
      TerminalPPatResolutions signature prevailing patterns targets holes
        bindings →
      TerminalPPatResolution signature prevailing (.tuple patterns)
        (.prod targets) holes bindings

/-- List form of actual-indexed terminal primitive-pattern resolution. -/
inductive TerminalPPatResolutions
    (signature : FrozenSig) (prevailing : Subst) :
    List PPat → List Ty → List Dual → MonoCtx → Prop where
  | nil :
      TerminalPPatResolutions signature prevailing [] [] [] []
  | cons
      {pattern target holes bindings patterns targets restHoles restBindings} :
      TerminalPPatResolution signature prevailing pattern target holes
        bindings →
      TerminalPPatResolutions signature prevailing patterns targets restHoles
        restBindings →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      TerminalPPatResolutions signature prevailing (pattern :: patterns)
        (target :: targets) (holes ++ restHoles) (bindings ++ restBindings)

end

mutual

/-- Raw primitive-pattern typing is already terminal at identity. -/
def PPatTy.terminal_id
    {signature : FrozenSig} :
    {pattern : PPat} → {target : Ty} → {holes : List Dual} →
      {bindings : MonoCtx} →
      PPatTy signature pattern target holes bindings →
      TerminalPPatResolution signature Subst.id pattern target holes bindings
  | _, _, _, _, .hole fresh => by
      simpa [Subst.apply_id] using
        (TerminalPPatResolution.hole
          (prevailing := Subst.id) fresh)
  | _, _, _, _, .wild => by
      simpa [Subst.apply_id] using
        (TerminalPPatResolution.wild (signature := signature)
          (prevailing := Subst.id) (rawTarget := _))
  | _, _, _, _, .pval => by
      simpa [Subst.apply_id] using
        (TerminalPPatResolution.pval (signature := signature)
          (prevailing := Subst.id) (rawTarget := _))
  | _, _, _, _, .ctor lookup children inst =>
      .ctor lookup children.terminal_id inst
  | _, _, _, _, .tuple children => .tuple children.terminal_id

/-- List form of `PPatTy.terminal_id`. -/
def PPatTys.terminal_id
    {signature : FrozenSig} :
    {patterns : List PPat} → {targets : List Ty} →
      {holes : List Dual} → {bindings : MonoCtx} →
      PPatTys signature patterns targets holes bindings →
      TerminalPPatResolutions signature Subst.id patterns targets holes bindings
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail distinct =>
      .cons head.terminal_id tail.terminal_id distinct

end

mutual

/-- Forget raw compound indices and expose the actual terminal resolution. -/
def PPatResolution.terminal
    {signature : FrozenSig} {prevailing : Subst} :
    {pattern : PPat} → {target : Ty} → {holes : List Dual} →
      {bindings : MonoCtx} →
      PPatResolution signature prevailing pattern target holes bindings →
      TerminalPPatResolution signature prevailing pattern
        (prevailing.apply target)
        (holes.map (Dual.applySubst prevailing))
        (bindings.applySubst prevailing)
  | _, _, _, _, .identity equality typing => by
      subst prevailing
      simpa [Subst.apply_id] using typing.terminal_id
  | _, _, _, _, .hole fresh => .hole fresh
  | _, _, _, _, .wild => .wild
  | _, _, _, _, .pval => .pval
  | _, _, _, _, .ctor lookup children _ actualInstance => by
      simpa using
        TerminalPPatResolution.ctor lookup children.terminal actualInstance
  | _, _, _, _, .tuple children => by
      simpa only [Subst.apply_prod] using
        TerminalPPatResolution.tuple children.terminal

/-- List form of `PPatResolution.terminal`. -/
def PPatResolutions.terminal
    {signature : FrozenSig} {prevailing : Subst} :
    {patterns : List PPat} → {targets : List Ty} →
      {holes : List Dual} → {bindings : MonoCtx} →
      PPatResolutions signature prevailing patterns targets holes bindings →
      TerminalPPatResolutions signature prevailing patterns
        (targets.map prevailing.apply)
        (holes.map (Dual.applySubst prevailing))
        (bindings.applySubst prevailing)
  | _, _, _, _, .identity equality typing => by
      subst prevailing
      simpa only [Subst.applyList_id, Dual.map_applySubst_id,
        MonoCtx.applySubst_id] using typing.terminal_id
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail distinct => by
      simpa only [List.map_cons, List.map_append, MonoCtx.applySubst] using
        TerminalPPatResolutions.cons head.terminal tail.terminal (by
          simpa [MonoCtx.names, MonoCtx.applySubst] using distinct)

end

/-! ## Primitive-pattern capability alignment -/

mutual

/--
Align the capabilities consumed by primitive-pattern holes with the
capability at the current pattern node.  A bare root hole is the catch-all
exception: it consumes one independently typed next matcher.  Every nested
hole consumes exactly its child capability.
-/
inductive PPatCapsAt (signature : FrozenSig) :
    Bool → PPat → List Cap → Cap → Prop where
  | rootHole {holeCapability outerCapability} :
      PPatCapsAt signature true .hole [holeCapability] outerCapability
  | childHole {capability} :
      PPatCapsAt signature false .hole [capability] capability
  | wild {atRoot outerCapability} :
      PPatCapsAt signature atRoot .wild [] outerCapability
  | pval {atRoot name outerCapability} :
      PPatCapsAt signature atRoot (.pval name) [] outerCapability
  | ctor
      {atRoot name entry patterns holeCapabilities childCapabilities
       outerCapability} :
      signature.findPatternCtor name = some entry →
      PPatCapsList signature patterns holeCapabilities childCapabilities →
      entry.CapCompatible childCapabilities outerCapability →
      PPatCapsAt signature atRoot (.ctor name patterns) holeCapabilities
        outerCapability
  | tuple {atRoot patterns holeCapabilities childCapabilities} :
      PPatCapsList signature patterns holeCapabilities childCapabilities →
      PPatCapsAt signature atRoot (.tuple patterns) holeCapabilities
        (.prod childCapabilities)

/-- Left-to-right list form of `PPatCapsAt`; hole capabilities are threaded. -/
inductive PPatCapsList (signature : FrozenSig) :
    List PPat → List Cap → List Cap → Prop where
  | nil :
      PPatCapsList signature [] [] []
  | cons
      {pattern patterns headHoles tailHoles headCapability tailCapabilities} :
      PPatCapsAt signature false pattern headHoles headCapability →
      PPatCapsList signature patterns tailHoles tailCapabilities →
      PPatCapsList signature (pattern :: patterns)
        (headHoles ++ tailHoles) (headCapability :: tailCapabilities)

end

/-!
`PPatTy` records the fresh variables introduced while checking primitive
patterns.  A clause does not consume those raw variables directly: one
shared prevailing substitution resolves the clause target, every hole dual,
and every primitive-pattern binding together.
-/

/-- A primitive-pattern derivation after applying one prevailing substitution. -/
inductive ResolvedPPatTy
    (signature : FrozenSig) (prevailing : Subst) :
    PPat → Ty → List Dual → MonoCtx → Prop where
  | ofAligned {pattern rawTarget rawHoles rawBindings} :
      PPatResolution signature prevailing pattern rawTarget rawHoles
        rawBindings →
      ResolvedPPatTy signature prevailing pattern
        (prevailing.apply rawTarget)
        (rawHoles.map (Dual.applySubst prevailing))
        (rawBindings.applySubst prevailing)
  | ofTerminal {pattern target holes bindings} :
      TerminalPPatResolution signature prevailing pattern target holes
        bindings →
      ResolvedPPatTy signature prevailing pattern target holes bindings

/-- Raw primitive-pattern typing resolves definitionally under identity. -/
theorem PPatTy.resolve_id
    {signature : FrozenSig} {pattern : PPat} {target : Ty}
    {holes : List Dual} {bindings : MonoCtx}
    (typing : PPatTy signature pattern target holes bindings) :
    ResolvedPPatTy signature Subst.id pattern target holes bindings := by
  simpa [Subst.apply_id] using
    ResolvedPPatTy.ofAligned (PPatResolution.identity rfl typing)

/-- Both raw-aligned and terminal introductions expose one terminal view. -/
theorem ResolvedPPatTy.terminal
    {signature : FrozenSig} {prevailing : Subst}
    {pattern : PPat} {target : Ty} {holes : List Dual}
    {bindings : MonoCtx}
    (typing : ResolvedPPatTy signature prevailing pattern target holes bindings) :
    TerminalPPatResolution signature prevailing pattern target holes bindings := by
  cases typing with
  | ofAligned resolution =>
      exact resolution.terminal
  | ofTerminal resolution => exact resolution

/-! ## Primitive data-pattern typing -/

mutual

/-- `Σ̂_D ⊢ dp : PDPattern τ ⇝ Δ`. -/
inductive DPatTy (signature : FrozenSig) : DPat → Ty → MonoCtx → Prop where
  | var {name target} :
      DPatTy signature (.var name) target [(name, target)]
  | wild {target} :
      DPatTy signature .wild target []
  | ctor {name scheme patterns targets result bindings} :
      signature.findDataCtor name = some scheme →
      DPatTys signature patterns targets bindings →
      scheme.Inst targets result →
      DPatTy signature (.ctor name patterns) result bindings
  | tuple {patterns targets bindings} :
      DPatTys signature patterns targets bindings →
      DPatTy signature (.tuple patterns) (.prod targets) bindings

/-- List form of primitive data-pattern typing. -/
inductive DPatTys (signature : FrozenSig) :
    List DPat → List Ty → MonoCtx → Prop where
  | nil :
      DPatTys signature [] [] []
  | cons {pattern target bindings patterns targets restBindings} :
      DPatTy signature pattern target bindings →
      DPatTys signature patterns targets restBindings →
      (∀ name, name ∈ bindings.names → name ∉ restBindings.names) →
      DPatTys signature (pattern :: patterns) (target :: targets)
        (bindings ++ restBindings)

end

/-! ## State-free runtime certificate

`RuntimeTyping` is the state-free certificate consumed by value typing and
preservation.  Its indices describe the type information needed by the
operational proof after inference state has been erased; it does not define
source acceptance.  The only source-typing judgment is `DDTyping` in
`TypePM.DemandTyping`.

The DD layer records capability-origin information separately and audits the
few suffix-sensitive facts at its published terminal substitution.  The
fixed-terminal mutual state-erasure theorem projects every DD family into the
semantic premises below.  Keeping this inductive family internal avoids
presenting it as a second source type system.
-/

mutual

/--
A runtime producer is compatible with an already-normalized consumer endpoint.
An explicit consumer `any` accepts every producer; all other heads decompose
structurally.

This semantic relation deliberately forgets raw matching syntax, solver
choices, and post-substitution provenance.  Those remain in executable
`MatcherToSlotRawCert` values until reconstruction erases them.  The `equal`
constructor expresses terminal endpoint equality and may overlap with `any` at
`CapabilityDemand .any .any`.
-/
inductive CapabilityDemand : Cap → Cap → Prop where
  | equal {capability} :
      CapabilityDemand capability capability
  | any {producer} :
      CapabilityDemand producer .any
  | con {name producers consumers} :
      CapabilityDemands producers consumers →
      CapabilityDemand (.con name producers) (.con name consumers)
  | prod {producers consumers} :
      CapabilityDemands producers consumers →
      CapabilityDemand (.prod producers) (.prod consumers)

/-- Pointwise runtime demand compatibility with exact order and arity. -/
inductive CapabilityDemands : List Cap → List Cap → Prop where
  | nil : CapabilityDemands [] []
  | cons {producer consumer producers consumers} :
      CapabilityDemand producer consumer →
      CapabilityDemands producers consumers →
      CapabilityDemands (producer :: producers) (consumer :: consumers)

end

mutual

/-- Applying one common capability substitution preserves terminal demand
compatibility. -/
theorem CapabilityDemand.apply (S : CapSubst) :
    ∀ {producer consumer : Cap},
      CapabilityDemand producer consumer →
        CapabilityDemand (producer.apply S) (consumer.apply S)
  | _, _, .equal => .equal
  | _, _, .any => .any
  | _, _, .con children => .con (CapabilityDemands.apply S children)
  | _, _, .prod children => .prod (CapabilityDemands.apply S children)

/-- Pointwise form of `CapabilityDemand.apply`. -/
theorem CapabilityDemands.apply (S : CapSubst) :
    ∀ {producers consumers : List Cap},
      CapabilityDemands producers consumers →
        CapabilityDemands (Cap.applyList S producers)
          (Cap.applyList S consumers)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (CapabilityDemand.apply S head) (CapabilityDemands.apply S tail)

end

/-- Erase raw one-way matching to terminal runtime demand evidence. -/
theorem CapabilityDemand.ofDemandMatches (S : CapSubst) :
    ∀ (producer consumer : Cap),
      DemandMatches S producer consumer →
      CapabilityDemand producer (consumer.apply S) := by
  intro producer consumer matching
  exact Cap.rec
    (motive_1 := fun consumer => ∀ producer,
      DemandMatches S producer consumer →
      CapabilityDemand producer (consumer.apply S))
    (motive_2 := fun consumers => ∀ producers,
      DemandMatchesList S producers consumers →
      CapabilityDemands producers (Cap.applyList S consumers))
    (by intro _ _; exact .any)
    (fun varId => by
      intro producer matching
      have equality : S varId = producer := by
        cases producer <;> simpa [DemandMatches] using matching
      rw [Cap.apply, equality]
      exact .equal)
    (fun consumerId => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producerId
      change producerId = consumerId at matching
      rw [matching]
      exact .equal)
    (fun consumerName consumers consumersIH => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producerName producers
      change producerName = consumerName ∧
        DemandMatchesList S producers consumers at matching
      rw [matching.1]
      exact .con (consumersIH producers matching.2))
    (fun consumers consumersIH => by
      intro producer matching
      cases producer <;> try contradiction
      rename_i producers
      change DemandMatchesList S producers consumers at matching
      exact .prod (consumersIH producers matching))
    (by
      intro producers matching
      cases producers with
      | nil => exact .nil
      | cons _ _ => contradiction)
    (fun _ _ consumerIH consumersIH => by
      intro producers matching
      cases producers with
      | nil => contradiction
      | cons producer producers =>
          simp only [DemandMatchesList] at matching
          exact .cons (consumerIH producer matching.1)
            (consumersIH producers matching.2))
    consumer producer matching

/-- A declarative one-way witness retains the normalized producer endpoint. -/
theorem CapabilityDemand.ofOneWayAt
    {S : CapSubst} {producer consumer : Cap}
    (matching : OneWayAt S producer consumer) :
    CapabilityDemand (producer.apply S) (consumer.apply S) := by
  rw [matching.2.1]
  exact CapabilityDemand.ofDemandMatches S producer consumer matching.2.2

/-- Raw, generation-time certificate for matcher-to-slot coercion. -/
structure MatcherToSlotRawCert
    (producerCap consumerCap : Cap)
    (producerTarget consumerTarget : Ty)
    (bindings : CapMatch.Bindings) (C : CapSubst) (T : TySubst) : Prop where
  matched : CapMatch.matchCap producerCap consumerCap = some bindings
  capSubstitution : C = bindings.toSubstWithin consumerCap.fcv
  targetUnified :
    Unification.mguTy
      (producerTarget.applyCapability C)
      (consumerTarget.applyCapability C) = some T
  rangeFixed : (Subst.mk C T).RangeFixed

/-- Raw, generation-time certificate for slot-to-slot checking. -/
structure SlotToSlotRawCert
    (sourceCap requestedCap : Cap)
    (sourceTarget requestedTarget : Ty)
    (C : CapSubst) (T : TySubst) : Prop where
  capabilityUnified : Unification.mguCap sourceCap requestedCap = some C
  targetUnified :
    Unification.mguTy
      (sourceTarget.applyCapability C)
      (requestedTarget.applyCapability C) = some T
  rangeFixed : (Subst.mk C T).RangeFixed

/-- Runtime demand exposed by an executable matcher-to-slot certificate. -/
theorem MatcherToSlotRawCert.capabilityDemand
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T) :
    CapabilityDemand (producerCap.apply C) (consumerCap.apply C) := by
  rw [raw.capSubstitution]
  exact CapabilityDemand.ofOneWayAt
    (CapMatch.matchCap_restricted_sound raw.matched)

/-- A common later capability substitution preserves the raw demand. -/
theorem MatcherToSlotRawCert.postCapabilityDemand
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T) (post : Subst) :
    CapabilityDemand ((producerCap.apply C).apply post.cap)
      ((consumerCap.apply C).apply post.cap) :=
  raw.capabilityDemand.apply post.cap

/-- The target endpoints of a raw matcher-to-slot solve normalize equally. -/
theorem MatcherToSlotRawCert.targetEquality
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T) :
    (Subst.mk C T).apply producerTarget =
      (Subst.mk C T).apply consumerTarget := by
  simpa only [Subst.apply] using Unification.mguTy_sound raw.targetUnified

/-- Any common later substitution preserves normalized target equality. -/
theorem MatcherToSlotRawCert.postTargetEquality
    {producerCap consumerCap : Cap}
    {producerTarget consumerTarget : Ty}
    {bindings : CapMatch.Bindings} {C : CapSubst} {T : TySubst}
    (raw : MatcherToSlotRawCert producerCap consumerCap producerTarget
      consumerTarget bindings C T) (post : Subst) :
    post.apply ((Subst.mk C T).apply producerTarget) =
      post.apply ((Subst.mk C T).apply consumerTarget) :=
  congrArg post.apply raw.targetEquality

/-- A raw slot-to-slot solve makes the fully normalized slot endpoints equal. -/
theorem SlotToSlotRawCert.slotEquality
    {sourceCap requestedCap : Cap}
    {sourceTarget requestedTarget : Ty}
    {C : CapSubst} {T : TySubst}
    (raw : SlotToSlotRawCert sourceCap requestedCap sourceTarget
      requestedTarget C T) :
    (Subst.mk C T).apply (.slot sourceCap sourceTarget) =
      (Subst.mk C T).apply (.slot requestedCap requestedTarget) := by
  have capability := Unification.mguCap_sound raw.capabilityUnified
  have target : (Subst.mk C T).apply sourceTarget =
      (Subst.mk C T).apply requestedTarget := by
    simpa only [Subst.apply] using Unification.mguTy_sound raw.targetUnified
  change Ty.slot (sourceCap.apply C)
      ((Subst.mk C T).apply sourceTarget) =
    Ty.slot (requestedCap.apply C)
      ((Subst.mk C T).apply requestedTarget)
  rw [capability, target]

/-- Any common later substitution preserves normalized slot equality. -/
theorem SlotToSlotRawCert.postSlotEquality
    {sourceCap requestedCap : Cap}
    {sourceTarget requestedTarget : Ty}
    {C : CapSubst} {T : TySubst}
    (raw : SlotToSlotRawCert sourceCap requestedCap sourceTarget
      requestedTarget C T) (post : Subst) :
    post.apply ((Subst.mk C T).apply (.slot sourceCap sourceTarget)) =
      post.apply ((Subst.mk C T).apply (.slot requestedCap requestedTarget)) :=
  congrArg post.apply raw.slotEquality

mutual

/-- State-free expression certificate `Σ̂ ; Γ ⊢ᵣ e : τ`. -/
inductive RuntimeTyping (signature : FrozenSig) : Context → Expr → Ty → Prop where
  /-- T-VAR. -/
  | var {context name scheme target} :
      context.find? name = some scheme →
      scheme.ValueFlowInst target →
      RuntimeTyping signature context (.var name) target
  /-- T-LAM. -/
  | lam {context name body domain codomain} :
      RuntimeTyping signature ((name, Scheme.mono domain) :: context) body codomain →
      RuntimeTyping signature context (.lam name body) (.fn domain codomain)
  /-- T-APP. -/
  | app {context function argument domain codomain} :
      RuntimeTyping signature context function (.fn domain codomain) →
      RuntimeTyping signature context argument domain →
      RuntimeTyping signature context (.app function argument) codomain
  /-- T-LET; its input type is already under the prevailing substitution. -/
  | letE {context name value body valueTy bodyTy} :
      RuntimeTyping signature context value valueTy →
      RuntimeTyping signature
        ((name, signature.generalize context valueTy) :: context) body bodyTy →
      RuntimeTyping signature context (.letE name value body) bodyTy
  /-- T-FIX, restricted to singleton direct-self monomorphic recursion. -/
  | fixE {context self argument body domain codomain} :
      self ≠ argument →
      DirectSelf.Holds self body →
      RuntimeTyping signature
        ((argument, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: context)
        body codomain →
      RuntimeTyping signature context (.fix self argument body) (.fn domain codomain)
  /-- T-LIT. -/
  | lit {context value} :
      RuntimeTyping signature context (.lit value) .int
  /-- T-TUPLE. -/
  | tuple {context expressions targets} :
      ExprsTy signature context expressions targets →
      RuntimeTyping signature context (.tuple expressions) (.prod targets)
  /-- T-CON. -/
  | ctor {context name expressions targets result scheme} :
      signature.findDataCtor name = some scheme →
      scheme.Inst targets result →
      ExprsTy signature context expressions targets →
      RuntimeTyping signature context (.ctor name expressions) result
  /-- T-PRIM. -/
  | prim {context op expressions targets result scheme} :
      signature.findPrimitive op = some scheme →
      scheme.Inst targets result →
      ExprsTy signature context expressions targets →
      RuntimeTyping signature context (.prim op expressions) result
  /--
  Declarative T-SOME: `something` inhabits `Matcher Any τ` for every target.

  The inference implementation generates a fresh target meta-variable;
  separating that algorithmic choice from this declarative rule makes
  substitution closure explicit (`somethingScheme = ∀α. Matcher Any α`).
  -/
  | something {context target} :
      RuntimeTyping signature context .something (.matcher .any target)
  /-- T-MATCHALL. -/
  | matchAll
      {prevailing context target matcher pattern body targetTy patternCap
       bindings result} :
      RuntimeTyping signature context target targetTy →
      ResolvedPatternTy signature prevailing context [] [] pattern
        patternCap targetTy bindings →
      RuntimeTyping signature context matcher (.slot patternCap targetTy) →
      RuntimeTyping signature (bindings.toContext ++ context) body result →
      RuntimeTyping signature context (.matchAll target matcher pattern body)
        (Ty.listT result)
  /-- T-MATCHER, tied to the evidence of these exact source clauses. -/
  | matcher
      {context clauses target capability evidence} :
      ResolvedClausesTy signature context clauses capability target evidence →
      Shape.inferShape signature.observability evidence = some capability →
      CatchAllLast clauses →
      ArmExhaustive signature clauses target →
      PPBindNodup clauses →
      ArmBindNodup clauses →
      CoverageOK signature.toMatcherSig clauses capability →
      RuntimeTyping signature context (.matcher clauses)
        (.matcher capability target)
  /--
  COERCE-MATCHER-TO-SLOT at the state-erased runtime boundary.  Both endpoints
  are already terminal: the targets coincide, and `CapabilityDemand` retains
  exactly the producer/consumer compatibility used by dynamic safety.
  Executable matching and unification evidence belongs to reconstruction, not
  to this runtime certificate.
  -/
  | coerceMatcherToSlot
      {context expression producerCap consumerCap target} :
      RuntimeTyping signature context expression
        (.matcher producerCap target) →
      CapabilityDemand producerCap consumerCap →
      RuntimeTyping signature context expression
        (.slot consumerCap target)
  /--
  COERCE-PRODUCT-MATCHER.

  This is a genuine unary product lift rather than a tuple-literal-only rule.
  The general form lets elaboration delay the view choice across `let` and
  insert the explicit coercion at the eventual matcher use site.
  -/
  | coerceProductMatcher {context expression} {duals : List Dual} :
      RuntimeTyping signature context expression
        (.prod (duals.map fun dual => .matcher dual.cap dual.target)) →
      RuntimeTyping signature context expression
        (.matcher (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))
  /-- COERCE-SLOT-TUPLE. -/
  | coerceSlotTuple {context expression} {duals : List Dual} :
      RuntimeTyping signature context expression
        (.prod (duals.map fun dual => .slot dual.cap dual.target)) →
      RuntimeTyping signature context expression
        (.slot (.prod (duals.map Dual.cap))
          (.prod (duals.map Dual.target)))

/-- Pointwise expression typing with exact source order and arity. -/
inductive ExprsTy (signature : FrozenSig) :
    Context → List Expr → List Ty → Prop where
  | nil {context} :
      ExprsTy signature context [] []
  | cons {context expression target expressions targets} :
      RuntimeTyping signature context expression target →
      ExprsTy signature context expressions targets →
      ExprsTy signature context (expression :: expressions) (target :: targets)

/-- Pattern dual typing `Σ̂;Γ;Φ;Δ ⊢ p : Pattern κ τ ; Δ'`. -/
inductive PatternTy (signature : FrozenSig) :
    Context → PatternCtx → MonoCtx → Pattern → Cap → Ty → MonoCtx → Prop where
  /-- PAT-VAR. -/
  | pvar {context parameters bindings name capVar tyVar} :
      name ∉ bindings.names →
      FreshCap signature context parameters bindings capVar →
      FreshTy signature context parameters bindings tyVar →
      PatternTy signature context parameters bindings (.pvar name)
        (.var capVar) (.var tyVar) (bindings ++ [(name, .var tyVar)])
  /-- PAT-WILD. -/
  | wild {context parameters bindings capVar tyVar} :
      FreshCap signature context parameters bindings capVar →
      FreshTy signature context parameters bindings tyVar →
      PatternTy signature context parameters bindings .wild
        (.var capVar) (.var tyVar) bindings
  /-- PAT-VALUE. -/
  | pval {context parameters bindings expression target capVar} :
      RuntimeTyping signature (bindings.toContext ++ context) expression target →
      FreshCap signature context parameters bindings capVar →
      capVar ∉ target.fcv →
      PatternTy signature context parameters bindings (.pval expression)
        (.var capVar) target bindings
  /-- PAT-EMBED. -/
  | embed {context parameters bindings name dual} :
      parameters.find? name = some dual →
      PatternTy signature context parameters bindings (.embed name)
        dual.cap dual.target bindings
  /-- PAT-TUPLE. -/
  | tuple {context parameters bindings patterns duals resultBindings} :
      PatternTys signature context parameters bindings
        patterns duals resultBindings →
      PatternTy signature context parameters bindings (.ptuple patterns)
        (.prod (duals.map Dual.cap)) (.prod (duals.map Dual.target))
        resultBindings
  /-- PAT-CON: capability projection and target instantiation share one entry. -/
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry →
      PatternTys signature context parameters bindings
        patterns duals resultBindings →
      entry.CapCompatible (duals.map Dual.cap) result.cap →
      entry.Inst (duals.map Dual.target) result.target →
      PatternTy signature context parameters bindings (.pctor name patterns)
        result.cap result.target resultBindings
  /-- PAT-AND. -/
  | and {context parameters bindings left right cap target middle result} :
      PatternTy signature context parameters bindings left cap target middle →
      PatternTy signature context parameters middle right cap target result →
      PatternTy signature context parameters bindings (.pand left right)
        cap target result
  /-- PAT-OR. -/
  | or {context parameters bindings left right cap target result} :
      PatternTy signature context parameters bindings left cap target result →
      PatternTy signature context parameters bindings right cap target result →
      PatternTy signature context parameters bindings (.por left right)
        cap target result
  /-- PAT-APP. -/
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme →
      PatternTys signature context parameters bindings
        patterns duals resultBindings →
      scheme.ValueFlowInst duals result →
      PatternTy signature context parameters bindings (.papp name patterns)
        result.cap result.target resultBindings

/-- Pattern-list typing with left-to-right `Δ` threading. -/
inductive PatternTys (signature : FrozenSig) :
    Context → PatternCtx → MonoCtx → List Pattern → List Dual → MonoCtx → Prop where
  | nil {context parameters bindings} :
      PatternTys signature context parameters bindings [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle
       patterns duals result} :
      PatternTy signature context parameters bindings pattern cap target middle →
      PatternTys signature context parameters middle patterns duals result →
      PatternTys signature context parameters bindings
        (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/--
Structurally aligned resolution of one user pattern.  All indices are raw;
the actual occurrence is obtained by applying `prevailing`.  Constructor and
pattern-function certificates are retained at both raw and actual child
indices, preventing an unrelated actual derivation from being paired with the
raw provenance tree.
-/
inductive PatternResolution (signature : FrozenSig) :
    Subst → Context → PatternCtx → MonoCtx → Pattern →
      Cap → Ty → MonoCtx → Prop where
  /-- Identity resolution may retain the whole raw derivation directly. -/
  | identity
      {context parameters bindings pattern capability target resultBindings} :
      prevailing = Subst.id →
      PatternTy signature context parameters bindings pattern capability target
        resultBindings →
      PatternResolution signature prevailing context parameters bindings
        pattern capability target resultBindings
  | pvar {context parameters bindings name capVar tyVar} :
      name ∉ bindings.names →
      FreshCap signature context parameters bindings capVar →
      FreshTy signature context parameters bindings tyVar →
      PatternResolution signature prevailing context parameters bindings
        (.pvar name) (.var capVar) (.var tyVar)
        (bindings ++ [(name, .var tyVar)])
  | wild {context parameters bindings capVar tyVar} :
      FreshCap signature context parameters bindings capVar →
      FreshTy signature context parameters bindings tyVar →
      PatternResolution signature prevailing context parameters bindings
        .wild (.var capVar) (.var tyVar) bindings
  | pval {context parameters bindings expression target capVar} :
      RuntimeTyping signature (bindings.toContext ++ context) expression target →
      FreshCap signature context parameters bindings capVar →
      capVar ∉ target.fcv →
      RuntimeTyping signature
        ((bindings.applySubst prevailing).toContext ++
          context.applySubst prevailing)
        expression (prevailing.apply target) →
      PatternResolution signature prevailing context parameters bindings
        (.pval expression) (.var capVar) target bindings
  | embed {context parameters bindings name dual} :
      parameters.find? name = some dual →
      (parameters.applySubst prevailing).find? name =
        some (dual.applySubst prevailing) →
      PatternResolution signature prevailing context parameters bindings
        (.embed name) dual.cap dual.target bindings
  | tuple {context parameters bindings patterns duals resultBindings} :
      PatternResolutions signature prevailing context parameters bindings
        patterns duals resultBindings →
      PatternResolution signature prevailing context parameters bindings
        (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry →
      PatternResolutions signature prevailing context parameters bindings
        patterns duals resultBindings →
      entry.CapCompatible (duals.map Dual.cap) result.cap →
      entry.Inst (duals.map Dual.target) result.target →
      entry.CapCompatible
        ((duals.map (Dual.applySubst prevailing)).map Dual.cap)
        (result.applySubst prevailing).cap →
      entry.Inst
        ((duals.map (Dual.applySubst prevailing)).map Dual.target)
        (result.applySubst prevailing).target →
      PatternResolution signature prevailing context parameters bindings
        (.pctor name patterns) result.cap result.target resultBindings
  | and
      {context parameters bindings left right cap target middle result} :
      PatternResolution signature prevailing context parameters bindings
        left cap target middle →
      PatternResolution signature prevailing context parameters middle
        right cap target result →
      PatternResolution signature prevailing context parameters bindings
        (.pand left right) cap target result
  | or {context parameters bindings left right cap target result} :
      PatternResolution signature prevailing context parameters bindings
        left cap target result →
      PatternResolution signature prevailing context parameters bindings
        right cap target result →
      PatternResolution signature prevailing context parameters bindings
        (.por left right) cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme →
      PatternResolutions signature prevailing context parameters bindings
        patterns duals resultBindings →
      scheme.ValueFlowInst duals result →
      scheme.ValueFlowInst (duals.map (Dual.applySubst prevailing))
        (result.applySubst prevailing) →
      PatternResolution signature prevailing context parameters bindings
        (.papp name patterns) result.cap result.target resultBindings

/-- List form of structurally aligned user-pattern resolution. -/
inductive PatternResolutions (signature : FrozenSig) :
    Subst → Context → PatternCtx → MonoCtx → List Pattern →
      List Dual → MonoCtx → Prop where
  /-- Identity resolution may retain the whole raw list derivation. -/
  | identity {context parameters bindings patterns duals resultBindings} :
      prevailing = Subst.id →
      PatternTys signature context parameters bindings patterns duals
        resultBindings →
      PatternResolutions signature prevailing context parameters bindings
        patterns duals resultBindings
  | nil {context parameters bindings} :
      PatternResolutions signature prevailing context parameters bindings
        [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle
       patterns duals result} :
      PatternResolution signature prevailing context parameters bindings
        pattern cap target middle →
      PatternResolutions signature prevailing context parameters middle
        patterns duals result →
      PatternResolutions signature prevailing context parameters bindings
        (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/- Terminal user-pattern resolution. -/

/--
User-pattern resolution indexed entirely by the actual occurrence.  Leaf
constructors retain the raw freshness/provenance needed to justify allocation;
compound constructors retain actual children and their final certificates.
-/
inductive TerminalPatternResolution
    (signature : FrozenSig) :
    Subst → Context → PatternCtx → MonoCtx → Pattern →
      Cap → Ty → MonoCtx → Prop where
  | pvar {rawContext rawParameters rawBindings name capVar tyVar}
      {actualContext : Context} :
      name ∉ rawBindings.names →
      FreshCap signature rawContext rawParameters rawBindings capVar →
      FreshTy signature rawContext rawParameters rawBindings tyVar →
      TerminalPatternResolution signature prevailing
        actualContext
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.pvar name)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        ((rawBindings ++ [(name, Ty.var tyVar)]).applySubst prevailing)
  | wild {rawContext rawParameters rawBindings capVar tyVar}
      {actualContext : Context} :
      FreshCap signature rawContext rawParameters rawBindings capVar →
      FreshTy signature rawContext rawParameters rawBindings tyVar →
      TerminalPatternResolution signature prevailing
        actualContext
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) .wild
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply (Ty.var tyVar))
        (rawBindings.applySubst prevailing)
  | pval
      {rawContext rawParameters rawBindings expression rawTarget capVar}
      {actualContext : Context} :
      FreshCap signature rawContext rawParameters rawBindings capVar →
      capVar ∉ rawTarget.fcv →
      RuntimeTyping signature
        ((rawBindings.applySubst prevailing).toContext ++
          actualContext)
        expression (prevailing.apply rawTarget) →
      TerminalPatternResolution signature prevailing
        actualContext
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.pval expression)
        ((Cap.var capVar).apply prevailing.cap)
        (prevailing.apply rawTarget)
        (rawBindings.applySubst prevailing)
  | embed
      {rawContext : Context} {rawParameters : PatternCtx}
      {rawBindings : MonoCtx} {name : String} {dual : Dual}
      {actualContext : Context} :
      rawParameters.find? name = some dual →
      (rawParameters.applySubst prevailing).find? name =
        some (dual.applySubst prevailing) →
      TerminalPatternResolution signature prevailing
        actualContext
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing) (.embed name)
        (dual.cap.apply prevailing.cap)
        (prevailing.apply dual.target)
        (rawBindings.applySubst prevailing)
  | tuple {context parameters bindings patterns duals resultBindings} :
      TerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings →
      TerminalPatternResolution signature prevailing context parameters
        bindings (.ptuple patterns) (.prod (duals.map Dual.cap))
        (.prod (duals.map Dual.target)) resultBindings
  | ctor
      {context parameters bindings name entry patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternCtor name = some entry →
      TerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings →
      entry.CapCompatible (duals.map Dual.cap) result.cap →
      entry.Inst (duals.map Dual.target) result.target →
      TerminalPatternResolution signature prevailing context parameters
        bindings (.pctor name patterns) result.cap result.target resultBindings
  | and
      {context parameters bindings left right cap target middle result} :
      TerminalPatternResolution signature prevailing context parameters
        bindings left cap target middle →
      TerminalPatternResolution signature prevailing context parameters
        middle right cap target result →
      TerminalPatternResolution signature prevailing context parameters
        bindings (.pand left right) cap target result
  | or {context parameters bindings left right cap target result} :
      TerminalPatternResolution signature prevailing context parameters
        bindings left cap target result →
      TerminalPatternResolution signature prevailing context parameters
        bindings right cap target result →
      TerminalPatternResolution signature prevailing context parameters
        bindings (.por left right) cap target result
  | app
      {context parameters bindings name scheme patterns duals resultBindings}
      {result : Dual} :
      signature.findPatternFun name = some scheme →
      TerminalPatternResolutions signature prevailing context parameters
        bindings patterns duals resultBindings →
      scheme.ValueFlowInst duals result →
      TerminalPatternResolution signature prevailing context parameters
        bindings (.papp name patterns) result.cap result.target resultBindings

/-- List form of actual-indexed terminal user-pattern resolution. -/
inductive TerminalPatternResolutions
    (signature : FrozenSig) :
    Subst → Context → PatternCtx → MonoCtx → List Pattern →
      List Dual → MonoCtx → Prop where
  | nil {context parameters bindings} :
      TerminalPatternResolutions signature prevailing context parameters
        bindings [] [] bindings
  | cons
      {context parameters bindings pattern cap target middle
       patterns duals result} :
      TerminalPatternResolution signature prevailing context parameters
        bindings pattern cap target middle →
      TerminalPatternResolutions signature prevailing context parameters
        middle patterns duals result →
      TerminalPatternResolutions signature prevailing context parameters
        bindings (pattern :: patterns) (⟨cap, target⟩ :: duals) result

/--
One raw pattern derivation resolved occurrence-wide by the prevailing
substitution used by T-MATCHALL.  In particular the context, target, matcher
capability, and output bindings cannot be resolved independently.
-/
inductive ResolvedPatternTy (signature : FrozenSig) :
    Subst → Context → PatternCtx → MonoCtx → Pattern → Cap → Ty → MonoCtx → Prop where
  | ofAligned
      {rawContext rawParameters rawBindings pattern rawCap rawTarget
       rawResultBindings} :
      PatternResolution signature prevailing rawContext rawParameters
        rawBindings pattern rawCap rawTarget rawResultBindings →
      ResolvedPatternTy signature prevailing
        (rawContext.applySubst prevailing)
        (rawParameters.applySubst prevailing)
        (rawBindings.applySubst prevailing)
        pattern
        (rawCap.apply prevailing.cap)
        (prevailing.apply rawTarget)
        (rawResultBindings.applySubst prevailing)
  | ofTerminal
      {context parameters bindings pattern capability target resultBindings} :
      TerminalPatternResolution signature prevailing context parameters
        bindings pattern capability target resultBindings →
      ResolvedPatternTy signature prevailing context parameters bindings
        pattern capability target resultBindings

/-- One matcher-clause arm. -/
inductive ArmTy (signature : FrozenSig) :
    Context → Ty → MonoCtx → Ty → Arm → Prop where
  | mk {context target ppBindings result pattern body armBindings} :
      DPatTy signature pattern target armBindings →
      RuntimeTyping signature
        (armBindings.toContext ++ ppBindings.toContext ++ context)
        body result →
      ArmTy signature context target ppBindings result (.mk pattern body)

/-- Pointwise arm typing. -/
inductive ArmsTy (signature : FrozenSig) :
    Context → Ty → MonoCtx → Ty → List Arm → Prop where
  | nil {context target ppBindings result} :
      ArmsTy signature context target ppBindings result []
  | cons {context target ppBindings result arm arms} :
      ArmTy signature context target ppBindings result arm →
      ArmsTy signature context target ppBindings result arms →
      ArmsTy signature context target ppBindings result (arm :: arms)

/-- CLAUSE-TY, indexed by its shared substitution and concrete evidence.
The order premise is intentionally explicit even though the final
`clauseEvidence` equality implies it: this belt-and-braces presentation keeps
the declarative boundary visible and matches the displayed paper rule. -/
inductive ClauseTy (signature : FrozenSig) :
    Subst → Context → Clause → Cap → Ty → Shape.Evidence → Prop where
  | mk
      {context capability target pp next arms holes ppBindings nextMatchers
       evidence} :
      PPatCoreOrder pp →
      ResolvedPPatTy signature prevailing pp target holes ppBindings →
      PPatCapsAt signature true pp (holes.map Dual.cap) capability →
      decomposeME next holes.length = some nextMatchers →
      ExprsTy signature context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) →
      ArmsTy signature context target ppBindings
        (Ty.listT (prodTy (holes.map Dual.target))) arms →
      clauseEvidence signature.toMatcherSig pp (holes.map Dual.cap) =
        some evidence →
      ClauseTy signature prevailing context (.mk pp next arms) capability
        target evidence

/-- Actual clause-list typing under one substitution shared by every clause. -/
inductive ClausesTy (signature : FrozenSig) :
    Subst → Context → List Clause → Cap → Ty →
      List Shape.Evidence → Prop where
  | nil {context target} :
      ClausesTy signature prevailing context [] capability target []
  | cons {context clause clauses target evidence evidences} :
      ClauseTy signature prevailing context clause capability target evidence →
      ClausesTy signature prevailing context clauses capability target evidences →
      ClausesTy signature prevailing context (clause :: clauses) capability
        target (evidence :: evidences)

/--
Existential packaging of the one prevailing substitution used by all actual
matcher clauses.  T-MATCHER consumes this package, so clauses cannot select
unrelated resolutions.
-/
inductive ResolvedClausesTy (signature : FrozenSig) :
    Context → List Clause → Cap → Ty → List Shape.Evidence → Prop where
  | ofShared {prevailing context clauses capability target evidence} :
      ClausesTy signature prevailing context clauses capability target evidence →
      ResolvedClausesTy signature context clauses capability target evidence

end

/-! ## Identity-resolution introductions -/

mutual

/-- Raw user-pattern typing is terminal at identity. -/
def PatternTy.terminal_id
    {signature : FrozenSig} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {pattern : Pattern} →
      {capability : Cap} → {target : Ty} → {result : MonoCtx} →
      PatternTy signature context parameters bindings pattern capability target
        result →
      TerminalPatternResolution signature Subst.id context parameters bindings
        pattern capability target result
  | _, _, _, _, _, _, _, .pvar missing freshCap freshTy => by
      simpa [Subst.apply_id] using
        (TerminalPatternResolution.pvar
          (prevailing := Subst.id) missing freshCap freshTy)
  | _, _, _, _, _, _, _, .wild freshCap freshTy => by
      simpa [Subst.apply_id] using
        (TerminalPatternResolution.wild
          (prevailing := Subst.id) freshCap freshTy)
  | _, _, _, _, _, _, _, .pval typing freshCap separate => by
      have resolved := TerminalPatternResolution.pval
        (prevailing := Subst.id) freshCap separate (by
          simpa [Subst.apply_id] using typing)
      simpa [Subst.apply_id] using resolved
  | rawContext, rawParameters, rawBindings, _, _, _, _, .embed lookup => by
      have resolved := TerminalPatternResolution.embed
        (signature := signature) (prevailing := Subst.id)
        (rawContext := rawContext) (rawParameters := rawParameters)
        (rawBindings := rawBindings) (actualContext := rawContext)
        lookup (by simpa using lookup)
      simpa [Subst.apply_id] using resolved
  | _, _, _, _, _, _, _, .tuple children => .tuple children.terminal_id
  | _, _, _, _, _, _, _, .ctor lookup children compatible inst =>
      .ctor lookup children.terminal_id compatible inst
  | _, _, _, _, _, _, _, .and left right =>
      .and left.terminal_id right.terminal_id
  | _, _, _, _, _, _, _, .or left right =>
      .or left.terminal_id right.terminal_id
  | _, _, _, _, _, _, _, .app lookup children inst =>
      .app lookup children.terminal_id inst

/-- List form of `PatternTy.terminal_id`. -/
def PatternTys.terminal_id
    {signature : FrozenSig} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {patterns : List Pattern} →
      {duals : List Dual} → {result : MonoCtx} →
      PatternTys signature context parameters bindings patterns duals result →
      TerminalPatternResolutions signature Subst.id context parameters bindings
        patterns duals result
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons head tail =>
      .cons head.terminal_id tail.terminal_id

end

mutual

/-- Forget raw compound indices and expose the actual terminal resolution. -/
def PatternResolution.terminal
    {signature : FrozenSig} {prevailing : Subst} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {pattern : Pattern} →
      {capability : Cap} → {target : Ty} → {result : MonoCtx} →
      PatternResolution signature prevailing context parameters bindings
        pattern capability target result →
      TerminalPatternResolution signature prevailing
        (context.applySubst prevailing) (parameters.applySubst prevailing)
        (bindings.applySubst prevailing) pattern
        (capability.apply prevailing.cap) (prevailing.apply target)
        (result.applySubst prevailing)
  | _, _, _, _, _, _, _, .identity equality typing => by
      subst prevailing
      simpa [Subst.apply_id] using typing.terminal_id
  | _, _, _, _, _, _, _, .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | _, _, _, _, _, _, _, .wild freshCap freshTy => .wild freshCap freshTy
  | _, _, _, _, _, _, _, .pval _ freshCap separate actualTyping =>
      .pval freshCap separate actualTyping
  | rawContext, _, _, _, _, _, _, .embed rawLookup actualLookup =>
      .embed (rawContext := rawContext)
        (actualContext := rawContext.applySubst prevailing)
        rawLookup actualLookup
  | _, _, _, _, _, _, _, .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using
        TerminalPatternResolution.tuple children.terminal
  | _, _, _, _, _, _, _,
      .ctor lookup children _ _ actualCompatible actualInstance => by
      simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
        TerminalPatternResolution.ctor lookup children.terminal
          actualCompatible actualInstance
  | _, _, _, _, _, _, _, .and left right =>
      .and left.terminal right.terminal
  | _, _, _, _, _, _, _, .or left right =>
      .or left.terminal right.terminal
  | _, _, _, _, _, _, _, .app lookup children _ actualInstance => by
      simpa only [Dual.cap_applySubst, Dual.target_applySubst] using
        TerminalPatternResolution.app lookup children.terminal actualInstance

/-- List form of `PatternResolution.terminal`. -/
def PatternResolutions.terminal
    {signature : FrozenSig} {prevailing : Subst} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {patterns : List Pattern} →
      {duals : List Dual} → {result : MonoCtx} →
      PatternResolutions signature prevailing context parameters bindings
        patterns duals result →
      TerminalPatternResolutions signature prevailing
        (context.applySubst prevailing) (parameters.applySubst prevailing)
        (bindings.applySubst prevailing) patterns
        (duals.map (Dual.applySubst prevailing))
        (result.applySubst prevailing)
  | _, _, _, _, _, _, .identity equality typing => by
      subst prevailing
      simpa [Subst.apply_id] using typing.terminal_id
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons head tail => by
      simpa [MonoCtx.applySubst, Dual.applySubst, Dual.apply] using
        TerminalPatternResolutions.cons head.terminal tail.terminal

end

mutual

/-- Recover the raw user-pattern derivation retained by an alignment. -/
def PatternResolution.raw
    {signature : FrozenSig} {prevailing : Subst} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {pattern : Pattern} →
      {capability : Cap} → {target : Ty} → {result : MonoCtx} →
      PatternResolution signature prevailing context parameters bindings
        pattern capability target result →
      PatternTy signature context parameters bindings pattern capability target
        result
  | _, _, _, _, _, _, _, .identity _ typing => typing
  | _, _, _, _, _, _, _, .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | _, _, _, _, _, _, _, .wild freshCap freshTy => .wild freshCap freshTy
  | _, _, _, _, _, _, _, .pval rawTyping freshCap separate _ =>
      .pval rawTyping freshCap separate
  | _, _, _, _, _, _, _, .embed rawLookup _ => .embed rawLookup
  | _, _, _, _, _, _, _, .tuple children => .tuple children.raw
  | _, _, _, _, _, _, _,
      .ctor lookup children rawCap rawInst _ _ =>
      .ctor lookup children.raw rawCap rawInst
  | _, _, _, _, _, _, _, .and left right =>
      .and left.raw right.raw
  | _, _, _, _, _, _, _, .or left right => .or left.raw right.raw
  | _, _, _, _, _, _, _, .app lookup children rawInst _ =>
      .app lookup children.raw rawInst

/-- List form of `PatternResolution.raw`. -/
def PatternResolutions.raw
    {signature : FrozenSig} {prevailing : Subst} :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {patterns : List Pattern} →
      {duals : List Dual} → {result : MonoCtx} →
      PatternResolutions signature prevailing context parameters bindings
        patterns duals result →
      PatternTys signature context parameters bindings patterns duals result
  | _, _, _, _, _, _, .identity _ typing => typing
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons head tail => .cons head.raw tail.raw

end

/-- Raw pattern typing resolves definitionally under identity. -/
theorem PatternTy.resolve_id
    {signature : FrozenSig} {context : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {target : Ty} {resultBindings : MonoCtx}
    (typing : PatternTy signature context parameters bindings pattern
      capability target resultBindings) :
    ResolvedPatternTy signature Subst.id context parameters bindings pattern
      capability target resultBindings := by
  simpa [Subst.apply_id] using
    ResolvedPatternTy.ofAligned (PatternResolution.identity rfl typing)

/-- Both raw-aligned and terminal introductions expose one terminal view. -/
theorem ResolvedPatternTy.terminal
    {signature : FrozenSig} {prevailing : Subst}
    {context : Context} {parameters : PatternCtx} {bindings : MonoCtx}
    {pattern : Pattern} {capability : Cap} {target : Ty}
    {resultBindings : MonoCtx}
    (typing : ResolvedPatternTy signature prevailing context parameters bindings
      pattern capability target resultBindings) :
    TerminalPatternResolution signature prevailing context parameters bindings
      pattern capability target resultBindings := by
  cases typing with
  | ofAligned resolution =>
      exact resolution.terminal
  | ofTerminal resolution => exact resolution

/-- Package identity-resolved clauses for T-MATCHER. -/
theorem ClausesTy.resolve_id
    {signature : FrozenSig} {context : Context} {clauses : List Clause}
    {capability : Cap} {target : Ty} {evidence : List Shape.Evidence}
    (typing :
      ClausesTy signature Subst.id context clauses capability target evidence) :
    ResolvedClausesTy signature context clauses capability target evidence :=
  ResolvedClausesTy.ofShared typing

/-! ## Fix inversion -/

/-- Every runtime-certified function-shaped `fix` satisfies the public
singleton direct-self boundary. -/
theorem RuntimeTyping.fix_inversion
    {signature : FrozenSig} {context : Context}
    {self argument : String} {body : Expr} {domain codomain : Ty}
    (typing :
      RuntimeTyping signature context (.fix self argument body)
        (.fn domain codomain)) :
    self ≠ argument ∧ DirectSelf.Holds self body := by
  cases typing with
  | fixE distinct direct _bodyTyping => exact ⟨distinct, direct⟩

/-- The higher-order self-flow counterexample cannot enter declarative T-FIX. -/
theorem higherOrderFix_untypable
    {signature : FrozenSig} {context : Context} {domain codomain : Ty} :
    ¬ RuntimeTyping signature context
      (.fix "f" "x" (.app (.lam "h" (.var "x")) (.var "f")))
      (.fn domain codomain) := by
  intro typing
  exact DirectSelf.self_as_argument_rejected "f" (.lam "h" (.var "x"))
    (RuntimeTyping.fix_inversion typing).2

/-! ## Matcher-literal inversion -/

/--
Inverting T-MATCHER exposes evidence from the actual clause list together
with every mandatory coverage and well-formedness premise.
-/
theorem RuntimeTyping.matcher_inversion
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing :
      RuntimeTyping signature context (.matcher clauses) (.matcher capability target)) :
    ∃ evidence,
      ResolvedClausesTy signature context clauses capability target evidence ∧
      Shape.inferShape signature.observability evidence = some capability ∧
      CatchAllLast clauses ∧
      ArmExhaustive signature clauses target ∧
      PPBindNodup clauses ∧
      ArmBindNodup clauses ∧
      CoverageOK signature.toMatcherSig clauses capability := by
  cases typing with
  | matcher clausesTyped shape catchAll exhaustive ppNodup armNodup coverage =>
      exact
        ⟨_, clausesTyped, shape, catchAll, exhaustive,
          ppNodup, armNodup, coverage⟩
  | coerceProductMatcher premise => cases premise

end TypePM
