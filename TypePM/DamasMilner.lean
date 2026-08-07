import TypePM.Source

/-!
# Direct-self Damas–Milner embedding on the pattern-free fragment

This module isolates the pattern-free `λ`/`let`/direct-self `fix` fragment of
the core expression language and relates it to a one-sorted Damas–Milner system
defined from scratch below.  Its recursion rule deliberately carries the same
singleton direct-self side conditions as the core.

The main theorem `DM.HasTy.emb` is the completeness half of the intended
fragment agreement: every derivation in this direct-self-restricted
Damas–Milner system embeds into the two-sort declarative system over any closed
frozen signature, with the capability sort inert.  Under the embedding,
capability binder lists are empty, capability substitutions act trivially, and
`let` generalization commutes with the two-sort generalizer.  The converse
(conservativity) direction is not claimed here.  `TypePM.CoherentTyping`
extends the embedding with `Coherent.dm_coherent`: every DM typing lands in
the mutual coherent judgment.  Algorithmic acceptance by public inference
remains open.
-/

namespace TypePM
namespace DM

/-! ## Simple types -/

/-- One-sorted simple types of the Damas–Milner fragment. -/
inductive STy where
  | var  : TypePM.TyVar → STy
  | int
  | fn   : STy → STy → STy
  | prod : List STy → STy
deriving Repr

mutual

/-- Embed a simple type into the two-sort type syntax. -/
def STy.emb : STy → Ty
  | .var name => .var name
  | .int => .int
  | .fn domain codomain => .fn domain.emb codomain.emb
  | .prod components => .prod (STy.embList components)

/-- List form of `STy.emb`. -/
def STy.embList : List STy → List Ty
  | [] => []
  | component :: components => component.emb :: STy.embList components

end

mutual

/-- Free variables of a simple type. -/
def STy.ftv : STy → List TypePM.TyVar
  | .var name => [name]
  | .int => []
  | .fn domain codomain => domain.ftv ++ codomain.ftv
  | .prod components => STy.ftvList components

/-- Free variables of a list of simple types. -/
def STy.ftvList : List STy → List TypePM.TyVar
  | [] => []
  | component :: components => component.ftv ++ STy.ftvList components

end

/-! ## One-sorted substitutions -/

/-- Total one-sorted substitutions. -/
abbrev SSubst := TypePM.TyVar → STy

/-- A substitution is the identity away from the listed variables. -/
def SSubst.SupportWithin (S : SSubst) (vars : List TypePM.TyVar) : Prop :=
  ∀ name, name ∉ vars → S name = .var name

mutual

/-- Apply a one-sorted substitution. -/
def STy.applySubst (S : SSubst) : STy → STy
  | .var name => S name
  | .int => .int
  | .fn domain codomain =>
      .fn (domain.applySubst S) (codomain.applySubst S)
  | .prod components => .prod (STy.applySubstList S components)

/-- List form of `STy.applySubst`. -/
def STy.applySubstList (S : SSubst) : List STy → List STy
  | [] => []
  | component :: components =>
      component.applySubst S :: STy.applySubstList S components

end

/-- The identity-defaulting substitution with one binding. -/
def SSubst.single (varId : TypePM.TyVar) (replacement : STy) : SSubst :=
  fun candidate => if varId = candidate then replacement else .var candidate

/-- A single binding has exactly singleton support. -/
theorem SSubst.single_supportWithin
    (varId : TypePM.TyVar) (replacement : STy) :
    (SSubst.single varId replacement).SupportWithin [varId] := by
  intro candidate outside
  simp only [List.mem_singleton] at outside
  have distinct : varId ≠ candidate := Ne.symm outside
  simp [SSubst.single, distinct]

/-! ## Schemes, contexts, and typing -/

/-- One-sorted type schemes. -/
structure SScheme where
  binders : List TypePM.TyVar
  body : STy

/-- A monomorphic scheme. -/
def SScheme.mono (τ : STy) : SScheme :=
  ⟨[], τ⟩

/-- Damas–Milner scheme instantiation. -/
def SScheme.Inst (scheme : SScheme) (target : STy) : Prop :=
  ∃ S, SSubst.SupportWithin S scheme.binders ∧
    scheme.body.applySubst S = target

/-- Free variables of a scheme, excluding its binders. -/
def SScheme.ftv (scheme : SScheme) : List TypePM.TyVar :=
  scheme.body.ftv.filter fun name => name ∉ scheme.binders

/-- One-sorted typing contexts. -/
abbrev SCtx := List (String × SScheme)

/-- Look up a one-sorted scheme. -/
def SCtx.find? (context : SCtx) (name : String) : Option SScheme :=
  (List.find? (fun entry => entry.1 == name) context).map Prod.snd

/-- Free variables of a one-sorted context. -/
def SCtx.ftv (context : SCtx) : List TypePM.TyVar :=
  context.flatMap fun entry => entry.2.ftv

/-- Standard Damas–Milner generalization over the context. -/
def SCtx.generalize (context : SCtx) (τ : STy) : SScheme :=
  ⟨uniqueVars (τ.ftv.filter fun name => name ∉ SCtx.ftv context), τ⟩

mutual

/-- Damas–Milner typing with the core's direct-self recursion boundary. -/
inductive HasTy : SCtx → Expr → STy → Prop where
  | var {context name scheme target} :
      SCtx.find? context name = some scheme →
      scheme.Inst target →
      HasTy context (.var name) target
  | lam {context name body domain codomain} :
      HasTy ((name, SScheme.mono domain) :: context) body codomain →
      HasTy context (.lam name body) (.fn domain codomain)
  | app {context function argument domain codomain} :
      HasTy context function (.fn domain codomain) →
      HasTy context argument domain →
      HasTy context (.app function argument) codomain
  | letE {context name value body valueTy bodyTy} :
      HasTy context value valueTy →
      HasTy ((name, SCtx.generalize context valueTy) :: context)
        body bodyTy →
      HasTy context (.letE name value body) bodyTy
  | fixE {context self argument body domain codomain} :
      self ≠ argument →
      DirectSelf.Holds self body →
      HasTy ((argument, SScheme.mono domain) ::
        (self, SScheme.mono (.fn domain codomain)) :: context)
        body codomain →
      HasTy context (.fix self argument body) (.fn domain codomain)
  | lit {context value} :
      HasTy context (.lit value) .int
  | tuple {context expressions targets} :
      HasTys context expressions targets →
      HasTy context (.tuple expressions) (.prod targets)

/-- Pointwise Damas–Milner typing with exact order and arity. -/
inductive HasTys : SCtx → List Expr → List STy → Prop where
  | nil {context} : HasTys context [] []
  | cons {context expression target expressions targets} :
      HasTy context expression target →
      HasTys context expressions targets →
      HasTys context (expression :: expressions) (target :: targets)

end

/-! ## Embedding into the two-sort system -/

/-- Embed a one-sorted scheme with an empty capability binder list. -/
def SScheme.emb (scheme : SScheme) : Scheme :=
  ⟨[], scheme.binders, scheme.body.emb⟩

/-- Embed a one-sorted context. -/
def SCtx.emb (context : SCtx) : Context :=
  context.map fun entry => (entry.1, entry.2.emb)

/-- Embed a one-sorted substitution as a target substitution. -/
def SSubst.emb (S : SSubst) : TySubst :=
  fun name => (S name).emb

mutual

/-- Embedded simple types have no capability leaves. -/
theorem STy.emb_fcv : ∀ τ : STy, τ.emb.fcv = []
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      rw [STy.emb, Ty.fcv, STy.emb_fcv domain, STy.emb_fcv codomain]
      rfl
  | .prod components => by
      rw [STy.emb, Ty.fcv, STy.embList_fcv components]

/-- List form of `STy.emb_fcv`. -/
theorem STy.embList_fcv :
    ∀ components : List STy, Ty.fcvList (STy.embList components) = []
  | [] => rfl
  | component :: components => by
      rw [STy.embList, Ty.fcvList, STy.emb_fcv component,
        STy.embList_fcv components]
      rfl

end

mutual

/-- Embedding preserves the free-variable list. -/
theorem STy.emb_ftv : ∀ τ : STy, τ.emb.ftv = τ.ftv
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      rw [STy.emb, Ty.ftv, STy.emb_ftv domain, STy.emb_ftv codomain,
        STy.ftv]
  | .prod components => by
      rw [STy.emb, Ty.ftv, STy.embList_ftv components, STy.ftv]

/-- List form of `STy.emb_ftv`. -/
theorem STy.embList_ftv :
    ∀ components : List STy,
      Ty.ftvList (STy.embList components) = STy.ftvList components
  | [] => rfl
  | component :: components => by
      rw [STy.embList, Ty.ftvList, STy.emb_ftv component,
        STy.embList_ftv components, STy.ftvList]

end

mutual

/-- Capability substitutions act trivially on embedded simple types. -/
theorem STy.emb_applyCapability (C : CapSubst) :
    ∀ τ : STy, τ.emb.applyCapability C = τ.emb
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      rw [STy.emb, Ty.applyCapability, STy.emb_applyCapability C domain,
        STy.emb_applyCapability C codomain]
  | .prod components => by
      rw [STy.emb, Ty.applyCapability,
        STy.embList_applyCapability C components]

/-- List form of `STy.emb_applyCapability`. -/
theorem STy.embList_applyCapability (C : CapSubst) :
    ∀ components : List STy,
      Ty.applyCapabilityList C (STy.embList components) =
        STy.embList components
  | [] => rfl
  | component :: components => by
      rw [STy.embList, Ty.applyCapabilityList,
        STy.emb_applyCapability C component,
        STy.embList_applyCapability C components]

end

mutual

/-- Target application commutes with the embedding. -/
theorem STy.emb_applyTarget (S : SSubst) :
    ∀ τ : STy, τ.emb.applyTarget (SSubst.emb S) = (τ.applySubst S).emb
  | .var name => rfl
  | .int => rfl
  | .fn domain codomain => by
      rw [STy.emb, Ty.applyTarget, STy.emb_applyTarget S domain,
        STy.emb_applyTarget S codomain, STy.applySubst, STy.emb]
  | .prod components => by
      rw [STy.emb, Ty.applyTarget, STy.embList_applyTarget S components,
        STy.applySubst, STy.emb]

/-- List form of `STy.emb_applyTarget`. -/
theorem STy.embList_applyTarget (S : SSubst) :
    ∀ components : List STy,
      Ty.applyTargetList (SSubst.emb S) (STy.embList components) =
        STy.embList (STy.applySubstList S components)
  | [] => rfl
  | component :: components => by
      rw [STy.embList, Ty.applyTargetList,
        STy.emb_applyTarget S component,
        STy.embList_applyTarget S components, STy.applySubstList,
        STy.embList]

end

/-- Damas–Milner instantiation embeds as a safe value-flow instance. -/
theorem SScheme.emb_valueFlowInst {scheme : SScheme} {target : STy}
    (instantiation : scheme.Inst target) :
    scheme.emb.ValueFlowInst target.emb := by
  obtain ⟨S, support, result⟩ := instantiation
  refine ⟨CapSubst.id, SSubst.emb S,
    { capSupport := fun name _ => rfl
      tySupport := fun name outside => by
        show (S name).emb = .var name
        rw [support name outside]
        rfl
      capBinderVariable := fun varId membership => by
        simp [SScheme.emb] at membership
      result := ?_ }⟩
  show (scheme.body.emb.applyCapability CapSubst.id).applyTarget
      (SSubst.emb S) = target.emb
  rw [STy.emb_applyCapability, STy.emb_applyTarget, result]

/-- Context lookup commutes with the embedding. -/
theorem SCtx.find?_emb {context : SCtx} {name : String} {scheme : SScheme}
    (found : SCtx.find? context name = some scheme) :
    Context.find? (SCtx.emb context) name = some scheme.emb := by
  induction context with
  | nil => cases found
  | cons entry rest induction =>
      unfold SCtx.find? at found
      unfold Context.find? SCtx.emb
      simp only [List.map_cons, List.find?_cons] at found ⊢
      cases nameEq : (entry.1 == name) with
      | true =>
          simp only [nameEq] at found ⊢
          simp only [Option.map_some, Option.some.injEq] at found ⊢
          rw [← found]
      | false =>
          simp only [nameEq] at found ⊢
          exact induction found

/-- Embedded contexts have no free capability variables. -/
theorem SCtx.emb_fcv (context : SCtx) : Context.fcv (SCtx.emb context) = [] := by
  induction context with
  | nil => rfl
  | cons entry rest induction =>
      unfold SCtx.emb Context.fcv at induction ⊢
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]
      have schemeFcv : entry.2.emb.fcv = [] := by
        unfold Scheme.fcv SScheme.emb
        rw [STy.emb_fcv]
        rfl
      rw [schemeFcv]
      rfl

/-- Embedding preserves context free variables. -/
theorem SCtx.emb_ftv (context : SCtx) :
    Context.ftv (SCtx.emb context) = SCtx.ftv context := by
  induction context with
  | nil => rfl
  | cons entry rest induction =>
      unfold SCtx.emb Context.ftv SCtx.ftv at induction ⊢
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]
      have schemeFtv : entry.2.emb.ftv = entry.2.ftv := by
        unfold Scheme.ftv SScheme.emb SScheme.ftv
        rw [STy.emb_ftv]
      rw [schemeFtv]

/--
Over a closed signature, two-sort generalization of an embedded type is the
embedded Damas–Milner generalization.
-/
theorem generalize_emb {signature : FrozenSig}
    (sigFtv : signature.ftv = [])
    (context : SCtx) (τ : STy) :
    signature.generalize (SCtx.emb context) (STy.emb τ) =
      (SCtx.generalize context τ).emb := by
  unfold FrozenSig.generalize TypePM.generalize SCtx.generalize SScheme.emb
  congr 1
  · rw [STy.emb_fcv]
    rfl
  · rw [STy.emb_ftv, sigFtv, SCtx.emb_ftv]
    rfl

mutual

/--
Every derivation in the direct-self Damas–Milner fragment embeds into the
two-sort declarative system over any closed frozen signature.
-/
theorem HasTy.emb {signature : FrozenSig}
    (sigFtv : signature.ftv = []) :
    ∀ {context : SCtx} {expression : Expr} {target : STy},
      HasTy context expression target →
      TypePM.HasTy signature (SCtx.emb context) expression target.emb
  | _, _, _, .var found instantiation =>
      TypePM.HasTy.var (SCtx.find?_emb found)
        (SScheme.emb_valueFlowInst instantiation)
  | _, _, _, .lam bodyTyping =>
      TypePM.HasTy.lam (HasTy.emb sigFtv bodyTyping)
  | _, _, _, .app functionTyping argumentTyping =>
      TypePM.HasTy.app (HasTy.emb sigFtv functionTyping)
        (HasTy.emb sigFtv argumentTyping)
  | _, _, _, .letE valueTyping bodyTyping => by
      refine TypePM.HasTy.letE (HasTy.emb sigFtv valueTyping) ?_
      rw [generalize_emb sigFtv]
      exact HasTy.emb sigFtv bodyTyping
  | _, _, _, .fixE distinct direct bodyTyping =>
      TypePM.HasTy.fixE distinct direct (HasTy.emb sigFtv bodyTyping)
  | _, _, _, .lit =>
      TypePM.HasTy.lit
  | _, _, _, .tuple componentTypings =>
      TypePM.HasTy.tuple (HasTys.emb sigFtv componentTypings)

/-- List form of `HasTy.emb`. -/
theorem HasTys.emb {signature : FrozenSig}
    (sigFtv : signature.ftv = []) :
    ∀ {context : SCtx} {expressions : List Expr} {targets : List STy},
      HasTys context expressions targets →
      TypePM.ExprsTy signature (SCtx.emb context) expressions
        (STy.embList targets)
  | _, _, _, .nil => TypePM.ExprsTy.nil
  | _, _, _, .cons headTyping tailTypings =>
      TypePM.ExprsTy.cons (HasTy.emb sigFtv headTyping)
        (HasTys.emb sigFtv tailTypings)

end

/-! ## The polymorphic `let` witness -/

/-- The classic polymorphic-identity program. -/
def idProgram : Expr :=
  .letE "id" (.lam "x" (.var "x"))
    (.app (.app (.var "id") (.var "id")) (.lit 1))

/-- `λx.x` receives the generalized scheme `∀0.\ 0 → 0` at the `let`. -/
theorem idProgram_dm_typed : HasTy [] idProgram .int := by
  refine HasTy.letE (valueTy := .fn (.var 0) (.var 0))
    (HasTy.lam (HasTy.var (scheme := SScheme.mono (.var 0)) rfl
      ⟨fun name => .var name, fun _ _ => rfl, rfl⟩)) ?_
  refine HasTy.app (domain := .int) ?_ HasTy.lit
  refine HasTy.app (domain := .fn .int .int)
    (HasTy.var rfl ?_) (HasTy.var rfl ?_)
  · exact ⟨SSubst.single 0 (.fn .int .int),
      SSubst.single_supportWithin 0 _, rfl⟩
  · exact ⟨SSubst.single 0 .int, SSubst.single_supportWithin 0 _, rfl⟩

/-- Over any closed signature, the two-sort system types the witness at
`Int` through the embedding. -/
theorem idProgram_two_sort_typed {signature : FrozenSig}
    (sigFtv : signature.ftv = []) :
    TypePM.HasTy signature [] idProgram .int :=
  HasTy.emb sigFtv idProgram_dm_typed

end DM
end TypePM
