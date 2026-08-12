import TypePM.DamasMilnerAcceptance
import TypePM.DemandTypingErasure
import TypePM.Preservation

/-!
# Conservativity of the audited source judgment over Damas--Milner

This module proves the converse half of the direct-self Damas--Milner
embedding.  The boundary is deliberately stated on the public audited
`SourceTyping` judgment.  Its closed state-erasure theorem supplies the exact
published target; the structural map below then forgets capability forms.  In
particular, no internal invariant is converted back into source acceptance.

The three fragment axes are explicit:

* `InFragmentExpr` excludes every pattern, matcher, constructor, and primitive
  form syntactically;
* `ContextErases` tracks the one-sort meaning of every local scheme use;
* `FrozenSig.SchemesClosed` prevents a global signature metavariable from
  entering generalization, even though the fragment never performs a
  signature lookup.

Direct-self recursion is retained by the `TypingInvariant.fixE` constructor;
the syntactic fragment excludes the matcher-bodied source form entirely.
-/

namespace TypePM
namespace DM

open Inference

/-! ## Capability-forgetting target erasure -/

mutual

/-- Forget the extra core type forms.  Matcher and slot wrappers erase to
their carried target, so every demand-directed coercion is invisible. -/
def eraseTy : Ty → STy
  | .var name => .var name
  | .skolem _ => .int
  | .unit => .int
  | .int => .int
  | .bool => .int
  | .data _ components => .prod (eraseTys components)
  | .prod components => .prod (eraseTys components)
  | .fn domain codomain => .fn (eraseTy domain) (eraseTy codomain)
  | .matcher _ target => eraseTy target
  | .slot _ target => eraseTy target

/-- List form of `eraseTy`. -/
def eraseTys : List Ty → List STy
  | [] => []
  | target :: targets => eraseTy target :: eraseTys targets

end

theorem eraseTys_matchers (duals : List Dual) :
    eraseTys (duals.map fun dual => .matcher dual.cap dual.target) =
      eraseTys (duals.map Dual.target) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [eraseTys, eraseTy, induction]

theorem eraseTys_slots (duals : List Dual) :
    eraseTys (duals.map fun dual => .slot dual.cap dual.target) =
      eraseTys (duals.map Dual.target) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [eraseTys, eraseTy, induction]

mutual

theorem lift_ftv : ∀ target : Ty,
    (PolyTy.lift (capArity := 0) (tyArity := 0) target).ftv = target.ftv
  | .var _ => by simp [PolyTy.lift, PolyTy.ftv, Ty.ftv]
  | .skolem _ => by simp [PolyTy.lift, PolyTy.ftv, Ty.ftv]
  | .unit => by simp [PolyTy.lift, PolyTy.ftv, Ty.ftv]
  | .int => by simp [PolyTy.lift, PolyTy.ftv, Ty.ftv]
  | .bool => by simp [PolyTy.lift, PolyTy.ftv, Ty.ftv]
  | .data _ children => by
      simp [PolyTy.lift, PolyTy.ftv, Ty.ftv, lift_ftvList children]
  | .prod children => by
      simp [PolyTy.lift, PolyTy.ftv, Ty.ftv, lift_ftvList children]
  | .fn domain codomain => by
      simp [PolyTy.lift, PolyTy.ftv, Ty.ftv, lift_ftv domain,
        lift_ftv codomain]
  | .matcher _ target => by
      simp [PolyTy.lift, PolyTy.ftv, Ty.ftv, lift_ftv target]
  | .slot _ target => by
      simp [PolyTy.lift, PolyTy.ftv, Ty.ftv, lift_ftv target]

theorem lift_ftvList : ∀ targets : List Ty,
    PolyTy.ftvList (targets.map
      (PolyTy.lift (capArity := 0) (tyArity := 0))) = Ty.ftvList targets
  | [] => rfl
  | target :: targets => by
      simp [PolyTy.ftvList, Ty.ftvList, lift_ftv target,
        lift_ftvList targets]

end

mutual

/-- Exact ordinary free variables remaining after abstraction. -/
theorem abstract_ftv_exact
    {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) : ∀ target : Ty,
    (PolyTy.abstract closeCap closeTy target).ftv =
      target.ftv.filter (fun name => closeTy name = none)
  | .var name => by
      simp only [PolyTy.abstract, Ty.ftv]
      cases found : closeTy name <;>
        simp [found, PolyTy.ftv]
  | .skolem _ => by simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
  | .unit => by simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
  | .int => by simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
  | .bool => by simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv]
  | .data _ children => by
      simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv,
        abstract_ftvList_exact closeCap closeTy children]
  | .prod children => by
      simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv,
        abstract_ftvList_exact closeCap closeTy children]
  | .fn domain codomain => by
      simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv,
        abstract_ftv_exact closeCap closeTy domain,
        abstract_ftv_exact closeCap closeTy codomain, List.filter_append]
  | .matcher _ target => by
      simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv,
        abstract_ftv_exact closeCap closeTy target]
  | .slot _ target => by
      simp [PolyTy.abstract, PolyTy.ftv, Ty.ftv,
        abstract_ftv_exact closeCap closeTy target]

/-- List form of `abstract_ftv_exact`. -/
theorem abstract_ftvList_exact
    {capArity tyArity : Nat}
    (closeCap : CapVar → Option (Fin capArity))
    (closeTy : TypePM.TyVar → Option (Fin tyArity)) : ∀ targets : List Ty,
    PolyTy.ftvList (targets.map (PolyTy.abstract closeCap closeTy)) =
      (Ty.ftvList targets).filter (fun name => closeTy name = none)
  | [] => rfl
  | target :: targets => by
      simp [PolyTy.ftvList, Ty.ftvList,
        abstract_ftv_exact closeCap closeTy target,
        abstract_ftvList_exact closeCap closeTy targets,
        List.filter_append]

end

mutual

/-- Erasure preserves the ordinary free-variable list. -/
theorem eraseTy_ftv : ∀ target : Ty, (eraseTy target).ftv = target.ftv
  | .var _ => rfl
  | .skolem _ => rfl
  | .unit => rfl
  | .int => rfl
  | .bool => rfl
  | .data _ components => by
      simp [eraseTy, STy.ftv, Ty.ftv, eraseTys_ftv components]
  | .prod components => by
      simp [eraseTy, STy.ftv, Ty.ftv, eraseTys_ftv components]
  | .fn domain codomain => by
      simp [eraseTy, STy.ftv, Ty.ftv, eraseTy_ftv domain,
        eraseTy_ftv codomain]
  | .matcher _ target => by
      simp [eraseTy, Ty.ftv, eraseTy_ftv target]
  | .slot _ target => by
      simp [eraseTy, Ty.ftv, eraseTy_ftv target]

/-- List form of `eraseTy_ftv`. -/
theorem eraseTys_ftv : ∀ targets : List Ty,
    STy.ftvList (eraseTys targets) = Ty.ftvList targets
  | [] => rfl
  | target :: targets => by
      simp [eraseTys, STy.ftvList, Ty.ftvList, eraseTy_ftv target,
        eraseTys_ftv targets]

end

mutual

@[simp] theorem eraseTy_emb : ∀ target : STy,
    eraseTy target.emb = target
  | .var _ => rfl
  | .int => rfl
  | .fn domain codomain => by
      simp [STy.emb, eraseTy, eraseTy_emb domain, eraseTy_emb codomain]
  | .prod components => by
      simp [STy.emb, eraseTy, eraseTys_emb components]

@[simp] theorem eraseTys_emb : ∀ targets : List STy,
    eraseTys (STy.embList targets) = targets
  | [] => rfl
  | target :: targets => by
      simp [STy.embList, eraseTys, eraseTy_emb target,
        eraseTys_emb targets]

end

/-- Read an arbitrary core target opening back as a one-sort substitution. -/
def SSubst.ofOpening (binders : List TypePM.TyVar)
    (openTy : Fin binders.length → Ty) : SSubst :=
  fun name =>
    match binders.finIdxOf? name with
    | some index => eraseTy (openTy index)
    | none => .var name

theorem SSubst.ofOpening_supportWithin
    (binders : List TypePM.TyVar)
    (openTy : Fin binders.length → Ty) :
    (SSubst.ofOpening binders openTy).SupportWithin binders := by
  intro name outside
  simp [SSubst.ofOpening, List.finIdxOf?_eq_none_iff.mpr outside]

mutual

/-- General form of opening erasure, used at `let` generalization. -/
theorem eraseTy_instantiate_abstract
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (openCap : Fin capBinders.length → Cap)
    (openTy : Fin tyBinders.length → Ty) : ∀ target : Ty,
    eraseTy
      (PolyTy.instantiate openCap openTy
        (PolyTy.abstract (fun name => capBinders.finIdxOf? name)
          (fun name => tyBinders.finIdxOf? name) target)) =
      (eraseTy target).applySubst
        (SSubst.ofOpening tyBinders openTy)
  | .var name => by
      simp only [PolyTy.abstract]
      split <;> rename_i found
      · simp [PolyTy.instantiate, eraseTy, STy.applySubst,
          SSubst.ofOpening, found]
      · simp [PolyTy.instantiate, eraseTy, STy.applySubst,
          SSubst.ofOpening, found]
  | .skolem name => by
      simp [PolyTy.abstract, PolyTy.instantiate, eraseTy, STy.applySubst]
  | .unit => by
      simp [PolyTy.abstract, PolyTy.instantiate, eraseTy, STy.applySubst]
  | .int => by
      simp [PolyTy.abstract, PolyTy.instantiate, eraseTy, STy.applySubst]
  | .bool => by
      simp [PolyTy.abstract, PolyTy.instantiate, eraseTy, STy.applySubst]
  | .data name components => by
      simp only [PolyTy.abstract, PolyTy.instantiate, eraseTy,
        STy.applySubst]
      congr 1
      exact eraseTys_instantiate_abstract capBinders tyBinders openCap openTy
        components
  | .prod components => by
      simp only [PolyTy.abstract, PolyTy.instantiate, eraseTy,
        STy.applySubst]
      congr 1
      exact eraseTys_instantiate_abstract capBinders tyBinders openCap openTy
        components
  | .fn domain codomain => by
      simp only [PolyTy.abstract, PolyTy.instantiate, eraseTy,
        STy.applySubst]
      rw [eraseTy_instantiate_abstract capBinders tyBinders openCap openTy
          domain,
        eraseTy_instantiate_abstract capBinders tyBinders openCap openTy
          codomain]
  | .matcher capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate, eraseTy]
      exact eraseTy_instantiate_abstract capBinders tyBinders openCap openTy
        target
  | .slot capability target => by
      simp only [PolyTy.abstract, PolyTy.instantiate, eraseTy]
      exact eraseTy_instantiate_abstract capBinders tyBinders openCap openTy
        target

/-- List form of `eraseTy_instantiate_abstract`. -/
theorem eraseTys_instantiate_abstract
    (capBinders : List CapVar) (tyBinders : List TypePM.TyVar)
    (openCap : Fin capBinders.length → Cap)
    (openTy : Fin tyBinders.length → Ty) : ∀ targets : List Ty,
    eraseTys
      ((targets.map
        (PolyTy.abstract (fun name => capBinders.finIdxOf? name)
          (fun name => tyBinders.finIdxOf? name))).map
        (PolyTy.instantiate openCap openTy)) =
      STy.applySubstList (SSubst.ofOpening tyBinders openTy)
        (eraseTys targets)
  | [] => rfl
  | target :: targets => by
      simp only [List.map_cons, eraseTys, STy.applySubstList]
      rw [eraseTy_instantiate_abstract capBinders tyBinders openCap openTy
          target,
        eraseTys_instantiate_abstract capBinders tyBinders openCap openTy
          targets]

end

/-! ## Semantic context erasure -/

structure SchemeErases (core : Scheme) (dm : SScheme) : Prop where
  inst : ∀ {target : Ty}, core.ValueFlowInst target →
    dm.Inst (eraseTy target)
  ftv_eq : core.ftv = dm.ftv

structure ContextErases (core : Context) (dm : SCtx) : Prop where
  lookup : ∀ {name : String} {coreScheme : Scheme},
    core.find? name = some coreScheme →
    ∃ dmScheme : SScheme, dm.find? name = some dmScheme ∧
      SchemeErases coreScheme dmScheme
  ftv_eq : core.ftv = dm.ftv

theorem ContextErases.nil : ContextErases [] [] := by
  refine ⟨?_, rfl⟩
  intro name scheme found
  cases found

theorem SchemeErases.mono (target : Ty) :
    SchemeErases (Scheme.mono target) (SScheme.mono (eraseTy target)) := by
  refine ⟨?_, ?_⟩
  · intro actual instantiation
    rw [instantiation.mono_eq]
    exact ⟨SSubst.id, SSubst.id_supportWithin [], STy.applySubst_id _⟩
  · simp only [Scheme.mono, Scheme.ftv, SScheme.mono, SScheme.ftv]
    rw [lift_ftv, eraseTy_ftv]
    exact (List.filter_eq_self.mpr (by
      intro item membership
      rfl)).symm

theorem ContextErases.cons
    {core : Context} {dm : SCtx} {name : String}
    {coreScheme : Scheme} {dmScheme : SScheme}
    (head : SchemeErases coreScheme dmScheme)
    (tail : ContextErases core dm) :
    ContextErases ((name, coreScheme) :: core) ((name, dmScheme) :: dm) := by
  refine ⟨?_, ?_⟩
  · intro query selected found
    unfold Context.find? at found
    unfold SCtx.find?
    simp only [List.find?_cons] at found ⊢
    cases nameEq : (name == query) with
    | true =>
        simp only [nameEq, Option.map_some, Option.some.injEq] at found ⊢
        subst selected
        exact ⟨dmScheme, rfl, head⟩
    | false =>
        simp only [nameEq] at found ⊢
        exact tail.lookup found
  · simp only [Context.ftv, SCtx.ftv, List.flatMap_cons]
    rw [head.ftv_eq]
    exact congrArg (fun rest => dmScheme.ftv ++ rest) tail.ftv_eq

theorem SchemeErases.generalize
    {signature : FrozenSig} (closed : signature.SchemesClosed)
    {core : Context} {dm : SCtx} (contexts : ContextErases core dm)
    (target : Ty) :
    SchemeErases (signature.generalize core target)
      (dm.generalize (eraseTy target)) := by
  have binderEq :
      generalizedTyVars (signature.ftv ++ core.ftv) target =
        uniqueVars ((eraseTy target).ftv.filter
          (fun name => name ∉ dm.ftv)) := by
    rw [closed.signatureTargets, List.nil_append, contexts.ftv_eq,
      eraseTy_ftv]
    rfl
  refine ⟨?_, ?_⟩
  · intro actual instantiation
    rcases instantiation with ⟨opening, result⟩
    let capBinders := generalizedCapVars (signature.fcv ++ core.fcv) target
    let tyBinders := generalizedTyVars (signature.ftv ++ core.ftv) target
    change (Scheme.close capBinders tyBinders target).ValueOpening at opening
    change (Scheme.close capBinders tyBinders target).openValue opening = actual
      at result
    let chosen := SSubst.ofOpening tyBinders opening.tyImage
    refine ⟨chosen, ?_, ?_⟩
    · unfold SCtx.generalize
      rw [← binderEq]
      exact SSubst.ofOpening_supportWithin _ _
    · rw [← result]
      change (eraseTy target).applySubst chosen =
        eraseTy
          (PolyTy.instantiate (fun index => .var (opening.capImage index))
            opening.tyImage
            (PolyTy.abstract
              (fun name => capBinders.finIdxOf? name)
              (fun name => tyBinders.finIdxOf? name) target))
      exact (eraseTy_instantiate_abstract capBinders tyBinders
        (fun index => .var (opening.capImage index)) opening.tyImage target).symm
  · unfold FrozenSig.generalize Scheme.generalize Scheme.close Scheme.ftv
    rw [abstract_ftv_exact]
    unfold SCtx.generalize SScheme.ftv
    rw [← binderEq, eraseTy_ftv]
    apply List.filter_congr
    intro name membership
    simp only [List.finIdxOf?_eq_none_iff]

/-! ## Direct inversion of the internal derivation -/

mutual

theorem TypingInvariant.toDM
    {signature : FrozenSig} (closed : signature.SchemesClosed) :
    ∀ {core : Context} {dm : SCtx} {expression : Expr} {target : Ty},
      ContextErases core dm → InFragmentExpr expression →
      TypePM.TypingInvariant signature core expression target →
      Typing dm expression (eraseTy target)
  | _, _, .var _, _, contexts, _, .var found instantiated => by
      obtain ⟨dmScheme, dmFound, erases⟩ := contexts.lookup found
      exact Typing.var dmFound (erases.inst instantiated)
  | _, _, .lam _ body, _, contexts, fragment, .lam bodyTyping => by
      simp only [InFragmentExpr, inFragmentExpr] at fragment
      exact Typing.lam (TypingInvariant.toDM closed
        (contexts.cons (SchemeErases.mono _)) fragment bodyTyping)
  | _, _, .app function argument, _, contexts, fragment,
      .app functionTyping argumentTyping => by
      simp only [InFragmentExpr, inFragmentExpr, Bool.and_eq_true] at fragment
      exact Typing.app
        (TypingInvariant.toDM closed contexts fragment.1 functionTyping)
        (TypingInvariant.toDM closed contexts fragment.2 argumentTyping)
  | _, _, .letE _ value body, _, contexts, fragment,
      .letE valueTyping bodyTyping => by
      simp only [InFragmentExpr, inFragmentExpr, Bool.and_eq_true] at fragment
      exact Typing.letE
        (TypingInvariant.toDM closed contexts fragment.1 valueTyping)
        (TypingInvariant.toDM closed
          (contexts.cons (SchemeErases.generalize closed contexts _))
          fragment.2 bodyTyping)
  | _, _, .fix _ _ body, _, contexts, fragment,
      .fixE distinct direct bodyTyping => by
      simp only [InFragmentExpr, inFragmentExpr] at fragment
      exact Typing.fixE distinct direct
        (TypingInvariant.toDM closed
          ((contexts.cons (SchemeErases.mono _)).cons
            (SchemeErases.mono _)) fragment bodyTyping)
  | _, _, .lit _, _, _, _, .lit => Typing.lit
  | _, _, .tuple expressions, _, contexts, fragment, .tuple children => by
      simp only [InFragmentExpr, inFragmentExpr] at fragment
      exact Typing.tuple (ExprsTy.toDM closed contexts fragment children)
  | _, _, .ctor _ _, _, _, fragment, typing => by
      simp [InFragmentExpr, inFragmentExpr] at fragment
  | _, _, .prim _ _, _, _, fragment, typing => by
      simp [InFragmentExpr, inFragmentExpr] at fragment
  | _, _, .something, _, _, fragment, typing => by
      simp [InFragmentExpr, inFragmentExpr] at fragment
  | _, _, .matcher _, _, _, fragment, typing => by
      simp [InFragmentExpr, inFragmentExpr] at fragment
  | _, _, .matchAll _ _ _ _, _, _, fragment, typing => by
      simp [InFragmentExpr, inFragmentExpr] at fragment
  | _, _, expression, _, contexts, fragment,
      .coerceMatcherToSlot inner demand => by
      have erasedInner := TypingInvariant.toDM closed contexts fragment inner
      exact erasedInner
  | _, _, expression, _, contexts, fragment,
      .coerceProductMatcher inner => by
      have erasedInner := TypingInvariant.toDM closed contexts fragment inner
      simpa only [eraseTy, eraseTys_matchers] using erasedInner
  | _, _, expression, _, contexts, fragment,
      .coerceSlotTuple inner => by
      have erasedInner := TypingInvariant.toDM closed contexts fragment inner
      simpa only [eraseTy, eraseTys_slots] using erasedInner

theorem ExprsTy.toDM
    {signature : FrozenSig} (closed : signature.SchemesClosed) :
    ∀ {core : Context} {dm : SCtx} {expressions : List Expr}
      {targets : List Ty},
      ContextErases core dm → inFragmentExprs expressions = true →
      TypePM.ExprsTy signature core expressions targets →
      Typings dm expressions (eraseTys targets)
  | _, _, [], [], _, _, .nil => Typings.nil
  | _, _, expression :: expressions, target :: targets, contexts, fragment,
      .cons head tail => by
      simp only [inFragmentExprs, Bool.and_eq_true] at fragment
      exact Typings.cons
        (TypingInvariant.toDM closed contexts fragment.1 head)
        (ExprsTy.toDM closed contexts fragment.2 tail)

end

/-! ## Public converse -/

/-- The audited two-sort source calculus is conservative over the exact
pattern-free, capability-inert, direct-self Damas--Milner fragment.

The DM witness is the capability-forgetting erasure of the published source
target.  Fresh ordinary metavariable names are therefore preserved exactly. -/
theorem sourceTyping_to_dm
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {expression : Expr} {target : Ty}
    (fragment : InFragmentExpr expression)
    (typed : SourceTyping signature [] expression target) :
    ∃ dmTarget : STy, Typing [] expression dmTarget := by
  refine ⟨eraseTy target, ?_⟩
  exact TypingInvariant.toDM signatureWF.schemesClosed ContextErases.nil
    fragment (typed.typingInvariant signatureWF.schemesClosed)

end DM
end TypePM
