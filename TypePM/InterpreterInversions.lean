import TypePM.DynamicMetatheory
import TypePM.SignatureChecker

/-!
# Canonical-form and coercion-stripping inversion lemmas

This module supplies the inversion toolkit consumed by the no-stuck theorem:

* canonical-form inversion for arrow-typed runtime values,
* totality of the primitive delta on canonically typed arguments, and
* typing inversions for each expression former that strip any chain of the
  three unary source coercions (`coerceMatcherToSlot`, `coerceProductMatcher`,
  `coerceSlotTuple`), all of which keep the same expression and context.
-/

namespace TypePM

/-! ## Canonical forms -/

/-- A value typed at an arrow type is a closure. -/
theorem ValueTy.fn_inversion
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {value : Value} {domain codomain : Ty}
    (typing : ValueTy signature value (.fn domain codomain)) :
    ∃ self environment parameter body,
      value = .closure self environment parameter body := by
  cases typing with
  | closure =>
      exact ⟨_, _, _, _, rfl⟩
  | ctor found instanceTyping =>
      obtain ⟨former, arguments, resultEq⟩ :=
        signatureWF.dataResult found instanceTyping
      exact nomatch resultEq

/-! ## Primitive delta totality -/

/-- On canonically-typed arguments every declared primitive computes. -/
theorem primEval_isSome
    {signature : FrozenSig} (signatureWF : FrozenSigWF signature)
    {op : PrimOp} {scheme : CtorScheme} {values : List Value}
    {targets : List Ty} {result : Ty}
    (found : signature.findPrimitive op = some scheme)
    (instanceTyping : scheme.Inst targets result)
    (valuesTyped : ValueTys signature values targets) :
    ∃ value, primEval op values = some value := by
  have schemeCanonical := signatureWF.primitivesCanonical found
  subst schemeCanonical
  cases op with
  | append =>
      obtain ⟨target, targetsEq, -⟩ :=
        appendCanonicalScheme_inst_inversion instanceTyping
      subst targetsEq
      cases valuesTyped with
      | @cons leftValue _ restValues _ leftTyped restTyped =>
          cases restTyped with
          | @cons rightValue _ nilValues _ rightTyped nilTyped =>
              cases nilTyped
              obtain ⟨leftElements, leftDecode⟩ :=
                listOfV_isSome signatureWF leftTyped
              obtain ⟨rightElements, rightDecode⟩ :=
                listOfV_isSome signatureWF rightTyped
              exact ⟨mkListV (leftElements ++ rightElements),
                by simp [primEval, leftDecode, rightDecode]⟩
  | splits =>
      obtain ⟨target, targetsEq, -⟩ :=
        splitsCanonicalScheme_inst_inversion instanceTyping
      subst targetsEq
      cases valuesTyped with
      | @cons argValue _ nilValues _ argTyped nilTyped =>
          cases nilTyped
          obtain ⟨elements, argDecode⟩ :=
            listOfV_isSome signatureWF argTyped
          exact ⟨mkListV ((List.range (elements.length + 1)).map fun index =>
              .tuple [mkListV (elements.take index),
                mkListV (elements.drop index)]),
            by simp [primEval, argDecode]⟩

/-! ## Coercion-stripping typing inversions

Structural recursion over `TypingInvariant` needs every index to be a
variable, so the shared stripping recursion below keeps the expression
generic; the per-former inversions then fix the expression and eliminate
the resulting `Terminal` evidence, whose constructors are exactly the
terminal source rules.
-/

/-- Every typing certificate strips its outer source coercions to a terminal
typing of the same expression in the same context. -/
theorem TypingInvariant.exists_terminal
    {signature : FrozenSig} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : TypingInvariant signature context expression target) :
    ∃ terminalTarget : Ty,
      ∃ terminal : TypingInvariant signature context expression terminalTarget,
        TypingInvariant.Terminal terminal :=
  match typing with
  | .coerceMatcherToSlot inner _ => inner.exists_terminal
  | .coerceProductMatcher inner => inner.exists_terminal
  | .coerceSlotTuple inner => inner.exists_terminal
  | terminalTyping@(.var hfind hinst) =>
      ⟨_, terminalTyping, .var hfind hinst⟩
  | terminalTyping@(.lam bodyTyping) =>
      ⟨_, terminalTyping, .lam bodyTyping⟩
  | terminalTyping@(.app functionTyping argumentTyping) =>
      ⟨_, terminalTyping, .app functionTyping argumentTyping⟩
  | terminalTyping@(.letE valueTyping bodyTyping) =>
      ⟨_, terminalTyping, .letE valueTyping bodyTyping⟩
  | terminalTyping@(.fixE distinct direct bodyTyping) =>
      ⟨_, terminalTyping, .fixE distinct direct bodyTyping⟩
  | terminalTyping@(.lit) =>
      ⟨_, terminalTyping, .lit⟩
  | terminalTyping@(.tuple expressionsTyping) =>
      ⟨_, terminalTyping, .tuple expressionsTyping⟩
  | terminalTyping@(.ctor hfind hinst expressionsTyping) =>
      ⟨_, terminalTyping, .ctor hfind hinst expressionsTyping⟩
  | terminalTyping@(.prim hfind hinst expressionsTyping) =>
      ⟨_, terminalTyping, .prim hfind hinst expressionsTyping⟩
  | terminalTyping@(.something) =>
      ⟨_, terminalTyping, .something⟩
  | terminalTyping@(.matchAll targetTyping patternTyping matcherTyping
      bodyTyping) =>
      ⟨_, terminalTyping,
        .matchAll targetTyping patternTyping matcherTyping bodyTyping⟩
  | terminalTyping@(.matcher clausesTyping shape catchAll exhaustive ppNodup
      armNodup coverage) =>
      ⟨_, terminalTyping,
        .matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
          coverage⟩

/-- Invert a variable typing through any chain of source coercions. -/
theorem TypingInvariant.var_facts
    {signature : FrozenSig} {context : Context} {name : String}
    {target : Ty}
    (typing : TypingInvariant signature context (.var name) target) :
    ∃ scheme, Context.find? context name = some scheme := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | var hfind _ => exact ⟨_, hfind⟩

/-- Invert an application typing through any chain of source coercions. -/
theorem TypingInvariant.app_facts
    {signature : FrozenSig} {context : Context} {fn arg : Expr}
    {target : Ty}
    (typing : TypingInvariant signature context (.app fn arg) target) :
    ∃ domain codomain,
      TypingInvariant signature context fn (.fn domain codomain) ∧
      TypingInvariant signature context arg domain := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | app functionTyping argumentTyping =>
      exact ⟨_, _, functionTyping, argumentTyping⟩

/-- Invert a `let` typing through any chain of source coercions. -/
theorem TypingInvariant.letE_facts
    {signature : FrozenSig} {context : Context} {name : String}
    {bound body : Expr} {target : Ty}
    (typing : TypingInvariant signature context (.letE name bound body)
      target) :
    ∃ valueTy bodyTy,
      TypingInvariant signature context bound valueTy ∧
      TypingInvariant signature
        ((name, signature.generalize context valueTy) :: context) body
        bodyTy := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | letE valueTyping bodyTyping => exact ⟨_, _, valueTyping, bodyTyping⟩

/-- Invert a tuple typing through any chain of source coercions. -/
theorem TypingInvariant.tuple_facts
    {signature : FrozenSig} {context : Context} {exprs : List Expr}
    {target : Ty}
    (typing : TypingInvariant signature context (.tuple exprs) target) :
    ∃ targets, ExprsTy signature context exprs targets := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | tuple expressionsTyping => exact ⟨_, expressionsTyping⟩

/-- Invert a data-constructor typing through any chain of source coercions. -/
theorem TypingInvariant.ctorE_facts
    {signature : FrozenSig} {context : Context} {name : String}
    {exprs : List Expr} {target : Ty}
    (typing : TypingInvariant signature context (.ctor name exprs) target) :
    ∃ scheme targets result,
      signature.findDataCtor name = some scheme ∧
      scheme.Inst targets result ∧
      ExprsTy signature context exprs targets := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | ctor hfind hinst expressionsTyping =>
      exact ⟨_, _, _, hfind, hinst, expressionsTyping⟩

/-- Invert a primitive typing through any chain of source coercions. -/
theorem TypingInvariant.prim_facts
    {signature : FrozenSig} {context : Context} {op : PrimOp}
    {exprs : List Expr} {target : Ty}
    (typing : TypingInvariant signature context (.prim op exprs) target) :
    ∃ scheme targets result,
      signature.findPrimitive op = some scheme ∧
      scheme.Inst targets result ∧
      ExprsTy signature context exprs targets := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | prim hfind hinst expressionsTyping =>
      exact ⟨_, _, _, hfind, hinst, expressionsTyping⟩

/-- Invert a `matchAll` typing through any chain of source coercions. -/
theorem TypingInvariant.matchAll_facts
    {signature : FrozenSig} {context : Context}
    {target matcher : Expr} {pattern : Pattern} {body : Expr}
    {overall : Ty}
    (typing :
      TypingInvariant signature context
        (.matchAll target matcher pattern body) overall) :
    ∃ (prevailing : Subst) (targetTy : Ty) (patternCap : Cap) (result : Ty)
      (bindings : MonoCtx),
      TypingInvariant signature context target targetTy ∧
      ResolvedPatternTy signature prevailing context [] [] pattern
        patternCap targetTy bindings ∧
      TypingInvariant signature context matcher (.slot patternCap targetTy) ∧
      TypingInvariant signature (bindings.toContext ++ context) body
        result := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | matchAll targetTyping patternTyping matcherTyping bodyTyping =>
      exact ⟨_, _, _, _, _, targetTyping, patternTyping, matcherTyping,
        bodyTyping⟩

/-- Invert a lambda typing through any chain of source coercions. -/
theorem TypingInvariant.lam_facts
    {signature : FrozenSig} {context : Context} {param : String}
    {body : Expr} {target : Ty}
    (typing : TypingInvariant signature context (.lam param body) target) :
    ∃ domain codomain,
      TypingInvariant signature ((param, Scheme.mono domain) :: context)
        body codomain := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | lam bodyTyping => exact ⟨_, _, bodyTyping⟩

/-- Invert a `fix` typing through any chain of source coercions. -/
theorem TypingInvariant.fix_facts
    {signature : FrozenSig} {context : Context} {self param : String}
    {body : Expr} {target : Ty}
    (typing : TypingInvariant signature context (.fix self param body)
      target) :
    ∃ domain codomain,
      self ≠ param ∧
      DirectSelf.Holds self body ∧
      TypingInvariant signature
        ((param, Scheme.mono domain) ::
          (self, Scheme.mono (.fn domain codomain)) :: context)
        body codomain := by
  obtain ⟨_, _, terminal⟩ := typing.exists_terminal
  cases terminal with
  | fixE distinct direct bodyTyping => exact ⟨_, _, distinct, direct, bodyTyping⟩

/-- A pointwise expression-list typing zips into per-element typings. -/
theorem ExprsTy.zip_facts
    {signature : FrozenSig} {context : Context} :
    {exprs : List Expr} → {targets : List Ty} →
    ExprsTy signature context exprs targets →
    exprs.length = targets.length ∧
      ∀ pair ∈ exprs.zip targets,
        TypingInvariant signature context pair.1 pair.2
  | _, _, .nil => ⟨rfl, fun _ membership => nomatch membership⟩
  | _, _, .cons headTyping tailTyping =>
      have tail := tailTyping.zip_facts
      ⟨by simpa using tail.1, by
        intro pair membership
        rw [List.zip_cons_cons] at membership
        rcases List.mem_cons.mp membership with rfl | membership
        · exact headTyping
        · exact tail.2 pair membership⟩

end TypePM
