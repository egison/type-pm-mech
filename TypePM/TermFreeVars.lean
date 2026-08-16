import TypePM.Term

/-!
# Free variables of expressions and pattern-embedded expressions

Purely syntactic support for the interpreter's no-stuck theorem.  The
statement "a typed program never gets stuck" separates two error sources:
type-shaped errors (refuted from the typing evidence) and unbound-variable
errors (refuted from a closedness invariant).  This module provides the
closedness side: free variables of expressions, the names a pattern is
guaranteed to bind on every matching branch (`Pattern.scopeVars`), and the
free names of the expressions embedded in a pattern under the left-to-right
runtime binding discipline (`Pattern.exprVarsUnder`).

Conventions:

* `Expr.freeVars` treats a matcher literal's clauses relative to the
  capturing environment: the next-matcher expression sees only that
  environment, and each arm body additionally sees its primitive-pattern
  and data-pattern binders.
* `Pattern.scopeVars` under-approximates on `por`: only names bound on both
  alternatives are guaranteed.
* `Pattern.exprVarsUnder bound p` collects the free names of `#e` value
  expressions in `p`, excluding `bound` and the pattern's own binders to
  the left of each occurrence.
-/

namespace TypePM

/-- Names bound by a runtime environment, newest first. -/
def Env.names (ρ : Env) : List String :=
  ρ.map Prod.fst

@[simp] theorem Env.names_nil : Env.names [] = [] := rfl

@[simp] theorem Env.names_cons (entry : String × Value) (ρ : Env) :
    Env.names (entry :: ρ) = entry.1 :: ρ.names := rfl

@[simp] theorem Env.names_append (left right : Env) :
    Env.names (left ++ right) = left.names ++ right.names := by
  simp [Env.names]

/-- Lookup succeeds exactly on the environment's names. -/
theorem Env.find?_isSome_of_mem_names {ρ : Env} {name : String}
    (membership : name ∈ ρ.names) :
    ∃ value, Env.find? ρ name = some value := by
  induction ρ with
  | nil => cases membership
  | cons entry ρ induction =>
      obtain ⟨entryName, entryValue⟩ := entry
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨entryValue, by simp [Env.find?]⟩
      · by_cases hName : entryName = name
        · exact ⟨entryValue, by simp [Env.find?, hName]⟩
        · obtain ⟨value, found⟩ := induction membership
          refine ⟨value, ?_⟩
          simpa [Env.find?, List.find?_cons, hName] using found

mutual

/-- Free variables of one expression, with duplicates, in occurrence
order. -/
def Expr.freeVars : Expr → List String
  | .var name => [name]
  | .lam param body => body.freeVars.removeAll [param]
  | .fix self param body => body.freeVars.removeAll [self, param]
  | .app fn arg => fn.freeVars ++ arg.freeVars
  | .lit _ => []
  | .tuple exprs => Expr.freeVarsList exprs
  | .ctor _ exprs => Expr.freeVarsList exprs
  | .prim _ exprs => Expr.freeVarsList exprs
  | .letE name bound body =>
      bound.freeVars ++ body.freeVars.removeAll [name]
  | .something => []
  | .matcher clauses => Clause.freeVarsList clauses
  | .matchAll target matcher pattern body =>
      target.freeVars ++ matcher.freeVars ++
        Pattern.exprVarsUnder [] pattern ++
        body.freeVars.removeAll pattern.scopeVars

/-- Pointwise free variables of an expression list. -/
def Expr.freeVarsList : List Expr → List String
  | [] => []
  | expression :: exprs => expression.freeVars ++ Expr.freeVarsList exprs

/-- Names one pattern is guaranteed to bind on every matching branch. -/
def Pattern.scopeVars : Pattern → List String
  | .pvar name => [name]
  | .wild => []
  | .pval _ => []
  | .embed _ => []
  | .pctor _ patterns => Pattern.scopeVarsList patterns
  | .pand left right => left.scopeVars ++ right.scopeVars
  | .por left right =>
      left.scopeVars.filter fun name => right.scopeVars.contains name
  | .papp _ patterns => Pattern.scopeVarsList patterns
  | .ptuple patterns => Pattern.scopeVarsList patterns

/-- Pointwise guaranteed binders of a pattern list. -/
def Pattern.scopeVarsList : List Pattern → List String
  | [] => []
  | pattern :: patterns =>
      pattern.scopeVars ++ Pattern.scopeVarsList patterns

/-- Free names of the value expressions embedded in one pattern, under the
left-to-right runtime binding discipline. -/
def Pattern.exprVarsUnder (bound : List String) : Pattern → List String
  | .pvar _ => []
  | .wild => []
  | .pval expression => expression.freeVars.removeAll bound
  | .embed _ => []
  | .pctor _ patterns => Pattern.exprVarsUnderList bound patterns
  | .pand left right =>
      Pattern.exprVarsUnder bound left ++
        Pattern.exprVarsUnder (bound ++ left.scopeVars) right
  | .por left right =>
      Pattern.exprVarsUnder bound left ++
        Pattern.exprVarsUnder bound right
  | .papp _ patterns => Pattern.exprVarsUnderList bound patterns
  | .ptuple patterns => Pattern.exprVarsUnderList bound patterns

/-- Left-to-right threading of `Pattern.exprVarsUnder` over a list. -/
def Pattern.exprVarsUnderList (bound : List String) :
    List Pattern → List String
  | [] => []
  | pattern :: patterns =>
      Pattern.exprVarsUnder bound pattern ++
        Pattern.exprVarsUnderList (bound ++ pattern.scopeVars) patterns

/-- Free names of one clause's expressions relative to the capturing
environment's names. -/
def Clause.freeVars : Clause → List String
  | .mk pp next arms =>
      next.freeVars ++ Arm.freeVarsList pp.bindVars arms

/-- Free names of arm bodies below their data-pattern and clause binders. -/
def Arm.freeVarsList (ppBinders : List String) : List Arm → List String
  | [] => []
  | .mk dp body :: arms =>
      body.freeVars.removeAll (dp.bindVars ++ ppBinders) ++
        Arm.freeVarsList ppBinders arms

/-- Pointwise clause free variables. -/
def Clause.freeVarsList : List Clause → List String
  | [] => []
  | clause :: clauses => clause.freeVars ++ Clause.freeVarsList clauses

end

/-! ## Subset utilities -/

/-- Removal bounds membership: a survivor was present and not removed. -/
theorem List.mem_of_mem_removeAll {name : String}
    {names removed : List String}
    (membership : name ∈ names.removeAll removed) :
    name ∈ names ∧ name ∉ removed := by
  simp only [List.removeAll, List.mem_filter] at membership
  refine ⟨membership.1, ?_⟩
  intro contradiction
  have := membership.2
  simp [List.elem_eq_contains, List.contains_eq_mem, contradiction] at this

/-- Membership survives removal of a disjoint list. -/
theorem List.mem_removeAll_of_mem {name : String}
    {names removed : List String}
    (membership : name ∈ names) (fresh : name ∉ removed) :
    name ∈ names.removeAll removed := by
  simp only [List.removeAll, List.mem_filter]
  refine ⟨membership, ?_⟩
  simpa [List.elem_eq_contains, List.contains_eq_mem] using fresh

/-- The clause table of a matcher literal is scoped by its free variables. -/
theorem Clause.freeVars_mem_of_mem
    {clause : Clause} {clauses : List Clause}
    (membership : clause ∈ clauses) :
    ∀ name ∈ clause.freeVars, name ∈ Clause.freeVarsList clauses := by
  induction clauses with
  | nil => cases membership
  | cons head tail induction =>
      intro name nameMembership
      rcases List.mem_cons.mp membership with rfl | membership
      · simp [Clause.freeVarsList, nameMembership]
      · simp [Clause.freeVarsList]
        exact .inr (induction membership name nameMembership)

/-- Arm bodies are scoped by the arm list's free variables. -/
theorem Arm.freeVars_mem_of_mem
    {dp : DPat} {body : Expr} {arms : List Arm} {ppBinders : List String}
    (membership : Arm.mk dp body ∈ arms) :
    ∀ name ∈ body.freeVars.removeAll (dp.bindVars ++ ppBinders),
      name ∈ Arm.freeVarsList ppBinders arms := by
  induction arms with
  | nil => cases membership
  | cons head tail induction =>
      obtain ⟨headDp, headBody⟩ := head
      intro name nameMembership
      rcases List.mem_cons.mp membership with headEq | membership
      · injection headEq with dpEq bodyEq
        subst dpEq
        subst bodyEq
        simp [Arm.freeVarsList]
        exact .inl nameMembership
      · simp [Arm.freeVarsList]
        exact .inr (induction membership name nameMembership)

end TypePM
