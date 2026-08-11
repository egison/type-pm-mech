import TypePM.Inference

/-!
# Well-formed inputs for executable inference

This module records the conventional finite source-input boundary for the
frozen Egison core.  It is kept separate from `FrozenSigWF`, whose remaining
fields concern the dynamic kernel rather than static inference.  Public
inference soundness is stronger: its fail-closed terminal validator needs no
caller-supplied `InferenceInputWF` premise once `infer` has succeeded.

Fresh-counter lower bounds are not input assumptions: `initialSupply` already
places both counters above every variable occurring in the frozen signature
and source context.  The only scheme conditions recorded here are uniqueness
of the two binder lists, together with the concrete core's fixed arm checker.
-/

namespace TypePM

/-! ## Binder hygiene -/

/-- The two quantified binder lists of an expression scheme are set-like. -/
def NamedScheme.BindersNodup (scheme : NamedScheme) : Prop :=
  scheme.capBinders.Nodup ∧ scheme.tyBinders.Nodup

/-- The two quantified binder lists of a constructor scheme are set-like. -/
def CtorScheme.BindersNodup (scheme : CtorScheme) : Prop :=
  scheme.capBinders.Nodup ∧ scheme.tyBinders.Nodup

/-- The two quantified binder lists of a dual scheme are set-like. -/
def DualScheme.BindersNodup (scheme : DualScheme) : Prop :=
  scheme.capBinders.Nodup ∧ scheme.tyBinders.Nodup

/-- Capture-avoiding substitution changes only a scheme body, so it preserves
the binder-hygiene condition definitionally. -/
theorem NamedScheme.BindersNodup.applySubst
    {scheme : NamedScheme} (wf : scheme.BindersNodup) (S : Subst) :
    (scheme.applySubst S).BindersNodup := by
  simpa [NamedScheme.BindersNodup, NamedScheme.applySubst] using wf

/-- A monomorphic scheme has no quantified binders. -/
@[simp] theorem NamedScheme.mono_bindersNodup (target : Ty) :
    (NamedScheme.mono target).BindersNodup := by
  simp [NamedScheme.BindersNodup, NamedScheme.mono]

/-- Signature-aware expression generalization always produces set-like
binder lists. -/
theorem FrozenSig.generalize_bindersNodup
    (signature : FrozenSig) (context : NamedContext) (target : Ty) :
    (signature.generalize context target).BindersNodup := by
  exact ⟨generalize_capBinders_nodup _ _ _,
    generalize_tyBinders_nodup _ _ _⟩

/-- Signature-aware dual generalization also removes duplicate binders. -/
theorem FrozenSig.generalizeDual_bindersNodup
    (signature : FrozenSig) (context : NamedContext)
    (arguments : List Dual) (result : Dual) :
    (signature.generalizeDual context arguments result).BindersNodup := by
  constructor
  · exact uniqueVars_nodup _
  · exact uniqueVars_nodup _

/-! ## Frozen-signature inputs -/

/--
The conventional static well-formedness boundary for a frozen core signature.

The binder fields are stated through the public lookup functions, so shadowed
table entries that can never be selected need not be constrained here.  The
public fail-closed `infer` neither consumes nor requires this structure for its
soundness theorem.
-/
structure FrozenSigInferenceWF (signature : FrozenSig) : Prop where
  /-- The target-insensitive conservative checker is the core checker. -/
  armExhaustiveBasic : signature.armExhaustive = basicArmExhaustive
  /-- Every selectable data-constructor scheme has unique binders. -/
  dataCtorBinders :
    ∀ {name scheme}, signature.findDataCtor name = some scheme →
      scheme.BindersNodup
  /-- Every selectable pattern-constructor scheme has unique binders. -/
  patternCtorBinders :
    ∀ {name entry}, signature.findPatternCtor name = some entry →
      entry.scheme.BindersNodup
  /-- Every selectable pattern-function scheme has unique binders. -/
  patternFunBinders :
    ∀ {name scheme}, signature.findPatternFun name = some scheme →
      scheme.BindersNodup
  /-- Every selectable primitive scheme has unique binders. -/
  primitiveBinders :
    ∀ {op scheme}, signature.findPrimitive op = some scheme →
      scheme.BindersNodup

/-! ## Source-context inputs and closure -/

/-- Every expression scheme selectable from the source context has unique
capability and ordinary binders. -/
structure ContextInferenceWF (context : NamedContext) : Prop where
  lookupBinders :
    ∀ {name scheme}, context.find? name = some scheme →
      scheme.BindersNodup

/-- Public static boundary for one executable inference run. -/
structure InferenceInputWF
    (signature : FrozenSig) (context : NamedContext) : Prop where
  signature : FrozenSigInferenceWF signature
  context : ContextInferenceWF context

/-- The empty source context is well formed for inference. -/
@[simp] theorem ContextInferenceWF.nil : ContextInferenceWF [] := by
  constructor
  intro name scheme lookup
  simp [NamedContext.find?] at lookup

/-- Adding one hygienic scheme preserves context well-formedness. -/
theorem ContextInferenceWF.cons
    {context : NamedContext} (contextWF : ContextInferenceWF context)
    {boundName : String} {scheme : NamedScheme}
    (schemeWF : scheme.BindersNodup) :
    ContextInferenceWF ((boundName, scheme) :: context) := by
  constructor
  intro name found lookup
  by_cases same : boundName = name
  · subst name
    have equality : scheme = found := by
      simpa [NamedContext.find?] using lookup
    subst found
    exact schemeWF
  · apply contextWF.lookupBinders
    simpa [NamedContext.find?, same] using lookup

/-- A monomorphic lambda, fix, or pattern binding may always be added to a
well-formed inference context. -/
theorem ContextInferenceWF.consMono
    {context : NamedContext} (contextWF : ContextInferenceWF context)
    (name : String) (target : Ty) :
    ContextInferenceWF ((name, NamedScheme.mono target) :: context) :=
  contextWF.cons (NamedScheme.mono_bindersNodup target)

/-- A let-generalized scheme may always be added to a well-formed inference
context. -/
theorem ContextInferenceWF.consGeneralize
    {context : NamedContext} (contextWF : ContextInferenceWF context)
    (signature : FrozenSig) (name : String) (target : Ty) :
    ContextInferenceWF
      ((name, signature.generalize context target) :: context) :=
  contextWF.cons (signature.generalize_bindersNodup context target)

/-- NamedContext substitution preserves lookup binder hygiene. -/
theorem ContextInferenceWF.applySubst
    {context : NamedContext} (contextWF : ContextInferenceWF context)
    (S : Subst) : ContextInferenceWF (context.applySubst S) := by
  constructor
  intro name found lookup
  rw [NamedContext.find?_applySubst] at lookup
  cases originalLookup : context.find? name with
  | none => simp [originalLookup] at lookup
  | some original =>
      have originalWF := contextWF.lookupBinders originalLookup
      have equality : original.applySubst S = found := by
        simpa [originalLookup] using lookup
      subst found
      exact originalWF.applySubst S

/-- Concatenating two well-formed lookup contexts preserves well-formedness.
The left context keeps its usual shadowing priority. -/
theorem ContextInferenceWF.append
    {left right : NamedContext}
    (leftWF : ContextInferenceWF left)
    (rightWF : ContextInferenceWF right) :
    ContextInferenceWF (left ++ right) := by
  constructor
  intro name scheme lookup
  unfold NamedContext.find? at lookup
  rw [List.find?_append] at lookup
  cases selected : List.find? (fun entry => entry.1 == name) left with
  | none =>
      apply rightWF.lookupBinders
      unfold NamedContext.find?
      simpa [selected] using lookup
  | some entry =>
      have resultEquality : entry.2 = scheme := by
        simpa [selected] using lookup
      subst scheme
      exact leftWF.lookupBinders (name := name) (scheme := entry.2) (by
        unfold NamedContext.find?
        simp [selected])

/-- A context obtained from monomorphic pattern bindings is well formed. -/
theorem MonoCtx.toContext_inferenceWF (bindings : MonoCtx) :
    ContextInferenceWF bindings.toContext := by
  induction bindings with
  | nil => exact ContextInferenceWF.nil
  | cons entry bindings induction =>
      rcases entry with ⟨name, target⟩
      simpa [MonoCtx.toContext] using induction.consMono name target

/-- Pattern bindings may be prefixed to any well-formed expression context. -/
theorem ContextInferenceWF.monoCtxAppend
    {context : NamedContext} (contextWF : ContextInferenceWF context)
    (bindings : MonoCtx) :
    ContextInferenceWF (bindings.toContext ++ context) :=
  (MonoCtx.toContext_inferenceWF bindings).append contextWF

end TypePM
