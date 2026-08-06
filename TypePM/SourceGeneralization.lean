import TypePM.SourceSubstitution
import TypePM.PatternFunction
import TypePM.InferenceBase

/-!
# Signature-aware source generalization

This module derives the admissible use of a source derivation at every safe
instance of its signature-aware generalization.  The proof works with the
ordered binder-local posts exposed by `SourceSubstitution`; it does not assume
a transported typing derivation or a blanket source-transport oracle.
-/

namespace TypePM

/-! ## Declarative instances of signature-aware generalizations -/

/--
Restrict one ordered action to exactly the binders selected by expression
generalization.  Fixing the ambient free variables makes this restriction
agree with the original action on the generalized body.
-/
theorem FrozenSig.generalize_valueFlowInst
    {signature : FrozenSig} {context : Context} {source : Ty} {S : Subst}
    (capFixed : ∀ varId,
      varId ∈ signature.fcv ++ context.fcv → S.cap varId = .var varId)
    (tyFixed : ∀ varId,
      varId ∈ signature.ftv ++ context.ftv → S.target varId = .var varId)
    (capVariable : ∀ varId, ∃ image, S.cap varId = .var image) :
    (signature.generalize context source).ValueFlowInst (S.apply source) := by
  let scheme := signature.generalize context source
  let C : CapSubst := fun varId =>
    if varId ∈ scheme.capBinders then S.cap varId else .var varId
  let T : TySubst := fun varId =>
    if varId ∈ scheme.tyBinders then S.target varId else .var varId
  refine ⟨C, T, ?_⟩
  refine
    { capSupport := ?_
      tySupport := ?_
      capBinderVariable := ?_
      result := ?_ }
  · intro varId outside
    have outside' : varId ∉ scheme.capBinders := by
      simpa [scheme] using outside
    simp [C, outside']
  · intro varId outside
    have outside' : varId ∉ scheme.tyBinders := by
      simpa [scheme] using outside
    simp [T, outside']
  · intro varId membership
    have membership' : varId ∈ scheme.capBinders := by
      simpa [scheme] using membership
    rcases capVariable varId with ⟨image, equation⟩
    exact ⟨image, by simp [C, membership', equation]⟩
  · change (Subst.mk C T).apply source = S.apply source
    apply Subst.apply_eq_of_free_agree
    · intro varId membership
      by_cases environment : varId ∈ signature.fcv ++ context.fcv
      · have outside : varId ∉ scheme.capBinders := by
          intro binder
          exact (mem_generalize_capBinders_not_env binder) environment
        simp [C, outside, capFixed varId environment]
      · have binder : varId ∈ scheme.capBinders := by
          exact mem_generalize_capBinders membership environment
        simp [C, binder]
    · intro varId membership
      by_cases environment : varId ∈ signature.ftv ++ context.ftv
      · have outside : varId ∉ scheme.tyBinders := by
          intro binder
          exact (mem_generalize_tyBinders_not_env binder) environment
        simp [T, outside, tyFixed varId environment]
      · have binder : varId ∈ scheme.tyBinders := by
          exact mem_generalize_tyBinders membership environment
        simp [T, binder]

/-- Dual counterpart of `FrozenSig.generalize_valueFlowInst`. -/
theorem FrozenSig.generalizeDual_valueFlowInst
    {signature : FrozenSig} {context : Context}
    {sourceArgs : List Dual} {sourceResult : Dual} {S : Subst}
    (capFixed : ∀ varId,
      varId ∈ signature.fcv ++ context.fcv → S.cap varId = .var varId)
    (tyFixed : ∀ varId,
      varId ∈ signature.ftv ++ context.ftv → S.target varId = .var varId)
    (capVariable : ∀ varId, ∃ image, S.cap varId = .var image) :
    (signature.generalizeDual context sourceArgs sourceResult).ValueFlowInst
      (sourceArgs.map (Dual.applySubst S))
      (sourceResult.applySubst S) := by
  let scheme := signature.generalizeDual context sourceArgs sourceResult
  let C : CapSubst := fun varId =>
    if varId ∈ scheme.capBinders then S.cap varId else .var varId
  let T : TySubst := fun varId =>
    if varId ∈ scheme.tyBinders then S.target varId else .var varId
  have capBinderOf : ∀ {varId},
      varId ∈ sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv →
      varId ∉ signature.fcv ++ context.fcv →
      varId ∈ scheme.capBinders := by
    intro varId sourceMembership environment
    exact mem_uniqueVars.mpr
      (List.mem_filter.mpr ⟨sourceMembership, by simp [environment]⟩)
  have capBinderNotEnv : ∀ {varId},
      varId ∈ scheme.capBinders →
      varId ∉ signature.fcv ++ context.fcv := by
    intro varId binder environment
    have binder' : varId ∈
        (signature.generalizeDual context sourceArgs sourceResult).capBinders := by
      simpa [scheme] using binder
    have filtered : varId ∈
        (sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv).filter
          fun candidate => candidate ∉ signature.fcv ++ context.fcv := by
      exact mem_uniqueVars.mp (by
        simpa only [FrozenSig.generalizeDual] using binder')
    exact (of_decide_eq_true (List.mem_filter.mp filtered).2) environment
  have tyBinderOf : ∀ {varId},
      varId ∈ sourceArgs.flatMap Dual.ftv ++ sourceResult.ftv →
      varId ∉ signature.ftv ++ context.ftv →
      varId ∈ scheme.tyBinders := by
    intro varId sourceMembership environment
    exact mem_uniqueVars.mpr
      (List.mem_filter.mpr ⟨sourceMembership, by simp [environment]⟩)
  have dualEquation : ∀ dual ∈ sourceArgs,
      dual.apply C T = dual.applySubst S := by
    intro dual dualMembership
    cases dual with
    | mk capability target =>
        simp only [Dual.apply, Dual.applySubst]
        congr 1
        · apply Cap.apply_eq_of_fcv_agree
          intro varId membership
          by_cases environment : varId ∈ signature.fcv ++ context.fcv
          · have outside : varId ∉ scheme.capBinders := by
              intro binder
              change varId ∈ uniqueVars
                ((sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv).filter
                  fun candidate =>
                    candidate ∉ signature.fcv ++ context.fcv) at binder
              exact (of_decide_eq_true
                (List.mem_filter.mp (mem_uniqueVars.mp binder)).2) environment
            simp [C, outside, capFixed varId environment]
          · have sourceMembership :
                varId ∈ sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv :=
              List.mem_append_left _
                (List.mem_flatMap.mpr
                  ⟨⟨capability, target⟩, dualMembership, by
                    simpa [Dual.fcv] using (Or.inl membership)⟩)
            have binder := capBinderOf sourceMembership environment
            simp [C, binder]
        · apply Subst.apply_eq_of_free_agree
          · intro varId membership
            by_cases environment : varId ∈ signature.fcv ++ context.fcv
            · have outside : varId ∉ scheme.capBinders := by
                intro binder
                change varId ∈ uniqueVars
                  ((sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv).filter
                    fun candidate =>
                      candidate ∉ signature.fcv ++ context.fcv) at binder
                exact (of_decide_eq_true
                  (List.mem_filter.mp (mem_uniqueVars.mp binder)).2) environment
              simp [C, outside, capFixed varId environment]
            · have sourceMembership :
                  varId ∈ sourceArgs.flatMap Dual.fcv ++ sourceResult.fcv :=
                List.mem_append_left _
                  (List.mem_flatMap.mpr
                    ⟨⟨capability, target⟩, dualMembership, by
                      simpa [Dual.fcv] using (Or.inr membership)⟩)
              have binder := capBinderOf sourceMembership environment
              simp [C, binder]
          · intro varId membership
            by_cases environment : varId ∈ signature.ftv ++ context.ftv
            · have outside : varId ∉ scheme.tyBinders := by
                intro binder
                change varId ∈ uniqueVars
                  ((sourceArgs.flatMap Dual.ftv ++ sourceResult.ftv).filter
                    fun candidate =>
                      candidate ∉ signature.ftv ++ context.ftv) at binder
                exact (of_decide_eq_true
                  (List.mem_filter.mp (mem_uniqueVars.mp binder)).2) environment
              simp [T, outside, tyFixed varId environment]
            · have sourceMembership :
                  varId ∈ sourceArgs.flatMap Dual.ftv ++ sourceResult.ftv :=
                List.mem_append_left _
                  (List.mem_flatMap.mpr
                    ⟨⟨capability, target⟩, dualMembership, membership⟩)
              have binder := tyBinderOf sourceMembership environment
              simp [T, binder]
  have resultEquation : sourceResult.apply C T =
      sourceResult.applySubst S := by
    cases sourceResult with
    | mk capability target =>
        simp only [Dual.apply, Dual.applySubst]
        congr 1
        · apply Cap.apply_eq_of_fcv_agree
          intro varId membership
          by_cases environment : varId ∈ signature.fcv ++ context.fcv
          · have outside : varId ∉ scheme.capBinders := by
              intro binder
              exact (capBinderNotEnv binder) environment
            simp [C, outside, capFixed varId environment]
          · have sourceMembership :
                varId ∈ sourceArgs.flatMap Dual.fcv ++
                  (Dual.mk capability target).fcv :=
              List.mem_append_right _ (by
                simpa [Dual.fcv] using (Or.inl membership))
            have binder := capBinderOf sourceMembership environment
            simp [C, binder]
        · apply Subst.apply_eq_of_free_agree
          · intro varId membership
            by_cases environment : varId ∈ signature.fcv ++ context.fcv
            · have outside : varId ∉ scheme.capBinders := by
                intro binder
                exact (capBinderNotEnv binder) environment
              simp [C, outside, capFixed varId environment]
            · have sourceMembership :
                  varId ∈ sourceArgs.flatMap Dual.fcv ++
                    (Dual.mk capability target).fcv :=
                List.mem_append_right _ (by
                  simpa [Dual.fcv] using (Or.inr membership))
              have binder := capBinderOf sourceMembership environment
              simp [C, binder]
          · intro varId membership
            by_cases environment : varId ∈ signature.ftv ++ context.ftv
            · have outside : varId ∉ scheme.tyBinders := by
                intro binder
                change varId ∈ uniqueVars
                  ((sourceArgs.flatMap Dual.ftv ++ target.ftv).filter
                    fun candidate =>
                      candidate ∉ signature.ftv ++ context.ftv) at binder
                exact (of_decide_eq_true
                  (List.mem_filter.mp (mem_uniqueVars.mp binder)).2) environment
              simp [T, outside, tyFixed varId environment]
            · have sourceMembership :
                  varId ∈ sourceArgs.flatMap Dual.ftv ++
                    (Dual.mk capability target).ftv :=
                List.mem_append_right _ membership
              have binder := tyBinderOf sourceMembership environment
              simp [T, binder]
  refine ⟨C, T, ?_⟩
  refine
    { capSupport := ?_
      tySupport := ?_
      capBinderVariable := ?_
      argsResult := ?_
      resultResult := resultEquation }
  · intro varId outside
    have outside' : varId ∉ scheme.capBinders := by
      simpa [scheme] using outside
    simp [C, outside']
  · intro varId outside
    have outside' : varId ∉ scheme.tyBinders := by
      simpa [scheme] using outside
    simp [T, outside']
  · intro varId membership
    have membership' : varId ∈ scheme.capBinders := by
      simpa [scheme] using membership
    rcases capVariable varId with ⟨image, equation⟩
    exact ⟨image, by simp [C, membership', equation]⟩
  · change sourceArgs.map (Dual.apply C T) =
      sourceArgs.map (Dual.applySubst S)
    apply List.map_congr_left
    intro dual membership
    exact dualEquation dual membership

/-! ## Internal source-context value flow -/

/--
One context entry transports every concrete use along any ordered post that
agrees with the surrounding action on the entry's genuinely free variables.
This parametric form lets T-LET freshen its local binders without changing the
action observed by the ambient context.
-/
def Scheme.FlowsUnder
    (S : Subst) (source target : Scheme) : Prop :=
  ∀ {A : Subst}, VariablePost A →
    (∀ varId, varId ∈ source.fcv → A.cap varId = S.cap varId) →
    (∀ varId, varId ∈ source.ftv → A.target varId = S.target varId) →
    ∀ {sourceTy : Ty}, source.ValueFlowInst sourceTy →
      target.ValueFlowInst (A.apply sourceTy)

/--
Aligned source contexts preserve names and transport each scheme use.  This
is an internal induction invariant; the public generalization theorem
constructs it from binder-local algebra and exposes no extra premise.
-/
inductive Context.FlowsUnder (S : Subst) : Context → Context → Prop where
  | nil : Context.FlowsUnder S [] []
  | cons {name sourceScheme targetScheme source target} :
      sourceScheme.FlowsUnder S targetScheme →
      Context.FlowsUnder S source target →
      Context.FlowsUnder S
        ((name, sourceScheme) :: source) ((name, targetScheme) :: target)

/-- A flowed context lookup produces a flowed target entry. -/
theorem Context.FlowsUnder.find?
    {S : Subst} {source target : Context}
    (flow : Context.FlowsUnder S source target)
    {name : String} {scheme : Scheme}
    (lookup : source.find? name = some scheme) :
    ∃ targetScheme,
      target.find? name = some targetScheme ∧
      scheme.FlowsUnder S targetScheme := by
  induction flow with
  | nil => simp [Context.find?] at lookup
  | @cons headName sourceScheme targetScheme source target headFlow tailFlow ih =>
      by_cases equal : headName = name
      · subst headName
        have schemeEq : scheme = sourceScheme := by
          have lookup' : some sourceScheme = some scheme := by
            simpa [Context.find?] using lookup
          exact (Option.some.inj lookup').symm
        subst scheme
        exact ⟨targetScheme, by simp [Context.find?], headFlow⟩
      · have tailLookup : source.find? name = some scheme := by
          simpa [Context.find?, equal] using lookup
        rcases ih tailLookup with ⟨found, foundLookup, foundFlow⟩
        exact ⟨found, by simpa [Context.find?, equal] using foundLookup,
          foundFlow⟩

/-- Monomorphic binders flow pointwise. -/
theorem Scheme.mono_flowsUnder (S : Subst) (source : Ty) :
    (Scheme.mono source).FlowsUnder S (Scheme.mono (S.apply source)) := by
  intro A _ capAgreement tyAgreement actual instanceTyping
  have actualEq := instanceTyping.mono_eq
  subst actual
  have appliedEq : A.apply source = S.apply source := by
    apply Subst.apply_eq_of_free_agree
    · intro varId membership
      exact capAgreement varId (by
        simpa [Scheme.mono, Scheme.fcv] using membership)
    · intro varId membership
      exact tyAgreement varId (by
        simpa [Scheme.mono, Scheme.ftv] using membership)
  rw [appliedEq]
  exact Scheme.mono_valueFlowInst (S.apply source)

/-- Flowing contexts can be extended by a transformed monomorphic binder. -/
theorem Context.FlowsUnder.consMono
    {S : Subst} {source target : Context}
    (flow : Context.FlowsUnder S source target)
    (name : String) (sourceTy : Ty) :
    Context.FlowsUnder S
      ((name, Scheme.mono sourceTy) :: source)
      ((name, Scheme.mono (S.apply sourceTy)) :: target) :=
  .cons (Scheme.mono_flowsUnder S sourceTy) flow

/-- Pointwise extension of a flowed context by transformed mono bindings. -/
theorem Context.FlowsUnder.prependMono
    {S : Subst} {source target : Context}
    (flow : Context.FlowsUnder S source target) :
    ∀ bindings : MonoCtx,
      Context.FlowsUnder S (bindings.toContext ++ source)
        ((bindings.applySubst S).toContext ++ target)
  | [] => flow
  | (name, bindingTy) :: bindings => by
      simpa [MonoCtx.toContext, MonoCtx.applySubst] using
        (flow.prependMono bindings).consMono name bindingTy

/-- Re-index one parametric scheme flow by an ambiently equal action. -/
theorem Scheme.FlowsUnder.reindex
    {S A : Subst} {source target : Scheme}
    (flow : source.FlowsUnder S target)
    (capAgreement : ∀ varId, varId ∈ source.fcv →
      A.cap varId = S.cap varId)
    (tyAgreement : ∀ varId, varId ∈ source.ftv →
      A.target varId = S.target varId) :
    source.FlowsUnder A target := by
  intro B postVariable capBA tyBA sourceTy instanceTyping
  apply flow postVariable
  · intro varId membership
    rw [capBA varId membership, capAgreement varId membership]
  · intro varId membership
    rw [tyBA varId membership, tyAgreement varId membership]
  · exact instanceTyping

/-- Re-index an aligned context by an action equal on all context frees. -/
theorem Context.FlowsUnder.reindex
    {S A : Subst} {source target : Context}
    (flow : Context.FlowsUnder S source target)
    (capAgreement : ∀ varId, varId ∈ source.fcv →
      A.cap varId = S.cap varId)
    (tyAgreement : ∀ varId, varId ∈ source.ftv →
      A.target varId = S.target varId) :
    Context.FlowsUnder A source target := by
  induction flow with
  | nil => exact .nil
  | @cons name sourceScheme targetScheme source target head tail ih =>
      apply Context.FlowsUnder.cons
      · apply head.reindex
        · intro varId membership
          exact capAgreement varId (by
            simp [Context.fcv, membership])
        · intro varId membership
          exact tyAgreement varId (by
            simp [Context.ftv, membership])
      · apply ih
        · intro varId membership
          apply capAgreement varId
          change varId ∈ sourceScheme.fcv ++ source.fcv
          exact List.mem_append_right _ membership
        · intro varId membership
          apply tyAgreement varId
          change varId ∈ sourceScheme.ftv ++ source.ftv
          exact List.mem_append_right _ membership

/-- A scheme flows to itself when the surrounding action fixes its frees. -/
theorem Scheme.self_flowsUnder
    {S : Subst} {scheme : Scheme}
    (capFixed : ∀ varId, varId ∈ scheme.fcv →
      S.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ scheme.ftv →
      S.target varId = .var varId) :
    scheme.FlowsUnder S scheme := by
  intro A postVariable capAgreement tyAgreement sourceTy instanceTyping
  apply instanceTyping.transport
  · intro varId membership
    rw [capAgreement varId membership, capFixed varId membership]
  · intro varId membership
    rw [tyAgreement varId membership, tyFixed varId membership]
  · exact postVariable.capVariable

/-- A context flows to itself when the surrounding action fixes its frees. -/
theorem Context.self_flowsUnder
    {S : Subst} (context : Context)
    (capFixed : ∀ varId, varId ∈ context.fcv →
      S.cap varId = .var varId)
    (tyFixed : ∀ varId, varId ∈ context.ftv →
      S.target varId = .var varId) :
    Context.FlowsUnder S context context := by
  induction context with
  | nil => exact .nil
  | cons entry context ih =>
      rcases entry with ⟨name, scheme⟩
      apply Context.FlowsUnder.cons
      · apply Scheme.self_flowsUnder
        · intro varId membership
          exact capFixed varId (by simp [Context.fcv, membership])
        · intro varId membership
          exact tyFixed varId (by simp [Context.ftv, membership])
      · apply ih
        · intro varId membership
          apply capFixed varId
          change varId ∈ scheme.fcv ++ Context.fcv context
          exact List.mem_append_right _ membership
        · intro varId membership
          apply tyFixed varId
          change varId ∈ scheme.ftv ++ Context.ftv context
          exact List.mem_append_right _ membership

/-! ## Capture-avoiding local freshening for T-LET -/

namespace LocalFreshening

/-- The capability variables that a local fresh batch must avoid. -/
noncomputable def capAvoid
    (signature : FrozenSig) (targetContext : Context)
    (source : Ty) {S : Subst} (postVariable : VariablePost S) :
    List CapVar :=
  signature.fcv ++ targetContext.fcv ++
    source.fcv.map postVariable.capRen ++
    source.ftv.flatMap fun varId => (S.target varId).fcv

/-- The ordinary variables that a local fresh batch must avoid. -/
def tyAvoid
    (signature : FrozenSig) (targetContext : Context)
    (source : Ty) (S : Subst) : List TypePM.TyVar :=
  signature.ftv ++ targetContext.ftv ++
    source.ftv.flatMap fun varId => (S.target varId).ftv

/-- First capability identifier outside the finite local avoidance set. -/
noncomputable def capNext
    (signature : FrozenSig) (targetContext : Context)
    (source : Ty) {S : Subst} (postVariable : VariablePost S) : Nat :=
  InferenceBase.binderSpan
    ((capAvoid signature targetContext source postVariable).map CapVar.id)

/-- First ordinary identifier outside the finite local avoidance set. -/
def tyNext
    (signature : FrozenSig) (targetContext : Context)
    (source : Ty) (S : Subst) : Nat :=
  InferenceBase.binderSpan (tyAvoid signature targetContext source S)

/-- The fresh capability image assigned to one local generalized binder. -/
def capImage (next : Nat) (varId : CapVar) : CapVar :=
  ⟨next + varId.id⟩

/-- The fresh ordinary image assigned to one local generalized binder. -/
def tyImage (next : Nat) (varId : TypePM.TyVar) : TypePM.TyVar :=
  next + varId

/--
Mask the surrounding post on one generalized binder batch, replacing those
binders by a disjoint variable batch and retaining the post everywhere else.
-/
def maskedPost
    (scheme : Scheme) (S : Subst) (capStart tyStart : Nat) : Subst :=
  { cap := fun varId =>
      if varId ∈ scheme.capBinders then
        .var (capImage capStart varId)
      else
        S.cap varId
    target := fun varId =>
      if varId ∈ scheme.tyBinders then
        .var (tyImage tyStart varId)
      else
        S.target varId }

/-- A masked local post keeps its capability component variable-valued. -/
theorem maskedPost_variable
    {scheme : Scheme} {S : Subst} {capStart tyStart : Nat}
    (postVariable : VariablePost S) :
    VariablePost (maskedPost scheme S capStart tyStart) := by
  constructor
  intro varId
  by_cases binder : varId ∈ scheme.capBinders
  · exact ⟨capImage capStart varId, by simp [maskedPost, binder]⟩
  · rcases postVariable.capVariable varId with ⟨image, equation⟩
    exact ⟨image, by simp [maskedPost, binder, equation]⟩

@[simp] theorem maskedPost_cap_binder
    {scheme : Scheme} {S : Subst} {capStart tyStart : Nat}
    {varId : CapVar} (binder : varId ∈ scheme.capBinders) :
    (maskedPost scheme S capStart tyStart).cap varId =
      .var (capImage capStart varId) := by
  simp [maskedPost, binder]

@[simp] theorem maskedPost_target_binder
    {scheme : Scheme} {S : Subst} {capStart tyStart : Nat}
    {varId : TypePM.TyVar} (binder : varId ∈ scheme.tyBinders) :
    (maskedPost scheme S capStart tyStart).target varId =
      .var (tyImage tyStart varId) := by
  simp [maskedPost, binder]

@[simp] theorem maskedPost_cap_outside
    {scheme : Scheme} {S : Subst} {capStart tyStart : Nat}
    {varId : CapVar} (outside : varId ∉ scheme.capBinders) :
    (maskedPost scheme S capStart tyStart).cap varId = S.cap varId := by
  simp [maskedPost, outside]

@[simp] theorem maskedPost_target_outside
    {scheme : Scheme} {S : Subst} {capStart tyStart : Nat}
    {varId : TypePM.TyVar} (outside : varId ∉ scheme.tyBinders) :
    (maskedPost scheme S capStart tyStart).target varId = S.target varId := by
  simp [maskedPost, outside]

/--
Replay an old binder-local instance through a fresh binder batch.  Variables
outside that batch are fixed, so this post is suitable for target-side
generalization.
-/
def replayPost
    (scheme : Scheme) (capStart tyStart : Nat)
    (instancePost outer : Subst) : Subst :=
  { cap := fun freshVar =>
      let sourceVar : CapVar := ⟨freshVar.id - capStart⟩
      if capStart ≤ freshVar.id ∧ sourceVar ∈ scheme.capBinders then
        (instancePost.cap sourceVar).apply outer.cap
      else
        .var freshVar
    target := fun freshVar =>
      let sourceVar : TypePM.TyVar := freshVar - tyStart
      if tyStart ≤ freshVar ∧ sourceVar ∈ scheme.tyBinders then
        outer.apply (instancePost.target sourceVar)
      else
        .var freshVar }

@[simp] theorem replayPost_cap_image
    {scheme : Scheme} {capStart tyStart : Nat}
    {instancePost outer : Subst} {varId : CapVar}
    (binder : varId ∈ scheme.capBinders) :
    (replayPost scheme capStart tyStart instancePost outer).cap
        (capImage capStart varId) =
      (instancePost.cap varId).apply outer.cap := by
  simp [replayPost, capImage, binder]

@[simp] theorem replayPost_target_image
    {scheme : Scheme} {capStart tyStart : Nat}
    {instancePost outer : Subst} {varId : TypePM.TyVar}
    (binder : varId ∈ scheme.tyBinders) :
    (replayPost scheme capStart tyStart instancePost outer).target
        (tyImage tyStart varId) =
      outer.apply (instancePost.target varId) := by
  simp [replayPost, tyImage, binder]

/-- A replay post fixes every capability identifier below its fresh region. -/
theorem replayPost_cap_fixed_of_lt
    {scheme : Scheme} {capStart tyStart : Nat}
    {instancePost outer : Subst} {varId : CapVar}
    (below : varId.id < capStart) :
    (replayPost scheme capStart tyStart instancePost outer).cap varId =
      .var varId := by
  have notAbove : ¬ capStart ≤ varId.id := Nat.not_le_of_lt below
  simp [replayPost, notAbove]

/-- A replay post fixes every ordinary identifier below its fresh region. -/
theorem replayPost_target_fixed_of_lt
    {scheme : Scheme} {capStart tyStart : Nat}
    {instancePost outer : Subst} {varId : TypePM.TyVar}
    (below : varId < tyStart) :
    (replayPost scheme capStart tyStart instancePost outer).target varId =
      .var varId := by
  have notAbove : ¬ tyStart ≤ varId := Nat.not_le_of_lt below
  simp [replayPost, notAbove]

/-- Every capability in the finite avoidance set lies below its fresh region. -/
theorem cap_lt_capNext_of_mem
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} {postVariable : VariablePost S}
    {varId : CapVar}
    (membership : varId ∈ capAvoid signature targetContext source postVariable) :
    varId.id < capNext signature targetContext source postVariable := by
  apply InferenceBase.mem_lt_binderSpan
  exact List.mem_map.mpr ⟨varId, membership, rfl⟩

/-- Every ordinary variable in the avoidance set lies below its fresh region. -/
theorem ty_lt_tyNext_of_mem
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} {varId : TypePM.TyVar}
    (membership : varId ∈ tyAvoid signature targetContext source S) :
    varId < tyNext signature targetContext source S := by
  exact InferenceBase.mem_lt_binderSpan membership

/-- Replay fixes the complete finite capability avoidance set. -/
theorem replayPost_cap_fixed_of_mem_avoid
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} {postVariable : VariablePost S}
    {scheme : Scheme} {instancePost outer : Subst}
    {varId : CapVar}
    (membership : varId ∈ capAvoid signature targetContext source postVariable) :
    (replayPost scheme
      (capNext signature targetContext source postVariable)
      (tyNext signature targetContext source S)
      instancePost outer).cap varId = .var varId :=
  replayPost_cap_fixed_of_lt (cap_lt_capNext_of_mem membership)

/-- Replay fixes the complete finite ordinary avoidance set. -/
theorem replayPost_target_fixed_of_mem_avoid
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} {postVariable : VariablePost S}
    {scheme : Scheme} {instancePost outer : Subst}
    {varId : TypePM.TyVar}
    (membership : varId ∈ tyAvoid signature targetContext source S) :
    (replayPost scheme
      (capNext signature targetContext source postVariable)
      (tyNext signature targetContext source S)
      instancePost outer).target varId = .var varId :=
  replayPost_target_fixed_of_lt (ty_lt_tyNext_of_mem membership)

/-- Replaying capability-variable binder images through a capability-variable
outer post again gives a capability-variable post. -/
theorem replayPost_variable
    {scheme : Scheme} {capStart tyStart : Nat}
    {instancePost outer : Subst}
    (instanceCapVariable : ∀ varId, varId ∈ scheme.capBinders →
      ∃ image, instancePost.cap varId = .var image)
    (outerVariable : VariablePost outer) :
    VariablePost (replayPost scheme capStart tyStart instancePost outer) := by
  constructor
  intro freshVar
  let sourceVar : CapVar := ⟨freshVar.id - capStart⟩
  by_cases inBatch : capStart ≤ freshVar.id ∧
      sourceVar ∈ scheme.capBinders
  · rcases instanceCapVariable sourceVar inBatch.2 with
      ⟨middle, middleEquation⟩
    rcases outerVariable.capVariable middle with ⟨image, imageEquation⟩
    exact ⟨image, by
      simp [replayPost, sourceVar, inBatch, middleEquation]
      simpa only [Cap.apply] using imageEquation⟩
  · exact ⟨freshVar, by simp [replayPost, sourceVar, inBatch]⟩

/-- Concrete capture-avoiding post selected for one T-LET value. -/
noncomputable def localPost
    (signature : FrozenSig) (sourceContext targetContext : Context)
    (source : Ty) {S : Subst} (postVariable : VariablePost S) : Subst :=
  maskedPost (signature.generalize sourceContext source) S
    (capNext signature targetContext source postVariable)
    (tyNext signature targetContext source S)

/-- The selected T-LET post keeps its capability component variable-valued. -/
theorem localPost_variable
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S) :
    VariablePost
      (localPost signature sourceContext targetContext source postVariable) :=
  maskedPost_variable postVariable

/-- Local freshening is invisible on the source context's capability frees. -/
theorem localPost_cap_agrees_context
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {varId : CapVar} (membership : varId ∈ sourceContext.fcv) :
    (localPost signature sourceContext targetContext source postVariable).cap
        varId = S.cap varId := by
  apply maskedPost_cap_outside
  intro binder
  exact (mem_generalize_capBinders_not_env binder)
    (by simp [membership])

/-- Local freshening is invisible on the source context's ordinary frees. -/
theorem localPost_target_agrees_context
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {varId : TypePM.TyVar} (membership : varId ∈ sourceContext.ftv) :
    (localPost signature sourceContext targetContext source postVariable).target
        varId = S.target varId := by
  apply maskedPost_target_outside
  intro binder
  exact (mem_generalize_tyBinders_not_env binder)
    (by simp [membership])

/-- Local freshening is likewise invisible on frozen-signature frees. -/
theorem localPost_cap_agrees_signature
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {varId : CapVar} (membership : varId ∈ signature.fcv) :
    (localPost signature sourceContext targetContext source postVariable).cap
        varId = S.cap varId := by
  apply maskedPost_cap_outside
  intro binder
  exact (mem_generalize_capBinders_not_env binder)
    (by simp [membership])

/-- Ordinary frozen-signature frees are unaffected by local freshening. -/
theorem localPost_target_agrees_signature
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {varId : TypePM.TyVar} (membership : varId ∈ signature.ftv) :
    (localPost signature sourceContext targetContext source postVariable).target
        varId = S.target varId := by
  apply maskedPost_target_outside
  intro binder
  exact (mem_generalize_tyBinders_not_env binder)
    (by simp [membership])

/-- The surrounding image of a source capability free is explicitly avoided. -/
theorem capRen_mem_capAvoid
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {varId : CapVar} (membership : varId ∈ source.fcv) :
    postVariable.capRen varId ∈
      capAvoid signature targetContext source postVariable := by
  change postVariable.capRen varId ∈
    signature.fcv ++ targetContext.fcv ++
      source.fcv.map postVariable.capRen ++
      source.ftv.flatMap fun sourceVar => (S.target sourceVar).fcv
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨varId, membership, rfl⟩

/-- Capability frees in surrounding target images are explicitly avoided. -/
theorem target_fcv_mem_capAvoid
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S)
    {sourceVar : TypePM.TyVar} (sourceMembership : sourceVar ∈ source.ftv)
    {varId : CapVar} (membership : varId ∈ (S.target sourceVar).fcv) :
    varId ∈ capAvoid signature targetContext source postVariable := by
  change varId ∈ signature.fcv ++ targetContext.fcv ++
    source.fcv.map postVariable.capRen ++
      source.ftv.flatMap fun candidate => (S.target candidate).fcv
  apply List.mem_append_right
  exact (List.mem_flatMap
    (f := fun candidate : TypePM.TyVar => (S.target candidate).fcv)).mpr
      ⟨sourceVar, sourceMembership, membership⟩

/-- Ordinary frees in surrounding target images are explicitly avoided. -/
theorem target_ftv_mem_tyAvoid
    {signature : FrozenSig} {targetContext : Context}
    {source : Ty} {S : Subst}
    {sourceVar : TypePM.TyVar} (sourceMembership : sourceVar ∈ source.ftv)
    {varId : TypePM.TyVar} (membership : varId ∈ (S.target sourceVar).ftv) :
    varId ∈ tyAvoid signature targetContext source S := by
  change varId ∈ signature.ftv ++ targetContext.ftv ++
    source.ftv.flatMap fun candidate => (S.target candidate).ftv
  apply List.mem_append_right
  exact (List.mem_flatMap
    (f := fun candidate : TypePM.TyVar => (S.target candidate).ftv)).mpr
      ⟨sourceVar, sourceMembership, membership⟩

/--
The inverse replay post turns the locally freshened body into the same result
as applying an arbitrary old local instance and then the surrounding post.
This is the algebraic core of the T-LET case.
-/
theorem replay_localPost_apply
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source sourceInstance : Ty} {S outer : Subst}
    (postVariable : VariablePost S)
    (outerCapAgreement : ∀ varId,
      varId ∈ (signature.generalize sourceContext source).fcv →
        outer.cap varId = S.cap varId)
    (outerTargetAgreement : ∀ varId,
      varId ∈ (signature.generalize sourceContext source).ftv →
        outer.target varId = S.target varId)
    {C : CapSubst} {T : TySubst}
    (instanceTyping :
      (signature.generalize sourceContext source).VariableInstAt
        C T sourceInstance) :
    let scheme := signature.generalize sourceContext source
    let instancePost := Subst.mk C T
    let capStart := capNext signature targetContext source postVariable
    let tyStart := tyNext signature targetContext source S
    (replayPost scheme capStart tyStart instancePost outer).apply
        ((localPost signature sourceContext targetContext source postVariable).apply
          source) =
      outer.apply sourceInstance := by
  dsimp only
  rw [← Subst.seq_apply]
  rw [← instanceTyping.result]
  rw [← Subst.seq_apply]
  apply Subst.apply_eq_of_free_agree
  · intro varId membership
    change
      ((localPost signature sourceContext targetContext source postVariable).cap
          varId).apply
        (replayPost (signature.generalize sourceContext source)
          (capNext signature targetContext source postVariable)
          (tyNext signature targetContext source S)
          (Subst.mk C T) outer).cap =
      (C varId).apply outer.cap
    by_cases binder : varId ∈
        (signature.generalize sourceContext source).capBinders
    · rw [show
          (localPost signature sourceContext targetContext source postVariable).cap
              varId =
            .var (capImage
              (capNext signature targetContext source postVariable) varId) by
          exact maskedPost_cap_binder binder]
      simp only [Cap.apply]
      exact replayPost_cap_image binder
    · have free : varId ∈
          (signature.generalize sourceContext source).fcv :=
        List.mem_filter.mpr ⟨membership, by simpa⟩
      have imageMembership : postVariable.capRen varId ∈
          capAvoid signature targetContext source postVariable :=
        capRen_mem_capAvoid postVariable membership
      rw [show
        (localPost signature sourceContext targetContext source postVariable).cap
            varId = S.cap varId by
          exact maskedPost_cap_outside binder]
      rw [postVariable.capEquation]
      rw [instanceTyping.capSupport varId binder]
      change
        (replayPost (signature.generalize sourceContext source)
          (capNext signature targetContext source postVariable)
          (tyNext signature targetContext source S)
          (Subst.mk C T) outer).cap (postVariable.capRen varId) =
        outer.cap varId
      rw [replayPost_cap_fixed_of_mem_avoid imageMembership]
      rw [outerCapAgreement varId free, postVariable.capEquation]
  · intro varId membership
    change
      (replayPost (signature.generalize sourceContext source)
        (capNext signature targetContext source postVariable)
        (tyNext signature targetContext source S)
        (Subst.mk C T) outer).apply
          ((localPost signature sourceContext targetContext source postVariable).target
            varId) =
      outer.apply (T varId)
    by_cases binder : varId ∈
        (signature.generalize sourceContext source).tyBinders
    · rw [show
          (localPost signature sourceContext targetContext source postVariable).target
              varId =
            .var (tyImage (tyNext signature targetContext source S) varId) by
          exact maskedPost_target_binder binder]
      change
        (replayPost (signature.generalize sourceContext source)
          (capNext signature targetContext source postVariable)
          (tyNext signature targetContext source S)
          (Subst.mk C T) outer).target
            (tyImage (tyNext signature targetContext source S) varId) =
          outer.apply (T varId)
      exact
        (replayPost_target_image
          (scheme := signature.generalize sourceContext source)
          (capStart := capNext signature targetContext source postVariable)
          (tyStart := tyNext signature targetContext source S)
          (instancePost := Subst.mk C T) (outer := outer) binder)
    · have free : varId ∈
          (signature.generalize sourceContext source).ftv :=
        List.mem_filter.mpr ⟨membership, by simpa⟩
      have replayFixed :
          (replayPost (signature.generalize sourceContext source)
            (capNext signature targetContext source postVariable)
            (tyNext signature targetContext source S)
            (Subst.mk C T) outer).apply (S.target varId) =
            S.target varId := by
        apply Subst.apply_eq_self_of_free_fixed
        · intro capVar capMembership
          apply replayPost_cap_fixed_of_mem_avoid
          exact target_fcv_mem_capAvoid postVariable membership capMembership
        · intro tyVar tyMembership
          apply replayPost_target_fixed_of_mem_avoid
          exact target_ftv_mem_tyAvoid membership tyMembership
      rw [show
        (localPost signature sourceContext targetContext source postVariable).target
            varId = S.target varId by
          exact maskedPost_target_outside binder]
      rw [instanceTyping.tySupport varId binder]
      change
        (replayPost (signature.generalize sourceContext source)
          (capNext signature targetContext source postVariable)
          (tyNext signature targetContext source S)
          (Subst.mk C T) outer).apply (S.target varId) =
        outer.target varId
      rw [replayFixed, outerTargetAgreement varId free]

end LocalFreshening

/--
Capture-avoiding generalization flow for a T-LET head.  The target scheme is
built from a locally freshened value type; every old binder-local instance is
replayed through that fresh batch, so no numerical binder collision with the
surrounding post can monomorphize the binding.
-/
theorem FrozenSig.generalize_flowsUnder
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst} (postVariable : VariablePost S) :
    (signature.generalize sourceContext source).FlowsUnder S
      (signature.generalize targetContext
        ((LocalFreshening.localPost signature sourceContext targetContext
          source postVariable).apply source)) := by
  intro outer outerVariable outerCapAgreement outerTargetAgreement
    sourceInstance instanceTyping
  rcases instanceTyping with ⟨C, T, instanceTyping⟩
  let sourceScheme := signature.generalize sourceContext source
  let instancePost := Subst.mk C T
  let capStart := LocalFreshening.capNext
    signature targetContext source postVariable
  let tyStart := LocalFreshening.tyNext signature targetContext source S
  let replay := LocalFreshening.replayPost
    sourceScheme capStart tyStart instancePost outer
  have replayVariable : VariablePost replay := by
    apply LocalFreshening.replayPost_variable
    · exact instanceTyping.capBinderVariable
    · exact outerVariable
  have replayCapFixed : ∀ varId,
      varId ∈ signature.fcv ++ targetContext.fcv →
        replay.cap varId = .var varId := by
    intro varId membership
    apply LocalFreshening.replayPost_cap_fixed_of_mem_avoid
    apply List.mem_append_left
    apply List.mem_append_left
    exact membership
  have replayTargetFixed : ∀ varId,
      varId ∈ signature.ftv ++ targetContext.ftv →
        replay.target varId = .var varId := by
    intro varId membership
    apply LocalFreshening.replayPost_target_fixed_of_mem_avoid
    apply List.mem_append_left
    exact membership
  have replayed := FrozenSig.generalize_valueFlowInst
    (signature := signature) (context := targetContext)
    (source :=
      (LocalFreshening.localPost signature sourceContext targetContext
        source postVariable).apply source)
    (S := replay) replayCapFixed replayTargetFixed
      replayVariable.capVariable
  change
    (signature.generalize targetContext
      ((LocalFreshening.localPost signature sourceContext targetContext
        source postVariable).apply source)).ValueFlowInst
      (replay.apply
        ((LocalFreshening.localPost signature sourceContext targetContext
          source postVariable).apply source)) at replayed
  have resultEquation := LocalFreshening.replay_localPost_apply
    (signature := signature) (sourceContext := sourceContext)
    (targetContext := targetContext) (source := source)
    (sourceInstance := sourceInstance) postVariable
    outerCapAgreement outerTargetAgreement instanceTyping
  rw [resultEquation] at replayed
  exact replayed

/-- Extend a flowed context by one capture-avoiding generalized T-LET head. -/
theorem Context.FlowsUnder.consGeneralizedFresh
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst}
    (flow : Context.FlowsUnder S sourceContext targetContext)
    (postVariable : VariablePost S) (name : String) :
    Context.FlowsUnder S
      ((name, signature.generalize sourceContext source) :: sourceContext)
      ((name, signature.generalize targetContext
        ((LocalFreshening.localPost signature sourceContext targetContext
          source postVariable).apply source)) :: targetContext) :=
  .cons (signature.generalize_flowsUnder postVariable) flow

/-- Re-index a flowed context by the locally masked T-LET post. -/
theorem Context.FlowsUnder.reindexLocal
    {signature : FrozenSig} {sourceContext targetContext : Context}
    {source : Ty} {S : Subst}
    (flow : Context.FlowsUnder S sourceContext targetContext)
    (postVariable : VariablePost S) :
    Context.FlowsUnder
      (LocalFreshening.localPost signature sourceContext targetContext
        source postVariable)
      sourceContext targetContext := by
  apply flow.reindex
  · intro varId membership
    exact LocalFreshening.localPost_cap_agrees_context
      (signature := signature) (sourceContext := sourceContext)
      (targetContext := targetContext) (source := source)
      postVariable membership
  · intro varId membership
    exact LocalFreshening.localPost_target_agrees_context
      (signature := signature) (sourceContext := sourceContext)
      (targetContext := targetContext) (source := source)
      postVariable membership

/-! ## Raw pattern resolution under one ordered post -/

set_option maxHeartbeats 800000
mutual

/--
Resolve a raw pattern directly under a post.  The two callbacks are discharged
by the surrounding mutual source proof: one transports an embedded value
expression, and the other composes a nested pattern-function instance.  They
are local induction hypotheses, not public admissibility assumptions.
-/
theorem PatternTy.resolveUnderPost
    {signature : FrozenSig} {S : Subst}
    (postVariable : VariablePost S)
    (expressionFlow :
      ∀ {context : Context} {bindings : MonoCtx}
        {expression : Expr} {target : Ty},
        HasTy signature (bindings.toContext ++ context) expression target →
        HasTy signature
          ((bindings.applySubst S).toContext ++ context.applySubst S)
          expression (S.apply target))
    (patternFunctionFlow :
      ∀ {scheme : DualScheme} {args : List Dual} {result : Dual},
        scheme.ValueFlowInst args result →
        scheme.ValueFlowInst
          (args.map (Dual.applySubst S)) (result.applySubst S))
    (constructorInstances : signature.PatternCtorInstCompositionAdm S) :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {pattern : Pattern} →
      {capability : Cap} → {target : Ty} → {result : MonoCtx} →
      PatternTy signature context parameters bindings pattern capability target
        result →
      TerminalPatternResolution signature S
        (context.applySubst S) (parameters.applySubst S)
        (bindings.applySubst S) pattern (capability.apply S.cap)
        (S.apply target) (result.applySubst S)
  | _, _, _, _, _, _, _, .pvar missing freshCap freshTy =>
      .pvar missing freshCap freshTy
  | _, _, _, _, _, _, _, .wild freshCap freshTy =>
      .wild freshCap freshTy
  | _, _, _, _, _, _, _, .pval typing freshCap separate =>
      .pval freshCap separate (expressionFlow typing)
  | rawContext, rawParameters, rawBindings, _, _, _, _, .embed lookup => by
      apply TerminalPatternResolution.embed
        (rawContext := rawContext) (rawParameters := rawParameters)
        (rawBindings := rawBindings) lookup
      rw [PatternCtx.find?_applySubst, lookup]
      rfl
  | _, _, _, _, _, _, _, .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using
        TerminalPatternResolution.tuple
          (PatternTys.resolveUnderPost postVariable expressionFlow patternFunctionFlow
            constructorInstances children)
  | _, _, _, _, _, _, _, .ctor lookup children compatible instantiated => by
      rename_i ctorPatterns ctorDuals resultDual
      have renamedCompatible := compatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      apply TerminalPatternResolution.ctor
        (result := resultDual.applySubst S) lookup
        (PatternTys.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances children)
      ·
        simpa only [Dual.map_cap_applySubst, Dual.cap_applySubst] using
          renamedCompatible
      ·
        simpa only [PatternCtorScheme.Inst,
          Dual.map_target_applySubst, Dual.target_applySubst] using
          (CtorScheme.Inst.transport instantiated
            (constructorInstances lookup))
  | _, _, _, _, _, _, _, .and left right =>
      .and
        (PatternTy.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances left)
        (PatternTy.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances right)
  | _, _, _, _, _, _, _, .or left right =>
      .or
        (PatternTy.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances left)
        (PatternTy.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances right)
  | _, _, _, _, _, _, _, .app lookup children instantiated => by
      exact TerminalPatternResolution.app lookup
        (PatternTys.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances children)
        (patternFunctionFlow instantiated)

/-- List form of `PatternTy.resolveUnderPost`. -/
theorem PatternTys.resolveUnderPost
    {signature : FrozenSig} {S : Subst}
    (postVariable : VariablePost S)
    (expressionFlow :
      ∀ {context : Context} {bindings : MonoCtx}
        {expression : Expr} {target : Ty},
        HasTy signature (bindings.toContext ++ context) expression target →
        HasTy signature
          ((bindings.applySubst S).toContext ++ context.applySubst S)
          expression (S.apply target))
    (patternFunctionFlow :
      ∀ {scheme : DualScheme} {args : List Dual} {result : Dual},
        scheme.ValueFlowInst args result →
        scheme.ValueFlowInst
          (args.map (Dual.applySubst S)) (result.applySubst S))
    (constructorInstances : signature.PatternCtorInstCompositionAdm S) :
    {context : Context} → {parameters : PatternCtx} →
      {bindings : MonoCtx} → {patterns : List Pattern} →
      {duals : List Dual} → {result : MonoCtx} →
      PatternTys signature context parameters bindings patterns duals result →
      TerminalPatternResolutions signature S
        (context.applySubst S) (parameters.applySubst S)
        (bindings.applySubst S) patterns (duals.map (Dual.applySubst S))
        (result.applySubst S)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons head tail =>
      .cons
        (PatternTy.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances head)
        (PatternTys.resolveUnderPost postVariable expressionFlow patternFunctionFlow
          constructorInstances tail)

end

/-! ## Transport of already-resolved user patterns -/

/-- Capability application follows the capability component of `Subst.seq`. -/
theorem Cap.apply_substSeq (later earlier : Subst) (capability : Cap) :
    capability.apply (Subst.seq later earlier).cap =
      (capability.apply earlier.cap).apply later.cap := by
  exact Cap.apply_comp later.cap earlier.cap capability

mutual

/--
Append one capability-variable/structural-target post to a terminal
user-pattern resolution while
allowing the actual expression context to follow `Context.FlowsUnder`.  Raw
freshness and provenance are unchanged; only the explicit actual context and
the concrete `pval` typing premise move.
-/
theorem TerminalPatternResolution.transportUnderPost
    {signature : FrozenSig} {prevailing S : Subst}
    (postVariable : VariablePost S)
    (expressionFlow :
      ∀ {sourceContext targetContext : Context}
        {expression : Expr} {target : Ty},
        Context.FlowsUnder S sourceContext targetContext →
        HasTy signature sourceContext expression target →
        HasTy signature targetContext expression (S.apply target))
    (patternFunctionFlow :
      ∀ {scheme : DualScheme} {args : List Dual} {result : Dual},
        scheme.ValueFlowInst args result →
        scheme.ValueFlowInst
          (args.map (Dual.applySubst S)) (result.applySubst S))
    (constructorInstances : signature.PatternCtorInstCompositionAdm S) :
    {sourceContext targetContext : Context} →
      {parameters : PatternCtx} → {bindings : MonoCtx} →
      {pattern : Pattern} → {capability : Cap} → {target : Ty} →
      {resultBindings : MonoCtx} →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolution signature prevailing sourceContext parameters
        bindings pattern capability target resultBindings →
      TerminalPatternResolution signature (Subst.seq S prevailing)
        targetContext (parameters.applySubst S) (bindings.applySubst S)
        pattern (capability.apply S.cap) (S.apply target)
        (resultBindings.applySubst S)
  | _, targetContext, _, _, _, _, _, _, contextFlow,
      .pvar missing freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.pvar
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) missing freshCap freshTy)
  | _, targetContext, _, _, _, _, _, _, contextFlow,
      .wild freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.wild
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) freshCap freshTy)
  | sourceContext, targetContext, _, _, _, _, _, _, contextFlow,
      .pval freshCap separate typing => by
      rename_i rawContext rawParameters rawBindings expression rawTarget capVar
      have bindingFlow := contextFlow.prependMono
        (rawBindings.applySubst prevailing)
      have movedTyping := expressionFlow bindingFlow typing
      have resolved := TerminalPatternResolution.pval
        (prevailing := Subst.seq S prevailing)
        (actualContext := targetContext) freshCap separate (by
          simpa only [MonoCtx.applySubst_seq, Subst.seq_apply] using movedTyping)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | _, targetContext, _, _, _, _, _, _, contextFlow,
      .embed rawLookup actualLookup => by
      rename_i rawContext rawParameters rawBindings name dual
      have nextLookup :
          ((rawParameters.applySubst prevailing).applySubst S).find? name =
            some ((dual.applySubst prevailing).applySubst S) := by
        rw [PatternCtx.find?_applySubst, actualLookup]
        rfl
      have resolved := TerminalPatternResolution.embed
        (signature := signature) (prevailing := Subst.seq S prevailing)
        (rawContext := rawContext) (rawParameters := rawParameters)
        (rawBindings := rawBindings) (actualContext := targetContext)
        rawLookup (by
          simpa only [PatternCtx.applySubst_seq, Dual.applySubst_seq] using
            nextLookup)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | _, _, _, _, _, _, _, _, contextFlow, .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using
        TerminalPatternResolution.tuple
          (TerminalPatternResolutions.transportUnderPost postVariable
            expressionFlow patternFunctionFlow constructorInstances
            contextFlow children)
  | _, _, _, _, _, _, _, _, contextFlow,
      .ctor lookup children compatible instantiated => by
      rename_i name entry patterns duals resultBindings result
      have renamedCompatible := compatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      apply TerminalPatternResolution.ctor
        (result := result.applySubst S) lookup
        (TerminalPatternResolutions.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow children)
      · simpa only [Dual.map_cap_applySubst, Dual.cap_applySubst] using
          renamedCompatible
      · simpa only [PatternCtorScheme.Inst,
          Dual.map_target_applySubst, Dual.target_applySubst] using
          (CtorScheme.Inst.transport instantiated
            (constructorInstances lookup))
  | _, _, _, _, _, _, _, _, contextFlow, .and left right =>
      .and
        (TerminalPatternResolution.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow left)
        (TerminalPatternResolution.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow right)
  | _, _, _, _, _, _, _, _, contextFlow, .or left right =>
      .or
        (TerminalPatternResolution.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow left)
        (TerminalPatternResolution.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow right)
  | _, _, _, _, _, _, _, _, contextFlow,
      .app lookup children instantiated => by
      rename_i name scheme patterns duals resultBindings result
      exact TerminalPatternResolution.app lookup
        (TerminalPatternResolutions.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow children)
        (patternFunctionFlow instantiated)

/-- List form of `TerminalPatternResolution.transportUnderPost`. -/
theorem TerminalPatternResolutions.transportUnderPost
    {signature : FrozenSig} {prevailing S : Subst}
    (postVariable : VariablePost S)
    (expressionFlow :
      ∀ {sourceContext targetContext : Context}
        {expression : Expr} {target : Ty},
        Context.FlowsUnder S sourceContext targetContext →
        HasTy signature sourceContext expression target →
        HasTy signature targetContext expression (S.apply target))
    (patternFunctionFlow :
      ∀ {scheme : DualScheme} {args : List Dual} {result : Dual},
        scheme.ValueFlowInst args result →
        scheme.ValueFlowInst
          (args.map (Dual.applySubst S)) (result.applySubst S))
    (constructorInstances : signature.PatternCtorInstCompositionAdm S) :
    {sourceContext targetContext : Context} →
      {parameters : PatternCtx} → {bindings : MonoCtx} →
      {patterns : List Pattern} → {duals : List Dual} →
      {resultBindings : MonoCtx} →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolutions signature prevailing sourceContext parameters
        bindings patterns duals resultBindings →
      TerminalPatternResolutions signature (Subst.seq S prevailing)
        targetContext (parameters.applySubst S) (bindings.applySubst S)
        patterns (duals.map (Dual.applySubst S))
        (resultBindings.applySubst S)
  | _, _, _, _, _, _, _, _contextFlow, .nil => .nil
  | _, _, _, _, _, _, _, contextFlow, .cons head tail =>
      .cons
        (TerminalPatternResolution.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow head)
        (TerminalPatternResolutions.transportUnderPost postVariable
          expressionFlow patternFunctionFlow constructorInstances
          contextFlow tail)

end

/-- Transport an actual resolved user pattern through a flowed context. -/
theorem ResolvedPatternTy.transportUnderPost
    {signature : FrozenSig} {prevailing S : Subst}
    (postVariable : VariablePost S)
    (expressionFlow :
      ∀ {sourceContext targetContext : Context}
        {expression : Expr} {target : Ty},
        Context.FlowsUnder S sourceContext targetContext →
        HasTy signature sourceContext expression target →
        HasTy signature targetContext expression (S.apply target))
    (patternFunctionFlow :
      ∀ {scheme : DualScheme} {args : List Dual} {result : Dual},
        scheme.ValueFlowInst args result →
        scheme.ValueFlowInst
          (args.map (Dual.applySubst S)) (result.applySubst S))
    (constructorInstances : signature.PatternCtorInstCompositionAdm S)
    {sourceContext targetContext : Context}
    {parameters : PatternCtx} {bindings : MonoCtx} {pattern : Pattern}
    {capability : Cap} {target : Ty} {resultBindings : MonoCtx}
    (contextFlow : Context.FlowsUnder S sourceContext targetContext)
    (typing : ResolvedPatternTy signature prevailing sourceContext parameters
      bindings pattern capability target resultBindings) :
    ResolvedPatternTy signature (Subst.seq S prevailing) targetContext
      (parameters.applySubst S) (bindings.applySubst S) pattern
      (capability.apply S.cap) (S.apply target)
      (resultBindings.applySubst S) :=
  .ofTerminal
    (TerminalPatternResolution.transportUnderPost postVariable expressionFlow
      patternFunctionFlow constructorInstances contextFlow typing.terminal)

/-! ## Occurrence-wide source transport through flowed contexts -/

/-!
The transport proof follows the mutual induction principle of the source
judgments, so every recursive premise is recognized directly from its typing
derivation.
-/

mutual

/-- Transport an expression derivation through an aligned value-flow context. -/
theorem HasTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {expression : Expr} {source : Ty}
    (typing : HasTy signature sourceContext expression source) :
    ∀ {S : Subst} {targetContext : Context}
      (_postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      HasTy signature targetContext expression (S.apply source) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .var lookup instanceTyping => by
      rcases contextFlow.find? lookup with
        ⟨targetScheme, targetLookup, schemeFlow⟩
      exact HasTy.var targetLookup
        (schemeFlow postVariable (by intros; rfl) (by intros; rfl)
          instanceTyping)
  | @HasTy.lam _ context name body domain codomain bodyTyping => by
      simpa only [Subst.apply_fn] using HasTy.lam
        (bodyTyping.transportFlows basic postVariable capFixed targetFixed
          (contextFlow.consMono _ _))
  | .app functionTyping argumentTyping => by
      exact HasTy.app
        (functionTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (argumentTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
  | @HasTy.letE _ context name value body valueTy bodyTy valueTyping
      bodyTyping => by
      let localPost := LocalFreshening.localPost signature context
        targetContext valueTy postVariable
      have localVariable : VariablePost localPost :=
        LocalFreshening.localPost_variable postVariable
      have localCapFixed : ∀ varId, varId ∈ signature.fcv →
          localPost.cap varId = .var varId := by
        intro varId membership
        rw [LocalFreshening.localPost_cap_agrees_signature
          postVariable membership, capFixed varId membership]
      have localTargetFixed : ∀ varId, varId ∈ signature.ftv →
          localPost.target varId = .var varId := by
        intro varId membership
        rw [LocalFreshening.localPost_target_agrees_signature
          postVariable membership, targetFixed varId membership]
      have valueMoved := valueTyping.transportFlows basic localVariable
        localCapFixed localTargetFixed
        (contextFlow.reindexLocal postVariable)
      have bodyMoved := bodyTyping.transportFlows basic postVariable capFixed
        targetFixed (contextFlow.consGeneralizedFresh postVariable name)
      exact HasTy.letE valueMoved bodyMoved
  | .fixE distinct direct bodyTyping => by
      simpa only [Subst.apply_fn] using HasTy.fixE distinct direct
        (bodyTyping.transportFlows basic postVariable capFixed targetFixed
          ((contextFlow.consMono _ _).consMono _ _))
  | .lit => by simpa only [Subst.apply_int] using
      (HasTy.lit (signature := signature) (context := targetContext))
  | .tuple expressionsTyping => by
      simpa only [Subst.apply_prod] using HasTy.tuple
        (expressionsTyping.transportFlows basic postVariable capFixed
          targetFixed contextFlow)
  | .ctor lookup instanceTyping expressionsTyping => by
      exact HasTy.ctor lookup
        (CtorScheme.Inst.transport instanceTyping
          ((signature.dataCtorInstCompositionAdm_of_free_fixed
            capFixed targetFixed) lookup))
        (expressionsTyping.transportFlows basic postVariable capFixed
          targetFixed contextFlow)
  | .prim lookup instanceTyping expressionsTyping => by
      exact HasTy.prim lookup
        (CtorScheme.Inst.transport instanceTyping
          ((signature.primitiveInstCompositionAdm_of_free_fixed
            capFixed targetFixed) lookup))
        (expressionsTyping.transportFlows basic postVariable capFixed
          targetFixed contextFlow)
  | .something => by simpa only [Subst.apply_matcher, Cap.apply] using
      (HasTy.something (signature := signature) (context := targetContext)
        (target := S.apply _))
  | .matchAll targetTyping patternTyping matcherTyping bodyTyping => by
      exact HasTy.matchAll
        (targetTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (patternTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (matcherTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (bodyTyping.transportFlows basic postVariable capFixed targetFixed
          (contextFlow.prependMono _))
  | .matcher clausesTyping shape catchAll exhaustive ppNodup armNodup
      coverage => by
      have clausesMoved := clausesTyping.transportFlows basic postVariable
        capFixed targetFixed contextFlow
      have shapeMoved := Shape.inferShape_applyRen_of_success
        postVariable.capRen signature.observability shape
      rw [← postVariable.applyCap_eq_applyRen] at shapeMoved
      have coverageMoved := coverage.applyRen postVariable.capRen
      rw [← postVariable.applyCap_eq_applyRen] at coverageMoved
      simpa only [Subst.apply_matcher] using HasTy.matcher clausesMoved
        shapeMoved catchAll (exhaustive.transport_basic basic) ppNodup armNodup
        coverageMoved
  | @HasTy.coerceMatcherToSlot _ context expression producerCap producerTarget
      consumerCap consumerTarget bindings C T post premise certificate
      premiseVariable => by
      have premiseMoved := premise.transportFlows basic postVariable capFixed
        targetFixed contextFlow
      have premiseFor : HasTy signature targetContext expression
          (.matcher ((producerCap.apply C).apply (Subst.seq S post).cap)
            ((Subst.seq S post).apply ((Subst.mk C T).apply producerTarget))) := by
        simpa only [Subst.apply_matcher, Cap.apply_substSeq,
          Subst.seq_apply] using premiseMoved
      have result := HasTy.coerceMatcherToSlot
        (post := Subst.seq S post) premiseFor certificate
        (postVariable.seq premiseVariable)
      simpa only [Subst.apply_matcher, Subst.apply_slot,
        Cap.apply_substSeq, Subst.seq_apply] using result
  | @HasTy.checkSlotToSlot _ context expression sourceCap sourceTarget
      requestedCap requestedTarget C T post premise certificate
      premiseVariable => by
      have premiseMoved := premise.transportFlows basic postVariable capFixed
        targetFixed contextFlow
      have premiseFor : HasTy signature targetContext expression
          (.slot ((sourceCap.apply C).apply (Subst.seq S post).cap)
            ((Subst.seq S post).apply ((Subst.mk C T).apply sourceTarget))) := by
        simpa only [Subst.apply_slot, Cap.apply_substSeq,
          Subst.seq_apply] using premiseMoved
      have result := HasTy.checkSlotToSlot
        (post := Subst.seq S post) premiseFor certificate
        (postVariable.seq premiseVariable)
      simpa only [Subst.apply_slot, Cap.apply_substSeq,
        Subst.seq_apply] using result
  | @HasTy.coerceProductMatcher _ context expression duals expressionTyping => by
      have expressionMoved := expressionTyping.transportFlows basic
        postVariable capFixed targetFixed contextFlow
      have result := HasTy.coerceProductMatcher
        (duals := duals.map (Dual.applySubst S)) (by
          simpa [List.map_map, Function.comp_def, Dual.applySubst, Dual.apply]
            using expressionMoved)
      simpa only [Subst.apply_matcher, Subst.apply_prod, Cap.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using result
  | @HasTy.coerceSlotTuple _ context expression duals expressionTyping => by
      have expressionMoved := expressionTyping.transportFlows basic
        postVariable capFixed targetFixed contextFlow
      have result := HasTy.coerceSlotTuple
        (duals := duals.map (Dual.applySubst S)) (by
          simpa [List.map_map, Function.comp_def, Dual.applySubst, Dual.apply]
            using expressionMoved)
      simpa only [Subst.apply_slot, Subst.apply_prod, Cap.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using result

termination_by structural typing

/-- List form of `HasTy.transportFlows`. -/
theorem ExprsTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {expressions : List Expr} {sources : List Ty}
    (typing : ExprsTy signature sourceContext expressions sources) :
    ∀ {S : Subst} {targetContext : Context}
      (_postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ExprsTy signature targetContext expressions (sources.map S.apply) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .nil => by
      exact .nil
  | .cons head tail => by
      simpa only [List.map_cons] using ExprsTy.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Resolve raw pattern typing while transporting its expression leaves. -/
theorem PatternTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {source : Ty} {resultBindings : MonoCtx}
    (typing : PatternTy signature sourceContext parameters bindings pattern
      capability source resultBindings) :
    ∀ {S : Subst} {targetContext : Context}
      (_postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolution signature S targetContext
        (parameters.applySubst S) (bindings.applySubst S) pattern
        (capability.apply S.cap) (S.apply source)
        (resultBindings.applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .pvar missing freshCap freshTy => by
      exact .pvar (actualContext := targetContext) missing freshCap freshTy
  | .wild freshCap freshTy => by
      exact .wild (actualContext := targetContext) freshCap freshTy
  | .pval expressionTyping freshCap separate => by
      exact .pval (actualContext := targetContext) freshCap separate
        (expressionTyping.transportFlows basic postVariable capFixed targetFixed
          (contextFlow.prependMono bindings))
  | .embed lookup => by
      exact .embed (rawContext := sourceContext)
        (actualContext := targetContext) lookup (by
        rw [PatternCtx.find?_applySubst, lookup]
        rfl)
  | .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using TerminalPatternResolution.tuple
          (children.transportFlows basic postVariable capFixed targetFixed
            contextFlow)
  | @PatternTy.ctor _ _ _ _ _ _ _ _ _ result lookup children compatible
      instanceTyping => by
      have renamedCompatible := compatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      exact TerminalPatternResolution.ctor (result := result.applySubst S) lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (by simpa only [Dual.map_cap_applySubst, Dual.cap_applySubst] using
          renamedCompatible)
        (by
          have moved := CtorScheme.Inst.transport instanceTyping
            ((signature.patternCtorInstCompositionAdm_of_free_fixed
              capFixed targetFixed) lookup)
          simpa only [PatternCtorScheme.Inst,
            Dual.map_target_applySubst, Dual.target_applySubst] using moved)
  | .and left right => by
      exact TerminalPatternResolution.and
        (left.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (right.transportFlows basic postVariable capFixed targetFixed contextFlow)
  | .or left right => by
      exact TerminalPatternResolution.or
        (left.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (right.transportFlows basic postVariable capFixed targetFixed contextFlow)
  | .app lookup children instanceTyping => by
      have instanceMoved := instanceTyping.transport
        (fun varId membership => capFixed varId
          (signature.patternFun_fcv_mem lookup membership))
        (fun varId membership => targetFixed varId
          (signature.patternFun_ftv_mem lookup membership))
        postVariable.capVariable
      exact TerminalPatternResolution.app lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        instanceMoved

termination_by structural typing

/-- List form of `PatternTy.transportFlows`. -/
theorem PatternTys.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {patterns : List Pattern} {duals : List Dual}
    {resultBindings : MonoCtx}
    (typing : PatternTys signature sourceContext parameters bindings patterns
      duals resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolutions signature S targetContext
        (parameters.applySubst S) (bindings.applySubst S) patterns
        (duals.map (Dual.applySubst S))
        (resultBindings.applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .nil => by
      exact .nil
  | .cons head tail => by
      simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
        TerminalPatternResolutions.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Append a post to an aligned raw pattern resolution. -/
theorem PatternResolution.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {rawContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {source : Ty} {resultBindings : MonoCtx}
    (typing : PatternResolution signature prevailing rawContext parameters
      bindings pattern capability source resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S (rawContext.applySubst prevailing) targetContext →
      TerminalPatternResolution signature (Subst.seq S prevailing)
        targetContext
        ((parameters.applySubst prevailing).applySubst S)
        ((bindings.applySubst prevailing).applySubst S) pattern
        ((capability.apply prevailing.cap).apply S.cap)
        (S.apply (prevailing.apply source))
        ((resultBindings.applySubst prevailing).applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .identity equality rawTyping => by
      subst prevailing
      simpa [Subst.apply_id] using rawTyping.transportFlows basic postVariable
        capFixed targetFixed (by simpa using contextFlow)
  | .pvar missing freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.pvar
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) missing freshCap freshTy)
  | .wild freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.wild
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) freshCap freshTy)
  | @PatternResolution.pval _ prevailing context parameters bindings expression
      target capVar rawTyping freshCap separate actualTyping => by
      have moved := actualTyping.transportFlows basic postVariable capFixed
        targetFixed (contextFlow.prependMono (bindings.applySubst prevailing))
      have resolved := TerminalPatternResolution.pval
        (prevailing := Subst.seq S prevailing)
        (actualContext := targetContext) freshCap separate (by
          simpa only [MonoCtx.applySubst_seq, Subst.seq_apply] using moved)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | @PatternResolution.embed _ prevailing context parameters bindings name dual
      rawLookup actualLookup => by
      have nextLookup :
          ((parameters.applySubst prevailing).applySubst S).find? name =
            some ((dual.applySubst prevailing).applySubst S) := by
        rw [PatternCtx.find?_applySubst, actualLookup]
        rfl
      have resolved := TerminalPatternResolution.embed
        (signature := signature) (prevailing := Subst.seq S prevailing)
        (rawContext := rawContext) (rawParameters := parameters)
        (rawBindings := bindings) (actualContext := targetContext)
        rawLookup (by simpa only [PatternCtx.applySubst_seq,
          Dual.applySubst_seq] using nextLookup)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using TerminalPatternResolution.tuple
          (children.transportFlows basic postVariable capFixed targetFixed
            contextFlow)
  | @PatternResolution.ctor _ _ _ _ _ _ _ _ _ _ result lookup children
      rawCompatible rawInstance actualCompatible actualInstance => by
      have renamedCompatible := actualCompatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      exact TerminalPatternResolution.ctor
        (result := (result.applySubst prevailing).applySubst S) lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (by simpa only [Dual.map_applySubst_seq, Dual.map_cap_applySubst,
            Dual.cap_applySubst] using renamedCompatible)
        (by
          have moved := CtorScheme.Inst.transport actualInstance
            ((signature.patternCtorInstCompositionAdm_of_free_fixed
              capFixed targetFixed) lookup)
          simpa only [PatternCtorScheme.Inst, Dual.map_applySubst_seq,
            Dual.map_target_applySubst, Dual.target_applySubst] using moved)
  | .and left right => by
      apply TerminalPatternResolution.and
      · exact left.transportFlows basic postVariable capFixed targetFixed
          contextFlow
      · exact right.transportFlows basic postVariable capFixed targetFixed
          contextFlow
  | .or left right => by
      apply TerminalPatternResolution.or
      · exact left.transportFlows basic postVariable capFixed targetFixed
          contextFlow
      · exact right.transportFlows basic postVariable capFixed targetFixed
          contextFlow
  | .app lookup children rawInstance actualInstance => by
      have instanceMoved := actualInstance.transport
        (fun varId membership => capFixed varId
          (signature.patternFun_fcv_mem lookup membership))
        (fun varId membership => targetFixed varId
          (signature.patternFun_ftv_mem lookup membership))
        postVariable.capVariable
      exact TerminalPatternResolution.app lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (by simpa only [Dual.map_applySubst_seq, Dual.applySubst_seq] using
          instanceMoved)

termination_by structural typing

/-- List form of `PatternResolution.transportFlows`. -/
theorem PatternResolutions.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {rawContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {patterns : List Pattern} {duals : List Dual}
    {resultBindings : MonoCtx}
    (typing : PatternResolutions signature prevailing rawContext parameters
      bindings patterns duals resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S (rawContext.applySubst prevailing) targetContext →
      TerminalPatternResolutions signature (Subst.seq S prevailing)
        targetContext
        ((parameters.applySubst prevailing).applySubst S)
        ((bindings.applySubst prevailing).applySubst S) patterns
        ((duals.map (Dual.applySubst prevailing)).map (Dual.applySubst S))
        ((resultBindings.applySubst prevailing).applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .identity equality rawTyping => by
      subst prevailing
      simpa [Subst.apply_id, Dual.applySubst_id] using
        rawTyping.transportFlows basic postVariable capFixed targetFixed
          (by simpa using contextFlow)
  | .nil => by
      exact .nil
  | .cons head tail => by
      simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
        TerminalPatternResolutions.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Transport a terminal pattern resolution and its expression leaves. -/
theorem TerminalPatternResolution.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {sourceContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {source : Ty} {resultBindings : MonoCtx}
    (typing : TerminalPatternResolution signature prevailing sourceContext
      parameters bindings pattern capability source resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolution signature (Subst.seq S prevailing)
        targetContext (parameters.applySubst S) (bindings.applySubst S)
        pattern (capability.apply S.cap) (S.apply source)
        (resultBindings.applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .pvar missing freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.pvar
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) missing freshCap freshTy)
  | .wild freshCap freshTy => by
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using
        (TerminalPatternResolution.wild
          (prevailing := Subst.seq S prevailing)
          (actualContext := targetContext) freshCap freshTy)
  | @TerminalPatternResolution.pval _ prevailing rawContext rawParameters
      rawBindings expression rawTarget capVar actualContext freshCap separate
      expressionTyping => by
      have moved := expressionTyping.transportFlows basic postVariable capFixed
        targetFixed
        (contextFlow.prependMono (rawBindings.applySubst prevailing))
      have resolved := TerminalPatternResolution.pval
        (prevailing := Subst.seq S prevailing)
        (actualContext := targetContext) freshCap separate (by
          simpa only [MonoCtx.applySubst_seq, Subst.seq_apply] using moved)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | @TerminalPatternResolution.embed _ prevailing rawContext rawParameters
      rawBindings name dual actualContext rawLookup actualLookup => by
      have nextLookup :
          ((rawParameters.applySubst prevailing).applySubst S).find? name =
            some ((dual.applySubst prevailing).applySubst S) := by
        rw [PatternCtx.find?_applySubst, actualLookup]
        rfl
      have resolved := TerminalPatternResolution.embed
        (signature := signature) (prevailing := Subst.seq S prevailing)
        (rawContext := rawContext) (rawParameters := rawParameters)
        (rawBindings := rawBindings) (actualContext := targetContext)
        rawLookup (by simpa only [PatternCtx.applySubst_seq,
          Dual.applySubst_seq] using nextLookup)
      simpa only [PatternCtx.applySubst_seq, MonoCtx.applySubst_seq,
        Cap.apply_substSeq, Subst.seq_apply] using resolved
  | .tuple children => by
      simpa only [Cap.apply_prod, Subst.apply_prod,
        Dual.map_cap_applySubst, Cap.applyList_eq_map,
        Dual.map_target_applySubst] using TerminalPatternResolution.tuple
          (children.transportFlows basic postVariable capFixed targetFixed
            contextFlow)
  | @TerminalPatternResolution.ctor _ _ _ _ _ _ _ _ _ _ result lookup
      children compatible instanceTyping => by
      have renamedCompatible := compatible.applyRen postVariable.capRen
      rw [← postVariable.applyCapList_eq_applyRenList,
        ← postVariable.applyCap_eq_applyRen] at renamedCompatible
      exact TerminalPatternResolution.ctor (result := result.applySubst S) lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        (by simpa only [Dual.map_cap_applySubst, Dual.cap_applySubst] using
          renamedCompatible)
        (by
          have moved := CtorScheme.Inst.transport instanceTyping
            ((signature.patternCtorInstCompositionAdm_of_free_fixed
              capFixed targetFixed) lookup)
          simpa only [PatternCtorScheme.Inst,
            Dual.map_target_applySubst, Dual.target_applySubst] using moved)
  | .and left right => by
      apply TerminalPatternResolution.and
      · exact left.transportFlows basic postVariable capFixed targetFixed
          contextFlow
      · exact right.transportFlows basic postVariable capFixed targetFixed
          contextFlow
  | .or left right => by
      apply TerminalPatternResolution.or
      · exact left.transportFlows basic postVariable capFixed targetFixed
          contextFlow
      · exact right.transportFlows basic postVariable capFixed targetFixed
          contextFlow
  | .app lookup children instanceTyping => by
      have instanceMoved := instanceTyping.transport
        (fun varId membership => capFixed varId
          (signature.patternFun_fcv_mem lookup membership))
        (fun varId membership => targetFixed varId
          (signature.patternFun_ftv_mem lookup membership))
        postVariable.capVariable
      exact TerminalPatternResolution.app lookup
        (children.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
        instanceMoved

termination_by structural typing

/-- List form of `TerminalPatternResolution.transportFlows`. -/
theorem TerminalPatternResolutions.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {sourceContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {patterns : List Pattern} {duals : List Dual}
    {resultBindings : MonoCtx}
    (typing : TerminalPatternResolutions signature prevailing sourceContext
      parameters bindings patterns duals resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      TerminalPatternResolutions signature (Subst.seq S prevailing)
        targetContext (parameters.applySubst S) (bindings.applySubst S)
        patterns (duals.map (Dual.applySubst S))
        (resultBindings.applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .nil => by
      exact .nil
  | .cons head tail => by
      simpa only [List.map_cons, Dual.applySubst, Dual.apply] using
        TerminalPatternResolutions.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Transport either packaging of a resolved user pattern. -/
theorem ResolvedPatternTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {sourceContext : Context} {parameters : PatternCtx}
    {bindings : MonoCtx} {pattern : Pattern} {capability : Cap}
    {source : Ty} {resultBindings : MonoCtx}
    (typing : ResolvedPatternTy signature prevailing sourceContext parameters
      bindings pattern capability source resultBindings) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ResolvedPatternTy signature (Subst.seq S prevailing) targetContext
        (parameters.applySubst S) (bindings.applySubst S) pattern
        (capability.apply S.cap) (S.apply source)
        (resultBindings.applySubst S) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | .ofAligned resolution => by
      exact .ofTerminal
        (resolution.transportFlows basic postVariable capFixed targetFixed
          contextFlow)
  | .ofTerminal resolution => by
      exact .ofTerminal
        (resolution.transportFlows basic postVariable capFixed targetFixed
          contextFlow)

termination_by structural typing

/-- Transport one matcher arm. -/
theorem ArmTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {source : Ty} {ppBindings : MonoCtx}
    {result : Ty} {arm : Arm}
    (typing : ArmTy signature sourceContext source ppBindings result arm) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ArmTy signature targetContext (S.apply source)
        (ppBindings.applySubst S) (S.apply result) arm := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | @ArmTy.mk _ context target ppBindings result pattern body armBindings
      patternTyping bodyTyping => by
      have extendedFlow : Context.FlowsUnder S
          (armBindings.toContext ++ ppBindings.toContext ++ context)
          ((armBindings.applySubst S).toContext ++
            (ppBindings.applySubst S).toContext ++ targetContext) := by
        simpa only [List.append_assoc] using
          ((contextFlow.prependMono ppBindings).prependMono armBindings)
      have bodyMoved := bodyTyping.transportFlows basic postVariable capFixed
        targetFixed extendedFlow
      exact ArmTy.mk
        (patternTyping.transport
          (signature.dataCtorInstCompositionAdm_of_free_fixed
            capFixed targetFixed))
        (by simpa only [List.append_assoc] using bodyMoved)

termination_by structural typing

/-- List form of `ArmTy.transportFlows`. -/
theorem ArmsTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {source : Ty} {ppBindings : MonoCtx}
    {result : Ty} {arms : List Arm}
    (typing : ArmsTy signature sourceContext source ppBindings result arms) :
    ∀ {S : Subst} {targetContext : Context},
      VariablePost S →
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ArmsTy signature targetContext (S.apply source)
        (ppBindings.applySubst S) (S.apply result) arms := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | @ArmsTy.nil _ context target ppBindings result => by
      exact .nil
  | @ArmsTy.cons _ context target ppBindings result arm arms head tail => by
      exact ArmsTy.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Transport one resolved matcher clause and its concrete shape evidence. -/
theorem ClauseTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {sourceContext : Context} {clause : Clause}
    {capability : Cap} {source : Ty} {evidence : Shape.Evidence}
    (typing : ClauseTy signature prevailing sourceContext clause capability
      source evidence) :
    ∀ {S : Subst} {targetContext : Context}
      (postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ClauseTy signature (Subst.seq S prevailing) targetContext clause
        (capability.apply S.cap) (S.apply source)
        (evidence.applyRen postVariable.capRen) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | @ClauseTy.mk _ prevailing context capability target pp next arms holes
      ppBindings nextMatchers evidence orderTyping ppTyping capsTyping decomposition
      nextTyping armsTyping evidenceTyping => by
      have ppMoved := ResolvedPPatTy.transport
        (signature.patternCtorInstCompositionAdm_of_free_fixed
          capFixed targetFixed) ppTyping
      have capsMoved := capsTyping.transport postVariable
      have nextMoved := nextTyping.transportFlows basic postVariable capFixed
        targetFixed contextFlow
      have armsMoved := armsTyping.transportFlows basic postVariable capFixed
        targetFixed contextFlow
      have evidenceMoved := clauseEvidence_applyRen_of_success
        postVariable.capRen evidenceTyping
      rw [← postVariable.applyCapList_eq_applyRenList] at evidenceMoved
      apply ClauseTy.mk orderTyping ppMoved
      · simpa only [Dual.map_cap_applySubst, Cap.applyList_eq_map] using capsMoved
      · simpa using decomposition
      · simpa only [Dual.map_slot_applySubst] using nextMoved
      · simpa only [Subst.apply_listT, Subst.apply_prodTy,
          Dual.map_target_applySubst] using armsMoved
      · simpa only [Dual.map_cap_applySubst, Cap.applyList_eq_map] using
          evidenceMoved

termination_by structural typing

/-- List form of `ClauseTy.transportFlows`. -/
theorem ClausesTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {prevailing : Subst} {sourceContext : Context} {clauses : List Clause}
    {capability : Cap} {source : Ty} {evidence : List Shape.Evidence}
    (typing : ClausesTy signature prevailing sourceContext clauses capability
      source evidence) :
    ∀ {S : Subst} {targetContext : Context}
      (postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ClausesTy signature (Subst.seq S prevailing) targetContext clauses
        (capability.apply S.cap) (S.apply source)
        (Shape.Evidence.applyRenList postVariable.capRen evidence) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | @ClausesTy.nil _ prevailing capability context target => by
      exact .nil
  | @ClausesTy.cons _ prevailing capability context clause clauses target evidence
      evidences head tail => by
      simpa only [Shape.Evidence.applyRenList] using ClausesTy.cons
        (head.transportFlows basic postVariable capFixed targetFixed contextFlow)
        (tail.transportFlows basic postVariable capFixed targetFixed contextFlow)

termination_by structural typing

/-- Transport the shared-substitution package for matcher clauses. -/
theorem ResolvedClausesTy.transportFlows
    {signature : FrozenSig}
    (basic : signature.armExhaustive = basicArmExhaustive)
    {sourceContext : Context} {clauses : List Clause}
    {capability : Cap} {source : Ty} {evidence : List Shape.Evidence}
    (typing : ResolvedClausesTy signature sourceContext clauses capability
      source evidence) :
    ∀ {S : Subst} {targetContext : Context}
      (postVariable : VariablePost S),
      (∀ varId, varId ∈ signature.fcv → S.cap varId = .var varId) →
      (∀ varId, varId ∈ signature.ftv → S.target varId = .var varId) →
      Context.FlowsUnder S sourceContext targetContext →
      ResolvedClausesTy signature targetContext clauses
        (capability.apply S.cap) (S.apply source)
        (Shape.Evidence.applyRenList postVariable.capRen evidence) := by
  intro S targetContext postVariable capFixed targetFixed contextFlow
  exact match typing with
  | @ResolvedClausesTy.ofShared _ prevailing context clauses capability target
      evidence clausesTyping => by
      exact ResolvedClausesTy.ofShared
        (clausesTyping.transportFlows basic postVariable capFixed targetFixed
          contextFlow)

termination_by structural typing

end

set_option maxHeartbeats 200000


/-- The exact source-level conclusion needed by let-bound runtime values. -/
def HasTy.GeneralizedValueFlow
    {signature : FrozenSig} {context : Context}
    {expression : Expr} {source : Ty}
    (_typing : HasTy signature context expression source) : Prop :=
  ∀ {target : Ty},
    (signature.generalize context source).ValueFlowInst target →
    HasTy signature context expression target

/-- Replay any binder-local instance of a generalized value derivation. -/
theorem HasTy.generalizedValueFlow
    {signature : FrozenSig} {context : Context}
    {expression : Expr} {source : Ty}
    (typing : HasTy signature context expression source)
    (basic : signature.armExhaustive = basicArmExhaustive) :
    typing.GeneralizedValueFlow := by
  intro target requested
  rcases requested with ⟨C, T, instanceTyping⟩
  let S := Subst.mk C T
  have postVariable : VariablePost S := by
    exact ⟨instanceTyping.capVariable⟩
  have capFixedEnvironment : ∀ varId,
      varId ∈ signature.fcv ++ context.fcv →
        S.cap varId = .var varId := by
    intro varId membership
    apply instanceTyping.capSupport varId
    intro binder
    exact (mem_generalize_capBinders_not_env binder) membership
  have targetFixedEnvironment : ∀ varId,
      varId ∈ signature.ftv ++ context.ftv →
        S.target varId = .var varId := by
    intro varId membership
    apply instanceTyping.tySupport varId
    intro binder
    exact (mem_generalize_tyBinders_not_env binder) membership
  have contextFlow : Context.FlowsUnder S context context :=
    Context.self_flowsUnder context
      (fun varId membership => capFixedEnvironment varId
        (List.mem_append_right _ membership))
      (fun varId membership => targetFixedEnvironment varId
        (List.mem_append_right _ membership))
  have moved := typing.transportFlows basic postVariable
    (fun varId membership => capFixedEnvironment varId
      (List.mem_append_left _ membership))
    (fun varId membership => targetFixedEnvironment varId
      (List.mem_append_left _ membership))
    contextFlow
  have resultEquation : S.apply source = target := instanceTyping.result
  rw [resultEquation] at moved
  exact moved

/-- Two entries with the same key coincide in a key-noduplicate table. -/
theorem pair_eq_of_key_nodup
    {β : Type} {entries : List (String × β)}
    (namesNodup : (entries.map Prod.fst).Nodup)
    {left right : String × β}
    (leftMem : left ∈ entries) (rightMem : right ∈ entries)
    (keys : left.1 = right.1) : left = right := by
  induction entries generalizing left right with
  | nil => simp at leftMem
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headMissing, tailNodup⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftTail
      · rcases rightMem with rfl | rightTail
        · rfl
        · exfalso
          apply headMissing
          exact List.mem_map.mpr ⟨right, rightTail, keys.symm⟩
      · rcases rightMem with rfl | rightTail
        · exfalso
          apply headMissing
          exact List.mem_map.mpr ⟨left, leftTail, keys⟩
        · exact induction tailNodup leftTail rightTail keys

/-- Recover the concrete table entry selected by pattern-function lookup. -/
theorem FrozenSig.findPatternFun_entry
    {signature : FrozenSig} {name : String} {scheme : DualScheme}
    (lookup : signature.findPatternFun name = some scheme) :
    ∃ entry, entry ∈ signature.patternFuns ∧
      entry.1 = name ∧ entry.2 = scheme := by
  rcases Option.map_eq_some_iff.mp lookup with ⟨entry, found, result⟩
  have selected := List.find?_some found
  have membership : entry ∈ signature.patternFuns := by
    rcases (List.find?_eq_some_iff_append.mp found).2 with
      ⟨pre, suf, equation, _⟩
    rw [equation]
    simp
  exact ⟨entry, membership, by simpa using selected, result⟩

/-- Every free capability of a dual generalization comes from its environment. -/
theorem FrozenSig.generalizeDual_fcv_mem_environment
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) {varId : CapVar}
    (membership :
      varId ∈ (signature.generalizeDual context args result).fcv) :
    varId ∈ signature.fcv ++ context.fcv := by
  by_cases outside : varId ∈ signature.fcv ++ context.fcv
  · exact outside
  · exfalso
    have parts := List.mem_filter.mp membership
    have binder : varId ∈
        (signature.generalizeDual context args result).capBinders := by
      change varId ∈ uniqueVars
        ((args.flatMap Dual.fcv ++ result.fcv).filter fun candidate =>
          candidate ∉ signature.fcv ++ context.fcv)
      exact mem_uniqueVars.mpr
        (List.mem_filter.mpr ⟨parts.1, by simp [outside]⟩)
    exact (of_decide_eq_true parts.2) binder

/-- Every free target variable of a dual generalization comes from its environment. -/
theorem FrozenSig.generalizeDual_ftv_mem_environment
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) {varId : TypePM.TyVar}
    (membership :
      varId ∈ (signature.generalizeDual context args result).ftv) :
    varId ∈ signature.ftv ++ context.ftv := by
  by_cases outside : varId ∈ signature.ftv ++ context.ftv
  · exact outside
  · exfalso
    have parts := List.mem_filter.mp membership
    have binder : varId ∈
        (signature.generalizeDual context args result).tyBinders := by
      change varId ∈ uniqueVars
        ((args.flatMap Dual.ftv ++ result.ftv).filter fun candidate =>
          candidate ∉ signature.ftv ++ context.ftv)
      exact mem_uniqueVars.mpr
        (List.mem_filter.mpr ⟨parts.1, by simp [outside]⟩)
    exact (of_decide_eq_true parts.2) binder

/-- A generalized dual capability binder is disjoint from its environment. -/
theorem FrozenSig.mem_generalizeDual_capBinders_not_environment
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) {varId : CapVar}
    (membership :
      varId ∈ (signature.generalizeDual context args result).capBinders) :
    varId ∉ signature.fcv ++ context.fcv := by
  change varId ∈ uniqueVars
    ((args.flatMap Dual.fcv ++ result.fcv).filter fun candidate =>
      candidate ∉ signature.fcv ++ context.fcv) at membership
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp membership)).2

/-- A generalized dual target binder is disjoint from its environment. -/
theorem FrozenSig.mem_generalizeDual_tyBinders_not_environment
    (signature : FrozenSig) (context : Context)
    (args : List Dual) (result : Dual) {varId : TypePM.TyVar}
    (membership :
      varId ∈ (signature.generalizeDual context args result).tyBinders) :
    varId ∉ signature.ftv ++ context.ftv := by
  change varId ∈ uniqueVars
    ((args.flatMap Dual.ftv ++ result.ftv).filter fun candidate =>
      candidate ∉ signature.ftv ++ context.ftv) at membership
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp membership)).2

/-- Substitution commutes with the ordered pattern-parameter context. -/
theorem patternParameterContext_applySubst
    (parameters : List (String × Ty)) (capabilities : List Cap)
    (S : Subst) (lengths : parameters.length = capabilities.length) :
    (patternParameterContext parameters capabilities).applySubst S =
      (parameters.map Prod.fst).zip
        ((patternParameterDuals parameters capabilities).map
          (Dual.applySubst S)) := by
  induction parameters generalizing capabilities with
  | nil =>
      cases capabilities with
      | nil => rfl
      | cons capability capabilities => simp at lengths
  | cons parameter parameters induction =>
      cases capabilities with
      | nil => simp at lengths
      | cons capability capabilities =>
          simp only [List.length_cons, Nat.succ.injEq] at lengths
          change
            (parameter.1,
                (Dual.mk capability parameter.2).applySubst S) ::
                (patternParameterContext parameters capabilities).applySubst S =
              (parameter.1,
                (Dual.mk capability parameter.2).applySubst S) ::
                (parameters.map Prod.fst).zip
                  ((patternParameterDuals parameters capabilities).map
                    (Dual.applySubst S))
          rw [induction capabilities lengths]

/-- A full-signature capability free remains ambient after self filtering. -/
theorem FrozenSig.fcv_mem_filtered_or_context
    (signature : FrozenSig) (context : Context) (removed : String)
    (scheme : DualScheme) (args : List Dual) (result : Dual)
    (namesNodup : (signature.patternFuns.map Prod.fst).Nodup)
    (lookup : signature.findPatternFun removed = some scheme)
    (schemeFreeCaps : scheme.fcv =
      (({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed }).generalizeDual
        context args result).fcv)
    {varId : CapVar} (membership : varId ∈ signature.fcv) :
    varId ∈
        ({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed }).fcv ++ context.fcv := by
  simp only [FrozenSig.fcv, List.mem_append] at membership
  rcases membership with ((dataMember | ctorMember) | funMember) | primMember
  · apply List.mem_append_left
    simp only [FrozenSig.fcv, List.mem_append]
    exact Or.inl (Or.inl (Or.inl dataMember))
  · apply List.mem_append_left
    simp only [FrozenSig.fcv, List.mem_append]
    exact Or.inl (Or.inl (Or.inr ctorMember))
  · rcases List.mem_flatMap.mp funMember with
      ⟨entry, entryMember, variableMember⟩
    by_cases removedEntry : entry.1 = removed
    · obtain ⟨selected, selectedMember, selectedName, selectedScheme⟩ :=
        signature.findPatternFun_entry lookup
      have entryEquality : entry = selected :=
        pair_eq_of_key_nodup namesNodup entryMember selectedMember
          (removedEntry.trans selectedName.symm)
      have entryScheme : entry.2 = scheme := by
        rw [entryEquality, selectedScheme]
      rw [entryScheme, schemeFreeCaps] at variableMember
      exact FrozenSig.generalizeDual_fcv_mem_environment
        ({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed })
        context args result variableMember
    · apply List.mem_append_left
      simp only [FrozenSig.fcv, List.mem_append]
      apply Or.inl
      apply Or.inr
      apply List.mem_flatMap.mpr
      exact ⟨entry, List.mem_filter.mpr ⟨entryMember, by
        simpa [bne_iff_ne] using removedEntry⟩, variableMember⟩
  · apply List.mem_append_left
    simp only [FrozenSig.fcv, List.mem_append]
    exact Or.inr primMember

/-- A full-signature target free remains ambient after self filtering. -/
theorem FrozenSig.ftv_mem_filtered_or_context
    (signature : FrozenSig) (context : Context) (removed : String)
    (scheme : DualScheme) (args : List Dual) (result : Dual)
    (namesNodup : (signature.patternFuns.map Prod.fst).Nodup)
    (lookup : signature.findPatternFun removed = some scheme)
    (schemeFreeTargets : scheme.ftv =
      (({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed }).generalizeDual
        context args result).ftv)
    {varId : TypePM.TyVar} (membership : varId ∈ signature.ftv) :
    varId ∈
        ({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed }).ftv ++ context.ftv := by
  simp only [FrozenSig.ftv, List.mem_append] at membership
  rcases membership with ((dataMember | ctorMember) | funMember) | primMember
  · apply List.mem_append_left
    simp only [FrozenSig.ftv, List.mem_append]
    exact Or.inl (Or.inl (Or.inl dataMember))
  · apply List.mem_append_left
    simp only [FrozenSig.ftv, List.mem_append]
    exact Or.inl (Or.inl (Or.inr ctorMember))
  · rcases List.mem_flatMap.mp funMember with
      ⟨entry, entryMember, variableMember⟩
    by_cases removedEntry : entry.1 = removed
    · obtain ⟨selected, selectedMember, selectedName, selectedScheme⟩ :=
        signature.findPatternFun_entry lookup
      have entryEquality : entry = selected :=
        pair_eq_of_key_nodup namesNodup entryMember selectedMember
          (removedEntry.trans selectedName.symm)
      have entryScheme : entry.2 = scheme := by
        rw [entryEquality, selectedScheme]
      rw [entryScheme, schemeFreeTargets] at variableMember
      exact FrozenSig.generalizeDual_ftv_mem_environment
        ({ signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != removed })
        context args result variableMember
    · apply List.mem_append_left
      simp only [FrozenSig.ftv, List.mem_append]
      apply Or.inl
      apply Or.inr
      apply List.mem_flatMap.mpr
      exact ⟨entry, List.mem_filter.mpr ⟨entryMember, by
        simpa [bne_iff_ne] using removedEntry⟩, variableMember⟩
  · apply List.mem_append_left
    simp only [FrozenSig.ftv, List.mem_append]
    exact Or.inr primMember

/--
The exact instantiated-body conclusion consumed by `Step.patfunEnter`.
The output binding context remains existential because checking a definition
body may introduce ordinary pattern bindings.
-/
def PatternDefTy.InstantiatedBody
    {signature : FrozenSig} {context : Context}
    {definition : PatternDef} {scheme : DualScheme}
    (_typing : PatternDefTy signature context definition scheme) : Prop :=
  ∀ {actualArgs : List Dual} {actualResult : Dual},
    scheme.ValueFlowInst actualArgs actualResult →
    ∃ prevailing bodyOutput,
      ResolvedPatternTy signature prevailing context
        (definition.parameterNames.zip actualArgs) [] definition.body
        actualResult.cap actualResult.target bodyOutput

/-- Instantiate a checked full-signature pattern-function body at any safe use. -/
theorem PatternDefTy.instantiatedBody
    {signature : FrozenSig} {context : Context}
    {definition : PatternDef} {scheme : DualScheme}
    (typing : PatternDefTy signature context definition scheme)
    (basic : signature.armExhaustive = basicArmExhaustive)
    (patternFunNamesNodup :
      (signature.patternFuns.map Prod.fst).Nodup) :
    typing.InstantiatedBody := by
  intro actualArgs actualResult requested
  cases typing with
  | @mk capabilities result resultBindings _ lookup nonrecursive
      parameterLength parameterNamesNodup freshCapabilities capabilitiesNodup
      bodyTyping linear schemeEquation =>
      let filteredSignature : FrozenSig :=
        { signature with
          patternFuns := signature.patternFuns.filter
            fun entry => entry.1 != definition.name }
      let sourceArgs :=
        patternParameterDuals definition.parameters capabilities
      have requestedLocal :
          (filteredSignature.generalizeDual context sourceArgs result).ValueFlowInst
            actualArgs actualResult := by
        exact (schemeEquation.instances actualArgs actualResult).mp requested
      rcases requestedLocal with ⟨C, T, instanceTyping⟩
      let S := Subst.mk C T
      have postVariable : VariablePost S :=
        ⟨instanceTyping.capVariable⟩
      have capFixedFilteredEnvironment : ∀ varId,
          varId ∈ filteredSignature.fcv ++ context.fcv →
            S.cap varId = .var varId := by
        intro varId membership
        apply instanceTyping.capSupport varId
        intro binder
        have binder' : varId ∈
            (filteredSignature.generalizeDual context sourceArgs result).capBinders := by
          exact binder
        exact (filteredSignature.mem_generalizeDual_capBinders_not_environment
          context sourceArgs result binder') membership
      have targetFixedFilteredEnvironment : ∀ varId,
          varId ∈ filteredSignature.ftv ++ context.ftv →
            S.target varId = .var varId := by
        intro varId membership
        apply instanceTyping.tySupport varId
        intro binder
        have binder' : varId ∈
            (filteredSignature.generalizeDual context sourceArgs result).tyBinders := by
          exact binder
        exact (filteredSignature.mem_generalizeDual_tyBinders_not_environment
          context sourceArgs result binder') membership
      have capFixedSignature : ∀ varId, varId ∈ signature.fcv →
          S.cap varId = .var varId := by
        intro varId membership
        apply capFixedFilteredEnvironment varId
        exact signature.fcv_mem_filtered_or_context context definition.name
          scheme sourceArgs result patternFunNamesNodup lookup
          schemeEquation.freeCaps membership
      have targetFixedSignature : ∀ varId, varId ∈ signature.ftv →
          S.target varId = .var varId := by
        intro varId membership
        apply targetFixedFilteredEnvironment varId
        exact signature.ftv_mem_filtered_or_context context definition.name
          scheme sourceArgs result patternFunNamesNodup lookup
          schemeEquation.freeTargets membership
      have contextFlow : Context.FlowsUnder S context context :=
        Context.self_flowsUnder context
          (fun varId membership => capFixedFilteredEnvironment varId
            (List.mem_append_right _ membership))
          (fun varId membership => targetFixedFilteredEnvironment varId
            (List.mem_append_right _ membership))
      have moved := bodyTyping.transportFlows basic postVariable
        capFixedSignature targetFixedSignature contextFlow
      have argsEquation :
          sourceArgs.map (Dual.applySubst S) = actualArgs := by
        change sourceArgs.map (Dual.apply C T) = actualArgs
        have equation := instanceTyping.argsResult
        simpa only [FrozenSig.generalizeDual, sourceArgs] using equation
      have resultEquation : result.applySubst S = actualResult := by
        change result.apply C T = actualResult
        have equation := instanceTyping.resultResult
        simpa only [FrozenSig.generalizeDual] using equation
      have parameterContextEquation :
          (patternParameterContext definition.parameters capabilities).applySubst S =
            definition.parameterNames.zip actualArgs := by
        have equation := patternParameterContext_applySubst
          definition.parameters capabilities S parameterLength
        rw [argsEquation] at equation
        simpa only [PatternDef.parameterNames] using equation
      have capabilityEquation :
          result.cap.apply S.cap = actualResult.cap := by
        simpa only [Dual.applySubst, Dual.apply] using
          congrArg Dual.cap resultEquation
      have targetEquation : S.apply result.target = actualResult.target := by
        simpa only [Dual.applySubst, Dual.apply] using
          congrArg Dual.target resultEquation
      rw [parameterContextEquation, capabilityEquation, targetEquation] at moved
      exact ⟨S, resultBindings.applySubst S, .ofTerminal moved⟩

end TypePM
