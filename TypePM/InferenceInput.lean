import TypePM.Inference

/-!
# Well-formed frozen inputs for executable inference

The public inference soundness theorem does not require a caller-supplied
input certificate. Fresh counters are computed above every free solver
metavariable in the signature and canonical expression context. Expression
schemes need no binder-name hygiene because bound occurrences are finite local
indices. This module therefore records only the remaining named-binder
conditions on frozen constructor and pattern-function schemes.
-/

namespace TypePM

/-- The two quantified binder lists of a constructor scheme are set-like. -/
def CtorScheme.BindersNodup (scheme : CtorScheme) : Prop :=
  scheme.capBinders.Nodup ∧ scheme.tyBinders.Nodup

/-- The two quantified binder lists of a dual scheme are set-like. -/
def DualScheme.BindersNodup (scheme : DualScheme) : Prop :=
  scheme.capBinders.Nodup ∧ scheme.tyBinders.Nodup

/-- Signature-aware dual generalization removes duplicate binders. -/
theorem FrozenSig.generalizeDual_bindersNodup
    (signature : FrozenSig) (context : Context)
    (arguments : List Dual) (result : Dual) :
    (signature.generalizeDual context arguments result).BindersNodup := by
  constructor <;> exact uniqueVars_nodup _

/-- Conventional static well-formedness boundary for a frozen core signature.
The public fail-closed `infer` neither consumes nor requires this structure. -/
structure FrozenSigInferenceWF (signature : FrozenSig) : Prop where
  armExhaustiveBasic : signature.armExhaustive = basicArmExhaustive
  dataCtorBinders :
    ∀ {name scheme}, signature.findDataCtor name = some scheme →
      scheme.BindersNodup
  patternCtorBinders :
    ∀ {name entry}, signature.findPatternCtor name = some entry →
      entry.scheme.BindersNodup
  patternFunBinders :
    ∀ {name scheme}, signature.findPatternFun name = some scheme →
      scheme.BindersNodup
  primitiveBinders :
    ∀ {op scheme}, signature.findPrimitive op = some scheme →
      scheme.BindersNodup

/-- Public static boundary retained for clients that validate frozen
signatures before inference. Canonical expression contexts add no premise. -/
structure InferenceInputWF
    (signature : FrozenSig) (_context : Context) : Prop where
  signature : FrozenSigInferenceWF signature

end TypePM
