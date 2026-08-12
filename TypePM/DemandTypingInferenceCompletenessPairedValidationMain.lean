import TypePM.DemandTypingInferenceCompletenessPairedValidatorRun
import TypePM.DemandTypingInferenceCompletenessValidationMain

/-!
# Paired constructor-wise validator composition

The constructor chains in `DemandTypingInferenceCompletenessValidationMain`
compose exact validator extensions.  Global completeness instead obtains a
paired extension from every recursive child.  This module supplies the small
dependent composition layer between those two representations: exact local
prefixes, alignments, and suffixes embed into paired chronology, while child
chronology remains paired throughout.

The helpers are intentionally independent of the global recursion and its
combined run wrapper.  Callers retain the raw `BisimulationExtension`s, so the
resulting validator index is definitionally the same chronological `.seq`
chain as the corresponding raw completion.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessPairedValidationMain

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessCertifiedRun
open DemandTypingInferenceCompletenessPairedValidatorRun

/-- Embed an exact local prefix and compose it before a paired recursive run. -/
theorem prependExact
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ : Subst}
    {initial middle final : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {prefixTransition : BisimulationExtension before ledger₁ declarative₁
      middle}
    {childTransition : BisimulationExtension prefixTransition.after ledger₂
      declarative₂ final}
    (front : ValidatorRunExtension terminal signature initial middle)
    {childHistory : middle.StateExtension final}
    (child : PairedValidatorRunExtension terminal signature childTransition
      childHistory) :
    PairedValidatorRunExtension terminal signature
      (prefixTransition.seq childTransition)
      (front.ordinary.history.trans childHistory) :=
  (PairedValidatorRunExtension.ofExact prefixTransition front).trans child

/-- Embed an exact local suffix and compose it after a paired recursive run. -/
theorem appendExact
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ : Subst}
    {initial middle final : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {childTransition : BisimulationExtension before ledger₁ declarative₁
      middle}
    {suffixTransition : BisimulationExtension childTransition.after ledger₂
      declarative₂ final}
    {childHistory : initial.StateExtension middle}
    (child : PairedValidatorRunExtension terminal signature childTransition
      childHistory)
    (suffix : ValidatorRunExtension terminal signature middle final) :
    PairedValidatorRunExtension terminal signature
      (childTransition.seq suffixTransition)
      (childHistory.trans suffix.ordinary.history) :=
  child.trans (PairedValidatorRunExtension.ofExact suffixTransition suffix)

/-- Surround one paired child by exact constructor-local prefix and suffix
segments.  This is the common shape of lambda, tuple, constructor, primitive,
and matcher-independent unary constructors. -/
theorem surroundExact
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ ledger₃ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ declarative₃ : Subst}
    {initial entered childFinal final : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {prefixTransition : BisimulationExtension before ledger₁ declarative₁
      entered}
    {childTransition : BisimulationExtension prefixTransition.after ledger₂
      declarative₂ childFinal}
    {suffixTransition : BisimulationExtension childTransition.after ledger₃
      declarative₃ final}
    (front : ValidatorRunExtension terminal signature initial entered)
    {childHistory : entered.StateExtension childFinal}
    (child : PairedValidatorRunExtension terminal signature childTransition
      childHistory)
    (suffix : ValidatorRunExtension terminal signature childFinal final) :
    PairedValidatorRunExtension terminal signature
      ((prefixTransition.seq childTransition).seq suffixTransition)
      ((front.ordinary.history.trans childHistory).trans
        suffix.ordinary.history) :=
  appendExact (prependExact front child) suffix

/-- Insert one exact local stage between two paired recursive runs.  This is
the application/fix core: synthesis, exact alignment, then another paired
child (or an exact finishing suffix). -/
theorem pairedExactPaired
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ ledger₃ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ declarative₃ : Subst}
    {initial firstFinal middle secondFinal : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {firstTransition : BisimulationExtension before ledger₁ declarative₁
      firstFinal}
    {middleTransition : BisimulationExtension firstTransition.after ledger₂
      declarative₂ middle}
    {secondTransition : BisimulationExtension middleTransition.after ledger₃
      declarative₃ secondFinal}
    {firstHistory : initial.StateExtension firstFinal}
    (first : PairedValidatorRunExtension terminal signature firstTransition
      firstHistory)
    (exactMiddle : ValidatorRunExtension terminal signature firstFinal middle)
    {secondHistory : middle.StateExtension secondFinal}
    (second : PairedValidatorRunExtension terminal signature secondTransition
      secondHistory) :
    PairedValidatorRunExtension terminal signature
      ((firstTransition.seq middleTransition).seq secondTransition)
      ((firstHistory.trans exactMiddle.ordinary.history).trans secondHistory) :=
  (appendExact first exactMiddle).trans second

/-- Compose two adjacent paired child runs.  Tuple/checking lists use this
head-to-tail law without converting either child back to exact validation. -/
theorem pairedCons
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ : CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ : Subst}
    {initial middle final : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {headTransition : BisimulationExtension before ledger₁ declarative₁ middle}
    {tailTransition : BisimulationExtension headTransition.after ledger₂
      declarative₂ final}
    {headHistory : initial.StateExtension middle}
    {tailHistory : middle.StateExtension final}
    (head : PairedValidatorRunExtension terminal signature headTransition
      headHistory)
    (tail : PairedValidatorRunExtension terminal signature tailTransition
      tailHistory) :
    PairedValidatorRunExtension terminal signature
      (headTransition.seq tailTransition) (headHistory.trans tailHistory) :=
  head.trans tail

/-- Exact constructor prefix, paired first child, exact intermediate cut,
paired second child, and exact finish.  The result is deliberately
left-associated to match the raw application and `let` completion chains. -/
theorem surroundPairedExactPaired
    {terminal : Subst} {signature : FrozenSig}
    {ledger₀ ledger₁ ledger₂ ledger₃ ledger₄ ledger₅ :
      CapabilityOriginLedger}
    {declarative₀ declarative₁ declarative₂ declarative₃ declarative₄
      declarative₅ : Subst}
    {initial entered firstFinal middle secondFinal final : InferState}
    {before : StateBisimulation ledger₀ declarative₀ initial}
    {frontTransition : BisimulationExtension before ledger₁ declarative₁
      entered}
    {firstTransition : BisimulationExtension frontTransition.after ledger₂
      declarative₂ firstFinal}
    {middleTransition : BisimulationExtension firstTransition.after ledger₃
      declarative₃ middle}
    {secondTransition : BisimulationExtension middleTransition.after ledger₄
      declarative₄ secondFinal}
    {backTransition : BisimulationExtension secondTransition.after ledger₅
      declarative₅ final}
    (front : ValidatorRunExtension terminal signature initial entered)
    {firstHistory : entered.StateExtension firstFinal}
    (first : PairedValidatorRunExtension terminal signature firstTransition
      firstHistory)
    (exactMiddle : ValidatorRunExtension terminal signature firstFinal middle)
    {secondHistory : middle.StateExtension secondFinal}
    (second : PairedValidatorRunExtension terminal signature secondTransition
      secondHistory)
    (back : ValidatorRunExtension terminal signature secondFinal final) :
    PairedValidatorRunExtension terminal signature
      ((((frontTransition.seq firstTransition).seq middleTransition).seq
        secondTransition).seq backTransition)
      ((((front.ordinary.history.trans firstHistory).trans
        exactMiddle.ordinary.history).trans secondHistory).trans
        back.ordinary.history) := by
  let throughFirst := prependExact
    (prefixTransition := frontTransition) front first
  let throughMiddle := appendExact
    (childTransition := frontTransition.seq firstTransition)
    (suffixTransition := middleTransition) throughFirst exactMiddle
  let throughSecond := throughMiddle.trans second
  exact appendExact
    (childTransition := ((frontTransition.seq firstTransition).seq
      middleTransition).seq secondTransition)
    (suffixTransition := backTransition) throughSecond back

/-! Constructor-facing names.  These aliases expose the intended selection
without duplicating the dependent proofs above. -/

/-- Lambda: visit/fresh, paired body, finish. -/
abbrev synthLam := @surroundExact

/-- Tuple: visit, paired child list, finish. -/
abbrev synthTuple := @surroundExact

/-- Constructor: visit/instantiate, paired checks, freeze/finish. -/
abbrev synthCtor := @surroundExact

/-- Primitive: visit/instantiate, paired checks, freeze/finish. -/
abbrev synthPrim := @surroundExact

/-- Application: visit, paired function, alignment, paired argument, finish. -/
abbrev synthApp := @surroundPairedExactPaired

/-- Let: visit, paired value, generalization, paired body, finish. -/
abbrev synthLet := @surroundPairedExactPaired

/-- Fix uses one paired body surrounded by its exact placeholder prefix and
alignment/finish suffix. -/
abbrev synthFix := @surroundExact

/-- Adjacent paired stages in `matchAll` compose with this named step; exact
target alignment is inserted with `appendExact`. -/
abbrev synthMatchAllStep := @pairedCons

end DemandTypingInferenceCompletenessPairedValidationMain
end TypePM
