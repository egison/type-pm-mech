import TypePM.DemandTypingErasure
import TypePM.DemandTypingRegression

/-!
# Public DD state-erasure regression

The flagship polymorphic-let derivation crosses the public, closed-program
`DDTyping` to `RuntimeTyping` bridge at its published `Int` type.
-/

namespace TypePM.DemandTypingRegression

theorem dmLet_runtimeTyping :
    RuntimeTyping CertifiedInferenceRegression.emptySignature [] dmLetProgram
      .int :=
  dmLet_ddTyping.runtimeTyping emptySignature_schemesClosed

end TypePM.DemandTypingRegression
