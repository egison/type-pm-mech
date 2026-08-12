import TypePM.DemandTypingErasure
import TypePM.DemandTypingRegression

/-!
# Public demand-directed state-erasure regression

The flagship polymorphic-let derivation crosses the public, closed-program
`SourceTyping` to `TypingInvariant` bridge at its published `Int` type.
-/

namespace TypePM.DemandTypingRegression

theorem dmLet_typingInvariant :
    TypingInvariant CertifiedInferenceRegression.emptySignature [] dmLetProgram
      .int :=
  dmLet_sourceTyping.typingInvariant emptySignature_schemesClosed

end TypePM.DemandTypingRegression
