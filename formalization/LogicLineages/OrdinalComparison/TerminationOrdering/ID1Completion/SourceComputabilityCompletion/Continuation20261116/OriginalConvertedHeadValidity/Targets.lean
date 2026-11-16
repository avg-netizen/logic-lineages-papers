module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
/-- Every raw encoded input, including failures of the original Encodable
head decoder, converts to a syntactically valid original numeric head. -/
def NativeConvertedValidity : Prop := ∀ (n encoded : Nat),
  (NumberedNumericDecoding.decodeHeadNumber n
    (evaluate (OriginalEncodedHeadConversion.convert n)
      (List.Vector.ofFn ![encoded]))).isSome = true
/-- Genuine internal validity of the actual conversion result. The only
premise is its actual graph, not encoded-image membership, pre-existing head
validity, a native assertion, or a supplied semantic oracle. All raw inputs
and outputs are quantified, with original failure/default0 behavior retained. -/
def InternalConvertedValidity : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (encoded raw : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 (OriginalEncodedHeadConversion.convert n) raw encoded)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Targets
