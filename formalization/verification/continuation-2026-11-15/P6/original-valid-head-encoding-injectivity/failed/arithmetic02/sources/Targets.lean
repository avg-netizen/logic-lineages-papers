module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Proof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
/-- Encoding equality reflects raw-head equality on the actual original
head-decoder success domain. No native image or semantic-head witness is
assumed. The unguarded all-raw injectivity claim would be false. -/
def InternalValidEncoding : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (f g ef eg : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f)) →
  Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  (Nonempty (Derivation body Delta (eqn ef eg)) ↔
    Nonempty (Derivation body Delta (eqn f g)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Targets
