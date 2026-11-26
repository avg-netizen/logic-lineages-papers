module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
/-- Literal two-key mapGraph answer order, including zero cached values. -/
def InternalTwoAnswers : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (keys tail first second table left right answers : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys first tail)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table first)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table second)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers keys table)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup left z answers)) ∧
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))
/-- Original cons dependency output, not a surrogate dependency list. -/
def InternalConsAnswers : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau head tail param deps table left right answers : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table head)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table tail)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps table)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup left z answers)) ∧
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Targets
