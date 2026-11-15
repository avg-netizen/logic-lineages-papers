module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Leaf cache is outer Some(inner Some nil), exactly 2, regardless of old table. -/
def InternalNilCache : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw frontier old param table : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (numeral 2) table raw))
/-- Actual local cons coherence: equal tail caches suffice; the two present head
cache values may differ. No equality to independent child calls is assumed. -/
def InternalConsTransport : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Targets
