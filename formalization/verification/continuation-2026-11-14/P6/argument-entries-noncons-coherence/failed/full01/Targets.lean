module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Actual raw non-cons step is tail-independent, including malformed payloads. -/
def InternalStepTransport : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tag tail1 tail2 value : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)) →
  Nonempty (Derivation body Delta (eqn tag (numeral 7)).not) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tail1)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tail2))
/-- Actual non-cons cache coherence requires no agreement between old tables. -/
def InternalCacheTransport : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw tag param frontier1 frontier2 old1 old2 table1 table2 found : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)) →
  Nonempty (Derivation body Delta (eqn tag (numeral 7)).not) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Targets
