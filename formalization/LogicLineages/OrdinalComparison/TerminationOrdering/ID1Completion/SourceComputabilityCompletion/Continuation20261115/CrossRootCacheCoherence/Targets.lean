module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Genuine all-raw cache-value coherence across two independently rooted
original recursion tables. Each side has its actual bounded index, original
subtraction depth, frontier membership, and successor graph table. No typing,
child-value agreement, positive index, or inductive hypothesis is assumed. -/
def InternalCacheTransport : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index1 seed1)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth1 index1 seed1)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier1 depth1 seed1 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table1 (suc index1) seed1 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index2 seed2)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth2 index2 seed2)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier2 depth2 seed2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table2 (suc index2) seed2 param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.Targets
