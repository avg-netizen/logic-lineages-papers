module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Genuine all-raw depth-cache Option-value transport, at the fixed explicit
depth layer and shared parameter. Both actual index/subtraction/frontier/successor
records are observed. Presence, strict-child rank induction, previous alignment and
whole ordered answer-list agreement are internal proof duties, not hypotheses.
No argument-entry values or decoded-node rank are reused. -/
def InternalCacheTransport : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw param index1 seed1 depth1 frontier1 table1 index2 seed2 depth2 frontier2 table2 found : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index1 seed1)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth1 index1 seed1)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier1 depth1 seed1 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.graph n) table1 (suc index1) seed1 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index2 seed2)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth2 index2 seed2)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationDepth.dependency) frontier2 depth2 seed2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.graph n) table2 (suc index2) seed2 param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.Targets
