module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114

/-- At the actual own-root final table, literal head/pair-snd extraction is
exactly the first-match cache payload. No singleton or typedness is assumed. -/
def InternalRootExtraction : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw param table value : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)) →
  (Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table raw)))

/-- Any actually aligned cache containing raw agrees with raw's standalone
extraction. In particular value zero is a present payload, not a missing key.
The independent child's graph equivalence is a conclusion, never a premise. -/
def InternalAlignedExtraction : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw param index seed depth frontier table value : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)) →
  (Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table raw)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Targets
