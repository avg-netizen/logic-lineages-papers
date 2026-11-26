module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
/-- Actual successor cache domain for this original enumeration tuple. The
rank is observed from R(seed), not identified with the raw seed number. No
success/validity/native-image premise; every actual member's lookup is nonzero. -/
def InternalDomain : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (index seed param seedRank depth frontier table node found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationRecursion.graph n) table (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)) →
  Nonempty (Derivation body Delta (eqn found z).not)
/-- Genuine cross-root first-match Option-value transport for the same node,
parameter and concrete G. All rank induction, child presence, predecessor
alignment and ordered answer-list agreement are internal duties. -/
def InternalTransport : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (node param index1 seed1 rank1 depth1 frontier1 table1
      index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank1 seed1 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index1 rank1)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth1 index1 rank1)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier1 depth1 seed1 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 node)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationRecursion.graph n) table1 (suc index1) seed1 param)) →
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank2 seed2 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index2 rank2)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth2 index2 rank2)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier2 depth2 seed2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 node)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationRecursion.graph n) table2 (suc index2) seed2 param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 node))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Targets
