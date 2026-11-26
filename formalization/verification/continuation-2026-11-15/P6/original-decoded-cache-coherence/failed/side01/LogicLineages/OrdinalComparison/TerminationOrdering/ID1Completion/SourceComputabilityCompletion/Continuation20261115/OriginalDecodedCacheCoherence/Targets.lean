module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual first-match Option cache-value transport between two independently
rooted original decoded recursion tables, for the same node/parameter/layer AST.
All smaller-rank agreement, totality witnesses, stage predecessors and equal
complete ordered answer lists are proved internally, not public hypotheses. -/
def InternalTransport : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node param index1 seed1 rank1 depth1 frontier1 table1
      index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank1 seed1 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index1 rank1)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth1 index1 rank1)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier1 depth1 seed1 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 node)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table1 (suc index1) seed1 param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank2 seed2 param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index2 rank2)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth2 index2 rank2)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier2 depth2 seed2 param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 node)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table2 (suc index2) seed2 param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 node))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.Targets
