module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedStandaloneExtraction.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal own-root selected extraction equals the payload of the actual
final cache. Singleton shape and Some-definedness are conclusions of the proof,
not premises. The actual rank controls the exact successor stage. -/
def InternalRootExtraction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node param rank table value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table (suc rank) node param)) →
  (Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) value node param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table node)))

/-- An arbitrary actually aligned decoded cache yields the independent node's
literal standalone value. No independent-child equivalence, valid decoder,
Some witness, or lookup agreement is assumed. Payload zero remains Some 0. -/
def InternalAlignedExtraction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node param index seed rank depth frontier table value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank seed param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index rank)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table (suc index) seed param)) →
  (Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) value node param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table node)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedStandaloneExtraction.Targets
