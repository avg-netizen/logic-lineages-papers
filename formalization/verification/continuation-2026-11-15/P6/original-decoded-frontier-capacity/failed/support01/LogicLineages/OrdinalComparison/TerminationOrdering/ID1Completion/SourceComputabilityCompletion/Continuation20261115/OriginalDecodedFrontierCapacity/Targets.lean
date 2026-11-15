module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
/-- Capacity at the literal decoded graph-recursion frontier. Its rank and
subtraction witnesses are recovered internally from the actual composition. -/
def InternalCapacity : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index previous seed param frontier node seedRank nodeRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank)) →
  Nonempty (Derivation body Delta (programGraph (ExchangeGraphRecursion.frontier (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)) frontier
    ![index, previous, seed, param])) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) nodeRank node param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank index))
/-- An actual dependency of a current successor-frontier member lies in the
literal preceding frontier. This is frontier membership, NOT cache presence
or cache value agreement; no hypothesis asserts either of those properties. -/
def InternalPreviousFrontier : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (index previous older seed param current prior node deps child seedRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (suc index) seedRank)) →
  Nonempty (Derivation body Delta (programGraph (ExchangeGraphRecursion.frontier (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)) current
    ![suc index, previous, seed, param])) →
  Nonempty (Derivation body Delta (programGraph (ExchangeGraphRecursion.frontier (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)) prior
    ![index, older, seed, param])) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) current node)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) prior child))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Targets
