module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
/-- Private frontier fuel-budget invariant for the actual enumeration R/D. -/
def InternalRankBound : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (depth seed param frontier node seedRank nodeRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R nodeRank node param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth nodeRank) seedRank))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.Targets
