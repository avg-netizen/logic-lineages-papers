module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
/-- Literal original decoded dependency frontier, arbitrary symbolic depth and
all raw seeds. Both ranks are actual graph outputs, not raw-code surrogates. -/
def InternalRankBound : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (depth seed param frontier node seedRank nodeRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) nodeRank node param)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth nodeRank) seedRank))
/-- The actual original frontier exhausts at actual original seed rank + 1,
including malformed seeds of rank zero. No native reflection or validity premise. -/
def InternalRankExhaustion : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (seed param seedRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)) →
  Nonempty (Derivation body Delta (graph3
    (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) z (suc seedRank) seed param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.Targets
