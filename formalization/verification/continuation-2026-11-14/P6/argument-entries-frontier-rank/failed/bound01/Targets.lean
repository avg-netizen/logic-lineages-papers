module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Arbitrary symbolic depth and ALL raw seeds; literal original frontier.
The conclusion is the object-language arithmetic bound depth+child ≤ seed. -/
def InternalRankBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (depth seed param frontier child : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)) →
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth child) seed))
/-- Actual original frontier is empty at the literal raw rank plus one, without
assuming decoding, typed validity, or any native calibration reflection. -/
def InternalRankExhaustion : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (seed param : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) z (suc seed) seed param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.Targets
