module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions
/-- Conditional internal aggregation over the actual original tag6/tag7
argument spine and its actual typed observation row, including multiplicities.
Final rank calibration must discharge AllSmall and LocalWeights independently.
No global rank-decoder equation or source-rank conclusion is assumed. -/
def ActualAggregation : Prop := ∀ (k : Nat) (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (types raw parameter gamma c observations rank bound : OTerm alpha) (params : Fin k → OTerm alpha),
 Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) observations raw parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw)) →
 Nonempty (Derivation body Delta (AllSmall observations bound)) →
 Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)) →
 Nonempty (Derivation body Delta (programGraph (SortWeightedDefinitions.weighted F) rank (Fin.cons observations params)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentTargets
