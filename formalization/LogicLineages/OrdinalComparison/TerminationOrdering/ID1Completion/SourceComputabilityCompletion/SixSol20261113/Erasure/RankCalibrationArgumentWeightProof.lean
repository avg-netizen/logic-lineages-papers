module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLocalWeightsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSmallProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationArgumentWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions ObservationDescentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualBase (kind : UnsortedChildDefinitions.BaseSlot) (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab parameter gamma c types raw observations rank base inner root rows payload sorted : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hg : Nonempty (Derivation body Delta (graph1 G (numeral 1) c)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) observations raw parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hroot : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (numeral (UnsortedChildDefinitions.tag kind)) payload)))
 (hsel : Nonempty (Derivation body Delta (graph1 (select (listPath (UnsortedChildDefinitions.slot kind))) sorted payload)))
 (hsort : Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted observations)))
 : Nonempty (Derivation body Delta (programGraph (SortWeightedDefinitions.weighted lookupWeight) rank
   (Fin.cons sorted (Fin.cons stage (Fin.cons tab Fin.elim0))))) := by
 have hw := RankCalibrationLocalWeightsProof.actualWeights R H G M W stage tab parameter gamma c ih ht hp hg
 have hb := RankCalibrationSmallProof.baseSmall kind (suc stage) base inner root rows payload observations sorted ho hi hroot hsel hsort
 have hagg := RankArgumentProof.actualAggregation 2 (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   lookupWeight H M W body alpha Delta types raw parameter gamma c observations rank (suc stage)
   (Fin.cons stage (Fin.cons tab Fin.elim0)) ha hp he hr hb hw
 exact SortWeightedSortProof.actualSort 2 lookupWeight body alpha Delta observations sorted rank
   (Fin.cons stage (Fin.cons tab Fin.elim0)) hsort hagg

theorem actualStored (slot : ListSlot) (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab parameter gamma c types raw observations rank base inner root rows payload label : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hg : Nonempty (Derivation body Delta (graph1 G (numeral 1) c)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) observations raw parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hroot : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root label payload)))
 (hsel : Nonempty (Derivation body Delta (graph1 (select (listPath slot)) observations payload)))
 : Nonempty (Derivation body Delta (programGraph (SortWeightedDefinitions.weighted lookupWeight) rank
   (Fin.cons observations (Fin.cons stage (Fin.cons tab Fin.elim0))))) := by
 have hw := RankCalibrationLocalWeightsProof.actualWeights R H G M W stage tab parameter gamma c ih ht hp hg
 have hb := RankCalibrationSmallProof.storedSmall slot (suc stage) base inner root rows payload observations label ho hi hroot hsel
 have hagg := RankArgumentProof.actualAggregation 2 (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   lookupWeight H M W body alpha Delta types raw parameter gamma c observations rank (suc stage)
   (Fin.cons stage (Fin.cons tab Fin.elim0)) ha hp he hr hb hw
 exact hagg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationArgumentWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationArgumentWeightProof
