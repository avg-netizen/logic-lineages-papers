module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open ObservationDescentDefinitions RankCalibrationSelectorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem baseValue (data label typedData typ headAndArgs head baseAndExtras base extras : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data label typedData)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ headAndArgs)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndArgs head baseAndExtras)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing baseAndExtras base extras))) :
 Nonempty (Derivation body Delta (graph1 (select (listPath .numberedBase)) base data)) :=
 rightValue [true,true,false] data label typedData base h0
   (rightValue [true,false] typedData typ headAndArgs base h1
     (rightValue [false] headAndArgs head baseAndExtras base h2
       (leftValue [] baseAndExtras base extras base h3 (nilValue base))))

theorem extrasValue (data label typedData typ headAndArgs head baseAndExtras base extras : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data label typedData)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ headAndArgs)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndArgs head baseAndExtras)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing baseAndExtras base extras))) :
 Nonempty (Derivation body Delta (graph1 (select (listPath .numberedExtras)) extras data)) :=
 rightValue [true,true,true] data label typedData extras h0
   (rightValue [true,true] typedData typ headAndArgs extras h1
     (rightValue [true] headAndArgs head baseAndExtras extras h2
       (rightValue [] baseAndExtras base extras extras h3 (nilValue extras))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedSelectorProof
