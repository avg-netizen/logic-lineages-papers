module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual application constructor coordinates and original child computations
supply the complete parent rank equation; no child decoder equation is assumed. -/
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab input parameter typ raw domain children payload fnRaw argRaw fnType fnPacked argPacked
 fnValue argValue fnObserved argObserved observations typedData data candidate base inner root rows rank fnRank argRank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hfs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fnPacked parameter)))
 (has : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) argPacked parameter)))
 (hfr : Nonempty (Derivation body Delta (graph1 variableRankRaw fnRank fnRaw)))
 (har : Nonempty (Derivation body Delta (graph1 variableRankRaw argRank argRaw)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children fnRaw argRaw)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnPacked fnType fnRaw)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argPacked domain argRaw)))
 (h7 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) fnValue fnPacked parameter)))
 (h8 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) argValue argPacked parameter)))
 (h9 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnObserved fnType fnValue)))
 (h10 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argObserved domain argValue)))
 (h11 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fnObserved argObserved)))
 (h12 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ observations)))
 (h13 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (h14 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (numeral 2) data)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 let xs : Fin 3 → OTerm alpha := ![domain,fnRaw,argRaw]
 have hchildren := binaryValue InternalPairing.pairing (.projection 1) (.projection 2)
   children fnRaw argRaw xs h3 (projectionValue 1 xs) (projectionValue 2 xs)
 have hpay := binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 1) (.projection 2))
   payload domain children xs h2 (projectionValue 0 xs) hchildren
 have happ := binaryValue InternalPairing.pairing (constant 3 2)
   (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2))) raw (numeral 2) payload xs
   h1 (constantValue 2 xs) hpay
 have hsum := rankSumForward rank fnRaw argRaw fnRank argRank hfr har
   (OriginalRawVariableRankApplicationProof.rankApplicationForward raw rank domain fnRaw argRaw happ
     (rankPackedForward input rank typ raw h0 hr))
 have heq := valueUnique InternalArithmeticPrograms.addition rank (InternalAdditionLawsProof.add fnRank argRank)
   (Fin.cons fnRank (Fin.cons argRank Fin.elim0)) hsum
   (InternalArithmeticProgramsSupportProof.additionValue fnRank argRank)
 have hc := OriginalRootObservationInternalProof.applicationLaw
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) body alpha Delta
   input parameter typ raw domain children payload fnRaw argRaw fnType fnPacked argPacked
   fnValue argValue fnObserved argObserved observations typedData data candidate
   h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
 have hroot := RankCalibrationRootEncodingProof.actualEncoding R H G M W
   input parameter (suc stage) inner base root rows candidate (numeral 2) data hs hv ho hi hc h14
 have hd := RankCalibrationApplicationStepProof.actualStep R H G M W
   stage tab base inner root rows data fnObserved fnType fnPacked parameter fnValue fnRank
   argObserved domain argPacked parameter argValue argRank ih ho hi hroot
   (RankCalibrationSelectorProof.functionValue data domain typedData typ observations fnObserved argObserved h13 h12 h11)
   h9 hfs h7 (rankPackedBackward fnPacked fnRank fnType fnRaw h5 hfr)
   (RankCalibrationSelectorProof.argumentValue data domain typedData typ observations fnObserved argObserved h13 h12 h11)
   h10 has h8 (rankPackedBackward argPacked argRank domain argRaw h6 har) ht
 obtain ⟨heq⟩ := heq
 exact outputTransport decoder (InternalAdditionLawsProof.add fnRank argRank) rank
   (Fin.cons (suc stage) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm heq⟩ hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationCoordinatesProof
