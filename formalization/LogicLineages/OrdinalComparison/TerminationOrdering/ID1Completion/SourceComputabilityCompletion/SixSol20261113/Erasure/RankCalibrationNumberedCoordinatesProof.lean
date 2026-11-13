module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawVariableRankSupportProof
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Same original numbered root: BASE is sorted but extras remain in order.
Both argument ranks are derived with original admission and strict code IH. -/
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields args afterBase extraTypes extras
 headValue values sorted extraValues baseAndExtras headAndArgs typedData data candidate c gamma headData headResult types
 base inner root rows rank baseRank extraRank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
 (hf : Nonempty (Derivation body Delta (OriginalTypedDecoderStepSpecification.StepArrowFields headData headResult types)))
 (hbr : Nonempty (Derivation body Delta (graph1 variableRankRaw baseRank args)))
 (her : Nonempty (Derivation body Delta (graph1 variableRankRaw extraRank extras)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields args afterBase)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)))
 (h7 : Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headValue head)))
 (h8 : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R)) values args parameter)))
 (h9 : Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted values)))
 (h10 : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R)) extraValues extras parameter)))
 (h11 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing baseAndExtras sorted extraValues)))
 (h12 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndArgs headValue baseAndExtras)))
 (h13 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ headAndArgs)))
 (h14 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data label typedData)))
 (h15 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (numeral 5) data)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 have hctor := OriginalRawSyntaxTransportInternalParserNumberedValueProof.numberedConstructorValue
   raw payload afterLabel afterHead numberedFields afterBase label head encodedType args extraTypes extras h1 h2 h3 h4 h5 h6
 have hsum := rankSumForward rank args extras baseRank extraRank hbr her
   (OriginalRawVariableRankNumberedProof.rankNumberedForward raw rank label head encodedType args extraTypes extras hctor
     (rankPackedForward input rank typ raw h0 hr))
 have heq := valueUnique InternalArithmeticPrograms.addition rank (InternalAdditionLawsProof.add baseRank extraRank)
   (Fin.cons baseRank (Fin.cons extraRank Fin.elim0)) hsum
   (InternalArithmeticProgramsSupportProof.additionValue baseRank extraRank)
 have hadmit := Context.SpineChildrenProof.actualNumbered H G M W body alpha Delta
   input parameter typ raw c gamma label head encodedType args extraTypes extras headData headResult types hs h0 hp hctor hh hf
 have hc := OriginalRootObservationComplexProof.numberedLaw
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) body alpha Delta
   input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields args afterBase extraTypes extras
   headValue values sorted extraValues baseAndExtras headAndArgs typedData data candidate
   h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
 have hroot := RankCalibrationRootEncodingProof.actualEncoding R H G M W
   input parameter (suc stage) inner base root rows candidate (numeral 5) data hs hv ho hi hc h15
 have hbsel := RankCalibrationNumberedSelectorProof.baseValue data label typedData typ headAndArgs headValue baseAndExtras sorted extraValues h14 h13 h12 h11
 have hesel := RankCalibrationNumberedSelectorProof.extrasValue data label typedData typ headAndArgs headValue baseAndExtras sorted extraValues h14 h13 h12 h11
 have hbw := RankCalibrationArgumentWeightProof.actualBase .numbered R H G M W
   stage tab parameter gamma c types args values baseRank base inner root rows data sorted
   ih ht hp (andLeft hadmit) (andLeft (andRight hadmit)) h8 hbr ho hi hroot hbsel h9
 have hew := RankCalibrationArgumentWeightProof.actualStored .numberedExtras R H G M W
   stage tab parameter gamma c extraTypes extras extraValues extraRank base inner root rows data (numeral 5)
   ih ht hp (andLeft hadmit) (andRight (andRight hadmit)) h10 her ho hi hroot hesel
 have hpay := RankMemoOpeningProof.payloadValue stage tab (suc stage) base inner root rows
   (numeral 5) data ⟨InternalTagArithmeticSupportProof.refl (suc stage)⟩ ho hi hroot
 have htag := RankMemoOpeningProof.tagValue stage tab (suc stage) base inner root rows
   (numeral 5) data ⟨InternalTagArithmeticSupportProof.refl (suc stage)⟩ ho hi hroot
 have hdecode := RankMemoSuccessorProof.atSuccessor stage tab (InternalAdditionLawsProof.add baseRank extraRank) ht
   (RankMemoDispatchProof.dispatch5 stage tab (InternalAdditionLawsProof.add baseRank extraRank) htag
     (RankMemoBranchValueProof.sumValue (rowRank .numberedBase) (rowRank .numberedExtras) stage tab baseRank extraRank
       (RankMemoBranchValueProof.rowValue .numberedBase stage tab data sorted baseRank hpay hbsel hbw)
       (RankMemoBranchValueProof.rowValue .numberedExtras stage tab data extraValues extraRank hpay hesel hew)))
 obtain ⟨heq⟩ := heq
 exact outputTransport decoder (InternalAdditionLawsProof.add baseRank extraRank) rank
   (Fin.cons (suc stage) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm heq⟩ hdecode
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedCoordinatesProof
