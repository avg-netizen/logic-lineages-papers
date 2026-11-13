module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationArgumentWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Original source admission, raw-rank reduction and sorted BASE aggregation
are all used at the same literal ordinary root and actual numeric envelope. -/
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab input parameter typ raw payload head args headValue values sorted headAndBase data candidate
 c gamma headData headResult types base inner root rows rank : OTerm alpha)
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
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload head args)))
 (h3 : Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headValue head)))
 (h4 : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R)) values args parameter)))
 (h5 : Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted values)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headAndBase headValue sorted)))
 (h7 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data typ headAndBase)))
 (h8 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (numeral 4) data)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 let xs : Fin 2 → OTerm alpha := ![head,args]
 have hpayload := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
   payload head args xs h2 (projectionValue 0 xs) (projectionValue 1 xs)
 have hctor := binaryValue InternalPairing.pairing (constant 2 4)
   (pairOf (.projection 0) (.projection 1)) raw (numeral 4) payload xs h1 (constantValue 4 xs) hpayload
 have hargsrank := OriginalRawVariableRankUnaryProof.rankOrdinaryForward raw rank head args hctor
   (rankPackedForward input rank typ raw h0 hr)
 have hadmit := Context.SpineChildrenProof.actualOrdinary H G M W body alpha Delta
   input parameter typ raw c gamma head args headData headResult types hs h0 hp hctor hh hf
 have hc := OriginalRootObservationComplexProof.ordinaryLaw
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) body alpha Delta
   input parameter typ raw payload head args headValue values sorted headAndBase data candidate
   h0 h1 h2 h3 h4 h5 h6 h7 h8
 have hroot := RankCalibrationRootEncodingProof.actualEncoding R H G M W
   input parameter (suc stage) inner base root rows candidate (numeral 4) data hs hv ho hi hc h8
 have hsel := RankCalibrationSelectorProof.lambdaValue data typ headAndBase headValue sorted h7 h6
 have hw := RankCalibrationArgumentWeightProof.actualBase .ordinary R H G M W
   stage tab parameter gamma c types args values rank base inner root rows data sorted
   ih ht hp (andLeft hadmit) (andRight hadmit) h4 hargsrank ho hi hroot hsel h5
 have hpay := RankMemoOpeningProof.payloadValue stage tab (suc stage) base inner root rows
   (numeral 4) data ⟨InternalTagArithmeticSupportProof.refl (suc stage)⟩ ho hi hroot
 have htag := RankMemoOpeningProof.tagValue stage tab (suc stage) base inner root rows
   (numeral 4) data ⟨InternalTagArithmeticSupportProof.refl (suc stage)⟩ ho hi hroot
 exact RankMemoSuccessorProof.atSuccessor stage tab rank ht
   (RankMemoDispatchProof.dispatch4 stage tab rank htag
     (RankMemoBranchValueProof.rowValue .ordinaryBase stage tab data sorted rank hpay hsel hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryCoordinatesProof
