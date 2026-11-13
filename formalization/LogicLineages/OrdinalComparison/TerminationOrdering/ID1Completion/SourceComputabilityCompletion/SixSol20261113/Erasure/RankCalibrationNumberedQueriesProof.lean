module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedObservationQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields args afterBase extraTypes extras rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields args afterBase)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply RankCalibrationNumberedObservationQueries.actualCases R H label head args extras parameter typ _
 intro beta j Theta headData headResult types headValue values sorted extraValues baseRank extraRank baseAndExtras headAndArgs typedData data candidate c gamma hj hh hf h7 h8 h9 h10 hbr her h11 h12 h13 h14 h15 hp
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have h0' := renameInto h0 j Theta hj
 have h1' := renameInto h1 j Theta hj
 have h2' := renameInto h2 j Theta hj
 have h3' := renameInto h3 j Theta hj
 have h4' := renameInto h4 j Theta hj
 have h5' := renameInto h5 j Theta hj
 have h6' := renameInto h6 j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr' h0' h1' h2' h3' h4' h5' h6'
 apply RankCalibrationEnvelopeQueries.actualCases (stage.relabel j) _
 intro delta k Xi tab base inner root rows hk ht ho hi
 simp only [graph1Rename,sucRelabel]
 have ih'' := renameInto ih' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hv'' := renameInto hv' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have h0'' := renameInto h0' k Xi hk
 have h1'' := renameInto h1' k Xi hk
 have h2'' := renameInto h2' k Xi hk
 have h3'' := renameInto h3' k Xi hk
 have h4'' := renameInto h4' k Xi hk
 have h5'' := renameInto h5' k Xi hk
 have h6'' := renameInto h6' k Xi hk
 have h7'' := renameInto h7 k Xi hk
 have h8'' := renameInto h8 k Xi hk
 have h9'' := renameInto h9 k Xi hk
 have h10'' := renameInto h10 k Xi hk
 have h11'' := renameInto h11 k Xi hk
 have h12'' := renameInto h12 k Xi hk
 have h13'' := renameInto h13 k Xi hk
 have h14'' := renameInto h14 k Xi hk
 have h15'' := renameInto h15 k Xi hk
 have hh'' := renameInto hh k Xi hk
 have hf'' := renameInto hf k Xi hk
 have hp'' := renameInto hp k Xi hk
 have hbr'' := renameInto hbr k Xi hk
 have her'' := renameInto her k Xi hk
 simp only [graph1Rename,graph2Rename,belowRawRename,stepArrowFieldsRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih'' hs'' hv'' hr'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8'' h9'' h10'' h11'' h12'' h13'' h14'' h15'' hh'' hf'' hp'' hbr'' her''
 exact RankCalibrationNumberedCoordinatesProof.actualCoordinates R H G M W
   ((stage.relabel j).relabel k) tab ((input.relabel j).relabel k) ((parameter.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) ((payload.relabel j).relabel k) ((label.relabel j).relabel k) ((afterLabel.relabel j).relabel k) ((head.relabel j).relabel k) ((afterHead.relabel j).relabel k) ((encodedType.relabel j).relabel k) ((numberedFields.relabel j).relabel k) ((args.relabel j).relabel k) ((afterBase.relabel j).relabel k) ((extraTypes.relabel j).relabel k) ((extras.relabel j).relabel k) (headValue.relabel k) (values.relabel k) (sorted.relabel k) (extraValues.relabel k) (baseAndExtras.relabel k) (headAndArgs.relabel k) (typedData.relabel k) (data.relabel k) (candidate.relabel k) (c.relabel k) (gamma.relabel k) (headData.relabel k) (headResult.relabel k) (types.relabel k) base inner root rows ((rank.relabel j).relabel k) (baseRank.relabel k) (extraRank.relabel k)
   ih'' hs'' hv'' hr'' ht ho hi hp'' hh'' hf'' hbr'' her'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8'' h9'' h10'' h11'' h12'' h13'' h14'' h15''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedQueriesProof
