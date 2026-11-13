module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryObservationQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryQueriesProof
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
 (stage input parameter typ raw head args rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (hctor : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head args))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply RankCalibrationOrdinaryObservationQueries.actualCases R H head args parameter typ _
 intro beta j Theta headData headResult types headValue values sorted headAndBase data candidate payload c gamma hj hh hf h3 h4 h5 h6 h7 h8 h2 hp
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have h0' := renameInto h0 j Theta hj
 have hctor' := renameInto hctor j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr' h0' hctor'
 let xs : Fin 2 → OTerm beta := ![head.relabel j,args.relabel j]
 have hpay := binaryValue InternalPairing.pairing (.projection 0) (.projection 1) payload
   (head.relabel j) (args.relabel j) xs h2 (projectionValue 0 xs) (projectionValue 1 xs)
 have h1 := binaryRecover InternalPairing.pairing (constant 2 4) (pairOf (.projection 0) (.projection 1))
   (raw.relabel j) (numeral 4) payload xs hctor' (constantValue 4 xs) hpay
 apply RankCalibrationEnvelopeQueries.actualCases (stage.relabel j) _
 intro delta k Xi tab base inner root rows hk ht ho hi
 simp only [graph1Rename,sucRelabel]
 have ih'' := renameInto ih' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hv'' := renameInto hv' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have h0'' := renameInto h0' k Xi hk
 have h1'' := renameInto h1 k Xi hk
 have h2'' := renameInto h2 k Xi hk
 have h3'' := renameInto h3 k Xi hk
 have h4'' := renameInto h4 k Xi hk
 have h5'' := renameInto h5 k Xi hk
 have h6'' := renameInto h6 k Xi hk
 have h7'' := renameInto h7 k Xi hk
 have h8'' := renameInto h8 k Xi hk
 have hh'' := renameInto hh k Xi hk
 have hf'' := renameInto hf k Xi hk
 have hp'' := renameInto hp k Xi hk
 simp only [graph1Rename,graph2Rename,belowRawRename,stepArrowFieldsRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih'' hs'' hv'' hr'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8'' hh'' hf'' hp''
 exact RankCalibrationOrdinaryCoordinatesProof.actualCoordinates R H G M W
   ((stage.relabel j).relabel k) tab ((input.relabel j).relabel k) ((parameter.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) (payload.relabel k) ((head.relabel j).relabel k) ((args.relabel j).relabel k) (headValue.relabel k) (values.relabel k) (sorted.relabel k) (headAndBase.relabel k) (data.relabel k) (candidate.relabel k) (c.relabel k) (gamma.relabel k) (headData.relabel k) (headResult.relabel k) (types.relabel k) base inner root rows ((rank.relabel j).relabel k)
   ih'' hs'' hv'' hr'' ht ho hi hp'' hh'' hf'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryQueriesProof
