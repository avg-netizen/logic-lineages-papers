module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter typ raw label head encoded args types extras rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,encoded,args,types,extras]))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply RankCalibrationNumberedRawQueries.actualCases raw label head encoded args types extras _ hc
 intro beta j Theta payload afterLabel afterHead numberedFields afterBase hj h1 h2 h3 h4 h5 h6
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have h0' := renameInto h0 j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr' h0'
 exact RankCalibrationNumberedQueriesProof.actualCoordinates R H G M W
   (stage.relabel j) (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j)
   payload (label.relabel j) afterLabel (head.relabel j) afterHead (encoded.relabel j) numberedFields
   (args.relabel j) afterBase (types.relabel j) (extras.relabel j) (rank.relabel j)
   ih' hs' hv' hr' h0' h1 h2 h3 h4 h5 h6
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawWrapperProof
