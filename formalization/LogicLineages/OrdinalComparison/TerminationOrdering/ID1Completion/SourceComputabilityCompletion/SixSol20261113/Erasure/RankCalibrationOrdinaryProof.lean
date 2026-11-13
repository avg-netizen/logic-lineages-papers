module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationPackedTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Source-only successor ordinary branch, retaining the SAME sorted BASE
selected by the original observation program. -/
theorem actualOrdinary (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) input))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply OriginalTypedArgumentObservationsWalkQueryProof.pairCases input _
 intro beta j Theta typ raw hj hp
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have htag' := renameInto htag j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr' htag'
 have hrawtag := RankCalibrationPackedTagProof.rawTag (input.relabel j) typ raw (numeral 4) hp htag'
 apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw _ hrawtag
 intro delta k Xi head args hk hc
 simp only [graph1Rename,sucRelabel]
 have ih'' := renameInto ih' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hv'' := renameInto hv' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have hp'' := renameInto hp k Xi hk
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih'' hs'' hv'' hr'' hp''
 exact RankCalibrationOrdinaryQueriesProof.actualCoordinates R H G M W
   ((stage.relabel j).relabel k) ((input.relabel j).relabel k) ((parameter.relabel j).relabel k)
   (typ.relabel k) (raw.relabel k) head args ((rank.relabel j).relabel k)
   ih'' hs'' hv'' hr'' hp'' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryProof
