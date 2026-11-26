module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationRawQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Source-only successor application branch. All child source and numeric
rank facts, observation nodes, strict descents and memo queries are discharged. -/
theorem actualApplication (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag (numeral 2) input))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply OriginalPackedSourceApplicationFieldsProof.actualFieldsCases body alpha Delta H G M W input parameter _ hs htag
 intro beta j Theta arrow domain typ fnRaw argRaw fnPacked argPacked hj hc hfs has
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr'
 apply RankCalibrationApplicationRawQueries.actualCases arrow domain typ fnRaw argRaw fnPacked argPacked (input.relabel j) _ hc
 intro delta k Xi raw payload children hk h0 h1 h2 h3
 simp only [graph1Rename,sucRelabel]
 have ih'' := renameInto ih' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hv'' := renameInto hv' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have hc'' := renameInto hc k Xi hk
 have hfs'' := renameInto hfs k Xi hk
 have has'' := renameInto has k Xi hk
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih'' hs'' hv'' hr'' hfs'' has''
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc''
 exact RankCalibrationApplicationQueriesProof.actualCoordinates R H G M W
   ((stage.relabel j).relabel k) ((input.relabel j).relabel k) ((parameter.relabel j).relabel k)
   (typ.relabel k) raw (domain.relabel k) children payload (fnRaw.relabel k) (argRaw.relabel k)
   (arrow.relabel k) (fnPacked.relabel k) (argPacked.relabel k) ((rank.relabel j).relabel k)
   ih'' hs'' hv'' hr'' hfs'' has'' h0 h1 h2 h3
   (andLeft hc'') (andLeft (andRight hc'')) (andLeft (andRight (andRight hc'')))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationProof
