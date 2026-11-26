module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceLambdaQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Source-only successor lambda branch of the strong numeric induction.
No child/source/rank/table/semantic-envelope correctness premise remains. -/
theorem actualLambda (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) input))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply RankCalibrationSourceLambdaQueries.actualCases H G M W input parameter _ hs htag
 intro beta j Theta arrow raw payload domain childRaw codomain context gamma extended child childParam hj h0 h1 h2 h3 h4 h5 h6 h7
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr'
 exact RankCalibrationLambdaQueriesProof.actualCoordinates R H G M W
   (stage.relabel j) (input.relabel j) (parameter.relabel j) arrow raw domain codomain payload childRaw child context gamma extended childParam (rank.relabel j)
   ih' hs' hv' hr' h0 h1 h2 h3 h4 h5 h6 h7
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaProof
