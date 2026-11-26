module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNonvariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBranchesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualAt (R : Program 2) (H G : Program 1) (M W : Program 2)
 (code input parameter rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W code)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) :
 Nonempty (Derivation body Delta (graph1 decoder rank code)) := by
 apply RankCalibrationSourceCasesProof.actualCases H G M W input parameter _ hs
 intro beta j Theta index hj ht
 rw [graph1Rename]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ih' hs' hv' hr'
 fin_cases index
 · exact RankCalibrationBaseProof.actualVariable R H G M W body beta Theta (input.relabel j) (parameter.relabel j) (code.relabel j) (rank.relabel j) hs' hv' hr' ht
 · exact RankCalibrationNonvariableProof.actualNonvariable R H G M W 0 (code.relabel j) (input.relabel j) (parameter.relabel j) (rank.relabel j) ih' hs' hv' hr' ht
 · exact RankCalibrationNonvariableProof.actualNonvariable R H G M W 1 (code.relabel j) (input.relabel j) (parameter.relabel j) (rank.relabel j) ih' hs' hv' hr' ht
 · exact RankCalibrationNonvariableProof.actualNonvariable R H G M W 2 (code.relabel j) (input.relabel j) (parameter.relabel j) (rank.relabel j) ih' hs' hv' hr' ht
 · exact RankCalibrationNonvariableProof.actualNonvariable R H G M W 3 (code.relabel j) (input.relabel j) (parameter.relabel j) (rank.relabel j) ih' hs' hv' hr' ht
 · exact RankCalibrationNonvariableProof.actualNonvariable R H G M W 4 (code.relabel j) (input.relabel j) (parameter.relabel j) (rank.relabel j) ih' hs' hv' hr' ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBranchesProof
