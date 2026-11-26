module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankProof
/-- Both actual source ranks compute through the same unchanged decoder at the
same actual evaluator code; original internal Program functionality identifies
its outputs. No structural-key or canonical-fold conclusion is involved. -/
theorem actualRankDeterminacy : EvaluatorRankTargets.ActualRankDeterminacy := by
 intro R H G M W body alpha Delta left right parameter code leftRank rightRank hl hr hel her hrl hrr
 have hdl := RankMemoCalibrationProof.actualSourceRankCalibration
   R H G M W body alpha Delta left parameter code leftRank hl hel hrl
 have hdr := RankMemoCalibrationProof.actualSourceRankCalibration
   R H G M W body alpha Delta right parameter code rightRank hr her hrr
 exact InternalControlGraphSupportProof.valueUnique RankMemoDefinitions.decoder
   leftRank rightRank (Fin.cons code Fin.elim0) hdl hdr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankProof
