module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCalibrationProof
open InternalApplicationStepPeelSupportProof (andIntro)
theorem actualSourceRankCalibration : RankMemoTargets.ActualSourceRankCalibration := by
 intro R H G M W body alpha Delta input parameter code rank hs hv hr
 exact RankCalibrationInductionBindingProof.atRawApply R H G M W code input parameter rank
   (RankCalibrationInductionProof.actualAtRaw R H G M W code) (andIntro hs (andIntro hv hr))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCalibrationProof
