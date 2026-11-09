module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RankProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks

theorem actual_residual_heads : RankTargets.ActualResidualHeads :=
  Proof.actualResidualHeads

theorem actual_residual_top_ranks : RankTargets.ActualResidualTopRanks :=
  Proof.actualResidualTopRanks

theorem residual_row_rank_bounds : RankTargets.ResidualRowRankBounds :=
  Proof.residualRowRankBounds

#print axioms actual_residual_heads
#print axioms actual_residual_top_ranks
#print axioms residual_row_rank_bounds

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks
