module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionLinear
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_linear_embedding : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionLinearEmbedding :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_linear_embedding

theorem fixed_socle_correction_finite_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionFiniteRank :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_finite_rank

theorem fixed_socle_correction_rank_le : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionRankLe :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_rank_le

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
