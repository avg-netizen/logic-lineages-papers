module

public import LogicLineages.ModelsAlgebra.PGroups.ExactHeight
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_exact_height_below_cut : LogicLineages.ModelsAlgebra.PGroups.Targets.groupExactHeightBelowCut :=
  LogicLineages.ModelsAlgebra.PGroups.exact_height_below_cut

theorem fixed_exact_height_zero_stage : LogicLineages.ModelsAlgebra.PGroups.Targets.groupExactHeightZeroStage :=
  LogicLineages.ModelsAlgebra.PGroups.exact_height_zero_stage

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
