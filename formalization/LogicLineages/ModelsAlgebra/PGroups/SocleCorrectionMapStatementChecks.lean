module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionMap
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_evaluation

theorem fixed_socle_correction_hom_kernel : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionHomKernel :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_hom_kernel

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
