module

public import LogicLineages.ModelsAlgebra.PGroups.CosetNormalization
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_coset_profile_maximum : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCosetProfileMaximum :=
  LogicLineages.ModelsAlgebra.PGroups.coset_profile_maximum

theorem fixed_coset_double_maximum : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCosetDoubleMaximum :=
  LogicLineages.ModelsAlgebra.PGroups.coset_double_maximum

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
