module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionBasics
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_representative : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionRepresentative :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_representative

theorem fixed_socle_correction_equality : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionEquality :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_equality

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
