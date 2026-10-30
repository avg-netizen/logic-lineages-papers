module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionCriterion
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_nonsurjective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionNonsurjective :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_nonsurjective

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
