module

public import LogicLineages.ModelsAlgebra.PGroups.HigherPerturbation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_higher_perturbation_proper : LogicLineages.ModelsAlgebra.PGroups.Targets.groupHigherPerturbationProper :=
  LogicLineages.ModelsAlgebra.PGroups.higher_perturbation_proper

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
