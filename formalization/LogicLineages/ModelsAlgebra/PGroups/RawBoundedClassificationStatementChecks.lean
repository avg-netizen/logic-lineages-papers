module

public import LogicLineages.ModelsAlgebra.PGroups.RawBoundedClassification
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_bounded_classification : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawBoundedClassification :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_bounded_classification

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
