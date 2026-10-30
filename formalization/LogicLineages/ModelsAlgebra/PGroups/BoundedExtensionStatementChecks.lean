module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_cyclic_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedCyclicExtension :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_cyclic_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
