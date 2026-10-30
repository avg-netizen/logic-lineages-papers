module

public import LogicLineages.ModelsAlgebra.PGroups.DescriptorScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_descriptor_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedDescriptorScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_descriptor_scott

theorem fixed_zero_lower_descriptor_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupZeroLowerDescriptorScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.zero_lower_descriptor_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
