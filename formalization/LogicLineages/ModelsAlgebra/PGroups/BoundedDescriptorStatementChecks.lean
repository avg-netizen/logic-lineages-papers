module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptorStatementChecks

theorem fixed_pure_pi_difference : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPurePiDifference :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pure_pi_difference

theorem fixed_bounded_descriptor : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedDescriptor :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_descriptor

theorem fixed_zero_lower_descriptor : LogicLineages.ModelsAlgebra.PGroups.Targets.groupZeroLowerDescriptor :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.zero_lower_descriptor

end LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptorStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
