module

public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicBoundedScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_intrinsic_bounded_difference_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIntrinsicBoundedDifferenceScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.intrinsic_bounded_difference_scott

theorem fixed_intrinsic_bounded_pi_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIntrinsicBoundedPiScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.intrinsic_bounded_pi_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks
