module

public import LogicLineages.ModelsAlgebra.PGroups.RawUpperBounds
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_finite_difference_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawFiniteDifferenceScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_finite_difference_scott

theorem fixed_raw_trivial_pi_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawTrivialPiOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_trivial_pi_one_scott

theorem fixed_raw_bounded_pi_three_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawBoundedPiThreeScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_bounded_pi_three_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
