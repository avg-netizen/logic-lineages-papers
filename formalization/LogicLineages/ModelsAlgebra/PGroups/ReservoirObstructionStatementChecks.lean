module

public import LogicLineages.ModelsAlgebra.PGroups.ReservoirObstruction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_reservoir_no_difference_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirNoDifferenceTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_no_difference_two_scott

theorem fixed_difference_scott_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupDifferenceScottIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.difference_scott_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
