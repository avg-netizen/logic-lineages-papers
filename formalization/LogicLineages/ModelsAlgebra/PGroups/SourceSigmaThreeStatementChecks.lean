module

public import LogicLineages.ModelsAlgebra.PGroups.SourceSigmaThree
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_sigma_scott_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaScottIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_scott_isomorphism

theorem fixed_reservoir_no_sigma_three_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirNoSigmaThreeScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_no_sigma_three_scott

theorem fixed_raw_source_two_infinite_no_sigma_three : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawSourceTwoInfiniteNoSigmaThree :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_source_two_infinite_no_sigma_three

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
