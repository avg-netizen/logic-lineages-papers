module

public import LogicLineages.ModelsAlgebra.PGroups.ScottTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_pi_scott_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiScottIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_scott_isomorphism

theorem fixed_full_shift_no_sigma_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftNoSigmaTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_no_sigma_two_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
