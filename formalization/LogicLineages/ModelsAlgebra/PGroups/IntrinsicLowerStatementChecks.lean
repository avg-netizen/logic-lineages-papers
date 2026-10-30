module

public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicLower
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_intrinsic_no_pi_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIntrinsicNoPiTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.intrinsic_no_pi_two_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
