module

public import LogicLineages.ModelsAlgebra.PGroups.LimitPiTwo
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.LimitPiTwoStatementChecks

theorem fixed_endomorphism_limit_pi_two : LogicLineages.ModelsAlgebra.PGroups.Targets.groupEndomorphismLimitPiTwo :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.endomorphism_limit_pi_two

end LogicLineages.ModelsAlgebra.PGroups.LimitPiTwoStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
