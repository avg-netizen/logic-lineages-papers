module

public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionStatementChecks

theorem fixed_join_left_assignment : LogicLineages.ModelsAlgebra.PGroups.Targets.groupJoinLeftAssignment :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.join_left_assignment

theorem fixed_join_right_assignment : LogicLineages.ModelsAlgebra.PGroups.Targets.groupJoinRightAssignment :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.join_right_assignment

theorem fixed_sigma_two_conjunction_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaTwoConjunctionRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_two_conjunction_realization

theorem fixed_sigma_two_conjunction_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaTwoConjunctionComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_two_conjunction_complexity

end LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
