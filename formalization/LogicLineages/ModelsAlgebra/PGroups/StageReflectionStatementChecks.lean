module

public import LogicLineages.ModelsAlgebra.PGroups.StageReflection
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_pi_two_tuple_retract_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiTwoTupleRetractReflection :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_two_tuple_retract_reflection

theorem fixed_difference_two_stage_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupDifferenceTwoStageReflection :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.difference_two_stage_reflection

theorem fixed_chain_no_difference_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupChainNoDifferenceTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.chain_no_difference_two_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
