module

public import LogicLineages.ModelsAlgebra.PGroups.SigmaThreeReflection
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_pi_two_parameterized_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiTwoParameterizedReflection :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_two_parameterized_reflection

theorem fixed_sigma_three_stage_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaThreeStageReflection :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_three_stage_reflection

theorem fixed_chain_no_sigma_three_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupChainNoSigmaThreeScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.chain_no_sigma_three_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
