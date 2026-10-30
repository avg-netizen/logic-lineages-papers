module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicDirectSum
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_root_sum_single : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumSingle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_single

theorem fixed_cyclic_root_sum_exponent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumExponent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_exponent

theorem fixed_cyclic_socle_coefficients_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicSocleCoefficientsInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_socle_coefficients_injective

theorem fixed_cyclic_socle_coefficients_range : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicSocleCoefficientsRange :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_socle_coefficients_range

theorem fixed_cyclic_root_sum_socle_composition : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumSocleComposition :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_socle_composition

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
