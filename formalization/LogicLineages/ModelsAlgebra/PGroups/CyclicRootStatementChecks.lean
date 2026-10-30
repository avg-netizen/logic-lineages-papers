module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicRoot
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_root_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_evaluation

theorem fixed_cyclic_root_generator : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootGenerator :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_generator

theorem fixed_cyclic_root_order : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootOrder :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_order

theorem fixed_cyclic_root_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_injective

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
