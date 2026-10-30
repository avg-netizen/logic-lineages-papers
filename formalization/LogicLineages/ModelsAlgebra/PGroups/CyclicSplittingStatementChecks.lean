module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSplitting
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_cyclic_retraction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedCyclicRetraction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_cyclic_retraction

theorem fixed_retraction_kernel_product : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRetractionKernelProduct :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.retraction_kernel_product

theorem fixed_maximal_cyclic_splitting : LogicLineages.ModelsAlgebra.PGroups.Targets.groupMaximalCyclicSplitting :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.maximal_cyclic_splitting

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
