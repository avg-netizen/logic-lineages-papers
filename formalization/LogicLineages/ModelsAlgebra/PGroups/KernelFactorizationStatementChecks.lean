module

public import LogicLineages.ModelsAlgebra.PGroups.KernelFactorization
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_kernel_factorization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupKernelFactorization :=
  LogicLineages.ModelsAlgebra.PGroups.kernel_factorization

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
