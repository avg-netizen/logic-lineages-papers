module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionKernel
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_prime_extension_kernel : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeExtensionKernel :=
  LogicLineages.ModelsAlgebra.PGroups.prime_extension_kernel

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
