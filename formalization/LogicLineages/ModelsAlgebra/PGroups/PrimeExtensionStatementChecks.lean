module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_prime_order_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeOrderExtension :=
  LogicLineages.ModelsAlgebra.PGroups.prime_order_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
