module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeCoset
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_prime_coset_order : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeCosetOrder :=
  LogicLineages.ModelsAlgebra.PGroups.prime_coset_order

theorem fixed_prime_coset_integer_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeCosetIntegerMembership :=
  LogicLineages.ModelsAlgebra.PGroups.prime_coset_integer_membership

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
