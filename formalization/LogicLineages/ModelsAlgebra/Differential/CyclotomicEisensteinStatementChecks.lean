module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicEisenstein
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_cyclotomicPrimeIrreducible : Targets.cyclotomicPrimeIrreducible :=
  CyclotomicFamily.prime_irreducible

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
