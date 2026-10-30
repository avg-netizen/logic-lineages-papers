module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicPromise
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_cyclotomicPrimeSpectralPromise : Targets.cyclotomicPrimeSpectralPromise :=
  CyclotomicFamily.prime_spectral_promise
theorem fixed_cyclotomicOrdersUnbounded : Targets.cyclotomicOrdersUnbounded :=
  CyclotomicFamily.orders_unbounded

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
