module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicGeometric
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_cyclotomicGeometricCoefficients : Targets.cyclotomicGeometricCoefficients :=
  CyclotomicFamily.geometric_coefficients

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
