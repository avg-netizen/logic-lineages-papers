module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneDivision
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks
universe u

theorem fixed_radicalDerivativeDivisibility : Targets.radicalDerivativeDivisibility :=
  OrderOneDivision.radicalDerivativeDivisibility
theorem fixed_orderOneDivisionCriterion : Targets.orderOneDivisionCriterion.{u} :=
  OrderOneDivision.orderOneDivisionCriterion

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
