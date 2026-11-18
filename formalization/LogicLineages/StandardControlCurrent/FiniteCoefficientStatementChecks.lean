module
public import LogicLineages.StandardControlCurrent.FiniteCoefficientTargets
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.StandardControlCurrent.FiniteCoefficientStatementChecks

theorem full : FiniteCoefficientTargets.FiniteCoefficient :=
  OrdinalComparison.actualFiniteHeadCollapse

#print axioms full

end LogicLineages.StandardControlCurrent.FiniteCoefficientStatementChecks
