module
public import LogicLineages.OrdinalComparison.ConstantCutPeriodProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualConstantBudgetCutPeriod : Targets.ActualConstantBudgetCutPeriod :=
  actualConstantBudgetCutPeriod

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
