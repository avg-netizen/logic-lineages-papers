module

public import LogicLineages.OrdinalComparison.LinkedResidueProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLinkedBudgetExponent : LogicLineages.OrdinalComparison.Targets.ActualLinkedBudgetExponent :=
  LogicLineages.OrdinalComparison.actualLinkedBudgetExponent

theorem fixed_actualLinkedResidueArithmetic : LogicLineages.OrdinalComparison.Targets.ActualLinkedResidueArithmetic :=
  LogicLineages.OrdinalComparison.actualLinkedResidueArithmetic

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
