module

public import LogicLineages.OrdinalComparison.AffordableLeadingProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAffordableLeadingMaximum : LogicLineages.OrdinalComparison.Targets.ActualAffordableLeadingMaximum :=
  LogicLineages.OrdinalComparison.actualAffordableLeadingMaximum

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
