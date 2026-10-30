module

public import LogicLineages.OrdinalComparison.PeakWordProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualPrincipalPeakWord : LogicLineages.OrdinalComparison.Targets.FullActualPrincipalPeakWord :=
  LogicLineages.OrdinalComparison.fullActualPrincipalPeakWord

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
