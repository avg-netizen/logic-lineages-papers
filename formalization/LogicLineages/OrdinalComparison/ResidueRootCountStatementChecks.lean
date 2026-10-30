module

public import LogicLineages.OrdinalComparison.ResidueRootCountProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualResidueSmallExponentNonfixed : LogicLineages.OrdinalComparison.Targets.ActualResidueSmallExponentNonfixed :=
  LogicLineages.OrdinalComparison.actualResidueSmallExponentNonfixed

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
