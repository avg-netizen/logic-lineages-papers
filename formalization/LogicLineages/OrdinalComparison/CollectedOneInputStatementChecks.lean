module

public import LogicLineages.OrdinalComparison.CollectedOneInputProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualCollectedOneInput : LogicLineages.OrdinalComparison.Targets.FullActualCollectedOneInput :=
  LogicLineages.OrdinalComparison.fullActualCollectedOneInput

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
