module

public import LogicLineages.OrdinalComparison.ProfileReserveProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualEffectiveProfileReserve : LogicLineages.OrdinalComparison.Targets.FullActualEffectiveProfileReserve :=
  LogicLineages.OrdinalComparison.fullActualEffectiveProfileReserve

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
