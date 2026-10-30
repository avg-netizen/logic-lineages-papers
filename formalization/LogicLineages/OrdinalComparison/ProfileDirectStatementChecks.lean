module

public import LogicLineages.OrdinalComparison.ProfileDirectProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualUniformProfileDirectGrowth : LogicLineages.OrdinalComparison.Targets.ActualUniformProfileDirectGrowth :=
  LogicLineages.OrdinalComparison.actualUniformProfileDirectGrowth

theorem fixed_fullActualDirectKernelGrowth : LogicLineages.OrdinalComparison.Targets.FullActualDirectKernelGrowth :=
  LogicLineages.OrdinalComparison.fullActualDirectKernelGrowth

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
