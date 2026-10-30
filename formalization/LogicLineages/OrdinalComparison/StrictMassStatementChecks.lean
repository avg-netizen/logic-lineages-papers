module

public import LogicLineages.OrdinalComparison.StrictMassProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPrincipalKernelStrictMass : LogicLineages.OrdinalComparison.Targets.ActualPrincipalKernelStrictMass :=
  LogicLineages.OrdinalComparison.actualPrincipalKernelStrictMass

theorem fixed_fullActualPrincipalStrictMass : LogicLineages.OrdinalComparison.Targets.FullActualPrincipalStrictMass :=
  LogicLineages.OrdinalComparison.fullActualPrincipalStrictMass

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
