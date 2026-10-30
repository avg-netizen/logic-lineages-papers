module

public import LogicLineages.OrdinalComparison.KernelMassKeyProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPrincipalKernelMassKey : LogicLineages.OrdinalComparison.Targets.ActualPrincipalKernelMassKey :=
  LogicLineages.OrdinalComparison.actualPrincipalKernelMassKey

theorem fixed_actualPrincipalKernelMassCompare : LogicLineages.OrdinalComparison.Targets.ActualPrincipalKernelMassCompare :=
  LogicLineages.OrdinalComparison.actualPrincipalKernelMassCompare

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
