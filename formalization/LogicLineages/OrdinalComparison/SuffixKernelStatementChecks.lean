module

public import LogicLineages.OrdinalComparison.SuffixKernelProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSuffixKernelInput : LogicLineages.OrdinalComparison.Targets.ActualSuffixKernelInput :=
  LogicLineages.OrdinalComparison.actualSuffixKernelInput

theorem fixed_actualSuffixKernelTrace : LogicLineages.OrdinalComparison.Targets.ActualSuffixKernelTrace :=
  LogicLineages.OrdinalComparison.actualSuffixKernelTrace

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
