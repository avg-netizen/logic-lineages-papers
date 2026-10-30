module

public import LogicLineages.OrdinalComparison.SmallKernelsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPhiEven : LogicLineages.OrdinalComparison.Targets.ActualPhiEven :=
  LogicLineages.OrdinalComparison.actualPhiEven

theorem fixed_actualOmegaSuffixKernel : LogicLineages.OrdinalComparison.Targets.ActualOmegaSuffixKernel :=
  LogicLineages.OrdinalComparison.actualOmegaSuffixKernel

theorem fixed_actualOmegaSquaredSuffixCount : LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredSuffixCount :=
  LogicLineages.OrdinalComparison.actualOmegaSquaredSuffixCount

theorem fixed_actualOmegaSquaredMassClasses : LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredMassClasses :=
  LogicLineages.OrdinalComparison.actualOmegaSquaredMassClasses

theorem fixed_fullActualSmallPrincipalKernels : LogicLineages.OrdinalComparison.Targets.FullActualSmallPrincipalKernels :=
  LogicLineages.OrdinalComparison.fullActualSmallPrincipalKernels

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
