module

public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOmegaMaximum : LogicLineages.OrdinalComparison.Targets.ActualOmegaMaximum :=
  LogicLineages.OrdinalComparison.actualOmegaMaximum

theorem fixed_actualOmegaSquaredMaximum : LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredMaximum :=
  LogicLineages.OrdinalComparison.actualOmegaSquaredMaximum

theorem fixed_actualExpansiveControlLinearCount : LogicLineages.OrdinalComparison.Targets.ActualExpansiveControlLinearCount :=
  LogicLineages.OrdinalComparison.actualExpansiveControlLinearCount

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
