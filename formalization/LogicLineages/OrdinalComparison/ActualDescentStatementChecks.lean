module

public import LogicLineages.OrdinalComparison.ActualDescent
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualNonfiniteDecomposition : Targets.ActualNonfiniteDecomposition :=
  actualNonfiniteDecomposition

theorem fixed_actualDescentStepStrict : Targets.ActualDescentStepStrict :=
  actualDescentStepStrict

theorem fixed_actualDescentStepCollapse : Targets.ActualDescentStepCollapse :=
  actualDescentStepCollapse

theorem fixed_actualDescentStepNorm : Targets.ActualDescentStepNorm :=
  actualDescentStepNorm

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
