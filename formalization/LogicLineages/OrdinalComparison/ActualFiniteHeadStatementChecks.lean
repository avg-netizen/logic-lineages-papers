module

public import LogicLineages.OrdinalComparison.ActualFiniteHead
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualFiniteHeadNorm : Targets.ActualFiniteHeadNorm :=
  actualFiniteHeadNorm

theorem fixed_actualFiniteHeadMaximum : Targets.ActualFiniteHeadMaximum :=
  actualFiniteHeadMaximum

theorem fixed_actualFiniteHeadCollapse : Targets.ActualFiniteHeadCollapse :=
  actualFiniteHeadCollapse

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
