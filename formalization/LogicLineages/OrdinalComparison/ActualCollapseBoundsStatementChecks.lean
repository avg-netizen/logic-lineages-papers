module

public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualFiniteTailClosureNorm : Targets.ActualFiniteTailClosureNorm :=
  actualFiniteTailClosureNorm

theorem fixed_actualCollapseDominatesNorm : Targets.ActualCollapseDominatesNorm :=
  actualCollapseDominatesNorm

theorem fixed_actualCollapseFiniteTailBound : Targets.ActualCollapseFiniteTailBound :=
  actualCollapseFiniteTailBound

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
