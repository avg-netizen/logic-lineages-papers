module

public import LogicLineages.OrdinalComparison.CollectedFiniteClosureProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedFiniteClosureDomain : LogicLineages.OrdinalComparison.Targets.CollectedFiniteClosureDomain :=
  LogicLineages.OrdinalComparison.collectedFiniteClosureDomain

theorem fixed_collectedDirectChildHeight : LogicLineages.OrdinalComparison.Targets.CollectedDirectChildHeight :=
  LogicLineages.OrdinalComparison.collectedDirectChildHeight

theorem fixed_collectedDirectTagReachable : LogicLineages.OrdinalComparison.Targets.CollectedDirectTagReachable :=
  LogicLineages.OrdinalComparison.collectedDirectTagReachable

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
