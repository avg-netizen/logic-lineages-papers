module

public import LogicLineages.OrdinalComparison.CollectedReachableProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedReachableTagDomain : LogicLineages.OrdinalComparison.Targets.CollectedReachableTagDomain :=
  LogicLineages.OrdinalComparison.collectedReachableTagDomain

theorem fixed_collectedAtomInputRegime : LogicLineages.OrdinalComparison.Targets.CollectedAtomInputRegime :=
  LogicLineages.OrdinalComparison.collectedAtomInputRegime

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
