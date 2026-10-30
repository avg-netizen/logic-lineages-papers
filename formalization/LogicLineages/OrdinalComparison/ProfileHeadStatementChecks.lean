module

public import LogicLineages.OrdinalComparison.ProfileHeadProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualFixedLimitProfileHeads : LogicLineages.OrdinalComparison.Targets.ActualFixedLimitProfileHeads :=
  LogicLineages.OrdinalComparison.actualFixedLimitProfileHeads

theorem fixed_actualOmegaProfileHead : LogicLineages.OrdinalComparison.Targets.ActualOmegaProfileHead :=
  LogicLineages.OrdinalComparison.actualOmegaProfileHead

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
