module

public import LogicLineages.OrdinalComparison.CollectedRangeCellsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedRangeCellTests : LogicLineages.OrdinalComparison.Targets.CollectedRangeCellTests :=
  LogicLineages.OrdinalComparison.collectedRangeCellTests

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
