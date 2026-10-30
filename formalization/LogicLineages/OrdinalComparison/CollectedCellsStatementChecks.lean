module

public import LogicLineages.OrdinalComparison.CollectedCellsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualCollectedSignedCells : LogicLineages.OrdinalComparison.Targets.ActualCollectedSignedCells :=
  LogicLineages.OrdinalComparison.actualCollectedSignedCells

theorem fixed_fullActualCollectedCells : LogicLineages.OrdinalComparison.Targets.FullActualCollectedCells :=
  LogicLineages.OrdinalComparison.fullActualCollectedCells

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
