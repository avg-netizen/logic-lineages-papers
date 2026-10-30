module

public import LogicLineages.OrdinalComparison.RepeatedWordOrderProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualRepeatedWordWeakOrder : LogicLineages.OrdinalComparison.Targets.ActualRepeatedWordWeakOrder :=
  LogicLineages.OrdinalComparison.actualRepeatedWordWeakOrder

theorem fixed_actualRepeatedWordStrictInput : LogicLineages.OrdinalComparison.Targets.ActualRepeatedWordStrictInput :=
  LogicLineages.OrdinalComparison.actualRepeatedWordStrictInput

theorem fixed_actualRepeatedWordStrictMass : LogicLineages.OrdinalComparison.Targets.ActualRepeatedWordStrictMass :=
  LogicLineages.OrdinalComparison.actualRepeatedWordStrictMass

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
