module

public import LogicLineages.OrdinalComparison.BinarySourceProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualSourceZeroProperNumerator : LogicLineages.OrdinalComparison.Targets.ActualSourceZeroProperNumerator :=
  LogicLineages.OrdinalComparison.actualSourceZeroProperNumerator

theorem fixed_actualSourceBinaryMatrix : LogicLineages.OrdinalComparison.Targets.ActualSourceBinaryMatrix :=
  LogicLineages.OrdinalComparison.actualSourceBinaryMatrix

theorem fixed_actualSourceBinaryObservability : LogicLineages.OrdinalComparison.Targets.ActualSourceBinaryObservability :=
  LogicLineages.OrdinalComparison.actualSourceBinaryObservability

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
