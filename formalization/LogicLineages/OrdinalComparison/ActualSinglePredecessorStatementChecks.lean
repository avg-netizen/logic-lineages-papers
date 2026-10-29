module

public import LogicLineages.OrdinalComparison.ActualSinglePredecessor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_single_predecessor_recurrence : Targets.ActualSinglePredecessorRecurrence :=
  actualSinglePredecessorRecurrence

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
