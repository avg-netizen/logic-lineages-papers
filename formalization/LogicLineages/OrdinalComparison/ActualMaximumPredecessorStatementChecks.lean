module

public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_maximum_correct :
    Targets.ActualMaximumPredecessorCorrect actualMaximumPredecessor :=
  actualMaximumPredecessor_correct

theorem fixed_actual_maximum_unique :
    Targets.ActualMaximumPredecessorUnique actualMaximumPredecessor :=
  actualMaximumPredecessor_unique

theorem fixed_actual_maximum_notation_correspondence :
    Targets.ActualMaximumPredecessorNotationCorrespondence actualMaximumPredecessor :=
  actualMaximumPredecessor_notationCorrespondence

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
