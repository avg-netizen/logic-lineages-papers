module

public import LogicLineages.OrdinalComparison.CollectedMergeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedTagInsertValue : LogicLineages.OrdinalComparison.Targets.CollectedTagInsertValue :=
  LogicLineages.OrdinalComparison.collectedTagInsertValue

theorem fixed_collectedTagInsertValid : LogicLineages.OrdinalComparison.Targets.CollectedTagInsertValid :=
  LogicLineages.OrdinalComparison.collectedTagInsertValid

theorem fixed_collectedTagsMergeCorrect : LogicLineages.OrdinalComparison.Targets.CollectedTagsMergeCorrect :=
  LogicLineages.OrdinalComparison.collectedTagsMergeCorrect

theorem fixed_collectedPositiveAddCorrect : LogicLineages.OrdinalComparison.Targets.CollectedPositiveAddCorrect :=
  LogicLineages.OrdinalComparison.collectedPositiveAddCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
