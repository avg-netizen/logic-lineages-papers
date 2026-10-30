module
public import LogicLineages.OrdinalComparison.HeadCompleteCountProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualHeadInputFacts : Targets.ActualHeadInputFacts := actualHeadInputFacts
theorem fixed_actualHeadCompleteCount : Targets.ActualHeadCompleteCount := actualHeadCompleteCount
theorem fixed_fullActualHeadCompleteCount : Targets.FullActualHeadCompleteCount := fullActualHeadCompleteCount

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
