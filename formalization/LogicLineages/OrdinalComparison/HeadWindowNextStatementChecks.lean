module
public import LogicLineages.OrdinalComparison.HeadWindowNextProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLeastNextLimit : Targets.ActualLeastNextLimit := actualLeastNextLimit
theorem fixed_actualNextLimitHeadFacts : Targets.ActualNextLimitHeadFacts := actualNextLimitHeadFacts
theorem fixed_actualCommonNormHeadOrder : Targets.ActualCommonNormHeadOrder := actualCommonNormHeadOrder

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
