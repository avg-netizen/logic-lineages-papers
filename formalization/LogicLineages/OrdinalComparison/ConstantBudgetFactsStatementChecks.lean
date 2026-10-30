module
public import LogicLineages.OrdinalComparison.ConstantBudgetFactsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualExactNormPredecessorsMembership : Targets.ActualExactNormPredecessorsMembership :=
  actualExactNormPredecessorsMembership
theorem fixed_actualEqualNormBelowLimitPart : Targets.ActualEqualNormBelowLimitPart :=
  actualEqualNormBelowLimitPart

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
