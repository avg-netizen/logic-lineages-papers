module
public import LogicLineages.OrdinalComparison.WWPolicyGeneratedProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPolicyGeneratedPartial : Source.Targets.ActualPolicyGeneratedPartial :=
  Source.LiteralPolicy.actualPolicyGeneratedPartial

theorem fixed_actualPolicyGeneratedAbstraction : Source.Targets.ActualPolicyGeneratedAbstraction :=
  Source.LiteralPolicy.actualPolicyGeneratedAbstraction

theorem fixed_actualPolicyGeneratedAssignment : Source.Targets.ActualPolicyGeneratedAssignment :=
  Source.LiteralPolicy.actualPolicyGeneratedAssignment

theorem fixed_actualPolicyGroundPositiveClosed : Source.Targets.ActualPolicyGroundPositiveClosed :=
  Source.LiteralPolicy.actualPolicyGroundPositiveClosed

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
