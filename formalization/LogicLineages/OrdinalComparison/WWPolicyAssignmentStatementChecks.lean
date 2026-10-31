module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLeftPolicyPartialCalibration :
    Source.Targets.ActualLeftPolicyPartialCalibration := Source.LiteralPolicy.actualLeftPolicyPartialCalibration

theorem fixed_actualClosedSourcePolicySeparation :
    Source.Targets.ActualClosedSourcePolicySeparation := Source.LiteralPolicy.actualClosedSourcePolicySeparation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
