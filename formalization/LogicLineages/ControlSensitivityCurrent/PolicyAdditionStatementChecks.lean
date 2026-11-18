module
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyAddition.StatementChecks
theorem fixed_exactAddition : PolicyAdditionTargets.ExactAddition := exactAddition
theorem fixed_exactOne : PolicyAdditionTargets.ExactOne := exactOne
theorem fixed_exactBinaryDAG : PolicyAdditionTargets.ExactBinaryDAG := exactBinaryDAG
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyAddition.StatementChecks
end LogicLineages.ControlSensitivityCurrent.PolicyAddition.StatementChecks
