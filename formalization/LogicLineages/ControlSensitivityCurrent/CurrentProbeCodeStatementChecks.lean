module
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentProbeCode.StatementChecks
theorem fixed_closing : CurrentProbeCodeTargets.ExactClosing := exactClosing
theorem fixed_probe : CurrentProbeCodeTargets.ExactProbe := exactProbe
theorem fixed_effective : CurrentProbeCodeTargets.Effective := effective
#audit_namespace LogicLineages.ControlSensitivityCurrent.CurrentProbeCode.StatementChecks
end LogicLineages.ControlSensitivityCurrent.CurrentProbeCode.StatementChecks
