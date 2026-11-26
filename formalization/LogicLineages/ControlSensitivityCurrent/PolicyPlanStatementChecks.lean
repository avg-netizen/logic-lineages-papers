module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan.StatementChecks
theorem fixed_equationNaturality : PolicyPlanTargets.EquationNaturality := equationNaturality
theorem fixed_compilation : PolicyPlanTargets.Compilation := compilation
theorem fixed_actualSize : PolicyPlanTargets.ActualSize := actualSize
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan.StatementChecks
end LogicLineages.ControlSensitivityCurrent.PolicyPlan.StatementChecks
