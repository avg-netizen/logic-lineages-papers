module
public import LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan.StatementChecks

theorem fixed_original_plan : CurrentMachinePlanTargets.OriginalPlan := original_plan
theorem fixed_pointwise_plan : CurrentMachinePlanTargets.PointwisePlan := pointwise_plan
theorem fixed_compiled_halting : CurrentMachinePlanTargets.CompiledHalting := compiled_halting

#print axioms fixed_original_plan
#print axioms fixed_pointwise_plan
#print axioms fixed_compiled_halting

end LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan.StatementChecks
