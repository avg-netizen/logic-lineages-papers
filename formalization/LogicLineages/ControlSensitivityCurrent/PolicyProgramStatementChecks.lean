module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgram.StatementChecks
theorem fixed_observations : PolicyProgramTargets.Observations := observations
theorem fixed_observation_binder : PolicyProgramTargets.ObservationBinder := observationBinder
theorem fixed_lowering : PolicyProgramTargets.Lowering := lowering
theorem fixed_forest : PolicyProgramTargets.Forest := forest
#print axioms fixed_observations
#print axioms fixed_observation_binder
#print axioms fixed_lowering
#print axioms fixed_forest
end LogicLineages.ControlSensitivityCurrent.PolicyProgram.StatementChecks
