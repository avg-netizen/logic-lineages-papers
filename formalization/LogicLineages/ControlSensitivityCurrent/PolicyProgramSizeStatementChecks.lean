module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramSizeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramSize.StatementChecks
theorem fixed_copied_load : PolicyProgramSizeTargets.CopiedLoad := copiedLoad
theorem fixed_lower_counts : PolicyProgramSizeTargets.LowerCounts := lowerCounts
theorem fixed_forest_load_counts : PolicyProgramSizeTargets.ForestLoadCounts := forestLoadCounts
theorem fixed_forest_code_counts : PolicyProgramSizeTargets.ForestCodeCounts := forestCodeCounts
#print axioms fixed_copied_load
#print axioms fixed_lower_counts
#print axioms fixed_forest_load_counts
#print axioms fixed_forest_code_counts
end LogicLineages.ControlSensitivityCurrent.PolicyProgramSize.StatementChecks
