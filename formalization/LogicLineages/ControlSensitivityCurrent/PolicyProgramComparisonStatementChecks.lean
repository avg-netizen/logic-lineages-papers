module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramComparison.StatementChecks
theorem fixed_pointwise : PolicyProgramComparisonTargets.Pointwise := pointwise
theorem fixed_comparison : PolicyProgramComparisonTargets.Comparison := comparison
theorem fixed_wrapper_syntax : PolicyProgramComparisonTargets.WrapperSyntax := wrapperSyntax
theorem fixed_output_sizes : PolicyProgramComparisonTargets.OutputSizes := outputSizes
#print axioms fixed_pointwise
#print axioms fixed_comparison
#print axioms fixed_wrapper_syntax
#print axioms fixed_output_sizes
end LogicLineages.ControlSensitivityCurrent.PolicyProgramComparison.StatementChecks
