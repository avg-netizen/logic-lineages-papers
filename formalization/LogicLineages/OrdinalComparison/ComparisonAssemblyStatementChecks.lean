module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyLayerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonAssembly.StatementChecks

theorem fixed_node_program : Targets.ActualComparisonQueryNodeProgram := node_program
theorem fixed_node_correct : Targets.ActualComparisonQueryNodeCorrect := node_correct
theorem fixed_programs : Targets.ActualComparisonQueryAssemblyPrograms := assembly_programs
theorem fixed_result_correct : Targets.ActualComparisonQueryResultCorrect := result_correct
theorem fixed_full : Targets.FullActualComparisonQueryAssembly := full

#print axioms fixed_node_program
#print axioms fixed_node_correct
#print axioms fixed_programs
#print axioms fixed_result_correct
#print axioms fixed_full

end LogicLineages.OrdinalComparison.ComparisonAssembly.StatementChecks
