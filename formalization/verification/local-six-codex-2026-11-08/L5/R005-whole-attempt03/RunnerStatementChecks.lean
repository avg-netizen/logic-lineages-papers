module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks

theorem all_input_termination : RunnerTargets.AllInputTermination := RunnerProof.allInputTermination
theorem exact_least_stopping : RunnerTargets.ExactLeastStopping := RunnerProof.exactLeastStopping
theorem finite_runner_program : RunnerTargets.FiniteRunnerProgram := RunnerCode.finiteRunnerProgram
theorem least_fuel_program : RunnerTargets.LeastFuelProgram := RunnerCode.leastFuel_computable
theorem exact_single_row_package : RunnerTargets.ExactSingleRowPackage := RunnerProof.exactSingleRowPackage
theorem exact_family_package : RunnerTargets.ExactFamilyPackage := RunnerProof.exactFamilyPackage
theorem actual_family_program : RunnerTargets.ActualFamilyProgram := RunnerCode.actualFamilyProgram
theorem full_ranked_cancellation : ContractTargets.FullRankedCancellation := RunnerProof.fullRankedCancellation

#print axioms all_input_termination
#print axioms exact_least_stopping
#print axioms finite_runner_program
#print axioms least_fuel_program
#print axioms exact_single_row_package
#print axioms exact_family_package
#print axioms actual_family_program
#print axioms full_ranked_cancellation

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks
