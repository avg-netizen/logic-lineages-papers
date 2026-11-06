module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerTargets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerSemanticsProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProgramsProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.LeastFuelProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerStatementChecks

theorem fixed_admissionCorrect : RunnerTargets.AdmissionCorrect := RunnerProof.admissionCorrect
theorem fixed_runEquations : RunnerTargets.RunEquations := RunnerProof.runEquations
theorem fixed_runBounds : RunnerTargets.RunBounds := RunnerProof.runBounds
theorem fixed_dispatchCoverage : RunnerTargets.DispatchCoverage := RunnerProof.dispatchCoverage
theorem fixed_runAdmission : RunnerTargets.RunAdmission := RunnerProof.runAdmission
theorem fixed_runTieBound : RunnerTargets.RunTieBound := RunnerProof.runTieBound
theorem fixed_traceDomains : RunnerTargets.TraceDomains := RunnerProof.traceDomains
theorem fixed_accumulatedComparison : RunnerTargets.AccumulatedComparison := RunnerProof.accumulatedComparison
theorem fixed_runnerTerminates : RunnerTargets.RunnerTerminates := RunnerProof.runnerTerminates
theorem fixed_terminalStability : RunnerTargets.TerminalStability := RunnerProof.terminalStability
theorem fixed_leastFuelCorrect : RunnerTargets.LeastFuelCorrect := RunnerProof.leastFuelCorrect
theorem fixed_runnerPrograms : RunnerTargets.RunnerPrograms := RunnerProgramsProof.runnerPrograms
theorem fixed_leastFuelProgram : RunnerTargets.LeastFuelProgram := LeastFuelProgramsProof.leastFuelProgram

#print axioms fixed_admissionCorrect
#print axioms fixed_runEquations
#print axioms fixed_runBounds
#print axioms fixed_dispatchCoverage
#print axioms fixed_runAdmission
#print axioms fixed_runTieBound
#print axioms fixed_traceDomains
#print axioms fixed_accumulatedComparison
#print axioms fixed_runnerTerminates
#print axioms fixed_terminalStability
#print axioms fixed_leastFuelCorrect
#print axioms fixed_runnerPrograms
#print axioms fixed_leastFuelProgram

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerStatementChecks
