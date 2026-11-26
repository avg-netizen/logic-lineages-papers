module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchStatementChecks
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineCorrectnessProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineLeastProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStatementChecks

theorem exact_constant_evaluation : MachineTargets.ExactConstantEvaluation :=
  ConstantLeafProof.exactConstantEvaluation

theorem all_input_termination : MachineTargets.AllInputTermination :=
  MachineProof.allInputTermination

theorem exact_least_stopping : MachineTargets.ExactLeastStopping :=
  MachineProof.exactLeastStopping

theorem actual_transition_programs : MachineTargets.ActualTransitionPrograms :=
  MachinePrograms.actualTransitionPrograms

theorem exact_finite_depth : MachineTargets.ExactFiniteDepth :=
  MachineProof.exactFiniteDepth

theorem adequate_fuel_correctness : MachineTargets.AdequateFuelCorrectness :=
  MachineProof.adequateFuelCorrectness

theorem uniform_numeric_solver : MachineTargets.UniformNumericSolver :=
  MachinePrograms.uniformNumericSolver

theorem actual_closed_decision : MachineTargets.ActualClosedDecision :=
  MachineProof.actualClosedDecision

/-- The concrete closed existential solver, with joint numeric computability
and the original global-domain semantics, at the frozen paper statement. -/
theorem full_closed_existential_word_arithmetic : MachineTargets.FullClosedExistentialWordArithmetic :=
  ⟨Machine.solve,MachinePrograms.solve_computable,MachineProof.actualClosedDecision⟩

#print axioms exact_constant_evaluation
#print axioms all_input_termination
#print axioms exact_least_stopping
#print axioms actual_transition_programs
#print axioms exact_finite_depth
#print axioms adequate_fuel_correctness
#print axioms uniform_numeric_solver
#print axioms actual_closed_decision
#print axioms full_closed_existential_word_arithmetic

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStatementChecks
