module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineFiniteDepthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStructuralChecks

theorem all_input_termination : MachineTargets.AllInputTermination :=
  MachineProof.allInputTermination

theorem exact_least_stopping : MachineTargets.ExactLeastStopping :=
  MachineProof.exactLeastStopping

theorem exact_finite_depth : MachineTargets.ExactFiniteDepth :=
  MachineProof.exactFiniteDepth

#print axioms all_input_termination
#print axioms exact_least_stopping
#print axioms exact_finite_depth

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStructuralChecks

#audit_namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineStructuralChecks
