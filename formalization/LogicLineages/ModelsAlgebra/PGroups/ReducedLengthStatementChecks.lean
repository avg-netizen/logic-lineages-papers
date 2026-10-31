module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.ReducedLengthStatementChecks
theorem leastStage : Targets.countableReducedExactLength := countable_reduced_exact_length
theorem normalForm : Targets.countableLengthNormalForm := countable_length_normal_form
theorem terminalBound : Targets.exactLengthTerminalBound := exact_length_terminal_bound
end LogicLineages.ModelsAlgebra.PGroups.ReducedLengthStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.ReducedLengthStatementChecks
