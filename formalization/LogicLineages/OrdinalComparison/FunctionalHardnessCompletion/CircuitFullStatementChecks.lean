module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.StatementChecks

theorem exactAllocation : Targets.ExactAllocation := Proof.exact_allocation
theorem scalarRunSemantics : Targets.ScalarRunSemantics := Proof.scalar_run_semantics
theorem literalRowsForward : Targets.LiteralRowsForward := Proof.literal_rows_forward
theorem literalRowsBackward : Targets.LiteralRowsBackward := Proof.literal_rows_backward
theorem fullCircuitEncoding : CircuitLinear.Targets.FullCircuitEncoding := Proof.full_circuit_encoding

#print axioms exactAllocation
#print axioms scalarRunSemantics
#print axioms literalRowsForward
#print axioms literalRowsBackward
#print axioms fullCircuitEncoding

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.StatementChecks
