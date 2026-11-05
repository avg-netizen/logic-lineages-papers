module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeRowsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitBridgeStatementChecks
open CircuitBridgeTargets

theorem fixedExpressionMeaning : ExpressionMeaning :=
  fun n x d => CircuitLinear.Proof.expression_toFinsupp (n := n) x d
theorem fixedRowMeaning : RowMeaning := CircuitLinear.Proof.row_interpret
theorem fixedRawSystemFaithful : RawSystemFaithful := CircuitLinear.Proof.raw_system_faithful
theorem fixedCircuitSystemWellFormed : CircuitSystemWellFormed := CircuitLinear.Proof.circuit_system_wellFormed

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitBridgeStatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitBridgeStatementChecks
