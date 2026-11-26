module
public import LogicLineages.ControlSensitivityCurrent.PolicyMatrixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyMatrix.StatementChecks
theorem fixed_gates : PolicyMatrixTargets.Gates := gatesExact
theorem fixed_bind : PolicyMatrixTargets.Bind := bindExact
theorem fixed_matrix : PolicyMatrixTargets.Matrix := matrixExact
theorem fixed_actual_size : PolicyMatrixTargets.ActualSize := linearOverhead
#print axioms fixed_gates
#print axioms fixed_bind
#print axioms fixed_matrix
#print axioms fixed_actual_size
end LogicLineages.ControlSensitivityCurrent.PolicyMatrix.StatementChecks
