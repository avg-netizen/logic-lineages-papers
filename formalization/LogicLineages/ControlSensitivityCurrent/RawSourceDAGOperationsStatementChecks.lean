module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations.StatementChecks
theorem fixed_references : RawSourceDAGOperationsTargets.References := references
theorem fixed_append : RawSourceDAGOperationsTargets.Append := append
theorem fixed_rename : RawSourceDAGOperationsTargets.Rename := rename
theorem fixed_insert : RawSourceDAGOperationsTargets.Insert := insert
theorem fixed_primitive : RawSourceDAGOperationsTargets.Primitive := primitive
#print axioms fixed_references
#print axioms fixed_append
#print axioms fixed_rename
#print axioms fixed_insert
#print axioms fixed_primitive
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations.StatementChecks
