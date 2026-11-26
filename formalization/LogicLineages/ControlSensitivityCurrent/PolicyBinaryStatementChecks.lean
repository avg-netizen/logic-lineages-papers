module
public import LogicLineages.ControlSensitivityCurrent.PolicyBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyBinary.StatementChecks
theorem fixed_rename : PolicyBinaryTargets.Rename := renameCorrect
theorem fixed_binary : PolicyBinaryTargets.Binary := binaryCorrect
theorem fixed_literal : PolicyBinaryTargets.Literal := literalCorrect
theorem fixed_actual_counts : PolicyBinaryTargets.ActualCounts := actualCounts
#print axioms fixed_rename
#print axioms fixed_binary
#print axioms fixed_literal
#print axioms fixed_actual_counts
end LogicLineages.ControlSensitivityCurrent.PolicyBinary.StatementChecks
