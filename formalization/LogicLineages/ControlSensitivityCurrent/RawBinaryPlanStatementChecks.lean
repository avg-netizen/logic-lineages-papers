module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanProof
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler.StatementChecks

theorem fixed_trace_exactness : RawBinaryPlanTargets.TraceExactness := trace_exactness
theorem fixed_constant_exactness : RawBinaryPlanTargets.ConstantExactness := constant_exactness
theorem fixed_primitive : RawBinaryPlanTargets.Primitive := primitive

#print axioms fixed_trace_exactness
#print axioms fixed_constant_exactness
#print axioms fixed_primitive

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler.StatementChecks
