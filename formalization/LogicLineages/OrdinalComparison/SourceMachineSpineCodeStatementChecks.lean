module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.StatementChecks
theorem exact_spine : Targets.ExactSpine := Proof.exactSpine
theorem exact_outputs : Targets.ExactOutputs := Proof.exactOutputs
theorem uniform_primitive_recursive : Targets.UniformPrimitiveRecursive := Proof.uniformPrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode
