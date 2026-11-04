module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.StatementChecks
theorem exact_ports : Targets.ExactPorts := Proof.exactPorts
theorem exact_expressions : Targets.ExactExpressions := Proof.exactExpressions
theorem exact_forests : Targets.ExactForests := Proof.exactForests
theorem uniform_primitive_recursive : Targets.UniformPrimitiveRecursive := Proof.uniformPrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode
