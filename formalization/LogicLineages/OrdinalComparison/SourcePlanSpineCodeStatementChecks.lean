module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.StatementChecks
theorem exact_compilation : Targets.ExactCompilation := Proof.exactCompilation
theorem exact_aggregate : Targets.ExactAggregate := Proof.exactAggregate
theorem uniform_primitive_recursive : Targets.UniformPrimitiveRecursive := Proof.uniformPrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode
