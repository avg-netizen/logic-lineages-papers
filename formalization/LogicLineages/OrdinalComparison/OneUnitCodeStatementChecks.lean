module
public import LogicLineages.OrdinalComparison.OneUnitCodeTargets
public import LogicLineages.OrdinalComparison.OneUnitCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode.StatementChecks
theorem exact_literal_syntax : Targets.ExactLiteralSyntax := Proof.exactLiteralSyntax
theorem exact_compiler : Targets.ExactCompiler := Proof.exactCompiler
theorem primitive_recursive_algorithms : Targets.PrimitiveRecursiveAlgorithms := Proof.primitiveRecursiveAlgorithms
theorem actual_compiler_totality : Targets.ActualCompilerTotality := Proof.actualCompilerTotality
end LogicLineages.OrdinalComparison.Source.OneUnitCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.OneUnitCode
