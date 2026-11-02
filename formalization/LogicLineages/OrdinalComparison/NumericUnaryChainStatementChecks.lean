module
public import LogicLineages.OrdinalComparison.NumericUnaryChainTargets
public import LogicLineages.OrdinalComparison.NumericUnaryChainProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain.StatementChecks
theorem exact_merged_payloads : Targets.ExactMergedPayloads := Proof.exactMergedPayloads
theorem exact_single_lambda : Targets.ExactSingleLambda := Proof.exactSingleLambda
theorem primitive_recursive_algorithms : Targets.PrimitiveRecursiveAlgorithms := Proof.primitiveRecursiveAlgorithms
theorem actual_compiled_chain : Targets.ActualCompiledChain := Proof.actualCompiledChain
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain
