module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanTargets
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.StatementChecks
theorem supported_syntax : Targets.SupportedSyntax := Proof.supportedSyntax
theorem exact_conjunction : Targets.ExactConjunction := Proof.exactConjunction
theorem exact_compiled_halting : Targets.ExactCompiledHalting := Proof.exactCompiledHalting
theorem exact_compiled_bounds : Targets.ExactCompiledBounds := Proof.exactCompiledBounds
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan
