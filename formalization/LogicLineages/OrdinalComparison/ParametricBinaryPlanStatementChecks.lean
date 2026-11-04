module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanTargets
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.StatementChecks
theorem exact_renaming : Targets.ExactRenaming := Proof.exactRenaming
theorem exact_binary_plan : Targets.ExactBinaryPlan := Proof.exactBinaryPlan
theorem actual_gamma_literal_compilation : Targets.ActualGammaLiteralCompilation := Proof.actualGammaLiteralCompilation
theorem exact_compiled_bounds : Targets.ExactCompiledBounds := Proof.exactCompiledBounds
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan
