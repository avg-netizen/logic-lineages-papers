module
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteTargets
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.StatementChecks
theorem generated_leaves : Targets.GeneratedLeaves := Proof.generatedLeaves
theorem uniform_compiler : Targets.UniformCompiler := Proof.uniformCompiler
theorem actual_gamma_compiler : Targets.ActualGammaCompiler := Proof.actualGammaCompiler
end LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite
