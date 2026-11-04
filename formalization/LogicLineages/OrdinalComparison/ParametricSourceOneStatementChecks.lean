module
public import LogicLineages.OrdinalComparison.ParametricSourceOneTargets
public import LogicLineages.OrdinalComparison.ParametricSourceOneProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceOne.StatementChecks
theorem identity_source_equation : Targets.IdentitySourceEquation := Proof.identitySourceEquation
theorem exact_one : Targets.ExactOne := Proof.exactOne
theorem actual_gamma_one : Targets.ActualGammaOne := Proof.actualGammaOne
end LogicLineages.OrdinalComparison.Source.ParametricSourceOne.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricSourceOne
