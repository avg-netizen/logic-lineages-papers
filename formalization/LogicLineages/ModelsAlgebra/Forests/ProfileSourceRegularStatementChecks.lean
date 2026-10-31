module
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.StatementChecks

theorem sourceMachineCorrect : Targets.SourceMachineCorrect := Proof.sourceMachineCorrect

theorem generalForbiddenRegular : Targets.GeneralForbiddenRegular := Proof.generalForbiddenRegular

end LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular
