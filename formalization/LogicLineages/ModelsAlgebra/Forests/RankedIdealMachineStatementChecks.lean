module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.StatementChecks
 theorem runCalibration : Targets.RunCalibration := Proof.runCalibration
 theorem languageExact : Targets.LanguageExact := Proof.languageExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine
