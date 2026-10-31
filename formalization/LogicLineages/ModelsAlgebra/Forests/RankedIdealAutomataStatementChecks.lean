module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomataProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.StatementChecks
 theorem closureExact : Targets.ClosureExact := Proof.closureExact
 theorem evaluationExact : Targets.EvaluationExact := Proof.evaluationExact
 theorem runCalibration : Targets.RunCalibration := Proof.runCalibration
 theorem determinizationExact : Targets.DeterminizationExact := Proof.determinizationExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata
