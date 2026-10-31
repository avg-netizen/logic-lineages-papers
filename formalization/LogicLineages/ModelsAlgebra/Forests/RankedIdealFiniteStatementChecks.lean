module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.StatementChecks
 theorem successorsExact : Targets.SuccessorsExact := Proof.successorsExact
 theorem closureExact : Targets.ClosureExact := Proof.closureExact
 theorem evaluationExact : Targets.EvaluationExact := Proof.evaluationExact
 theorem acceptanceExact : Targets.AcceptanceExact := Proof.acceptanceExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite
