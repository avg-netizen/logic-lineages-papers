module
public import LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.StatementChecks

theorem emptyInputCorrect : Targets.EmptyInputCorrect := Proof.emptyInputCorrect

theorem emptyForbiddenCase : Targets.EmptyForbiddenCase := Proof.emptyForbiddenCase

theorem emptyLanguageCase : Targets.EmptyLanguageCase := Proof.emptyLanguageCase

theorem exceptionSound : Targets.ExceptionSound := Proof.exceptionSound

end LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision
