module
public import LogicLineages.ModelsAlgebra.PGroups.CloseAllProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.CloseAllStatementChecks
theorem existential : Targets.sigmaCloseAllCorrect := sigma_close_all_correct
theorem universal : Targets.piCloseAllCorrect := pi_close_all_correct
end LogicLineages.ModelsAlgebra.PGroups.CloseAllStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.CloseAllStatementChecks
