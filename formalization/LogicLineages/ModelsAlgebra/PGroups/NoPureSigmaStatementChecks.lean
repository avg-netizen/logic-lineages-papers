module
public import LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaStatementChecks
theorem evenLowering : Targets.primaryEvenSigmaLowering := primary_even_sigma_lowering
theorem fullNoPureSigma : Targets.primaryAllSigmaLowering := primary_all_sigma_lowering
end LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaStatementChecks
