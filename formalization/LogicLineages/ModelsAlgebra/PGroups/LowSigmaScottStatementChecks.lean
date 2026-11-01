module
public import LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottStatementChecks
theorem zero : Targets.primaryNoRawSigmaZero := primary_no_raw_sigma_zero
theorem one : Targets.primaryNoRawSigmaOne := primary_no_raw_sigma_one
theorem twoLowering : Targets.primaryRawSigmaTwoLowering := primary_raw_sigma_two_lowering
end LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottStatementChecks
