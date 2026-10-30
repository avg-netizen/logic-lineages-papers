module
public import LogicLineages.OrdinalComparison.ThetaEntryProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualThetaEntryWitness : Targets.ActualThetaEntryWitness := actualThetaEntryWitness
theorem fixed_fullActualThetaEntry : Targets.FullActualThetaEntry := fullActualThetaEntry

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
