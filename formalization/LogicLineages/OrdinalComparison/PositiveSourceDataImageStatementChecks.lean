module
public import LogicLineages.OrdinalComparison.PositiveSourceDataImageProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.PositiveSourceDomain.StatementChecks

theorem fixed_data_image : Targets.PositiveSourceDataImage := data_image

end LogicLineages.OrdinalComparison.PositiveSourceDomain.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.PositiveSourceDomain
