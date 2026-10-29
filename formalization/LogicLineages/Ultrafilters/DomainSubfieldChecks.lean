module

public import LogicLineages.Ultrafilters.DomainSubfield
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_domain_subfield : Targets.DomainSubfield := domain_subfield

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
