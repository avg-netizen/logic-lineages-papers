module

public import LogicLineages.Ultrafilters.DomainCorollary
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_domain_corollary : Targets.DomainCorollary := domain_corollary

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
