module

public import LogicLineages.Ultrafilters.DomainDerivation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_domain_derivation : Targets.DomainDerivation := domain_derivation

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
