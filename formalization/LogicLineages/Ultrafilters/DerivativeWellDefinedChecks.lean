module

public import LogicLineages.Ultrafilters.DerivativeWellDefined
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_derivative_well_defined : Targets.DerivativeWellDefined :=
  derivative_well_defined

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
