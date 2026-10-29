module

public import LogicLineages.Ultrafilters.UltrapowerProperness
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_universal_ultrapower_properness :
    Targets.UniversalUltrapowerProperness := universal_ultrapower_properness

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
