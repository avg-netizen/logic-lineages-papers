module

public import LogicLineages.Ultrafilters.AdmissibleExistence
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_admissible_existence : Targets.AdmissibleExistence := admissible_exists

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
