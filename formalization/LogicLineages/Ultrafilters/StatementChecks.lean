module

public import LogicLineages.Ultrafilters.PersistentDiscontinuity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_persistent_discontinuity : Targets.PersistentDiscontinuity :=
  persistent_discontinuity

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
