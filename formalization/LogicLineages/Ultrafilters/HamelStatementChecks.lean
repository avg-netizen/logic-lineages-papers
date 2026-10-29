module

public import LogicLineages.Ultrafilters.HamelLength
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_hamel_length_escapes : Targets.HamelLengthEscapes :=
  hamel_length_escapes

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
