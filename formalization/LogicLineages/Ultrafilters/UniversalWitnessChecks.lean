module

public import LogicLineages.Ultrafilters.UniversalWitness
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_universal_properness_witness : Targets.UniversalPropernessWitness :=
  universal_properness_witness

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
