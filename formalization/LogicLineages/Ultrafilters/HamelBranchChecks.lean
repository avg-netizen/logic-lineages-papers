module

public import LogicLineages.Ultrafilters.HamelBranch
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_vanishing_coordinate_witness : Targets.VanishingCoordinateWitness :=
  vanishing_coordinate_witness

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
