module

public import LogicLineages.Ultrafilters.CoordinateBranch
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_nonprincipal_coordinate_witness :
    Targets.NonprincipalCoordinateWitness := nonprincipal_coordinate_witness

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
