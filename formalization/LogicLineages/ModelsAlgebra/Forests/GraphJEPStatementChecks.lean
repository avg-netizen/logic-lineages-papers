module

public import LogicLineages.ModelsAlgebra.Forests.GraphJEPProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem graphAvoidanceIsoInvariant : LogicLineages.ModelsAlgebra.Forests.Targets.GraphAvoidanceIsoInvariant :=
  LogicLineages.ModelsAlgebra.Forests.GraphJEPProof.graphAvoidanceIsoInvariant

theorem comparabilityAvoidance : LogicLineages.ModelsAlgebra.Forests.Targets.ComparabilityAvoidance :=
  LogicLineages.ModelsAlgebra.Forests.GraphJEPProof.comparabilityAvoidance

theorem forbiddenGraphRepresented : LogicLineages.ModelsAlgebra.Forests.Targets.ForbiddenGraphRepresented :=
  LogicLineages.ModelsAlgebra.Forests.GraphJEPProof.forbiddenGraphRepresented

theorem forbiddenFamilyJEPEquivalence : LogicLineages.ModelsAlgebra.Forests.Targets.ForbiddenFamilyJEPEquivalence :=
  LogicLineages.ModelsAlgebra.Forests.GraphJEPProof.forbiddenFamilyJEPEquivalence

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
