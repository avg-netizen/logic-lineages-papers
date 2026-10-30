module

public import LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem realizedForestAgeHasJEP : LogicLineages.ModelsAlgebra.Forests.Targets.RealizedForestAgeHasJEP :=
  LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof.realizedForestAgeHasJEP

theorem unboundedForestAgeInfinite : LogicLineages.ModelsAlgebra.Forests.Targets.UnboundedForestAgeInfinite :=
  LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof.unboundedForestAgeInfinite

theorem unboundedForestAgeCountablyInfinite : LogicLineages.ModelsAlgebra.Forests.Targets.UnboundedForestAgeCountablyInfinite :=
  LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof.unboundedForestAgeCountablyInfinite

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
