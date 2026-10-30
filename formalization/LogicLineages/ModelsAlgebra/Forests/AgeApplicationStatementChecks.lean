module

public import LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem realizedForestAgeNonempty : LogicLineages.ModelsAlgebra.Forests.Targets.RealizedForestAgeNonempty :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.realizedForestAgeNonempty

theorem avoidanceClassHereditary : LogicLineages.ModelsAlgebra.Forests.Targets.AvoidanceClassHereditary :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.avoidanceClassHereditary

theorem avoidanceClassNonemptyCriterion : LogicLineages.ModelsAlgebra.Forests.Targets.AvoidanceClassNonemptyCriterion :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.avoidanceClassNonemptyCriterion

theorem noEmptyCodeTestCorrect : LogicLineages.ModelsAlgebra.Forests.Targets.NoEmptyCodeTestCorrect :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.noEmptyCodeTestCorrect

theorem noEmptyCodeTestPrimitiveRecursive : LogicLineages.ModelsAlgebra.Forests.Targets.NoEmptyCodeTestPrimitiveRecursive :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.noEmptyCodeTestPrimitiveRecursive

theorem forbiddenForestAgeCriterion : LogicLineages.ModelsAlgebra.Forests.Targets.ForbiddenForestAgeCriterion :=
  LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof.forbiddenForestAgeCriterion

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
