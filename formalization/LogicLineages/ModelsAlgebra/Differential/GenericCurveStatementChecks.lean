module

public import LogicLineages.ModelsAlgebra.Differential.GenericCurve
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_genericCurveUniformWitness : Targets.genericCurveUniformWitness :=
  GenericCurve.genericCurveUniformWitness

theorem fixed_genericCurveAvoidance : Targets.genericCurveAvoidance :=
  GenericCurve.genericCurveAvoidance

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
