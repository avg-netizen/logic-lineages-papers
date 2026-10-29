module

public import LogicLineages.ModelsAlgebra.Differential.Radical
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_rationalRadicalMonicSquarefree : Targets.rationalRadicalMonicSquarefree :=
  Radical.rationalRadicalMonicSquarefree

theorem fixed_rationalRadicalRootCriterion : Targets.rationalRadicalRootCriterion :=
  Radical.rationalRadicalRootCriterion

theorem fixed_radicalAmbientRootVanishing : Targets.radicalAmbientRootVanishing :=
  Radical.radicalAmbientRootVanishing

theorem fixed_badConstantCurveWitness : Targets.badConstantCurveWitness :=
  Radical.badConstantCurveWitness

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
