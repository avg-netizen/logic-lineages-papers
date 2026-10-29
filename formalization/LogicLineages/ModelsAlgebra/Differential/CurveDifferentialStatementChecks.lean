module

public import LogicLineages.ModelsAlgebra.Differential.CurveDifferential
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_pairEvaluationChainRule : Targets.pairEvaluationChainRule :=
  CurveDifferential.pairEvaluationChainRule

theorem fixed_curveSecondJet : Targets.curveSecondJet :=
  CurveDifferential.curveSecondJet

theorem fixed_curveFirstJetField : Targets.curveFirstJetField :=
  CurveDifferential.curveFirstJetField

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
