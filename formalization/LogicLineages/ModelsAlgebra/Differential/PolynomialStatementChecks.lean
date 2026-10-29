module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialTargets
public import LogicLineages.ModelsAlgebra.Differential.PolynomialEvaluation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem jet_evaluation_commutes : Targets.jetEvaluationCommutes := by
  intro F _ _ D a p
  exact jetEval_polynomialDerivation D a p

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
