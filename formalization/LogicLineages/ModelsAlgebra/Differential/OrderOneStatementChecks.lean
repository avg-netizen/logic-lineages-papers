module

public import LogicLineages.ModelsAlgebra.Differential.OrderOne
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_liftedOrdinaryDerivation : Targets.liftedOrdinaryDerivation :=
  OrderOne.liftedOrdinaryDerivation

theorem fixed_liftedPolynomialEvaluation : Targets.liftedPolynomialEvaluation :=
  OrderOne.liftedPolynomialEvaluation

theorem fixed_liftedJetEvaluation : Targets.liftedJetEvaluation :=
  OrderOne.liftedJetEvaluation

theorem fixed_orderOneNonzeroSpecialization : Targets.orderOneNonzeroSpecialization :=
  OrderOne.orderOneNonzeroSpecialization

theorem fixed_orderOneZeroSpecialization : Targets.orderOneZeroSpecialization :=
  OrderOne.orderOneZeroSpecialization

theorem fixed_orderOneCriterion : Targets.orderOneCriterion :=
  OrderOne.orderOneCriterion

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
