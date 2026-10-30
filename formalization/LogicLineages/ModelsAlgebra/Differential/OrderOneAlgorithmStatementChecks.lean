module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks
universe u

theorem fixed_orderOneAlgorithmInputCoverage : Targets.orderOneAlgorithmInputCoverage :=
  OrderOneAlgorithm.input_coverage
theorem fixed_orderOneAlgorithmSpecialization : Targets.orderOneAlgorithmSpecialization :=
  OrderOneAlgorithm.specialization_correct
theorem fixed_orderOneAlgorithmSearchCorrect : Targets.orderOneAlgorithmSearchCorrect.{u} :=
  OrderOneAlgorithm.search_answer_correct
theorem fixed_orderOneAlgorithmSearchTotal : Targets.orderOneAlgorithmSearchTotal :=
  OrderOneAlgorithm.search_total
theorem fixed_orderOneAlgorithmSearchPartialRecursive : Targets.orderOneAlgorithmSearchPartialRecursive :=
  OrderOneAlgorithm.search_partial_recursive
theorem fixed_orderOneAlgorithmComputableRealization : Targets.orderOneAlgorithmComputableRealization.{u} :=
  OrderOneAlgorithm.computable_realization

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
