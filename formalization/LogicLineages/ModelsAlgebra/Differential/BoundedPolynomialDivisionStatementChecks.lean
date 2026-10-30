module

public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionComplete
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_boundedDivisionInputCoverage : Targets.boundedDivisionInputCoverage :=
  BoundedPolynomialDivision.input_coverage
theorem fixed_boundedDivisionSearchCorrect : Targets.boundedDivisionSearchCorrect :=
  BoundedPolynomialDivision.search_correct
theorem fixed_boundedDivisionSearchTotal : Targets.boundedDivisionSearchTotal :=
  BoundedPolynomialDivision.search_total
theorem fixed_boundedDivisionSearchPartialRecursive : Targets.boundedDivisionSearchPartialRecursive :=
  BoundedPolynomialDivision.search_partial_recursive
theorem fixed_boundedDivisionComputableRealization : Targets.boundedDivisionComputableRealization :=
  BoundedPolynomialDivision.computable_realization

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
