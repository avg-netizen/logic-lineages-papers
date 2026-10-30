module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicComplete
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_cyclotomicCoefficientCode : Targets.cyclotomicCoefficientCode :=
  CyclotomicAlgorithm.coefficient_code
theorem fixed_cyclotomicAlgorithmTotal : Targets.cyclotomicAlgorithmTotal :=
  CyclotomicAlgorithm.search_total
theorem fixed_cyclotomicAlgorithmPartialRecursive : Targets.cyclotomicAlgorithmPartialRecursive :=
  CyclotomicAlgorithm.search_partial_recursive
theorem fixed_cyclotomicEffectiveFamily : Targets.cyclotomicEffectiveFamily :=
  CyclotomicAlgorithm.effective_family
theorem fixed_cyclotomicFullSource : Targets.cyclotomicFullSource := CyclotomicFamily.full_source

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
