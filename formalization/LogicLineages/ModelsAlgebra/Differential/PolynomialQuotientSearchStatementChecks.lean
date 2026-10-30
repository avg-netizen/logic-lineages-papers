module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_polynomialQuotientAtIndexPrimitiveRecursive :
    Targets.polynomialQuotientAtIndexPrimitiveRecursive :=
  PolynomialQuotientSearch.atIndex_primitive_recursive

theorem fixed_polynomialQuotientSearchCorrect : Targets.polynomialQuotientSearchCorrect :=
  PolynomialQuotientSearch.search_correct

theorem fixed_polynomialQuotientSearchTotal : Targets.polynomialQuotientSearchTotal :=
  PolynomialQuotientSearch.search_total

theorem fixed_polynomialQuotientSearchPartialRecursive :
    Targets.polynomialQuotientSearchPartialRecursive := PolynomialQuotientSearch.search_partial_recursive

theorem fixed_polynomialQuotientComputableRealization :
    Targets.polynomialQuotientComputableRealization := PolynomialQuotientSearch.computable_realization

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
