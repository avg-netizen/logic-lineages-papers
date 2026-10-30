module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndex
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_kroneckerIndexInjective : Targets.kroneckerIndexInjective := KroneckerIndex.index_injective
theorem fixed_kroneckerIndexBound : Targets.kroneckerIndexBound := KroneckerIndex.index_bound
theorem fixed_kroneckerDigitsBound : Targets.kroneckerDigitsBound := KroneckerIndex.digits_bound
theorem fixed_kroneckerDigitsIndex : Targets.kroneckerDigitsIndex := KroneckerIndex.digits_index
theorem fixed_kroneckerIndexDigits : Targets.kroneckerIndexDigits := KroneckerIndex.index_digits

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
