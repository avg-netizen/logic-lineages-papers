module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminant
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_numericDeterminantCorrect : Targets.numericDeterminantCorrect :=
  NumericDeterminant.determinant_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
