module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantWeight
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_numericDeterminantPermutationWeight : Targets.numericDeterminantPermutationWeight :=
  NumericDeterminant.permutation_weight

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
