module

public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScottStatementChecks

theorem fixed_embedding_low_comparison : Targets.groupEmbeddingLowBackForth :=
  GroupInfinitary.embedding_low_comparison

theorem fixed_embedding_low_pi_descent : Targets.groupEmbeddingLowPiDescent :=
  GroupInfinitary.embedding_low_pi_descent

theorem fixed_sigma_two_finite_submodel : Targets.groupSigmaTwoFiniteSubmodel :=
  GroupInfinitary.sigma_two_finite_submodel

theorem fixed_locally_finite_no_sigma_two_scott : Targets.groupLocallyFiniteNoSigmaTwoScott :=
  GroupInfinitary.locally_finite_no_sigma_two_scott

end LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
