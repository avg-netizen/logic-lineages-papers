module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem fixed_forestCodeCodecFaithful : Targets.ForestCodeCodecFaithful :=
  FiniteCodeProof.forestCodeCodecFaithful

theorem fixed_forestCodeValidation : Targets.ForestCodeValidation :=
  FiniteCodeProof.forestCodeValidation

theorem fixed_forestCodeEnumeration : Targets.ForestCodeEnumeration :=
  FiniteCodeProof.forestCodeEnumeration

theorem fixed_forestMapWordEnumeration : Targets.ForestMapWordEnumeration :=
  FiniteCodeProof.forestMapWordEnumeration

theorem fixed_forestMapTestCorrect : Targets.ForestMapTestCorrect :=
  FiniteCodeProof.forestMapTestCorrect

theorem fixed_forestEmbeddingTestCorrect : Targets.ForestEmbeddingTestCorrect :=
  FiniteCodeProof.forestEmbeddingTestCorrect

theorem fixed_forestAvoidanceTestCorrect : Targets.ForestAvoidanceTestCorrect :=
  FiniteCodeProof.forestAvoidanceTestCorrect

theorem fixed_forestBoundedHostTestCorrect : Targets.ForestBoundedHostTestCorrect :=
  FiniteCodeProof.forestBoundedHostTestCorrect

theorem fixed_forestNegativePairTestCorrect : Targets.ForestNegativePairTestCorrect :=
  FiniteCodeProof.forestNegativePairTestCorrect

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
