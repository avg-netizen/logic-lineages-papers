module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeSquare
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.PrimeSquareStatementChecks

theorem fixed_prime_square_inclusion_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeSquareInclusionEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.prime_square_inclusion_evaluation

theorem fixed_prime_square_inclusion_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeSquareInclusionInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.prime_square_inclusion_injective

theorem fixed_prime_square_inclusion_range : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeSquareInclusionRange :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.prime_square_inclusion_range

theorem fixed_prime_square_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPrimeSquareSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.prime_square_socle_roots

end LogicLineages.ModelsAlgebra.PGroups.PrimeSquareStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
