module

public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.PowerCyclicStatementChecks

theorem fixed_power_cyclic_inclusion_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicInclusionEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_inclusion_evaluation

theorem fixed_power_cyclic_inclusion_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicInclusionInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_inclusion_injective

theorem fixed_power_cyclic_inclusion_range : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicInclusionRange :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_inclusion_range

theorem fixed_power_cyclic_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_socle_roots

theorem fixed_power_cyclic_socle_witness : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicSocleWitness :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_socle_witness

theorem fixed_power_cyclic_annihilation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerCyclicAnnihilation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_cyclic_annihilation

end LogicLineages.ModelsAlgebra.PGroups.PowerCyclicStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
