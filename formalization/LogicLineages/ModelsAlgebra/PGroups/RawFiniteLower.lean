module
public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
public import LogicLineages.ModelsAlgebra.PGroups.FiniteScottLower
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem raw_finite_no_sigma_one_scott : Targets.groupRawFiniteNoSigmaOneScott.{u} := by
  intro G _ _ _ φ hφ hs
  exact finite_no_sigma_one_scott G φ hφ (raw_scott_restriction G φ hs)

theorem raw_nontrivial_no_pi_one_scott : Targets.groupRawNontrivialNoPiOneScott.{u} := by
  intro G _ _ _ φ hφ hs
  exact nontrivial_no_pi_one_scott G φ hφ (raw_scott_restriction G φ hs)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
