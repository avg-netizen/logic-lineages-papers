module
public import LogicLineages.ModelsAlgebra.PGroups.RawBoundedLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
public import LogicLineages.ModelsAlgebra.PGroups.TorsionScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem raw_bounded_no_sigma_two_scott : Targets.groupRawBoundedNoSigmaTwoScott := by
  intro p _ G _ _ _ N hN φ hφ hs
  exact p_primary_no_sigma_two_scott p (Fact.out : p.Prime) G (fun x => ⟨N,hN x⟩)
    φ hφ (raw_scott_restriction G φ hs)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
