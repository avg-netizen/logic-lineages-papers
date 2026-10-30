module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteBoundsTargets
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicBoundedScott
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicLower
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScott
public import LogicLineages.ModelsAlgebra.PGroups.UniversalScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem positive_lower_scott_bounds : Targets.groupPositiveLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hf hi hlo hn
  letI : Infinite (multipleImage G (p ^ (k-1))) := hi
  letI : Infinite G := Infinite.of_injective
    (Subtype.val : multipleImage G (p ^ (k-1)) → G) Subtype.val_injective
  exact ⟨intrinsic_bounded_difference_scott p G k N hk hkN hb hf hi hlo,
    p_primary_no_sigma_two_scott p (Fact.out : p.Prime) G (fun g => ⟨N,hb g⟩),
    intrinsic_no_pi_two_scott p G k N hk hkN hb hf hi hlo hn⟩

theorem zero_lower_scott_bounds : Targets.groupZeroLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hf hi hlo
  letI : Infinite (multipleImage G (p ^ (k-1))) := hi
  letI : Infinite G := Infinite.of_injective
    (Subtype.val : multipleImage G (p ^ (k-1)) → G) Subtype.val_injective
  have hlocal : LocallyFinite G := torsion_locally_finite G
    (p_primary_torsion p (Fact.out : p.Prime) G (fun g => ⟨N,hb g⟩))
  exact ⟨intrinsic_bounded_pi_scott p G k N hk hkN hb hf hi hlo,
    universal_no_scott G, locally_finite_no_difference_one_scott G hlocal⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
