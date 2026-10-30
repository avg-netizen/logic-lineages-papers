module
public import LogicLineages.ModelsAlgebra.PGroups.RawSourceOneInfiniteTargets
public import LogicLineages.ModelsAlgebra.PGroups.SourceOneInfinite
public import LogicLineages.ModelsAlgebra.PGroups.RawScott
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem raw_source_positive_lower_scott_bounds : Targets.groupRawSourcePositiveLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hi hf hp
  obtain ⟨⟨d,hd,hs⟩,hSigma,hPi⟩ := source_positive_lower_scott_bounds p G k N hk hkN hb hi hf hp
  refine ⟨⟨guardDifference d, ?_, raw_guard_difference_scott_transfer G d hs⟩, ?_, ?_⟩
  · exact raw_guard_difference_complexity 2 (Order.one_le_iff_ne_zero.mpr (by simp)) d hd
  · intro φ hφ hraw
    exact hSigma φ hφ (raw_scott_restriction G φ hraw)
  · intro φ hφ hraw
    exact hPi φ hφ (raw_scott_restriction G φ hraw)

theorem raw_source_zero_lower_scott_bounds : Targets.groupRawSourceZeroLowerScottBounds := by
  intro p _ G _ _ k N hk hkN hb hi hf hz
  obtain ⟨⟨φ,hφ,hs⟩,hPi,hd⟩ := source_zero_lower_scott_bounds p G k N hk hkN hb hi hf hz
  refine ⟨⟨guardPi φ, ?_, raw_guard_scott_transfer G φ hs⟩, ?_, ?_⟩
  · exact raw_guard_pi_complexity 2 (Order.one_le_iff_ne_zero.mpr (by simp)) φ hφ
  · intro ψ hψ hraw
    exact hPi ψ hψ (raw_scott_restriction G ψ hraw)
  · intro d hlevel hraw
    exact hd d hlevel (raw_difference_scott_restriction G d hraw)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
