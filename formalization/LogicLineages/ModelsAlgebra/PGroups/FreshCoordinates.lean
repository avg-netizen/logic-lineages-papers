module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCoordinatesTargets
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem reserve_even_injective : Targets.groupReserveEvenInjective := by
  intro M a b h
  simp only [reserveEven] at h
  split_ifs at h <;> omega

theorem reserve_odd_injective : Targets.groupReserveOddInjective := by
  intro M a b h
  simp only [reserveOdd] at h
  omega

theorem reserve_ranges_disjoint : Targets.groupReserveRangesDisjoint := by
  intro M
  apply Set.disjoint_left.mpr
  rintro y ⟨a,rfl⟩ ⟨b,h⟩
  simp only [reserveEven, reserveOdd] at h
  split_ifs at h <;> omega

theorem reserve_even_fixes : Targets.groupReserveEvenFixes := by
  intro M n h
  exact if_pos h

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
