module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_filtration_bottom : Targets.groupCyclicFiltrationBottom := by
  intro p k j h
  rw [finite_filtration_multiple_image]
  ext x
  change (∃ y : ZMod (p ^ k), p ^ j • y = x) ↔ x = 0
  constructor
  · rintro ⟨y, rfl⟩
    exact power_cyclic_annihilation p k j h y
  · intro hx
    exact ⟨0, by simp [hx]⟩

theorem cyclic_filtration_socle : Targets.groupCyclicFiltrationSocle := by
  intro p _ k j hj
  ext x
  change (x ∈ finiteFiltration p j ∧ p • x = 0) ↔
    (x ∈ (⊤ : AddSubgroup (ZMod (p ^ k))) ∧ p • x = 0)
  constructor
  · intro hx
    exact ⟨AddSubgroup.mem_top x, hx.2⟩
  · intro hx
    refine ⟨?_, hx.2⟩
    rw [finite_filtration_multiple_image]
    obtain ⟨y, hy⟩ := power_cyclic_socle_roots p k (by omega) x hx.2
    refine ⟨p ^ (k - 1 - j) • y, ?_⟩
    change p ^ j • (p ^ (k - 1 - j) • y) = x
    rw [smul_smul, ← pow_add, Nat.add_sub_of_le (show j ≤ k - 1 by omega)]
    exact hy

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
