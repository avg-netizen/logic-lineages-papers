module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssemblyTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlm
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem finite_cyclic_ulm_rank : Targets.groupFiniteCyclicUlmRank := by
  classical
  intro p _ t ℓ j
  rw [pi_ulm_rank]
  have hr (i : Fin t) : Module.rank (ZMod p)
      (UlmLayer p (finiteFiltration p j : AddSubgroup (ZMod (p ^ ℓ i)))) =
      if j + 1 = ℓ i then 1 else 0 := cyclic_ulm_rank p (ℓ i) j
  simp_rw [hr]
  let d : Fin t → ℕ := fun i => if j + 1 = ℓ i then 1 else 0
  have hd (i : Fin t) : (if j + 1 = ℓ i then 1 else 0 : Cardinal) = Cardinal.mk (Fin (d i)) := by
    by_cases hi : j + 1 = ℓ i <;> simp [d, hi]
  simp_rw [hd]
  rw [← Cardinal.mk_sigma, Cardinal.mk_fintype]
  simp [Fintype.card_sigma, d]

theorem infinite_cyclic_ulm_rank : Targets.groupInfiniteCyclicUlmRank := by
  intro p _ k j
  rw [finsupp_ulm_rank, cyclic_ulm_rank]
  by_cases h : j + 1 = k <;> simp [h]

theorem full_shift_ulm_rank : Targets.groupFullShiftUlmRank := by
  intro p _ k t ℓ s r j
  dsimp only [FullShiftGroup, BlockShiftGroup, UpperCyclicGroup]
  rw [product_ulm_rank, product_ulm_rank, finite_cyclic_ulm_rank,
    infinite_cyclic_ulm_rank, finite_cyclic_ulm_rank]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
