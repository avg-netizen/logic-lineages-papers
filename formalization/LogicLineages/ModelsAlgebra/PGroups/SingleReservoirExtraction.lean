module
public import LogicLineages.ModelsAlgebra.PGroups.SingleReservoirExtractionTargets
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclic
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricity
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssembly
public import Mathlib.Data.Finsupp.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem single_reservoir_extraction : Targets.groupSingleReservoirExtraction := by
  classical
  intro p _ K _ _ N a hbound ha
  obtain ⟨I, _, hI⟩ := bounded_cyclic_calibrated_decomposition p K N hbound
  letI (l : Fin N) : Countable (I l) := Cardinal.mk_le_aleph0_iff.mp
    ((hI l).le.trans (countable_ulm_rank_bound p K l.val))
  let A := ResidualCyclicProduct p N I a a
  let R := A × (ℕ →₀ ZMod (p^(a.val+1)))
  have hR : ∀ x : R, p^N • x = 0 := by
    intro x
    apply Prod.ext
    · exact residual_cyclic_exponent p N I a a x.1
    · ext n
      exact power_cyclic_annihilation p (a.val+1) N (Nat.succ_le_of_lt a.isLt) (x.2 n)
  have hr (j : Fin N) : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup K)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup R)) := by
    change _ = Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val :
      AddSubgroup (A × (ℕ →₀ ZMod (p^(a.val+1))))))
    rw [product_ulm_rank, residual_cyclic_rank, infinite_cyclic_ulm_rank]
    by_cases hja : j = a
    · subst j
      simp [ha, Fin.val_inj]
    · simp [hja, Fin.val_inj, hI j]
  obtain ⟨e⟩ := bounded_ulm_categoricity p K R N hbound hR hr
  exact ⟨A, inferInstance, inferInstance, ⟨e⟩⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
