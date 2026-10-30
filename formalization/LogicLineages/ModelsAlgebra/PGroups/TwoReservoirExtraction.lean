module
public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtractionTargets
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclic
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricity
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssembly
public import Mathlib.Data.Finsupp.Encodable
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem two_reservoir_extraction : Targets.groupTwoReservoirExtraction := by
  classical
  intro p _ G _ _ N a b hab hbound ha hb
  obtain ⟨I, _, hI⟩ := bounded_cyclic_calibrated_decomposition p G N hbound
  letI (l : Fin N) : Countable (I l) := Cardinal.mk_le_aleph0_iff.mp
    ((hI l).le.trans (countable_ulm_rank_bound p G l.val))
  let A := ResidualCyclicProduct p N I a b
  let R := ReservoirGroup A (ZMod (p^(a.val+1))) (ZMod (p^(b.val+1)))
  have hA : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup A)) = 0 := by
    simpa using residual_cyclic_rank p N I a b a
  have hR : ∀ x : R, p^N • x = 0 := by
    intro x
    apply Prod.ext
    · exact residual_cyclic_exponent p N I a b x.1
    apply Prod.ext
    · ext n
      exact power_cyclic_annihilation p (a.val+1) N (Nat.succ_le_of_lt a.isLt) (x.2.1 n)
    · ext n
      exact power_cyclic_annihilation p (b.val+1) N (Nat.succ_le_of_lt b.isLt) (x.2.2 n)
  have hr (j : Fin N) : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup R)) := by
    change _ = Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val :
      AddSubgroup (A × ((ℕ →₀ ZMod (p^(a.val+1))) × (ℕ →₀ ZMod (p^(b.val+1)))))))
    rw [product_ulm_rank, product_ulm_rank, residual_cyclic_rank,
      infinite_cyclic_ulm_rank, infinite_cyclic_ulm_rank]
    have hne : a ≠ b := ne_of_lt hab
    by_cases hja : j = a
    · subst j
      simp [ha, hne, Fin.val_inj]
    · by_cases hjb : j = b
      · subst j
        simp [hb, hne, hne.symm, Fin.val_inj]
      · simp [hja,hjb, Fin.val_inj, hI j]
  obtain ⟨e⟩ := bounded_ulm_categoricity p G R N hbound hR hr
  exact ⟨A, inferInstance, inferInstance, hA, ⟨e⟩⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
